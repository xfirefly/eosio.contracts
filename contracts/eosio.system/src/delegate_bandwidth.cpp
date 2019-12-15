#include <eosio/datastream.hpp>
#include <eosio/eosio.hpp>
#include <eosio/multi_index.hpp>
#include <eosio/privileged.hpp>
#include <eosio/serialize.hpp>
#include <eosio/transaction.hpp>

#include <eosio.system/eosio.system.hpp>
#include <eosio.token/eosio.token.hpp>

#include "name_bidding.cpp"
// Unfortunately, this is needed until CDT fixes the duplicate symbol error with eosio::send_deferred

namespace eosiosystem {

   using eosio::asset;
   using eosio::const_mem_fun;
   using eosio::current_time_point;
   using eosio::indexed_by;
   using eosio::permission_level;
   using eosio::seconds;
   using eosio::time_point_sec;
   using eosio::token;

   time_point_sec current_time_point_sec() 
   {
      const static time_point_sec cts{ current_time_point() };
      return cts;
   };

   /*
   计算time1-time2的天数
   */
   uint32_t difftime(const time_point_sec& time1, const time_point_sec& time2)
   {
      time_point_sec out(time1.sec_since_epoch());

      check(time1 >= time2, "time1  must be greater than time2");
      out -= time2;

      return out.sec_since_epoch()/86400;
   }

   /**
    *  This action will buy an exact amount of ram and bill the payer the current market price.
    */
   void system_contract::buyrambytes( const name& payer, const name& receiver, uint32_t bytes ) {
      auto itr = _rammarket.find(ramcore_symbol.raw());
      const int64_t ram_reserve   = itr->base.balance.amount;
      const int64_t eos_reserve   = itr->quote.balance.amount;
      const int64_t cost          = exchange_state::get_bancor_input( ram_reserve, eos_reserve, bytes );
      const int64_t cost_plus_fee = cost / double(0.995);
      buyram( payer, receiver, asset{ cost_plus_fee, core_symbol() } );
   }


   /**
    *  When buying ram the payer irreversiblly transfers quant to system contract and only
    *  the receiver may reclaim the tokens via the sellram action. The receiver pays for the
    *  storage of all database records associated with this action.
    *
    *  RAM is a scarce resource whose supply is defined by global properties max_ram_size. RAM is
    *  priced using the bancor algorithm such that price-per-byte with a constant reserve ratio of 100:1.
    */
   void system_contract::buyram( const name& payer, const name& receiver, const asset& quant )
   {
      require_auth( payer );
      update_ram_supply();

      check( quant.symbol == core_symbol(), "must buy ram with core token" );
      check( quant.amount > 0, "must purchase a positive amount" );

      auto fee = quant;
      fee.amount = ( fee.amount + 199 ) / 200; /// .5% fee (round up)
      // fee.amount cannot be 0 since that is only possible if quant.amount is 0 which is not allowed by the assert above.
      // If quant.amount == 1, then fee.amount == 1,
      // otherwise if quant.amount > 1, then 0 < fee.amount < quant.amount.
      auto quant_after_fee = quant;
      quant_after_fee.amount -= fee.amount;
      // quant_after_fee.amount should be > 0 if quant.amount > 1.
      // If quant.amount == 1, then quant_after_fee.amount == 0 and the next inline transfer will fail causing the buyram action to fail.
      {
         token::transfer_action transfer_act{ token_account, { {payer, active_permission}, {ram_account, active_permission} } };
         transfer_act.send( payer, ram_account, quant_after_fee, "buy ram" );
      }
      if ( fee.amount > 0 ) {
         token::transfer_action transfer_act{ token_account, { {payer, active_permission} } };
         transfer_act.send( payer, ramfee_account, fee, "ram fee" );
         channel_to_rex( ramfee_account, fee );
      }

      int64_t bytes_out;

      const auto& market = _rammarket.get(ramcore_symbol.raw(), "ram market does not exist");
      _rammarket.modify( market, same_payer, [&]( auto& es ) {
         bytes_out = es.direct_convert( quant_after_fee,  ram_symbol ).amount;
      });

      check( bytes_out > 0, "must reserve a positive amount" );

      _gstate.total_ram_bytes_reserved += uint64_t(bytes_out);
      _gstate.total_ram_stake          += quant_after_fee.amount;

      user_resources_table  userres( get_self(), receiver.value );
      auto res_itr = userres.find( receiver.value );
      if( res_itr ==  userres.end() ) {
         res_itr = userres.emplace( receiver, [&]( auto& res ) {
               res.owner = receiver;
               res.net_weight = asset( 0, core_symbol() );
               res.cpu_weight = asset( 0, core_symbol() );
               res.ram_bytes = bytes_out;
            });
      } else {
         userres.modify( res_itr, receiver, [&]( auto& res ) {
               res.ram_bytes += bytes_out;
            });
      }

      auto voter_itr = _voters.find( res_itr->owner.value );
      if( voter_itr == _voters.end() || !has_field( voter_itr->flags1, voter_info::flags1_fields::ram_managed ) ) {
         int64_t ram_bytes, net, cpu;
         get_resource_limits( res_itr->owner, ram_bytes, net, cpu );
         set_resource_limits( res_itr->owner, res_itr->ram_bytes + ram_gift_bytes, net, cpu );
      }
   }

  /**
    *  The system contract now buys and sells RAM allocations at prevailing market prices.
    *  This may result in traders buying RAM today in anticipation of potential shortages
    *  tomorrow. Overall this will result in the market balancing the supply and demand
    *  for RAM over time.
    */
   void system_contract::sellram( const name& account, int64_t bytes ) {
      require_auth( account );
      update_ram_supply();

      check( bytes > 0, "cannot sell negative byte" );

      user_resources_table  userres( get_self(), account.value );
      auto res_itr = userres.find( account.value );
      check( res_itr != userres.end(), "no resource row" );
      check( res_itr->ram_bytes >= bytes, "insufficient quota" );
      check( res_itr->ram_bytes >= (bytes + 65536), "Can't sell free memory ( 65536 bytes) " );   //xzy add

      asset tokens_out;
      auto itr = _rammarket.find(ramcore_symbol.raw());
      _rammarket.modify( itr, same_payer, [&]( auto& es ) {
         /// the cast to int64_t of bytes is safe because we certify bytes is <= quota which is limited by prior purchases
         tokens_out = es.direct_convert( asset(bytes, ram_symbol), core_symbol());
      });

      check( tokens_out.amount > 1, "token amount received from selling ram is too low" );

      _gstate.total_ram_bytes_reserved -= static_cast<decltype(_gstate.total_ram_bytes_reserved)>(bytes); // bytes > 0 is asserted above
      _gstate.total_ram_stake          -= tokens_out.amount;

      //// this shouldn't happen, but just in case it does we should prevent it
      check( _gstate.total_ram_stake >= 0, "error, attempt to unstake more tokens than previously staked" );

      userres.modify( res_itr, account, [&]( auto& res ) {
          res.ram_bytes -= bytes;
      });

      auto voter_itr = _voters.find( res_itr->owner.value );
      if( voter_itr == _voters.end() || !has_field( voter_itr->flags1, voter_info::flags1_fields::ram_managed ) ) {
         int64_t ram_bytes, net, cpu;
         get_resource_limits( res_itr->owner, ram_bytes, net, cpu );
         set_resource_limits( res_itr->owner, res_itr->ram_bytes + ram_gift_bytes, net, cpu );
      }

      {
         token::transfer_action transfer_act{ token_account, { {ram_account, active_permission}, {account, active_permission} } };
         transfer_act.send( ram_account, account, asset(tokens_out), "sell ram" );
      }
      auto fee = ( tokens_out.amount + 199 ) / 200; /// .5% fee (round up)
      // since tokens_out.amount was asserted to be at least 2 earlier, fee.amount < tokens_out.amount
      if ( fee > 0 ) {
         token::transfer_action transfer_act{ token_account, { {account, active_permission} } };
         transfer_act.send( account, ramfee_account, asset(fee, core_symbol()), "sell ram fee" );
         channel_to_rex( ramfee_account, asset(fee, core_symbol() ));
      }
   }

//   void validate_b1_vesting( int64_t stake ) {
//      const int64_t base_time = 1527811200; /// 2018-06-01
//      const int64_t max_claimable = 100'000'000'0000ll;
//      const int64_t claimable = int64_t(max_claimable * double(current_time_point().sec_since_epoch() - base_time) / (10*seconds_per_year) );
//
//      check( max_claimable - claimable <= stake, "b1 can only claim their tokens over 10 years" );
//   }

   void system_contract::changebw( name from, const name& receiver,
                                   const asset& stake_net_delta, const asset& stake_cpu_delta, bool transfer )
   {
      require_auth( from );
      check( stake_net_delta.amount != 0 || stake_cpu_delta.amount != 0, "should stake non-zero amount" );
      check( std::abs( (stake_net_delta + stake_cpu_delta).amount )
             >= std::max( std::abs( stake_net_delta.amount ), std::abs( stake_cpu_delta.amount ) ),
             "net and cpu deltas cannot be opposite signs" );

      name source_stake_from = from;
      if ( transfer ) {
         from = receiver;
      }

      // update stake delegated from "from" to "receiver"
      {
         del_bandwidth_table     del_tbl( get_self(), from.value );
         auto itr = del_tbl.find( receiver.value );
         if( itr == del_tbl.end() ) {
            itr = del_tbl.emplace( from, [&]( auto& dbo ){
                  dbo.from          = from;
                  dbo.to            = receiver;
                  dbo.net_weight    = stake_net_delta;
                  dbo.cpu_weight    = stake_cpu_delta;
               });
         }
         else {
            del_tbl.modify( itr, same_payer, [&]( auto& dbo ){
                  dbo.net_weight    += stake_net_delta;
                  dbo.cpu_weight    += stake_cpu_delta;
               });
         }
         check( 0 <= itr->net_weight.amount, "insufficient staked net bandwidth" );
         check( 0 <= itr->cpu_weight.amount, "insufficient staked cpu bandwidth" );
         if ( itr->is_empty() ) {
            del_tbl.erase( itr );
         }
      } // itr can be invalid, should go out of scope

      // update totals of "receiver"
      {
         user_resources_table   totals_tbl( get_self(), receiver.value );
         auto tot_itr = totals_tbl.find( receiver.value );
         if( tot_itr ==  totals_tbl.end() ) {
            tot_itr = totals_tbl.emplace( from, [&]( auto& tot ) {
                  tot.owner = receiver;
                  tot.net_weight    = stake_net_delta;
                  tot.cpu_weight    = stake_cpu_delta;
               });
         } else {
            totals_tbl.modify( tot_itr, from == receiver ? from : same_payer, [&]( auto& tot ) {
                  tot.net_weight    += stake_net_delta;
                  tot.cpu_weight    += stake_cpu_delta;
               });
         }
         check( 0 <= tot_itr->net_weight.amount, "insufficient staked total net bandwidth" );
         check( 0 <= tot_itr->cpu_weight.amount, "insufficient staked total cpu bandwidth" );

         {
            bool ram_managed = false;
            bool net_managed = false;
            bool cpu_managed = false;

            auto voter_itr = _voters.find( receiver.value );
            if( voter_itr != _voters.end() ) {
               ram_managed = has_field( voter_itr->flags1, voter_info::flags1_fields::ram_managed );
               net_managed = has_field( voter_itr->flags1, voter_info::flags1_fields::net_managed );
               cpu_managed = has_field( voter_itr->flags1, voter_info::flags1_fields::cpu_managed );
            }

            if( !(net_managed && cpu_managed) ) {
               int64_t ram_bytes, net, cpu;
               get_resource_limits( receiver, ram_bytes, net, cpu );

               set_resource_limits( receiver,
                                    ram_managed ? ram_bytes : std::max( tot_itr->ram_bytes + ram_gift_bytes, ram_bytes ),
                                    net_managed ? net : tot_itr->net_weight.amount,
                                    cpu_managed ? cpu : tot_itr->cpu_weight.amount );
            }
         }

         if ( tot_itr->is_empty() ) {
            totals_tbl.erase( tot_itr );
         }
      } // tot_itr can be invalid, should go out of scope

      // create refund or update from existing refund
      if ( stake_account != source_stake_from ) { //for eosio both transfer and refund make no sense
         refunds_table refunds_tbl( get_self(), from.value );
         auto req = refunds_tbl.find( from.value );

         //create/update/delete refund
         auto net_balance = stake_net_delta;
         auto cpu_balance = stake_cpu_delta;
         bool need_deferred_trx = false;


         // net and cpu are same sign by assertions in delegatebw and undelegatebw
         // redundant assertion also at start of changebw to protect against misuse of changebw
         bool is_undelegating = (net_balance.amount + cpu_balance.amount ) < 0;
         bool is_delegating_to_self = (!transfer && from == receiver);

         if( is_delegating_to_self || is_undelegating ) {
            if ( req != refunds_tbl.end() ) { //need to update refund
               refunds_tbl.modify( req, same_payer, [&]( refund_request& r ) {
                  if ( net_balance.amount < 0 || cpu_balance.amount < 0 ) {
                     r.request_time = current_time_point();
                  }
                  r.net_amount -= net_balance;
                  if ( r.net_amount.amount < 0 ) {
                     net_balance = -r.net_amount;
                     r.net_amount.amount = 0;
                  } else {
                     net_balance.amount = 0;
                  }
                  r.cpu_amount -= cpu_balance;
                  if ( r.cpu_amount.amount < 0 ){
                     cpu_balance = -r.cpu_amount;
                     r.cpu_amount.amount = 0;
                  } else {
                     cpu_balance.amount = 0;
                  }
               });

               check( 0 <= req->net_amount.amount, "negative net refund amount" ); //should never happen
               check( 0 <= req->cpu_amount.amount, "negative cpu refund amount" ); //should never happen

               if ( req->is_empty() ) {
                  refunds_tbl.erase( req );
                  need_deferred_trx = false;
               } else {
                  need_deferred_trx = true;
               }
            } else if ( net_balance.amount < 0 || cpu_balance.amount < 0 ) { //need to create refund
               refunds_tbl.emplace( from, [&]( refund_request& r ) {
                  r.owner = from;
                  if ( net_balance.amount < 0 ) {
                     r.net_amount = -net_balance;
                     net_balance.amount = 0;
                  } else {
                     r.net_amount = asset( 0, core_symbol() );
                  }
                  if ( cpu_balance.amount < 0 ) {
                     r.cpu_amount = -cpu_balance;
                     cpu_balance.amount = 0;
                  } else {
                     r.cpu_amount = asset( 0, core_symbol() );
                  }
                  r.request_time = current_time_point();
               });
               need_deferred_trx = true;
            } // else stake increase requested with no existing row in refunds_tbl -> nothing to do with refunds_tbl
         } /// end if is_delegating_to_self || is_undelegating

         if ( need_deferred_trx ) {
            eosio::transaction out;
            out.actions.emplace_back( permission_level{from, active_permission},
                                      get_self(), "refund"_n,
                                      from
            );
            out.delay_sec = refund_delay_sec;
            eosio::cancel_deferred( from.value ); // TODO: Remove this line when replacing deferred trxs is fixed
            out.send( from.value, from, true );
         } else {
            eosio::cancel_deferred( from.value );
         }

         auto transfer_amount = net_balance + cpu_balance;
         if ( 0 < transfer_amount.amount ) {
            token::transfer_action transfer_act{ token_account, { {source_stake_from, active_permission} } };
            transfer_act.send( source_stake_from, stake_account, asset(transfer_amount), "stake bandwidth" );
         }
      }

      vote_stake_updater( from );
      update_voting_power( from, stake_net_delta + stake_cpu_delta );
   }

   void system_contract::update_voting_power( const name& voter, const asset& total_update )
   {
      auto voter_itr = _voters.find( voter.value );
      if( voter_itr == _voters.end() ) {
         voter_itr = _voters.emplace( voter, [&]( auto& v ) {
            v.owner  = voter;
            v.staked = total_update.amount;
         });
      } else {
         _voters.modify( voter_itr, same_payer, [&]( auto& v ) {
            v.staked += total_update.amount;
         });
      }

      check( 0 <= voter_itr->staked, "stake for voting cannot be negative" );

//      if( voter == "b1"_n ) {
//         validate_b1_vesting( voter_itr->staked );
//      }

      if( voter_itr->producers.size() || voter_itr->proxy ) {
         update_votes( voter, voter_itr->proxy, voter_itr->producers, false );
      }
   }

   /*抵押/解除抵押资源时,计算/发放利息,重置更新时间*/
   void system_contract::changeit( const name& owner, const asset& quanity) {
      auto now = current_time_point_sec();

      /*年利率: 利率就从年化5%开始到年化最多15%，每多一周增加0.2 */
      uint64_t rate = 50;

      /*每过一周增长的年利率:0.2%(2表示0.2%)*/
      uint64_t rate_tips = 2;

      /*年利率上限:15%(150表示15%)*/
      uint64_t rate_max = 150;

      /*精度*/
      uint64_t base = 1000;

      interests_table interests( get_self(), owner.value );
      auto iter_interest = interests.find( owner.value );
      if( iter_interest == interests.end() )
      {
         if(quanity.amount < 0)
         {
            return; //check(0, "owner not found..");  // other 抵押给自己, 然后自己undelegatebw 触发
         }
         iter_interest = interests.emplace( owner, [&]( auto& i ) {
            i.owner  = owner;
            i.balance = quanity;
            i.last_time = now;
            i.inviter = "eosio"_n;
         });
      }
      else
      {
         uint64_t day = difftime(now, iter_interest->last_time);

         uint64_t diff = day / 7;

         rate += rate_tips * diff;

         if(rate > rate_max)
         {
            rate = rate_max;
         }

         /*
         日利率=年利率/360
         日利息=本金*日利率
         */
         uint64_t out = day * iter_interest->balance.amount * rate / 360 / base;

         if(out > 0)
         {
            uint64_t inviter_out = 0;

            if ( iter_interest->inviter != "eosio"_n ) {
                inviter_out = out / 10;
            }

            token::issue_action issue_act{ "eosio.token"_n, { {get_self(), active_permission} } };
            issue_act.send( get_self(), asset(out+inviter_out, core_symbol()), "issue for vote yield" );

            //token::transfer_action transfer_act{ "eosio.token"_n, { {get_self(), active_permission}, {owner, active_permission} } };
            token::transfer_action transfer_act{ token_account, { {get_self(), active_permission} } };
            transfer_act.send( get_self(), owner, asset(out, core_symbol()), "vote yield" );

            if ( inviter_out > 0 ) {
                transfer_act.send( get_self(), iter_interest->inviter, asset(inviter_out, core_symbol()), "invitation reward" );
            }
         }

         interests.modify( iter_interest, same_payer, [&]( auto& i ) {
            i.balance += quanity;
            i.last_time = now;
            if (i.balance.amount < 0)  // 如果 undelegatebw 的比 delegatebw  多, 此处为负
               i.balance = asset( 0, core_symbol() );
         });
      }
   }

   void system_contract::setinviter( const name& owner, const name& inviter  ) 
   {
        check(owner != inviter, "can not invite self");  
        check( is_account( inviter ), "inviter does not exist");
        require_auth( owner );

        interests_table interests( get_self(), owner.value );
        auto iter_interest = interests.find( owner.value );
        if( iter_interest == interests.end() ) {
            auto now = current_time_point_sec();
            iter_interest = interests.emplace( owner, [&]( auto& i ) {
            i.owner  = owner;
            i.balance = asset( 0, core_symbol() );
            i.last_time = now;
            i.inviter = inviter; 
            });
        }
        else
        {
            check(iter_interest->inviter == "eosio"_n , "Inviter has been set" );
            interests.modify( iter_interest, same_payer, [&]( auto& i ) {
                     i.inviter = inviter;
                 });
        }
    }


   /*for test*/
   void system_contract::update( const name& from, uint64_t day )
   {
      require_auth( get_self() );
      interests_table interests( get_self(), from.value );
      auto iter_interest = interests.find( from.value );
      if( iter_interest == interests.end() )
      {
         check( 0, "from not found..." );
      }
      else
      {
         if(day > 0)
         {
            uint32_t sec = day * 86400;
            time_point_sec last_time{ iter_interest->last_time.utc_seconds - sec };
            interests.modify( iter_interest, same_payer, [&]( auto& i ) {
               i.last_time = last_time;
            });
         }
         return;
      } 
   }

   void system_contract::delegatebw( const name& from, const name& receiver,
                                     const asset& stake_net_quantity,
                                     const asset& stake_cpu_quantity, bool transfer )
   {
      asset zero_asset( 0, core_symbol() );
      check( stake_cpu_quantity >= zero_asset, "must stake a positive amount" );
      check( stake_net_quantity >= zero_asset, "must stake a positive amount" );
      check( stake_net_quantity.amount + stake_cpu_quantity.amount > 0, "must stake a positive amount" );
      check( !transfer || from != receiver, "cannot use transfer flag if delegating to self" );

      changebw( from, receiver, stake_net_quantity, stake_cpu_quantity, transfer);

      if (from == receiver) {
      changeit(from, stake_net_quantity + stake_cpu_quantity);
      }
   } // delegatebw

   void system_contract::undelegatebw( const name& from, const name& receiver,
                                       const asset& unstake_net_quantity, const asset& unstake_cpu_quantity )
   {
      asset zero_asset( 0, core_symbol() );
      check( unstake_cpu_quantity >= zero_asset, "must unstake a positive amount" );
      check( unstake_net_quantity >= zero_asset, "must unstake a positive amount" );
      check( unstake_cpu_quantity.amount + unstake_net_quantity.amount > 0, "must unstake a positive amount" );
      check( _gstate.thresh_activated_stake_time != time_point(),
             "cannot undelegate bandwidth until the chain is activated (at least 15% of all tokens participate in voting)" );
      changebw( from, receiver, -unstake_net_quantity, -unstake_cpu_quantity, false);
      auto total = unstake_net_quantity + unstake_cpu_quantity;

      if (from == receiver) {
      changeit(from, -total);
      }
   } // undelegatebw


   void system_contract::refund( const name& owner ) {
      require_auth( owner );

      refunds_table refunds_tbl( get_self(), owner.value );
      auto req = refunds_tbl.find( owner.value );
      check( req != refunds_tbl.end(), "refund request not found" );
      check( req->request_time + seconds(refund_delay_sec) <= current_time_point(),
             "refund is not available yet" );
      token::transfer_action transfer_act{ token_account, { {stake_account, active_permission}, {req->owner, active_permission} } };
      transfer_act.send( stake_account, req->owner, req->net_amount + req->cpu_amount, "unstake" );
      refunds_tbl.erase( req );
   }


} //namespace eosiosystem
