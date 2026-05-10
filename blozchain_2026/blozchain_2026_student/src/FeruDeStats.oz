functor
export
   decode:Decode
   executeBlockchain:ExecuteBlockchain
   biggestSenders:BiggestSenders
   receivedMost:ReceivedMost
   moneyPeak:MoneyPeak
define
   fun {Puissance X N}
      if N == 0 then 1 else X * {Puissance X N-1} end
   end

   fun {TransactionHash T}
      (T.nonce + T.sender + T.receiver + T.value) mod {Puissance 10 6}
   end

   fun {Somme_T_lst Liste}
      case Liste of nil then 0
      [] H|T then {TransactionHash H} + {Somme_T_lst T}
      end
   end

   fun {BlockHash B}
      (B.number + B.previousHash + {Somme_T_lst B.transactions}) mod {Puissance 10 6}
   end

   fun {Effort T N Acc}
      if T.value >= 10 then
         {Effort transition(value: T.value div 10) N+1 Acc+{Puissance 2 N}}
      else Acc end
   end

   fun {AdaptGenesis GenesisState}
      {Record.mapInd GenesisState
       fun {$ _ Balance} user(balance:Balance nonce:0) end}
   end

   fun {Valid_transaction T State}
      local
         Sender = {CondSelect State T.sender user(balance:0 nonce:0)}
      in
         if T.max_effort >= 0 andthen
            T.max_effort >= {Effort T 1 1} andthen
            T.value >= 0 andthen
            Sender.balance >= T.value andthen
            T.hash \= 0 andthen
            T.hash == {TransactionHash T} andthen
            T.nonce == Sender.nonce + 1
         then true else false end
      end
   end

   fun {NewState State T}
      local
         Sender = T.sender
         Receiver = T.receiver
         Value = T.value
         OldSender = {CondSelect State Sender user(balance:0 nonce:0)}
         OldReceiver = {CondSelect State Receiver user(balance:0 nonce:0)}
         NewSender = user(balance:OldSender.balance - Value nonce:OldSender.nonce + 1)
         NewReceiver = user(balance:OldReceiver.balance + Value nonce:OldReceiver.nonce)
      in
         {AdjoinAt {AdjoinAt State Sender NewSender} Receiver NewReceiver}
      end
   end

   fun {UpdateStateWithList State Lst}
      case Lst of nil then State
      [] H|T then {UpdateStateWithList {NewState State H} T}
      end
   end

   fun {CheckBlockTransactions Trans State Num AccEffort}
      case Trans of nil then nil
      [] T|Reste then
         local E = {Effort T 1 1} in
            if {Valid_transaction T State} andthen
               T.block_number == Num andthen (AccEffort + E) =< 300
            then
               T | {CheckBlockTransactions Reste {NewState State T} Num AccEffort + E}
            else
               {CheckBlockTransactions Reste State Num AccEffort}
            end
         end
      end
   end

   fun {CreateBlock Transactions State Num PrevHash}
      local
         ValidT = {CheckBlockTransactions Transactions State Num 0}
         B = block(number:Num previousHash:PrevHash transactions:ValidT)
      in
         {Adjoin B block(hash:{BlockHash B})}
      end
   end

   fun {CreateBlockChain State Transactions Num PrevHash}
      local B = {CreateBlock Transactions State Num PrevHash} in
         if B.transactions == nil then nil#State
         else
            local
               NextS = {UpdateStateWithList State B.transactions}
               Rec = {CreateBlockChain NextS Transactions Num+1 B.hash}
            in
               (B|Rec.1)#Rec.2
            end
         end
      end
   end

   Tableau_Sharelock=tableau(10:&a 11:&b 12:&c 13:&d 14:&e 15:&f 16:&g 17:&h 18:&i 19:&j 20:&k 21:&l 22:&m 23:&n 24:&o 25:&p 26:&q 27:&r 28:&s 29:&t 30:&u 31:&v 32:&w 33:&x 34:&y 35:&z 36:& )

   fun {Decrypt Number}
      local N = (Number mod 37) in
         if N < 10 then Tableau_Sharelock.36
         else Tableau_Sharelock.N
         end
      end
   end

   fun {TransformToList N}
      {Map {IntToString N} fun {$ Char} Char - 48 end}
   end

   fun {Phrase_Liste Liste}
      case Liste of nil then nil
      [] H|H2|T then {Decrypt (10*H+H2)}|{Phrase_Liste T}
      [] _|nil then nil
      end
   end

   fun {Phrase Hash}
      {Phrase_Liste {TransformToList Hash}}
   end

   fun {Decode BlockChain}
      {Flatten
       case BlockChain of nil then nil
       [] B|R then {Phrase B.hash}|{Decode R}
       end}
   end

   proc {ExecuteBlockchain Genesis Transactions FinalState FinalBlockchain}
      local
         StartState = {AdaptGenesis Genesis}
         TransWithEffort =
            {Map Transactions fun {$ T} {Adjoin T transition(effort:{Effort T 1 1})} end}
         Res = {CreateBlockChain StartState TransWithEffort 0 0}
      in
         FinalBlockchain = Res.1
         FinalState = Res.2
      end
   end

   fun {AddValue Rec Key Value}
      local Old = {CondSelect Rec Key 0} in
         {AdjoinAt Rec Key Old + Value}
      end
   end

   fun {CountSendersInTransactions Transactions Counts}
      case Transactions of nil then Counts
      [] T|R then
         {CountSendersInTransactions R {AddValue Counts T.sender 1}}
      end
   end

   fun {CountReceiversInTransactions Transactions Counts}
      case Transactions of nil then Counts
      [] T|R then
         {CountReceiversInTransactions R {AddValue Counts T.receiver T.value}}
      end
   end

   fun {CountSenders Blockchain Counts}
      case Blockchain of nil then Counts
      [] B|R then
         {CountSenders R {CountSendersInTransactions B.transactions Counts}}
      end
   end

   fun {CountReceivers Blockchain Counts}
      case Blockchain of nil then Counts
      [] B|R then
         {CountReceivers R {CountReceiversInTransactions B.transactions Counts}}
      end
   end

   fun {RecordToPairs Rec}
      fun {Loop Features}
         case Features of nil then nil
         [] F|R then (F#{CondSelect Rec F 0})|{Loop R}
         end
      end
   in
      {Loop {Arity Rec}}
   end

   fun {BetterPair A B}
      if A.2 > B.2 then true
      elseif A.2 < B.2 then false
      else A.1 < B.1 end
   end

   fun {InsertPair Pair Pairs}
      case Pairs of nil then [Pair]
      [] H|T then
         if {BetterPair Pair H} then Pair|Pairs
         else H|{InsertPair Pair T} end
      end
   end

   fun {SortPairs Pairs}
      case Pairs of nil then nil
      [] H|T then {InsertPair H {SortPairs T}}
      end
   end

   fun {TakeUsers Pairs N}
      if N =< 0 then nil
      else
         case Pairs of nil then nil
         [] H|T then H.1|{TakeUsers T N-1}
         end
      end
   end

   fun {BiggestSenders Blockchain N}
      if N =< 0 then ~1
      else {TakeUsers {SortPairs {RecordToPairs {CountSenders Blockchain counts}}} N}
      end
   end

   fun {ReceivedMost Blockchain N}
      if N =< 0 then ~1
      else {TakeUsers {SortPairs {RecordToPairs {CountReceivers Blockchain counts}}} N}
      end
   end

   fun {BetterPeak Candidate Best}
      if Best == none then Candidate
      elseif Candidate.2 > Best.2 then Candidate
      elseif Candidate.2 < Best.2 then Best
      elseif Candidate.1 < Best.1 then Candidate
      else Best end
   end

   fun {ApplyTransactionForPeak T Balances Peak}
      local
         OldSender = {CondSelect Balances T.sender 0}
         OldReceiver = {CondSelect Balances T.receiver 0}
         NewSenderBalance = OldSender - T.value
         NewReceiverBalance = OldReceiver + T.value
         NewBalances =
            {AdjoinAt {AdjoinAt Balances T.sender NewSenderBalance}
             T.receiver NewReceiverBalance}
         PeakAfterSender = {BetterPeak T.sender#NewSenderBalance Peak}
         PeakAfterReceiver = {BetterPeak T.receiver#NewReceiverBalance PeakAfterSender}
      in
         NewBalances#PeakAfterReceiver
      end
   end

   fun {MoneyPeakTransactions Transactions Balances Peak}
      case Transactions of nil then Balances#Peak
      [] T|R then
         local Res = {ApplyTransactionForPeak T Balances Peak} in
            {MoneyPeakTransactions R Res.1 Res.2}
         end
      end
   end

   fun {MoneyPeakBlocks Blockchain Balances Peak}
      case Blockchain of nil then Peak
      [] B|R then
         local Res = {MoneyPeakTransactions B.transactions Balances Peak} in
            {MoneyPeakBlocks R Res.1 Res.2}
         end
      end
   end

   fun {MoneyPeak Blockchain}
      local Peak = {MoneyPeakBlocks Blockchain balances none} in
         if Peak == none then ~1 else Peak end
      end
   end
end
