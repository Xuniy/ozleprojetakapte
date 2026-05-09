functor
export
   decode:Decode
   executeBlockchain:ExecuteBlockchain
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

   fun {Contains X L}
      case L of nil then false
      [] H|T then
         if H == X then true else {Contains X T} end
      end
   end

   fun {AddToDenylist Sender Denylist}
      if {Contains Sender Denylist} then Denylist else Sender|Denylist end
   end

   fun {RegisterSender Sender Counts Denylist}
      local
         OldCount = {CondSelect Counts Sender 0}
         NewCount = OldCount + 1
         NewCounts = {AdjoinAt Counts Sender NewCount}
         NewDenylist =
            if NewCount >= 3 then {AddToDenylist Sender Denylist}
            else Denylist end
      in
         NewCounts#NewDenylist
      end
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
         S = T.sender R = T.receiver V = T.value
         OldS = {CondSelect State S user(balance:0 nonce:0)}
         OldR = {CondSelect State R user(balance:0 nonce:0)}
         NS = user(balance: OldS.balance - V nonce: OldS.nonce + 1)
         NR = user(balance: OldR.balance + V nonce: OldR.nonce)
      in
         {AdjoinAt {AdjoinAt State S NS} R NR}
      end
   end

   fun {CheckBlockTransactions Trans State Num AccEffort Denylist Counts}
      case Trans of nil then nil#Denylist
      [] T|Reste then
         if T.block_number == Num then
            if {Contains T.sender Denylist} then
               {CheckBlockTransactions Reste State Num AccEffort Denylist Counts}
            else
               local
                  E = {Effort T 1 1}
                  IsValid =
                     {Valid_transaction T State} andthen (AccEffort + E) =< 300
                  NextState =
                     if IsValid then {NewState State T} else State end
                  NextEffort =
                     if IsValid then AccEffort + E else AccEffort end
                  Updated = {RegisterSender T.sender Counts Denylist}
                  Rec =
                     {CheckBlockTransactions
                      Reste NextState Num NextEffort Updated.2 Updated.1}
               in
                  if IsValid then (T|Rec.1)#Rec.2 else Rec end
               end
            end
         else
            {CheckBlockTransactions Reste State Num AccEffort Denylist Counts}
         end
      end
   end

   fun {CreateBlock Transactions State Num PrevHash Denylist}
      local
         Checked = {CheckBlockTransactions Transactions State Num 0 Denylist counts}
         ValidT = Checked.1
         NewDenylist = Checked.2
         B = block(number: Num previousHash: PrevHash transactions: ValidT)
      in
         {Adjoin B block(hash: {BlockHash B})}#NewDenylist
      end
   end

   fun {UpdateStateWithList State Lst}
      case Lst of nil then State
      [] H|T then {UpdateStateWithList {NewState State H} T}
      end
   end

   fun {BuildChain State Trans Num PrevHash Denylist}
      local Created = {CreateBlock Trans State Num PrevHash Denylist}
         B = Created.1
         NextDenylist = Created.2
      in
         if B.transactions == nil then nil#State
         else
            local
               NextS = {UpdateStateWithList State B.transactions}
               Rec = {BuildChain NextS Trans Num+1 B.hash NextDenylist}
            in
               (B | Rec.1)#Rec.2
            end
         end
      end
   end

   Tableau_Sharelock=tableau(10:97 11:98 12:99 13:100 14:101 15:102 16:103 17:104 18:105 19:106 20:107 21:108 22:109 23:110 24:111 25:112 26:113 27:114 28:115 29:116 30:117 31:118 32:119 33:120 34:121 35:122 36:32)

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

   fun {Decode BChain}
      {Flatten
       case BChain of nil then nil
       [] B|R then {Phrase B.hash} | {Decode R}
       end}
   end

   proc {ExecuteBlockchain Genesis Transactions FinalState FinalBlockchain}
      local
         S0 = {AdaptGenesis Genesis}
         TransWithEffort =
            {Map Transactions fun {$ T} {Adjoin T transition(effort:{Effort T 1 1})} end}
         Res = {BuildChain S0 TransWithEffort 0 0 nil}
      in
         FinalBlockchain = Res.1
         FinalState = Res.2
      end
   end
end
