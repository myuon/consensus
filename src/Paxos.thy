theory Paxos
imports Main
begin

datatype Request = Propose int | Prepare int | Promise int int int | Accept int int | Learn int int

datatype ProposerID = ProposerID "nat"
datatype AcceptorID = AcceptorID "nat"
datatype LearnerID = LearnerID "nat"

datatype Response = Nothing | SendAcceptors Request | SendBackProposer Request | SendLearners Request

datatype Node = NProposer ProposerID | NAcceptor AcceptorID | NLearner LearnerID

record Proposer =
  crnd :: "int"
  cval :: int
  P :: "(int \<times> int) set"
  pickNextRound :: "int \<Rightarrow> int"
  acceptors :: "AcceptorID set"
  n :: "nat"
  f :: "nat"

fun newProposer :: "AcceptorID set \<Rightarrow> Proposer" where
  "newProposer acc = \<lparr>
    crnd = -1,
    cval = 0,
    P = {},
    pickNextRound = \<lambda>x. x+1,
    acceptors = acc,
    n = card acc,
    f = ((card acc - 1) mod 2)
  \<rparr>"

fun updateProposer :: "Request => Proposer => Proposer \<times> Response" where
  "updateProposer (Propose val) p = (let next_crnd = pickNextRound p (crnd p) in (p \<lparr> crnd := next_crnd \<rparr>, SendAcceptors (Prepare next_crnd)))"
| "updateProposer (Promise rnd vrnd vval) p = (if rnd = crnd p then p \<lparr> P := P p \<union> {(vrnd, vval)} \<rparr> else p, Nothing)"
| "updateProposer _ _ = undefined"

fun checkProposer :: "(int set \<Rightarrow> int) \<Rightarrow> Proposer \<Rightarrow> Proposer \<times> Response" where
  "checkProposer pick p = (if card (P p) \<ge> n p - f p
    then
      let j = Max (fst ` {x. x \<in> P p}) in
      if j \<ge> 0
        then (p \<lparr> cval := pick {vval. (j,vval) \<in> P p} \<rparr>, SendAcceptors (Accept (crnd p) (cval p)))
        else (p, Nothing)
    else (p, Nothing)
  )"

record Acceptor =
  rnd :: int
  vrnd :: int
  vval :: int

fun updateAcceptor :: "Request \<Rightarrow> Acceptor \<Rightarrow> Acceptor \<times> Response" where
  "updateAcceptor (Prepare prnd) p = (if prnd > rnd p
    then (p \<lparr> rnd := prnd \<rparr>, SendBackProposer (Promise prnd (vrnd p) (vval p)))
    else (p, Nothing)
  )"
| "updateAcceptor (Accept i v) p = (if i \<ge> rnd p
    then (p \<lparr> rnd := i, vrnd := i, vval := v \<rparr>, SendLearners (Learn i v))
    else (p, Nothing)
  )"
| "updateAcceptor _ _ = undefined"

record Learner =
  V :: "(int \<times> int) set"

fun updateLearner :: "Request \<Rightarrow> Learner \<Rightarrow> Learner" where
  "updateLearner (Learn i v) p = p \<lparr> V := V p \<union> {(i,v)} \<rparr>"
| "updateLearner _ _ = undefined"

fun isChosen :: "nat \<Rightarrow> nat \<Rightarrow> Learner \<Rightarrow> bool" where
  "isChosen n' f' p = (card (V p) \<ge> n' - f')"

record Paxos =
  proposers :: "ProposerID set"
  acceptors :: "AcceptorID set"
  learners :: "LearnerID set"

end
