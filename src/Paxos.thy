theory Paxos
imports Main LTL
begin

(* ============== Paxos ============== *)

record 'v Proposer =
  crnd :: nat
  cval :: 'v
  pairs :: "(nat\<times>nat) set"

record Acceptor =
  rnd :: nat
  vrnd :: nat
  vval :: nat

record Learner =
  learned :: "(nat\<times>nat) set"

record 'v ProposeM =
  val :: 'v

record PrepareM =
  prnd :: nat

record PromiseM =
  rnd :: nat
  vrnd :: nat
  vval :: nat

record AcceptM =
  index :: nat
  aval :: nat

record LearnM =
  index :: nat
  chosen :: nat

datatype 'v Message
  = Propose "'v ProposeM"
  | Prepare PrepareM
  | Promise PromiseM
  | Accept AcceptM
  | Learn LearnM

fun isPropose where
  "isPropose (Propose _) = True"
| "isPropose _ = False"

record 'v Paxos =
  messages :: "('v Message) set"
  proposer :: "'v Proposer"
  acceptors :: "Acceptor list"
  learner :: "Learner"

locale Paxos =
  fixes P :: "('v,'p) Paxos_scheme" (structure)
  (* crash failure *)
  and cf :: nat
  (* pick function *)
  and pickNextRound :: "nat \<Rightarrow> nat"
  and V :: "'v set"

  assumes enough_acceptors: "size (acceptors P) \<ge> 2 * cf + 1"
  and init: "\<Turnstile> Latom (card (messages P) = 0)"
  and prepare: "\<Turnstile> Latom ({m. m \<in> messages P \<and> isPropose m} \<noteq> {})"
  and phase1a: "\<exists>propose. \<Turnstile> \<circle> Latom (Propose propose \<in> messages P)
     \<longrightarrow> (let crnd_next = pickNextRound (crnd (proposer P)) in 
     \<Turnstile> Latom (Prepare (PrepareM \<lparr> prnd = crnd_next \<rparr>) \<in> messages P)
     \<and> \<Turnstile> Latom (proposer P = \<lparr> crnd = crnd_next, cval = val propose, pairs = {} \<rparr>))"

end
