theory Paxos
imports Main LTL
begin

record 'v Propose =
  valPropose :: 'v

record Prepare =
  balPrepare :: nat

record 'v Promise =
  rndPromise :: nat
  vrndPromise :: "nat option"
  vvalPromise :: "'v option"

record 'v Accept =
  iAccept :: nat
  vAccept :: 'v

record 'v Learn =
  iLearn :: nat
  vLearn :: 'v

datatype 'v Message
  = Propose "'v Propose"
  | Prepare Prepare
  | Promise "'v Promise"
  | Accept "'v Accept"
  | Learn "'v Learn"

record 'v Proposer =
  crndProposer :: nat
  cvalProposer :: 'v
  PProposer :: "(nat option \<times> 'v option) set"

record 'v Acceptor =
  rndAcceptor :: "nat option"
  vrndAcceptor :: "nat option"
  vvalAcceptor :: "'v option"

record 'v Learner =
  VLearner :: "(nat \<times> 'v) list"

record 'v Paxos =
  msgs :: "'v Message set"
  proposer :: "'v Proposer"
  acceptors :: "'v Acceptor list"
  learner :: "'v Learner"
  chosen :: "'v option"
  proposed :: "'v set"

locale Paxos =
  fixes P :: "('v, 'p) Paxos_scheme" (structure)
  and pickNextRound
  and pick

  assumes proposer_propose: "\<exists>val.
  \<Turnstile>
    Latom (Propose \<lparr> valPropose = val \<rparr> \<in> msgs P) \<union>t
    Latom (
      let crnd_next = pickNextRound (crndProposer (proposer P)) in
      Prepare \<lparr> balPrepare = crnd_next \<rparr> \<in> msgs P \<and>
      val \<in> proposed P \<and>
      proposer P = \<lparr> crndProposer = crnd_next, cvalProposer = val, PProposer = {} \<rparr>
    )
  "
  and proposer_promise: "\<exists>rnd vrnd vval.
  \<Turnstile>
    Latom (
      Promise \<lparr> rndPromise = rnd, vrndPromise = vrnd, vvalPromise = vval \<rparr> \<in> msgs P \<and>
      crndProposer (proposer P) = rnd
    ) \<union>t
    Latom (
      (vrnd,vval) \<in> PProposer (proposer P)
    )
  "
  and proposer_accept: "\<exists>ps.
  \<Turnstile>
    Latom (
      PProposer (proposer P) = ps \<and>
      card (PProposer (proposer P)) \<ge> size (acceptors P) - size (acceptors P) div 2
    ) \<union>t
    Latom (
      let j = Max (these {vrnd. (vrnd,vval) \<in> ps}) in
      if j \<ge> 0 then cvalProposer (proposer P) = pick (snd ` {xy. xy \<in> ps \<and> fst xy = Some j}) else True \<and>
      Accept \<lparr> iAccept = crndProposer (proposer P), vAccept = cvalProposer (proposer P) \<rparr> \<in> msgs P
    )
  "

  assumes acceptor_prepare: "\<exists>prnd acc.
  \<Turnstile>
    Latom (
      Prepare \<lparr> balPrepare = prnd \<rparr> \<in> msgs P \<and>
      map_option (\<lambda>rnd. prnd > rnd) (rndAcceptor (acceptors P ! acc)) = Some(True)
    ) \<union>t
    Latom (
      let acceptor = acceptors P ! acc in
      Promise \<lparr> rndPromise = prnd, vrndPromise = vrndAcceptor acceptor, vvalPromise = vvalAcceptor acceptor \<rparr> \<in> msgs P \<and>
      rndAcceptor (acceptors P ! acc) = Some(prnd)
    )
  "
  and acceptor_accept: "\<exists>i v acc.
  \<Turnstile>
    Latom (
      Accept \<lparr> iAccept = i, vAccept = v \<rparr> \<in> msgs P \<and>
      map_option (\<lambda>rnd. i \<ge> rnd) (rndAcceptor (acceptors P ! acc)) = Some(True)
    ) \<union>t
    Latom (
      acceptors P ! acc = \<lparr> rndAcceptor = Some i, vrndAcceptor = Some i, vvalAcceptor = Some v \<rparr> \<and>
      Learn \<lparr> iLearn = i, vLearn = v \<rparr> \<in> msgs P
    )
  "
  
  assumes learner_learn: "\<exists>i v vs.
  \<Turnstile>
    Latom (
      Learn \<lparr> iLearn = i, vLearn = v \<rparr> \<in> msgs P \<and>
      VLearner (learner P) = vs
    ) \<union>t
    Latom (
      VLearner (learner P) = (i,v) # vs
    )
  "
  and learner_choose: "\<exists>i v.
  \<Turnstile>
    Latom (
      size (find (\<lambda>pair. pair = (i,v)) (VLearner (learner P))) \<ge> size (acceptors P) - size (acceptors P) div 2
    ) \<union>t
    Latom (
      chosen P = Some(v)
    )
  "

theorem CS1: "\<Turnstile> \<box> (\<not>t Latom (Option.is_none (chosen P)) \<rightarrow>t Latom (the (chosen P) \<in> proposed P))"
  sorry

theorem CS2: "\<not> (\<exists>v1 v2. v1 \<noteq> v2 \<and> \<Turnstile> Latom (chosen P = Some(v1)) \<union>t Latom (chosen P = Some(v2)))"
  sorry

theorem CS3: "\<exists>i. \<Turnstile> \<box> (\<not>t Latom (Option.is_none (chosen P)) \<rightarrow>t Latom (Learn \<lparr> iLearn = i, vLearn = the (chosen P) \<rparr> \<in> msgs P))"
  sorry

end
