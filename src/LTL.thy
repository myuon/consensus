theory LTL
  imports Main
begin

datatype 'a LTL
  = Latom 'a
  | Ltrue
  | Lor "'a LTL" "'a LTL" (infixl "\<or>t" 81)
  | Lnot "'a LTL" ("\<not>t _" [85] 85)
  | Lnext "'a LTL" ("\<circle> _" [88] 87)
  | Luntil "'a LTL" "'a LTL" (infixr "\<union>t" 83)

definition Land (infixl "\<and>t" 82) where
  "Land p q = \<not>t (\<not>t p \<or>t \<not>t q)"

definition Limp (infixr "\<rightarrow>t" 80) where
  "Limp p q = \<not>t p \<or>t q"

definition Liff (infixl "\<leftrightarrow>t" 80) where
  "Liff p q = (p \<rightarrow>t q) \<and>t (q \<rightarrow>t p)"

definition Lfalse where
  "Lfalse = \<not>t Ltrue"

definition Lrelease (infixr "Rt" 83) where
  "Lrelease p q = \<not>t (\<not>t p \<union>t \<not>t q)"

definition Lfinally ("\<diamond> _" [88] 87) where
  "Lfinally p = Ltrue \<union>t p"

definition Lglobally ("\<box> _" [88] 87) where
  "Lglobally p = Lfalse Rt p"

fun shift :: "(nat \<Rightarrow> 'a set) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'a set)" where
  "shift w n = (\<lambda>k. w (n + k))"

primrec kripke_semantics :: "(nat \<Rightarrow> 'a set) \<Rightarrow> 'a LTL \<Rightarrow> bool" ("_ \<Turnstile> _" [80,80] 80) where
  "w \<Turnstile> Latom p = (p \<in> w 0)"
| "w \<Turnstile> Ltrue = True"
| "w \<Turnstile> p \<or>t q = (w \<Turnstile> p \<or> w \<Turnstile> q)"
| "w \<Turnstile> \<not>t p = (\<not> w \<Turnstile> p)"
| "w \<Turnstile> \<circle> p = shift w 1 \<Turnstile> p"
| "w \<Turnstile> p \<union>t q = (\<exists>i \<ge> 0. shift w i \<Turnstile> q \<and> (\<forall>k. 0 \<le> k \<and> k < i \<longrightarrow> shift w k \<Turnstile> p))"

definition valid ("\<Turnstile> _" [80] 80) where
  "\<Turnstile> p = (\<forall>w. w \<Turnstile> p)"

lemma notF_iff_G: "\<Turnstile> (\<not>t \<diamond> (\<not>t p)) = \<Turnstile> \<box> p"
  unfolding Lfinally_def Lglobally_def Lrelease_def Lfalse_def valid_def
  apply simp
  done

(* Examples *)

datatype Color = red | green | yellow

locale traffic =
  assumes red_to_green: "\<circle> (Latom red) = Latom green"
  and green_to_yellow: "\<circle> (Latom green) = Latom yellow"
  and yellow_to_red: "\<circle> (Latom yellow) = Latom red"

lemma (in traffic) "\<Turnstile> \<circle> (Latom green) \<rightarrow>t \<diamond> (Latom red)"
  using red_to_green by auto

end
