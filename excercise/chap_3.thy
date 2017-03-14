theory chap_3
imports Main
begin
(* 3.1 *)

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N a) s = a" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N a) = N a" |
"asimp_const (V x) = V x" |
"asimp_const (Plus p q) = 
 (case (asimp_const p, asimp_const q) of 
  (N a, N b) \<Rightarrow> N (a+b) |
  (x, y) \<Rightarrow> Plus x y)"

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N a) (N b) = N (a+b)" |
"plus p (N i) = (if i = 0 then p else Plus p (N i))" |
"plus (N i) p = (if i = 0 then p else Plus (N i) p)" |
"plus p q = (Plus p q)"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N a) = N a" |
"asimp (V x) = V x" |
"asimp (Plus p q) = plus (asimp p) (asimp q)"

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N a) = True" |
"optimal (V x) = True" |
"optimal (Plus (N a) (N b)) = False" | 
"optimal (Plus x y) = ((optimal x) \<and> (optimal y))"

theorem asimp_const_optimal: "optimal (asimp_const a)"
apply (induction a)
apply (auto split: aexp.split)
done

(* 3.2 *)

fun plus_ex :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus_ex (N a) (N b) = N (a+b)" |
"plus_ex (Plus p (N a)) (N b) = Plus p (N (a+b))" |
"plus_ex (N b) (Plus p (N a)) = Plus p (N (a+b))" |
"plus_ex (Plus p (N a)) q = Plus (Plus p q) (N a)" |
"plus_ex q (Plus p (N a)) = Plus (Plus p q) (N a)" |
"plus_ex p (N i) = (if i = 0 then p else Plus p (N i))" |
"plus_ex (N i) p = (if i = 0 then p else Plus p (N i))" |
"plus_ex p q = (Plus p q)"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp (N a) = N a" |
"full_asimp (V x) = V x" |
"full_asimp (Plus p q) = plus_ex (full_asimp p) (full_asimp q)"

value "full_asimp (Plus (Plus ((Plus (V ''x'') (N 7))) (V ''x'')) (N 5))" 

lemma aval_plus_ex: "aval (plus_ex p q) s = aval p s + aval q s"
apply (induction rule:plus_ex.induct)
apply (auto)
done

theorem "aval (full_asimp p) s = aval p s"
apply (induction p)
apply (auto simp add:aval_plus_ex)
done

(* 3.3 *)

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (N k) = (N k)" |
"subst x a (V y) = (if x = y then a else (V y))" |
"subst x a (Plus p q) = Plus (subst x a p) (subst x a q)"

theorem aval_subst[simp]:  "aval (subst x a e) s = aval e (s(x:=aval a s))"
apply (induction e)
apply (auto)
done 

theorem "aval a s = aval b s \<longrightarrow> aval (subst x a e) s = aval (subst x b e) s"
apply (auto)
done

(* 3.4 *)

datatype aexpm = Nm int | Vm vname | Plusm aexpm aexpm | Timesm aexpm aexpm

fun avalm :: "aexpm \<Rightarrow> state \<Rightarrow> val" where
"avalm (Nm a) s = a" |
"avalm (Vm x) s = s x" |
"avalm (Plusm a b) s = avalm a s + avalm b s" |
"avalm (Timesm a b) s = avalm a s * avalm b s"

fun plusm :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
"plusm (Nm a) (Nm b) = Nm (a+b)" |
"plusm p (Nm i) = (if i = 0 then p else Plusm p (Nm i))" |
"plusm (Nm i) p = (if i = 0 then p else Plusm (Nm i) p)" |
"plusm p q = (Plusm p q)"

fun timesm :: "aexpm \<Rightarrow> aexpm \<Rightarrow> aexpm" where
"timesm (Nm a) (Nm b) = Nm (a*b)" |
"timesm p (Nm i) = (if i = 0 then (Nm 0) else if i = 1 then p else Timesm p (Nm i))" |
"timesm (Nm i) p = (if i = 0 then (Nm 0) else if i = 1 then p else Timesm p (Nm i))" |
"timesm p q = (Timesm p q)"

fun asimpm :: "aexpm \<Rightarrow> aexpm" where
"asimpm (Nm a) = Nm a" |
"asimpm (Vm x) = Vm x" |
"asimpm (Plusm p q) = plusm (asimpm p) (asimpm q)" |
"asimpm (Timesm p q) = timesm (asimpm p) (asimpm q)"

lemma avalm_plus[simp]: "avalm (plusm p q) s = avalm p s + avalm q s"
apply (induction rule:plusm.induct)
apply (auto)
done

lemma avalm_times[simp]: "avalm (timesm p q) s = avalm p s * avalm q s"
apply (induction rule:timesm.induct)
apply (auto)
done

theorem "avalm (asimpm p) s = avalm p s"
apply (induction p)
apply (auto)
done 

(*  3.5 *)

datatype aexp2 = N2 int | V2 vname | PlusPlus2 vname | Plus2 aexp2 aexp2 | 
 Times2 aexp2 aexp2 | Div2 aexp2 aexp2 

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> (val \<times> state) option" where
"aval2 (N2 a) s = Some (a, s)" |
"aval2 (V2 x) s = Some (s x, s)" |
"aval2 (PlusPlus2 x) s = Some (s x, s(x:= 1 + (s x)))" |
"aval2 (Plus2 a b) s = 
 (case (aval2 a s, aval2 b s) of 
  (None, Some q) \<Rightarrow> None |
  (Some p, None) \<Rightarrow> None |
  (Some p, Some q) \<Rightarrow> Some ((fst p + fst q), (\<lambda>x.((snd p) x) + ((snd q) x) - (s x))))" |
"aval2 (Times2 a b) s = 
 (case (aval2 a s, aval2 b s) of 
  (None, Some q) \<Rightarrow> None |
  (Some p, None) \<Rightarrow> None |
  (Some p, Some q) \<Rightarrow> Some ((fst p * fst q), (\<lambda>x.((snd p) x) + ((snd q) x) - (s x))))" |
"aval2 (Div2 a b) s =
 (case (aval2 a s, aval2 b s) of 
  (None, Some q) \<Rightarrow> None |
  (Some p, None) \<Rightarrow> None |
  (Some p, Some q) \<Rightarrow> 
   (if fst q = 0 then 
    None 
   else Some ((fst p div fst q), (\<lambda>x.((snd p) x) + ((snd q) x) - (s x)))))"
 
  
end
  