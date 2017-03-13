theory chap_2
  imports Main
begin
(* 2.1 *)
value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* 2.2 *)
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc(add m n)"
lemma add_02: "add m 0 = m"
  apply(induction m)
  apply(auto)
  done
thm add_02

lemma add_associative: "add(add n m) z = add n (add m z)"
  apply(induction n)
  apply(auto)
  done
thm add_associative      

lemma add_0[simp]: "add m 0 = m"
  by (induct m) simp_all
  
lemma add_gen[simp]: "add m (Suc n) = Suc (add m n)"
  by (induct m) simp_all
  
lemma add_commutative: "add k m = add m k"
  apply(induction k)
  apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
  "double m = add m m"

lemma "double m = add m m"
  apply(induction m)
  apply(auto)
  done
  
(* 2.3 *)
fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] x = 0" |
  "count (x # xs) y = (if x = y then Suc (count xs y) else (count xs y))"

lemma count: "count xs x \<le> length xs"
  apply(induction xs)
  apply(auto)
  done
  
(* 2.4 *)
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (y # ys) x = y # (snoc ys x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (y # ys) = snoc (reverse ys) y"
  
lemma reverse_snoc[simp]: "reverse (snoc xs y) = y # reverse xs"
  apply(induction xs)
   apply auto
  done
  
    
lemma reverse_proof: "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)  
done
    
find_theorems "rev (rev _) = _"

thm rev_rev_ident

(* 2.5 *)
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0" |
  "sum_upto (Suc n)  = Suc n + sum_upto n"

value "sum_upto 4 = 10"
  
lemma discrete_add: "sum_upto n = (n * (n + 1)) div 2"
  apply(induction n)
  apply(auto)
  done   

(* 2.6 *)
datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"
  
fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []" |
  "contents (Node l v r) = v # ((contents l) @ (contents r))"
  
fun treesum :: "nat tree \<Rightarrow> nat " where
  "treesum Tip = 0" |
  "treesum (Node l v r) = v + (treesum l) + (treesum r)"
  
  
lemma "listsum(contents t) = treesum t"
  apply(induction t)
  apply(auto)
  done
sorry

(* 2.7 *)
datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"
  
fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror (Tip v) = Tip v" |
  "mirror (Node l v r) = Node (mirror r) v (mirror l)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Tip v) = [v]" |
  "pre_order (Node l v r) = v # ((pre_order l) @ (pre_order r))"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Tip v) = [v]" |
  "post_order (Node l v r) = (post_order l) @ (post_order r) @ [v]"
  
lemma "pre_order (mirror t) = rev(post_order t)"
  apply(induction t)
  apply auto
  done 

(* 2.8 *)
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse c [] = []" |
  "intersperse c [v] = [v]" |
  "intersperse c (v#t) = v # c # (intersperse c t)"
  
(*value "intersperse(2,[]) = []"*)

(*value "intersperse(2,[4]) = [4]"*)

value "intersperse(2, [4,1,5,8])"

lemma "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs rule:intersperse.induct)
    apply(auto)
  done  
    
    
(* 2.9 *)
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "itadd 0 n = n" |
  "itadd (Suc m) n = itadd m (Suc n)"
  
lemma "itadd m n = add m n"
  apply(induction m arbitrary:n)
  apply auto
done
  
(* 2.10 *)
datatype tree0 = Tip | Node tree0 tree0

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node l r) = 1 + nodes l + nodes r"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc n) t = explode n (Node t t)"

theorem explode_exponential: "nodes (explode n t) = 2^n * nodes t + 2^n - 1"
apply (induction n arbitrary:t)
apply (auto simp add:algebra_simps)
done
  
(* 2.11 *)
datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var x = x" |
"eval (Const k) x = k" |
"eval (Add p q) x = eval p x + eval q x" |
"eval (Mult p q) x = eval p x * eval q x"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] y = 0" |
"evalp (x # xs) y = x + y * evalp xs y"

fun vsum :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"vsum [] xs = xs" |
"vsum xs [] = xs" |
"vsum (x # xs) (y # ys) = (x + y) # vsum xs ys"

fun scalar_mult :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"scalar_mult k [] = []" |
"scalar_mult k (x # xs) = k * x # scalar_mult k xs"

fun vmult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"vmult [] xs = []" |
"vmult (x # xs) ys = vsum (scalar_mult x ys) (0 # vmult xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const k) = [k]" |
"coeffs (Add p q) = vsum (coeffs p) (coeffs q)" |
"coeffs (Mult p q) = vmult (coeffs p) (coeffs q)"

lemma evalp_additive[simp]: "evalp (vsum xs ys) a = evalp xs a + evalp ys a"
apply (induction rule:vsum.induct)
apply (auto simp add:Int.int_distrib)
done

lemma eval_preserves_mult[simp]: "evalp (scalar_mult x ys) a = x * evalp ys a"
apply (induction ys)
apply (auto simp add:Int.int_distrib)
done 

lemma evalp_multiplicative[simp]: "evalp (vmult xs ys) a = evalp xs a * evalp ys a"
apply (induction xs)
apply (auto simp add:Int.int_distrib)
done 

theorem evalp_eval: "evalp (coeffs e) x = eval e x"
apply (induction e)
apply (auto)
done
  
end