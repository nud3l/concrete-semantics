theory 22
imports Main
begin
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

end
  