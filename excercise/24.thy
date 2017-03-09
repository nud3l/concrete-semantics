theory 24
  imports Main
begin
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (y # ys) x = y # (snoc ys x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (y # ys) = snoc (reverse ys) y"

lemma reverse_proof: "reverse (reverse xs) = xs"
  apply(induction xs)
  apply(auto)  
  
lemma reverse_snoc: "reverse (snoc (reverse xs) y) = y # xs"
  by (induct xs) auto
    
lemma reverse_rev:"reverse (reverse xs) = xs"
  by (induct xs) (auto simp add: reverse_snoc)

find_theorems "rev (rev _) = _"

thm rev_rev_ident
theorem "reverse (reverse xs) = xs" by (simp add: reverse_rev)

end
  