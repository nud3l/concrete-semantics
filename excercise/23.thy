theory 23
imports Main
begin
fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
  "count [] x = 0" |
  "count (x # xs) y = (if x = y then Suc (count xs y) else (count xs y))"

lemma count: "count xs x \<le> length xs"
  apply(induction xs)
  apply(auto)
  done  
end
  