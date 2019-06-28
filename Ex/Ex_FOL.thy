theory Ex_FOL imports FOL
begin

class semigroup =
  fixes op :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"  (infixl "\<bullet>" 70)
  assumes assoc: "(x \<bullet> y) \<bullet> z = x \<bullet> (y \<bullet> z)"
begin

definition dup :: "'a \<Rightarrow> 'a" where "dup(x) = x \<bullet> x"
lemma dup_dup: "dup (dup(x)) = x \<bullet> x \<bullet> x \<bullet> x" by (simp only: dup_def assoc)

end

term semigroup.dup
thm semigroup.dup_def semigroup.dup_dup

end

