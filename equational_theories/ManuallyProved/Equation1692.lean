import Mathlib

-- https://leanprover.zulipchat.com/user_uploads/3121/ASjTo5huToAvNGcg7pOGOOSy/Equation1692.pdf

#synth AddGroup (∀ n: ℕ, ℤ)

-- TODO -  only finitely many entries are non-zero?
abbrev G := (ℕ →₀ ℚ)

noncomputable abbrev n_q_basis := Finsupp.basisSingleOne (R := ℚ) (ι := ℕ)
noncomputable abbrev basis_n := DFunLike.coe n_q_basis
noncomputable abbrev all_basis := (λ n: ℕ => (n, basis_n n)) '' Set.univ

-- lemma basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis

theorem foo: 1 = 1 := by
  -- Actual start of proof
  let s_i := λ i: ℕ => {val ∈ all_basis | val.1 ≡ 2^i [MOD 2^(i + 1)] }
  have no_overlap: ∀ i j: ℕ, i < j → s_i i ∩ s_i j = ∅ := by
    intro i j i_lt_j

    rw [Set.inter_def]
    by_contra!
    simp at this
    obtain ⟨⟨k, e_k⟩, ⟨e_k_in_i, e_k_in_j⟩⟩ := this

    have e_k_in_i: k ≡ 2^i [MOD 2^(i + 1)] := by
      simp [s_i] at e_k_in_i
      exact e_k_in_i.2

    have e_k_in_j: k ≡ 2^j [MOD 2^(j + 1)] := by
      simp [s_i] at e_k_in_j
      exact e_k_in_j.2

    have mod_imp_factor: ∀ k i : ℕ, k ≡ 2^i [MOD 2^(i + 1)] → k.factorization 2 = i := by
      intro k i e_k_in_i

      have k_le_first: 2^i ≤ k := by
        rw [Nat.ModEq] at e_k_in_i
        have two_pow_lt: 2^i < 2^(i + 1) := by
          apply Nat.pow_lt_pow_succ
          simp
        rw [Nat.mod_eq_of_lt two_pow_lt] at e_k_in_i
        have k_mod_lt: k % 2 ^ (i + 1)< (2^(i+1)) := by
          apply Nat.mod_lt
          simp

        by_contra!
        have k_lt_2i_plus: k < 2^(i+1) := by
          exact Nat.lt_trans this two_pow_lt

        have bar := Nat.mod_eq_of_lt k_lt_2i_plus
        rw [bar] at e_k_in_i
        linarith

      apply Nat.ModEq.symm at e_k_in_i
      apply (Nat.modEq_iff_dvd' k_le_first).mp at e_k_in_i
      obtain ⟨c, hc⟩ := e_k_in_i

      have k_i_eq_sum: k = 2^i + 2^(i + 1) * c := by
        apply Nat.eq_add_of_sub_eq k_le_first  at hc
        rw [Nat.add_comm] at hc
        exact hc


      have k_i_factor: k = 2^i * (1 + 2 * c) := by
        rw [k_i_eq_sum]
        ring

      have two_factor_i: (2^i * (1 + 2 * c)).factorization 2 = i := by
        rw [Nat.factorization_mul]
        rw [Nat.Prime.factorization_pow (Nat.prime_two)]
        simp [Nat.factorization_eq_zero_of_not_dvd]
        simp
        simp

      rw [← k_i_factor] at two_factor_i
      exact two_factor_i


    have i_factor := mod_imp_factor k i e_k_in_i
    have j_factor := mod_imp_factor k j e_k_in_j
    rw [i_factor] at j_factor
    linarith

  have si_union_basis: ⋃ i, s_i i = all_basis := by
    ext ⟨k, e_k⟩
    refine ⟨?_, ?_⟩
    intro e_k_in_union
    simp at e_k_in_union
    obtain ⟨i, e_k_in_i⟩ := e_k_in_union
    simp [s_i] at e_k_in_i
    exact e_k_in_i.1

    intro e_k_in_basis
    rw [Set.mem_iUnion]
    simp [s_i]
    refine ⟨e_k_in_basis, ?_⟩
    by_cases k_even_odd: Even k
    . obtain ⟨j, hj⟩ := k_even_odd
      have k_neq_zero: k ≠ 0 := by sorry
      have k_eq_2j: k = 2 * j := by
        rw [hj]
        linarith
      use k.log2
      apply Nat.ModEq.symm
      rw [Nat.modEq_iff_dvd']
      refine ⟨?z, ?_⟩
      sorry




      --apply Nat.sub_eq_of_eq_add





      have k_factor: k = 2^(k.log2) * (k / 2^(k.log2)) := by

        sorry



      sorry
      sorry
      --apply Nat.log2_self_le k_neq_zero
    . have k_odd: Odd k := by
        exact Nat.not_even_iff_odd.mp k_even_odd
      obtain ⟨j, hj⟩ := k_odd
      use 0
      simp
      have k_minus_eq: k - 1 = 2 * j := by
        rw [hj]
        simp
      apply Nat.ModEq.symm
      rw [Nat.modEq_iff_dvd']
      have two_div: 2 ∣ k - 1 := by
        exact Dvd.intro j (id (Eq.symm k_minus_eq))
      exact two_div
      linarith







  rfl

noncomputable def xSeq (n: ℕ): G := basis_n n

class TreeData where
  a: G
  b: G

deriving DecidableEq

inductive ReverseTree where
| root: ReverseTree
| left: ReverseTree → ReverseTree
| right: ReverseTree → ReverseTree
  deriving DecidableEq

def newNum: ReverseTree → ℕ
  | ReverseTree.root => 2
  | ReverseTree.left prev => 2 * (newNum prev) - 1
  | ReverseTree.right prev => 2 * (newNum prev)

noncomputable def ReverseTree.getData: ReverseTree → TreeData
| ReverseTree.root => {a := xSeq 0, b := xSeq 1}
| ReverseTree.left base => {a := -base.getData.b, b := xSeq (newNum base)}
| ReverseTree.right base => {a := xSeq (newNum base), b := base.getData.a - base.getData.b}

def treeDepth: ReverseTree → ℕ
| ReverseTree.root => 0
| ReverseTree.left t => 1 + treeDepth t
| ReverseTree.right t => 1 + treeDepth t


--noncomputable def mkRoot: ReverseTree := ReverseTree.root
--noncomputable def mkLeft (base: ReverseTree): ReverseTree := ReverseTree.left {a := -base.getData.b, b := xSeq (newNum base)} base
--noncomputable def mkRight (base: ReverseTree): ReverseTree := ReverseTree.right {a := xSeq (newNum base), b := base.getData.a - base.getData.b} base

noncomputable def my_set: Finset G := ({xSeq 0, xSeq 1} : Finset G)

lemma tree_linear_comb_left (t: ReverseTree): (∃ s: Finset ℕ, ∃ g: ℕ -> ℚ, t.getData.a = ∑ i ∈ s, g i • basis_n i) ∧ (∃ s: Finset ℕ, ∃ g: ℕ -> ℚ, t.getData.b = ∑ i ∈ s, g i • basis_n i)  := by
  induction t with
  | root =>
    refine ⟨?_, ?_⟩

    use {0, 1}
    use fun i => if i = 0 then 1 else 0
    simp
    simp [ReverseTree.getData]
    simp [xSeq, basis_n]

    use {0, 1}
    use fun i => if i = 0 then 0 else 1
    simp
    simp [ReverseTree.getData]
    simp [xSeq, basis_n]
  | left prev h_prev =>
    simp [ReverseTree.getData]
    refine ⟨?_,?_⟩
    . obtain ⟨_, ⟨s, g, h_g⟩⟩ := h_prev
      refine ⟨s, ?_, ?_⟩
      use fun i => -1 * g i
      simp
      simp [basis_n] at h_g
      apply h_g
    . use {newNum prev}
      use fun i => if i = newNum prev then 1 else 0
      simp
      simp [xSeq, basis_n]
  | right prev h_prev =>
    simp [ReverseTree.getData]
    refine ⟨?_,?_⟩
    . use {newNum prev}
      use fun i => if i = newNum prev then 1 else 0
      simp
      simp [xSeq, basis_n]
    have sub_in_span: (prev.getData.a - prev.getData.b) ∈ Submodule.span ℚ (Set.range basis_n) := by
      apply Basis.mem_span
    have foo := (Finsupp.mem_span_iff_linearCombination ℚ (Set.range basis_n) (prev.getData.a - prev.getData.b)).mp sub_in_span
    obtain ⟨l, hl⟩ := foo
    simp [Finsupp.linearCombination_apply] at hl
    rw [Finsupp.sum] at hl



lemma tree_linear_independent (t: ReverseTree): LinearIndependent ℚ ![t.getData.a, t.getData.b] := by
  simp [LinearIndependent.pair_iff]
  intro p q eq_zero
  cases t with
  | root =>
    simp [ReverseTree.getData] at eq_zero
    have basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis
    rw [linearIndependent_iff'] at basis_indep
    specialize basis_indep {0, 1} fun g => if g = 0 then p else q
    simp only [one_smul, Finset.mem_singleton, zero_ne_one,
      not_false_eq_true, Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert, one_ne_zero,
      imp_false, not_or] at basis_indep
    simp only [↓reduceIte, Finsupp.smul_single, smul_eq_mul, mul_one,
      forall_eq_or_imp, forall_eq, one_ne_zero] at basis_indep
    rw [xSeq, basis_n] at eq_zero
    rw [xSeq, basis_n] at eq_zero
    exact basis_indep eq_zero
  | left prev =>
    simp [ReverseTree.getData] at eq_zero


    sorry
  | right a prev => sorry





-- inductive MyTree {α: Type} where
--   | root: TreeData (α := α) 0 → MyTree
--   | left (n: ℕ) (hn: n > 0): TreeData (n - 1) → MyTree
--   | right (n: ℕ) (hn: n > 0): TreeData (n - 1) → MyTree


-- def treeAt(n: ℕ ): MyTree (α := String) :=
--   MyTree.left { MyTree.root {a := "a", b := "b"}
