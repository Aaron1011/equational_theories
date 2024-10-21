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
    sorry
    -- ext ⟨k, e_k⟩
    -- refine ⟨?_, ?_⟩
    -- intro e_k_in_union
    -- simp at e_k_in_union
    -- obtain ⟨i, e_k_in_i⟩ := e_k_in_union
    -- simp [s_i] at e_k_in_i
    -- exact e_k_in_i.1

    -- intro e_k_in_basis
    -- rw [Set.mem_iUnion]
    -- simp [s_i]
    -- refine ⟨e_k_in_basis, ?_⟩
    -- by_cases k_even_odd: Even k
    -- . obtain ⟨j, hj⟩ := k_even_odd
    --   have k_neq_zero: k ≠ 0 := by sorry
    --   have k_eq_2j: k = 2 * j := by
    --     rw [hj]
    --     linarith
    --   use k.log2
    --   apply Nat.ModEq.symm
    --   rw [Nat.modEq_iff_dvd']
    --   refine ⟨?z, ?_⟩
    --   sorry




    --   --apply Nat.sub_eq_of_eq_add





    --   have k_factor: k = 2^(k.log2) * (k / 2^(k.log2)) := by

    --     sorry



    --   sorry
    --   sorry
    --   --apply Nat.log2_self_le k_neq_zero
    -- . have k_odd: Odd k := by
    --     exact Nat.not_even_iff_odd.mp k_even_odd
    --   obtain ⟨j, hj⟩ := k_odd
    --   use 0
    --   simp
    --   have k_minus_eq: k - 1 = 2 * j := by
    --     rw [hj]
    --     simp
    --   apply Nat.ModEq.symm
    --   rw [Nat.modEq_iff_dvd']
    --   have two_div: 2 ∣ k - 1 := by
    --     exact Dvd.intro j (id (Eq.symm k_minus_eq))
    --   exact two_div
    --   linarith







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

#synth Neg (ℕ →₀ ℚ)

noncomputable def my_set: Finset G := ({xSeq 0, xSeq 1} : Finset G)

lemma newnem_gt_one (t: ReverseTree): 1 < newNum t := by
  induction t with
  | root =>
    simp [newNum]
  | left prev h_prev =>
    simp [newNum]
    omega
  | right prev h_prev =>
    simp [newNum]
    linarith

lemma newnum_increasing (t: ReverseTree): newNum t < newNum (ReverseTree.left t) ∧ newNum t < newNum (ReverseTree.right t) := by
  induction t with
  | root =>
    simp [newNum]
  | left prev h_prev =>
    simp [newNum]
    have gt_zero: 1 < newNum prev := by
      exact newnem_gt_one prev
    refine ⟨?_, ?_⟩
    refine Nat.sub_lt_sub_right ?_ ?_
    linarith
    refine Nat.mul_lt_mul_of_pos_left ?left.refine_1.refine_2.h ?left.refine_1.refine_2.hk
    omega
    linarith
    omega
  | right prev h_prev =>
    simp [newNum]
    have gt_zero: 1 < newNum prev := by
      exact newnem_gt_one prev
    refine ⟨?_, ?_⟩
    omega
    omega

variable {M A : Type*}
variable [Zero A] [SMulZeroClass M A]

lemma tree_linear_comb (t: ReverseTree):
  (∃ g: ℕ -> ℚ, ∃ m: ℕ, m ≤  newNum t ∧ t.getData.a = ∑ i ∈ Finset.range m, g i • basis_n i) ∧
  (∃ g: ℕ -> ℚ, ∃ m: ℕ, m ≤ newNum t ∧ t.getData.b = ∑ i ∈ Finset.range m, g i • basis_n i) := by
  induction t with
  | root =>
    refine ⟨?_, ?_⟩
    use fun i => if i = 0 then 1 else 0
    simp [newNum]
    use 1
    simp
    simp [ReverseTree.getData]
    simp [xSeq, basis_n]
    rw [newNum]

    use fun i => if i = 1 then 1 else 0
    simp
    use 2
    simp [ReverseTree.getData]
    simp [xSeq, basis_n]

  | left prev h_prev =>
    simp only [ReverseTree.getData]
    refine ⟨?_,?_⟩
    . obtain ⟨_, ⟨g, m, m_le, h_g⟩⟩ := h_prev
      rw [newNum]
      have newnum_gt_one: 1 < newNum prev := newnem_gt_one prev
      have prev_lt_mul: newNum prev < 2 * newNum prev - 1 := by
        omega

      use fun i => -1 * if i ∈ Finset.range m then g i else 0
      use m
      simp [prev_lt_mul]
      simp only [basis_n] at h_g
      refine ⟨?_, ?_⟩
      apply le_trans m_le (le_of_lt prev_lt_mul)

      simp at h_g
      rw [neg_eq_iff_eq_neg]
      rw [← neg_one_zsmul]
      rw [← Finset.sum_zsmul]
      simp only [Finsupp.smul_single, smul_ite]
      simp
      rw [← Fin.sum_univ_eq_sum_range]
      simp



      rw [← Fin.sum_univ_eq_sum_range] at h_g
      exact h_g
    . obtain ⟨_, ⟨g, m, _⟩⟩ := h_prev
      rw [newNum]
      use fun i => if i = newNum prev then 1 else 0
      use (newNum prev) + 1
      refine ⟨?_, ?_⟩
      have newnum_gt_one: 1 < newNum prev := newnem_gt_one prev
      omega
      simp
      simp [xSeq, basis_n, n_q_basis]
  | right prev h_prev =>
    simp only [ReverseTree.getData]
    refine ⟨?_,?_⟩
    . obtain ⟨_, ⟨g, m, _⟩⟩ := h_prev
      rw [newNum]
      use fun i => if i = newNum prev then 1 else 0
      use (newNum prev) + 1
      refine ⟨?_, ?_⟩
      have newnum_gt_one: 1 < newNum prev := newnem_gt_one prev
      omega
      simp
      simp [xSeq, basis_n, n_q_basis]
    . obtain ⟨⟨g_l, m_l, m_l_le, h_g_l⟩, ⟨g, m, m_le, h_g⟩⟩ := h_prev
      have my_subset: Finset.range (m_l) ⊆ Finset.range (newNum prev) := by
        refine Finset.range_subset.mpr ?_
        linarith

      have my_subset_right: Finset.range (m) ⊆ Finset.range (newNum prev) := by
        refine Finset.range_subset.mpr ?_
        linarith

      rw [← Finset.sum_extend_by_zero] at h_g_l
      rw [Finset.sum_subset my_subset] at h_g_l


      rw [← Finset.sum_extend_by_zero] at h_g
      rw [Finset.sum_subset my_subset_right] at h_g

      rw [h_g_l, h_g]
      rw [← Finset.sum_sub_distrib]
      simp only [← ite_zero_smul]
      simp only [← sub_smul]
      use fun x => (if x ∈ Finset.range m_l then g_l x else 0) - (if x ∈ Finset.range m then g x else 0)
      use (newNum prev)
      refine ⟨?_, ?_⟩

      rw [newNum]
      linarith

      rfl
      intro x _ m_lt_x
      simp [m_lt_x]
      intro x _ m_lt_x
      simp [m_lt_x]


lemma tree_linear_independent (t: ReverseTree): LinearIndependent ℚ ![t.getData.a, t.getData.b] := by
  induction t with
  | root =>
    simp [LinearIndependent.pair_iff]
    intro p q eq_zero
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
  | left prev h_prev =>
    simp [ReverseTree.getData]
    simp [ReverseTree.getData] at h_prev
    obtain ⟨_, ⟨b_coords, ⟨max_num, max_num_lt, b_eq⟩⟩⟩ := tree_linear_comb prev


    have nonzero_b_coord: ∃n, n < max_num ∧ b_coords n ≠ 0 := by
      by_contra!
      have sum_eq_zero: ∑ i ∈ Finset.range max_num, b_coords i • basis_n i = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        specialize this x (Finset.mem_range.mp hx)
        simp [this]
      rw [sum_eq_zero] at b_eq
      rw [b_eq] at h_prev
      have foo := LinearIndependent.ne_zero 1 h_prev
      simp at foo

    rw [b_eq]
    rw [xSeq, basis_n]
    simp only [LinearIndependent.pair_iff]
    intro s t hs_t

    have basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis
    rw [linearIndependent_iff'] at basis_indep
    rw [add_comm] at hs_t

    let f := λ x => t • n_q_basis x

    have ite_eq: (if (newNum prev) ∈ Finset.range (newNum prev + 1) then f (newNum prev) else 0) = t • n_q_basis (newNum prev) := by
      simp [f]


    rw [← ite_eq] at hs_t
    simp only [← Finset.sum_ite_eq] at hs_t
    --let f := (λ x: ℕ => t • n_q_basis (newNum prev))
    --have eq_f: t • n_q_basis (newNum prev) = f 0 := by
    --  simp only [f]
    --rw [eq_f] at hs_t
    --rw [← Finset.sum_range_one f] at hs_t

    have max_num_nonzero: 0 < max_num := by
      obtain ⟨n, hn⟩ := nonzero_b_coord
      linarith

    --have my_subset: Finset.range 1 ⊆ Finset.range max_num := by
    --  refine Finset.range_subset.mpr ?_
    --  linarith


    have max_subset: Finset.range max_num ⊆ Finset.range (newNum prev + 1) := by
      refine Finset.range_subset.mpr ?_
      linarith

    nth_rw 2 [← Finset.sum_extend_by_zero] at hs_t
    rw [Finset.sum_subset max_subset] at hs_t

    --rw [← Finset.sum_extend_by_zero] at hs_t
    --rw [Finset.sum_subset my_subset] at hs_t
    rw [← neg_one_zsmul] at hs_t
    rw [← Finset.sum_zsmul] at hs_t
    rw [Finset.smul_sum] at hs_t
    rw [← Finset.sum_add_distrib] at hs_t
    simp only [f] at hs_t
    simp only [← ite_zero_smul] at hs_t
    simp only [← smul_assoc] at hs_t
    simp only [← add_smul] at hs_t

    apply (basis_indep _) at hs_t
    obtain ⟨b_nonzero, h_b_lt, h_b_zeronzero⟩ := nonzero_b_coord
    have s_eq_zero := hs_t b_nonzero

    have newnum_prev_nonzero: 1 < newNum prev := by
      exact newnem_gt_one prev

    have neq_zero: newNum prev ≠ 0 := by
      omega

    have b_nonzero_lt: b_nonzero < newNum prev + 1 := by
      linarith

    have b_nonzero_lt_other: b_nonzero < newNum prev := by
      linarith

    have n_nonzero_neq: newNum prev ≠ b_nonzero := by
      omega

    simp [neq_zero, b_nonzero_lt, n_nonzero_neq, h_b_lt, h_b_zeronzero] at s_eq_zero
    have foo: ¬(newNum prev < max_num) := by
      linarith

    have t_eq_zero := hs_t (newNum prev)
    simp [foo] at t_eq_zero
    refine ⟨s_eq_zero, t_eq_zero⟩
    intro x hx hx_not_in
    simp [hx_not_in]
  | right a prev => sorry





-- inductive MyTree {α: Type} where
--   | root: TreeData (α := α) 0 → MyTree
--   | left (n: ℕ) (hn: n > 0): TreeData (n - 1) → MyTree
--   | right (n: ℕ) (hn: n > 0): TreeData (n - 1) → MyTree


-- def treeAt(n: ℕ ): MyTree (α := String) :=
--   MyTree.left { MyTree.root {a := "a", b := "b"}
