import Mathlib

-- https://leanprover.zulipchat.com/user_uploads/3121/ASjTo5huToAvNGcg7pOGOOSy/Equation1692.pdf

#synth AddGroup (∀ n: ℕ, ℤ)

-- TODO -  only finitely many entries are non-zero?
abbrev G := (ℕ →₀ ℚ)

noncomputable abbrev n_q_basis := Finsupp.basisSingleOne (R := ℚ) (ι := ℕ)
noncomputable abbrev basis_n := DFunLike.coe n_q_basis
noncomputable abbrev all_basis := (λ n: ℕ => (n, basis_n n)) '' Set.univ

-- lemma basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis

-- 1, 3, 5, 7, 9, 11, 13, 15, 17, 19, 21, 23
-- 2, 6, 10, 14, 18, 22
-- 4, 12, 20, 28
-- 8, 24, 40, 56,
-- 16, 48, 80, 112

-- 23424 = 2**7 + higher_order
-- 23424 mod 2**8 = (2**7 + higher_order) mod 2**8 = 2**7 +

-- theorem bar (x: ℚ) : 1 =1 := by
--   let foo: Set ℝ := ∅
--   have wrong: ∀ y ∈ foo, 1 = 2 := by
--     simp [foo]

--   have foo: ∀ y ∈ {5, 6}, x = 1 := by s_orry
--   have other: x = 1 := by
--     simp_all only [Set.mem_univ, true_implies, forall_const]


--set_option pp.instances false
--set_option pp.coercions false
--set_option pp.all true

theorem foo: 1 = 1 := by

  -- Actual start of proof
  -- Hack - include the basis element 0, since the proof pdf starts numbering them at 1
  let s_i := λ i: ℕ => {val ∈ all_basis | val.1 ≡ 2^i [MOD 2^(i + 1)] } ∪ (if i = 0 then {(0, basis_n 0)} else {})
  have no_overlap: ∀ i j: ℕ, i < j → s_i i ∩ s_i j = ∅ := by
    intro i j i_lt_j
    by_contra!
    have i_neq_zero: i ≠ 0 := by
      by_contra! i_eq_zero
      have j_neq_zero: j ≠ 0 := by
        linarith

      rw [Set.inter_def] at this
      simp only [s_i, i_eq_zero] at this
      simp at this
      obtain ⟨⟨k, e_k⟩, ⟨e_k_in_i, e_k_in_j⟩⟩ := this
      simp [j_neq_zero] at e_k_in_j
      simp [i_eq_zero] at e_k_in_i
      cases e_k_in_i with
      | inl left =>
        have k_eq_zero: k = 0 := left.1
        rw [k_eq_zero] at e_k_in_j
        obtain ⟨_, bad_zero⟩ := e_k_in_j
        have bar := Nat.modEq_zero_iff_dvd.mp (bad_zero.symm)
        have gt_zero: 0 < 2^j := by
          apply Nat.pow_pos
          linarith
        have larger: 2^j < 2^(j + 1) := by
          apply Nat.pow_lt_pow_succ
          simp

        have smaller := (Nat.le_of_dvd gt_zero) bar
        linarith
      | inr right =>
        have pow_montone:  2 ^ j < 2 ^ (j + 1) := by
          apply Nat.pow_lt_pow_succ
          simp
        have one_lt: 1 < 2 := by simp
        have k_mod := Nat.mod_eq_of_modEq right.2 one_lt
        rw [← Nat.odd_iff] at k_mod
        have j_mod := e_k_in_j.2
        --have new_j_mod := Nat.mod_eq_of_modEq j_mod pow_montone

        rw [Nat.modEq_iff_dvd] at j_mod
        have j_plus_ne: j + 1 ≠ 0 := by
          linarith
        have two_dvd_pow: 2 ∣ (((2 : ℕ)^((j + 1): ℕ)) : ℕ)  := by
          exact dvd_pow_self 2 j_plus_ne

        have coerce: (2 : ℤ) ∣ ↑((2: ℕ) ^ (j + 1)) := by
          exact Int.ofNat_dvd_right.mpr two_dvd_pow

        have tmp_dvd := Dvd.dvd.trans coerce j_mod

        rw [Int.dvd_def] at tmp_dvd
        obtain ⟨c, hc⟩ := tmp_dvd
        have rearrange: (((2: ℕ) ^ (j: ℕ)): ℕ) - 2 * c = ↑k := by
          rw [Eq.comm, sub_eq_neg_add] at hc
          have bar := add_eq_of_eq_neg_add hc
          have other := add_neg_eq_of_eq_add bar.symm
          exact other

        have cast_z: 2^j - 2*c = k := by
          rw [← rearrange]
          simp

        rw [← mul_pow_sub_one j_neq_zero] at cast_z
        have factor_2: 2*(2 ^ (j - 1) - c) = ↑k := by
          rw [← cast_z]
          ring
        have two_dvd_k: (2: ℤ) ∣ k := by
          exact Dvd.intro (2 ^ (j - 1) - c) factor_2
        have k_even: Even (k: ℤ) := by
          apply even_iff_two_dvd.mpr two_dvd_k
        have odd_k: Odd (k: ℤ) := by
          exact (Int.odd_coe_nat k).mpr k_mod
        rw [← Int.not_odd_iff_even] at k_even
        contradiction

    have j_neq_zero: j ≠ 0 := by
      linarith
    rw [Set.inter_def] at this
    simp at this
    obtain ⟨⟨k, e_k⟩, ⟨e_k_in_i, e_k_in_j⟩⟩ := this

    have e_k_in_i: k ≡ 2^i [MOD 2^(i + 1)] := by
      simp [s_i, i_neq_zero] at e_k_in_i
      exact e_k_in_i.2

    have e_k_in_j: k ≡ 2^j [MOD 2^(j + 1)] := by
      simp [s_i, j_neq_zero] at e_k_in_j
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

-- BAD - this is for intersction, not the whole union
-- Simpler idea: What happens if j = 2^a mod 2^(a+1) and j = 2^b mod 2^(b+1) for a ≠ b?
-- c*2^(a+1) + 2^a = j
-- d*2^(b+1) + 2^b = j

-- c*2^(a+1) + 2^a = d*2^(b+1) + 2^b
-- wlog a < b
-- c*2^(1) + 1 = d*2^(b+1-a) + 2^(b-a)
-- LHS is odd, RHS is even
-- contradiction

-- New idea:
-- Let 2^a be the largest power of 2 dividing j
-- Then, j = 2^a + (j - 2^a)
--

  have s_i_infinite: ∀ i, (s_i i).Infinite := by
    intro i
    let n_to_multiple := fun n => (2^i + n*2^(i+1), basis_n (2^i + n*2^(i+1)))
    have image_subset: Set.range n_to_multiple ⊆ (s_i i) := by
      simp only [n_to_multiple, s_i]
      rw [Set.subset_def]
      intro x hx
      simp at hx
      obtain ⟨y, hy⟩ := hx
      simp
      left
      refine ⟨?_, ?_⟩
      use 2 ^ i + y * 2 ^ (i + 1)
      rw [← hy]
      simp [Nat.ModEq]


    have injective_fun: Function.Injective (fun n => (2^i + n*2^(i+1), basis_n (2^i + n*2^(i+1)))) := by
      -- ???: How does this simp work
      simp [Function.Injective]

    have range_infinite := Set.infinite_range_of_injective  injective_fun
    simp only [n_to_multiple] at image_subset
    apply Set.Infinite.mono image_subset range_infinite



  have new_si_union_basis: ⋃ i, s_i i = all_basis := by
    ext ⟨k, e_k⟩
    refine ⟨?_, ?_⟩
    . intro e_k_in_union
      simp at e_k_in_union
      obtain ⟨i, e_k_in_i⟩ := e_k_in_union
      simp [s_i] at e_k_in_i
      simp [all_basis]
      cases e_k_in_i with
      | inl left =>
        exact left.1
      | inr right =>
        rw [right.2.1, right.2.2]
    .
      intro e_k_in_basis
      by_cases is_k_zero: k = 0
      . simp [is_k_zero, s_i]
        use 0
        right
        simp [all_basis, is_k_zero] at e_k_in_basis
        rw [e_k_in_basis]
        simp
      .
        simp [is_k_zero, s_i]
        by_cases two_div_k: 2 ∣ k
        .
          have pow_two_div_k := Nat.dvd_ord_proj_of_dvd is_k_zero Nat.prime_two two_div_k

          have k_pow_two: k = 2^(k.factorization 2) * ( k / 2^(k.factorization 2)) := by
            exact Eq.symm (Nat.ord_proj_mul_ord_compl_eq_self k 2)

          have two_not_div := Nat.not_dvd_ord_compl Nat.prime_two is_k_zero

          have odd_val: Odd (k / 2 ^ k.factorization 2) := by
            refine Nat.odd_iff.mpr ?_
            rw [Nat.two_dvd_ne_zero] at two_not_div
            exact two_not_div

          obtain ⟨f, hf⟩ := odd_val
          rw [hf] at k_pow_two

          have dummy := calc
            (k: ℤ) - (2^(k.factorization 2): ℕ) = (2 ^ k.factorization 2 * (2 * f + 1) : ℕ) - 2^(k.factorization 2) := by
              nth_rewrite 1 [k_pow_two]
              norm_cast
            _ = (2 ^ k.factorization 2 * (2 * f + 1) : ℕ)  -2^(k.factorization 2)*1 := by ring
            _ = (2 ^ k.factorization 2 * ((2 * f + 1) - 1) : ℕ) := by
              push_cast
              ring
            _ = 2 ^ k.factorization 2 * (2 * f) := by simp
            _ = (2 ^ (1 + k.factorization 2) : ℕ) * (f : ℤ) := by
              norm_cast
              ring

          have sub_div: (((2 ^ (1 + k.factorization 2)) : ℕ ) : ℤ) ∣ (k: ℤ) - ((2 ^ k.factorization 2): ℕ) := by
            exact Dvd.intro f (id (Eq.symm dummy))

          have k_mod: 2 ^ k.factorization 2 ≡ k [MOD 2 ^ (1 + k.factorization 2)] := by
            exact Nat.modEq_of_dvd sub_div

          have k_mod_reverse: k ≡ 2 ^ k.factorization 2 [MOD 2 ^ (1 + k.factorization 2)] := by
            exact Nat.ModEq.symm k_mod

          have k_mod_swap: k ≡ 2 ^ k.factorization 2 [MOD 2 ^ (k.factorization 2 + 1)] := by
            rwa [Nat.add_comm]

          simp [all_basis] at e_k_in_basis
          refine ⟨e_k_in_basis, ?_⟩
          use k.factorization 2
        . simp [all_basis] at e_k_in_basis
          refine ⟨e_k_in_basis, ?_⟩
          use 0
          simp_all only [Nat.two_dvd_ne_zero]
          exact two_div_k


  rfl

noncomputable def xSeq (n: ℕ): G := basis_n n

lemma xseq_injective: Function.Injective xSeq := by
  simp [Function.Injective]
  intro n_1 n_2 h_eq
  simp [xSeq] at h_eq
  have one_neq_zero: (1: ℚ) ≠ 0 := by
    simp
  have single_injective := Finsupp.single_left_injective (α := ℕ) one_neq_zero
  simp [Function.Injective] at single_injective
  have injective_imp := @single_injective n_1 n_2
  exact injective_imp h_eq

structure TreeData where
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

lemma newnum_injective (t1: ReverseTree) (t2: ReverseTree) (h_eq: newNum t1 = newNum t2): t1 = t2 := by
  induction t1 generalizing t2 with
  | root =>
    have t2_root: t2 = ReverseTree.root := by
      by_contra!
      match t2 with
      | ReverseTree.root => contradiction
      | ReverseTree.left prev =>
        simp [newNum] at h_eq
        omega
      | ReverseTree.right prev =>
        -- TODO - how is this simpliffying to `newNum prev = 1`?
        simp [newNum] at h_eq
        have gt_one: 1 < newNum prev := by
          exact newnem_gt_one prev
        have not_eq_one: newNum prev ≠ 1 := by
          linarith
        contradiction
    rw [t2_root]
  | left prev h_prev =>
    have t2_left: ∃ d, t2 = ReverseTree.left d := by
      by_contra!
      match t2 with
      | ReverseTree.root =>
        simp [newNum] at h_eq
        omega
      | ReverseTree.left prev2 =>
        specialize this prev2
        contradiction
      | ReverseTree.right prev2 =>
        simp [newNum] at h_eq
        have gt_one: 1 < newNum prev := by
          exact newnem_gt_one prev
        omega
    obtain ⟨d, hd⟩ := t2_left

    have d_num_eq: newNum prev = newNum d := by
      rw [hd] at h_eq
      simp [newNum] at h_eq
      omega

    have d_eq_prev: d = prev := by
      specialize h_prev d d_num_eq
      rw [Eq.comm] at h_prev
      exact h_prev
    rw [d_eq_prev] at hd
    rw [Eq.comm] at hd
    exact hd

  | right prev h_prev =>
    have t2_right: ∃ d, t2 = ReverseTree.right d := by
      by_contra!
      match t2 with
      | ReverseTree.root =>
        simp [newNum] at h_eq
        have gt_one: 1 < newNum prev := by
          exact newnem_gt_one prev
        omega
      | ReverseTree.left prev2 =>
        simp [newNum] at h_eq
        have gt_one: 1 < newNum prev := by
          exact newnem_gt_one prev
        omega
      | ReverseTree.right prev2 =>
        specialize this prev2
        contradiction
    obtain ⟨d, hd⟩ := t2_right
    have d_num_eq: newNum prev = newNum d := by
      rw [hd] at h_eq
      simp [newNum] at h_eq
      omega

    have d_eq_prev: d = prev := by
      specialize h_prev d d_num_eq
      rw [Eq.comm] at h_prev
      exact h_prev
    rw [d_eq_prev] at hd
    rw [Eq.comm] at hd
    exact hd

variable {M A : Type*}
variable [Zero A] [SMulZeroClass M A]

lemma tree_linear_comb (t: ReverseTree):
  (∃ g: ℕ →₀ ℚ, ∃ m: ℕ, m ≤ newNum t ∧ g.support.max < m ∧ t.getData.a = ∑ i ∈ Finset.range m, g i • basis_n i) ∧
  (∃ g: ℕ →₀ ℚ, ∃ m: ℕ, m ≤ newNum t ∧ g.support.max < m ∧ t.getData.b = ∑ i ∈ Finset.range m, g i • basis_n i) := by
  induction t with
  | root =>
    refine ⟨?_, ?_⟩
    . let f := Finsupp.single 0 (1 : ℚ)
      have zero_outside: ∀ (a : ℕ), f a ≠ 0 → a ∈ Finset.range 1 := by
        intro a ha
        simp only [f] at ha
        simp [Finsupp.single_apply_ne_zero] at ha
        simpa
      use f
      let wrapped_f := Finsupp.onFinset (Finset.range 1) f zero_outside
      simp [newNum]
      use 1
      simp
      simp [ReverseTree.getData]
      simp [xSeq, basis_n]
      simp [f]
      rw [Finsupp.support_single_ne_zero]
      simp
      linarith


    let f := Finsupp.single 1 (1 : ℚ)
    have zero_outside: ∀ (a : ℕ), f a ≠ 0 → a ∈ Finset.range 2 := by
      intro a ha
      simp only [f] at ha
      simp [Finsupp.single_apply_ne_zero] at ha
      simp
      linarith

    use f
    use 2
    simp only [ReverseTree.getData]
    simp only [xSeq, basis_n, n_q_basis, f]
    refine ⟨?_, ?_⟩
    simp [newNum]
    refine ⟨?_, ?_⟩
    rw [Finsupp.support_single_ne_zero]
    simp
    simp

    ext n
    by_cases n_eq_one: n = 1
    . simp [n_eq_one, Finsupp.single_apply]
    . simp [n_eq_one, Finsupp.single_apply]
  | left prev h_prev =>
    simp only [ReverseTree.getData]
    refine ⟨?_,?_⟩
    . obtain ⟨_, ⟨g, m, m_le, h_g⟩⟩ := h_prev
      rw [newNum]
      have newnum_gt_one: 1 < newNum prev := newnem_gt_one prev
      have prev_lt_mul: newNum prev < 2 * newNum prev - 1 := by
        omega

      let neg_val := λ i => (-1: ℚ) * i
      have neg_val_zero: neg_val 0 = 0 := by
        simp [neg_val]
      let f := Finsupp.mapRange neg_val neg_val_zero g

      use f
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
      rw [← Fin.sum_univ_eq_sum_range]
      rw [← Fin.sum_univ_eq_sum_range] at h_g
      simp only [f]
      refine ⟨?_, ?_⟩
      . have supp_subset := Finsupp.support_mapRange (f := neg_val) (hf := neg_val_zero) (g := g)
        have card_le := Finset.card_le_card supp_subset
        have neg_val_injective: Function.Injective neg_val := by
          simp [neg_val]
          exact neg_injective
        have maprange_supp_eq := Finsupp.support_mapRange_of_injective (he0 := neg_val_zero) g neg_val_injective
        rw [maprange_supp_eq]
        exact h_g.1


      simp only [Finsupp.mapRange_apply, neg_val]
      simp
      exact h_g.2
    . obtain ⟨_, ⟨g, m, _⟩⟩ := h_prev
      rw [newNum]
      let f := Finsupp.single (newNum prev) (1 : ℚ)
      use f
      use (newNum prev) + 1
      refine ⟨?_, ?_⟩
      have newnum_gt_one: 1 < newNum prev := newnem_gt_one prev
      omega
      simp [f]
      simp [xSeq, basis_n, n_q_basis]
      refine ⟨?_, ?_⟩
      . rw [Finsupp.support_single_ne_zero]
        simp
        have newnum_gt_zero: 1 < newNum prev := by
          exact newnem_gt_one prev
        have one_eq_coe: @OfNat.ofNat (WithBot ℕ) 1 One.toOfNat1 = ↑(1: ℕ) := by
          simp
        rw [one_eq_coe]
        have neq_bot: ↑(newNum prev) ≠ ⊥ := by
          simp
          linarith

        have real_lt: newNum prev < newNum prev + 1 := by
          linarith
        have other := (WithBot.coe_lt_coe.mpr real_lt)
        simp at other
        exact other
        simp

      -- TODO - how does this work?
      simp [Finsupp.single_apply]
      simp [apply_ite (Finsupp.single _)]
        -- @Finset.sum n (n →₀ R) Finsupp.instAddCommMonoid Finset.univ fun x ↦ Finsupp.single x (if i = x then a else 0) : n →₀ R
        -- @Finset.sum ℕ (ℕ →₀ ℚ) Finsupp.instAddCommMonoid (Finset.range (newNum prev + 1)) fun x ↦
  | right prev h_prev =>
    simp only [ReverseTree.getData]
    refine ⟨?_,?_⟩
    . obtain ⟨_, ⟨g, m, _⟩⟩ := h_prev
      rw [newNum]
      let f := Finsupp.single (newNum prev) (1 : ℚ)
      use f
      use (newNum prev) + 1
      refine ⟨?_, ?_⟩
      have newnum_gt_one: 1 < newNum prev := newnem_gt_one prev
      omega
      simp [f]
      simp [xSeq, basis_n, n_q_basis]
      refine ⟨?_, ?_⟩
      . rw [Finsupp.support_single_ne_zero]
        simp

        have real_lt: newNum prev < newNum prev + 1 := by
          linarith
        have other := (WithBot.coe_lt_coe.mpr real_lt)
        simp at other
        exact other

        simp

      . simp [Finsupp.single_apply]
        simp [apply_ite (Finsupp.single _)]

    . obtain ⟨⟨g_l, m_l, m_l_le, g_l_card, h_g_l⟩, ⟨g, m, m_le, g_card, h_g⟩⟩ := h_prev
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
      let f := λ x => (if x ∈ Finset.range m_l then g_l x else 0) - (if x ∈ Finset.range m then g x else 0)
      have zero_outside: ∀ (a : ℕ), f a ≠ 0 → a ∈ Finset.range (newNum prev) := by
        simp only [f]
        intro a ha
        have one_nonzero: (if a ∈ Finset.range m_l then g_l a else 0) ≠ 0 ∨ (if a ∈ Finset.range m then g a else 0) ≠ 0 := by
          by_contra!
          obtain ⟨c, d⟩ := this
          rw [c, d] at ha
          simp at ha
        cases one_nonzero with
        | inl h_l =>
          simp at h_l
          simp
          linarith
        | inr h_r =>
          simp at h_r
          simp
          linarith
      use Finsupp.onFinset _ f (zero_outside)
      use (newNum prev)
      refine ⟨?_, ?_⟩

      rw [newNum]
      linarith
      refine ⟨?_, ?_⟩
      have support_subset: (Finsupp.onFinset (Finset.range (newNum prev)) f zero_outside).support ⊆ Finset.range (newNum prev) := by
        simp
      have card_le := Finset.card_le_card support_subset
      simp at card_le
      by_cases supp_empty: (Finsupp.onFinset (Finset.range (newNum prev)) f zero_outside).support = ∅
      . rw [supp_empty]
        simp
        -- TODO - why can't we just use WithBot.bot_lt_coe
        -- simp [WithBot.bot_lt_coe]
        exact ⟨newNum prev, rfl, fun _ hb => (Option.not_mem_none _ hb).elim⟩
      . have set_nonempty: Set.Nonempty ((Finsupp.onFinset (Finset.range (newNum prev)) f zero_outside).support: Set ℕ) := by
          simp at supp_empty
          simp [Finset.coe_nonempty]
          exact Finsupp.support_nonempty_iff.mpr supp_empty

        have foo := Finset.max'_subset set_nonempty support_subset
        have newnum_gt_one := newnem_gt_one prev
        have newnum_new_zero: newNum prev ≠ 0 := by linarith
        have finset_nrage_nonempty: (Finset.range (newNum prev)).Nonempty := by
          simp
          linarith
        have zero_lt_newnum: 0 < newNum prev := by
          linarith
        have maxprime_lt: (Finset.range (newNum prev)).max' finset_nrage_nonempty < (newNum prev) := by
          simp
        rw [← Finset.coe_max' set_nonempty]
        simp

        have desired: ((Finsupp.onFinset (Finset.range (newNum prev)) f zero_outside).support.max' set_nonempty) < newNum prev := by
          linarith
        have other := (WithBot.coe_lt_coe.mpr desired)
        exact other


      rfl
      intro x _ m_lt_x
      simp [m_lt_x]
      intro x _ m_lt_x
      simp [m_lt_x]


--   One element in each pair must be fresh - assume wlog that 'c' and 'x' are fresh.
--     Then, in order for 'c - d = x - y', we must have 'x' occuring in 'd' and 'c' occuring in 'y'.
--     This means depth(parent_one) >= depth(parent_two) and depth(parent_two) >= depth(parent_one), since each must have at least the depth where the other fresh element is first introduced.
--     Thus, depth(parent_one) = depth(parent_two).
--     The only way for this to work is if the parents look like (x_i, p) and (q, x_i) - that this, the same fresh node.
--      Otherwise, one of the nodes will contain a fresh element that's not in the other node.
--     This implies that the parents are the left/right children of the same node.
--     Let this common ancestor be (f, g).

lemma cross_eq_same_parent {t1 t2: ReverseTree} (h_a_neq: t1.getData.a ≠ t2.getData.a) (h_eq: t1.getData.a - t1.getData.b = t2.getData.a - t2.getData.b) : ∃ ancestor: ReverseTree, (t1 = ancestor.left ∧ t2 = ancestor.right) ∨ (t1 = ancestor.right ∧ t2 = ancestor.left) := by
    have parents_b_neq: t1.getData.b ≠ t2.getData.b := by
      by_contra!
      rw [this] at h_eq
      simp at h_eq
      contradiction

    have t1_neq_root: t1 ≠ ReverseTree.root := by
      by_contra!
      rw [this] at h_a_neq
      rw [this] at h_eq
      simp at h_a_neq
      simp [ReverseTree.getData] at h_a_neq
      simp [ReverseTree.getData] at h_eq
      sorry

    match h_t1: t1 with
    | .root => sorry
    | .left t1_parent =>
      simp [ReverseTree.getData] at h_eq

      have t1_b_fresh: t1.getData.b = xSeq (newNum t1_parent) := by
        simp [h_t1, ReverseTree.getData]
      have t2_a_fresh: t2.getData.a = xSeq (newNum t1_parent) := by
        sorry

      have t2_is_right: ∃ parent: ReverseTree, t2 = parent.right := by
        sorry

      obtain ⟨t2_parent, h_t2_parent⟩ := t2_is_right
      have t2_parent_eq: t1_parent = t2_parent := by
        by_contra!
        rw [h_t2_parent] at t2_a_fresh
        rw [← t1_b_fresh] at t2_a_fresh
        rw [h_t1] at t2_a_fresh
        simp [ReverseTree.getData] at t2_a_fresh
        apply xseq_injective at t2_a_fresh
        apply newnum_injective at t2_a_fresh
        rw [eq_comm] at t2_a_fresh
        contradiction

      use t2_parent
      left
      refine ⟨?_, ?_⟩
      rw [t2_parent_eq]
      exact h_t2_parent
    | .right t2_parent => sorry

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
    obtain ⟨_, ⟨b_coords, ⟨max_num, max_num_lt, b_coord_card, b_eq⟩⟩⟩ := tree_linear_comb prev


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
  | right prev h_prev =>
    simp [ReverseTree.getData]
    simp [ReverseTree.getData] at h_prev
    obtain ⟨⟨a_coords, ⟨a_max_num, a_max_num_lt, a_support_max, a_eq⟩⟩, ⟨b_coords, ⟨b_max_num, b_max_num_lt, b_support_max, b_eq⟩⟩⟩ := tree_linear_comb prev


    rw [a_eq, b_eq]
    rw [xSeq, basis_n]
    simp only [LinearIndependent.pair_iff]
    intro s t hs_t

    nth_rw 1 [← Finset.sum_extend_by_zero] at hs_t
    nth_rw 2 [← Finset.sum_extend_by_zero] at hs_t

    have a_subset: Finset.range a_max_num ⊆ Finset.range (newNum prev + 1) := by
      refine Finset.range_subset.mpr ?_
      linarith

    have b_subset: Finset.range b_max_num ⊆ Finset.range (newNum prev + 1) := by
      refine Finset.range_subset.mpr ?_
      linarith

    let f := λ x => s • n_q_basis x
    have ite_eq: (if (newNum prev) ∈ Finset.range (newNum prev + 1) then f (newNum prev) else 0) = s • n_q_basis (newNum prev) := by
      simp [f]

    have basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis
    rw [linearIndependent_iff'] at basis_indep

    rw [← ite_eq] at hs_t
    simp only [← Finset.sum_ite_eq] at hs_t

    rw [Finset.sum_subset a_subset] at hs_t
    rw [Finset.sum_subset b_subset] at hs_t
    rw [← Finset.sum_sub_distrib] at hs_t
    simp only [← ite_zero_smul] at hs_t
    simp only [← sub_smul] at hs_t
    rw [Finset.smul_sum] at hs_t
    rw [← Finset.sum_add_distrib] at hs_t
    simp only [f] at hs_t
    simp only [← ite_zero_smul] at hs_t
    simp only [← smul_assoc] at hs_t
    simp only [← add_smul] at hs_t

    apply (basis_indep _) at hs_t
    refine ⟨?_, ?_⟩

    have a_max_num_lt: a_max_num < newNum prev + 1 := by
      linarith

    have not_lt_a: ¬ (newNum prev < a_max_num) := by
      linarith

    have not_lt_b: ¬ (newNum prev < b_max_num) := by
      linarith

    have s_eq_zero := hs_t (newNum prev)
    simp [not_lt_a, not_lt_b] at s_eq_zero
    exact s_eq_zero

    have noneq_coord: ∃ n, n < (max a_max_num b_max_num) ∧ a_coords n ≠ b_coords n := by
      by_cases a_eq_b: a_max_num = b_max_num
      . by_contra!
        rw [a_eq_b] at this
        simp at this
        rw [a_eq_b] at a_eq
        have a_eq_sum_b: prev.getData.a = ∑ i ∈ Finset.range b_max_num, b_coords i • basis_n i := by
          rw [a_eq]
          apply Finset.sum_congr
          rfl
          intro x hx
          have x_lt_b_max: x < b_max_num := by
            exact Finset.mem_range.mp hx
          specialize this x x_lt_b_max
          rw [this]
        rw [← b_eq] at a_eq_sum_b
        rw [LinearIndependent.pair_iff'] at h_prev
        specialize h_prev 1
        simp at h_prev
        contradiction

        -- Prove a neq zero
        by_contra!
        rw [this] at h_prev
        have ne_zero := LinearIndependent.ne_zero 0 h_prev
        simp at ne_zero

      . by_contra! all_coords_eq
        by_cases a_lt_b: a_max_num < b_max_num
        .
          have nonzero_gt_a: ∃ m, a_max_num ≤ m ∧ m < (max a_max_num b_max_num) ∧  b_coords m ≠ 0 := by
            by_contra!
            have eq_sum_smaller: ∑ i ∈ Finset.range a_max_num, b_coords i • basis_n i = ∑ i ∈ Finset.range b_max_num, b_coords i • basis_n i := by
              apply Finset.sum_subset
              simp
              linarith
              intro x hx
              specialize this x
              simp
              intro x_gt_a
              specialize this x_gt_a
              simp at hx
              have x_le_max: x < max a_max_num b_max_num := by
                simp
                right
                exact hx
              apply this x_le_max
            rw [← eq_sum_smaller] at b_eq
            have b_eq_a_sum: prev.getData.b = ∑ i ∈ Finset.range a_max_num, a_coords i • basis_n i := by
              rw [b_eq]
              apply Finset.sum_congr
              rfl
              intro x hx
              simp at hx
              specialize all_coords_eq x
              have x_lt_max: x < max a_max_num b_max_num := by
                simp
                left
                exact hx
              rw [all_coords_eq]
              exact x_lt_max
            rw [← a_eq] at b_eq_a_sum
            rw [LinearIndependent.pair_iff'] at h_prev
            specialize h_prev 1
            simp at h_prev
            rw [Eq.comm] at h_prev
            contradiction

            -- Prove a neq zero
            by_contra!
            rw [this] at h_prev
            have ne_zero := LinearIndependent.ne_zero 0 h_prev
            simp at ne_zero
          obtain ⟨m, hm_gt, hm_lt_max, b_m_nonzero⟩ := nonzero_gt_a
          have a_coords_zero: a_coords m = 0 := by
            have m_gt_max: a_coords.support.max < m := by
              have hm_withbot: (a_max_num : WithBot ℕ) ≤ m := by
                exact WithBot.coe_le_coe.mpr hm_gt
              exact gt_of_ge_of_gt hm_withbot a_support_max

            have n_not_supp: m ∉ a_coords.support := by
              apply Finset.not_mem_of_max_lt_coe m_gt_max
            exact Finsupp.not_mem_support_iff.mp n_not_supp
          have coord_neq_a_b: a_coords m ≠ b_coords m := by
            exact ne_of_eq_of_ne a_coords_zero (id (Ne.symm b_m_nonzero))
          specialize all_coords_eq m hm_lt_max
          contradiction
        -- BEGIN HORRIBLE COPY-PASTE
        . have nonzero_gt_b: ∃ m, b_max_num ≤ m ∧ m < (max a_max_num b_max_num) ∧ a_coords m ≠ 0 := by
            by_contra!
            have eq_sum_smaller: ∑ i ∈ Finset.range b_max_num, a_coords i • basis_n i = ∑ i ∈ Finset.range a_max_num, a_coords i • basis_n i := by
              apply Finset.sum_subset
              simp
              linarith
              intro x hx
              specialize this x
              simp
              intro x_gt_a
              specialize this x_gt_a
              simp at hx
              have x_le_max: x < max a_max_num b_max_num := by
                simp
                left
                exact hx
              apply this x_le_max
            rw [← eq_sum_smaller] at a_eq
            have a_eq_b_sum: prev.getData.a = ∑ i ∈ Finset.range b_max_num, b_coords i • basis_n i := by
              rw [a_eq]
              apply Finset.sum_congr
              rfl
              intro x hx
              simp at hx
              specialize all_coords_eq x
              have x_lt_max: x < max a_max_num b_max_num := by
                simp
                right
                exact hx
              rw [all_coords_eq]
              exact x_lt_max
            rw [← b_eq] at a_eq_b_sum
            rw [LinearIndependent.pair_iff'] at h_prev
            specialize h_prev 1
            simp at h_prev
            contradiction

            -- Prove b neq zero
            by_contra!
            rw [this] at h_prev
            have ne_zero := LinearIndependent.ne_zero 0 h_prev
            simp at ne_zero
          obtain ⟨m, hm_gt, hm_lt_max, a_m_nonzero⟩ := nonzero_gt_b
          have b_coords_zero: b_coords m = 0 := by
            have m_gt_max: b_coords.support.max < m := by
              have hm_withbot: (b_max_num : WithBot ℕ) ≤ m := by
                exact WithBot.coe_le_coe.mpr hm_gt
              exact gt_of_ge_of_gt hm_withbot b_support_max

            have n_not_supp: m ∉ b_coords.support := by
              apply Finset.not_mem_of_max_lt_coe m_gt_max
            exact Finsupp.not_mem_support_iff.mp n_not_supp
          have coord_neq_a_b: b_coords m ≠ a_coords m := by
            exact ne_of_eq_of_ne b_coords_zero (id (Ne.symm a_m_nonzero))
          specialize all_coords_eq m hm_lt_max
          rw [Eq.comm] at all_coords_eq
          contradiction
          -- END HORRIBLE COPY-PASTE-


    obtain ⟨n, n_lt_max, n_neq⟩ := noneq_coord

    have n_neq_newnum: newNum prev ≠ n := by
      omega

    have n_lt_newnum: n < newNum prev + 1 := by
      omega

    have a_coord_zero_gt: ∀ n, a_max_num ≤ n → a_coords n = 0 := by
      intro n hn
      have hn_withbot: (a_max_num : WithBot ℕ) ≤ n := by
        exact WithBot.coe_le_coe.mpr hn
      have n_gt_max: a_coords.support.max < n := by
        exact gt_of_ge_of_gt hn_withbot a_support_max

      have n_not_supp: n ∉ a_coords.support := by
        apply Finset.not_mem_of_max_lt_coe n_gt_max
      exact Finsupp.not_mem_support_iff.mp n_not_supp

    have b_coord_zero_gt: ∀ n, b_max_num ≤ n → b_coords n = 0 := by
      intro n hn
      have hn_withbot: (b_max_num : WithBot ℕ) ≤ n := by
        exact WithBot.coe_le_coe.mpr hn
      have n_gt_max: b_coords.support.max < n := by
        exact gt_of_ge_of_gt hn_withbot b_support_max

      have n_not_supp: n ∉ b_coords.support := by
        apply Finset.not_mem_of_max_lt_coe n_gt_max
      exact Finsupp.not_mem_support_iff.mp n_not_supp

    have t_eq_zero := hs_t n
    simp [n_neq_newnum, n_lt_newnum, n_lt_max] at t_eq_zero
    have coord_neq: a_coords n - b_coords n ≠ 0 := by
      exact sub_ne_zero_of_ne n_neq
    have diff_neq_zero: ((if n < a_max_num then a_coords n else 0) - if n < b_max_num then b_coords n else 0) ≠ 0 := by

      by_cases n_lt_a_max: n < a_max_num
      . simp [n_lt_a_max]
        by_cases n_lt_b_max: n < b_max_num
        . simp [n_lt_b_max, coord_neq]
        . simp [n_lt_b_max]
          by_contra!
          simp [this] at coord_neq
          simp at n_lt_b_max
          have b_coord_zero := b_coord_zero_gt n n_lt_b_max
          contradiction
      . simp only [n_lt_a_max]
        simp only [↓reduceIte, zero_sub, ne_eq, neg_eq_zero]
        by_cases n_lt_b_max: n < b_max_num
        . simp [n_lt_b_max]
          simp at n_lt_a_max
          have ac := a_coord_zero_gt n n_lt_a_max
          simp [ac] at coord_neq
          exact coord_neq
        . simp only [n_lt_b_max]
          simp
          simp [n_lt_a_max, n_lt_b_max] at n_lt_max
    simp [diff_neq_zero] at t_eq_zero
    exact t_eq_zero

    intro x hx hx_not_in
    simp [hx_not_in]

    intro x hx hx_not_in
    simp [hx_not_in]


lemma tree_supp_disjoint (t: ReverseTree): t.getData.b.support ∩ t.getData.a.support = ∅ := by
  match t with
    | .root =>
      simp [ReverseTree.getData, xSeq]
      have one_ne_zero: (1: ℚ) ≠ 0 := by
        simp
      rw [Finsupp.support_single_ne_zero 0 one_ne_zero]
      rw [Finsupp.support_single_ne_zero 1 one_ne_zero]
      simp
    | .left parent =>
        simp [ReverseTree.getData, xSeq]
        obtain ⟨_, g, m, m_le_newnum, m_supp_lt, b_linear_comb⟩ := tree_linear_comb parent
        rw [b_linear_comb]
        by_contra!
        obtain ⟨x, hx⟩ := Finset.Nonempty.exists_mem (Finset.nonempty_of_ne_empty this)
        have x_in_cur: x ∈ (fun₀ | newNum parent => (1: ℚ)).support := by
          exact Finset.mem_of_mem_inter_left hx

        have x_in_parent: x ∈ (∑ i ∈ Finset.range m, g i • basis_n i).support := by
          exact Finset.mem_of_mem_inter_right hx

        have one_ne_zero: (1 : ℚ) ≠ 0 := by
          simp
        have bar := Finsupp.support_single_ne_zero (newNum parent) one_ne_zero
        simp [bar] at x_in_cur

        have x_lt_max := Finset.le_max x_in_parent
        have support_subset := Finsupp.support_finset_sum (s := Finset.range m) (f := fun i => g i • basis_n i)
        --simp [basis_n] at support_subset

        have supp_single: ∀ x ∈ Finset.range m, ((g x) • (Finsupp.single x 1 : ℕ →₀ ℚ)).support ⊆ Finset.range m := by
          intro x hx
          have foo := Finsupp.support_single_subset (a := x) (b := ( 1: ℚ))
          have x_single_subset: {x} ⊆ Finset.range m := by
            simp
            simp at hx
            exact hx
          have mul_support := Finsupp.support_smul (b := g x) (g := fun₀ | x => (1: ℚ))
          have first_trans := Finset.Subset.trans mul_support foo
          have second_trans := Finset.Subset.trans first_trans x_single_subset
          exact second_trans


        have mul_supp_subset: ∀ i ∈ Finset.range m, (g i • basis_n i).support ⊆ (basis_n i).support := by
          intro i hi
          exact Finsupp.support_smul

        simp only [basis_n, Finsupp.coe_basisSingleOne, Finsupp.smul_single,
          smul_eq_mul, mul_one] at mul_supp_subset





        have bar := (Finset.biUnion_subset (s := Finset.range m) (t := fun x => (g x • (Finsupp.single x 1 : ℕ →₀ ℚ)).support)).mpr supp_single
        have x_in_biunion: x ∈ ((Finset.range m).biUnion fun x ↦ (g x • basis_n x).support) := by
          apply Finset.mem_of_subset support_subset x_in_parent

        simp only [basis_n, Finsupp.coe_basisSingleOne] at x_in_biunion
        have x_in_range: x ∈ Finset.range m := by
          apply Finset.mem_of_subset bar x_in_biunion

        have x_lt_m: x < m := by
          simp at x_in_range
          exact x_in_range
        linarith
    | .right parent =>
      -- TODO - a lot of this could probably be factored out and shared between the left and right branches
      simp [ReverseTree.getData, xSeq]
      obtain ⟨⟨a_g, a_m, a_m_le_newnum, a_m_supp_lt, a_linear_comb⟩, b_g, b_m, b_m_le_newnum, b_m_supp_lt, b_linear_comb⟩ := tree_linear_comb parent
      rw [a_linear_comb, b_linear_comb]
      by_contra!
      obtain ⟨x, hx⟩ := Finset.Nonempty.exists_mem (Finset.nonempty_of_ne_empty this)
      have x_in_cur: x ∈ (fun₀ | newNum parent => (1: ℚ)).support := by
        exact Finset.mem_of_mem_inter_right hx

      have x_in_sum := Finset.mem_of_mem_inter_left hx
      have x_lt_max := Finset.le_max x_in_sum

      have one_ne_zero: (1 : ℚ) ≠ 0 := by
        simp
      have newnum_support := Finsupp.support_single_ne_zero (newNum parent) one_ne_zero
      simp [newnum_support] at x_in_cur
      have newnum_ge_max: (max a_m b_m) ≤ newNum parent := by
        simp
        exact ⟨a_m_le_newnum, b_m_le_newnum⟩

      rw [← Finset.sum_extend_by_zero] at hx
      nth_rw 2 [← Finset.sum_extend_by_zero] at hx

      have a_subset_max: Finset.range a_m ⊆ Finset.range (max a_m b_m) := by
        simp
      have b_subset_max: Finset.range b_m ⊆ Finset.range (max a_m b_m) := by
        simp

      have a_sum_extend: (∑ i ∈ Finset.range a_m, if i ∈ Finset.range a_m then a_g i • basis_n i else 0) = (∑ i ∈ Finset.range (max a_m b_m), if i ∈ Finset.range a_m then a_g i • basis_n i else 0) := by
        apply Finset.sum_subset a_subset_max ?_
        intro x hx x_not_in
        simp [x_not_in]

      have b_sum_extend: (∑ i ∈ Finset.range b_m, if i ∈ Finset.range b_m then b_g i • basis_n i else 0) = (∑ i ∈ Finset.range (max a_m b_m), if i ∈ Finset.range b_m then b_g i • basis_n i else 0) := by
        apply Finset.sum_subset b_subset_max ?_
        intro x hx x_not_in
        simp [x_not_in]

      rw [a_sum_extend, b_sum_extend] at hx
      rw [← Finset.sum_sub_distrib] at hx

      -- TODO - can we avoid rewriting the sum twice (for x_in_sum and for hx)
      rw [← Finset.sum_extend_by_zero] at x_in_sum
      nth_rw 2 [← Finset.sum_extend_by_zero] at x_in_sum
      rw [a_sum_extend, b_sum_extend] at x_in_sum
      rw [← Finset.sum_sub_distrib] at x_in_sum

      have supp_single: ∀ g: ℕ →₀ ℚ, ∀ x ∈ Finset.range (max a_m b_m), ((g x) • (Finsupp.single x 1 : ℕ →₀ ℚ)).support ⊆ Finset.range (max a_m b_m) := by
        intro g x hx
        have foo := Finsupp.support_single_subset (a := x) (b := ( 1: ℚ))
        have x_single_subset: {x} ⊆ Finset.range (max a_m b_m) := by
          simp
          simp at hx
          exact hx
        have mul_support := Finsupp.support_smul (b := g x) (g := fun₀ | x => (1: ℚ))
        have first_trans := Finset.Subset.trans mul_support foo
        have second_trans := Finset.Subset.trans first_trans x_single_subset
        exact second_trans


      have mul_supp_subset: ∀ g: ℕ →₀ ℚ, ∀ i ∈ Finset.range (max a_m b_m), (g i • basis_n i).support ⊆ (basis_n i).support := by
        intro g i hi
        exact Finsupp.support_smul

      have combined_supp_subset: ∀ x ∈ Finset.range (max a_m b_m), ((if x ∈ Finset.range a_m then a_g x • basis_n x else 0) - if x ∈ Finset.range b_m then b_g x • basis_n x else 0).support ⊆ Finset.range (max a_m b_m) := by
        intro x hx
        by_cases x_lt_a: x < a_m
        . by_cases x_lt_b: x < b_m
          . simp [x_lt_a, x_lt_b]
            have a_supp := supp_single a_g x hx
            have b_supp := supp_single b_g x hx
            have support_sub_subset := Finsupp.support_sub (f := (fun₀ | x => a_g x)) (g := fun₀ | x => b_g x)
            have support_union_subset := Finset.union_subset_iff.mpr ⟨a_supp, b_supp⟩
            simp at support_union_subset
            apply Finset.Subset.trans support_sub_subset support_union_subset
          . simp [x_lt_a, x_lt_b]
            have a_supp := supp_single a_g x hx
            simp at a_supp
            exact a_supp
        . by_cases x_lt_b: x < b_m
          . simp [x_lt_a, x_lt_b]
            have b_supp := supp_single b_g x hx
            simp at b_supp
            exact b_supp
          . simp [x_lt_a, x_lt_b]


      simp only [basis_n, Finsupp.coe_basisSingleOne, Finsupp.smul_single,
          smul_eq_mul, mul_one] at mul_supp_subset

      have biunion_subset := (Finset.biUnion_subset (s := Finset.range (max a_m b_m))).mpr combined_supp_subset
      have support_subset := Finsupp.support_finset_sum (s := Finset.range (max a_m b_m)) (f := fun x => ((if x ∈ Finset.range a_m then a_g x • basis_n x else 0) - if x ∈ Finset.range b_m then b_g x • basis_n x else 0))

      have x_in_biunion := Finset.mem_of_subset support_subset x_in_sum

      simp only [basis_n, Finsupp.coe_basisSingleOne] at x_in_biunion
      have x_in_range: x ∈ Finset.range (max a_m b_m) := by
        apply Finset.mem_of_subset biunion_subset x_in_biunion

      have x_lt_m: x < (max a_m b_m) := by
        simp at x_in_range
        simp
        exact x_in_range

      linarith
#check LinearIndependent.eq_zero_of_pair

lemma tree_vals_nonzero (t: ReverseTree) : t.getData.a ≠ 0 ∧ t.getData.b ≠ 0 := by
  have a_neq_zero: t.getData.a ≠ 0 := by
    have bar := LinearIndependent.ne_zero 0 (tree_linear_independent t)
    simp at bar
    assumption
  have b_neq_zero: t.getData.b ≠ 0 := by
    have bar := LinearIndependent.ne_zero 1 (tree_linear_independent t)
    simp at bar
    assumption
  exact ⟨a_neq_zero, b_neq_zero⟩

lemma basis_neq_elem_diff (t: ReverseTree) (a: ℕ) (b c r: ℚ) (hb: b ≠ 0) (hc: c ≠ 0) (hr: r ≠ 0): Finsupp.single a r ≠ b • t.getData.b + c • t.getData.a := by
  by_contra!
  have coord_intersect: t.getData.b.support ∩ t.getData.a.support = ∅ := by
    apply tree_supp_disjoint t
  have coord_disjoint: Disjoint t.getData.b.support t.getData.a.support := by
    exact Finset.disjoint_iff_inter_eq_empty.mpr coord_intersect

  have b_mul_subset: (b • t.getData.b).support ⊆ t.getData.b.support := by
    exact Finsupp.support_smul
  have c_mul_subset: (c • t.getData.a).support ⊆ t.getData.a.support := by
    exact Finsupp.support_smul

  have mul_support_disjoint: Disjoint (b • t.getData.b).support (c • t.getData.a).support := by
    exact Disjoint.mono b_mul_subset c_mul_subset coord_disjoint

  have a_neq_zero: t.getData.a ≠ 0 := by
    have bar := LinearIndependent.ne_zero 0 (tree_linear_independent t)
    simp at bar
    assumption
  have b_neq_zero: t.getData.b ≠ 0 := by
    have bar := LinearIndependent.ne_zero 1 (tree_linear_independent t)
    simp at bar
    assumption
  have single_card_one: (fun₀ | a => r).support.card = 1 := by
    rw [Finsupp.support_single_ne_zero a hr]
    simp

  let s: Finset (Fin 2) := {0, 1}
  let g := fun (i: Fin 2) => if i = 0 then b • t.getData.b else c • t.getData.a
  have g_supp_disjoint: ∀ (i_1 i_2: Fin 2), i_1 ≠ i_2 → Disjoint (g i_1).support (g i_2).support := by
    intro i_1 i_2 i_neq
    simp [g]
    by_cases i_1_eq: i_1 = 0
    .
      have i_2_eq: i_2 = 1 := by
        have bar := i_2.isLt
        omega
      simp [i_1_eq, i_2_eq]
      exact mul_support_disjoint
    . have i_1_eq: i_1 = 1 := by
        have bar := i_1.isLt
        omega
      have i_2_eq: i_2 = 0 := by
        have bar := i_2.isLt
        omega
      simp [i_1_eq, i_2_eq]
      exact mul_support_disjoint.symm


  have support_sum := Finsupp.support_sum_eq_biUnion s g_supp_disjoint
  simp [s, g] at support_sum

  have a_supp_card: 1 ≤ t.getData.a.support.card := by
    have bar := Finsupp.card_support_eq_zero.not.mpr a_neq_zero
    exact Nat.one_le_iff_ne_zero.mpr bar
  have b_supp_card: 1 ≤ t.getData.b.support.card := by
    have bar := Finsupp.card_support_eq_zero.not.mpr b_neq_zero
    exact Nat.one_le_iff_ne_zero.mpr bar

  have b_mul_card: 1 ≤ (b • t.getData.b).support.card := by
    rw [Finsupp.support_smul_eq hb]
    exact b_supp_card

  have c_mul_card: 1 ≤ (c • t.getData.a).support.card := by
    rw [Finsupp.support_smul_eq hc]
    exact a_supp_card

  have card_union_sum := Finset.card_union_eq_card_add_card.mpr mul_support_disjoint


  have card_sum_le: 2 ≤ ((b • t.getData.b).support ∪ (c • t.getData.a).support).card := by
    rw [Finset.card_union_eq_card_add_card.mpr mul_support_disjoint]
    linarith

  rw [Finsupp.ext_iff'] at this
  obtain ⟨support_eq, _⟩ := this
  have card_eq: (fun₀ | a => r).support.card = (b • t.getData.b + c • t.getData.a).support.card := by
    rw [support_eq]

  rw [single_card_one] at card_eq
  rw [support_sum, card_union_sum] at card_eq
  linarith

lemma finsupp_new_zero_newnum (t: ReverseTree) (a b: ℚ) (hb: b ≠ 0): (fun₀ | 0 => (a: ℚ)) ≠ (fun₀ | newNum t => (b: ℚ)) := by
  by_contra!
  have eval_at := DFunLike.congr (x := newNum t) (y := newNum t) this rfl
  simp at eval_at
  have t2_gt_one := newnem_gt_one t
  have newnum_new_zero: 0 ≠ newNum t := by
    omega
  simp [newnum_new_zero] at eval_at
  rw [eq_comm] at eval_at
  contradiction

lemma finsupp_new_one_newnum (t: ReverseTree) (a b: ℚ) (hb: b ≠ 0): (fun₀ | 1 => (a: ℚ)) ≠ (fun₀ | newNum t => (b: ℚ)) := by
  by_contra!
  have eval_at := DFunLike.congr (x := newNum t) (y := newNum t) this rfl
  simp at eval_at
  have t2_gt_one := newnem_gt_one t
  have newnum_new_zero: 1 ≠ newNum t := by
    omega
  simp [newnum_new_zero] at eval_at
  rw [eq_comm] at eval_at
  contradiction

lemma xseq_zero_neq_b (t: ReverseTree) (s: ℚ) (hs: s ≠ 0): xSeq 0 ≠ s • t.getData.b := by
  by_contra!
  match t with
  | .root =>
      -- TODO - there must be a simpler way of doing 'congr'
      simp [ReverseTree.getData, xSeq] at this
      have eval_at := DFunLike.congr (x := 0) (y := 0) this rfl
      simp at eval_at
  | .left t2_parent_parent =>
      simp [ReverseTree.getData, xSeq] at this
      have fun_neq := finsupp_new_zero_newnum t2_parent_parent 1 s hs
      contradiction
    | .right t2_parent_parent =>
      simp [ReverseTree.getData, xSeq] at this
      have neg_s_neq_zero: (-s) ≠ 0 := by
        simp
        exact hs
      have vals_neq := basis_neq_elem_diff t2_parent_parent 0 (-s) s 1 neg_s_neq_zero hs (by simp)
      simp only [one_smul, neg_one_smul, add_comm] at vals_neq
      rw [neg_smul, ← sub_eq_add_neg] at vals_neq
      rw [smul_sub] at this
      contradiction


lemma partial_function (t1: ReverseTree) (t2: ReverseTree) (h_a_eq: t1.getData.a = t2.getData.a) (h_min: ∀ (tree1 tree2: ReverseTree), tree1.getData.a = tree2.getData.a ∧ tree1 ≠ tree2 → newNum t1 ≤ newNum tree1) (this: t1 ≠ t2): False := by
  match t1 with
  | .root =>
    match t2 with
    | .root => contradiction
    | .left t2_parent =>
        simp [ReverseTree.getData] at h_a_eq
        have b_neq := xseq_zero_neq_b t2_parent (-1) (by simp)
        simp at b_neq
        contradiction
    | .right t2_parent =>
        simp [ReverseTree.getData, xSeq] at h_a_eq
        have fun_neq := finsupp_new_zero_newnum t2_parent 1 1 (by simp)
        contradiction
  | .left t1_parent =>
    match t2 with
    | .root =>
        simp [ReverseTree.getData] at h_a_eq
        have b_neq := xseq_zero_neq_b t1_parent (-1) (by simp)
        simp at b_neq
        rw [eq_comm] at b_neq
        contradiction
    | .left t2_parent =>
      -- 4. So, they must both be left trees:
        match t1_parent with
        | .root =>
            simp [ReverseTree.getData] at h_a_eq
            match t2_parent with
            | .root => contradiction
            | .left t2_parent_parent =>
                simp [ReverseTree.getData] at h_a_eq
                apply xseq_injective at h_a_eq
                have val_gt_one := newnem_gt_one t2_parent_parent
                omega
            | .right t2_parent_parent =>
                simp [ReverseTree.getData, xSeq] at h_a_eq
                have vals_neq := basis_neq_elem_diff t2_parent_parent 1 (-1) 1 1 (by simp) (by simp) (by simp)
                simp only [one_smul, neg_one_smul] at vals_neq
                rw [add_comm, ← sub_eq_add_neg] at vals_neq
                contradiction
        | .left t1_parent_parent =>
            match t2_parent with
            | .root =>
              simp [ReverseTree.getData] at h_a_eq
              apply xseq_injective at h_a_eq
              have val_gt_one := newnem_gt_one t1_parent_parent
              omega
            | .left t2_parent_parent =>
              -- If both parents are left trees - we know that left trees have unique 'b' values so their parents must be the same node. But then our original nodes are left children of the same node, so they're again the same node - contradiction
              simp [ReverseTree.getData] at h_a_eq
              apply xseq_injective at h_a_eq
              apply newnum_injective at h_a_eq
              rw [h_a_eq] at this
              contradiction
            | .right t2_parent_parent =>
                simp [ReverseTree.getData, xSeq] at h_a_eq
                rw [← Finsupp.single_neg] at h_a_eq
                have vals_neq := basis_neq_elem_diff t2_parent_parent (newNum t1_parent_parent) (1) (-1) (-1) (by simp) (by simp) (by simp)
                simp at vals_neq
                rw [← sub_eq_add_neg, ← Finsupp.single_neg] at vals_neq
                contradiction
        | .right t1_parent_parent =>
          match t2_parent with
          | .root =>
            simp [ReverseTree.getData, xSeq] at h_a_eq
            rw [← Finsupp.single_neg] at h_a_eq
            have vals_neq := basis_neq_elem_diff t1_parent_parent 1 (1) (-1) (-1) (by simp) (by simp) (by simp)
            simp only [one_smul, neg_one_smul] at vals_neq
            rw [← sub_eq_add_neg] at vals_neq
            rw [eq_comm] at h_a_eq
            contradiction
          | .left t2_parent_parent =>
            simp [ReverseTree.getData, xSeq] at h_a_eq
            rw [← Finsupp.single_neg] at h_a_eq
            have vals_neq := basis_neq_elem_diff t1_parent_parent (newNum t2_parent_parent) (1) (-1) (-1) (by simp) (by simp) (by simp)
            simp only [one_smul, neg_one_smul] at vals_neq
            rw [← sub_eq_add_neg] at vals_neq
            rw [eq_comm] at h_a_eq
            contradiction
          | .right t2_parent_parent =>
            -- So, both parents must be right trees.
            simp [ReverseTree.getData] at h_a_eq
            -- TODO - add a minimality assumption to the original top-level 'by_contra!' somehow, and use that here
            have parents_a_neq: t1_parent_parent.getData.a ≠ t2_parent_parent.getData.a := by sorry

            -- So, the parents look like (c, d) and (x, y) with c ≠ x, We must also have d ≠ y to satisfy 'c - d = x - y'
            have parents_b_neq: t1_parent_parent.getData.b ≠ t2_parent_parent.getData.b := by
              by_contra!
              rw [this] at h_a_eq
              simp at h_a_eq
              contradiction

            -- TODO adjust it in the argument instead of 'reverting' it like this
            apply_fun (fun x => -1 • x) at h_a_eq
            simp at h_a_eq
            have common_ancestor := cross_eq_same_parent parents_a_neq h_a_eq
            apply_fun (fun x => -1 • x) at h_a_eq
            simp at h_a_eq

            obtain ⟨ancestor, h_ancestor⟩ := common_ancestor
--     Let this common ancestor be (f, g).
--     Then, the parents are (-g, x_i) and (x_i, f - g),
--     We have -g - x_i = x_i - (f - g)
--              -g -x_i = x_i - f + g
--              0 = 2x_i + 2g - f
--     This is impossible, because x_i is fresh: g and/or f would need to contain x_i, which is impossible.
            cases h_ancestor with
            | inl left_right =>
              simp [left_right.1, left_right.2, ReverseTree.getData] at h_a_eq
              have x_seq_add: xSeq (newNum ancestor) + ancestor.getData.b  + xSeq (newNum ancestor) = ancestor.getData.a - ancestor.getData.b := by
                exact add_eq_of_eq_sub h_a_eq

              have x_swap: xSeq (newNum ancestor) + ancestor.getData.b  + xSeq (newNum ancestor) = xSeq (newNum ancestor) + xSeq (newNum ancestor) + ancestor.getData.b := by
                exact
                  Eq.symm
                    (add_rotate (xSeq (newNum ancestor)) (xSeq (newNum ancestor))
                      ancestor.getData.b)

              rw [x_swap] at x_seq_add
              have sub_b: xSeq (newNum ancestor) + xSeq (newNum ancestor) = ancestor.getData.a - ancestor.getData.b - ancestor.getData.b := by
                apply_fun (fun x => x - ancestor.getData.b) at x_seq_add
                simp at x_seq_add
                exact x_seq_add

              rw [← two_nsmul, sub_sub, ← two_nsmul] at sub_b

              have ⟨⟨g_a, m_a, m_a_gt, a_supp_max, a_repr⟩, ⟨g_b, m_b, m_b_gt, b_supp_max, b_repr⟩⟩ := tree_linear_comb ancestor

              rw [← Finset.sum_extend_by_zero] at a_repr
              rw [← Finset.sum_extend_by_zero] at b_repr



              have a_subset_newnum: Finset.range m_a ⊆ Finset.range (newNum ancestor) := by
                simp
                exact m_a_gt
              have b_subset_newnum: Finset.range m_b ⊆ Finset.range (newNum ancestor) := by
                simp
                exact m_b_gt

              rw [Finset.sum_subset a_subset_newnum ?_] at a_repr
              rw [Finset.sum_subset b_subset_newnum ?_] at b_repr
              rw [a_repr, b_repr] at sub_b
              rw [← Finset.sum_nsmul] at sub_b
              rw [← Finset.sum_sub_distrib] at sub_b
              simp only [basis_n, xSeq] at sub_b
              apply n_q_basis.ext_elem_iff.mp at sub_b
              specialize sub_b (newNum ancestor)
              simp only [n_q_basis, Finsupp.basisSingleOne_repr, Finsupp.coe_basisSingleOne, Finsupp.smul_single, nsmul_eq_mul, Nat.cast_ofNat, mul_one, LinearEquiv.refl_apply, Finsupp.single_eq_same, Finset.mem_range, smul_eq_mul, smul_ite, Finsupp.single_mul, smul_zero, Finsupp.coe_sub, Finsupp.coe_finset_sum, Pi.sub_apply, Finset.sum_apply] at sub_b
              -- TODO - avoid copy-pasting the entire sum
              have sum_eq_zero: ∑ x ∈ Finset.range (newNum ancestor), (((if x < m_a then fun₀ | x => g_a x else 0) (newNum ancestor) - (if x < m_b then (fun₀ | x => (2: ℚ)) * fun₀ | x => g_b x else 0) (newNum ancestor))) = ∑ x ∈ Finset.range (newNum ancestor), 0 := by
                apply Finset.sum_congr rfl
                intro x hx
                simp at hx
                have x_neq_newnum: x ≠ newNum ancestor := by
                  linarith
                by_cases x_lt_a: x < m_a
                . by_cases x_lt_b: x < m_b
                  . simp [x_neq_newnum, x_lt_a, x_lt_b]
                  . simp [x_neq_newnum, x_lt_a, x_lt_b]
                . by_cases x_lt_b: x < m_b
                  . simp [x_neq_newnum, x_lt_a, x_lt_b]
                  . simp [x_neq_newnum, x_lt_a, x_lt_b]

              rw [sum_eq_zero] at sub_b
              simp at sub_b

              -- TODO - move these up earlier when we do `Finset.sum_subset a_subset_newnum ?_`
              . intro x hx x_not_in
                simp [x_not_in]
              . intro x hx x_not_in
                simp [x_not_in]



            | inr right_left =>
              sorry
    | .right t2_parent =>
      simp [ReverseTree.getData] at h_a_eq
      match t1_parent with
      | .root =>
        simp [ReverseTree.getData, xSeq] at h_a_eq
        have fun_neq := finsupp_new_one_newnum t2_parent (-1) 1 (by simp)
        rw [← Finsupp.single_neg] at h_a_eq
        contradiction
      | .left t1_parent_parent =>
        simp [ReverseTree.getData, xSeq] at h_a_eq
        rw [← Finsupp.single_neg] at h_a_eq
        rw [Finsupp.single_eq_single_iff] at h_a_eq
        match h_a_eq with
        | .inl ⟨_, neq_eq_one⟩ =>
          contradiction
        | .inr ⟨neq_eq_one, _⟩ =>
          contradiction
      | .right t1_parent_parent =>
        simp [ReverseTree.getData, xSeq] at h_a_eq
        have vals_neq := basis_neq_elem_diff t1_parent_parent (newNum t2_parent) 1 (-1) 1 (by simp) (by simp) (by simp)
        simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at vals_neq
        rw [eq_comm] at h_a_eq
        contradiction
  | .right t1_parent =>
    match t2 with
    | .root =>
        simp [ReverseTree.getData] at h_a_eq
        have newnum_gt_one := newnem_gt_one t1_parent
        simp [xSeq] at h_a_eq
        have one_ne_zero: (1 : ℚ) ≠ 0 := by
          simp
        have single_injective := Finsupp.single_left_injective (α := ℕ) one_ne_zero
        simp [Function.Injective] at single_injective
        specialize @single_injective (newNum t1_parent) 0 h_a_eq
        linarith
    | .left t2_parent =>
      simp [ReverseTree.getData] at h_a_eq
      match t2_parent with
      | .root =>
        simp [ReverseTree.getData, xSeq] at h_a_eq
        rw [← Finsupp.single_neg] at h_a_eq
        have eval_at: (fun₀ | newNum t1_parent => 1) (newNum t1_parent) = (fun₀ | 1 => (-1: ℚ)) (newNum t1_parent) := by
          refine DFunLike.congr ?h₁ rfl
          exact h_a_eq
        simp at eval_at
        have newnum_gt_one: 1 < newNum t1_parent := by
          exact newnem_gt_one t1_parent
        have newnum_neq_one: 1 ≠ newNum t1_parent := by
          linarith
        rw [Finsupp.single_apply] at eval_at
        simp [newnum_neq_one] at eval_at
      | .left t2_parent_parent =>
          -- b is fresh - it must therefore come from a different node, which will therefore have a different basis element - contradiction.
          simp [ReverseTree.getData, xSeq] at h_a_eq
          apply eq_neg_iff_add_eq_zero.mp at h_a_eq
          have basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis
          simp [n_q_basis] at basis_indep
          have linear_indep: LinearIndependent ℚ ![fun₀ | (newNum t1_parent) => (1 : ℚ), fun₀ | (newNum t2_parent_parent) => 1] := by
            apply LinearIndependent.pair_iff.mpr
            intro s t h_sum_zero

            simp [linearIndependent_iff'] at basis_indep
            specialize basis_indep {newNum t1_parent, newNum t2_parent_parent}
            have parents_neq: t1_parent ≠ t2_parent_parent := by
              by_contra! other_parents_eq
              simp [other_parents_eq] at h_a_eq
              simp [add_eq_zero_iff_eq_neg] at h_a_eq
              have eq_zero: (fun₀ | newNum t2_parent_parent => 1) = 0 := by
                simp [← Finsupp.single_neg] at h_a_eq
                simp [Finsupp.single] at h_a_eq
                contradiction
              simp at eq_zero

            have nums_not_eq: newNum t1_parent ≠  newNum t2_parent_parent := by
              apply Function.Injective.ne newnum_injective parents_neq
            have num_reverse: newNum t2_parent_parent ≠ newNum t1_parent := by
              exact id (Ne.symm nums_not_eq)
            let g : ℕ → ℚ := fun n => if n = newNum t1_parent then s else if n = newNum t2_parent_parent then t else 0
            have finsum_to_pair := Finset.sum_pair (f := fun x => fun₀ | x => g x) nums_not_eq
            specialize basis_indep g
            simp only [g] at basis_indep
            simp [g] at finsum_to_pair
            simp only [finsum_to_pair] at basis_indep
            simp only [num_reverse] at basis_indep
            simp at h_sum_zero
            specialize basis_indep h_sum_zero
            have s_eq_zero := basis_indep (newNum t1_parent)
            simp at s_eq_zero
            have t_eq_zero := basis_indep (newNum t2_parent_parent)
            simp [num_reverse] at t_eq_zero
            exact ⟨s_eq_zero, t_eq_zero⟩
          simp [LinearIndependent.pair_iff] at linear_indep
          specialize linear_indep 1 1 h_a_eq
          contradiction
      | .right t2_parent_parent =>
        --  b = p - q for some p and q. We know that p and q have disjoint coordinates, and q is not zero, so we have two different representations for 'a' - impossible.
        simp [ReverseTree.getData, xSeq] at h_a_eq
        have vals_neq := basis_neq_elem_diff t2_parent_parent (newNum t1_parent) 1 (-1) 1 (by simp) (by simp) (by simp)
        simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at vals_neq
        contradiction
    | .right t2_parent =>
      -- If they're both right trees, contradiction - all right trees have unique 'a' values
      simp [ReverseTree.getData] at h_a_eq
      apply xseq_injective at h_a_eq
      apply newnum_injective at h_a_eq
      simp [h_a_eq] at this






-- The (a, b) values have disjoint coordinates (of basis elements) - prove this by induction

-- FOR REAL?
-- 1. Suppose two distinct nodes have the same 'a' value. Let one of these nodes have minimal depth
-- 2. DONE: If they're both right trees, contradiction - all right trees have unique 'a' values
-- 3. IMPROVE: If one is left and the other is right:
---  We have a = -b for some b. There are two cases:
--    b is fresh - it must therefore come from a different node, which will therefore have a different basis element - contradiction.
--    b = p - q for some p and q. We know that p and q have disjoint coordinates, and q is not zero, so we have two different representations for 'a' - impossible.
--    OLD: We have a fresh basis element equal to the negation of some linear combination - this is impossible, by linear independence. Todo - what if we have -(-(a))
-- 4. So, they must both be left trees:
-- * Now consider their parents, which look like (_, -a)
--   * If both parents are left trees - we know that left trees have unique 'b' values so their parents must be the same node. But then our original nodes are left children of the same node, so they're again the same node - contradiction
--   * If one is left and the other is right, then see the similar argument above: then we have a fresh basis (from the left tree) equal to 'p - q' (a lienar combination of basis elements),  which is a condiction (TODO - what if 'q' is zero?)
--   So, both parents must be right trees.
--   The parents have right nodes 'c - d = x - y':
--   If the parents have the same 'a' value, then this would contradict the minimal depth of our starting node.
--   So, the parents look like (c, d) and (x, y) with c ≠ x, We must also have d ≠ y to satisfy 'c - d = x - y'
--   One element in each pair must be fresh - assume wlog that 'c' and 'x' are fresh.
--     Then, in order for 'c - d = x - y', we must have 'x' occuring in 'd' and 'c' occuring in 'y'.
--     This means depth(parent_one) >= depth(parent_two) and depth(parent_two) >= depth(parent_one), since each must have at least the depth where the other fresh element is first introduced.
--     Thus, depth(parent_one) = depth(parent_two).
--     The only way for this to work is if the parents look like (x_i, p) and (q, x_i) - that this, the same fresh node.
--      Otherwise, one of the nodes will contain a fresh element that's not in the other node.
--     This implies that the parents are the left/right children of the same node.
--     Let this common ancestor be (f, g).
--     Then, the parents are (-g, x_i) and (x_i, f - g),
--     We have -g - x_i = x_i - (f - g)
--              -g -x_i = x_i - f + g
--              0 = 2x_i + 2g - f
--     This is impossible, because x_i is fresh: g and/or f would need to contain x_i, which is impossible.
--     DONE???
--
--
--
--   If they're both right children, then the 'c' and 'x' values are distinct fresh elements, so we can't have 'c - d = x - y'
--   If they're both left children, then 'd' and 'y' values are distinct fresh elements, so we can't have 'c - d = x - y'
--   If one is left and one is right, then wlog 'c' is fresh and 'y' is fresh, so we can't have 'c - d = x - y'
--   We get a contradiction in all cases.
---  DONE?
--

---- WRONG: we could have '(e_1 + e_2) - e_3 = (e_1) - (-e_2 + e_3)
--         since the elements in the pair have disjoint coordinates, we must have c = x and d = y
--      Then, the grandparents are (c, d) and (x, y). This gives us two nodes with the same 'a' value,
--      one of which has a strictly smaller depth than our original node of minimal depth - contradictiob.






--   The grantparents are then (c, d) and (e, f) with c - d = a and e - f = a
    -- If both the grandparents are right trees, then
-- Another bad idea:
-- New proof idea:
-- * A pair (a, b) always have disjoint basis elements (this is stronger than linear independency - e.g. two non-perpendiculatr vectors in the plane are linearly independent)
--   Prove this by induction


-- New idea:
--  Each coefficient must be in {-1, 0, 1}.
--  The values determine our path from the root to the node.
--  The coefficient representation is unique (because it's the representation in our basis), so two nodes with the same 'a' value has the same coefficients,
--  and therefore the same path, thus are the same node.

-- Trying again:

-- Suppose two distinct nodes have the same 'a' value.
-- If they're both right trees, contradiction - all right trees have unique 'a' values
-- If one is left and the other is right, we have a fresh basis element equal to something - this should be impossible, because the disjoint coordinates implies no cancellation.
-- So, they must both be left trees:


-- Latest idea:
-- Suppose two distinct nodes have the same 'a' value.
-- If they're both right trees, contradiction - all right trees have unique 'a' values
-- If one is left and the other is right, then we have a fresh basis element equal to the negation of some linear combination - this is impossible, by linear independence. Todo - what if we have -(-(a))
-- So, they must both be left trees:
-- * Now consider their parents, which look like (_, -a)
--   * If both parents are left trees - we know that left trees have unique 'b' values so their parents must be the same node. But then our original nodes are left children of the same parents, so they're equal - contradiction
--   * If one is left and the other is right, then we have a fresh basis (from the left tree) equal to 'p - q' (a lienar combination of basis elements),  which is a condiction (TODO - what if 'q' is zero?)
--   So, both parents must be right trees.
--   The parents look like (p, a) and (q, a).

--   The grantparents are then (c, d) and (e, f) with c - d = a and e - f = a
    -- If both the grandparents are right trees, then
-- Another bad idea:
-- New proof idea:
-- * A pair (a, b) always have disjoint basis elements (this is stronger than linear independency - e.g. two non-perpendiculatr vectors in the plane are linearly independent)
--   Prove this by induction
--


-- BAD - highest index can decrease (e.g. x3 -> x1 + x2),  so this won't work
-- High-level idea:
-- If we have two distinct tree nodes with the same 'a' value, then those trees have different 'newNum' values (since they're distinct)
-- We can then write 'a' in two ways:

-- ∑ i = 0..(newNum t1), t1_coord i * basis_n i
-- ∑ i = 0..(newNum t2), t2_coord i * basis_n i

-- This should give us a contradiction by the fact that the basis representation of 'a' is unique
-- This requires that we actually have a nonzero t1_coord that's > (newNum t1), where newNum t1 < newNum t2
-- I already did something like this in the linear independency proof, so I should be able to reuse that
----------
--

lemma temp_partial_function: ∀ (t1 t2: ReverseTree), (t1.getData.a = t2.getData.a) → t1 = t2 := by
  by_contra!
  let counterexamples := {(t1, t2) : (ReverseTree × ReverseTree) | t1.getData.a = t2.getData.a ∧ t1 ≠ t2}
  let first_newnum := fun ((t1, t2): (ReverseTree × ReverseTree)) => newNum t1

  --let min_num := counter_nums.min counter_nonempty
  have counter_nonempty: counterexamples.Nonempty := by
    obtain ⟨t1, t2, h_t1_eq⟩ := this
    simp [Set.Nonempty, counterexamples]
    use t1
    use t2

  let counter_nums := first_newnum '' counterexamples
  have counter_nums_nonempty: counter_nums.Nonempty := by
    simp [counter_nums]
    exact counter_nonempty

  let min_newnum := Nat.lt_wfRel.wf.min counter_nums counter_nums_nonempty
  have min_newnum_le: ∀ (tree1 tree2: ReverseTree), tree1.getData.a = tree2.getData.a ∧ tree1 ≠ tree2 → min_newnum ≤ newNum tree1 := by
    intro tree1 tree2 h_neq
    have trees_in: (tree1, tree2) ∈ counterexamples := by
      simp [counterexamples]
      exact h_neq
    have num_in: newNum tree1 ∈ counter_nums := by
      simp only [first_newnum, counter_nums, counterexamples]
      simp only [Set.mem_image, Set.mem_setOf_eq]
      use (tree1, tree2)

    have min_number := WellFounded.min_le (Nat.lt_wfRel.wf) num_in
    exact min_number

  have min_pair: ∃ (t1 t2: ReverseTree), (t1, t2) ∈ counterexamples ∧ newNum t1 = min_newnum := by
    have min_mem: min_newnum ∈ counter_nums := by
      apply WellFounded.min_mem
    simp [counter_nums] at min_mem
  obtain ⟨t1, t2, h_t1_eq, h_min⟩ := min_pair
  simp [counterexamples] at h_t1_eq
  rw [← h_min] at min_newnum_le
  exact partial_function t1 t2 h_t1_eq.1 min_newnum_le h_t1_eq.2


lemma bad_partial_function (t1: ReverseTree) (t2: ReverseTree) (h_a_eq: t1.getData.a = t2.getData.a): t1 = t2 := by
  by_contra!
  have newnum_neq: newNum t1 ≠ newNum t2 := by
    intro h_eq
    have t1_eq_t2: t1 = t2 := by
      apply newnum_injective
      exact h_eq
    contradiction
  obtain ⟨⟨first_coords, first_m, h_first_m, first_m_supp, a_eq_first⟩, _⟩ := tree_linear_comb t1
  obtain ⟨⟨second_coords, second_m, h_second_m, second_m_supp, a_eq_second⟩, _⟩ := tree_linear_comb t2

  rw [h_a_eq] at a_eq_first
  rw [a_eq_first] at a_eq_second
  -- have foo := nonempty_denumerable_iff

  sorry


-- inductive MyTree {α: Type} where
--   | root: TreeData (α := α) 0 → MyTree
--   | left (n: ℕ) (hn: n > 0): TreeData (n - 1) → MyTree
--   | right (n: ℕ) (hn: n > 0): TreeData (n - 1) → MyTree


-- def treeAt(n: ℕ ): MyTree (α := String) :=
--   MyTree.left { MyTree.root {a := "a", b := "b"}

noncomputable abbrev diamond (f: G → G) (x y: G) := x + (f (y - x))
infix:50    " ⋄ " => diamond

lemma first_equiv (f: G → G) (x y: G):
  (diamond f (x + (y - x) + (f (-(y - x)))) (diamond f (x + (y - x) + (f (-(y - x)))) (x + y - x))) = x + (y - x) + (f (-(y - x))) + (f (f (- (f (- (y - x))))))  := by
    simp

lemma functional_equiv (f: G → G) (x y: G):
  (f (f (-(f x))) = x - (f x)) ↔ (x = diamond f (x + (y - x) + (f (-(y - x)))) (diamond f (x + (y - x) + (f (-(y - x)))) (x + y - x))) := by
  simp [diamond]


noncomputable def total_function (x: G): G := by
  by_cases x_in_tree: ∃ t: ReverseTree, x = t.getData.a
  . let t := Classical.choose x_in_tree
    have ht:= Classical.choose_spec x_in_tree
    exact t.getData.b
  . exact total_function x
    -- nonempty_denumerable_iff
