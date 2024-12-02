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

-- Hack - include the basis element 0, since the proof pdf starts numbering them at 1
def s_i := λ i: ℕ => {val ∈ all_basis | val.1 ≡ 2^i [MOD 2^(i + 1)] } ∪ (if i = 0 then {(0, basis_n 0)} else {})

lemma s_i_disjoint (i j: ℕ) (i_lt_j: i < j): s_i i ∩ s_i j = ∅ := by
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


lemma s_i_infinite (i: ℕ): (s_i i).Infinite := by
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


  -- Actual start of proof


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

lemma s_i_from_basis (i: ℕ): ∀ x ∈ s_i i, x.2 = basis_n x.1 := by
  intro x hx
  simp [s_i, Nat.ModEq] at hx
  match hx with
  | .inl left =>
      obtain ⟨⟨x_basis, h_x_basis⟩, hy⟩ := left
      rw [← h_x_basis]
      simp
  | .inr right =>
      simp [right.2]





lemma s_i_union_basis: ⋃ i, s_i i = all_basis := by
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


noncomputable def xSeq (n: ℕ): G := basis_n n


lemma basis_n_injective: Function.Injective basis_n := by
  simp [Function.Injective]
  intro n_1 n_2 h_eq
  have one_neq_zero: (1: ℚ) ≠ 0 := by
    simp
  have single_injective := Finsupp.single_left_injective (α := ℕ) one_neq_zero
  simp [Function.Injective] at single_injective
  have injective_imp := @single_injective n_1 n_2
  exact injective_imp h_eq

lemma xseq_injective: Function.Injective xSeq := by
  exact basis_n_injective

structure TreeData where
  a: G
  b: G

deriving DecidableEq

structure XVals where
  i: ℕ
  -- x_basis: Set.range x_vals ⊆ Set.range basis_n

noncomputable def XVals.x_vals (vals: XVals) (n: ℕ): G := basis_n (2^(vals.i) + n*2^(vals.i+1))
noncomputable def XVals.x_to_index (vals: XVals) (n: ℕ): ℕ := (2^(vals.i) + n*2^(vals.i+1))
lemma XVals.x_to_index_increasing (vals: XVals): StrictMono (XVals.x_to_index vals) :=
  by simp [XVals.x_to_index, StrictMono]
lemma XVals.x_to_index_inj (vals: XVals): Function.Injective (XVals.x_to_index vals) :=
  by simp [XVals.x_to_index, Function.Injective]
lemma XVals.x_to_index_eq (vals: XVals): ∀ n, vals.x_vals n = basis_n (vals.x_to_index n) := by
  simp [XVals.x_vals, XVals.x_to_index]

lemma XVals.x_inj (vals: XVals): Function.Injective vals.x_vals := by
    simp [Function.Injective]
    intro a1 a2 funs_eq
    simp [XVals.x_vals] at funs_eq
    have apply_eq: ((fun₀ | 2 ^ (vals.i) + a1 * 2 ^ (vals.i + 1) => (1: ℚ))) ( 2 ^ (vals.i) + a1 * 2 ^ (vals.i + 1)) = ((fun₀ | 2 ^ (vals.i) + a2 * 2 ^ (vals.i + 1) => 1)) (2 ^ (vals.i) + a1 * 2 ^ ((vals.i) + 1)) := by
      rw [funs_eq]
    simp at apply_eq
    simp [Finsupp.single_apply] at apply_eq
    rw [eq_comm] at apply_eq
    simp at apply_eq
    exact apply_eq.symm

lemma XVals.x_supp_nonempty (vals: XVals): ∀ n: ℕ, (vals.x_vals n).support.Nonempty := by
  intro n
  simp [XVals.x_vals, basis_n]
  refine Finsupp.support_nonempty_iff.mpr ?_
  simp

lemma XVals.x_increasing (vals: XVals): ∀ n: ℕ, ∀ m, m < n → (vals.x_vals m).support.max' (vals.x_supp_nonempty m) < (vals.x_vals n).support.min' (vals.x_supp_nonempty n) := by
  intro m n m_lt_n
  simp only [XVals.x_vals, basis_n, n_q_basis, Finsupp.coe_basisSingleOne]
  have n_supp := Finsupp.support_single_ne_zero (b := (1 : ℚ)) (2 ^ (vals.i) + n * 2 ^ (vals.i + 1)) (by simp)
  have m_supp := Finsupp.support_single_ne_zero (b := (1 : ℚ)) (2 ^ (vals.i) + m * 2 ^ (vals.i + 1)) (by simp)
  simp [n_supp, m_supp]
  exact m_lt_n

lemma XVals.x_basis (vals: XVals): Set.range vals.x_vals ⊆ Set.range basis_n := by
  intro x hx
  simp at hx
  simp
  obtain ⟨h, hy⟩ := hx
  use 2 ^ vals.i + h * 2 ^ (vals.i + 1)
  simp [XVals.x_vals] at hy
  exact hy

noncomputable def mk_x_vals (i: ℕ): XVals := by
  exact {
    i := i,
    -- x_to_index_inj := by simp [Function.Injective],
    -- x_to_index_increasing := by simp [StrictMono],
    -- x_to_index_eq := by simp,
    -- x_inj := by
    --   simp [Function.Injective]
    --   intro a1 a2 funs_eq
    --   have apply_eq: ((fun₀ | 2 ^ i + a1 * 2 ^ (i + 1) => (1: ℚ))) ( 2 ^ i + a1 * 2 ^ (i + 1)) = ((fun₀ | 2 ^ i + a2 * 2 ^ (i + 1) => 1)) (2 ^ i + a1 * 2 ^ (i + 1)) := by
    --     rw [funs_eq]
    --   simp at apply_eq
    --   simp [Finsupp.single_apply] at apply_eq
    --   rw [eq_comm] at apply_eq
    --   simp at apply_eq
    --   exact apply_eq.symm

    -- x_supp_nonempty := by
    --   intro n
    --   simp [basis_n]
    --   refine Finsupp.support_nonempty_iff.mpr ?_
    --   simp
    -- x_increasing := by
    --   intro m n m_lt_n
    --   simp only [basis_n, n_q_basis, Finsupp.coe_basisSingleOne]
    --   have n_supp := Finsupp.support_single_ne_zero (b := (1 : ℚ)) (2 ^ i + n * 2 ^ (i + 1)) (by simp)
    --   have m_supp := Finsupp.support_single_ne_zero (b := (1 : ℚ)) (2 ^ i + m * 2 ^ (i + 1)) (by simp)
    --   simp [n_supp, m_supp]
    --   exact m_lt_n
    -- x_basis := by
    --   intro x hx
    --   simp at hx
    --   simp
    --   obtain ⟨h, hy⟩ := hx
    --   use 2 ^ i + h * 2 ^ (i + 1)
  }

def mk_vals_range_s_i (i: ℕ): Set.range (mk_x_vals i).x_vals ⊆ (λ b => b.2) '' (s_i i) := by
  simp [mk_x_vals, s_i]
  intro x hx
  simp at hx
  simp
  obtain ⟨y, hy⟩ := hx
  use 2 ^ i + y * 2 ^ (i + 1)
  left
  refine ⟨hy, ?_⟩
  simp [Nat.ModEq]



def mk_vals_disjoint (vals1 vals2: XVals) (h_vals: vals1.i ≠ vals2.i): Set.range vals1.x_vals ∩ Set.range vals2.x_vals = ∅ := by
  have i_subset := mk_vals_range_s_i vals1.i
  have j_subset := mk_vals_range_s_i vals2.i
  have disjoint: s_i vals1.i ∩ s_i vals2.i = ∅ := by
    by_cases i_lt_j: vals1.i < vals2.i
    . exact s_i_disjoint vals1.i vals2.i i_lt_j
    . simp at i_lt_j
      have j_neq_i: vals2.i ≠ vals1.i := h_vals.symm
      have j_lt_i: vals2.i < vals1.i := by
        exact Nat.lt_of_le_of_ne i_lt_j j_neq_i
      rw [Set.inter_comm]
      exact s_i_disjoint vals2.i vals1.i j_lt_i
  by_contra!
  obtain ⟨x, x_in_i, x_in_j⟩ := this
  have x_in_s_i: x ∈ (λ b => b.2) '' (s_i vals1.i) := by
    exact i_subset x_in_i
  have x_in_s_j: x ∈ (λ b => b.2) '' (s_i vals2.i) := by
    exact j_subset x_in_j

  simp at x_in_s_i
  simp at x_in_s_j
  obtain ⟨a, ha⟩ := x_in_s_i
  obtain ⟨b, hb⟩ := x_in_s_j
  have x_eq_basis_a := s_i_from_basis vals1.i ⟨a, x⟩ ha
  have x_eq_basis_b := s_i_from_basis vals2.i ⟨b, x⟩ hb
  simp at x_eq_basis_a
  simp at x_eq_basis_b

  have a_eq_b: a = b := by
    rw [x_eq_basis_a] at x_eq_basis_b
    have foo := Finsupp.single_left_inj (a := a) (a' := b) (b := (1:ℚ)) (by simp)
    apply foo.mp x_eq_basis_b

  rw [a_eq_b] at ha
  have inter_elem: ⟨b, x⟩ ∈ (s_i vals1.i) ∩ (s_i vals2.i) := by
    refine ⟨ha, hb⟩
  have inter_nonempty: (s_i vals1.i) ∩ (s_i vals2.i) ≠ ∅ := by
    exact ne_of_mem_of_not_mem' inter_elem fun a ↦ a
  contradiction


inductive ReverseTree {vals: XVals} where
| root: ReverseTree
| left: ReverseTree → ReverseTree
| right: ReverseTree → ReverseTree
  deriving DecidableEq

def newNum {vals: XVals}: @ReverseTree vals → ℕ
  | ReverseTree.root => 2
  | ReverseTree.left prev => 2 * (newNum prev) - 1
  | ReverseTree.right prev => 2 * (newNum prev)

noncomputable def ReverseTree.getData {vals: XVals}: @ReverseTree vals → TreeData
| ReverseTree.root => {a := vals.x_vals 0, b := vals.x_vals 1}
| ReverseTree.left base => {a := -base.getData.b, b := vals.x_vals (newNum base)}
| ReverseTree.right base => {a := vals.x_vals (newNum base), b := base.getData.a - base.getData.b}

def treeDepth {vals: XVals}: @ReverseTree vals → ℕ
| ReverseTree.root => 0
| ReverseTree.left t => 1 + treeDepth t
| ReverseTree.right t => 1 + treeDepth t


--noncomputable def mkRoot: ReverseTree := ReverseTree.root
--noncomputable def mkLeft (base: ReverseTree): ReverseTree := ReverseTree.left {a := -base.getData.b, b := xSeq (newNum base)} base
--noncomputable def mkRight (base: ReverseTree): ReverseTree := ReverseTree.right {a := xSeq (newNum base), b := base.getData.a - base.getData.b} base

#synth Neg (ℕ →₀ ℚ)

noncomputable def my_set: Finset G := ({xSeq 0, xSeq 1} : Finset G)

lemma newnem_gt_one {vals: XVals} (t: @ReverseTree vals): 1 < newNum t := by
  induction t with
  | root =>
    simp [newNum]
  | left prev h_prev =>
    simp [newNum]
    omega
  | right prev h_prev =>
    simp [newNum]
    linarith

lemma newnum_increasing {vals: XVals} (t: @ReverseTree vals): newNum t < newNum (ReverseTree.left t) ∧ newNum t < newNum (ReverseTree.right t) := by
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

lemma newnum_injective {vals: XVals} (t1: @ReverseTree vals) (t2: ReverseTree) (h_eq: newNum t1 = newNum t2): t1 = t2 := by
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

lemma tree_linear_comb {vals: XVals} (t: @ReverseTree vals):
  (∃ g: ℕ →₀ ℚ, ∃ m: ℕ, m ≤ newNum t ∧ g.support.max < m ∧ t.getData.a = ∑ i ∈ Finset.range m, g i • vals.x_vals i) ∧
  (∃ g: ℕ →₀ ℚ, ∃ m: ℕ, m ≤ newNum t ∧ g.support.max < m ∧ t.getData.b = ∑ i ∈ Finset.range m, g i • vals.x_vals i) := by
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
      -- let wrapped_f := Finsupp.onFinset (Finset.range 1) f zero_outside
      simp [newNum]
      use 1
      simp
      simp [ReverseTree.getData]
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
      refine ⟨?_, ?_⟩
      apply le_trans m_le (le_of_lt prev_lt_mul)

      rw [neg_eq_iff_eq_neg]
      rw [← neg_one_zsmul]
      rw [← Finset.sum_zsmul]
      -- simp only [Finsupp.smul_single, smul_ite]
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

lemma eval_larger_a_eq_zero {vals: XVals} (t: @ReverseTree vals) (n: ℕ) (hn: newNum t ≤ n) : t.getData.a (vals.x_to_index n) = 0 := by
  obtain ⟨⟨g, m, m_le, g_card, h_g⟩, _⟩ := tree_linear_comb t

  have val_newnum_le: vals.x_to_index (newNum t) ≤ vals.x_to_index n := by
    simp [StrictMono.le_iff_le vals.x_to_index_increasing]
    exact hn

  have n_not_supp: ∀ i, i < m → vals.x_to_index n ∉ (vals.x_vals i).support := by
    intro i hi
    rw [vals.x_to_index_eq]
    simp [basis_n]
    have vals_x_lt: vals.x_to_index i < vals.x_to_index m := by
      exact vals.x_to_index_increasing hi
    have vals_m_le: vals.x_to_index m ≤ vals.x_to_index (newNum t) := by
      simp [StrictMono.le_iff_le vals.x_to_index_increasing]
      exact m_le
    have n_neq_i: vals.x_to_index n ≠ vals.x_to_index i := by
      linarith
    exact Finsupp.single_eq_of_ne (id (Ne.symm n_neq_i))

  have sum_eval_eq_zero: ∑ i ∈ Finset.range m, (g i • vals.x_vals i) (vals.x_to_index n) = ∑ i ∈ Finset.range m, 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    simp at hx
    specialize n_not_supp x hx
    have supp_subset := Finsupp.support_smul (g := vals.x_vals x) (b := g x)
    have n_not_full_supp: vals.x_to_index n ∉ (g x • vals.x_vals x).support := by
      exact fun a ↦ n_not_supp (supp_subset a)
    apply Finsupp.not_mem_support_iff.mp at n_not_full_supp
    exact n_not_full_supp
  have fun_congr := DFunLike.congr h_g (x := vals.x_to_index n) rfl
  rw [Finsupp.finset_sum_apply] at fun_congr
  rw [sum_eval_eq_zero] at fun_congr
  simp at fun_congr
  exact fun_congr

-- TODO - this is almost identical to 'eval_larger_a_eq_zero'
lemma eval_larger_b_eq_zero {vals: XVals} (t: @ReverseTree vals) (n: ℕ) (hn: newNum t ≤ n) : t.getData.b (vals.x_to_index n) = 0 := by
  obtain ⟨_, ⟨g, m, m_le, g_card, h_g⟩⟩ := tree_linear_comb t

  have val_newnum_le: vals.x_to_index (newNum t) ≤ vals.x_to_index n := by
    simp [StrictMono.le_iff_le vals.x_to_index_increasing]
    exact hn

  have n_not_supp: ∀ i, i < m → vals.x_to_index n ∉ (vals.x_vals i).support := by
    intro i hi
    rw [vals.x_to_index_eq]
    simp [basis_n]
    have vals_x_lt: vals.x_to_index i < vals.x_to_index m := by
      exact vals.x_to_index_increasing hi
    have vals_m_le: vals.x_to_index m ≤ vals.x_to_index (newNum t) := by
      simp [StrictMono.le_iff_le vals.x_to_index_increasing]
      exact m_le
    have n_neq_i: vals.x_to_index n ≠ vals.x_to_index i := by
      linarith
    exact Finsupp.single_eq_of_ne (id (Ne.symm n_neq_i))

  have sum_eval_eq_zero: ∑ i ∈ Finset.range m, (g i • vals.x_vals i) (vals.x_to_index n) = ∑ i ∈ Finset.range m, 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    simp at hx
    specialize n_not_supp x hx
    have supp_subset := Finsupp.support_smul (g := vals.x_vals x) (b := g x)
    have n_not_full_supp: vals.x_to_index n ∉ (g x • vals.x_vals x).support := by
      exact fun a ↦ n_not_supp (supp_subset a)
    apply Finsupp.not_mem_support_iff.mp at n_not_full_supp
    exact n_not_full_supp
  have fun_congr := DFunLike.congr h_g (x := vals.x_to_index n) rfl
  rw [Finsupp.finset_sum_apply] at fun_congr
  rw [sum_eval_eq_zero] at fun_congr
  simp at fun_congr
  exact fun_congr

lemma tree_linear_independent {vals: XVals} (t: @ReverseTree vals): LinearIndependent ℚ ![t.getData.a, t.getData.b] := by
  induction t with
  | root =>
    simp [LinearIndependent.pair_iff]
    intro p q eq_zero
    simp [ReverseTree.getData] at eq_zero
    have basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis
    rw [linearIndependent_iff'] at basis_indep
    have vals_zero_basis: vals.x_vals 0 ∈ Set.range basis_n := Set.mem_of_mem_of_subset (by simp) vals.x_basis
    have vals_one_basis: vals.x_vals 1 ∈ Set.range basis_n := Set.mem_of_mem_of_subset (by simp) vals.x_basis
    obtain ⟨zero_val, h_zero_val⟩ := vals_zero_basis
    obtain ⟨one_val, h_one_val⟩ := vals_one_basis

    specialize basis_indep {zero_val, one_val} fun g => if g = zero_val then p else q
    have vals_neq: vals.x_vals 0 ≠ vals.x_vals 1 := by
      apply (Function.Injective.ne_iff vals.x_inj).mpr
      simp

    rw [← h_zero_val, ← h_one_val] at vals_neq
    have zero_val_neq: zero_val ≠ one_val := by
      apply (Function.Injective.ne_iff basis_n_injective).mp
      exact vals_neq

    rw [Finset.sum_pair zero_val_neq] at basis_indep
    simp [zero_val_neq, zero_val_neq.symm] at basis_indep
    rw [← h_zero_val, ← h_one_val] at eq_zero
    simp [basis_n] at eq_zero
    exact basis_indep eq_zero
  | left prev h_prev =>
    simp [ReverseTree.getData]
    simp [ReverseTree.getData] at h_prev
    obtain ⟨_, ⟨b_coords, ⟨max_num, max_num_lt, b_coord_card, b_eq⟩⟩⟩ := tree_linear_comb prev


    have nonzero_b_coord: ∃n, n < max_num ∧ b_coords n ≠ 0 := by
      by_contra!
      have sum_eq_zero: ∑ i ∈ Finset.range max_num, b_coords i • vals.x_vals i = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        specialize this x (Finset.mem_range.mp hx)
        simp [this]
      rw [sum_eq_zero] at b_eq
      rw [b_eq] at h_prev
      have foo := LinearIndependent.ne_zero 1 h_prev
      simp at foo

    rw [b_eq]
    simp only [LinearIndependent.pair_iff]
    intro s t hs_t

    have basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis
    have basis_x_val_indep := LinearIndependent.comp basis_indep vals.x_to_index vals.x_to_index_inj
    rw [linearIndependent_iff'] at basis_indep
    rw [linearIndependent_iff'] at basis_x_val_indep
    rw [add_comm] at hs_t

    let f := λ x => t • (vals.x_vals x)

    have x_val_basis: vals.x_vals (newNum prev) ∈ Set.range basis_n := Set.mem_of_mem_of_subset (by simp) vals.x_basis
    obtain ⟨newnum_val, h_newnum_val⟩ := x_val_basis

    have ite_eq: (if (newNum prev) ∈ Finset.range (newNum prev + 1) then f (newNum prev) else 0) = t • (vals.x_vals (newNum prev)) := by
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
    simp only [vals.x_to_index_eq] at hs_t
    simp only [basis_n] at hs_t

    apply (basis_x_val_indep _) at hs_t
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

    let f := λ x => s • (vals.x_vals x)

    have x_val_basis: vals.x_vals (newNum prev) ∈ Set.range basis_n := Set.mem_of_mem_of_subset (by simp) vals.x_basis
    obtain ⟨newnum_val, h_newnum_val⟩ := x_val_basis

    have ite_eq: (if (newNum prev) ∈ Finset.range (newNum prev + 1) then f (newNum prev) else 0) = s • (vals.x_vals (newNum prev)) := by
      simp [f]

    have basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis
    have basis_x_val_indep := LinearIndependent.comp basis_indep vals.x_to_index vals.x_to_index_inj
    rw [linearIndependent_iff'] at basis_indep
    rw [linearIndependent_iff'] at basis_x_val_indep

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
    simp only [vals.x_to_index_eq] at hs_t
    simp only [basis_n] at hs_t

    apply (basis_x_val_indep _) at hs_t
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
        have a_eq_sum_b: prev.getData.a = ∑ i ∈ Finset.range b_max_num, b_coords i • vals.x_vals i := by
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
            have eq_sum_smaller: ∑ i ∈ Finset.range a_max_num, b_coords i • vals.x_vals i = ∑ i ∈ Finset.range b_max_num, b_coords i • vals.x_vals i := by
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
              left
              apply this x_le_max
            rw [← eq_sum_smaller] at b_eq
            have b_eq_a_sum: prev.getData.b = ∑ i ∈ Finset.range a_max_num, a_coords i • vals.x_vals i := by
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
            have eq_sum_smaller: ∑ i ∈ Finset.range b_max_num, a_coords i • vals.x_vals i = ∑ i ∈ Finset.range a_max_num, a_coords i • vals.x_vals i := by
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
              left
              apply this x_le_max
            rw [← eq_sum_smaller] at a_eq
            have a_eq_b_sum: prev.getData.a = ∑ i ∈ Finset.range b_max_num, b_coords i • vals.x_vals i := by
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


lemma tree_supp_disjoint {vals: XVals} (t: @ReverseTree vals): t.getData.b.support ∩ t.getData.a.support = ∅ := by
  match t with
    | .root =>
      simp [ReverseTree.getData]
      simp [vals.x_to_index_eq]
      have other_one_ne_zero: (vals.x_to_index 0) ≠ (vals.x_to_index 1) := by
        apply Function.Injective.ne vals.x_to_index_inj
        simp

      have one_ne_zero: (1: ℚ) ≠ 0:= by
        simp

      rw [Finsupp.support_single_ne_zero (vals.x_to_index 0) one_ne_zero]
      rw [Finsupp.support_single_ne_zero (vals.x_to_index 1) one_ne_zero]
      simp [other_one_ne_zero]
    | .left parent =>
        simp [ReverseTree.getData, xSeq]
        obtain ⟨_, g, m, m_le_newnum, m_supp_lt, b_linear_comb⟩ := tree_linear_comb parent
        rw [b_linear_comb]
        by_contra!
        obtain ⟨x, hx⟩ := Finset.Nonempty.exists_mem (Finset.nonempty_of_ne_empty this)
        have x_in_cur: x ∈ (vals.x_vals (newNum parent)).support := by
          exact Finset.mem_of_mem_inter_left hx

        have x_in_parent: x ∈ (∑ i ∈ Finset.range m, g i • vals.x_vals i).support := by
          exact Finset.mem_of_mem_inter_right hx

        have one_ne_zero: (1 : ℚ) ≠ 0 := by
          simp
        have bar := Finsupp.support_single_ne_zero (vals.x_to_index (newNum parent)) one_ne_zero
        rw [vals.x_to_index_eq] at x_in_cur
        simp [bar] at x_in_cur

        have x_lt_max := Finset.le_max x_in_parent
        have support_subset := Finsupp.support_finset_sum (s := Finset.range m) (f := fun i => g i • vals.x_vals i)
        --simp [basis_n] at support_subset

        have supp_single: ∀ x ∈ Finset.range m, ((g x) • vals.x_vals x).support ⊆ Finset.range (vals.x_to_index m) := by
          intro x hx
          have old_foo := Finsupp.support_single_subset (a := x) (b := ( 1: ℚ))
          have single_supp: (vals.x_vals x).support ⊆ {vals.x_to_index x} := by
            rw [vals.x_to_index_eq]
            simp only [basis_n]
            apply Finsupp.support_single_subset
          have x_val_subset: {vals.x_to_index x} ⊆ Finset.range (vals.x_to_index m) := by
            simp
            simp at hx
            apply vals.x_to_index_increasing
            exact hx
          have mul_support := Finsupp.support_smul (b := g x) (g := vals.x_vals x)
          have first_trans := Finset.Subset.trans mul_support single_supp
          have second_trans := Finset.Subset.trans first_trans x_val_subset
          exact second_trans


        have mul_supp_subset: ∀ i ∈ Finset.range m, (g i • basis_n i).support ⊆ (basis_n i).support := by
          intro i hi
          exact Finsupp.support_smul

        simp only [basis_n, Finsupp.coe_basisSingleOne, Finsupp.smul_single,
          smul_eq_mul, mul_one] at mul_supp_subset





        have bar := (Finset.biUnion_subset (s := Finset.range (m)) (t := fun x => (g x • vals.x_vals x).support)).mpr supp_single
        have x_in_biunion: x ∈ ((Finset.range m).biUnion fun x ↦ (g x • vals.x_vals x).support) := by
          apply Finset.mem_of_subset support_subset x_in_parent

        simp only [basis_n, Finsupp.coe_basisSingleOne] at x_in_biunion
        -- TODO - this seems wrong. x is in range 'm' - we need to map this to the potentnial larger 'x_to_index'
        have x_in_range: x ∈ Finset.range (vals.x_to_index m) := by
          apply Finset.mem_of_subset bar x_in_biunion

        have index_m_lt_newnum: vals.x_to_index m ≤ vals.x_to_index (newNum parent) := by
          simp [StrictMono.le_iff_le vals.x_to_index_increasing]
          linarith

        have x_lt_m: x < vals.x_to_index (m) := by
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
      have x_in_cur: x ∈ (vals.x_vals (newNum parent)).support := by
        exact Finset.mem_of_mem_inter_right hx

      have x_in_sum := Finset.mem_of_mem_inter_left hx
      have x_lt_max := Finset.le_max x_in_sum

      have one_ne_zero: (1 : ℚ) ≠ 0 := by
        simp
      have newnum_support := Finsupp.support_single_ne_zero (vals.x_to_index (newNum parent)) one_ne_zero
      rw [vals.x_to_index_eq] at x_in_cur
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

      have a_sum_extend: (∑ i ∈ Finset.range a_m, if i ∈ Finset.range a_m then a_g i • vals.x_vals i else 0) = (∑ i ∈ Finset.range (max a_m b_m), if i ∈ Finset.range a_m then a_g i • vals.x_vals i else 0) := by
        apply Finset.sum_subset a_subset_max ?_
        intro x hx x_not_in
        simp [x_not_in]

      have b_sum_extend: (∑ i ∈ Finset.range b_m, if i ∈ Finset.range b_m then b_g i • vals.x_vals i else 0) = (∑ i ∈ Finset.range (max a_m b_m), if i ∈ Finset.range b_m then b_g i • vals.x_vals i else 0) := by
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

      have supp_single: ∀ g: ℕ →₀ ℚ, ∀ x ∈ Finset.range (max a_m b_m), ((g x) • vals.x_vals x).support ⊆ Finset.range (max (vals.x_to_index a_m) (vals.x_to_index b_m)) := by
        intro g x hx
        --have foo := Finsupp.support_single_subset (a := vals.x_vals x) (b := ( 1: ℚ))
        have single_supp: (vals.x_vals x).support ⊆ {vals.x_to_index x} := by
          rw [vals.x_to_index_eq]
          simp only [basis_n]
          apply Finsupp.support_single_subset
        have x_single_subset: {vals.x_to_index x} ⊆ Finset.range (max (vals.x_to_index a_m) (vals.x_to_index b_m)) := by
          simp
          simp at hx
          -- TODO - is there a way of doing 'apply' on an 'or'
          match hx with
          | .inl x_left =>
            left
            apply vals.x_to_index_increasing
            exact x_left
          | .inr x_right =>
            right
            apply vals.x_to_index_increasing
            exact x_right
        have mul_support := Finsupp.support_smul (b := g x) (g := vals.x_vals x)
        have first_trans := Finset.Subset.trans mul_support single_supp
        have second_trans := Finset.Subset.trans first_trans x_single_subset
        exact second_trans


      have mul_supp_subset: ∀ g: ℕ →₀ ℚ, ∀ i ∈ Finset.range (max a_m b_m), (g i • vals.x_vals i).support ⊆ (vals.x_vals i).support := by
        intro g i hi
        exact Finsupp.support_smul

      have combined_supp_subset: ∀ x ∈ Finset.range (max a_m b_m), ((if x ∈ Finset.range a_m then a_g x • vals.x_vals x else 0) - if x ∈ Finset.range b_m then b_g x • vals.x_vals x else 0).support ⊆ Finset.range (max (vals.x_to_index a_m) (vals.x_to_index b_m)) := by
        intro x hx
        by_cases x_lt_a: x < a_m
        . by_cases x_lt_b: x < b_m
          . simp [x_lt_a, x_lt_b]
            have a_supp := supp_single a_g x hx
            have b_supp := supp_single b_g x hx
            have support_sub_subset := Finsupp.support_sub (f := a_g x • vals.x_vals x) (g := b_g x • vals.x_vals x)
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
      have support_subset := Finsupp.support_finset_sum (s := Finset.range (max a_m b_m)) (f := fun x => ((if x ∈ Finset.range a_m then a_g x • vals.x_vals x else 0) - if x ∈ Finset.range b_m then b_g x • vals.x_vals x else 0))

      have x_in_biunion := Finset.mem_of_subset support_subset x_in_sum

      simp only [basis_n, Finsupp.coe_basisSingleOne] at x_in_biunion
      have other := Finset.mem_of_subset biunion_subset x_in_biunion
      have x_in_range: x ∈ Finset.range (max (vals.x_to_index a_m) (vals.x_to_index b_m)) := by
        apply Finset.mem_of_subset biunion_subset x_in_biunion

      have max_le_newnum: (max (vals.x_to_index a_m) (vals.x_to_index b_m)) ≤ vals.x_to_index (newNum parent) := by
        simp
        refine ⟨?_, ?_⟩
        . simp [StrictMono.le_iff_le vals.x_to_index_increasing]
          linarith
        . simp [StrictMono.le_iff_le vals.x_to_index_increasing]
          linarith

      have x_lt_m: x < (max (vals.x_to_index a_m) (vals.x_to_index b_m)) := by
        simp at x_in_range
        simp
        exact x_in_range

      linarith
#print axioms tree_supp_disjoint

lemma tree_vals_nonzero {vals: XVals} (t: @ReverseTree vals) : t.getData.a ≠ 0 ∧ t.getData.b ≠ 0 := by
  have a_neq_zero: t.getData.a ≠ 0 := by
    have bar := LinearIndependent.ne_zero 0 (tree_linear_independent t)
    simp at bar
    assumption
  have b_neq_zero: t.getData.b ≠ 0 := by
    have bar := LinearIndependent.ne_zero 1 (tree_linear_independent t)
    simp at bar
    assumption
  exact ⟨a_neq_zero, b_neq_zero⟩

lemma basis_neq_elem_diff {vals: XVals} (t:@ ReverseTree vals) (a: ℕ) (b c r: ℚ) (hb: b ≠ 0) (hc: c ≠ 0) (hr: r ≠ 0): Finsupp.single a r ≠ b • t.getData.b + c • t.getData.a := by
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

lemma finsupp_new_zero_newnum {vals: XVals} (t: @ReverseTree vals) (a b: ℚ) (hb: b ≠ 0): (fun₀ | vals.x_to_index 0 => (a: ℚ)) ≠ (fun₀ | (vals.x_to_index (newNum t)) => (b: ℚ)) := by
  by_contra!
  have eval_at := DFunLike.congr (x := (vals.x_to_index (newNum t))) (y := vals.x_to_index (newNum t)) this rfl
  simp at eval_at
  have t2_gt_one := newnem_gt_one t
  have newnum_neq_zero: 0 ≠ newNum t := by
    omega
  have vals_neq: vals.x_to_index 0 ≠ vals.x_to_index (newNum t) := by
    apply Function.Injective.ne vals.x_to_index_inj
    exact newnum_neq_zero
  simp [vals_neq] at eval_at
  rw [eq_comm] at eval_at
  contradiction

lemma finsupp_new_one_newnum {vals: XVals} (t: @ReverseTree vals) (a b: ℚ) (hb: b ≠ 0): (fun₀ | vals.x_to_index 1 => (a: ℚ)) ≠ (fun₀ | (vals.x_to_index (newNum t)) => (b: ℚ)) := by
  by_contra!
  have eval_at := DFunLike.congr (x := (vals.x_to_index (newNum t))) (y := vals.x_to_index (newNum t)) this rfl
  simp at eval_at
  have t2_gt_one := newnem_gt_one t
  have newnum_neq_one: 1 ≠ newNum t := by
    omega
  have vals_neq: vals.x_to_index 1 ≠ vals.x_to_index (newNum t) := by
    apply Function.Injective.ne vals.x_to_index_inj
    exact newnum_neq_one
  simp [vals_neq] at eval_at
  rw [eq_comm] at eval_at
  contradiction

lemma xseq_zero_neq_b {vals: XVals} (t: @ReverseTree vals) (s: ℚ) (hs: s ≠ 0): basis_n (vals.x_to_index 0) ≠ s • t.getData.b := by
  by_contra!
  match t with
  | .root =>
      -- TODO - there must be a simpler way of doing 'congr'
      simp [ReverseTree.getData, xSeq] at this
      have eval_at := DFunLike.congr (x := (vals.x_to_index 0)) (y := (vals.x_to_index 0)) this rfl
      rw [vals.x_to_index_eq] at eval_at
      simp [basis_n] at eval_at
      have vals_neq: vals.x_to_index 1 ≠ vals.x_to_index 0 := by
        apply Function.Injective.ne vals.x_to_index_inj
        simp
      simp [vals_neq] at eval_at
  | .left t2_parent_parent =>
      simp [ReverseTree.getData, xSeq] at this
      rw [vals.x_to_index_eq] at this
      simp [basis_n] at this
      have fun_neq := finsupp_new_zero_newnum t2_parent_parent 1 s hs
      contradiction
    | .right t2_parent_parent =>
      simp [ReverseTree.getData, xSeq] at this
      have neg_s_neq_zero: (-s) ≠ 0 := by
        simp
        exact hs
      have vals_neq := basis_neq_elem_diff t2_parent_parent (vals.x_to_index 0) (-s) s 1 neg_s_neq_zero hs (by simp)
      simp only [one_smul, neg_one_smul, add_comm] at vals_neq
      rw [neg_smul, ← sub_eq_add_neg] at vals_neq
      rw [smul_sub] at this
      contradiction


lemma common_ancestor_stuff {vals: XVals} (ancestor t1 t2: @ReverseTree vals) (left_right: t1 = ancestor.left ∧ t2 = ancestor.right)
  (h_a_eq: t1.getData.b - t1.getData.a = t2.getData.b - t2.getData.a): False := by

  simp [left_right.1, left_right.2, ReverseTree.getData] at h_a_eq
  have x_seq_add: vals.x_vals (newNum ancestor) + ancestor.getData.b  + vals.x_vals (newNum ancestor) = ancestor.getData.a - ancestor.getData.b := by
    exact add_eq_of_eq_sub h_a_eq

  have x_swap: vals.x_vals (newNum ancestor) + ancestor.getData.b  + vals.x_vals (newNum ancestor) = vals.x_vals (newNum ancestor) + vals.x_vals (newNum ancestor) + ancestor.getData.b := by
    exact
      Eq.symm
        (add_rotate (vals.x_vals (newNum ancestor)) (vals.x_vals (newNum ancestor))
          ancestor.getData.b)

  rw [x_swap] at x_seq_add
  have sub_b: vals.x_vals (newNum ancestor) + vals.x_vals (newNum ancestor) = ancestor.getData.a - ancestor.getData.b - ancestor.getData.b := by
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
  apply n_q_basis.ext_elem_iff.mp at sub_b
  specialize sub_b (vals.x_to_index (newNum ancestor))
  simp only [n_q_basis, Finsupp.basisSingleOne_repr, Finsupp.coe_basisSingleOne, Finsupp.smul_single, nsmul_eq_mul, Nat.cast_ofNat, mul_one, LinearEquiv.refl_apply, Finsupp.single_eq_same, Finset.mem_range, smul_eq_mul, smul_ite, Finsupp.single_mul, smul_zero, Finsupp.coe_sub, Finsupp.coe_finset_sum, Pi.sub_apply, Finset.sum_apply] at sub_b
  -- TODO - avoid copy-pasting the entire sum
  have sum_eq_zero: ∑ x ∈ Finset.range (newNum ancestor), (((if x < m_a then (g_a x • vals.x_vals x) else 0) (vals.x_to_index (newNum ancestor)) - (if x < m_b then 2 • g_b x • vals.x_vals x else 0) ((vals.x_to_index (newNum ancestor))))) = ∑ x ∈ Finset.range (newNum ancestor), 0 := by
    apply Finset.sum_congr rfl
    intro x hx
    simp at hx
    have x_neq_newnum: x ≠ newNum ancestor := by
      linarith
    have index_x_neq_newnum: vals.x_to_index x ≠ vals.x_to_index (newNum ancestor) := by
      apply Function.Injective.ne vals.x_to_index_inj
      exact x_neq_newnum
    -- TODO - can we simplify this?
    by_cases x_lt_a: x < m_a
    . by_cases x_lt_b: x < m_b
      .
        simp [x_lt_a, x_lt_b, vals.x_to_index_eq, index_x_neq_newnum]
      . simp [x_lt_a, x_lt_b, vals.x_to_index_eq, index_x_neq_newnum]
    . by_cases x_lt_b: x < m_b
      . simp [x_lt_a, x_lt_b, vals.x_to_index_eq, index_x_neq_newnum]
      . simp [x_lt_a, x_lt_b, vals.x_to_index_eq, index_x_neq_newnum]

  rw [sum_eq_zero] at sub_b
  rw [vals.x_to_index_eq] at sub_b
  simp at sub_b

  -- TODO - move these up earlier when we do `Finset.sum_subset a_subset_newnum ?_`
  . intro x hx x_not_in
    simp [x_not_in]
  . intro x hx x_not_in
    simp [x_not_in]


--   One element in each pair must be fresh - assume wlog that 'c' and 'x' are fresh.
--     Then, in order for 'c - d = x - y', we must have 'x' occuring in 'd' and 'c' occuring in 'y'.
--     This means depth(parent_one) >= depth(parent_two) and depth(parent_two) >= depth(parent_one), since each must have at least the depth where the other fresh element is first introduced.
--     Thus, depth(parent_one) = depth(parent_two).
--     The only way for this to work is if the parents look like (x_i, p) and (q, x_i) - that this, the same fresh node.
--      Otherwise, one of the nodes will contain a fresh element that's not in the other node.
--     This implies that the parents are the left/right children of the same node.
--     Let this common ancestor be (f, g).

-- New argument - pick the largest fresh term - it cannot occur in the other side 'normally', since the fresh terms have higher basis indices than the other term
-- Since the sides are equal, both fresh terms must equal the largest term
-- This can only happen when the two are children of the same parent.
lemma cross_eq_same_parent {vals: XVals} {t1 t2: @ReverseTree vals} (h_a_neq: t1.getData.a ≠ t2.getData.a) (h_eq: t1.getData.a - t1.getData.b = t2.getData.a - t2.getData.b) : ∃ ancestor: ReverseTree, (t1 = ancestor.left ∧ t2 = ancestor.right) ∨ (t1 = ancestor.right ∧ t2 = ancestor.left) := by
    have parents_b_neq: t1.getData.b ≠ t2.getData.b := by
      by_contra!
      rw [this] at h_eq
      simp at h_eq
      contradiction

    have newnum_neq: newNum t1 ≠ newNum t2 := by
      by_contra!
      have t1_eq_t2: t1 = t2 := by
        exact newnum_injective t1 t2 this
      rw [t1_eq_t2] at h_a_neq
      contradiction

    match h_t1: t1 with
    | .root =>
      match h_t2: t2 with
      | .root =>
        have t1_eq_t2: t1 = t2 := by
          rwa [← h_t2] at h_t1
        rw [← h_t1, t1_eq_t2] at h_a_neq
        contradiction
      | .left t2_parent =>
          -- TODO - deduplicate this with the '.left t1_parent' 't2 root' case belo
          simp [ReverseTree.getData] at h_eq
          have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t2_parent)) rfl
          have t2_a_zero := eval_larger_a_eq_zero t2_parent (newNum t2_parent) (by simp)
          simp at fun_congr
          have t2_b_zero := eval_larger_b_eq_zero t2_parent (newNum t2_parent) (by simp)
          have t2_gt_one: 1 < newNum t2_parent := by
            exact newnem_gt_one t2_parent
          have t2_neq_zero: 0 ≠ newNum t2_parent := by linarith
          have index_zero_neq: vals.x_to_index 0 ≠ vals.x_to_index (newNum t2_parent) := by
            apply Function.Injective.ne vals.x_to_index_inj t2_neq_zero
          have t2_neq_one: 1 ≠ newNum t2_parent := by linarith
          have index_one_neq: vals.x_to_index 1 ≠ vals.x_to_index (newNum t2_parent) := by
            apply Function.Injective.ne vals.x_to_index_inj t2_neq_one
          repeat rw [vals.x_to_index_eq] at fun_congr
          --rw [t2_a_zero] at fun_congr
          --simp [t2_a_zero, xSeq] at fun_congr
          --rw [Finsupp.single_apply] at fun_congr
          --rw [Finsupp.single_apply] at fun_congr
          -- Implicit contradiction
          simp [index_zero_neq, index_one_neq, t2_b_zero] at fun_congr
      | .right t2_parent =>
          -- TODO - this is virtually identical to the '.left t2_parent' block above
          simp [ReverseTree.getData] at h_eq
          have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t2_parent)) rfl
          have t2_a_zero := eval_larger_a_eq_zero t2_parent (newNum t2_parent) (by simp)
          simp at fun_congr
          have t2_b_zero := eval_larger_b_eq_zero t2_parent (newNum t2_parent) (by simp)
          have t2_gt_one: 1 < newNum t2_parent := by
            exact newnem_gt_one t2_parent
          have t2_neq_zero: 0 ≠ newNum t2_parent := by linarith
          have index_zero_neq: vals.x_to_index 0 ≠ vals.x_to_index (newNum t2_parent) := by
            apply Function.Injective.ne vals.x_to_index_inj t2_neq_zero
          have t2_neq_one: 1 ≠ newNum t2_parent := by linarith
          have index_one_neq: vals.x_to_index 1 ≠ vals.x_to_index (newNum t2_parent) := by
            apply Function.Injective.ne vals.x_to_index_inj t2_neq_one
          repeat rw [vals.x_to_index_eq] at fun_congr
          --rw [t2_a_zero] at fun_congr
          --simp [t2_a_zero, xSeq] at fun_congr
          --rw [Finsupp.single_apply] at fun_congr
          --rw [Finsupp.single_apply] at fun_congr
          -- Implicit contradiction
          simp [index_zero_neq, index_one_neq, t2_b_zero, t2_a_zero] at fun_congr
    | .left t1_parent =>
        match h_t2: t2 with
          | .root =>
            simp [ReverseTree.getData] at h_eq
            have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t1_parent)) rfl
            have t1_a_zero := eval_larger_a_eq_zero t1_parent (newNum t1_parent) (by simp)
            have t1_b_zero := eval_larger_b_eq_zero t1_parent (newNum t1_parent) (by simp)
            have t1_gt_one: 1 < newNum t1_parent := by
              exact newnem_gt_one t1_parent
            have t1_neq_zero: 0 ≠ newNum t1_parent := by linarith
            have index_zero_neq: vals.x_to_index 0 ≠ vals.x_to_index (newNum t1_parent) := by
              apply Function.Injective.ne vals.x_to_index_inj t1_neq_zero
            have t1_neq_one: 1 ≠ newNum t1_parent := by linarith
            have index_one_neq: vals.x_to_index 1 ≠ vals.x_to_index (newNum t1_parent) := by
              apply Function.Injective.ne vals.x_to_index_inj t1_neq_one
            repeat rw [vals.x_to_index_eq] at fun_congr
            simp [t1_a_zero] at fun_congr
            rw [Finsupp.single_apply] at fun_congr
            rw [Finsupp.single_apply] at fun_congr
            -- Implicit contradiction
            simp [index_zero_neq, index_one_neq, t1_b_zero] at fun_congr
          | .left t2_parent =>
              by_cases is_t1_lt: newNum t1_parent < newNum t2_parent
              .
                have is_t1_le: newNum t1_parent ≤ newNum t2_parent := by
                  linarith
                simp [ReverseTree.getData] at h_eq
                have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t2_parent)) rfl
                have t1_b_zero := eval_larger_b_eq_zero t1_parent (newNum t2_parent) is_t1_le
                have t2_a_zero := eval_larger_a_eq_zero t2_parent (newNum t2_parent) (by simp)
                have t2_b_zero := eval_larger_b_eq_zero t2_parent (newNum t2_parent) (by simp)
                simp [t1_b_zero, t2_a_zero, t2_b_zero, xSeq] at fun_congr
                repeat rw [vals.x_to_index_eq] at fun_congr
                simp [basis_n] at fun_congr
                rw [Finsupp.single_apply] at fun_congr
                simp at fun_congr
                apply vals.x_to_index_inj at fun_congr
                linarith
              .
                have is_t2_le: newNum t2_parent ≤ newNum t1_parent := by
                  linarith
                simp [ReverseTree.getData] at h_eq
                have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t1_parent)) rfl
                simp at fun_congr
                have t2_a_zero := eval_larger_a_eq_zero t2_parent (newNum t1_parent) is_t2_le
                have t2_b_zero := eval_larger_b_eq_zero t2_parent (newNum t1_parent) is_t2_le
                have t1_b_zero := eval_larger_b_eq_zero t1_parent (newNum t1_parent) (by simp)
                simp [t1_b_zero, t2_a_zero, t2_b_zero, xSeq] at fun_congr
                repeat rw [vals.x_to_index_eq] at fun_congr
                simp [basis_n] at fun_congr
                rw [Finsupp.single_apply, eq_comm] at fun_congr
                simp at fun_congr
                apply vals.x_to_index_inj at fun_congr
                have parents_eq: t2_parent = t1_parent := by
                  exact newnum_injective t2_parent t1_parent fun_congr
                have t1_eq_t2: t1 = t2 := by
                  rw [parents_eq.symm] at h_t1
                  rwa [← h_t2] at h_t1
                rw [← h_t1, ← h_t2, t1_eq_t2] at h_a_neq
                contradiction
          | .right t2_parent =>
              have newnums_eq: newNum t1_parent = newNum t2_parent := by
                by_contra!
                by_cases is_t1_lt: newNum t1_parent < newNum t2_parent
                .
                  have is_t1_le: newNum t1_parent ≤ newNum t2_parent := by
                    linarith
                  simp [ReverseTree.getData] at h_eq
                  have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t2_parent)) rfl
                  simp at fun_congr
                  have t1_b_zero := eval_larger_b_eq_zero t1_parent (newNum t2_parent) is_t1_le
                  have t2_a_zero := eval_larger_a_eq_zero t2_parent (newNum t2_parent) (by simp)
                  have t2_b_zero := eval_larger_b_eq_zero t2_parent (newNum t2_parent) (by simp)
                  simp [t1_b_zero, t2_a_zero, t2_b_zero, xSeq] at fun_congr
                  repeat rw [vals.x_to_index_eq] at fun_congr
                  simp [basis_n] at fun_congr
                  have vals_newnum_neq: vals.x_to_index (newNum t1_parent) ≠ vals.x_to_index (newNum t2_parent) := by
                    apply Function.Injective.ne vals.x_to_index_inj this
                  simp [Finsupp.single_eq_of_ne vals_newnum_neq] at fun_congr
                . have is_t2_le: newNum t2_parent ≤ newNum t1_parent := by
                    linarith
                  simp [ReverseTree.getData] at h_eq
                  have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t1_parent)) rfl
                  simp at fun_congr
                  have t2_a_zero := eval_larger_a_eq_zero t2_parent (newNum t1_parent) is_t2_le
                  have t2_b_zero := eval_larger_b_eq_zero t2_parent (newNum t1_parent) is_t2_le
                  have t1_b_zero := eval_larger_b_eq_zero t1_parent (newNum t1_parent) (by simp)
                  simp [t1_b_zero, t2_a_zero, t2_b_zero, xSeq] at fun_congr
                  repeat rw [vals.x_to_index_eq] at fun_congr
                  simp [basis_n] at fun_congr
                  have vals_newnum_neq: vals.x_to_index (newNum t1_parent) ≠ vals.x_to_index (newNum t2_parent) := by
                    apply Function.Injective.ne vals.x_to_index_inj this
                  simp [Finsupp.single_eq_of_ne vals_newnum_neq.symm] at fun_congr
              have parents_eq: t1_parent = t2_parent := by
                exact newnum_injective t1_parent t2_parent newnums_eq
              use t1_parent
              left
              rw [parents_eq]
              refine ⟨rfl, rfl⟩
    -- Begin horrible copy-paste - we should be able to deduplicate all of the sub-cases here
    | .right t1_parent =>
      match h_t2: t2 with
        | .root =>
          -- TODO - this is identical to the '.left t2_parent' block way above
          simp [ReverseTree.getData] at h_eq
          have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t1_parent)) rfl
          have t2_a_zero := eval_larger_a_eq_zero t1_parent (newNum t1_parent) (by simp)
          simp at fun_congr
          have t2_b_zero := eval_larger_b_eq_zero t1_parent (newNum t1_parent) (by simp)
          have t2_gt_one: 1 < newNum t1_parent := by
            exact newnem_gt_one t1_parent
          have t2_neq_zero: 0 ≠ newNum t1_parent := by linarith
          have index_zero_neq: vals.x_to_index 0 ≠ vals.x_to_index (newNum t1_parent) := by
            apply Function.Injective.ne vals.x_to_index_inj t2_neq_zero
          have t2_neq_one: 1 ≠ newNum t1_parent := by linarith
          have index_one_neq: vals.x_to_index 1 ≠ vals.x_to_index (newNum t1_parent) := by
            apply Function.Injective.ne vals.x_to_index_inj t2_neq_one
          repeat rw [vals.x_to_index_eq] at fun_congr
          --rw [t2_a_zero] at fun_congr
          --simp [t2_a_zero, xSeq] at fun_congr
          --rw [Finsupp.single_apply] at fun_congr
          --rw [Finsupp.single_apply] at fun_congr
          -- Implicit contradiction
          simp [index_zero_neq, index_one_neq, t2_b_zero, t2_a_zero] at fun_congr
        -- TODO - deduplicate this with the 'left-right' case from the top-level t1 match
        | .left t2_parent =>
              have newnums_eq: newNum t1_parent = newNum t2_parent := by
                by_contra!
                by_cases is_t1_lt: newNum t1_parent < newNum t2_parent
                .
                  have is_t1_le: newNum t1_parent ≤ newNum t2_parent := by
                    linarith
                  simp [ReverseTree.getData] at h_eq
                  have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t2_parent)) rfl
                  simp at fun_congr
                  have t1_a_zero := eval_larger_a_eq_zero t1_parent (newNum t2_parent) is_t1_le
                  have t1_b_zero := eval_larger_b_eq_zero t1_parent (newNum t2_parent) is_t1_le
                  have t2_a_zero := eval_larger_a_eq_zero t2_parent (newNum t2_parent) (by simp)
                  have t2_b_zero := eval_larger_b_eq_zero t2_parent (newNum t2_parent) (by simp)
                  simp [t1_a_zero, t1_b_zero, t2_a_zero, t2_b_zero, xSeq] at fun_congr
                  repeat rw [vals.x_to_index_eq] at fun_congr
                  simp [basis_n] at fun_congr
                  have vals_newnum_neq: vals.x_to_index (newNum t1_parent) ≠ vals.x_to_index (newNum t2_parent) := by
                    apply Function.Injective.ne vals.x_to_index_inj this
                  simp [Finsupp.single_eq_of_ne vals_newnum_neq] at fun_congr
                . have is_t2_le: newNum t2_parent ≤ newNum t1_parent := by
                    linarith
                  simp [ReverseTree.getData] at h_eq
                  have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t1_parent)) rfl
                  simp at fun_congr
                  have t1_a_zero := eval_larger_a_eq_zero t1_parent (newNum t1_parent) (by simp)
                  have t2_a_zero := eval_larger_a_eq_zero t2_parent (newNum t1_parent) is_t2_le
                  have t2_b_zero := eval_larger_b_eq_zero t2_parent (newNum t1_parent) is_t2_le
                  have t1_b_zero := eval_larger_b_eq_zero t1_parent (newNum t1_parent) (by simp)
                  simp [t1_a_zero, t1_b_zero, t2_a_zero, t2_b_zero, xSeq] at fun_congr
                  repeat rw [vals.x_to_index_eq] at fun_congr
                  simp [basis_n] at fun_congr
                  have vals_newnum_neq: vals.x_to_index (newNum t1_parent) ≠ vals.x_to_index (newNum t2_parent) := by
                    apply Function.Injective.ne vals.x_to_index_inj this
                  simp [Finsupp.single_eq_of_ne vals_newnum_neq.symm] at fun_congr
              have parents_eq: t1_parent = t2_parent := by
                exact newnum_injective t1_parent t2_parent newnums_eq
              use t1_parent
              right
              rw [parents_eq]
              refine ⟨rfl, rfl⟩
        | .right t2_parent =>
            by_cases is_t2_lt: newNum t2_parent < newNum t1_parent
            .
              have is_t2_le: newNum t2_parent ≤ newNum t1_parent := by
                linarith
              simp [ReverseTree.getData] at h_eq
              have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t1_parent)) rfl
              have t2_a_zero := eval_larger_a_eq_zero t2_parent (newNum t1_parent) is_t2_le
              have t2_b_zero := eval_larger_b_eq_zero t2_parent (newNum t1_parent) is_t2_le
              have t1_a_zero := eval_larger_a_eq_zero t1_parent (newNum t1_parent) (by simp)
              have t1_b_zero := eval_larger_b_eq_zero t1_parent (newNum t1_parent) (by simp)
              simp [t2_a_zero, t2_b_zero, t1_a_zero, t1_b_zero, xSeq] at fun_congr
              repeat rw [vals.x_to_index_eq] at fun_congr
              simp [basis_n] at fun_congr
              rw [Finsupp.single_apply, eq_comm] at fun_congr
              simp at fun_congr
              apply vals.x_to_index_inj at fun_congr
              have parents_eq: t2_parent = t1_parent := by
                exact newnum_injective t2_parent t1_parent fun_congr
              have t1_eq_t2: t1 = t2 := by
                rw [parents_eq.symm] at h_t1
                rwa [← h_t2] at h_t1
              rw [← h_t1, ← h_t2, t1_eq_t2] at h_a_neq
              contradiction
            .
              have is_t1_le: newNum t1_parent ≤ newNum t2_parent := by
                linarith
              simp [ReverseTree.getData] at h_eq
              have fun_congr := DFunLike.congr h_eq (x := vals.x_to_index (newNum t2_parent)) rfl
              simp at fun_congr
              have t1_a_zero := eval_larger_a_eq_zero t1_parent (newNum t2_parent) is_t1_le
              have t1_b_zero := eval_larger_b_eq_zero t1_parent (newNum t2_parent) is_t1_le
              have t2_a_zero := eval_larger_a_eq_zero t2_parent (newNum t2_parent) (by simp)
              have t2_b_zero := eval_larger_b_eq_zero t2_parent (newNum t2_parent) (by simp)
              simp [t1_a_zero, t1_b_zero, t2_a_zero, t2_b_zero, xSeq] at fun_congr
              repeat rw [vals.x_to_index_eq] at fun_congr
              simp [basis_n] at fun_congr
              rw [Finsupp.single_apply] at fun_congr
              simp at fun_congr
              apply vals.x_to_index_inj at fun_congr
              have parents_eq: t2_parent = t1_parent := by
                exact newnum_injective t2_parent t1_parent fun_congr.symm
              have t1_eq_t2: t1 = t2 := by
                rw [parents_eq.symm] at h_t1
                rwa [← h_t2] at h_t1
              rw [← h_t1, ← h_t2, t1_eq_t2] at h_a_neq
              contradiction


#print axioms cross_eq_same_parent

lemma partial_function {vals: XVals} {t1 t2: @ReverseTree vals} (h_a_eq: t1.getData.a = t2.getData.a) (h_min: ∀ (tree1 tree2: @ReverseTree vals), tree1.getData.a = tree2.getData.a ∧ tree1 ≠ tree2 → newNum t1 ≤ newNum tree1) (this: t1 ≠ t2): False := by
  match t1 with
  | .root =>
    match t2 with
    | .root => contradiction
    | .left t2_parent =>
        simp [ReverseTree.getData] at h_a_eq
        rw [vals.x_to_index_eq] at h_a_eq
        have b_neq := xseq_zero_neq_b t2_parent (-1) (by simp)
        simp at b_neq
        contradiction
    | .right t2_parent =>
        simp [ReverseTree.getData, vals.x_to_index_eq, basis_n] at h_a_eq
        have fun_neq := finsupp_new_zero_newnum t2_parent 1 1 (by simp)
        contradiction
  | .left t1_parent =>
    match t2 with
    | .root =>
        simp [ReverseTree.getData, vals.x_to_index_eq, basis_n] at h_a_eq
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
                simp only [vals.x_to_index_eq] at h_a_eq
                apply basis_n_injective at h_a_eq
                apply vals.x_to_index_inj at h_a_eq
                have val_gt_one := newnem_gt_one t2_parent_parent
                omega
            | .right t2_parent_parent =>
                simp [ReverseTree.getData, vals.x_to_index_eq, basis_n] at h_a_eq
                have vals_neq := basis_neq_elem_diff t2_parent_parent (vals.x_to_index 1) (-1) 1 1 (by simp) (by simp) (by simp)
                simp only [one_smul, neg_one_smul] at vals_neq
                rw [add_comm, ← sub_eq_add_neg] at vals_neq
                contradiction
        | .left t1_parent_parent =>
            match t2_parent with
            | .root =>
              simp [ReverseTree.getData] at h_a_eq
              apply vals.x_inj at h_a_eq
              have val_gt_one := newnem_gt_one t1_parent_parent
              omega
            | .left t2_parent_parent =>
              -- If both parents are left trees - we know that left trees have unique 'b' values so their parents must be the same node. But then our original nodes are left children of the same node, so they're again the same node - contradiction
              simp [ReverseTree.getData] at h_a_eq
              apply vals.x_inj at h_a_eq
              apply newnum_injective at h_a_eq
              rw [h_a_eq] at this
              contradiction
            | .right t2_parent_parent =>
                simp [ReverseTree.getData, vals.x_to_index_eq, basis_n] at h_a_eq
                rw [← Finsupp.single_neg] at h_a_eq
                have vals_neq := basis_neq_elem_diff t2_parent_parent (vals.x_to_index (newNum t1_parent_parent)) (1) (-1) (-1) (by simp) (by simp) (by simp)
                simp at vals_neq
                rw [← sub_eq_add_neg, ← Finsupp.single_neg] at vals_neq
                contradiction
        | .right t1_parent_parent =>
          match t2_parent with
          | .root =>
            simp [ReverseTree.getData, vals.x_to_index_eq, basis_n] at h_a_eq
            rw [← Finsupp.single_neg] at h_a_eq
            have vals_neq := basis_neq_elem_diff t1_parent_parent (vals.x_to_index 1) (1) (-1) (-1) (by simp) (by simp) (by simp)
            simp only [one_smul, neg_one_smul] at vals_neq
            rw [← sub_eq_add_neg] at vals_neq
            rw [eq_comm] at h_a_eq
            contradiction
          | .left t2_parent_parent =>
            simp [ReverseTree.getData, vals.x_to_index_eq, basis_n] at h_a_eq
            rw [← Finsupp.single_neg] at h_a_eq
            have vals_neq := basis_neq_elem_diff t1_parent_parent (vals.x_to_index (newNum t2_parent_parent)) 1 (-1) (-1) (by simp) (by simp) (by simp)
            simp only [one_smul, neg_one_smul] at vals_neq
            rw [← sub_eq_add_neg] at vals_neq
            rw [eq_comm] at h_a_eq
            contradiction
          | .right t2_parent_parent =>
            -- So, both parents must be right trees.
            simp [ReverseTree.getData] at h_a_eq

            have grandparents_neq: t1_parent_parent ≠ t2_parent_parent := by
              by_contra! grandparents_eq
              rw [grandparents_eq] at this
              simp at this

            -- This is where we use the minimality assumption
            have parents_a_neq: t1_parent_parent.getData.a ≠ t2_parent_parent.getData.a := by
              by_contra! grandparent_a_eq
              specialize h_min t1_parent_parent t2_parent_parent ⟨grandparent_a_eq, grandparents_neq⟩
              have newnum_gt_right := (newnum_increasing t1_parent_parent).2
              have newnum_gt_left := (newnum_increasing t1_parent_parent.right).1
              omega

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
              exact common_ancestor_stuff ancestor t1_parent_parent t2_parent_parent left_right h_a_eq
            | inr right_left =>
              exact common_ancestor_stuff ancestor t2_parent_parent t1_parent_parent right_left.symm h_a_eq.symm
    | .right t2_parent =>
      simp [ReverseTree.getData] at h_a_eq
      match t1_parent with
      | .root =>
        simp [ReverseTree.getData, vals.x_to_index_eq, basis_n] at h_a_eq
        have fun_neq := finsupp_new_one_newnum t2_parent (-1) 1 (by simp)
        rw [← Finsupp.single_neg] at h_a_eq
        contradiction
      | .left t1_parent_parent =>
        simp [ReverseTree.getData, vals.x_to_index_eq, basis_n] at h_a_eq
        rw [← Finsupp.single_neg] at h_a_eq
        rw [Finsupp.single_eq_single_iff] at h_a_eq
        match h_a_eq with
        | .inl ⟨_, neq_eq_one⟩ =>
          contradiction
        | .inr ⟨neq_eq_one, _⟩ =>
          contradiction
      | .right t1_parent_parent =>
        simp [ReverseTree.getData, vals.x_to_index_eq, basis_n] at h_a_eq
        have vals_neq := basis_neq_elem_diff t1_parent_parent (vals.x_to_index (newNum t2_parent)) 1 (-1) 1 (by simp) (by simp) (by simp)
        simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at vals_neq
        rw [eq_comm] at h_a_eq
        contradiction
  | .right t1_parent =>
    match t2 with
    | .root =>
        simp [ReverseTree.getData] at h_a_eq
        have newnum_gt_one := newnem_gt_one t1_parent
        simp [vals.x_to_index_eq, basis_n] at h_a_eq
        have one_ne_zero: (1 : ℚ) ≠ 0 := by
          simp
        have single_injective := Finsupp.single_left_injective (α := ℕ) one_ne_zero
        simp [Function.Injective] at single_injective
        specialize @single_injective (vals.x_to_index (newNum t1_parent)) (vals.x_to_index 0) h_a_eq
        apply vals.x_to_index_inj at single_injective
        linarith
    | .left t2_parent =>
      simp [ReverseTree.getData] at h_a_eq
      match t2_parent with
      | .root =>
        simp [ReverseTree.getData, vals.x_to_index_eq, basis_n] at h_a_eq
        rw [← Finsupp.single_neg] at h_a_eq
        have eval_at: (fun₀ | (vals.x_to_index (newNum t1_parent)) => 1) (vals.x_to_index (newNum t1_parent)) = (fun₀ | (vals.x_to_index 1) => (-1: ℚ)) (vals.x_to_index (newNum t1_parent)) := by
          refine DFunLike.congr ?h₁ rfl
          exact h_a_eq
        simp at eval_at
        have newnum_gt_one: 1 < newNum t1_parent := by
          exact newnem_gt_one t1_parent
        have newnum_neq_one: 1 ≠ newNum t1_parent := by
          linarith
        have index_one_neq: vals.x_to_index 1 ≠ vals.x_to_index (newNum t1_parent) := by
          apply Function.Injective.ne vals.x_to_index_inj newnum_neq_one
        rw [Finsupp.single_apply] at eval_at
        simp [index_one_neq] at eval_at
      | .left t2_parent_parent =>
          -- b is fresh - it must therefore come from a different node, which will therefore have a different basis element - contradiction.
          simp [ReverseTree.getData, xSeq] at h_a_eq
          apply eq_neg_iff_add_eq_zero.mp at h_a_eq
          have basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis
          simp [n_q_basis] at basis_indep
          have linear_indep: LinearIndependent ℚ ![fun₀ | (vals.x_to_index (newNum t1_parent)) => (1 : ℚ), fun₀ | (vals.x_to_index (newNum t2_parent_parent)) => 1] := by
            apply LinearIndependent.pair_iff.mpr
            intro s t h_sum_zero

            simp [linearIndependent_iff'] at basis_indep
            specialize basis_indep {vals.x_to_index (newNum t1_parent), vals.x_to_index (newNum t2_parent_parent)}
            have parents_neq: t1_parent ≠ t2_parent_parent := by
              by_contra! other_parents_eq
              simp [other_parents_eq] at h_a_eq
              simp [add_eq_zero_iff_eq_neg] at h_a_eq
              have eq_zero: (fun₀ | (vals.x_to_index (newNum t2_parent_parent)) => 1) = 0 := by
                simp [vals.x_to_index_eq] at h_a_eq
                simp [← Finsupp.single_neg] at h_a_eq
                simp [Finsupp.single] at h_a_eq
                contradiction
              simp at eq_zero

            have nums_not_eq: newNum t1_parent ≠  newNum t2_parent_parent := by
              apply Function.Injective.ne newnum_injective parents_neq
            have num_reverse: newNum t2_parent_parent ≠ newNum t1_parent := by
              exact id (Ne.symm nums_not_eq)
            have val_newnums_neq: vals.x_to_index (newNum t2_parent_parent) ≠ vals.x_to_index (newNum t1_parent) := by
              apply Function.Injective.ne vals.x_to_index_inj num_reverse
            let g : ℕ → ℚ := fun n => if n = vals.x_to_index (newNum t1_parent) then s else if n = (vals.x_to_index (newNum t2_parent_parent)) then t else 0
            have finsum_to_pair := Finset.sum_pair (f := fun x => fun₀ | x => g x) val_newnums_neq.symm
            specialize basis_indep g
            simp only [g] at basis_indep
            simp [g] at finsum_to_pair
            simp only [finsum_to_pair] at basis_indep
            simp only [val_newnums_neq] at basis_indep
            simp at h_sum_zero
            specialize basis_indep h_sum_zero
            have s_eq_zero := basis_indep (vals.x_to_index (newNum t1_parent))
            simp at s_eq_zero
            have t_eq_zero := basis_indep (vals.x_to_index (newNum t2_parent_parent))
            simp [val_newnums_neq] at t_eq_zero
            exact ⟨s_eq_zero, t_eq_zero⟩
          simp [LinearIndependent.pair_iff] at linear_indep
          simp [vals.x_to_index_eq, basis_n] at h_a_eq
          specialize linear_indep 1 1 h_a_eq
          contradiction
      | .right t2_parent_parent =>
        --  b = p - q for some p and q. We know that p and q have disjoint coordinates, and q is not zero, so we have two different representations for 'a' - impossible.
        simp [ReverseTree.getData, vals.x_to_index_eq, basis_n] at h_a_eq
        have vals_neq := basis_neq_elem_diff t2_parent_parent (vals.x_to_index (newNum t1_parent)) 1 (-1) 1 (by simp) (by simp) (by simp)
        simp only [one_smul, neg_one_smul, ← sub_eq_add_neg] at vals_neq
        contradiction
    | .right t2_parent =>
      -- If they're both right trees, contradiction - all right trees have unique 'a' values
      simp [ReverseTree.getData] at h_a_eq
      apply vals.x_inj at h_a_eq
      apply newnum_injective at h_a_eq
      simp [h_a_eq] at this



#print axioms partial_function


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

lemma temp_partial_function {vals: XVals}: ∀ {t1 t2: @ReverseTree vals}, (t1.getData.a = t2.getData.a) → t1 = t2 := by
  intro t1 t2
  by_contra!
  let counterexamples := {(t1, t2) : (@ReverseTree vals × ReverseTree) | t1.getData.a = t2.getData.a ∧ t1 ≠ t2}
  let first_newnum := fun ((t1, t2): (@ReverseTree vals × @ReverseTree vals)) => newNum t1

  --let min_num := counter_nums.min counter_nonempty
  have counter_nonempty: counterexamples.Nonempty := by
    simp [Set.Nonempty, counterexamples]
    use t1
    use t2

  let counter_nums := first_newnum '' counterexamples
  have counter_nums_nonempty: counter_nums.Nonempty := by
    simp [counter_nums]
    exact counter_nonempty

  let min_newnum := Nat.lt_wfRel.wf.min counter_nums counter_nums_nonempty
  have min_newnum_le: ∀ (tree1 tree2: @ReverseTree vals), tree1.getData.a = tree2.getData.a ∧ tree1 ≠ tree2 → min_newnum ≤ newNum tree1 := by
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
    obtain ⟨t1, t2, h_t1_eq, h_min⟩ := min_mem
    use t1
    use t2
  obtain ⟨t1, t2, h_t1_eq, h_min⟩ := min_pair
  simp [counterexamples] at h_t1_eq
  rw [← h_min] at min_newnum_le
  exact partial_function h_t1_eq.1 min_newnum_le h_t1_eq.2

lemma g_countable: Countable (@Set.univ G) := by
  simp [G]
  exact Set.countable_univ

noncomputable def g_denumerable: Denumerable G := by
  have nonempty_denum := (nonempty_denumerable_iff (α := G)).mpr ⟨(by infer_instance), (by infer_instance)⟩
  exact Classical.choice nonempty_denum

noncomputable abbrev g_enumerate: ℕ → G := by
  have nonempty_denum := (nonempty_denumerable_iff (α := G)).mpr ⟨(by infer_instance), (by infer_instance)⟩
  have bar := Classical.choice nonempty_denum
  exact Denumerable.ofNat G

lemma g_enum_zero_eq_one: g_enumerate 0 = basis_n 1 := by
  sorry

#synth Encodable G

noncomputable def g_to_num (g: G): ℕ := by
  have nonempty_denum := (nonempty_denumerable_iff (α := G)).mpr ⟨(by infer_instance), (by infer_instance)⟩
  have bar := Classical.choice nonempty_denum
  exact bar.toEncodable.encode g

def g_num_inverse (n: ℕ): g_to_num (g_enumerate n) = n := by
  sorry

def g_enum_inverse (g: G): g_enumerate (g_to_num g) = g := by
  sorry


def tree_to_supp {vals: XVals} (t: @ReverseTree vals): Set ℕ :=
  t.getData.a.support.toSet

structure XValsFullData (n: ℕ) where
  vals: Set XVals
  from_mk: ∀ x_vals: XVals, x_vals ∈ vals → ∃ n, x_vals = mk_x_vals n
  contains_n: ∃ x_vals: XVals, ∃ t: @ReverseTree x_vals, x_vals ∈ vals ∧ t.getData.a = (g_enumerate n)




noncomputable def full_x_vals (n: ℕ): XValsFullData n := by
  match n with
  | 0 => exact {
        vals := {mk_x_vals 0},
        from_mk := by
          simp
        contains_n := by
          use mk_x_vals 0
          use ReverseTree.root
          simp [g_enum_zero_eq_one]
          simp [ReverseTree.getData, mk_x_vals, XVals.x_vals]
      }
  | n + 1 =>
    let prev_x_vals := full_x_vals n
    by_cases exists_tree: ∃ x_vals: XVals, ∃ t: @ReverseTree x_vals, x_vals ∈ prev_x_vals.vals ∧ t.getData.a = (g_enumerate (n + 1))
    . exact {
        vals := prev_x_vals.vals,
        from_mk := prev_x_vals.from_mk,
        contains_n := exists_tree
      }
      -- TODO - build new tree
    .
      have candidate_val: ∃ new_vals: XVals, ∃ t :@ReverseTree new_vals, t.getData.a = (g_enumerate (n + 1)) := by
        sorry
      let x_vals_to_supp := (λ new_x_vals : XVals => (tree_to_supp '' Set.univ (α := @ReverseTree new_x_vals)).sUnion)
      have all_prev_supps := (x_vals_to_supp '' prev_x_vals.vals).sUnion
      have s_i_without: ∃ i, ((g_enumerate n).support.toSet ∪ all_prev_supps) ∩ ((λ s => s.2.support.toSet) '' (s_i i)).sUnion = ∅ := by
        by_contra!
        sorry
      have i := Classical.choose s_i_without
      let new_x_vals  := mk_x_vals i
      exact  {
        vals := prev_x_vals.vals ∪ {new_x_vals},
        from_mk := by
          simp
          exact prev_x_vals.from_mk
        contains_n := by
          use mk_x_vals i
          sorry


      }



structure GAndProof (n: ℕ) where
  x_vals: XVals
  tree: @ReverseTree x_vals
  proof: tree.getData.a = (g_enumerate n)
  new_proof: ∀ t: @ReverseTree x_vals, t.getData.a = (g_enumerate n) → t = tree
  --zero_if_zero: n = 0 → x_vals = mk_x_vals 0
  preserved_val: ∀ vals: XVals, (∃ t: @ReverseTree vals, t.getData.a = (g_enumerate n)) → x_vals = vals

lemma neq_implies_neq_i {vals1 vals2: XVals} (h_vals: vals1 ≠ vals2): vals1.i ≠ vals2.i := by
  by_contra! vals_eq
  have vals_destructure: vals1 = { i := vals1.i} := by
    simp
  have choose_destructure: vals2 = { i := vals2.i} := by
    simp
  rw [vals_eq] at vals_destructure
  rw [← choose_destructure] at vals_destructure
  contradiction

-- TODO - what exactly is the interpretation of this lemma, and why can't lean figure it our for us?
lemma cast_data_eq {vals1 vals2: XVals} (t: @ReverseTree vals1) (h_vals: vals1 = vals2) (hv: @ReverseTree vals1 = @ReverseTree vals2): t.getData = (cast hv t).getData := by
  congr
  rw [heq_comm]
  simp

-- Maps the nth element of G by applying our construced function 'f'
noncomputable def full_fun_from_n (n: ℕ): GAndProof n := by
  by_cases n_tree_left: ∃ x_vals: XVals, ∃ t: @ReverseTree x_vals, t.getData.a = (g_enumerate n)
  .
    exact {
      x_vals := Classical.choose n_tree_left,
      tree := Classical.choose (Classical.choose_spec n_tree_left),
      proof := Classical.choose_spec (Classical.choose_spec n_tree_left),
      new_proof := by
        intro t ht
        let same_x_vals := Classical.choose n_tree_left
        have other_proof := Classical.choose_spec (Classical.choose_spec n_tree_left)
        conv at other_proof =>
          rhs
          rw [← ht]
        have same_tree := temp_partial_function other_proof
        exact same_tree.symm
      -- zero_if_zero := by
      --   intro hn
      --   have my_spec := Classical.choose_spec (Classical.choose_spec n_tree_left)
      --   have g_enum_eq_one: g_enumerate n = basis_n 1 := by
      --     rw [hn, g_enum_zero_eq_one]
      --   match h_eq : Classical.choose (Classical.choose_spec n_tree_left) with
      --   | .root =>
      --       simp only [h_eq] at my_spec
      --       simp only [ReverseTree.getData] at my_spec
      --       have mk_vals_zero_eq: (mk_x_vals 0).x_vals 0 = basis_n 1 := by
      --         simp [mk_x_vals, XVals.x_vals]
      --       by_contra!
      --       -- TODO - there must be a simpler way to do this
      --       have vals_i_neq: (Classical.choose n_tree_left).i ≠ (mk_x_vals 0).i := by
      --         by_contra! vals_eq
      --         have vals_destructure: (mk_x_vals 0) = { i := (mk_x_vals 0).i} := by
      --           simp
      --         have choose_destructure: (Classical.choose n_tree_left) = { i := (Classical.choose n_tree_left).i} := by
      --           simp
      --         rw [← vals_eq] at vals_destructure
      --         rw [← choose_destructure] at vals_destructure
      --         rw [eq_comm] at vals_destructure
      --         contradiction
      --       have vals_disjoint := mk_vals_disjoint (Classical.choose n_tree_left) (mk_x_vals 0) vals_i_neq
      --       sorry
      --   | .left t1_parent => sorry
      --   | .right t1_parent => sorry
      preserved_val := by
        intro vals h_t
        obtain ⟨first_t, h_first_t⟩ := h_t
        let second_t := Classical.choose (Classical.choose_spec n_tree_left)
        have h_second_t := Classical.choose_spec (Classical.choose_spec n_tree_left)
        --obtain ⟨second_vals, second_t, h_second_t⟩ := n_tree_left
        rw [← h_second_t] at h_first_t
        obtain ⟨⟨first_g, first_m, first_m_lt, first_m_supp, first_data_eq⟩, _⟩ := tree_linear_comb first_t
        obtain ⟨⟨second_g, second_m, second_lt, second_m_supp, second_data_eq⟩, _⟩ := tree_linear_comb second_t
        have first_data_eq_orig := first_data_eq

        have vals_eq: vals = (Classical.choose n_tree_left) := by
          by_contra! vals_neq
          have i_neq := neq_implies_neq_i vals_neq
          have vals_disjoint := mk_vals_disjoint vals (Classical.choose n_tree_left) i_neq

          have inject_sum := LinearIndependent.injective_linearCombination (Basis.linearIndependent n_q_basis)

          have first_lin_comb := Finsupp.linearCombination_apply (M := G) (v := λ x => basis_n (vals.x_to_index x)) ℚ (first_g)
          simp only [Finsupp.sum] at first_lin_comb
          have first_sum_eq: (∑ x ∈ first_g.support, first_g x • basis_n (vals.x_to_index x)) = ∑ i ∈ Finset.range first_m, first_g i • basis_n (vals.x_to_index i) := by
            apply Finset.sum_subset
            .
              intro x hx
              simp

              have x_le_max: x ≤ first_g.support.max := by
                apply Finset.le_max hx

              simp at x_le_max
              have trans_le := LE.le.trans_lt x_le_max first_m_supp
              exact WithBot.some_lt_some.mp trans_le
            .
              intro x hx x_not_supp
              simp [Finsupp.not_mem_support_iff.mp x_not_supp]



          rw [first_sum_eq] at first_lin_comb
          simp only [vals.x_to_index_eq] at first_data_eq
          rw [← first_lin_comb] at first_data_eq
          have first_comp_eq: ((fun x ↦ basis_n x) ∘ fun x ↦ vals.x_to_index x) = fun x => basis_n (vals.x_to_index x) := by
            exact rfl
          have first_comp_apply := Finsupp.linearCombination_comp (R := ℚ) (v := λ x => basis_n x) (λ x => (vals).x_to_index x)
          rw [first_comp_eq] at first_comp_apply


          have second_lin_comb := Finsupp.linearCombination_apply (M := G) (v := λ x => basis_n ((Classical.choose n_tree_left).x_to_index x)) ℚ (second_g)
          simp only [Finsupp.sum] at second_lin_comb
          have second_sum_eq: (∑ x ∈ second_g.support, second_g x • basis_n ((Classical.choose n_tree_left).x_to_index x)) = ∑ i ∈ Finset.range second_m, second_g i • basis_n ((Classical.choose n_tree_left).x_to_index i) := by
            apply Finset.sum_subset
            -- TODO - get 'max' working
            .
              intro x hx
              simp

              have x_le_max: x ≤ second_g.support.max := by
                apply Finset.le_max hx

              simp at x_le_max
              have trans_le := LE.le.trans_lt x_le_max second_m_supp
              exact WithBot.some_lt_some.mp trans_le
            .
              intro x hx x_not_supp
              simp [Finsupp.not_mem_support_iff.mp x_not_supp]



          rw [second_sum_eq] at second_lin_comb
          simp only [(Classical.choose n_tree_left).x_to_index_eq] at second_data_eq
          rw [← second_lin_comb] at second_data_eq
          have second_comp_eq: ((fun x ↦ basis_n x) ∘ fun x ↦ (Classical.choose n_tree_left).x_to_index x) = fun x => basis_n ((Classical.choose n_tree_left).x_to_index x) := by
            exact rfl
          have second_comp_apply := Finsupp.linearCombination_comp (R := ℚ) (v := λ x => basis_n x) (λ x => (Classical.choose n_tree_left).x_to_index x)
          rw [second_comp_eq] at second_comp_apply

          rw [first_data_eq, second_data_eq] at h_first_t
          rw [first_comp_apply, second_comp_apply] at h_first_t
          apply inject_sum at h_first_t
          simp only [Finsupp.lmapDomain_apply] at h_first_t
          have map_inj := Finsupp.mapDomain_injective (M := ℚ) (vals.x_to_index_inj)

          have g_eq_zero: ∀ n, first_g n = 0 := by
            intro n
            have my_arg := congr_arg (Finsupp.mapDomain (fun x ↦ vals.x_to_index x) first_g) (a₁ := vals.x_to_index n) rfl
            nth_rw 1 [h_first_t] at my_arg
            have map_apply_first := Finsupp.mapDomain_apply (vals.x_to_index_inj) first_g n
            have map_apply_second := Finsupp.mapDomain_apply ((Classical.choose n_tree_left).x_to_index_inj) second_g n
            simp only [map_apply_first] at my_arg
            simp  [Finsupp.mapDomain, Finsupp.sum] at my_arg
            simp [Finsupp.single_apply] at my_arg

            have index_not_eq: ∀ c: ℕ , (Classical.choose n_tree_left).x_to_index c ≠ (vals.x_to_index n) := by
              by_contra!
              obtain ⟨c, hc⟩ := this
              have basis_n_eq: basis_n ((Classical.choose n_tree_left).x_to_index c) = basis_n (vals.x_to_index n) := by
                rw [hc]
              rw [← vals.x_to_index_eq] at basis_n_eq
              rw [← (Classical.choose n_tree_left).x_to_index_eq] at basis_n_eq
              have val_n_range: vals.x_vals n ∈ Set.range vals.x_vals := by
                simp
              have val_c_range: (Classical.choose n_tree_left).x_vals c ∈ Set.range (Classical.choose n_tree_left).x_vals := by
                simp
              rw [basis_n_eq] at val_c_range
              have val_n_intersect: vals.x_vals n ∈ Set.range vals.x_vals ∩ Set.range (Classical.choose n_tree_left).x_vals  := by
                exact ⟨val_n_range, val_c_range⟩
              have inter_nonempty: Set.range vals.x_vals ∩ Set.range (Classical.choose n_tree_left).x_vals ≠ ∅ := by
                exact ne_of_mem_of_not_mem' val_n_intersect fun a ↦ a
              contradiction

            simp [index_not_eq] at my_arg
            exact my_arg.symm

          simp [g_eq_zero] at first_data_eq_orig
          have first_t_neq_zero := (tree_vals_nonzero first_t).1
          contradiction
        exact vals_eq.symm
        -- have types_eq: @ReverseTree vals = @ReverseTree second_vals := by
        --   simp [vals_eq]
        -- have other := cast_data_eq first_t vals_eq types_eq
        -- rw [other] at h_first_t
        -- have trees_eq := temp_partial_function h_first_t




    }

  let candidate_x_vals := (full_x_vals n).vals
  have val_in_x_vals: ∃ x_vals: XVals, ∃ t: @ReverseTree x_vals, x_vals ∈ candidate_x_vals ∧ t.getData.a = (g_enumerate n) := by
    have my_proof := (full_x_vals n).contains_n
    simp [candidate_x_vals]
    obtain ⟨new_vals , ⟨t, h_vals_and_t⟩⟩ := my_proof
    use new_vals
    refine ⟨?_, ?_⟩
    exact h_vals_and_t.1
    use t
    exact h_vals_and_t.2


    --have trees_eq := temp_partial_function (t1 := other_t) (t2 := t) other_a_eq

    --simp [candidate_x_vals, full_x_vals] at h_other_t

  let h_x_val := Classical.choose_spec val_in_x_vals
  let tree := Classical.choose h_x_val
  have simplified: ∃ x_vals: XVals, ∃ t: @ReverseTree x_vals, t.getData.a = (g_enumerate n) := by
    obtain ⟨x_vals, t, h⟩ := val_in_x_vals
    use x_vals
    use t
    exact h.2
  obtain ⟨_, tree_eq⟩ := Classical.choose_spec h_x_val


  -- have zero_if_zero: n = 0 → (Classical.choose val_in_x_vals) = mk_x_vals 0 := by
  --   by_cases n_eq_zero: n = 0
  --   .
  --     simp [n_eq_zero]
  --     have choose_in := Classical.choose_spec val_in_x_vals
  --     have candidate_eq_zero: candidate_x_vals = {mk_x_vals 0} := by
  --       simp [candidate_x_vals, n_eq_zero, full_x_vals]
  --     simp only [candidate_eq_zero, Set.mem_singleton_iff] at val_in_x_vals
  --     simp only [candidate_eq_zero, Set.mem_singleton_iff] at choose_in
  --     obtain ⟨_, choose_eq, _⟩ := choose_in
  --     simp [candidate_eq_zero]
  --     simp [n_eq_zero] at choose_eq
  --     exact choose_eq
  --   . simp [n_eq_zero]

  exact {
    x_vals := (Classical.choose val_in_x_vals),
    tree := tree,
    proof := tree_eq,
    --zero_if_zero := zero_if_zero,
    preserved_val := by
      intro vals
      simp only [not_exists] at n_tree_left
      specialize n_tree_left vals
      rw [← not_exists] at n_tree_left
      simp [n_tree_left]
  }


noncomputable abbrev f (g: G): G := (full_fun_from_n (g_to_num g)).tree.getData.b

-- Starting value: a

--        - (-b, c)
-- (a, b)
--        - (c, a - b)

-- LHS
-- -f (a) = -b
-- f(-b) = c
-- f(c) = a - b
-- RHS
-- a - f(a) = a - b


lemma x_vals_preserved {vals: XVals} (t: @ReverseTree vals): (full_fun_from_n (g_to_num t.getData.a)).x_vals = vals := by
  have proof := (full_fun_from_n (g_to_num t.getData.a)).preserved_val
  have my_tree : (∃ t_1: @ReverseTree vals, t_1.getData.a = g_enumerate (g_to_num t.getData.a)) := by
    use t
    rw [g_enum_inverse]
  exact proof vals my_tree



lemma f_eval_at {vals: XVals} (t: @ReverseTree vals): f (t.getData.a) = t.getData.b := by
  simp [f]
  have preserved := x_vals_preserved t
  have proof := (full_fun_from_n (g_to_num t.getData.a)).proof
  rw [g_enum_inverse] at proof
  have types_eq: @ReverseTree (full_fun_from_n (g_to_num t.getData.a)).x_vals = @ReverseTree vals := by
    simp [preserved]

  have my_cast_data := cast_data_eq t preserved.symm types_eq.symm
  conv at proof =>
    rhs
    rw [my_cast_data]

  -- rw [← preserved] at t

  have bar := temp_partial_function proof
  have tree_eq: (full_fun_from_n (g_to_num t.getData.a)).tree.getData.b = t.getData.b := by
    rw [bar, ← my_cast_data]
  exact tree_eq
    --temp_partial_function proof

lemma f_eval_at_b (vals: XVals) (t: @ReverseTree vals): f (-t.getData.b) = t.left.getData.b := by
  have t_left_a_eq: -t.getData.b = t.left.getData.a := by
    simp [ReverseTree.getData]
  rw [t_left_a_eq]
  rw [f_eval_at t.left]


lemma f_function_eq (g: G): f (f (- f g)) = g - (f g) := by
  conv =>
    pattern - f g
    simp [f]
  rw [f_eval_at_b]

  have left_b_eq: (full_fun_from_n (g_to_num g)).tree.left.getData.b = (full_fun_from_n (g_to_num g)).tree.right.getData.a := by
    simp [ReverseTree.getData]

  rw [left_b_eq]
  rw [f_eval_at]
  simp [ReverseTree.getData]
  rw [(full_fun_from_n (g_to_num g)).proof]
  rw [g_enum_inverse]


#print axioms temp_partial_function

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

lemma second_equiv (f: G → G) (hf: ∀ g: G, f (f (- f g)) = g - (f g)): ∀ x y: G, x = x + (y - x) + (f (-(y - x))) + (f (f (- (f (- (y - x))))))  := by
    intro x y
    specialize hf (x - y)
    simp [hf]

-- TODO - don't use 'f' for both our real function and a variable
-- Our constructed function 'f' satisfies the diamond law
lemma diamond_real_f (x y: G): x = (diamond f (x + (y - x) + (f (-(y - x)))) (diamond f (x + (y - x) + (f (-(y - x)))) (x + y - x))) := by
  rw [first_equiv]
  have other_equiv := second_equiv f f_function_eq x y
  rw [← other_equiv]


noncomputable abbrev f_0 := f (g_enumerate 0)

lemma f_zero_tree: f_0 = f (ReverseTree.root (vals := (mk_x_vals 0))).getData.a := by
  simp [f_0, ReverseTree.getData, g_enum_zero_eq_one]
  simp [mk_x_vals, XVals.x_vals]


-- lemma f_zero_eq: f (g_enumerate 0) = (mk_x_vals 0).x_vals 1 := by
--   simp [f]
--   have proof := (full_fun_from_n 0).proof
--   have other_proof := (full_fun_from_n 0).preserved_val
--   have x_vals_eq: (full_fun_from_n 0).x_vals = mk_x_vals 0 := by
--     have proof := (full_fun_from_n 0).zero_if_zero
--     simp at proof
--     exact proof

--   have tree_eq: (ReverseTree.root (vals := (full_fun_from_n 0).x_vals)).getData.a = (g_enumerate 0) := by
--     rw [x_vals_eq, g_enum_zero_eq_one]
--     simp [ReverseTree.getData]
--     simp [mk_x_vals]

--   rw [← proof] at tree_eq
--   have fun_tree_eq := temp_partial_function tree_eq
--   rw [g_num_inverse]
--   rw [← fun_tree_eq]
--   simp [ReverseTree.getData]
--   rw [x_vals_eq]




structure MyInner where
  data: ℕ
  with_prop: 1 = 1

inductive Outer {a: MyInner} where
| root: Outer
| other: Outer → Outer

lemma cast_outer (a_1 a_2: MyInner) (outer_a: @Outer a_1) (outer_b: @Outer a_2) (h_a_eq: a_1 = a_2): True := by
  have first_eq: ∃ b, b = outer_b := by
    use outer_b
  have types_eq: @Outer a_1 = @Outer a_2 := by
    rw [h_a_eq]
  subst types_eq
  have other_eq: ∃ b: @Outer a_1, b = outer_b := by
    sorry



lemma not_equation_23: (f 0) + (f (- (f 0))) ≠ 0 := by
  simp [f]
  have eq_left_child: (full_fun_from_n (g_to_num (-(full_fun_from_n (g_to_num 0)).tree.getData.b))).tree.getData.b = (full_fun_from_n (g_to_num 0)).tree.left.getData.b := by
    sorry
  rw [eq_left_child]
  simp [ReverseTree.getData]
  -- TODO - when starting a new tree, we need to make our new element the root
  have zero_eq_x_vals_zero: (full_fun_from_n (g_to_num 0)).tree.getData.b = (full_fun_from_n (g_to_num 0)).x_vals.x_vals 0 := by
    sorry
  rw [zero_eq_x_vals_zero]
  have newnum_neq_zero: 0 ≠ newNum (full_fun_from_n (g_to_num 0)).tree := by
    have gt_one := newnem_gt_one (full_fun_from_n (g_to_num 0)).tree
    linarith

  simp [XVals.x_to_index_eq]

  -- TODO - extract this out to apply linear independence to pair of finsupp
  have basis_indep: LinearIndependent ℚ n_q_basis := Basis.linearIndependent n_q_basis
  rw [linearIndependent_iff'] at basis_indep

  let zero_val := (full_fun_from_n (g_to_num 0)).x_vals.x_to_index 0
  let one_val := (full_fun_from_n (g_to_num 0)).x_vals.x_to_index (newNum (full_fun_from_n (g_to_num 0)).tree)
  have my_set: Finset ℕ := {zero_val, one_val}
  have eq_false: (∀ i ∈ my_set, 1 = 0) = False := by
    sorry
  specialize basis_indep {zero_val, one_val} fun g => 1

  have zero_val_neq: zero_val ≠ one_val := by
    sorry

  -- TODO - this is really messy
  rw [Finset.sum_pair zero_val_neq] at basis_indep
  simp [zero_val_neq, zero_val_neq.symm] at basis_indep
  apply not_imp_not.mpr at basis_indep
  simp at basis_indep
  specialize basis_indep one_val
  simp [zero_val, one_val] at basis_indep
  exact basis_indep


lemma not_equation_47: 0 ≠ f (f (f 0)) := by
  rw [f]
  exact (tree_vals_nonzero (full_fun_from_n (g_to_num (f (f 0)))).tree).2.symm



lemma not_equation_1832: 0 ≠ f (f 0) + f ((f 0) - f (f 0)) := by
  have neg_4_not_in: ∀ t: @ReverseTree (mk_x_vals 0), t.getData.b ≠ - (mk_x_vals 0).x_vals 4 := by
    sorry
  have neg_4_not_all: ∀ {vals: XVals}, ∀ t: @ReverseTree vals, t.getData.b ≠ - (mk_x_vals 0).x_vals 4 := by
    sorry
  have f_1_eq: f ((mk_x_vals 0).x_vals 1) = (mk_x_vals 0).x_vals 4 := by
    sorry

  conv =>
    rhs
    pattern f 0
    rw [f_zero_tree]

  rw [f_eval_at]
  simp [ReverseTree.getData]
  rw [f_1_eq]
  rw [f]
  specialize neg_4_not_all ((full_fun_from_n (g_to_num (f 0 - f (f 0)))).tree)
  rw [eq_comm, add_eq_zero_iff_eq_neg]
  rw [Ne, eq_comm, neg_eq_iff_eq_neg] at neg_4_not_all
  exact neg_4_not_all


lemma f_neg_f: f (- (f_0)) = ((mk_x_vals 0).x_vals 2) := by
  simp  [f_zero_tree, f_eval_at, f_eval_at_b]
  simp [ReverseTree.getData, newNum]

lemma not_equation_2441: 0 ≠ (f ((f_0) + f (-(f_0)))) + (f ( -(f ((f_0) + f (- (f_0))))) ) := by
  have f_neq_one_eq: f (- (mk_x_vals 0).x_vals 1) = (mk_x_vals 0).x_vals 2 := by
    sorry
  have f_x_plus: f (((mk_x_vals 0).x_vals 1) + ((mk_x_vals 0).x_vals 2)) = (mk_x_vals 0).x_vals 6 := by
    sorry
  have f_x_minus_7: f (- (mk_x_vals 0).x_vals 6) = (mk_x_vals 0).x_vals 11 := by
    sorry

  rw [f_zero_tree, f_eval_at]
  simp [ReverseTree.getData]
  simp [f_neq_one_eq]

  simp [f_neq_one_eq, f_x_plus, f_x_minus_7]
  simp [mk_x_vals, XVals.x_vals]
  rw [eq_comm, add_eq_zero_iff_eq_neg, ← Finsupp.single_neg]
  by_contra!
  have app_eq := DFunLike.congr (x := 13) this rfl
  repeat rw [Finsupp.single_apply] at app_eq
  norm_cast at app_eq


lemma not_equation_3050: 0 ≠ (f 0) + (f (- (f 0))) + (f (- (f 0) - f (- f 0))) + (f (- (f 0) - f (- f 0) - f (- (f 0) - f (- f 0)))) := by
  have f_neq_one_eq: f (- (mk_x_vals 0).x_vals 1) = (mk_x_vals 0).x_vals 2 := by
    sorry
  sorry



lemma not_equation_3456: f_0 ≠ f ((f_0) + f (- (f_0))) := by
  have tree_eq: ReverseTree.root (vals := (mk_x_vals 0)).left.right.getData.b = -((mk_x_vals 0).x_vals 1 + (mk_x_vals 0).x_vals 2) := by
    simp [ReverseTree.getData, mk_x_vals, newNum, XVals.x_vals]
    simp [← Finsupp.single_neg]
    rw [sub_eq_add_neg, add_comm]
    rw [← Finsupp.single_neg]

  have f_double_neg: f ((mk_x_vals 0).x_vals 1 + (mk_x_vals 0).x_vals 2) = f (-(-((mk_x_vals 0).x_vals 1 + (mk_x_vals 0).x_vals 2))) := by
    simp

  simp  [f_zero_tree, f_eval_at, f_eval_at_b]
  simp [ReverseTree.getData, newNum]
  rw [f_double_neg, ← tree_eq, f_eval_at_b]
  simp [mk_x_vals, ReverseTree.getData, newNum]
  refine Finsupp.ne_iff.mpr ?_
  use 3
  simp [XVals.x_vals]

lemma not_equation_4065: f 0 ≠ (f 0) + f (- f 0) + f ((- f 0) + f (- (f 0) - f (-f 0))) := by
  sorry

-- noncomputable def total_function (x: G): G := by
--   by_cases x_in_tree: ∃ t: ReverseTree, x = t.getData.a
--   . let t := Classical.choose x_in_tree
--     have ht:= Classical.choose_spec x_in_tree
--     exact t.getData.b
--   . exact total_function x
--     -- nonempty_denumerable_iff
