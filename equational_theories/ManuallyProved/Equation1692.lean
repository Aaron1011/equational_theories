import Mathlib
import Mathlib.Algebra.Module.Equiv.Defs

-- https://leanprover.zulipchat.com/user_uploads/3121/ASjTo5huToAvNGcg7pOGOOSy/Equation1692.pdf

-- TODO - re-enable lints
set_option linter.unusedVariables false





-- TODO -  only finitely many entries are non-zero?
abbrev G := (ℕ →₀ ℚ)

abbrev MyMod := Module ℚ (ℕ →₀ ℚ)

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
  -- NEXT STEP - tie 'i' and 'root_elem' together in some way
  -- We need to block constructing multiple XVals with different 'i' values but the same 'root_elem'
  i: ℕ
  root_elem: G
  supp_gt: ∀ n, root_elem.support.max < (basis_n (2^(i) + n*2^(i+1))).support.min
  root_neq: root_elem ∉ Set.range (fun n => basis_n (2^(i) + n*2^(i+1)))
  root_nonzero: root_elem ≠ 0
  root_indep: ∀ n, LinearIndependent ℚ ![root_elem, (basis_n (2^(i) + n*2^(i+1)))]
  -- x_basis: Set.range x_vals ⊆ Set.range basis_n

noncomputable def XVals.x_vals (vals: XVals) (n: ℕ): G := if n = 0 then vals.root_elem else basis_n (2^(vals.i) + (n-1)*2^(vals.i+1))
noncomputable def XVals.x_to_index (vals: XVals) (n: ℕ): ℕ := (2^(vals.i) + n*2^(vals.i+1))
lemma XVals.x_to_index_increasing (vals: XVals): StrictMono (XVals.x_to_index vals) :=
  by simp [XVals.x_to_index, StrictMono]
lemma XVals.x_to_index_inj (vals: XVals): Function.Injective (XVals.x_to_index vals) :=
  by simp [XVals.x_to_index, Function.Injective]
lemma XVals.x_to_index_eq (vals: XVals): ∀ n, vals.x_vals (n + 1) = basis_n (vals.x_to_index (n)) := by
  simp [XVals.x_vals, XVals.x_to_index]


lemma XVals.x_inj (vals: XVals): Function.Injective vals.x_vals := by
    simp [Function.Injective]
    intro a1 a2 funs_eq
    simp [XVals.x_vals] at funs_eq
    match ha1: a1 with
    | 0 =>
      simp at funs_eq
      match ha2: a2 with
      | 0 =>
        rfl
      | new_a2 + 1 =>
        simp at funs_eq
        have not_eq := vals.root_neq
        simp at not_eq
        specialize not_eq new_a2
        rw [eq_comm] at not_eq
        contradiction
    | new_a1 + 1 =>
      match ha2: a2 with
      | 0 =>
        simp at funs_eq
        have not_eq := vals.root_neq
        simp at not_eq
        specialize not_eq new_a1
        contradiction
      | new_a2 + 1 =>
        simp at funs_eq
        have apply_eq: (fun₀ | 2 ^ vals.i + new_a1 * 2 ^ (vals.i + 1) => (1 : ℚ)) (2 ^ (vals.i) + new_a1 * 2 ^ ((vals.i) + 1)) = (fun₀ | 2 ^ vals.i + new_a2 * 2 ^ (vals.i + 1) => 1) ((2 ^ (vals.i) + new_a1 * 2 ^ ((vals.i) + 1))) := by
          rw [funs_eq]
        simp at apply_eq
        simp [Finsupp.single_apply] at apply_eq
        rw [eq_comm] at apply_eq
        simp
        have new_a1_neq: new_a1 ≠ a1 := by
          linarith
        simp [new_a1_neq] at apply_eq
        exact apply_eq.symm

lemma XVals.x_supp_nonempty (vals: XVals): ∀ n: ℕ, (vals.x_vals n).support.Nonempty := by
  intro n
  simp [XVals.x_vals, basis_n]
  refine Finsupp.support_nonempty_iff.mpr ?_
  simp
  by_cases n_eq_zero: n = 0
  . simp [n_eq_zero]
    exact vals.root_nonzero
  . simp [n_eq_zero]

lemma XVals.x_increasing (vals: XVals): ∀ n: ℕ, ∀ m, m < n → (vals.x_vals m).support.max' (vals.x_supp_nonempty m) < (vals.x_vals n).support.min' (vals.x_supp_nonempty n) := by
  intro m n m_lt_n
  simp only [XVals.x_vals, basis_n, n_q_basis, Finsupp.coe_basisSingleOne]
  have n_supp := Finsupp.support_single_ne_zero (b := (1 : ℚ)) (2 ^ (vals.i) + (n - 1) * 2 ^ (vals.i + 1)) (by simp)
  have m_supp := Finsupp.support_single_ne_zero (b := (1 : ℚ)) (2 ^ (vals.i) + (m - 1) * 2 ^ (vals.i + 1)) (by simp)
  have m_supp_nonempty: (Finsupp.single (2 ^ vals.i + (m - 1) * 2 ^ (vals.i + 1)) (1: ℚ)).support.Nonempty := by
    simp [m_supp]
  --simp only [n_supp, m_supp]
  by_cases n_eq_zero: n = 0
  . simp only [n_eq_zero, reduceIte]
    have m_neq_zero: ¬(m = 0) := by
      linarith
    simp only [m_neq_zero, reduceIte]
    have supp_lt := vals.supp_gt (m - 1)
    simp at supp_lt
    have max_coe := Finset.coe_max' (vals.x_supp_nonempty 0)
    have m_coe := Finset.coe_min' m_supp_nonempty
    simp [XVals.x_vals] at max_coe
    rw [← max_coe, ← m_coe] at supp_lt
    apply WithBot.coe_lt_coe.mp at supp_lt
    exact supp_lt
  . simp only [n_eq_zero, reduceIte]
    have m_neq_zero: ¬(m = 0) := by
      linarith
    simp only [m_neq_zero, reduceIte]
    conv =>
      lhs
      arg 1
      rw [n_supp]
    conv =>
      rhs
      arg 1
      rw [m_supp]

    simp
    omega

-- lemma XVals.x_basis (vals: XVals): Set.range vals.x_vals ⊆ Set.range basis_n := by
--   intro x hx
--   simp at hx
--   simp
--   obtain ⟨h, hy⟩ := hx
--   use 2 ^ vals.i + h * 2 ^ (vals.i + 1)
--   simp [XVals.x_vals] at hy
--   exact hy

noncomputable def mk_x_vals (i: ℕ) (root: G): XVals := by
  exact {
    i := i,
    root_elem := root
    supp_gt := sorry
    root_neq := sorry
    root_nonzero := sorry
    root_indep := sorry
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

-- MAJOR REFACTOR : This is no longer true, and needs to exclude the root element
def mk_vals_range_s_i (i: ℕ) (root: G): Set.range (mk_x_vals i root).x_vals ⊆ (λ b => b.2) '' (s_i i) := by
  simp [mk_x_vals, s_i]
  intro x hx
  simp at hx
  simp
  obtain ⟨y, hy⟩ := hx
  use 2 ^ i + y * 2 ^ (i + 1)
  left
  refine ⟨hy, ?_⟩
  simp [Nat.ModEq]



def mk_vals_disjoint (vals1 vals2: XVals) (h_vals: vals1.i ≠ vals2.i) (h_roots: vals1.root_elem ≠ vals2.root_elem): Set.range vals1.x_vals ∩ Set.range vals2.x_vals = ∅ := by
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
| ReverseTree.root => {a := vals.root_elem, b := vals.x_vals 1}
| ReverseTree.left base => {a := -base.getData.b, b := vals.x_vals (newNum base)}
| ReverseTree.right base => {a := vals.x_vals (newNum base), b := base.getData.a - base.getData.b}

def treeDepth {vals: XVals}: @ReverseTree vals → ℕ
| ReverseTree.root => 0
| ReverseTree.left t => 1 + treeDepth t
| ReverseTree.right t => 1 + treeDepth t


--noncomputable def mkRoot: ReverseTree := ReverseTree.root
--noncomputable def mkLeft (base: ReverseTree): ReverseTree := ReverseTree.left {a := -base.getData.b, b := xSeq (newNum base)} base
--noncomputable def mkRight (base: ReverseTree): ReverseTree := ReverseTree.right {a := xSeq (newNum base), b := base.getData.a - base.getData.b} base


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

lemma newnum_neq_zero {vals: XVals} (t: @ReverseTree vals): newNum t ≠ 0 := by
  have foo := newnem_gt_one t
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
      simp [XVals.x_vals]
      simp


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
    by_cases i_eq_zero: i = 0
    . simp [XVals.x_vals, i_eq_zero]
      have root_supp := vals.supp_gt (n)
      have index_supp := Finsupp.support_single_ne_zero (b := (1 : ℚ)) (vals.x_to_index n) (by simp)
      simp [XVals.x_to_index] at index_supp
      simp [basis_n] at root_supp
      simp [index_supp] at root_supp
      have val_not_supp: 2 ^ vals.i + ↑n * 2 ^ (vals.i + 1) ∉ vals.root_elem.support := by
        exact Finset.not_mem_of_max_lt_coe root_supp
      exact Finsupp.not_mem_support_iff.mp val_not_supp
    . simp [i_eq_zero]
      have index_eq := vals.x_to_index_eq (i - 1)
      simp [XVals.x_vals, XVals.x_to_index]
      simp [i_eq_zero]
      rw [Finsupp.single_apply]
      simp
      omega

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
    by_cases i_eq_zero: i = 0
    . simp [XVals.x_vals, i_eq_zero]
      have root_supp := vals.supp_gt (n)
      have index_supp := Finsupp.support_single_ne_zero (b := (1 : ℚ)) (vals.x_to_index n) (by simp)
      simp [XVals.x_to_index] at index_supp
      simp [basis_n] at root_supp
      simp [index_supp] at root_supp
      have val_not_supp: 2 ^ vals.i + ↑n * 2 ^ (vals.i + 1) ∉ vals.root_elem.support := by
        exact Finset.not_mem_of_max_lt_coe root_supp
      exact Finsupp.not_mem_support_iff.mp val_not_supp
    . simp [i_eq_zero]
      have index_eq := vals.x_to_index_eq (i - 1)
      simp [XVals.x_vals, XVals.x_to_index]
      simp [i_eq_zero]
      rw [Finsupp.single_apply]
      simp
      omega

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

    specialize basis_indep {2 ^ vals.i, (2 ^ vals.i) + 2 ^ (vals.i + 1)} fun g => if g = 2 ^ vals.i then p else q
    have vals_neq: vals.x_vals 0 ≠ vals.x_vals 1 := by
      apply (Function.Injective.ne_iff vals.x_inj).mpr
      simp

    rw [Finset.sum_pair (by simp)] at basis_indep
    simp at basis_indep
    simp [basis_n, XVals.x_vals] at eq_zero
    have root_indep := vals.root_indep 0
    simp [LinearIndependent.pair_iff] at root_indep
    exact root_indep p q eq_zero
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

    --have x_val_basis: vals.x_vals (newNum prev) ∈ Set.range basis_n := Set.mem_of_mem_of_subset (by simp) vals.x_basis
    --obtain ⟨newnum_val, h_newnum_val⟩ := x_val_basis

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
    --simp only [vals.x_to_index_eq] at hs_t
    --simp only [basis_n] at hs_t


    simp [n_q_basis] at basis_x_val_indep
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

lemma g_enum_zero_eq_zero: g_enumerate 0 = 0 := by
  sorry

lemma g_enum_one_eq_one: g_enumerate 1 = fun₀ | 1 => 1 := by
  sorry


noncomputable def g_to_num (g: G): ℕ := by
  have nonempty_denum := (nonempty_denumerable_iff (α := G)).mpr ⟨(by infer_instance), (by infer_instance)⟩
  have bar := Classical.choice nonempty_denum
  exact bar.toEncodable.encode g

def g_num_inverse (n: ℕ): g_to_num (g_enumerate n) = n := by
  sorry

def g_enum_inverse (g: G): g_enumerate (g_to_num g) = g := by
  sorry

lemma g_num_zero_eq_zero: g_to_num 0 = 0 := by
  sorry

lemma g_num_one_eq_one: g_to_num (fun₀ | 1 => 1) = 1 := by
  sorry


def tree_to_supp {vals: XVals} (t: @ReverseTree vals): Set ℕ :=
  t.getData.a.support.toSet


--noncomputable abbrev f (g: G): G := (full_fun_from_n (g_to_num g)).tree.getData.b

-- Quotient - we want to form Submodule.span from all elements of the form 'fresh_tree_elem - (@ReverseTree.root (correct_tree)).getData.a',
-- where 'fresh_tree_elem' is an element that would make us start a new tree, 'correct_tree' is that tree, and 'a' is the 'a' value of the root of that new tree.

-- TODO - do we need to worry about duplicates here
def my_subset := {g: G | ∃ a: G, g = a - (@ReverseTree.root (mk_x_vals (g_to_num a))).getData.a ∧ ∀ vals: XVals, ∀ t: @ReverseTree vals, t.getData.a ≠ a}
noncomputable def submod := Submodule.span ℚ my_subset

-- 'opaque' speeds this up for some reason
def make_range (vals: XVals): Set (ℕ →₀ ℚ) := Set.range vals.x_vals

structure XValsIso where
  vals: XVals
  -- This maps arguments to 'f' to elements that have a left tree
  -- We apply this in the forward direction to find a tree for our 'f' argument,
  -- and in the backward direction to convert the 'tree.b' value back
  iso: G ≃ₗ[ℚ] G


structure XValsFullData where
  g: G
  vals: Set (XValsIso)
  target_val: XValsIso
  target_val_in: target_val ∈ vals
  tree: @ReverseTree target_val.vals
  tree_iso_a: tree.getData.a = target_val.iso g
  fixes_if_tree: (∃ other_vals: XVals, ∃ other_t: @ReverseTree other_vals, other_t.getData.a = g) → tree.getData.a = g
  -- BAD - we *cannot* have the isomorphism fix 'b', since 'b' could be 'parent.a - parent.b', which would
  -- mean that the isomorphism would fix 'a'
  --tree_iso_b: tree.getData.b = target_val.iso.symm ⟨tree.getData.b, b_in_range⟩
  --preserves_x_val: ∀ vals: XVals, (∃ t: @ReverseTree vals, t.getData.a = g) → target_val.vals = vals
  preserves_tree: ∀ other_vals: XVals, ∀ other_t: @ReverseTree other_vals, (other_t.getData.a = g) → tree.getData.b = other_t.getData.b ∧ tree.getData.a = other_t.getData.a


  --iso: ((Submodule.span ℚ (Set.range vals.x_vals: Set (ℕ →₀ ℚ) ))) ≃ₗ[ℚ] other_space

-- TODO - is there a cleaner way of doing this?
structure WrapperXValsFullData (g: G) where
  inner: XValsFullData
  g_eq: inner.g = g


structure PrevData (g: G) (prev_isos: Set XValsIso) where
  x_vals_iso: XValsIso
  x_vals_in: x_vals_iso ∈ prev_isos
  tree: @ReverseTree x_vals_iso.vals
  tree_in_range: tree.getData.a = x_vals_iso.iso g

noncomputable def full_x_vals_num (n: ℕ): WrapperXValsFullData (g_enumerate n) := by
  let g := g_enumerate n
  match hn: n with
  | 0 =>
    have g_vals_zero: g = (mk_x_vals 0).x_vals 0 := by
      dsimp [g]
      rw [hn]
      rw [g_enum_zero_eq_zero]
      simp [mk_x_vals, XVals.x_vals]
    let initial_vals: XValsIso := {
      vals := mk_x_vals 0,
      iso := LinearEquiv.refl _ _
    }
    exact {
        inner := {
          g := g
          vals := {initial_vals},
          target_val := initial_vals,
          target_val_in := by simp,
          tree := ReverseTree.root,
          tree_iso_a := by
            simp [initial_vals]
            simp [ReverseTree.getData]
            exact g_vals_zero.symm
          preserves_tree := by
            intro other_vals other_t data_eq
            simp [ReverseTree.getData]
            refine ⟨?_, ?_⟩
            sorry
            sorry
          fixes_if_tree := sorry
        }
        g_eq := by
          dsimp [g]
          rw [hn]
    }
  -- Note - we set up 'g_to_num' so that the first element is '(mk_x_vals 0).x_vals 0'
  | a + 1 =>
    by_cases have_tree: ∃ data: PrevData g (full_x_vals_num a).inner.vals, True
    . let prev_data := Classical.choose have_tree
      exact {
        inner := {
          g := g
          vals := (full_x_vals_num a).inner.vals,
          target_val := prev_data.x_vals_iso,
          target_val_in := by
            exact prev_data.x_vals_in
          tree := by
            exact prev_data.tree
          tree_iso_a := by
            exact prev_data.tree_in_range
          preserves_tree := by
            intro other_vals other_t data_eq
            simp
            refine ⟨?_, ?_⟩
            sorry
            sorry
          fixes_if_tree := sorry
        }
        g_eq := by
          dsimp [g]
          rw [hn]
      }
    . sorry

noncomputable def full_x_vals (g: G): WrapperXValsFullData g := by
  let bar := full_x_vals_num (g_to_num g)
  rw [g_enum_inverse] at bar
  exact bar

attribute [local instance] Classical.propDecidable

structure LatestXVals (g: G) where
  vals: Finset XVals
  distinct_i: ∀ a ∈ vals, ∀ b ∈ vals, a.i = b.i → a = b
  distinct_trees: ∀ a ∈ vals, ∀ b ∈ vals, (∃ ta: @ReverseTree a, ∃ tb: @ReverseTree b, ta.getData.a = tb.getData.a) → a = b
  cur: XVals
  cur_in_vals: cur ∈ vals
  -- FIXME - can we just delete 'preserves_i'?
  preserves_i: ∀ val ∈ vals, val.i = (vals.image XVals.i).max → (∃ t: @ReverseTree val, t.getData.a = g) → val.i = cur.i
  choose_min_i: cur.i = (({v ∈ vals | ∃ t: @ReverseTree v, t.getData.a = g} : Finset XVals).image (fun v => v.i)).min
  minimal_vals: ∀ other_vals ∈ vals, other_vals.i ≤ cur.i
  tree: @ReverseTree cur
  a_val: tree.getData.a = g
  -- new_cur_maximal: cur.i = (vals.image XVals.i).max' (by
  --   simp
  --   simp [Finset.Nonempty]
  --   use cur
  -- )
  --cur_maximal: ∀ x_vals: XVals, ∀ t: @ReverseTree x_vals, x_vals ∈ vals → t.getData.a = g → x_vals.i ≤ cur.i
  --tree_agree: ∀ other_vals: XVals, ∀ other_tree: @ReverseTree other_vals, other_tree.getData.a = g → tree.getData.b = other_tree.getData.b

lemma single_x_vals: ∀ a b: XVals, (∃ t1: @ReverseTree a, ∃ t2: @ReverseTree b, t1.getData.a = t2.getData.a) → a = b := by
  intro a b
  intro exists_data
  obtain ⟨t1, t2, h_t1_t2⟩ := exists_data
  sorry

noncomputable def latest_x_vals (n: ℕ): LatestXVals (g_enumerate n) := by
  match hn: n with
  | 0 =>
    let x_vals := mk_x_vals 0 (g_enumerate n)
    exact {
      vals := {x_vals},
      cur := x_vals,
      cur_in_vals := by simp,
      tree := ReverseTree.root,
      a_val := by
        simp only [ReverseTree.getData, x_vals, XVals.root_elem, hn]
        rw [g_enum_zero_eq_zero]
        simp only [mk_x_vals]
      choose_min_i := by
        dsimp [x_vals]
        have exists_t: ∃ t: @ReverseTree (mk_x_vals 0 (g_enumerate n)), t.getData.a = g_enumerate 0 := by
          use ReverseTree.root
          simp only [ReverseTree.getData, mk_x_vals]
          rw [hn]
        rw [Finset.filter_singleton]
        simp only [exists_t]
        simp
      minimal_vals := by simp
      distinct_i := by simp
      preserves_i := by simp
      --cur_maximal := sorry
      -- tree_agree := by
      --   intro other_vals other_tree a_eq
      --   rw [g_enum_zero_eq_zero] at a_eq
      --   simp [ReverseTree.getData]
      --   match other_tree with
      --   | .root =>
      --     simp [ReverseTree.getData, XVals.x_vals]
      --     simp [ReverseTree.getData] at a_eq
      --     sorry
      --   | .left other_tree_parent =>
      --     sorry
      --   | .right other_tree_parent =>
      --     sorry
  }
  | a + 1 =>
    let prev_x_vals := latest_x_vals a
    -- WRONG - we may need to grab a previous 'XVals' tree when looking up a node with a larger index (e.g. if 'basis_n 3' has a very high g_to_num)
    by_cases has_tree: ∃ x_vals: XVals, ∃ t: @ReverseTree x_vals, x_vals ∈ prev_x_vals.vals ∧ t.getData.a = g_enumerate n ∧ (∀ other_vals ∈ prev_x_vals.vals, other_vals.i ≤ x_vals.i) ∧ x_vals.i = (({v ∈ prev_x_vals.vals | ∃ t: @ReverseTree v, t.getData.a = (g_enumerate n)} : Finset XVals).image (fun v => v.i)).min
    . exact {
      vals := prev_x_vals.vals,
      cur := Classical.choose has_tree,
      cur_in_vals := (Classical.choose_spec (Classical.choose_spec has_tree)).1,
      tree := Classical.choose (Classical.choose_spec has_tree)
      a_val := by
        have tree_eq := (Classical.choose_spec (Classical.choose_spec has_tree)).2.1
        have n_eq: n = a  +1 := by
          simp [hn]
        rw [← n_eq]
        exact tree_eq
      minimal_vals := by
        intro other_vals
        exact (Classical.choose_spec (Classical.choose_spec has_tree)).2.2.1 other_vals
      distinct_i := prev_x_vals.distinct_i
      choose_min_i := by
        have my_spec := (Classical.choose_spec (Classical.choose_spec has_tree)).2.2.2
        have n_eq: n = a + 1 := by
          simp [hn]
        rw [← n_eq]
        exact my_spec

      preserves_i := by
        intro val h_val_prev val_i_max exists_t
        -- have additional_val: ∀ other_vals ∈ prev_x_vals.vals, other_vals.i ≤ val.i := by
        --   sorry

        have im_nonempty: (prev_x_vals.vals.image XVals.i).Nonempty := by
          simp
          simp [Finset.Nonempty]
          use val

        rw [← Finset.coe_max' im_nonempty] at val_i_max
        have val_i_max := WithBot.coe_eq_coe.mp val_i_max
        simp at val_i_max

        -- have val_i_max: val.i = (prev_x_vals.vals.image XVals.i).max' im_nonempty := by
        --   sorry

        have chose_i_in: (Classical.choose has_tree).i ∈ (prev_x_vals.vals.image XVals.i) := by
          have my_spec := (Classical.choose_spec (Classical.choose_spec has_tree)).1
          simp only [Finset.mem_image]
          use Classical.choose has_tree

        have choose_i_greatest: IsGreatest (↑(Finset.image XVals.i prev_x_vals.vals)) (Classical.choose has_tree).i := by
          simp [IsGreatest]
          refine ⟨?_, ?_⟩
          simp at chose_i_in
          apply chose_i_in
          simp [upperBounds]
          intro a ha
          have my_spec := (Classical.choose_spec (Classical.choose_spec has_tree)).2.2.1
          specialize my_spec a ha
          simp at my_spec
          exact my_spec


        have choose_max: (prev_x_vals.vals.image XVals.i).max' im_nonempty = (Classical.choose has_tree).i := by
          --simp [Finset.max', Finset.sup', Finset.sup]
          --simp


          have foo := Finset.isGreatest_max' _ im_nonempty
          exact IsGreatest.unique foo choose_i_greatest

        rw [choose_max] at val_i_max
        exact val_i_max



        -- have my_spec := prev_x_vals.preserves_i val h_val_prev


        -- have exists_t: ∃ other_t: @ReverseTree val, other_t.getData.a = g_enumerate a := by
        --   sorry
        -- have other_spec := (Classical.choose_spec (Classical.choose_spec has_tree)).2.1
        -- specialize my_spec exists_t
        -- rw [my_spec]

        -- sorry


      --cur_maximal := sorry
      -- tree_agree := by
      --   intro other_vals other_tree a_eq
      --   sorry
    }
    .
      have img_nonempty : (prev_x_vals.vals.image XVals.i).Nonempty := by
        simp [Finset.Nonempty]
        use prev_x_vals.cur.i
        use prev_x_vals.cur
        refine ⟨prev_x_vals.cur_in_vals, rfl⟩
      let max_i := (prev_x_vals.vals.image XVals.i).max' img_nonempty
      let new_x_vals := mk_x_vals (max_i + 1) (g_enumerate n)
      exact {
        vals := prev_x_vals.vals ∪ {new_x_vals},
        cur := new_x_vals,
        cur_in_vals := by simp,
        tree := ReverseTree.root,
        a_val := by
          simp only [ReverseTree.getData, new_x_vals, XVals.root_elem, hn]
          simp [mk_x_vals]
        minimal_vals := by
          intro other_vals other_vals_in
          simp at other_vals_in
          match other_vals_in with
          | .inl h_prev =>
            dsimp [new_x_vals, mk_x_vals, max_i]
            have le_max : other_vals.i ≤ (Finset.image XVals.i prev_x_vals.vals).max' img_nonempty := by
              apply Finset.le_max'
              simp
              use other_vals
            omega
          | .inr h_new =>
            rw [h_new]
        distinct_i := by
          intro a ha b hb i_eq
          simp at ha
          simp at hb
          match ha with
          | .inl a_prev =>
            match hb with
            | .inl b_prev => apply prev_x_vals.distinct_i a a_prev b b_prev i_eq
            | .inr b_new =>
              have a_le_max: a.i ≤ max_i := by
                dsimp [max_i]
                apply Finset.le_max'
                simp
                use a
              have a_lt_b: a.i < b.i := by
                rw [b_new]
                dsimp [new_x_vals, mk_x_vals]
                omega
              rw [i_eq] at a_lt_b
              -- obtains a contradiction
              simp at a_lt_b
          | .inr a_new =>
            match hb with
            | .inl b_prev =>
              -- TODO - this is identical to the other case, just with variables swapped around
                have b_le_max: b.i ≤ max_i := by
                  dsimp [max_i]
                  apply Finset.le_max'
                  simp
                  use b
                have b_lt_a: b.i < a.i := by
                  rw [a_new]
                  dsimp [new_x_vals, mk_x_vals]
                  omega
                rw [i_eq] at b_lt_a
                -- obtains a contradiction
                simp at b_lt_a
            | .inr b_new => rw [a_new, b_new]
        preserves_i := by
          sorry
        choose_min_i := by
          conv =>
            rhs
            arg 1
            arg 2
            rw [Finset.filter_congr (q := fun v => v = new_x_vals)]
            rfl
            tactic =>
              intro x
              simp only [Finset.mem_union, Finset.mem_singleton, Option.some.injEq, iff_false]
              intro hx
              refine ⟨?_, ?_⟩
              . intro new_has_tree
                match hx with
                | .inl x_in_prev =>
                  have prev_choose_min := prev_x_vals.choose_min_i
                  -- have x_i_le: (Finset.image (fun v ↦ v.i) (Finset.filter (fun v ↦ ∃ t: @ReverseTree v, t.getData.a = g_enumerate a) prev_x_vals.vals)).min ≤ x.i := by
                  --   apply Finset.min_le
                  --   simp only [Option.some.injEq,
                  --     Nat.cast_id, Finset.mem_image, Finset.mem_filter]
                  --   use prev_x_vals.cur
                  --   sorry


                    --refine ⟨⟨x_in_prev, ?_⟩, ?_⟩
                   -- use prev_x_vals.tree


                  dsimp [new_x_vals]
                  have prex_vals_a := prev_x_vals.a_val
                  have prev_minimal := prev_x_vals.minimal_vals
                  obtain ⟨x_tree, h_x_tree⟩ := new_has_tree
                  have actually_has_tree: ∃ x_vals: XVals, ∃ t: @ReverseTree x_vals, x_vals ∈ prev_x_vals.vals ∧ t.getData.a = g_enumerate n ∧ (∀ other_vals ∈ prev_x_vals.vals, other_vals.i ≤ x_vals.i) ∧ x_vals.i = (({v ∈ prev_x_vals.vals | ∃ t: @ReverseTree v, t.getData.a = (g_enumerate n)} : Finset XVals).image (fun v => v.i)).min := by
                    use x
                    use x_tree
                    refine ⟨x_in_prev, ?_, ?_, ?_⟩
                    .
                      simp only [hn]
                      exact h_x_tree
                    .
                      intro other_vals h_other_vals
                      specialize prev_minimal other_vals h_other_vals
                      have x_i_ge: other_vals.i ≤ x.i := by
                        sorry
                      omega
                    .
                      sorry
                  contradiction
                | .inr x_eq_new => exact x_eq_new
              . intro x_eq_new
                use ReverseTree.root
                simp only [ReverseTree.getData]
                rw [x_eq_new]
                simp only [new_x_vals, mk_x_vals]
                rw [hn]
          --rw [Finset.filter_union]
          --simp [Finset.filter_singleton]
          simp [Finset.filter_eq' (prev_x_vals.vals ∪ {new_x_vals}) new_x_vals]
        --cur_maximal := sorry
        -- tree_agree := by
        --   intro other_vals other_tree a_eq
        --   sorry
      }

-- lemma latest_vals_minimal (a b: ℕ) (ha: a < b) (t: @ReverseTree (latest_x_vals a).cur) : t.getData.a ≠ (latest_x_vals b).tree.getData.a := by
--   induction b with
--   | zero =>
--     contradiction
--   | succ b h_prev =>
--     -- by_cases a_lt_b: a < b
--     -- .
--     --   have not_tree : ¬ ∃ x_vals: XVals, ∃ new_t: @ReverseTree x_vals, x_vals ∈ (latest_x_vals b).vals ∧ new_t.getData.a = g_enumerate (b + 1) := by
--     --     by_contra!
--     --     obtain ⟨x_vals, new_t, x_vals_in, new_t_a⟩ := this
--     --     specialize h_prev a_lt_b

--     -- . sorry

--     have a_eq := (latest_x_vals (b + 1)).a_val
--     by_cases has_tree: ∃ x_vals: XVals, ∃ new_t: @ReverseTree x_vals, x_vals ∈ (latest_x_vals b).vals ∧ new_t.getData.a = g_enumerate (b + 1)
--     .
--       simp [latest_x_vals]
--       rw [dite_cond_eq_true]
--       .
--         simp [ReverseTree.getData]
--         sorry
--       . simp only [eq_iff_iff, iff_true]
--         exact has_tree

--     . sorry
-- structure FAndData (g: G) where
--   t: @ReverseTree (full_x_vals g).target_val.vals
--   preserves_tree: (∃ vals: XVals, ∃ other_t: @ReverseTree vals, other_t.getData.a = g) → t.getData.a = g

--set_option maxHeartbeats 5000000
--set_option maxRecDepth 5000000

lemma latest_x_vals_succ (n: ℕ): (latest_x_vals n).vals ⊆ (latest_x_vals (n + 1)).vals := by
  induction n with
  | zero =>
    rw [latest_x_vals]
    simp [g_enum_zero_eq_zero]
    rw [latest_x_vals]
    --simp
    by_cases has_tree: ∃ x_vals: XVals, ∃ new_t: @ReverseTree x_vals, x_vals.i < 1 ∧ new_t.getData.a = g_enumerate 1
    .
      simp only [latest_x_vals]
      simp [g_enum_zero_eq_zero]
      rw [dite_cond_eq_true]
      --simp
      simp only [eq_iff_iff, iff_true]
      exact has_tree
    .
      simp only [latest_x_vals]
      simp [g_enum_zero_eq_zero]
      rw [dite_cond_eq_false]
      --simp
      simp only [eq_iff_iff, iff_false]
      exact has_tree
  | succ new_n h_prev =>
    nth_rw 2 [latest_x_vals]
    by_cases has_tree: ∃ x_vals: XVals, ∃ new_t: @ReverseTree x_vals, x_vals.i < new_n + 1 + 1 ∧ new_t.getData.a = g_enumerate (new_n + 1 + 1)
    .
      rw [dite_cond_eq_true]
      simp only [Nat.succ_eq_add_one, Option.some.injEq,
        eq_iff_iff, iff_true]
      exact has_tree
    . rw [dite_cond_eq_false]
      simp only [Nat.succ_eq_add_one, Option.some.injEq,
        eq_iff_iff, iff_true, iff_false]
      --simp
      simp only [Nat.succ_eq_add_one, Option.some.injEq,
        eq_iff_iff, iff_false]
      exact has_tree


lemma latest_x_vals_set (a b: ℕ) (hab: a ≤ b): (latest_x_vals a).vals ⊆ (latest_x_vals b).vals := by
  induction b with
  | zero =>
    have a_eq_zero: a = 0 := by
      omega
    rw [a_eq_zero]
  | succ new_b h_prev =>
    by_cases a_le_new_b: a ≤ new_b
    .
      specialize h_prev a_le_new_b
      have new_b_subset := latest_x_vals_succ new_b
      exact fun ⦃a_1⦄ a ↦ new_b_subset (h_prev a)
    . have a_eq_b_plus: a = new_b + 1 := by
        omega
      rw [a_eq_b_plus]


-- This is FALSE with the correct definition of 'latest_x_vals' - the 'cur' tree may jump
-- around in the set of XVals
lemma latest_x_vals_succ_i (n: ℕ): (latest_x_vals n).cur.i ≤ (latest_x_vals (n + 1)).cur.i := by
  have vals_in_self := (latest_x_vals n).cur_in_vals
  have vals_in := (latest_x_vals_set n (n + 1) (by omega)) (latest_x_vals n).cur_in_vals
  have foo := (latest_x_vals (n + 1)).minimal_vals ⟨(latest_x_vals n).cur, vals_in⟩
  simp at foo
  exact foo

lemma latest_x_vals_i_monotone: Monotone (fun n => (latest_x_vals n).cur.i) := by
  apply monotone_nat_of_le_succ latest_x_vals_succ_i

noncomputable def f (g: G): G := (latest_x_vals (g_to_num g)).tree.getData.b


-- TODO - what exactly is the interpretation of this lemma, and why can't lean figure it our for us?
lemma cast_data_eq {vals1 vals2: XVals} (t: @ReverseTree vals1) (h_vals: vals1 = vals2) (hv: @ReverseTree vals1 = @ReverseTree vals2): t.getData = (cast hv t).getData := by
  congr
  rw [heq_comm]
  simp

-- lemma latest_x_vals_preserves_cur {vals: XVals} (a b: ℕ) (hb: a ≤ b) (hvals: vals ∈ (latest_x_vals a).vals): (latest_x_vals b).cur = vals := by
--   induction b with
--   | zero =>
--     have a_eq_zero: a = 0 := by
--       omega
--     simp only [latest_x_vals]
--     rw [a_eq_zero] at hvals
--     simp only [latest_x_vals] at hvals
--     simp only [Finset.mem_singleton] at hvals
--     exact hvals.symm
--   | succ new_b h_prev =>
--     have vals_set


lemma latest_x_vals_i_eq {other_vals: XVals} (t: @ReverseTree other_vals) {n: ℕ} (hvals: (latest_x_vals n).cur = other_vals): (latest_x_vals (g_to_num t.getData.a)).cur.i = other_vals.i := by
  by_contra!
  by_cases t_i_lt: (latest_x_vals (g_to_num t.getData.a)).cur.i < other_vals.i
  .
    simp [← hvals] at t_i_lt
    have args_lt := Monotone.reflect_lt latest_x_vals_i_monotone t_i_lt
    have min_val := (latest_x_vals (n)).choose_min_i

    --have other_vals_in := latest_x_vals_set _ _ (le_of_lt args_lt)
    have other_vals_self := (latest_x_vals n).cur_in_vals
    simp [hvals] at other_vals_self
    --specialize other_vals_in other_vals_self

    --have m_cur_in := (latest_x_vals m).cur_in_vals
    --specialize other_vals_in m_cur_in
    --rw [m_in.2] at other_vals_in

    have cast_trees := cast_data_eq (latest_x_vals n).tree hvals
    have types_eq: @ReverseTree (latest_x_vals n).cur = @ReverseTree other_vals := by
      simp [hvals]
    have trees_eq := cast_data_eq t hvals.symm types_eq.symm

    have t_data_num_le: ((latest_x_vals (n)).cur.i : WithTop ℕ) ≤ ((latest_x_vals (g_to_num t.getData.a)).cur.i : WithTop ℕ) := by
      rw [min_val]
      apply Finset.min_le
      simp only [Finset.mem_image, Finset.mem_filter]
      use (latest_x_vals n).cur
      simp only [hvals]
      refine ⟨⟨other_vals_self, ?_⟩, ?_⟩
      use (latest_x_vals n).tree
      have a_eq := (latest_x_vals n).a_val
      exact a_eq

    simp at t_data_num_le
    omega
  .
    simp at t_i_lt
    have other_i_lt: other_vals.i < (latest_x_vals (g_to_num t.getData.a)).cur.i := by omega
    have orig_other_i_lt := other_i_lt
    clear t_i_lt
    simp [← hvals] at other_i_lt
    have args_lt := Monotone.reflect_lt latest_x_vals_i_monotone other_i_lt

    have min_val := (latest_x_vals (g_to_num t.getData.a)).choose_min_i

    have other_vals_in := latest_x_vals_set _ _ (le_of_lt args_lt)
    have other_vals_self := (latest_x_vals n).cur_in_vals
    specialize other_vals_in other_vals_self
    --have m_cur_in := (latest_x_vals m).cur_in_vals
    --specialize other_vals_in m_cur_in
    --rw [m_in.2] at other_vals_in

    have cast_trees := cast_data_eq (latest_x_vals n).tree hvals
    have types_eq: @ReverseTree (latest_x_vals n).cur = @ReverseTree other_vals := by
      simp [hvals]
    have trees_eq := cast_data_eq t hvals.symm types_eq.symm

    have t_data_num_le: ((latest_x_vals (g_to_num t.getData.a)).cur.i : WithTop ℕ) ≤ ((latest_x_vals (n)).cur.i : WithTop ℕ) := by
      rw [min_val]
      apply Finset.min_le
      simp only [Finset.mem_image, Finset.mem_filter]
      use (latest_x_vals n).cur
      refine ⟨⟨other_vals_in, ?_⟩, ?_⟩
      use (cast types_eq.symm t)
      rw [← trees_eq]
      rw [g_enum_inverse]
      simp

    simp at t_data_num_le
    omega



-- NEXT STEP - do we need some kind of minimality assumption on 'n'?
-- The output of 'latest_x_vals' could have a smaller 'i'
lemma new_eval_left {other_vals: XVals} (t: @ReverseTree other_vals) {n: ℕ} (hvals: (latest_x_vals n).cur = other_vals): f t.getData.a = t.getData.b := by
  simp [f]
  have a_eq := (latest_x_vals (g_to_num t.getData.a)).a_val
  have out_num_eq:  (latest_x_vals (g_to_num t.getData.a)).cur.i = other_vals.i := by
    apply latest_x_vals_i_eq (n := n)
    exact hvals

  have root_elem_eq: (latest_x_vals (g_to_num t.getData.a)).cur.root_elem = other_vals.root_elem := by
    by_contra!
    by_cases n_le_num: n ≤ g_to_num t.getData.a
    .
      have vals_in := latest_x_vals_set n (g_to_num t.getData.a) n_le_num
      have t_num_self := (latest_x_vals (g_to_num t.getData.a)).cur_in_vals
      have n_self := (latest_x_vals n).cur_in_vals
      specialize vals_in n_self
      simp [← hvals] at out_num_eq
      have vals_distinct := (latest_x_vals (g_to_num t.getData.a)).distinct_i (latest_x_vals n).cur vals_in (latest_x_vals (g_to_num t.getData.a)).cur t_num_self out_num_eq.symm
      rw [← vals_distinct] at this
      rw [hvals] at this
      contradiction
    .
      simp at n_le_num
      have n_le_num : g_to_num t.getData.a ≤ n := by linarith
      -- TODO - deduplicate this
      have vals_in := latest_x_vals_set  (g_to_num t.getData.a) n n_le_num
      have t_num_self := (latest_x_vals (g_to_num t.getData.a)).cur_in_vals
      have n_self := (latest_x_vals n).cur_in_vals
      specialize vals_in t_num_self
      simp [← hvals] at out_num_eq
      have vals_distinct := (latest_x_vals (n)).distinct_i (latest_x_vals n).cur n_self (latest_x_vals (g_to_num t.getData.a)).cur vals_in out_num_eq.symm
      rw [← vals_distinct] at this
      rw [hvals] at this
      contradiction

  -- TODO - this all seems ridiculous. Can we somehow eliminate all of this nonsense (except for 'temp_partial_function')
  have cast_trees := cast_data_eq (latest_x_vals (g_to_num t.getData.a)).tree x_vals_eq
  have types_eq: @ReverseTree (latest_x_vals (g_to_num t.getData.a)).cur = @ReverseTree other_vals := by
    simp [x_vals_eq]
  have trees_eq := cast_data_eq t x_vals_eq.symm types_eq.symm
  have orig_trees_eq := trees_eq

  have better_x_vals_eq: (latest_x_vals (g_to_num t.getData.a)).cur = other_vals := by
    by_cases n_le_num: n ≤ g_to_num t.getData.a
    . have vals_subset := latest_x_vals_set n (g_to_num t.getData.a) n_le_num
      have t_num_self := (latest_x_vals (g_to_num t.getData.a)).cur_in_vals
      have n_self := (latest_x_vals n).cur_in_vals
      specialize vals_subset n_self
      have same_tree: ∃ ta: @ReverseTree (latest_x_vals n).cur, ∃ tb: @ReverseTree (latest_x_vals (g_to_num t.getData.a)).cur, ta.getData.a = tb.getData.a := by
        use t

      have x_vals_eq := (latest_x_vals (g_to_num t.getData.a)).distinct_trees (latest_x_vals n).cur vals_subset (latest_x_vals (g_to_num t.getData.a)).cur t_num_self same_tree
      rw [hvals] at x_vals_eq
      exact x_vals_eq.symm


  have x_vals_eq: (latest_x_vals (g_to_num t.getData.a)).cur = other_vals := by
    calc
      (latest_x_vals (g_to_num t.getData.a)).cur = {
        i := (latest_x_vals (g_to_num t.getData.a)).cur.i
        root_elem := (latest_x_vals (g_to_num t.getData.a)).cur.root_elem
        supp_gt := (latest_x_vals (g_to_num t.getData.a)).cur.supp_gt
        root_neq := (latest_x_vals (g_to_num t.getData.a)).cur.root_neq
        root_nonzero := (latest_x_vals (g_to_num t.getData.a)).cur.root_nonzero
        root_indep := (latest_x_vals (g_to_num t.getData.a)).cur.root_indep
      } := rfl
      _ = {
        i := other_vals.i
        root_elem := other_vals.root_elem
        supp_gt := other_vals.supp_gt
        root_neq := other_vals.root_neq
        root_nonzero := other_vals.root_nonzero
        root_indep := other_vals.root_indep
      } := by
        simp only [out_num_eq, root_elem_eq]
      _ = other_vals := rfl


  simp [g_enum_inverse] at a_eq

  apply_fun (fun x => TreeData.a x) at trees_eq
  simp [← a_eq] at trees_eq
  have partial_fun_trees := temp_partial_function trees_eq
  rw [partial_fun_trees]
  rw [← orig_trees_eq]







lemma f_b_preserved {vals: XVals} (t: @ReverseTree vals): t.getData.b = (full_x_vals t.getData.a).inner.tree.getData.b := by
  have preserved_tree := (full_x_vals t.getData.a).inner.preserves_tree vals t
  simp [ (full_x_vals t.getData.a).g_eq] at preserved_tree
  rw [preserved_tree.1]

--lemma f_b_in {vals: XVals} (t: @ReverseTree vals): t.getData.b ∈ Submodule.span ℚ (make_range (full_x_vals t.getData.a).inner.target_val.vals) := by
--  have b_in := (full_x_vals t.getData.a).inner.b_in_range
--  rwa [← f_b_preserved t] at b_in



  -- have preserves_tree := (full_x_vals t.getData.a).inner.preserves_tree vals t
  -- simp [(full_x_vals t.getData.a).g_eq] at preserves_tree
  -- obtain ⟨preserves_b, preserves_a⟩ := preserves_tree
  -- conv =>
  --   lhs
  --   --simp [preserves_tree]

  -- have iso_b := (full_x_vals t.getData.a).inner.tree_iso_b
  -- simp [← iso_b]


  -- have a_iso := (full_x_vals t.getData.a).inner.tree_iso_a

  -- conv =>
  --   lhs
  --   rw [preserves_b]



  -- have x_vals_eq := (full_x_vals t.getData.a)..preserves_x_val (vals) ⟨t, rfl⟩
  -- have cast_trees := cast_data_eq (full_x_vals t.getData.a).tree x_vals_eq
  -- have types_eq: @ReverseTree (full_x_vals t.getData.a).target_val.vals = @ReverseTree vals := by
  --   simp [x_vals_eq]
  -- have trees_eq := cast_data_eq t x_vals_eq.symm types_eq.symm
  -- rw [trees_eq]
  -- apply_fun (fun x => TreeData.a x) at trees_eq
  -- have trees_eq := temp_partial_function trees_eq

  -- have bar := (full_x_vals t.getData.a).preserves_tree ⟨cast types_eq.symm t, by
  --   rw [← trees_eq]
  -- ⟩

  --have trees_eq := temp_partial_function ((full_x_vals (g_to_num t.getData.a)).target_val.vals)




  -- match n with
  -- | 0 => exact {
  --       vals := {
  --         {
  --           vals := mk_x_vals 0,
  --           contains_n := b7
  --         }
  --       },
  --       contains_n := by
  --         use mk_x_vals 0
  --         use ReverseTree.root
  --         simp [g_enum_zero_eq_one]
  --         simp [ReverseTree.getData, mk_x_vals, XVals.x_vals]
  --     }
  -- | n + 1 =>
  --   let prev_x_vals := full_x_vals n
  --   by_cases exists_tree: ∃ x_vals: XVals, ∃ t: @ReverseTree x_vals, x_vals ∈ prev_x_vals.vals ∧ t.getData.a = (g_enumerate (n + 1))
  --   . exact {
  --       vals := prev_x_vals.vals,
  --       from_mk := prev_x_vals.from_mk,
  --       contains_n := exists_tree
  --     }
  --     -- TODO - build new tree
  --   .

  --     have candidate_val: ∃ new_vals: XVals, ∃ t :@ReverseTree new_vals, t.getData.a = (g_enumerate (n + 1)) := by
  --       sorry
  --     let x_vals_to_supp := (λ new_x_vals : XVals => (tree_to_supp '' Set.univ (α := @ReverseTree new_x_vals)).sUnion)
  --     have all_prev_supps := (x_vals_to_supp '' prev_x_vals.vals).sUnion
  --     have s_i_without: ∃ i, ((g_enumerate n).support.toSet ∪ all_prev_supps) ∩ ((λ s => s.2.support.toSet) '' (s_i i)).sUnion = ∅ := by
  --       by_contra!
  --       sorry
  --     have i := Classical.choose s_i_without
  --     let new_x_vals  := mk_x_vals i
  --     exact  {
  --       vals := prev_x_vals.vals ∪ {new_x_vals},
  --       from_mk := by
  --         simp
  --         exact prev_x_vals.from_mk
  --       contains_n := by
  --         use mk_x_vals i
  --         sorry


  --     }


#check G ⧸ submod

structure GAndProof (n: ℕ) where
  x_vals: XVals
  tree: @ReverseTree x_vals
  --proof: tree.getData.a = (g_enumerate n)
  new_proof: ∀ t: @ReverseTree x_vals, t.getData.a = (g_enumerate n) → t = tree
  --zero_if_zero: n = 0 → x_vals = mk_x_vals 0
  preserved_val: ∀ vals: XVals, (∃ t: @ReverseTree vals, t.getData.a = (g_enumerate n)) → x_vals = vals
  in_quot : ∃ t: @ReverseTree x_vals, (Submodule.Quotient.mk (p := submod) t.getData.a) = Submodule.Quotient.mk (g_enumerate n)
  better_in_quot: (Submodule.Quotient.mk (p := submod) tree.getData.a) = Submodule.Quotient.mk (g_enumerate n)

lemma neq_implies_neq_i {vals1 vals2: XVals} (h_vals: vals1 ≠ vals2): vals1.i ≠ vals2.i := by
  by_contra! vals_eq
  have vals_destructure: vals1 = { i := vals1.i} := by
    simp
  have choose_destructure: vals2 = { i := vals2.i} := by
    simp
  rw [vals_eq] at vals_destructure
  rw [← choose_destructure] at vals_destructure
  contradiction

-- Maps the nth element of G by applying our construced function 'f'
noncomputable def full_fun_from_n (n: ℕ): GAndProof n := by
  by_cases n_tree_left: ∃ x_vals: XVals, ∃ t: @ReverseTree x_vals, t.getData.a = (g_enumerate n)
  .
    exact {
      x_vals := Classical.choose n_tree_left,
      tree := Classical.choose (Classical.choose_spec n_tree_left),
      in_quot := by
        use Classical.choose (Classical.choose_spec n_tree_left)
        rw [Classical.choose_spec (Classical.choose_spec n_tree_left)]
      better_in_quot := by
        rw [Classical.choose_spec (Classical.choose_spec n_tree_left)]
      -- proof := Classical.choose_spec (Classical.choose_spec n_tree_left),
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
  . exact {
      x_vals := mk_x_vals n,
      tree := ReverseTree.root,
      new_proof := by
        intro t
        rw [not_exists] at n_tree_left
        specialize n_tree_left (mk_x_vals n)
        rw [not_exists] at n_tree_left
        specialize n_tree_left t
        simp [n_tree_left]
      preserved_val := by
        intro vals
        simp [not_exists] at n_tree_left
        specialize n_tree_left vals
        rw [← not_exists] at n_tree_left
        simp [n_tree_left]
      in_quot := by
        use @ReverseTree.root (mk_x_vals n)
        rw [eq_comm]
        simp only [ReverseTree.getData]
        refine (Submodule.Quotient.eq submod).mpr ?_
        have span_subset := Submodule.subset_span (R := ℚ) (s := my_subset)
        have diff_in_subset: (g_enumerate n - (@ReverseTree.root (mk_x_vals n)).getData.a) ∈ my_subset := by
          simp only [my_subset, ne_eq, Option.some.injEq, Set.mem_setOf_eq]
          use g_enumerate n
          refine ⟨by (simp [ReverseTree.getData, g_num_inverse]), ?_⟩
          intro vals t
          rw [not_exists] at n_tree_left
          specialize n_tree_left vals
          rw [not_exists] at n_tree_left
          specialize n_tree_left t
          exact n_tree_left
        simp only [submod]
        exact span_subset diff_in_subset
      -- TODO - deduplicate this or remove 'in_quot'
      better_in_quot := by
        rw [eq_comm]
        simp only [ReverseTree.getData]
        refine (Submodule.Quotient.eq submod).mpr ?_
        have span_subset := Submodule.subset_span (R := ℚ) (s := my_subset)
        have diff_in_subset: (g_enumerate n - (@ReverseTree.root (mk_x_vals n)).getData.a) ∈ my_subset := by
          simp only [my_subset, ne_eq, Option.some.injEq, Set.mem_setOf_eq]
          use g_enumerate n
          refine ⟨by (simp [ReverseTree.getData, g_num_inverse]), ?_⟩
          intro vals t
          rw [not_exists] at n_tree_left
          specialize n_tree_left vals
          rw [not_exists] at n_tree_left
          specialize n_tree_left t
          exact n_tree_left
        simp only [submod]
        exact span_subset diff_in_subset
  }


#synth Module ℚ G

abbrev G' := G ⧸ submod


  -- The 'g_to_num' values of all elements in the quotient equivalene class of 't.getData.a'
  -- have nums_related := {n: ℕ | ∃ a: G, g_to_num a = n ∧ (Submodule.Quotient.mk (p := submod) a) = g}
  -- let min_num := sInf nums_related
  -- exact Submodule.Quotient.mk (full_fun_from_n min_num).tree.getData.b

  -- TODO - is there a better way to do this?
  --have eq_mk_repr := Submodule.Quotient.mk_surjective submod g
  --let g_repr := Classical.choose eq_mk_repr
  --exact Submodule.Quotient.mk ((full_fun_from_n (g_to_num g_repr)).tree.getData.b)

  -- by_cases has_tree: ∃ t: @ReverseTree (full_fun_from_n (g_to_num g_repr)).x_vals, t.getData.a = g_repr
  -- . exact Submodule.Quotient.mk ((full_fun_from_n (g_to_num g_repr)).tree.getData.b)
  -- . --FINAL TODO: What x_vals should we actually use here?
  --   exact Submodule.Quotient.mk ((@ReverseTree.root (mk_x_vals (g_to_num g_repr))).getData.b)
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



lemma f_eval_at {vals: XVals} (t: @ReverseTree vals): f (Submodule.Quotient.mk t.getData.a) = (Submodule.Quotient.mk t.getData.b) := by
  simp [f]

  let my_set := {n | ∃ a, g_to_num a = n ∧ Submodule.Quotient.mk a = Submodule.Quotient.mk (p := submod) t.getData.a}
  have g_num_in: (g_to_num t.getData.a) ∈ my_set := by
    simp [my_set, Set.Nonempty]
    use t.getData.a

  have my_set_nonempty : my_set.Nonempty := by
    exact Set.nonempty_of_mem g_num_in

  let my_val := (sInf my_set)
  have sinf_in := Nat.sInf_mem my_set_nonempty
  simp only [my_set] at sinf_in
  rw [Set.mem_setOf_eq] at sinf_in
  obtain ⟨a, h_num, h_eq⟩ := sinf_in



  have sinf_eq_num: sInf my_set = (g_to_num) t.getData.a := by
    by_contra!
    have sinf_le_num: sInf my_set ≤ (g_to_num) t.getData.a := by
      exact Nat.sInf_le g_num_in
    have sinf_lt: sInf my_set < (g_to_num) t.getData.a := by
      omega
    simp [my_set] at sinf_lt






  have eq_my_val: (Submodule.Quotient.mk (p := submod) (g_enumerate my_val)) = Submodule.Quotient.mk t.getData.a := by
    rw [← h_eq]
    simp only [my_val, my_set]
    rw [← h_num]
    rw [g_enum_inverse]

  have eq_t_a : (full_fun_from_n (sInf {n | ∃ a, g_to_num a = n ∧ Submodule.Quotient.mk a = Submodule.Quotient.mk (p := submod) t.getData.a})).tree.getData.a = t.getData.a := by
    sorry

  have preserved := x_vals_preserved t
  have types_eq: @ReverseTree (full_fun_from_n (g_to_num t.getData.a)).x_vals = @ReverseTree vals := by
    simp [preserved]

  have orig_new_proof := (full_fun_from_n (g_to_num t.getData.a)).new_proof
  have new_proof := (full_fun_from_n (g_to_num t.getData.a)).new_proof (cast types_eq.symm t)
  have my_cast_data := cast_data_eq t preserved.symm types_eq.symm

  have choose_spec := Classical.choose_spec (Submodule.Quotient.mk_surjective submod (Submodule.Quotient.mk t.getData.a))
  let val := Classical.choose (Submodule.Quotient.mk_surjective submod (Submodule.Quotient.mk t.getData.a))
  have other_quot_eq: Submodule.Quotient.mk (t.getData.a) = Submodule.Quotient.mk (p := submod)  val := by
    simp [val]
    exact id (Eq.symm choose_spec)


  -- have quot_singleton: ∀ other_t, (Submodule.Quotient.mk t.getData.a) = (Submodule.Quotient.mk (p := submod) other_t.getData.a) → t = other_t := by
  --   intro other_t quot_eq
  --   have diff_in := Submodule.Quotient.eq submod (x := (t.getData.a)) (y := other_t.getData.a)
  --   apply diff_in.mp at quot_eq
  --   simp [submod] at quot_eq
  --   have span_subset := Submodule.subset_span (R := ℚ) (s := my_subset)

  --   have diff_not_in_subset: t.getData.a - other_t.getData.a ∉ my_subset := by
  --     simp only [my_subset]
  --     rw [Set.mem_setOf_eq]
  --     rw [not_exists]
  --     intro a
  --     simp
  --     intro h_eq
  --     use vals
  --     use t
  --     simp [ReverseTree.getData] at h_eq





  have in_quot := (full_fun_from_n (g_to_num t.getData.a)).better_in_quot
  simp [g_enum_inverse] at in_quot
  simp [g_enum_inverse, my_cast_data] at new_proof
  rw [← new_proof] at in_quot

  rw [← new_proof]

  rw [← my_cast_data]

-- lemma f_eval_at_b {vals: XVals} (t: @ReverseTree vals): f (-t.getData.b) = (full_x_vals (-t.getData.b)).inner.target_val.iso.symm ⟨t.left.getData.b, f_b_in t⟩  := by
--   have t_left_a_eq: -t.getData.b = t.left.getData.a := by
--     simp [ReverseTree.getData]
--   rw [t_left_a_eq]
--   rw [new_f_eval_at t.left]

  -- suppose f(g) = g + g
  -- -f(g)= -g - g
  -- f(-f(g))= (-g - g) + (-g - g) = -4g
  -- f(f(-f(g))) = -4g + -4g = -8g

-- noncomputable instance subtypeNeg (S: Submodule ℚ (ℕ →₀ ℚ)) : Neg (Subtype fun p => p ∈ S) where
--   neg x := ⟨-x.val, by simp⟩

-- lemma subtype_neg_eq {S: Submodule ℚ (ℕ →₀ ℚ)} {x: S}: -x = ⟨-x.val, by simp⟩ := by
--   rfl

lemma temp_new_eval_left {vals: XVals} (t: @ReverseTree vals): f (t.getData.a) = t.getData.b := by
  simp [f]
  have a_eq := (latest_x_vals (g_to_num t.getData.a)).a_val
  simp [g_enum_inverse] at a_eq
  have same_vals: (latest_x_vals (g_to_num t.getData.a)).cur = vals := by
    by_contra!
    have i_or_root_neq: (latest_x_vals (g_to_num t.getData.a)).cur.i ≠ vals.i ∨ (latest_x_vals (g_to_num t.getData.a)).cur ≠ vals := by
      by_contra both_eq
      simp at both_eq
      -- TODO - can this be simplified?
      have vals_eq: (latest_x_vals (g_to_num t.getData.a)).cur = vals := by
        calc
          (latest_x_vals (g_to_num t.getData.a)).cur = {
            i := (latest_x_vals (g_to_num t.getData.a)).cur.i
            root_elem := (latest_x_vals (g_to_num t.getData.a)).cur.root_elem
            supp_gt := (latest_x_vals (g_to_num t.getData.a)).cur.supp_gt
            root_neq := (latest_x_vals (g_to_num t.getData.a)).cur.root_neq
            root_nonzero := (latest_x_vals (g_to_num t.getData.a)).cur.root_nonzero
            root_indep := (latest_x_vals (g_to_num t.getData.a)).cur.root_indep
          } := rfl
          _ = {
            i := vals.i
            root_elem := vals.root_elem
            supp_gt := vals.supp_gt
            root_neq := vals.root_neq
            root_nonzero := vals.root_nonzero
            root_indep := vals.root_indep
          } := by
            simp only [both_eq.1]
            simp only [both_eq.2]
          _ = vals := rfl
      contradiction
    match i_or_root_neq with
    | .inl i_neq =>
      match t with
      | .root =>
        simp [ReverseTree.getData] at a_eq

      sorry
    | .inr root_neq =>
      sorry



  have tree_same := (latest_x_vals (g_to_num t.getData.a)).a_val

  sorry

lemma f_functional_eq (g: G): f (f (- f g)) = g - (f g) := by
  let g_data := latest_x_vals (g_to_num g)
  have neg_eq_left: - f g = (latest_x_vals (g_to_num g)).tree.left.getData.a := by
    simp [f]
    simp [ReverseTree.getData]
  have eval_neg := new_eval_left (latest_x_vals (g_to_num g)).tree.left (other_vals := (latest_x_vals (g_to_num g)).cur) (n := g_to_num g) rfl
  rw [neg_eq_left]
  rw [eval_neg]

  have left_eq_right_a: (latest_x_vals (g_to_num g)).tree.left.getData.b = (latest_x_vals (g_to_num g)).tree.right.getData.a := by
    simp [ReverseTree.getData]

  have eval_right := new_eval_left (latest_x_vals (g_to_num g)).tree.right (other_vals := (latest_x_vals (g_to_num g)).cur) (n := g_to_num g) rfl
  rw [left_eq_right_a]
  rw [eval_right]
  simp [ReverseTree.getData, f]
  have g_eq := g_data.a_val
  simp only [g_data] at g_eq
  rw [g_eq]
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
  have other_equiv := second_equiv f f_functional_eq x y
  rw [← other_equiv]


noncomputable abbrev f_0 := f (g_enumerate 0)

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




-- structure MyInner where
--   data: ℕ
--   with_prop: 1 = 1

-- inductive Outer {a: MyInner} where
-- | root: Outer
-- | other: Outer → Outer

-- lemma cast_outer (a_1 a_2: MyInner) (outer_a: @Outer a_1) (outer_b: @Outer a_2) (h_a_eq: a_1 = a_2): True := by
--   have first_eq: ∃ b, b = outer_b := by
--     use outer_b
--   have types_eq: @Outer a_1 = @Outer a_2 := by
--     rw [h_a_eq]
--   subst types_eq
--   have other_eq: ∃ b: @Outer a_1, b = outer_b := by
--     sorry


lemma neg_f_zero: - f (0) = (latest_x_vals 0).tree.left.getData.a := by
  simp [f]
  simp [ReverseTree.getData]
  simp only [latest_x_vals]
  rw [g_num_zero_eq_zero]
  simp only [mk_x_vals, XVals.x_vals]
  simp
  simp [latest_x_vals]
  simp only [ReverseTree.getData, mk_x_vals, XVals.x_vals]
  simp

lemma f_neg_b {other_vals: XVals} (t: @ReverseTree other_vals) {n: ℕ} (hvals: (latest_x_vals n).cur = other_vals): f (-t.getData.b) = t.left.getData.b := by
  have eq_tree: -t.getData.b = t.left.getData.a := by
    simp [ReverseTree.getData]
  rw [eq_tree]
  rw [new_eval_left (n := n) _ hvals]



theorem not_equation_23: (f (0)) + (f (- (f (0)))) ≠ 0 := by
  let g_data := latest_x_vals 0

  have eval_neg := new_eval_left (latest_x_vals 0).tree.left (n := 0) rfl
  rw [neg_f_zero, eval_neg]
  simp [f]
  simp [latest_x_vals]
  simp only [ReverseTree.getData, mk_x_vals, XVals.x_vals]
  simp
  have mynum_gt_1 := newnem_gt_one (@ReverseTree.root (mk_x_vals 0 (g_enumerate 0)))
  have root_neq_zero: newNum (@ReverseTree.root (mk_x_vals 0 (g_enumerate 0))) ≠ 0 := by
    linarith
  simp [root_neq_zero]
  by_contra!
  have app_eq := DFunLike.congr (x := 1) this rfl
  simp at app_eq
  have val_neq_1: 1 + (newNum (@ReverseTree.root (mk_x_vals 0 (g_enumerate 0))) - 1) * 2 ≠ 1 := by
    omega
  simp [val_neq_1] at app_eq
  rw [g_num_zero_eq_zero] at app_eq
  simp [latest_x_vals] at app_eq
  simp only [ReverseTree.getData] at app_eq
  rw [g_enum_zero_eq_zero] at app_eq
  simp only [mk_x_vals, XVals.x_vals] at app_eq
  simp at app_eq


theorem not_equation_47: 0 ≠ f (f (f 0)) := by
  rw [f]
  have vals_nonzero := (tree_vals_nonzero (latest_x_vals (g_to_num (f (f 0)))).tree).2
  exact vals_nonzero.symm


lemma f_zero_eq: f (0) = (fun₀ | 1 => 1) := by
  have tree_eq: 0 = (@ReverseTree.root (mk_x_vals 0 (g_enumerate 0))).getData.a := by
    simp only [ReverseTree.getData]
    rw [g_enum_zero_eq_zero]
    simp [mk_x_vals]
  rw [tree_eq, new_eval_left (n := 0)]
  simp only [ReverseTree.getData]
  rw [g_enum_zero_eq_zero]
  simp [mk_x_vals, XVals.x_vals]
  simp [latest_x_vals]

theorem not_equation_1832: 0 ≠ f (f (0)) + f ((f (0)) - f (f (0))) := by
  simp [f_zero_eq]

  have no_root_left: ∀ t: @ReverseTree (mk_x_vals 0 0), t.getData.a ≠ fun₀ | 1 => 1 := by
    intro t
    by_contra!
    induction t with
    | root =>
      -- TODO - make a single lemma that does all of this
      simp only [ReverseTree.getData] at this
      simp only [mk_x_vals, XVals.x_vals] at this
      rw [eq_comm] at this
      rw [← Finsupp.support_eq_empty] at this
      have one_in_supp: 1 ∈ (fun₀ | 1 => (1 : ℚ)).support := by
        simp
      have supp_nonempty: (fun₀ | 1 => (1 : ℚ)).support ≠ ∅ := by
        exact Finset.ne_empty_of_mem one_in_supp
      contradiction
    | left t1_parent h_parent =>
      simp only [ReverseTree.getData] at this
      match t1_parent with
      | .root =>
        simp only [ReverseTree.getData] at this
        simp only [mk_x_vals, XVals.x_vals] at this
        simp at this
        rw [Finsupp.eq_single_iff] at this
        simp at this
        have bad := this.2
        contradiction
      | .left t1_grand =>
        simp only [ReverseTree.getData] at this
        simp only [mk_x_vals, XVals.x_vals] at this
        simp [newnum_neq_zero] at this
        rw [Finsupp.eq_single_iff] at this
        simp at this
        rw [Finsupp.support_single_ne_zero _ (by simp)] at this
        simp at this
        have bad_newnum := this.1
        have val_gt_one := newnem_gt_one t1_grand
        omega
      | .right t1_grand =>
        simp only [ReverseTree.getData] at this
        have not_comb := basis_neq_elem_diff t1_grand 1 1 (-1) 1 (by simp) (by simp) (by simp)
        simp at this
        simp at not_comb
        rw [← sub_eq_add_neg] at not_comb
        rw [eq_comm] at this
        contradiction
    | right t1_parent h_parent =>
      simp only [ReverseTree.getData] at this
      simp only [mk_x_vals, XVals.x_vals, newnum_neq_zero] at this
      simp at this
      have val_neq_one: 1 + (newNum t1_parent - 1) * 2 ≠ 1 := by
        have t1_ne_one: newNum t1_parent > 1 := by
          apply newnem_gt_one
        omega
      rw [Finsupp.eq_single_iff] at this
      simp at this
      rw [Finsupp.support_single_ne_zero _ (by simp)] at this
      simp at this
      omega

  have tree_one_not_in_x_vals_0: (∃ x_vals: XVals, ∃ t: @ReverseTree x_vals, x_vals ∈ ({mk_x_vals 0 (g_enumerate 0)} : Set XVals) ∧ t.getData.a = g_enumerate 1) = False := by
    rw [g_enum_zero_eq_zero]
    rw [g_enum_one_eq_one]
    simp [no_root_left]

  have one_is_root: (latest_x_vals (g_to_num fun₀ | 1 => 1)).tree = ReverseTree.root := by
    rw [g_num_one_eq_one]
    simp [latest_x_vals]
    conv =>
      lhs
    rw [dite_cond_eq_false tree_one_not_in_x_vals_0]


  -- MAJOR REFACTOR - generialize this to any power of 2, and make it a lemma
  have nothing_maps_other_val: ∀ {vals: XVals}, ∀ t: @ReverseTree vals, t.getData.b ≠ -fun₀ | 2 ^ (latest_x_vals (g_to_num fun₀ | 1 => 1)).cur.i => 1 := by
    intro vals t
    match t with
    | .root =>
      simp only [ReverseTree.getData]
      simp only [mk_x_vals, XVals.x_vals]
      simp
      by_contra!
      rw [← Finsupp.single_neg] at this
      rw [Finsupp.single_eq_single_iff] at this
      simp at this
      have bad := this.2
      contradiction
    | .left t1_parent =>
      simp [ReverseTree.getData]
      by_contra!
      simp [XVals.x_vals, newnum_neq_zero] at this
      rw [← Finsupp.single_neg] at this
      rw [Finsupp.single_eq_single_iff] at this
      simp at this
      have bad := this.2
      contradiction
    | .right t1_parent =>
      simp [ReverseTree.getData]
      by_contra!
      have not_eq := basis_neq_elem_diff t1_parent (2 ^ (latest_x_vals (g_to_num fun₀ | 1 => 1)).cur.i) (-1) 1 (-1) (by simp) (by simp) (by simp)
      simp at not_eq
      rw [neg_add_eq_sub, eq_comm] at not_eq
      contradiction

  by_contra!
  rw [eq_comm, add_comm, add_eq_zero_iff_eq_neg] at this
  conv at this =>
    rhs
    rw [f, one_is_root]
  simp only [ReverseTree.getData, XVals.x_vals] at this
  simp at this
  specialize nothing_maps_other_val (latest_x_vals (g_to_num ((fun₀ | 1 => 1) - f fun₀ | 1 => 1))).tree
  exact nothing_maps_other_val this

lemma sum_1_3_eq_tree: (fun₀ | 1 => (1: ℚ)) + (fun₀ | 3 => 1) = (@ReverseTree.root (mk_x_vals 0 (g_enumerate 0))).left.right.left.getData.a := by
  simp [ReverseTree.getData, mk_x_vals, XVals.x_vals, newnum_neq_zero, newNum]
  rw [add_comm]


theorem not_equation_2441: 0 ≠ (f ((f 0) + (f (- f 0)))) + (f ( -(f ((f 0) + f (- f (0))))) ) := by
  simp [neg_f_zero]
  simp [new_eval_left (n := 0)]
  simp only [latest_x_vals, ReverseTree.getData]
  rw [g_enum_zero_eq_zero]
  simp [mk_x_vals, XVals.x_vals]
  simp [newnum_neq_zero]
  simp [f_zero_eq]
  simp [newNum]

  rw [sum_1_3_eq_tree]
  rw [new_eval_left (n := 0) _ rfl]

  rw [f_neg_b (n := 0) _ rfl]
  simp only [ReverseTree.getData]
  simp [mk_x_vals, XVals.x_vals, newnum_neq_zero, newNum]
  by_contra!
  simp [latest_x_vals, mk_x_vals] at this
  have app_eq := DFunLike.congr (x := 11) this rfl
  simp at app_eq

lemma x_vals_zero_left_a: (latest_x_vals 0).tree.left.getData.a = (-fun₀ | 1 => 1) := by
  simp [ReverseTree.getData]
  simp [XVals.x_vals, newnum_neq_zero, newNum]
  simp only [latest_x_vals]
  rw [g_enum_zero_eq_zero]
  simp [mk_x_vals]

lemma x_vals_zero_left_b: (latest_x_vals 0).tree.left.getData.b = fun₀ | 3 => 1 := by
  simp [ReverseTree.getData]
  simp [XVals.x_vals, newnum_neq_zero, newNum]
  simp only [latest_x_vals]
  rw [g_enum_zero_eq_zero]
  simp [mk_x_vals]


theorem not_equation_3050: 0 ≠ (f 0) + (f (- (f 0))) + (f (- (f 0) - f (- f 0))) + (f (- (f 0) - f (- f 0) - f (- (f 0) - f (- f 0)))) := by
  rw [neg_f_zero, new_eval_left (n := 0)]
  nth_rw 1 [f_zero_eq]
  simp [x_vals_zero_left_a, x_vals_zero_left_b]
  by_contra!
  sorry
  rfl






lemma cancellation_for_3050 (x: G): ((x + f 0) + f (-f 0) + f (x - (x + f 0 + f (-f 0))) + f (x - (x + f 0 + f (-f 0) + f (x - (x + f 0 + f (-f 0)))))) - x
  = ((f 0) + (f (- (f 0))) + (f (- (f 0) - f (- f 0))) + (f (- (f 0) - f (- f 0) - f (- (f 0) - f (- f 0))))) := by
    abel

lemma diamond_not_equation_3050 (x : G): x ≠ diamond f (diamond f (diamond f (diamond f x x) x) x) x := by
  simp [diamond]
  by_contra!
  apply_fun (λ y => y - x) at this
  simp at this
  rw [cancellation_for_3050 x] at this
  exact not_equation_3050 this




theorem not_equation_3456: f 0 ≠ f ((f 0) + f (- (f 0))) := by
  simp only [neg_f_zero]
  rw [new_eval_left (n := 0)]
  simp [f_zero_eq]
  simp [ReverseTree.getData, newNum]
  simp only [latest_x_vals]
  rw [g_enum_zero_eq_zero]
  simp [mk_x_vals, XVals.x_vals]

  rw [sum_1_3_eq_tree]
  rw [new_eval_left (n := 0)]
  simp only [ReverseTree.getData]
  rw [g_enum_zero_eq_zero]
  simp [mk_x_vals, XVals.x_vals, newnum_neq_zero, newNum]
  by_contra!
  rw [Finsupp.single_left_inj] at this
  linarith
  simp
  simp [latest_x_vals]
  rfl

lemma nothing_maps_some_val {vals: XVals} (t: @ReverseTree vals) (i: ℕ): t.getData.b ≠ -fun₀ | i => 1 := by
  match t with
  | .root =>
    simp only [ReverseTree.getData]
    simp only [mk_x_vals, XVals.x_vals]
    simp
    by_contra!
    rw [← Finsupp.single_neg] at this
    rw [Finsupp.single_eq_single_iff] at this
    simp at this
    have bad := this.2
    contradiction
  | .left t1_parent =>
    simp [ReverseTree.getData]
    by_contra!
    simp [XVals.x_vals, newnum_neq_zero] at this
    rw [← Finsupp.single_neg] at this
    rw [Finsupp.single_eq_single_iff] at this
    simp at this
    have bad := this.2
    contradiction
  | .right t1_parent =>
    simp [ReverseTree.getData]
    by_contra!
    have not_eq := basis_neq_elem_diff t1_parent (i) (-1) 1 (-1) (by simp) (by simp) (by simp)
    simp at not_eq
    rw [neg_add_eq_sub, eq_comm] at not_eq
    contradiction

theorem not_equation_4065: f 0 ≠ (f 0) + (f (- f 0)) + f ((- f 0) - f (- (f 0) - f (-f 0))) := by
  rw [neg_f_zero, new_eval_left (n := 0)]
  nth_rw 1 [f_zero_eq]
  simp [x_vals_zero_left_a, x_vals_zero_left_b]
  rw [f_zero_eq]
  by_contra!
  apply_fun (λ y => -(fun₀ | 1 => 1) + y) at this
  simp at this
  rw [← add_assoc] at this
  rw [← add_assoc] at this
  simp at this
  apply_fun (λ y => -(fun₀ | 3 => 1) + y) at this
  rw [← add_assoc] at this
  simp at this


  nth_rw 1 [f] at this
  have not_maps := nothing_maps_some_val (latest_x_vals (g_to_num ((-fun₀ | 1 => 1) - f ((-fun₀ | 1 => 1) - fun₀ | 3 => 1)))).tree 3
  rw [eq_comm] at this
  exact not_maps this
  rfl

-- noncomputable def total_function (x: G): G := by
--   by_cases x_in_tree: ∃ t: ReverseTree, x = t.getData.a
--   . let t := Classical.choose x_in_tree
--     have ht:= Classical.choose_spec x_in_tree
--     exact t.getData.b
--   . exact total_function x
--     -- nonempty_denumerable_iff
