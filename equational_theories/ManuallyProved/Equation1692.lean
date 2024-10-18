import Mathlib

-- https://leanprover.zulipchat.com/user_uploads/3121/ASjTo5huToAvNGcg7pOGOOSy/Equation1692.pdf

#synth AddGroup (∀ n: ℕ, ℤ)

-- TODO -  only finitely many entries are non-zero?
abbrev G := (∀ n: ℕ, ℚ)

theorem foo: 1 = 1 := by
  have is_group: AddGroup (G) := by infer_instance
  have divsion_ring: DivisionRing ℚ := by infer_instance
  have is_module: Module ℚ G := by infer_instance
  have add_comm: AddCommGroup G := by infer_instance

  let n_q_basis := Finsupp.basisSingleOne (R := ℚ) (ι := ℕ)
  let basis_n := DFunLike.coe n_q_basis
  let all_basis := (λ n: ℕ => (n, basis_n n)) '' Set.univ
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
      have k_eq_2j: k = 2 * j := by
        rw [hj]
        linarith
      use j
      sorry
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
