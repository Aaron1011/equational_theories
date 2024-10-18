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


    have k_le_first: 2^i ≤ k := by
      simp [s_i] at e_k_in_i
      obtain ⟨_, k_eq⟩ := e_k_in_i
      rw [Nat.ModEq] at k_eq
      have two_pow_lt: 2^i < 2^(i + 1) := by
        apply Nat.pow_lt_pow_succ
        simp
      rw [Nat.mod_eq_of_lt two_pow_lt] at k_eq
      have k_mod_lt: k % 2 ^ (i + 1)< (2^(i+1)) := by
        apply Nat.mod_lt
        simp

      by_contra!
      have k_lt_2i_plus: k < 2^(i+1) := by
        exact Nat.lt_trans this two_pow_lt

      have bar := Nat.mod_eq_of_lt k_lt_2i_plus
      rw [bar] at k_eq
      linarith

    have k_le_second: 2^j ≤ k := by
      sorry

    have e_k_in_i: k ≡ 2^i [MOD 2^(i + 1)] := by
      simp [s_i] at e_k_in_i
      exact e_k_in_i.2

    have e_k_in_j: k ≡ 2^j [MOD 2^(j + 1)] := by
      simp [s_i] at e_k_in_j
      exact e_k_in_j.2

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

    apply Nat.ModEq.symm at e_k_in_j
    apply (Nat.modEq_iff_dvd' k_le_second).mp at e_k_in_j
    obtain ⟨d, hd⟩ := e_k_in_j

    have k_j_eq_sum: k = 2^j + 2^(j + 1) * d := by
      apply Nat.eq_add_of_sub_eq k_le_second at hd
      rw [Nat.add_comm] at hd
      exact hd

    have k_j_factor: k = 2^j * (1 + 2 * d) := by
      rw [k_j_eq_sum]
      ring

    have two_factor_i: (2^i * (1 + 2 * c)).factorization 2 = i := by
      rw [Nat.factorization_mul]
      rw [Nat.Prime.factorization_pow (Nat.prime_two)]
      simp [Nat.factorization_eq_zero_of_not_dvd]
      simp
      simp

    have two_factor_j: (2^j * (1 + 2 * d)).factorization 2 = j := by
      rw [Nat.factorization_mul]
      rw [Nat.Prime.factorization_pow (Nat.prime_two)]
      simp [Nat.factorization_eq_zero_of_not_dvd]
      simp
      simp

    rw [← k_i_factor] at two_factor_i
    rw [← k_j_factor] at two_factor_j
    rw [two_factor_i] at two_factor_j
    linarith

  rfl
