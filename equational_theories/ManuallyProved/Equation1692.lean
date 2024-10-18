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

    --have foo := Nat.modEq_and_modEq_iff_modEq_mul sorry


    have pow_divides: 2^(i+1) ∣ 2^(j+1) := by
      refine (Nat.pow_dvd_pow_iff_le_right ?w).mpr ?_
      simp
      linarith


    let my_gcd := Nat.gcd (2^(i+1)) (2^(j+1))
    have my_gcd_eq: my_gcd = 2^(i+1) := by
      simp only [my_gcd]
      exact Nat.gcd_eq_left pow_divides

    have gcd_div_i: my_gcd ∣ 2^(i+1) := by
      exact Nat.gcd_dvd_left (2^(i+1)) (2^(j+1))

    have gcd_div_j: my_gcd ∣ 2^(j+1) := by
      exact Nat.gcd_dvd_right (2 ^ (i + 1)) (2 ^ (j + 1))

    obtain ⟨p, hp⟩ := gcd_div_i
    rw [hp] at e_k_in_i

    obtain ⟨q, hq⟩ := gcd_div_j
    rw [hq] at e_k_in_j

    have gcd_gt_zero: 0 < my_gcd := by
      simp only [my_gcd]
      apply Nat.gcd_pos_of_pos_left
      simp

    have gcd_div_coprime: Nat.Coprime (2^(i+1) / my_gcd) (2^(j+1) / my_gcd) := by
      simp only [my_gcd]
      apply Nat.coprime_div_gcd_div_gcd gcd_gt_zero


    have k_eq_div_i: 2^i ≡ k [MOD 2^(i + 1) / my_gcd] := by
      sorry

    have k_eq_div_j: 2^j ≡ k [MOD 2^(j + 1) / my_gcd] := by
      sorry

    have gcd_divides: my_gcd ∣ 2^j - 2^i := by
      sorry

    have exp_mono: 2^i < 2^j := by
      apply pow_lt_pow_right
      simp
      assumption

    have not_divide: ¬(my_gcd ∣ 2^j - 2^i) := by
      apply Nat.not_dvd_of_pos_of_lt
      simp
      apply exp_mono
      rw [my_gcd_eq]
      linarith

    rw [my_gcd_eq] at gcd_divides
    simp at gcd_divides



    -- simp at e_k_in_i
    -- apply Nat.ModEq.dvd at e_k_in_i
    -- obtain ⟨c, hc⟩ := e_k_in_i

    -- simp at e_k_in_j
    -- apply Nat.ModEq.dvd at e_k_in_j
    -- obtain ⟨d, hd⟩ := e_k_in_j




    -- have k_eq_i: k = 2^i - 2^(i + 1) * c := by
    --   sorry

    -- have k_eq_j: k = 2^j - 2^(j + 1) * d := by
    --   sorry

    -- have k_fac: k = 2^i * (1 - 2 * c) := by
    --   rw [k_eq_i]
    --   ring

    -- have k_fac2: k = 2^j * (1 - 2 * d) := by
    --   rw [k_eq_j]
    --   ring

    -- have sides_eq: 2^i * (1 - 2 * c) = 2^j * (1 - 2 * d) := by
    --   linarith

    -- have div_pow: 2^(i - j) * (1 - 2 * c) = 1 - 2 * d := by
    --   sorry

    -- have val_eq: 2^(i - j) =  (1 - 2 * d) / (1 - 2 * c) := by
    --   sorry






  rfl
