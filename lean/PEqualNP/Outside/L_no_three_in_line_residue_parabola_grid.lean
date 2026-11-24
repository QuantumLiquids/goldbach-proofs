import Mathlib

theorem PEqualNP.Outside.L_no_three_in_line_residue_parabola_grid :
    let valid := fun (n : ℕ) (S : Finset (ℕ × ℕ)) => (∀ z ∈ S, z.1 < n ∧ z.2 < n) ∧ (∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, a ≠ b → a ≠ c → b ≠ c → ((b.1 : ℤ) - (a.1 : ℤ)) * ((c.2 : ℤ) - (a.2 : ℤ)) ≠ ((b.2 : ℤ) - (a.2 : ℤ)) * ((c.1 : ℤ) - (a.1 : ℤ))); ∀ p : ℕ, Nat.Prime p → let S := (Finset.range p).image (fun x => (x, x^2 % p)); valid p S ∧ S.card = p := by
  dsimp only
  intro p hp
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  have hne {i j : ℕ} (hi : i ∈ Finset.range p) (hj : j ∈ Finset.range p)
      (hne : (i, i^2 % p) ≠ (j, j^2 % p)) : (i : ZMod p) ≠ (j : ZMod p) := by
    intro h
    have hij := (ZMod.natCast_eq_natCast_iff' i j p).mp h
    rw [Nat.mod_eq_of_lt (Finset.mem_range.mp hi),
      Nat.mod_eq_of_lt (Finset.mem_range.mp hj)] at hij
    exact hne (congrArg (fun t : ℕ => (t, t^2 % p)) hij)
  constructor
  · constructor
    · intro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      exact ⟨Finset.mem_range.mp hi, Nat.mod_lt _ hp.pos⟩
    · intro A hA B hB C hC
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hB
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hC
      intro hAB hAC hBC hdet
      have hf := congrArg (fun t : ℤ => (t : ZMod p)) hdet
      dsimp only at hf
      simp only [Int.cast_mul, Int.cast_sub, Int.cast_natCast, ZMod.natCast_mod, Nat.cast_pow] at hf
      have hz : ((j : ZMod p) - i) * ((k : ZMod p) - i) * ((k : ZMod p) - j) = 0 := by
        linear_combination hf
      exact ((mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr (hne hi hj hAB).symm)
        (sub_ne_zero.mpr (hne hi hk hAC).symm)) (sub_ne_zero.mpr (hne hj hk hBC).symm)) hz).elim
  · rw [Finset.card_image_of_injective, Finset.card_range]
    intro i j hij
    exact congrArg Prod.fst hij
