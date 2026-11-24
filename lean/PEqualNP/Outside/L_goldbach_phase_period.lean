import Mathlib

theorem PEqualNP.Outside.L_goldbach_phase_period :
    let E := fun x : ℝ => Complex.exp (((2*Real.pi*x:ℝ):ℂ)*Complex.I); ∀ (t : ℝ) (m : ℤ), E (t+(m:ℝ))=E t := by
  dsimp only
  intro t m
  calc
    _ = Complex.exp
        ((((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) +
          (m : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) := by
      congr 1
      push_cast
      ring
    _ = _ := by rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
