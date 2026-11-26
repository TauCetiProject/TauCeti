/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.SU2.Weyl.Integration

/-!
# The conjugacy angle of `SU(2)`

The conjugacy angle parametrizes the conjugacy classes of `SU(2)` by the closed interval
`[0, π]`. In this coordinate, Haar probability has density `(2/π) sin² θ` and the character of
the degree-`d` symmetric power is the Chebyshev value `U_d(cos θ)`.

See K. S. Kedlaya, *Notes on analytic number theory*, §24.5.
-/

public section

open MeasureTheory

namespace TauCeti.SU2

/-- The angle in `[0, π]` of the conjugacy class of an element of `SU(2)`. -/
noncomputable def conjugacyAngle (g : SU2) : ℝ :=
  Real.arccos ((Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)).re / 2)

/-- The angle is the inverse cosine of half the trace. -/
theorem conjugacyAngle_def (g : SU2) :
    conjugacyAngle g = Real.arccos ((Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ)).re / 2) :=
  (rfl)

/-- The conjugacy angle belongs to the closed Weyl chamber. -/
theorem conjugacyAngle_mem_Icc (g : SU2) : conjugacyAngle g ∈ Set.Icc (0 : ℝ) Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- The angle is continuous as a function of the group element. -/
@[fun_prop]
theorem continuous_conjugacyAngle : Continuous conjugacyAngle := by
  have ht : Continuous fun g : SU2 ↦ Matrix.trace (g : Matrix (Fin 2) (Fin 2) ℂ) :=
    Continuous.matrix_trace continuous_subtypeVal
  exact Real.continuous_arccos.comp ((Complex.continuous_re.comp ht).div_const 2)

/-- Conjugate elements have the same angle. -/
theorem conjugacyAngle_eq_of_isConj {g h : SU2} (hgh : IsConj g h) :
    conjugacyAngle g = conjugacyAngle h := by
  simp only [conjugacyAngle_def, trace_eq_of_isConj hgh]

/-- In the Weyl chamber, the angle of the diagonal representative is its parameter. -/
@[simp]
theorem conjugacyAngle_torusExp {θ : ℝ} (hθ : θ ∈ Set.Icc (0 : ℝ) Real.pi) :
    conjugacyAngle (torusExp θ) = θ := by
  rw [conjugacyAngle_def, trace_torusExp]
  simpa [Complex.mul_re, Complex.cos_ofReal_re] using Real.arccos_cos hθ.1 hθ.2

/-- A group element is conjugate to the diagonal representative at its angle. -/
theorem isConj_torusExp_conjugacyAngle (g : SU2) : IsConj g (torusExp (conjugacyAngle g)) := by
  obtain ⟨θ, hθ, hg⟩ := exists_isConj_torusExp_mem_Icc g
  rwa [conjugacyAngle_eq_of_isConj hg, conjugacyAngle_torusExp hθ]

/-- The angle is a complete conjugacy invariant. -/
theorem conjugacyAngle_eq_iff_isConj {g h : SU2} :
    conjugacyAngle g = conjugacyAngle h ↔ IsConj g h := by
  refine ⟨fun he ↦ (isConj_torusExp_conjugacyAngle g).trans ?_, conjugacyAngle_eq_of_isConj⟩
  rw [he]
  exact (isConj_torusExp_conjugacyAngle h).symm

/-- Integrating a real continuous test function of the angle against Haar probability gives the
integral against the density `(2/π) sin² θ` on the closed Weyl chamber. -/
theorem integral_comp_conjugacyAngle {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 Real.pi)) :
    ∫ g, f (conjugacyAngle g) ∂haarProb SU2 =
      (2 / Real.pi) * ∫ θ in (0 : ℝ)..Real.pi, f θ * Real.sin θ ^ 2 := by
  have hcont : Continuous (f ∘ conjugacyAngle) :=
    hf.comp_continuous continuous_conjugacyAngle conjugacyAngle_mem_Icc
  have h := weyl_integration_formula (Complex.continuous_ofReal.comp hcont) (fun u g ↦ by
    have hc : IsConj g (u * g * u⁻¹) := isConj_iff.mpr ⟨u, rfl⟩
    simpa only [Function.comp_apply] using
      congrArg (fun θ ↦ (f θ : ℂ)) (conjugacyAngle_eq_of_isConj hc).symm)
  have hfactor :
      ∫ θ in (0 : ℝ)..Real.pi,
        (f (conjugacyAngle (torusExp θ)) : ℂ) * ((4 * Real.sin θ ^ 2 : ℝ) : ℂ) =
      4 * ((∫ θ in (0 : ℝ)..Real.pi, f θ * Real.sin θ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun θ hθ ↦ ?_
    rw [Set.uIcc_of_le Real.pi_pos.le] at hθ
    rw [conjugacyAngle_torusExp hθ]
    push_cast
    ring
  simp only [Function.comp_apply, Function.comp_def, integral_complex_ofReal, hfactor] at h
  calc
    ∫ g, f (conjugacyAngle g) ∂haarProb SU2 =
        (1 / (2 * Real.pi)) * (4 * ∫ θ in (0 : ℝ)..Real.pi, f θ * Real.sin θ ^ 2) := by
      exact_mod_cast h
    _ = _ := by ring

/-- The symmetric-power character of an element with conjugacy angle `θ` is the real
Chebyshev value `U_d(cos θ)`. -/
theorem character_symPower_eq_chebyshevU_eval_cos_conjugacyAngle (d : ℕ) (g : SU2) :
    (symPower d).character g =
      ((Polynomial.Chebyshev.U ℝ d).eval (Real.cos (conjugacyAngle g)) : ℝ) := by
  rw [character_symPower_eq_chebyshevU_eval, trace_eq_of_isConj (isConj_torusExp_conjugacyAngle g),
    trace_torusExp, mul_comm (2 : ℂ), mul_div_cancel_right₀ _ (by norm_num : (2 : ℂ) ≠ 0)]
  rw [← Polynomial.Chebyshev.map_U Complex.ofRealHom]
  exact Polynomial.eval_map_apply Complex.ofRealHom _

end TauCeti.SU2
