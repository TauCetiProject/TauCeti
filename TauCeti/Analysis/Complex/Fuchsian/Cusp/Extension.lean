/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Fuchsian.Cusp.Coordinate
public import Mathlib.NumberTheory.ModularForms.QExpansion

/-!
# Extension of invariant functions at a Fuchsian cusp

Let `D` be normalized cusp data for a subgroup of `PSL(2, ℝ)`. Pulling a function on the
upper half-plane back by `D.scaling⁻¹` turns invariance under the cusp stabilizer into
periodicity by `D.width`. Mathlib's periodic cusp function therefore descends the function to
the punctured q-disc. If the original function is holomorphic and bounded as the scaled height
tends to infinity, the descended function extends holomorphically across `q = 0`.

The construction uses the same q-coordinate as
`TauCeti.Subgroup.CuspDatum.qCoordinate`. In particular, no choice of representatives of the
stabilizer quotient occurs.

## Main declarations

* `TauCeti.Subgroup.CuspDatum.cuspExtension`: the function of the q-variable, including its
  value at `q = 0`.
* `TauCeti.Subgroup.CuspDatum.descend`: its restriction to the punctured unit disc.
* `TauCeti.Subgroup.CuspDatum.mdifferentiable_descend`: an invariant holomorphic function
  descends holomorphically.
* `TauCeti.Subgroup.CuspDatum.analyticAt_cuspExtension_zero`: boundedness in the normalized
  scaling coordinate makes the singularity at `q = 0` removable.

## References

* Fred Diamond and Jerry Shurman, *A First Course in Modular Forms*, §2.4.
* Otto Forster, *Lectures on Riemann Surfaces*, §19.
-/

public noncomputable section

open Function Matrix.ProjectiveSpecialLinearGroup MulAction UpperHalfPlane
open scoped Complex.UnitDisc ContDiff Manifold MatrixGroups

namespace TauCeti.Subgroup.CuspDatum

variable {Γ : Subgroup PSL(2, ℝ)}

/-- Pullback by the inverse scaling is periodic by the cusp width when a function is invariant
under the full cusp stabilizer. -/
theorem periodic_comp_ofComplex_inv_smul (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z) :
    Periodic ((fun z : ℍ ↦ f (D.scaling⁻¹ • z)) ∘ ofComplex) D.width := by
  apply UpperHalfPlane.periodic_comp_ofComplex
  intro z
  have htranslate : D.scaling⁻¹ • (D.width +ᵥ z) =
      (D.generator : PSL(2, ℝ)) • (D.scaling⁻¹ • z) := by
    have h : D.scaling • ((D.generator : PSL(2, ℝ)) • (D.scaling⁻¹ • z)) =
        D.width +ᵥ z := by
      simpa only [zpow_one, Int.cast_one, one_mul, Subgroup.smul_def, smul_inv_smul] using
        TauCeti.Subgroup.CuspDatum.scaling_smul_generator_zpow D (1 : ℤ)
          (D.scaling⁻¹ • z)
    rw [← h, inv_smul_smul]
  rw [htranslate]
  simpa only [Subgroup.smul_def] using
    hf ⟨D.generator, D.generator_mem_stabilizer⟩ (D.scaling⁻¹ • z)

/-- Pulling a holomorphic function back by the inverse cusp scaling is holomorphic. -/
theorem mdifferentiable_inv_smul (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) fun z : ℍ ↦ f (D.scaling⁻¹ • z) :=
  hhol.comp <|
    (contMDiff_const_smul (I := 𝓘(ℂ, ℂ)) (n := ∞) D.scaling⁻¹).mdifferentiable (by simp)

/-- The function of the q-variable associated to a function on the upper half-plane and normalized
cusp data. Away from zero it is obtained by a logarithmic lift in the scaling coordinate; its
value at zero is Mathlib's `limUnder` extension. -/
def cuspExtension (D : Γ.CuspDatum) (f : ℍ → ℂ) : ℂ → ℂ :=
  UpperHalfPlane.cuspFunction D.width fun z ↦ f (D.scaling⁻¹ • z)

/-- An invariant function is recovered by evaluating its cusp extension in the normalized
q-coordinate. -/
@[simp]
theorem cuspExtension_coordinate (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z) (z : ℍ) :
    cuspExtension D f (coordinate D z) = f z := by
  rw [cuspExtension, coordinate_apply]
  simpa using UpperHalfPlane.eq_cuspFunction (D.scaling • z) D.width_pos.ne'
    (periodic_comp_ofComplex_inv_smul D f hf)

/-- The descent of a function to the punctured q-disc associated to normalized cusp data. -/
def descend (D : Γ.CuspDatum) (f : ℍ → ℂ) : {q : 𝔻 // q ≠ 0} → ℂ :=
  fun q ↦ cuspExtension D f q

/-- The descended function is the restriction of the cusp extension to the punctured unit disc. -/
@[simp]
theorem descend_apply (D : Γ.CuspDatum) (f : ℍ → ℂ) (q : {q : 𝔻 // q ≠ 0}) :
    descend D f q = cuspExtension D f q :=
  (rfl)

/-- An invariant function is recovered by pulling its punctured-disc descent back along the
normalized q-coordinate. -/
theorem descend_qCoordinate (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z) (z : ℍ) :
    descend D f (qCoordinate D z) = f z := by
  rw [descend_apply, coe_qCoordinate, cuspExtension_coordinate D f hf]

/-- The descended function is the unique function on the punctured q-disc whose pullback along
the normalized q-coordinate is the original invariant function. -/
theorem descend_unique (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    {F : {q : 𝔻 // q ≠ 0} → ℂ} (hF : ∀ z, F (qCoordinate D z) = f z) :
    F = descend D f := by
  funext q
  obtain ⟨z, rfl⟩ := (isOpenQuotientMap_qCoordinate D).surjective q
  rw [hF, descend_qCoordinate D f hf]

/-- The cusp extension of an invariant holomorphic function is complex differentiable at every
nonzero point of the open unit disc. -/
theorem differentiableAt_cuspExtension_of_ne_zero (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) {q : ℂ} (hq : q ≠ 0) (hq_norm : ‖q‖ < 1) :
    DifferentiableAt ℂ (cuspExtension D f) q := by
  rw [cuspExtension, ← Function.Periodic.qParam_right_inv D.width_pos.ne' hq]
  apply Function.Periodic.differentiableAt_cuspFunction D.width_pos.ne'
    (periodic_comp_ofComplex_inv_smul D f hf)
  have him : 0 < (Function.Periodic.invQParam D.width q).im :=
    Function.Periodic.im_invQParam_pos_of_norm_lt_one D.width_pos hq_norm hq
  simpa only using UpperHalfPlane.mdifferentiableAt_iff.mp
    (mdifferentiable_inv_smul D f hhol ⟨Function.Periodic.invQParam D.width q, him⟩)

/-- An invariant holomorphic function descends to a holomorphic function on the punctured
q-disc. -/
theorem mdifferentiable_descend (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f) :
    MDifferentiable 𝓘(ℂ) 𝓘(ℂ) (descend D f) := by
  intro q
  apply MDifferentiableAt.comp q
    (DifferentiableAt.mdifferentiableAt <|
      differentiableAt_cuspExtension_of_ne_zero D f hf hhol
        (fun h ↦ q.2 (Complex.UnitDisc.coe_injective h)) q.1.norm_lt_one)
  exact TauCeti.Complex.UnitDisc.mdifferentiable_coe_punctured q

/-- If an invariant holomorphic function is bounded as the normalized scaling coordinate tends
to `i∞`, then its cusp extension is analytic at `q = 0`. -/
theorem analyticAt_cuspExtension_zero (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbounded : IsBoundedAtImInfty fun z ↦ f (D.scaling⁻¹ • z)) :
    AnalyticAt ℂ (cuspExtension D f) 0 := by
  rw [cuspExtension]
  apply UpperHalfPlane.analyticAt_cuspFunction_zero D.width_pos
    (periodic_comp_ofComplex_inv_smul D f hf)
  · exact mdifferentiable_inv_smul D f hhol
  · exact hbounded

/-- For an invariant holomorphic function bounded at the cusp, the value of its holomorphic
extension at `q = 0` is the limit of the function in the normalized scaling coordinate. -/
theorem cuspExtension_zero_eq_valueAtInfty (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbounded : IsBoundedAtImInfty fun z ↦ f (D.scaling⁻¹ • z)) :
    cuspExtension D f 0 = valueAtInfty (fun z ↦ f (D.scaling⁻¹ • z)) := by
  rw [cuspExtension]
  exact UpperHalfPlane.cuspFunction_apply_zero D.width_pos
    (analyticAt_cuspExtension_zero D f hf hhol hbounded)
    (periodic_comp_ofComplex_inv_smul D f hf)

/-- A bounded invariant holomorphic function approaches its cusp-extension value at the first
q-exponential rate in the normalized scaling coordinate. -/
theorem isBigO_sub_cuspExtension_zero (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hbounded : IsBoundedAtImInfty fun z ↦ f (D.scaling⁻¹ • z)) :
    (fun z : ℍ ↦ f (D.scaling⁻¹ • z) - cuspExtension D f 0) =O[atImInfty]
      fun z ↦ Real.exp (-2 * Real.pi * z.im / D.width) := by
  rw [cuspExtension_zero_eq_valueAtInfty D f hf hhol hbounded]
  apply UpperHalfPlane.exp_decay_sub_atImInfty D.width_pos
    (periodic_comp_ofComplex_inv_smul D f hf)
  · exact mdifferentiable_inv_smul D f hhol
  · exact hbounded

/-- If a function tends to zero in the normalized scaling coordinate, then the value of its cusp
extension at `q = 0` is zero. -/
@[simp]
theorem cuspExtension_zero_eq_zero (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hzero : IsZeroAtImInfty fun z ↦ f (D.scaling⁻¹ • z)) :
    cuspExtension D f 0 = 0 := by
  rw [cuspExtension]
  exact UpperHalfPlane.IsZeroAtImInfty.cuspFunction_apply_zero hzero D.width_pos

/-- An invariant holomorphic function that tends to zero at the cusp does so at the first
q-exponential rate in the normalized scaling coordinate. -/
theorem isBigO_inv_smul_of_isZeroAtImInfty (D : Γ.CuspDatum) (f : ℍ → ℂ)
    (hf : ∀ (g : stabilizer Γ D.cusp) (z : ℍ), f (g • z) = f z)
    (hhol : MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f)
    (hzero : IsZeroAtImInfty fun z ↦ f (D.scaling⁻¹ • z)) :
    (fun z : ℍ ↦ f (D.scaling⁻¹ • z)) =O[atImInfty]
      fun z ↦ Real.exp (-2 * Real.pi * z.im / D.width) := by
  simpa only [cuspExtension_zero_eq_zero D f hzero, sub_zero] using
    isBigO_sub_cuspExtension_zero D f hf hhol hzero.isBoundedAtImInfty

end TauCeti.Subgroup.CuspDatum
