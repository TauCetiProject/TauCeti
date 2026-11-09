/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Closed
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.BoundarylessStokes
public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.Positivity
public import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Orientation

/-!
# Harmonic functions on compact almost complex surfaces are constant

Let `(C, j)` be a surface with a smooth almost complex structure, oriented so that every frame
`(e, j e)` is positive. A real function `τ` on `C` is harmonic when its *conjugate differential*
`dτ ∘ j` is closed. For instance, if `σ + i τ` is holomorphic, then `dτ (j e) = dσ e`, so
`dτ ∘ j = dσ` is closed. Here `σ` may take values in a circle, so that `dσ` is a closed one-form
which need not be exact; this is the case of a holomorphic map to the cylinder `(ℝ / ℤ) × ℝ`.

On a compact boundaryless surface, a `C¹` function whose conjugate differential is a closed smooth
one-form is locally constant
(`TauCeti.SmoothAlmostComplexStructure.mvfderiv_eq_zero_of_isClosed`). Write `β = dτ ∘ j` for the
closed conjugate differential. By the Leibniz rule,

`d(τ β)(e, j e) = dτ(e) β(j e) - dτ(j e) β(e) = -(dτ(e)² + dτ(j e)²)`,

since `β(j e) = dτ(j (j e)) = -dτ(e)` and `β(e) = dτ(j e)`. So `-d(τ β)` is a nonnegative top
form, positive wherever `dτ ≠ 0`, and Stokes' theorem gives `∫_C d(τ β) = 0`. Hence `dτ = 0`
everywhere. No integrable complex coordinates on `C` are used, and `τ` need only be `C¹`.

The pointwise positivity step,
`TauCeti.SmoothAlmostComplexStructure.apply_basis_nonneg_of_forall_nonneg`, turns the sign of
`-d(τ β)` on the frames `(e, j e)` into its sign on positively oriented bases.

## Main results

* `TauCeti.SmoothAlmostComplexStructure.mvfderiv_eq_zero_of_isClosed`: a `C¹` function on a
  compact boundaryless surface whose conjugate differential `dτ ∘ j` is a closed smooth one-form
  has zero differential.

## References

* O. Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  Sections 9 and 19 (harmonic functions and the conjugate differential `*dτ`).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.2 (energy of holomorphic curves and Stokes'
  theorem).
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti

namespace SmoothAlmostComplexStructure

variable {E H C : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace C] [ChartedSpace H C]
  [IsManifold I ∞ C] (j : SmoothAlmostComplexStructure I C) {o : Manifold.Orientation I C (Fin 2)}

/-- **Harmonic functions on compact surfaces are constant.** Let `C` be a compact boundaryless
surface with an almost complex structure `j`, oriented so that the frames `(e, j e)` are positive,
and let `τ` be a `C¹` function whose conjugate differential `dτ ∘ j` is a closed smooth one-form
`β`. Then `τ` has zero differential at every point. -/
theorem mvfderiv_eq_zero_of_isClosed [T2Space C] [CompactSpace C] [BoundarylessManifold I C]
    (ho : ∀ c (b : Basis (Fin 2) ℝ (TangentSpace I c)), b 1 = j c (b 0) →
      b.orientation = o.orientationAt c)
    {τ : C → ℝ} (hτ : ContMDiff I 𝓘(ℝ) 1 τ) {β : SmoothForm I C ℝ 1} (hβ : β.IsClosed)
    (hτβ : ∀ c e, mvfderiv I τ c (j c e) = β.1 c ![e]) (c : C) : mvfderiv I τ c = 0 := by
  -- The one-form `α = τ β`, and the top form `η = -dα`.
  set α : RoughForm I C ℝ 1 := fun c ↦ τ c • β.1 c
  have hα : IsSmoothForm I 1 α := (β.isSmoothForm.of_le (by simp)).fun_smul hτ
  set η : RoughForm I C ℝ 2 := (-1 : ℝ) • mextDeriv α
  -- On a frame `(e, j e)`, `η` is the energy density `dτ(e)² + dτ(j e)²`.
  have hη (c : C) (e : TangentSpace I c) :
      η c ![e, j c e] = mvfderiv I τ c e ^ 2 + mvfderiv I τ c (j c e) ^ 2 := by
    have hβ' : mextDeriv β.1 c ![e, j c e] = 0 := by
      rw [(SmoothForm.isClosed_iff_forall_mextDeriv_apply_eq_zero β).1 hβ c]
      rfl
    have hβj : β.1 c ![j c e] = -mvfderiv I τ c e := by
      rw [← hτβ, apply_apply, map_neg]
    simp only [η, Pi.smul_apply, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
    rw [mextDeriv_fun_smul_apply (hτ.mdifferentiableAt one_ne_zero)
      ((β.isSmoothForm.contMDiff c).mdifferentiableAt (by simp)), hβ', hβj, ← hτβ]
    ring
  -- By Stokes' theorem, `∫_C η = 0`.
  have hint : integralTopForm o η = 0 := by
    rw [integralTopForm_smul, integralTopForm_mextDeriv_eq_zero o hα
      (isClosed_tsupport _).isCompact, mul_zero]
  by_contra hne
  obtain ⟨e, he⟩ : ∃ e, mvfderiv I τ c e ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (ContinuousLinearMap.ext h)
  -- The frame `(e, j e)` is positive, and `η` is positive on it.
  have he0 : e ≠ 0 := by
    rintro rfl
    exact he (map_zero _)
  set b₀ := basisOfLinearIndependentOfCardEqFinrank
    ((j.almostComplexStructureAt c).linearIndependent_pair he0)
    (by simpa using (o.finrank_tangentSpace_eq c).symm)
  have hb₀ : ⇑b₀ = ![e, j c e] := by
    rw [coe_basisOfLinearIndependentOfCardEqFinrank, almostComplexStructureAt_apply]
  have hpos : 0 < η c b₀ := by
    rw [hb₀, hη]
    positivity
  refine (integralTopForm_pos o (hα.continuous_mextDeriv.smul (-1))
    (isClosed_tsupport _).isCompact
    (fun c' b hb ↦ j.apply_basis_nonneg_of_forall_nonneg (ho c')
      (fun e' ↦ (hη c' e').symm ▸ by positivity) b hb)
    ⟨c, b₀, ho c b₀ (by rw [hb₀]; simp), hpos⟩).ne' hint

end SmoothAlmostComplexStructure

end TauCeti
