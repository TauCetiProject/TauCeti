/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.Suspension
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Periodic tori in symplectic suspensions

A periodic point `x` of a diffeomorphism `φ`, with positive period `d`, determines the torus
`(s, t) ↦ (s, [t, x])` in `(ℝ / ℤ) × Y_φ`. For a `C^n` diffeomorphism with `1 ≤ n` of a
finite-dimensional boundaryless fiber manifold it is a `C^n` immersion, and is an embedding
exactly when `d` is the least period of `x`. Its image is the product of the independent
time circle with the closed suspension orbit, so changing the starting point along the
periodic orbit does not change this image.

The pullback of `Ω = ds ∧ dt + σ_v` is `ds ∧ dt`, while the pullback of the fiber form is zero.
These identities hold for every invariant two-form `σ`; neither its nondegeneracy nor
compactness of the fiber manifold is needed. The area integral over the fundamental
parameter rectangle `[0, 1] × [0, d]` is `d`, with the order `ds ∧ dt` fixing the sign.

## References

* E. Ionel and T. Parker, *Gromov invariants and symplectic maps*, Mathematische Annalen
  314 (1999), 127–158 (tori associated to periodic orbits).
* M. Hutchings and M. Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (the suspension form and closed orbits).
-/

public noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}
  (φ : M ≃ₘ^n⟮I, I⟯ M) {d : ℕ} {x : M}

/-- The torus over a periodic suspension orbit, parametrized by the independent unit circle
and the orbit's period circle. A nonminimal period traverses the same image several times. -/
def periodicTorus (hx : IsPeriodicPt φ d x) :
    UnitAddCircle × AddCircle (d : ℝ) → UnitAddCircle × SmoothMappingTorus φ :=
  Prod.map id (closedOrbit φ hx)

variable {φ} (hx : IsPeriodicPt φ d x)

/-- The periodic torus preserves the first circle and follows the closed orbit in the second
factor. -/
@[simp]
theorem periodicTorus_apply (p : UnitAddCircle × AddCircle (d : ℝ)) :
    periodicTorus φ hx p = (p.1, closedOrbit φ hx p.2) := (rfl)

/-- The image is the product of the independent time circle with the closed suspension orbit. -/
theorem range_periodicTorus :
    range (periodicTorus φ hx) = univ ×ˢ range (closedOrbit φ hx) := by
  rw [periodicTorus, range_prodMap, range_id]

/-- Changing the starting point along the periodic orbit rotates the second parameter. -/
theorem periodicTorus_apply_iterate (j : ℕ) (p : UnitAddCircle × AddCircle (d : ℝ)) :
    periodicTorus φ (hx.apply_iterate j) p = periodicTorus φ hx (p.1, p.2 + (j : ℝ)) := by
  simp only [periodicTorus_apply]
  exact congrArg (p.1, ·) (closedOrbit_apply_iterate hx j p.2)

/-- All starting points on one periodic orbit determine the same torus image. -/
theorem range_periodicTorus_apply_iterate (j : ℕ) :
    range (periodicTorus φ (hx.apply_iterate j)) = range (periodicTorus φ hx) := by
  rw [range_periodicTorus, range_periodicTorus, range_closedOrbit_apply_iterate]

section Manifold

variable [IsManifold I n M] [T2Space M] [LocallyCompactSpace M] [Fact (0 < (d : ℝ))]

/-- The periodic torus is `C^n` for every positive period. -/
theorem contMDiff_periodicTorus :
    ContMDiff (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) n (periodicTorus φ hx) :=
  contMDiff_id.prodMap (contMDiff_closedOrbit hx)

/-- Every positive period gives an immersed torus, even when it is not the least period. -/
theorem isImmersion_periodicTorus [I.Boundaryless] [FiniteDimensional ℝ E] (hn : 1 ≤ n) :
    IsImmersion (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) n
      (periodicTorus φ hx) :=
  IsImmersion.id.prodMap (isImmersion_closedOrbit hx hn)

/-- The periodic torus is a smooth embedding exactly when its period is the least period.
The fiber manifold need not be compact. -/
theorem isSmoothEmbedding_periodicTorus_iff [I.Boundaryless] [FiniteDimensional ℝ E]
    (hn : 1 ≤ n) :
    IsSmoothEmbedding (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) n
      (periodicTorus φ hx) ↔ minimalPeriod φ x = d := by
  constructor
  · intro h
    apply (injective_closedOrbit_iff hx).1
    intro t u htu
    have hh : periodicTorus φ hx ((0 : UnitAddCircle), t) = periodicTorus φ hx (0, u) :=
      congrArg ((0 : UnitAddCircle), ·) htu
    exact congrArg Prod.snd (h.isEmbedding.injective hh)
  · intro hd
    exact IsSmoothEmbedding.id.prodMap ((isSmoothEmbedding_closedOrbit_iff hx hn).2 hd)

end Manifold

section Smooth

variable [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  {φ : M ≃ₘ⟮I, I⟯ M} (hx : IsPeriodicPt φ d x) [Fact (0 < (d : ℝ))]

/-- The tangent map preserves the independent time direction and sends the orbit direction
to the suspension vector field. -/
theorem mfderiv_periodicTorus (p : UnitAddCircle × AddCircle (d : ℝ))
    (v : ℝ × ℝ) :
    mfderiv (𝓘(ℝ).prod 𝓘(ℝ)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (periodicTorus φ hx) p v =
      (Manifold.tangentSpaceProdEquiv _).symm
        (v.1, v.2 • timeVectorField φ (closedOrbit φ hx p.2)) := by
  have hγ : mfderiv 𝓘(ℝ) (𝓘(ℝ).prod I) (closedOrbit φ hx) p.2 v.2 =
      v.2 • timeVectorField φ (closedOrbit φ hx p.2) := by
    have h := congrArg (fun L : ℝ →L[ℝ] TangentSpace (𝓘(ℝ).prod I)
      (closedOrbit φ hx p.2) ↦ L v.2) (mfderiv_closedOrbit hx p.2)
    simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self] at h
    convert! h using 1
  have h := Manifold.mfderiv_prodMap_apply (I := 𝓘(ℝ)) (J := 𝓘(ℝ))
    (I' := 𝓘(ℝ)) (J' := 𝓘(ℝ).prod I) (f := id) (g := closedOrbit φ hx) (p := p)
    mdifferentiableAt_id ((contMDiff_closedOrbit hx).mdifferentiableAt (by simp))
    ((v.1 : ℝ), (v.2 : ℝ))
  -- The source circle tangent spaces are the real model lines.
  erw [Manifold.tangentSpaceProdEquiv_symm_apply] at h
  simp only [mfderiv_id, hγ] at h
  convert! h using 1

variable {σ : SmoothTwoForm I M} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

/-- The fiber two-form vanishes on the periodic torus: both of its mapping-torus tangent
components are multiples of the suspension vector field. -/
@[simp]
theorem mpullback_periodicTorus_fiberForm :
    SmoothForm.mpullback (periodicTorus φ hx) (contMDiff_periodicTorus hx)
      (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ)) = 0 := by
  apply SmoothBundleForm.ext_eval₂
  intro p v w
  rw [SmoothForm.eval₂_mpullback]
  -- Circle tangent spaces are the real model lines; `erw` unfolds their type synonyms.
  erw [mfderiv_periodicTorus, mfderiv_periodicTorus,
    SmoothForm.eval₂_mpullback_snd]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  erw [SmoothBundleForm.eval₂_smul_left, eval₂_fiberForm_timeVectorField_left]
  rw [SmoothBundleForm.eval₂_apply]
  simp

/-- The suspension form on a periodic torus is the standard area form, with the independent
time direction first. -/
theorem mpullback_periodicTorus_suspensionForm :
    SmoothForm.mpullback (periodicTorus φ hx) (contMDiff_periodicTorus hx)
        (suspensionForm φ σ hσ) =
      SmoothForm.wedge (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm 1))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm (d : ℝ))) := by
  apply SmoothBundleForm.ext_eval₂
  intro p v w
  have htime (c : ℝ) :
      (timeForm φ).1 (closedOrbit φ hx p.2)
        ![c • timeVectorField φ (closedOrbit φ hx p.2)] = c := by
    simp only [timeForm_apply, Matrix.cons_val_zero, map_smul]
    rw [mfderiv_proj_timeVectorField]
    exact mul_one c
  rw [SmoothForm.eval₂_mpullback]
  -- Circle tangent spaces are the real model lines; `erw` unfolds their type synonyms.
  erw [mfderiv_periodicTorus, mfderiv_periodicTorus,
    eval₂_suspensionForm, SmoothForm.eval₂_wedge_one_one]
  simp only [ContinuousLinearEquiv.apply_symm_apply]
  erw [htime, htime, SmoothBundleForm.eval₂_smul_left,
    eval₂_fiberForm_timeVectorField_left]
  simp only [smul_zero, add_zero, SmoothForm.mpullback_fst_apply,
    SmoothForm.mpullback_snd_apply, AddCircle.timeForm_apply]
  erw [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_apply]
  rfl

/-- Evaluation of the pulled-back suspension form in the circle's real tangent coordinates is
the determinant `v₁ w₂ - w₁ v₂`. -/
theorem eval₂_mpullback_periodicTorus_suspensionForm
    (p : UnitAddCircle × AddCircle (d : ℝ)) (v w : ℝ × ℝ) :
    (SmoothForm.mpullback (periodicTorus φ hx) (contMDiff_periodicTorus hx)
      (suspensionForm φ σ hσ)).eval₂ p v w =
        v.1 * w.2 - w.1 * v.2 := by
  rw [mpullback_periodicTorus_suspensionForm]
  -- Read the circle tangent spaces in their real model coordinates.
  erw [SmoothForm.eval₂_wedge_one_one]
  simp only [SmoothForm.mpullback_fst_apply, SmoothForm.mpullback_snd_apply,
    AddCircle.timeForm_apply]
  erw [Manifold.tangentSpaceProdEquiv_apply, Manifold.tangentSpaceProdEquiv_apply]
  rfl

/-- The signed area integral of the actual pulled-back form over one fundamental parameter
rectangle is the period `d`. The tangent vectors are the positive real time directions on
the two circles. -/
theorem integral_periodicTorus_suspensionForm :
    (∫ s : ℝ in 0..1, ∫ t : ℝ in 0..(d : ℝ),
      (SmoothForm.mpullback (periodicTorus φ hx) (contMDiff_periodicTorus hx)
        (suspensionForm φ σ hσ)).eval₂ ((s : UnitAddCircle), (t : AddCircle (d : ℝ)))
          ((1 : ℝ), (0 : ℝ)) ((0 : ℝ), (1 : ℝ))) = d := by
  simp [eval₂_mpullback_periodicTorus_suspensionForm]

end Smooth

end TauCeti.SmoothMappingTorus
