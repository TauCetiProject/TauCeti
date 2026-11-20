/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Integration.AddCircle
public import TauCeti.Geometry.Manifold.DifferentialForm.MappingTorus.Iterate
public import TauCeti.Geometry.Manifold.LocalDiffeomorph.Prod.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Suspension.Basic

/-!
# The suspension form under integer iterates

Let `φ : M ≃ₘ⟮I, I⟯ M` be a diffeomorphism preserving a two-form `σ`, and let
`Ω = ds ∧ dt + σ_v` be the suspension form on `X_φ = (ℝ / ℤ)_s × Y_φ`
(`TauCeti.SmoothMappingTorus.suspensionForm`). For an integer `k`, the natural map
`Y_(φ^k) → Y_φ`, `[t, x] ↦ [k t, x]` (`TauCeti.SmoothMappingTorus.iterateMap`), induces the map
`(s, y) ↦ (s, iterateMap φ k y)` from `X_(φ^k)` to `X_φ`. This file records how `Ω` and the areas
of orbit tori behave under it.

The iterate map multiplies the time form by `k` and preserves the fiber form, so this map pulls
`Ω` back to `ds ∧ k dt + σ_v` on `X_(φ^k)`, rather than to the suspension form of `φ ^ k`. For
`k ≠ 0` it is a surjective local diffeomorphism, so this rescaled form is symplectic exactly when
`σ` is.

A point `x` of positive period `d` for `φ ^ k` has period `k.natAbs * d` for `φ`. The map sends the
orbit torus of `φ ^ k` through `x` to the orbit torus of `φ` through `x`, precomposed with the
rescaling `[t] ↦ [k t]` of the second parameter circle
(`TauCeti.SmoothMappingTorus.prodMap_iterateMap_comp_orbitTorus`). The `Ω`-area of the composite
is the signed number `k * d`: the area `k.natAbs * d` of the orbit torus of `φ` through `x`, with
the sign of `k` from the orientation of the rescaling. Its `σ_v`-area is zero. The same sign
`k.sign` appears in the integral classes
(`TauCeti.SmoothMappingTorus.singularHomologyMap_prodMap_iterateMap_orbitTorusHomologyClass`).
No nondegeneracy of `σ` and no compactness of `M` are needed for the area formulas.

## Main results

* `TauCeti.SmoothMappingTorus.mpullback_prodMap_iterateMap_suspensionForm`: the map pulls `Ω`
  back to `ds ∧ k dt + σ_v`.
* `TauCeti.SmoothMappingTorus.isSymplectic_smul_wedge_timeForm_add_fiberForm_iff`: for `k ≠ 0`,
  the form `ds ∧ k dt + σ_v` on `X_(φ^k)` is symplectic exactly when `σ` is.
* `SmoothMappingTorus.integralTopForm_mpullback_prodMap_iterateMap_comp_orbitTorus_suspensionForm`:
  the `Ω`-area of the image of an orbit torus of `φ ^ k` with period `d` is `k * d`.
  The underlying pullback of `Ω` is
  `SmoothMappingTorus.mpullback_prodMap_iterateMap_comp_orbitTorus_suspensionForm`.
* `SmoothMappingTorus.integralTopForm_mpullback_prodMap_iterateMap_comp_orbitTorus_fiberForm`:
  its `σ_v`-area is zero.

## References

* M. Hutchings and M. Sullivan, *The periodic Floer homology of a Dehn twist*, Algebraic
  & Geometric Topology 5 (2005), 301–354, Section 2 (the suspension form and the multiple covers of
  closed orbits).
-/

public noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  (φ : M ≃ₘ⟮I, I⟯ M) (k : ℤ) {σ : SmoothTwoForm I M}
  (hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ)

/-- The map `(s, y) ↦ (s, iterateMap φ k y)` from `(ℝ / ℤ) × Y_(φ^k)` to `(ℝ / ℤ) × Y_φ` pulls the
form `Ω = ds ∧ dt + σ_v` back to `ds ∧ k dt + σ_v`. The time form of `Y_φ` pulls back to `k` times
the time form of `Y_(φ^k)`, while the fiber form of `σ` has no rescaling factor. -/
theorem mpullback_prodMap_iterateMap_suspensionForm :
    SmoothForm.mpullback (Prod.map id (iterateMap φ k))
        (contMDiff_id.prodMap (contMDiff_iterateMap φ k)) (suspensionForm φ σ hσ) =
      (k : ℝ) • SmoothForm.wedge
          (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm 1))
          (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm (φ ^ k))) +
        SmoothForm.mpullback Prod.snd contMDiff_snd
          (fiberForm (φ ^ k) σ (SmoothForm.mpullback_zpow_eq_self hσ k)) := by
  have hm := contMDiff_iterateMap φ k
  -- `rw [map_add]` is slow here: the wedge `ds ∧ dt` has degree `1 + 1`, while `Ω` has degree `2`.
  refine (congrArg _ suspensionForm_def).trans ((map_add _ _ _).trans (congrArg₂ (· + ·) ?_
    (by rw [SmoothForm.mpullback_prodMap_mpullback_snd contMDiff_id hm,
      mpullback_iterateMap_fiberForm])))
  refine (SmoothForm.mpullback_prodMap_wedge_mpullback_fst_snd (k := 1) (l := 1) contMDiff_id hm
    _ _).trans ?_
  simp only [SmoothForm.mpullback_id, LinearMap.id_apply, mpullback_iterateMap_timeForm, map_smul]

/-- For a nonzero integer `k`, the form `ds ∧ k dt + σ_v` on `(ℝ / ℤ) × Y_(φ^k)` is symplectic
exactly when `σ` is. It is the pullback of the suspension form `Ω` of `φ` along the surjective
local diffeomorphism `(s, y) ↦ (s, iterateMap φ k y)`. -/
theorem isSymplectic_smul_wedge_timeForm_add_fiberForm_iff (hk : k ≠ 0) :
    ((k : ℝ) • SmoothForm.wedge
          (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm 1))
          (SmoothForm.mpullback Prod.snd contMDiff_snd (timeForm (φ ^ k))) +
        SmoothForm.mpullback Prod.snd contMDiff_snd
          (fiberForm (φ ^ k) σ (SmoothForm.mpullback_zpow_eq_self hσ k)) :
      SmoothTwoForm (𝓘(ℝ).prod (𝓘(ℝ).prod I))
        (UnitAddCircle × SmoothMappingTorus (φ ^ k))).IsSymplectic ↔ σ.IsSymplectic := by
  have hf : IsLocalDiffeomorph (𝓘(ℝ).prod (𝓘(ℝ).prod I)) (𝓘(ℝ).prod (𝓘(ℝ).prod I)) ∞
      (Prod.map id (iterateMap φ k)) :=
    IsLocalDiffeomorph.prodMap (Diffeomorph.refl 𝓘(ℝ) UnitAddCircle ∞).isLocalDiffeomorph
      (isLocalDiffeomorph_iterateMap φ k hk)
  rw [← mpullback_prodMap_iterateMap_suspensionForm φ k hσ,
    hf.isSymplectic_mpullback_iff (surjective_id.prodMap (iterateMap_surjective φ k hk)),
    isSymplectic_suspensionForm_iff]

variable {d : ℕ} {x : M} (hx : IsPeriodicPt (φ ^ k) d x) [Fact (0 < (d : ℝ))]

/-- The map `(s, y) ↦ (s, iterateMap φ k y)` pulls the form `Ω` of `φ` back along the orbit torus of
`φ ^ k` through a point `x` of period `d` to `k ds ∧ dt_d`. -/
theorem mpullback_prodMap_iterateMap_comp_orbitTorus_suspensionForm :
    SmoothForm.mpullback (Prod.map id (iterateMap φ k) ∘ orbitTorus (φ ^ k) hx)
        ((contMDiff_id.prodMap (contMDiff_iterateMap φ k)).comp (contMDiff_orbitTorus hx))
        (suspensionForm φ σ hσ) =
      (k : ℝ) • SmoothForm.wedge
        (SmoothForm.mpullback Prod.fst contMDiff_fst (AddCircle.timeForm 1))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (AddCircle.timeForm (d : ℝ))) := by
  rw [← SmoothForm.mpullback_mpullback _ _ (contMDiff_orbitTorus hx)
      (contMDiff_id.prodMap (contMDiff_iterateMap φ k)),
    mpullback_prodMap_iterateMap_suspensionForm, map_add,
    map_smul, mpullback_orbitTorus_mpullback_snd_fiberForm hx two_ne_zero, add_zero]
  exact congrArg ((k : ℝ) • ·) (mpullback_orbitTorus_wedge_timeForm hx)

/-- **The `Ω`-area of an iterated orbit torus.** Orient the parameter torus `(ℝ / ℤ) × (ℝ / dℤ)`
as the product of the positive orientations of its two circles, the `s`-direction first. For a
point `x` of positive period `d` for `φ ^ k`, the image of the orbit torus of `φ ^ k` through `x`
under `(s, y) ↦ (s, iterateMap φ k y)` has `Ω`-area `k * d`. It is the orbit torus of `φ` through
`x`, of period `k.natAbs * d`, reparametrized by `[t] ↦ [k t]`, which reverses orientation exactly
when `k` is negative. -/
theorem integralTopForm_mpullback_prodMap_iterateMap_comp_orbitTorus_suspensionForm :
    integralTopForm ((AddCircle.orientation (1 : ℝ)).prod (AddCircle.orientation (d : ℝ)))
      (SmoothForm.mpullback (Prod.map id (iterateMap φ k) ∘ orbitTorus (φ ^ k) hx)
        ((contMDiff_id.prodMap (contMDiff_iterateMap φ k)).comp (contMDiff_orbitTorus hx))
        (suspensionForm φ σ hσ)).val = k * d := by
  rw [mpullback_prodMap_iterateMap_comp_orbitTorus_suspensionForm, Submodule.coe_smul,
    integralTopForm_smul, AddCircle.integralTopForm_wedge_timeForm, one_mul]

/-- The fiber form `σ_v` of `φ` has zero area on the image of an orbit torus of `φ ^ k` under
`(s, y) ↦ (s, iterateMap φ k y)`, for every orientation of the parameter torus. -/
theorem integralTopForm_mpullback_prodMap_iterateMap_comp_orbitTorus_fiberForm
    (o : Manifold.Orientation (𝓘(ℝ).prod 𝓘(ℝ)) (UnitAddCircle × AddCircle (d : ℝ)) (Fin 2)) :
    integralTopForm o
      (SmoothForm.mpullback (Prod.map id (iterateMap φ k) ∘ orbitTorus (φ ^ k) hx)
        ((contMDiff_id.prodMap (contMDiff_iterateMap φ k)).comp (contMDiff_orbitTorus hx))
        (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ σ hσ))).val = 0 := by
  rw [← SmoothForm.mpullback_mpullback _ _ (contMDiff_orbitTorus hx)
      (contMDiff_id.prodMap (contMDiff_iterateMap φ k)),
    SmoothForm.mpullback_prodMap_mpullback_snd contMDiff_id (contMDiff_iterateMap φ k),
    mpullback_iterateMap_fiberForm, mpullback_orbitTorus_mpullback_snd_fiberForm hx two_ne_zero]
  exact integralTopForm_zero o

end TauCeti.SmoothMappingTorus
