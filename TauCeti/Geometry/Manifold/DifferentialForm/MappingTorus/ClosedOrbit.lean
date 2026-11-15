/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.MappingTorus
public import TauCeti.Geometry.Manifold.Instances.MappingTorus.ClosedOrbit

/-!
# The time form and fiber forms on closed orbits of the suspension flow

For a point `x` of period `d` of a diffeomorphism `φ`, the closed orbit
`γ : ℝ / dℤ → Y_φ`, `[t] ↦ [t, x]` (`TauCeti.SmoothMappingTorus.closedOrbit`), of the suspension
flow pulls the time form `dt` of the mapping torus back to the time form `dt_d` of the circle
`ℝ / dℤ`, so one circuit of `γ` has `dt`-length `d`, while every fiber form of positive degree
vanishes on `γ`. These fiber forms also vanish on the orbit torus `(s, θ) ↦ (s, γ θ)`
(`TauCeti.SmoothMappingTorus.orbitTorus`) after pullback from the mapping torus to its product
with a second circle.

## Main results

* `TauCeti.SmoothMappingTorus.mpullback_closedOrbit_timeForm`,
  `TauCeti.SmoothMappingTorus.mpullback_closedOrbit_fiberForm`: the closed orbit through a point
  of period `d` pulls `dt` back to `dt_d` and every fiber form of positive degree back to zero.
* `TauCeti.SmoothMappingTorus.mpullback_orbitTorus_mpullback_snd_fiberForm`: every fiber form
  of positive degree, pulled back to `(ℝ / ℤ) × Y_φ`, vanishes on the orbit torus.
-/

public section

noncomputable section

open Function
open scoped Manifold ContDiff

namespace TauCeti.SmoothMappingTorus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [LocallyCompactSpace M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}
  {φ : M ≃ₘ⟮I, I⟯ M} {σ : SmoothForm I M F k} {hσ : SmoothForm.mpullback φ φ.contMDiff σ = σ}

variable {d : ℕ} {x : M} (h : IsPeriodicPt φ d x) [Fact (0 < (d : ℝ))]

/-- Pulling a form back along the closed orbit and then the circle quotient is the same as
restricting its pullback to `ℝ × M` to the line through `(0, x)`. -/
private theorem mpullback_coe_mpullback_closedOrbit
    (β : SmoothForm (𝓘(ℝ).prod I) (SmoothMappingTorus φ) F k) :
    SmoothForm.mpullback ((↑) : ℝ → AddCircle (d : ℝ)) (AddCircle.contMDiff_coe (d : ℝ) ∞)
        (SmoothForm.mpullback (closedOrbit φ h) (contMDiff_closedOrbit h) β) =
      SmoothForm.mpullback (fun t : ℝ ↦ (t, x)) (contMDiff_id.prodMk contMDiff_const)
        (SmoothForm.mpullback (uncurry (mk φ)) (contMDiff_uncurry_mk φ) β) := by
  have hcomp : closedOrbit φ h ∘ ((↑) : ℝ → AddCircle (d : ℝ)) =
      uncurry (mk φ) ∘ fun t ↦ (t, x) := funext fun t ↦ closedOrbit_coe h t
  simp only [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp, hcomp]

/-- The time form pulls back along the closed orbit `γ : ℝ / dℤ → Y_φ` through a point of period
`d` to the time form `dt_d` of the circle `ℝ / dℤ`. -/
@[simp]
theorem mpullback_closedOrbit_timeForm :
    SmoothForm.mpullback (closedOrbit φ h) (contMDiff_closedOrbit h) (timeForm φ) =
      AddCircle.timeForm (d : ℝ) := by
  have hline : ContMDiff 𝓘(ℝ) (𝓘(ℝ).prod I) ∞ fun t : ℝ ↦ (t, x) :=
    contMDiff_id.prodMk contMDiff_const
  refine Subtype.ext (AddCircle.mpullback_coe_injective (d : ℝ) ?_)
  have hfst : Prod.fst ∘ (fun t : ℝ ↦ (t, x)) = id := rfl
  rw [← SmoothForm.coe_mpullback _ (AddCircle.contMDiff_coe (d : ℝ) ∞),
    mpullback_coe_mpullback_closedOrbit h]
  simp only [SmoothForm.coe_mpullback]
  rw [mpullback_uncurry_mk_timeForm,
    ← mpullback_comp (hline.mdifferentiable (by simp)) mdifferentiable_fst,
    hfst, mpullback_id, AddCircle.mpullback_coe_timeForm]

/-- Every fiber form of positive degree vanishes on the closed orbit `γ : ℝ / dℤ → Y_φ` through a
point of period `d`: the pullback of `σ_v` along `γ` is zero. -/
@[simp]
theorem mpullback_closedOrbit_fiberForm (hk : k ≠ 0) :
    SmoothForm.mpullback (closedOrbit φ h) (contMDiff_closedOrbit h) (fiberForm φ σ hσ) = 0 := by
  have hline : ContMDiff 𝓘(ℝ) (𝓘(ℝ).prod I) ∞ fun t : ℝ ↦ (t, x) :=
    contMDiff_id.prodMk contMDiff_const
  refine Subtype.ext (AddCircle.mpullback_coe_injective (d : ℝ) ?_)
  have hsnd : Prod.snd ∘ (fun t : ℝ ↦ (t, x)) = fun _ ↦ x := rfl
  rw [← SmoothForm.coe_mpullback _ (AddCircle.contMDiff_coe (d : ℝ) ∞),
    mpullback_coe_mpullback_closedOrbit h, mpullback_uncurry_mk_fiberForm]
  simp only [SmoothForm.coe_mpullback, ZeroMemClass.coe_zero, mpullback_zero]
  rw [← mpullback_comp (hline.mdifferentiable (by simp)) mdifferentiable_snd, hsnd]
  -- The constant map `t ↦ x` has derivative zero, and a form of positive degree vanishes on
  -- zero vectors.
  funext t
  refine ContinuousAlternatingMap.ext fun v ↦ ?_
  rw [TauCeti.mpullback_apply, mfderiv_const, Pi.zero_apply, ContinuousAlternatingMap.coe_zero,
    Pi.zero_apply]
  exact (σ.1 x).map_coord_zero ⟨0, Nat.pos_of_ne_zero hk⟩ (zero_apply _)

/-- Every fiber form of positive degree, pulled back to `(ℝ / ℤ) × Y_φ`, vanishes on the orbit
torus. -/
@[simp]
theorem mpullback_orbitTorus_mpullback_snd_fiberForm {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {k : ℕ} {τ : SmoothForm I M F k}
    {hτ : SmoothForm.mpullback φ φ.contMDiff τ = τ} (hk : k ≠ 0) :
    SmoothForm.mpullback (orbitTorus φ h) (contMDiff_orbitTorus h)
        (SmoothForm.mpullback Prod.snd contMDiff_snd (fiberForm φ τ hτ)) = 0 := by
  have hsnd : Prod.snd ∘ orbitTorus φ h = closedOrbit φ h ∘ Prod.snd :=
    funext fun p ↦ congrArg Prod.snd (orbitTorus_apply h p)
  rw [← LinearMap.comp_apply, ← SmoothForm.mpullback_comp]
  simp only [hsnd]
  rw [SmoothForm.mpullback_comp _ _ contMDiff_snd (contMDiff_closedOrbit h), LinearMap.comp_apply,
    mpullback_closedOrbit_fiberForm h hk, map_zero]

end TauCeti.SmoothMappingTorus
