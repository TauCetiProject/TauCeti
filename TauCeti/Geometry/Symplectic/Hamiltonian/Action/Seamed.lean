/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Seamed
public import TauCeti.Geometry.Symplectic.Hamiltonian.Action.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.LoopVariation
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Variation
import TauCeti.Geometry.Manifold.MFDeriv.Curve

/-!
# The Hamiltonian action of seamed paths

Let `σ` be a two-form on a manifold `M`, `f : M → M` a map and `H : ℝ → M → ℝ` a time-dependent
Hamiltonian. The Floer theory of a symplectomorphism `f` replaces the loops of Hamiltonian Floer
theory by `f`-seamed paths, paths `γ` on `[0, 1]` with `γ 1 = f (γ 0)` (`TauCeti.SeamedPath`), and
its action functional measures a seamed path `γ` against a smooth `f`-seamed cylinder `u` from `γ`
to a reference seamed path `γ₀` (`TauCeti.IsSmoothSeamedCylinder`):

`𝒜_H(γ, u) = ∫ u^* σ - ∫₀¹ H(t, γ(t)) dt`,

which is `TauCeti.cylinderAction σ H u`, the action of the loop case measured against a seamed
cylinder. Its gluing and recapping laws (`TauCeti.cylinderAction_rectangleTrans`,
`TauCeti.cylinderAction_sub_cylinderAction`) hold for arbitrary maps of the plane, and so apply to
seamed cylinders as they stand. This file adds what depends on the seam.

* **Homotopy invariance.** When `σ` is closed and `f` preserves it, `f^* σ = σ`, the action does
  not change along a homotopy of seamed cylinders relative to their end paths
  (`TauCeti.cylinderAction_eq_of_seamedHomotopy`, in
  `TauCeti.Geometry.Symplectic.Hamiltonian.Action.Basic`): the two sides of the homotopy swept out
  by the seam carry the same area. So the action only depends on the homotopy class of the
  reference cylinder.
* **The action relative to a reference path.** When `σ` vanishes on `f`-seamed tori
  (`TauCeti.VanishesOnSeamedTori`), the action does not depend on the seamed cylinder, and defines
  the action `TauCeti.SmoothTwoForm.seamedReferenceAction σ f H γ₀ γ` of a seamed path `γ` relative
  to `γ₀` (`TauCeti.SmoothTwoForm.seamedReferenceAction_eq`). For `f = id` it is the action
  `TauCeti.SmoothTwoForm.referenceAction` relative to a reference loop
  (`TauCeti.SmoothTwoForm.seamedReferenceAction_id`). This happens for an exact symplectomorphism
  of an exact form (`TauCeti.vanishesOnSeamedTori_mextDeriv`); in general the action is measured
  against reference seamed cylinders on the reference-cylinder cover of the space of seamed paths
  (`TauCeti.Floer.ReferenceCylinderCover`).
* **The first variation formula.** Along a smooth variation `w` through `f`-seamed paths,
  `w (s, 1) = f (w (s, 0))`, the action relative to `γ₀` has derivative
  `∫₀¹ σ(∂_t w - X_{H_t}(w), ∂_s w) dt`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_seamedReferenceAction`), for Hamiltonian
  vector fields `ι_{X_{H_t}} σ = dH_t`, exactly as for loops: the area swept out by the variation
  is the only part of the action that moves.
* **Critical points.** A smooth seamed path joined to `γ₀` by a seamed cylinder is a critical point
  of the action (`TauCeti.SmoothTwoForm.IsSeamedReferenceActionCritical`) exactly when it solves
  `γ' = X_{H_t}(γ)` at the times `t ∈ (0, 1)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isSeamedReferenceActionCritical_iff`), on a manifold
  without boundary modelled on a finite-dimensional space. Unlike the loop case no periodicity
  of `H` in time is needed: the test variations are supported inside `(0, 1)`, away from the seam.
  In particular the seamed solutions of `X_H` (`TauCeti.seamedSolutions`), whose time-zero points
  are the fixed points of `f⁻¹ ∘ φ_H¹` and which generate the Floer complex of `f`, are critical
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isSeamedReferenceActionCritical_of_mem_seamedSolutions`).

## Main definitions

* `TauCeti.SmoothTwoForm.seamedReferenceAction σ f H γ₀ γ`: the action of the `f`-seamed path `γ`
  measured against a smooth `f`-seamed cylinder to `γ₀`, when one exists.
* `TauCeti.SmoothTwoForm.IsSeamedReferenceActionCritical σ f H γ₀ γ`: `γ` is a critical point of
  the action relative to `γ₀`.

## Main results

* `TauCeti.SmoothTwoForm.seamedReferenceAction_eq`: the action relative to `γ₀` is the action
  measured against any seamed cylinder to `γ₀`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.hasDerivAt_seamedReferenceAction`: the first variation
  formula.
* `TauCeti.SmoothTwoForm.IsNondegenerate.isSeamedReferenceActionCritical_iff`: the critical points
  of the action are the seamed paths solving the Hamiltonian equation on `(0, 1)`.

## References

* A. Floer, *Symplectic fixed points and holomorphic spheres*, Comm. Math. Phys. 120 (1989),
  575–611.
* Y.-J. Lee, *Reidemeister torsion in Floer–Novikov theory and counting pseudo-holomorphic tori,
  I*, J. Symplectic Geom. 3 (2005), 221–311, §3.1.
-/

public section

noncomputable section

open Function Set
open scoped Manifold Interval ContDiff Topology

namespace TauCeti

variable {E H' M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H'} [TopologicalSpace M] [ChartedSpace H' M] {f : M → M}

namespace SmoothTwoForm

variable [IsManifold I ∞ M] {σ : SmoothTwoForm I M} {H : ℝ → M → ℝ} {γ γ₀ : ℝ → M}
  {u : ℝ × ℝ → M} {w : ℝ × ℝ → M}

/-! ### The action relative to a reference seamed path -/

/-- **Independence of the seamed cylinder.** If `σ` vanishes on `f`-seamed tori, the action of an
`f`-seamed path is the same measured against any two smooth `f`-seamed cylinders to the same
reference path. -/
theorem cylinderAction_eq_of_vanishesOnSeamedTori (hT : VanishesOnSeamedTori f σ.val)
    {v : ℝ × ℝ → M} (hu : IsSmoothSeamedCylinder I f γ γ₀ u)
    (hv : IsSmoothSeamedCylinder I f γ γ₀ v) :
    cylinderAction σ.val H u = cylinderAction σ.val H v := by
  rw [cylinderAction_def, cylinderAction_def, hT.rectangleIntegral_eq
    (σ.isSmoothForm.of_le (by simp)) hu hv]
  simp only [hu.apply_zero, hv.apply_zero]

open Classical in
/-- The Hamiltonian action of an `f`-seamed path `γ` relative to the reference `f`-seamed path
`γ₀`, measured against a smooth `f`-seamed cylinder from `γ` to `γ₀`; it is `0` when there is no
such cylinder. When `σ` vanishes on `f`-seamed tori it does not depend on the cylinder
(`TauCeti.SmoothTwoForm.seamedReferenceAction_eq`). -/
def seamedReferenceAction (σ : SmoothTwoForm I M) (f : M → M) (H : ℝ → M → ℝ) (γ₀ γ : ℝ → M) :
    ℝ :=
  if h : ∃ u : ℝ × ℝ → M, IsSmoothSeamedCylinder I f γ γ₀ u then
    cylinderAction σ.val H h.choose
  else 0

/-- If `σ` vanishes on `f`-seamed tori, the action of an `f`-seamed path relative to `γ₀` is its
action measured against any smooth `f`-seamed cylinder to `γ₀`. -/
theorem seamedReferenceAction_eq (hT : VanishesOnSeamedTori f σ.val)
    (hu : IsSmoothSeamedCylinder I f γ γ₀ u) :
    σ.seamedReferenceAction f H γ₀ γ = cylinderAction σ.val H u := by
  have h : ∃ u : ℝ × ℝ → M, IsSmoothSeamedCylinder I f γ γ₀ u := ⟨u, hu⟩
  simp only [seamedReferenceAction, h, ↓reduceDIte]
  exact cylinderAction_eq_of_vanishesOnSeamedTori hT h.choose_spec hu

/-- The action of a path relative to `γ₀` is `0` when there is no smooth `f`-seamed cylinder to
`γ₀`. -/
@[simp]
theorem seamedReferenceAction_eq_zero_of_not_exists
    (h : ¬∃ u : ℝ × ℝ → M, IsSmoothSeamedCylinder I f γ γ₀ u) :
    σ.seamedReferenceAction f H γ₀ γ = 0 :=
  dite_eq_right h

/-- If `σ` vanishes on `f`-seamed tori, a smooth `f`-seamed reference path `γ₀` has action
`-∫₀¹ H(t, γ₀(t)) dt` relative to itself. -/
@[simp]
theorem seamedReferenceAction_self (hT : VanishesOnSeamedTori f σ.val)
    (hγ₀ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ₀) (hseam : γ₀ 1 = f (γ₀ 0)) :
    σ.seamedReferenceAction f H γ₀ γ₀ = -∫ t in 0..1, H t (γ₀ t) := by
  have hc : IsSmoothSeamedCylinder I f γ₀ γ₀ (γ₀ ∘ Prod.snd) :=
    ⟨hγ₀.comp contDiff_snd.contMDiff, fun _ ↦ rfl, fun _ _ ↦ rfl, fun _ _ ↦ hseam⟩
  rw [seamedReferenceAction_eq hT hc, cylinderAction_def, rectangleIntegral_comp_snd, zero_sub]
  simp only [comp_apply]

/-- **The seamed action for the identity is the action relative to a reference loop.** If `σ`
vanishes on tori, the action of a loop relative to `γ₀` measured against `id`-seamed cylinders is
`TauCeti.SmoothTwoForm.referenceAction`. -/
theorem seamedReferenceAction_id (hT : VanishesOnTori σ.val) :
    σ.seamedReferenceAction id H γ₀ γ = σ.referenceAction H γ₀ γ := by
  by_cases h : ∃ u : ℝ × ℝ → M, IsSmoothCylinder I γ γ₀ u
  · obtain ⟨u, hu⟩ := h
    rw [seamedReferenceAction_eq ((vanishesOnSeamedTori_id_iff _).mpr hT)
      (isSmoothSeamedCylinder_id_iff.mpr hu), referenceAction_eq hT hu]
  · rw [referenceAction_eq_zero_of_not_exists h, seamedReferenceAction_eq_zero_of_not_exists]
    simpa only [isSmoothSeamedCylinder_id_iff] using h

/-! ### The first variation formula -/

variable [FiniteDimensional ℝ E]

/-- **The first variation of the action of seamed paths.** Let `σ` be a nondegenerate two-form
vanishing on `f`-seamed tori, `H` a jointly `C¹` time-dependent Hamiltonian and `w` a smooth
variation through `f`-seamed paths, `w (s, 1) = f (w (s, 0))`, whose path `w (s₀, ·)` is joined
to the reference path `γ₀` by a smooth `f`-seamed cylinder. Then the action of the paths
`w (s, ·)` relative to `γ₀` has derivative `∫₀¹ σ(∂_t w - X_{H_t}(w), ∂_s w) dt` at `s₀`, with all
terms taken at `(s₀, t)`. -/
theorem IsNondegenerate.hasDerivAt_seamedReferenceAction (h : σ.IsNondegenerate)
    (hT : VanishesOnSeamedTori f σ.val) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ w) (hseam : ∀ s, w (s, 1) = f (w (s, 0))) {s₀ : ℝ}
    (hcyl : ∃ u, IsSmoothSeamedCylinder I f (fun t ↦ w (s₀, t)) γ₀ u) :
    HasDerivAt (fun s ↦ σ.seamedReferenceAction f H γ₀ fun t ↦ w (s, t))
      (∫ t in 0..1, σ.val (w (s₀, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (s₀, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I w (s₀, t) (1, 0)]) s₀ := by
  obtain ⟨u, hu⟩ := hcyl
  have hσ : IsSmoothForm I 0 σ.val := σ.isSmoothForm.of_le (by simp)
  have hw1 : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 w := hwc.of_le (by simp)
  -- the area term of the action of `w (s, ·)` is the area swept from `s` to `s₀` plus the area
  -- of `u`
  have heq : (fun s ↦ σ.seamedReferenceAction f H γ₀ fun t ↦ w (s, t)) = fun s ↦
      (rectangleIntegral σ.val (w ∘ Prod.map (fun r ↦ s + (s₀ - s) * r) id) (0, 0) (1, 1) +
        rectangleIntegral σ.val u (0, 0) (1, 1)) - ∫ t in 0..1, H t (w (s, t)) := by
    funext s
    -- the path `w (s, ·)` is joined to `γ₀` through the variation from `s` to `s₀`, then `u`
    have hcyl : IsSmoothSeamedCylinder I f (fun t ↦ w (s, t)) γ₀
        (rectangleTrans (w ∘ Prod.map (fun r ↦ s + (s₀ - s) * r) id) u) :=
      (isSmoothSeamedCylinder_comp_prodMap_affine hwc hseam s s₀).trans hu fun t ↦ by
        simp [hu.apply_zero]
    rw [seamedReferenceAction_eq hT hcyl,
      cylinderAction_rectangleTrans hσ H (hw1.comp (contMDiff_prodMap_affine s s₀))
        (hu.contMDiff.of_le (by simp)) fun t ↦ by simp [hu.apply_zero], cylinderAction_def]
    simp only [comp_apply, Prod.map_apply, mul_zero, add_zero, id_eq]
    ring
  rw [heq]
  exact h.hasDerivAt_sub_intervalIntegral hH hw1
    ((hasDerivAt_rectangleIntegral_comp_prodMap_affine hσ hw1 s₀ 0 1).add_const _)

/-! ### Critical points of the seamed action -/

/-- A path `γ` is a **critical point of the action of `f`-seamed paths relative to the reference
path** `γ₀` when it is a smooth path joined to `γ₀` by a smooth `f`-seamed cylinder, hence an
`f`-seamed path (`TauCeti.SmoothTwoForm.IsSeamedReferenceActionCritical.apply_one`), and, for
every smooth variation `w` through `f`-seamed paths starting at `γ`, the action
`𝒜_H(w (s, ·))` relative to `γ₀` has derivative `0` at `s = 0`. -/
structure IsSeamedReferenceActionCritical (σ : SmoothTwoForm I M) (f : M → M) (H : ℝ → M → ℝ)
    (γ₀ γ : ℝ → M) : Prop where
  /-- A critical path is smooth. -/
  contMDiff : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ
  /-- A critical path is joined to the reference path by a smooth seamed cylinder. -/
  exists_isSmoothSeamedCylinder : ∃ u, IsSmoothSeamedCylinder I f γ γ₀ u
  /-- The action is stationary along every variation through seamed paths. -/
  hasDerivAt : ∀ ⦃w : ℝ × ℝ → M⦄, ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ w →
    (∀ s, w (s, 1) = f (w (s, 0))) → (∀ t, w (0, t) = γ t) →
    HasDerivAt (fun s ↦ σ.seamedReferenceAction f H γ₀ fun t ↦ w (s, t)) 0 0

omit [FiniteDimensional ℝ E] in
/-- A critical point of the action of `f`-seamed paths is an `f`-seamed path. -/
theorem IsSeamedReferenceActionCritical.apply_one
    (hc : σ.IsSeamedReferenceActionCritical f H γ₀ γ) : γ 1 = f (γ 0) :=
  hc.exists_isSmoothSeamedCylinder.choose_spec.source_apply_one

/-- Along a smooth variation through seamed paths of a path `γ` joined to `γ₀` by a smooth
seamed cylinder, the action relative to `γ₀` has at `s = 0` the derivative given by the first
variation formula. -/
private theorem IsNondegenerate.hasDerivAt_seamedReferenceAction_zero (h : σ.IsNondegenerate)
    (hT : VanishesOnSeamedTori f σ.val) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hcyl : ∃ u, IsSmoothSeamedCylinder I f γ γ₀ u) (hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ w)
    (hseam : ∀ s, w (s, 1) = f (w (s, 0))) (h0 : ∀ t, w (0, t) = γ t) :
    HasDerivAt (fun s ↦ σ.seamedReferenceAction f H γ₀ fun t ↦ w (s, t))
      (∫ t in 0..1, σ.val (w (0, t))
        ![mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (0, 1) - σ.hamiltonianVectorField (H t) (w (0, t)),
          mfderiv 𝓘(ℝ, ℝ × ℝ) I w (0, t) (1, 0)]) 0 :=
  h.hasDerivAt_seamedReferenceAction hT hH hwc hseam (funext h0 ▸ hcyl)

/-- **Seamed paths solving the Hamiltonian equation are critical.** For a nondegenerate two-form
vanishing on `f`-seamed tori and a jointly `C¹` Hamiltonian, a smooth path joined to `γ₀` by a
smooth `f`-seamed cylinder which solves `γ' = X_{H_t}(γ)` at the times `t ∈ (0, 1)` is a
critical point of the action relative to `γ₀`. -/
theorem IsNondegenerate.isSeamedReferenceActionCritical (h : σ.IsNondegenerate)
    (hT : VanishesOnSeamedTori f σ.val) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ) (hcyl : ∃ u, IsSmoothSeamedCylinder I f γ γ₀ u)
    (hsol : ∀ t ∈ Ioo (0 : ℝ) 1, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
      ((1 : ℝ →L[ℝ] ℝ).smulRight (σ.hamiltonianVectorField (H t) (γ t)))) :
    σ.IsSeamedReferenceActionCritical f H γ₀ γ where
  contMDiff := hγ
  exists_isSmoothSeamedCylinder := hcyl
  hasDerivAt w hwc hw h0 := by
    convert h.hasDerivAt_seamedReferenceAction_zero hT hH hcyl hwc hw h0 using 1
    exact (σ.intervalIntegral_apply_sub_hamiltonianVectorField_eq_zero
      (fun t ht ↦ hsol t (by rwa [uIoo_of_le zero_le_one] at ht))
      (fun t ↦ (hwc (0, t)).mdifferentiableAt (by simp)) h0).symm

/-- **Seamed solutions are critical.** For a nondegenerate two-form vanishing on `f`-seamed tori
and a jointly `C¹` Hamiltonian, a smooth seamed solution of `X_H` with seam `f` joined to `γ₀` by a
smooth `f`-seamed cylinder is a critical point of the action relative to `γ₀`. -/
theorem IsNondegenerate.isSeamedReferenceActionCritical_of_mem_seamedSolutions
    (h : σ.IsNondegenerate) (hT : VanishesOnSeamedTori f σ.val)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hcyl : ∃ u, IsSmoothSeamedCylinder I f γ γ₀ u)
    (hsol : γ ∈ seamedSolutions (fun t ↦ σ.hamiltonianVectorField (H t)) f) :
    σ.IsSeamedReferenceActionCritical f H γ₀ γ :=
  h.isSeamedReferenceActionCritical hT hH hγ hcyl fun t _ ↦ (mem_seamedSolutions.mp hsol).1 t

/-- **The chart variations of a seamed path.** Let `γ` be a critical point of the seamed action,
`J ⊆ (0, 1)` an open set of times on which `γ` stays in the chart at `x₀`, and `φ` a smooth
profile supported in `J` such that the points `ψ (γ t) + (c φ(t)) • e`, `|c| ≤ 1`, stay in the
chart target. Write `g t` for the pairing of the obstruction `γ' - X_H` at `t` with the tangent
vector of chart coordinates `e` at `γ t`. Then `∫₀¹ φ g = 0`, and `φ g` is continuous. The chart
variation leaves `γ` unchanged outside `J`, in particular at the times `0` and `1`, so it is a
variation through seamed paths. -/
private theorem IsSeamedReferenceActionCritical.integral_mul_apply_eq_zero [I.Boundaryless]
    (hc : σ.IsSeamedReferenceActionCritical f H γ₀ γ) (h : σ.IsNondegenerate)
    (hT : VanishesOnSeamedTori f σ.val) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    {x₀ : M} {J : Set ℝ} {φ : ℝ → ℝ} {e : E} (hJo : IsOpen J) (hJ01 : J ⊆ Ioo 0 1)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    (hTJ : ∀ t ∈ J, ∀ c : ℝ, |c| ≤ 1 →
      extChartAt I x₀ (γ t) + (c * φ t) • e ∈ (extChartAt I x₀).target)
    (hφ : ContDiff ℝ ∞ φ) (hφJ : tsupport φ ⊆ J) :
    (∫ t in 0..1, φ t * σ.val (γ t) ![Manifold.curveVelocity I γ t -
        σ.hamiltonianVectorField (H t) (γ t), (trivializationAt E (TangentSpace I) x₀).symmL ℝ
          (γ t) e]) = 0 ∧
      Continuous fun t ↦ φ t * σ.val (γ t) ![Manifold.curveVelocity I γ t -
        σ.hamiltonianVectorField (H t) (γ t), (trivializationAt E (TangentSpace I) x₀).symmL ℝ
          (γ t) e] := by
  have hn : (1 : ℕ∞) ≤ ⊤ := le_top
  have hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (Manifold.sinChartVariation I γ x₀ J φ e) :=
    Manifold.contMDiff_sinChartVariation hJo hJ hTJ hφ hφJ hc.contMDiff
  -- the variation fixes the end points `γ 0` and `γ 1`, so it runs through seamed paths
  have hseam (s : ℝ) : Manifold.sinChartVariation I γ x₀ J φ e (s, 1) =
      f (Manifold.sinChartVariation I γ x₀ J φ e (s, 0)) := by
    rw [Manifold.sinChartVariation_of_notMem (fun h1 ↦ (hJ01 h1).2.false),
      Manifold.sinChartVariation_of_notMem (fun h0 ↦ (hJ01 h0).1.false), hc.apply_one]
  have h0 := Manifold.sinChartVariation_zero (φ := φ) (e := e) hJ
  -- the first-variation integrand along the chart variation is `φ g`
  refine ⟨(intervalIntegral.integral_congr fun t _ ↦ (σ.apply_mfderiv_sinChartVariation hn hJo hJ
    hTJ hφ hφJ hc.contMDiff t).symm).trans ((h.hasDerivAt_seamedReferenceAction_zero hT hH
      hc.exists_isSmoothSeamedCylinder hwc hseam h0).unique (hc.hasDerivAt hwc hseam h0)),
    h.continuous_mul_apply_curveVelocity_sub hH hn hJo hJ hTJ hφ hφJ hc.contMDiff⟩

/-- **Critical points of the seamed action solve the Hamiltonian equation.** Let `σ` be a
nondegenerate two-form vanishing on `f`-seamed tori on a manifold without boundary modelled on a
finite-dimensional space, and `H` a jointly `C¹` Hamiltonian. Then a critical point `γ` of the
action of `f`-seamed paths relative to `γ₀` solves `γ' = X_{H_t}(γ)` at every time
`t₀ ∈ (0, 1)`. -/
theorem IsSeamedReferenceActionCritical.hasMFDerivAt [I.Boundaryless]
    (hc : σ.IsSeamedReferenceActionCritical f H γ₀ γ) (h : σ.IsNondegenerate)
    (hT : VanishesOnSeamedTori f σ.val) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Ioo (0 : ℝ) 1) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀
      ((1 : ℝ →L[ℝ] ℝ).smulRight (σ.hamiltonianVectorField (H t₀) (γ t₀))) := by
  have hγd : MDifferentiable 𝓘(ℝ, ℝ) I γ := hc.contMDiff.mdifferentiable (by simp)
  suffices hv : Manifold.curveVelocity I γ t₀ = σ.hamiltonianVectorField (H t₀) (γ t₀) by
    rw [← hv]
    exact Manifold.hasMFDerivAt_curveVelocity (hγd t₀)
  by_contra hne
  set x₀ := γ t₀
  -- a chart vector `e` whose tangent vector at `x₀` pairs positively with the obstruction
  -- `γ' - X_H` at `t₀`
  obtain ⟨e, he, hU⟩ :=
    h.exists_pos_apply_and_eventually_add_smul_mem_target (sub_ne_zero.mpr hne)
  -- a radius `δ` of times near `t₀`, inside `(0, 1)`, along which `γ` stays in the chart at `x₀`
  -- and the points displaced by at most `e` stay in the chart target
  obtain ⟨δ₀, hδ₀, hδ₀U⟩ := Metric.eventually_nhds_iff.mp
    ((hc.contMDiff.continuous.continuousAt (x := t₀)).eventually hU)
  set δ := min δ₀ (min t₀ (1 - t₀))
  have hδ : 0 < δ := lt_min hδ₀ (lt_min ht₀.1 (by linarith [ht₀.2]))
  have hball : Metric.ball t₀ δ ⊆ Ioo 0 1 := fun t ht ↦ by
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at ht
    have h1 : δ ≤ t₀ := (min_le_right _ _).trans (min_le_left _ _)
    have h2 : δ ≤ 1 - t₀ := (min_le_right _ _).trans (min_le_right _ _)
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hγU : ∀ t ∈ Metric.ball t₀ δ, γ t ∈ (extChartAt I x₀).source ∧ ∀ c : ℝ, |c| ≤ 1 →
      extChartAt I x₀ (γ t) + c • e ∈ (extChartAt I x₀).target := fun t ht ↦
    hδ₀U (lt_of_lt_of_le ht (min_le_left _ _))
  -- `g t` pairs the obstruction at `t` with the tangent vector of chart coordinates `e`
  set g : ℝ → ℝ := fun t ↦ σ.val (γ t) ![Manifold.curveVelocity I γ t -
    σ.hamiltonianVectorField (H t) (γ t), (trivializationAt E (TangentSpace I) x₀).symmL ℝ (γ t) e]
  have hg₀ : 0 < g t₀ := he
  -- every bump `φ` around `t₀` of outer radius below `δ` has a chart variation, so `∫₀¹ φ g = 0`
  -- with `φ g` continuous
  have hbump : ∀ φ : ContDiffBump t₀, φ.rOut < δ →
      (∫ t in 0..1, φ t * g t) = 0 ∧ Continuous fun t ↦ φ t * g t := by
    intro φ hφδ
    have hφJ : tsupport φ ⊆ Metric.ball t₀ δ := by
      rw [φ.tsupport_eq]
      exact Metric.closedBall_subset_ball hφδ
    refine hc.integral_mul_apply_eq_zero h hT hH Metric.isOpen_ball hball
      (fun t ht ↦ (hγU t ht).1) (fun t ht c hc1 ↦ (hγU t ht).2 _ ?_) φ.contDiff hφJ
    -- the amplitude `c φ(t)` stays in `[-1, 1]`
    rw [abs_mul, abs_of_nonneg φ.nonneg]
    exact (mul_le_mul hc1 φ.le_one φ.nonneg zero_le_one).trans_eq (one_mul 1)
  -- `g` is continuous at `t₀`, where it agrees with `φ g` for a bump `φ` equal to `1` near `t₀`
  have hgcont : ContinuousAt g t₀ := by
    let φ : ContDiffBump t₀ := ⟨δ / 4, δ / 2, by positivity, by linarith⟩
    refine (hbump φ (by change δ / 2 < δ; linarith)).2.continuousAt.congr ?_
    filter_upwards [Metric.ball_mem_nhds t₀ (by positivity : 0 < δ / 4)] with t ht
    rw [φ.one_of_mem_closedBall (Metric.ball_subset_closedBall ht), one_mul]
  -- a bump supported where `g > 0` gives a nonnegative continuous `φ g`, supported in `(0, 1)`,
  -- with zero integral over `[0, 1]`, but `φ g = g > 0` at `t₀`
  obtain ⟨ε, hε, hεg⟩ := Metric.eventually_nhds_iff.mp (hgcont.eventually (lt_mem_nhds hg₀))
  set r := min (δ / 2) ε
  have hr : 0 < r := lt_min (by positivity) hε
  let φ : ContDiffBump t₀ := ⟨r / 2, r, by positivity, by linarith⟩
  obtain ⟨hint, hcont⟩ := hbump φ (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have hsupp : support (fun t ↦ φ t * g t) ⊆ Metric.ball t₀ r :=
    (support_mul_subset_left _ _).trans φ.support_eq.subset
  have hnn : 0 ≤ fun t ↦ φ t * g t := fun t ↦ by
    by_cases ht : t ∈ Metric.ball t₀ r
    · exact mul_nonneg φ.nonneg (hεg (lt_of_lt_of_le ht (min_le_right _ _))).le
    · exact (notMem_support.mp fun hs ↦ ht (hsupp hs)).ge
  have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_ne_zero (μ := MeasureTheory.volume)
    (φ.hasCompactSupport.mul_right) hnn (x := t₀)
    (by rw [φ.one_of_mem_closedBall (Metric.mem_closedBall_self (by positivity)), one_mul]
        exact hg₀.ne')
  rw [← intervalIntegral.integral_eq_integral_of_support_subset
    (hsupp.trans ((Metric.ball_subset_ball (min_le_left _ _ |>.trans (by linarith))).trans
      (hball.trans Ioo_subset_Ioc_self))), hint] at hpos
  exact lt_irrefl 0 hpos

/-- **The critical points of the seamed action.** Let `σ` be a nondegenerate two-form vanishing
on `f`-seamed tori on a manifold without boundary modelled on a finite-dimensional space, and `H`
a jointly `C¹` Hamiltonian. A smooth path joined to the reference path `γ₀` by a smooth
`f`-seamed cylinder is a critical point of the action relative to `γ₀` exactly when it solves
`γ' = X_{H_t}(γ)` at every time `t ∈ (0, 1)`. -/
theorem IsNondegenerate.isSeamedReferenceActionCritical_iff [I.Boundaryless]
    (h : σ.IsNondegenerate) (hT : VanishesOnSeamedTori f σ.val)
    (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H)) (hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ γ)
    (hcyl : ∃ u, IsSmoothSeamedCylinder I f γ γ₀ u) :
    σ.IsSeamedReferenceActionCritical f H γ₀ γ ↔
      ∀ t ∈ Ioo (0 : ℝ) 1, HasMFDerivAt 𝓘(ℝ, ℝ) I γ t
        ((1 : ℝ →L[ℝ] ℝ).smulRight (σ.hamiltonianVectorField (H t) (γ t))) :=
  ⟨fun hc _ ht ↦ hc.hasMFDerivAt h hT hH ht, h.isSeamedReferenceActionCritical hT hH hγ hcyl⟩

end SmoothTwoForm

end TauCeti
