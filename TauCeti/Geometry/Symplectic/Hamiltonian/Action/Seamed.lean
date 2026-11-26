/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Flow.Seamed
public import TauCeti.Geometry.Symplectic.Hamiltonian.Action.Basic
public import TauCeti.Geometry.Symplectic.Hamiltonian.LoopVariation
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
seamed cylinders as they stand. When `σ` is closed and `f` preserves it, `f^* σ = σ`, the action
does not change along a homotopy of seamed cylinders relative to their end paths
(`TauCeti.cylinderAction_eq_of_seamedHomotopy`). When `σ` vanishes on `f`-seamed tori
(`TauCeti.VanishesOnSeamedTori`), for instance when `σ = dα` and `f` preserves the primitive,
`f^* α = α` (`TauCeti.vanishesOnSeamedTori_mextDeriv`), the action does not depend on the seamed
cylinder, and defines the action `TauCeti.SmoothTwoForm.seamedReferenceAction σ f H γ₀ γ` of a
seamed path `γ` relative to `γ₀` (`TauCeti.SmoothTwoForm.seamedReferenceAction_eq`); for `f = id`
it is the action `TauCeti.SmoothTwoForm.referenceAction` relative to a reference loop
(`TauCeti.SmoothTwoForm.seamedReferenceAction_id`). These are in
`TauCeti.Geometry.Symplectic.Hamiltonian.Action.Basic`; in general the action is measured against
reference seamed cylinders on the reference-cylinder cover of the space of seamed paths
(`TauCeti.Floer.ReferenceCylinderCover`). This file computes the first variation of the action
relative to `γ₀` and its critical points; for `f = id` these give the first variation formula and
the critical loops of the action relative to a reference loop in
`TauCeti.Geometry.Symplectic.Hamiltonian.Action.FirstVariation`.

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
  without boundary modelled on a finite-dimensional space; a critical point then solves it on
  `[0, 1]` (`TauCeti.SmoothTwoForm.IsSeamedReferenceActionCritical.hasMFDerivAt`). Unlike the
  loop case no periodicity of `H` in time is needed: the test variations are supported inside
  `(0, 1)`, away from the seam, as for paths between Lagrangians, and the chart-variation argument
  is shared with that case, in `TauCeti.Geometry.Symplectic.Hamiltonian.LoopVariation`. In
  particular the seamed solutions of `X_H` (`TauCeti.seamedSolutions`), which generate the Floer
  complex of `f`, are critical
  (`TauCeti.SmoothTwoForm.IsNondegenerate.isSeamedReferenceActionCritical_of_mem_seamedSolutions`);
  when the suspension of `X_H` is complete, their time-zero points are the points where the
  time-one map agrees with `f` (`TauCeti.seamedSolutionsEquiv`).

## Main definitions

* `TauCeti.SmoothTwoForm.IsSeamedReferenceActionCritical σ f H γ₀ γ`: `γ` is a critical point of
  the action relative to `γ₀`.

## Main results

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
vector of chart coordinates `e` at `γ t`. Then `∫₀¹ φ g = 0`. The chart variation leaves `γ`
unchanged outside `J`, in particular at the times `0` and `1`, so it is a variation through seamed
paths. -/
private theorem IsSeamedReferenceActionCritical.integral_mul_apply_eq_zero [I.Boundaryless]
    (hc : σ.IsSeamedReferenceActionCritical f H γ₀ γ) (h : σ.IsNondegenerate)
    (hT : VanishesOnSeamedTori f σ.val) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    {x₀ : M} {J : Set ℝ} {φ : ℝ → ℝ} {e : E} (hJo : IsOpen J) (hJ01 : J ⊆ Ioo 0 1)
    (hJ : ∀ t ∈ J, γ t ∈ (extChartAt I x₀).source)
    (hTJ : ∀ t ∈ J, ∀ c : ℝ, |c| ≤ 1 →
      extChartAt I x₀ (γ t) + (c * φ t) • e ∈ (extChartAt I x₀).target)
    (hφ : ContDiff ℝ ∞ φ) (hφJ : tsupport φ ⊆ J) :
    ∫ t in 0..1, φ t * σ.val (γ t) ![Manifold.curveVelocity I γ t -
      σ.hamiltonianVectorField (H t) (γ t), (trivializationAt E (TangentSpace I) x₀).symmL ℝ
        (γ t) e] = 0 := by
  have hwc : ContMDiff 𝓘(ℝ, ℝ × ℝ) I ∞ (Manifold.sinChartVariation I γ x₀ J φ e) :=
    Manifold.contMDiff_sinChartVariation hJo hJ hTJ hφ hφJ hc.contMDiff
  -- the variation fixes the end points `γ 0` and `γ 1`, so it runs through seamed paths
  have hseam (s : ℝ) : Manifold.sinChartVariation I γ x₀ J φ e (s, 1) =
      f (Manifold.sinChartVariation I γ x₀ J φ e (s, 0)) := by
    rw [Manifold.sinChartVariation_of_notMem (fun h1 ↦ (hJ01 h1).2.false),
      Manifold.sinChartVariation_of_notMem (fun h0 ↦ (hJ01 h0).1.false), hc.apply_one]
  have h0 := Manifold.sinChartVariation_zero (φ := φ) (e := e) hJ
  -- the first-variation integrand along the chart variation is `φ g`
  exact (intervalIntegral.integral_congr fun t _ ↦ (σ.apply_mfderiv_sinChartVariation
    (n := ⊤) le_top hJo hJ hTJ hφ hφJ hc.contMDiff t).symm).trans
    ((h.hasDerivAt_seamedReferenceAction_zero hT hH hc.exists_isSmoothSeamedCylinder hwc hseam
      h0).unique (hc.hasDerivAt hwc hseam h0))

/-- **Critical points of the seamed action solve the Hamiltonian equation.** Let `σ` be a
nondegenerate two-form vanishing on `f`-seamed tori on a manifold without boundary modelled on a
finite-dimensional space, and `H` a jointly `C¹` Hamiltonian. Then a critical point `γ` of the
action of `f`-seamed paths relative to `γ₀` solves `γ' = X_{H_t}(γ)` at every time
`t₀ ∈ [0, 1]`: the first variation vanishes along its chart variations supported in `(0, 1)`. -/
theorem IsSeamedReferenceActionCritical.hasMFDerivAt [I.Boundaryless]
    (hc : σ.IsSeamedReferenceActionCritical f H γ₀ γ) (h : σ.IsNondegenerate)
    (hT : VanishesOnSeamedTori f σ.val) (hH : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) 1 (uncurry H))
    {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (0 : ℝ) 1) :
    HasMFDerivAt 𝓘(ℝ, ℝ) I γ t₀
      ((1 : ℝ →L[ℝ] ℝ).smulRight (σ.hamiltonianVectorField (H t₀) (γ t₀))) := by
  rw [← h.curveVelocity_eq_hamiltonianVectorField_of_forall_integral_mul_eq_zero hH (n := ⊤)
    le_top hc.contMDiff (fun _ _ _ _ hJo hJ01 hJ hTJ hφ hφJ ↦
      hc.integral_mul_apply_eq_zero h hT hH hJo hJ01 hJ hTJ hφ hφJ) ht₀]
  exact Manifold.hasMFDerivAt_curveVelocity
    ((hc.contMDiff t₀).mdifferentiableAt (by simp))

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
  ⟨fun hc _ ht ↦ hc.hasMFDerivAt h hT hH (Ioo_subset_Icc_self ht),
    h.isSeamedReferenceActionCritical hT hH hγ hcyl⟩

end SmoothTwoForm

end TauCeti
