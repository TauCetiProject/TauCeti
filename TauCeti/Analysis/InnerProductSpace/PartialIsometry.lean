/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8
-/
module

/-
Staged for Tau Ceti, roadmap topic T02.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
a new `Mathlib/Analysis/InnerProductSpace/PartialIsometry.lean`.

Sub-dev II of the operator polar decomposition project — COMPLETE
(proof-complete; reduction uses only:
`propext, Classical.choice, Quot.sound`). Tickets PD-05..PD-07.
-/

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.Subspace
public import Mathlib.Algebra.Star.StarProjection


/-! # Partial isometries (Sub-dev II)

A **partial isometry** in a star-monoid is an element `u` with `u * star u * u = u`.
This implies that `star u * u` is a projection (`IsStarProjection`), but the reverse
implication does not hold for arbitrary star-monoids. For operators on an inner
product space, this is the classical notion: `u` restricts to an isometry on
`(ker u)ᗮ` and vanishes on `ker u`.

Mathlib currently has **no** partial-isometry API (grep-confirmed). This packages the unitary factor
of the polar decomposition `A = U |A|`.

Source: Conway, *A Course in Functional Analysis*, 2nd ed., §VI.3 (partial isometries and the polar
decomposition); Reed–Simon, *Methods of Modern Mathematical Physics I*, §VI (before Thm VI.10).

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.PartialIsometry`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `3676b55`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, Claude Opus 4.8; Copyright (c) 2026 Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

open scoped InnerProductSpace
open LinearMap

/-- **Partial isometry** (algebraic form): `u * star u * u = u`. -/
@[expose]
def IsPartialIsometry {R : Type*} [Monoid R] [StarMul R] (u : R) : Prop :=
  u * star u * u = u

namespace IsPartialIsometry

variable {R : Type*} [Monoid R] [StarMul R]

/-- For a partial isometry, `star u * u` is a projection. Conway VI.3.2. -/
theorem isStarProjection_star_mul_self {u : R} (hu : IsPartialIsometry u) :
    IsStarProjection (star u * u) :=
  isStarProjection_iff'.mpr
    ⟨by rw [mul_assoc, ← mul_assoc u (star u) u, hu], by rw [star_mul, _root_.star_star]⟩

/-- `star u` is a partial isometry when `u` is. -/
theorem star_star {u : R} (hu : IsPartialIsometry u) : IsPartialIsometry (star u) := by
  unfold IsPartialIsometry
  rw [_root_.star_star]
  have h := congrArg star hu
  rwa [star_mul, star_mul, _root_.star_star, ← mul_assoc] at h

/-- A unitary element is a partial isometry (`star u * u = 1`). -/
theorem of_star_mul_self_eq_one {u : R} (h : star u * u = 1) : IsPartialIsometry u := by
  unfold IsPartialIsometry
  rw [mul_assoc, h, mul_one]

end IsPartialIsometry

section Operator

variable {𝕜 E : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]

/-- Pointwise isometry-defect identity `‖u x‖² = re ⟪(star u * u) x, x⟫`. Holds for *every* operator
`u`; the partial-isometry hypothesis enters only when identifying `star u * u` with a projection. -/
private theorem re_inner_star_mul_self (u : E →ₗ[𝕜] E) (x : E) :
    ‖u x‖ ^ 2 = RCLike.re ⟪(star u * u) x, x⟫_𝕜 := by
  rw [star_eq_adjoint, Module.End.mul_apply, LinearMap.adjoint_inner_left,
    InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜)]

/-- The initial projection of a partial isometry is the orthogonal projection onto `(ker u)ᗮ`:
`star u * u = P_{(ker u)ᗮ}`. Conway VI.3.2. -/
theorem IsPartialIsometry.star_mul_self_eq_starProjection {u : E →ₗ[𝕜] E}
    (hu : IsPartialIsometry u) :
    star u * u = ((ker u)ᗮ).starProjection.toLinearMap := by
  have hu' : u * star u * u = u := hu
  ext x
  have huxx : u ((star u * u) x) = u x := by
    have hx : (u * star u * u) x = u x := congrArg (fun f : E →ₗ[𝕜] E => f x) hu'
    rwa [mul_assoc, Module.End.mul_apply] at hx
  have hv : (star u * u) x ∈ (ker u)ᗮ := by
    rw [LinearMap.orthogonal_ker, star_eq_adjoint, Module.End.mul_apply]
    exact LinearMap.mem_range_self _ _
  have hz : x - (star u * u) x ∈ ((ker u)ᗮ)ᗮ := by
    rw [Submodule.orthogonal_orthogonal, LinearMap.mem_ker, map_sub, huxx, sub_self]
  have hres := Submodule.eq_starProjection_of_mem_orthogonal' (u := x) hv hz (by abel)
  simpa using hres.symm

/-- **Operator characterization:** `u` is a partial isometry iff it is norm-preserving on the
orthogonal complement of its kernel. Conway VI.3.2. -/
theorem isPartialIsometry_iff_norm_map {u : E →ₗ[𝕜] E} :
    IsPartialIsometry u ↔ ∀ x ∈ (ker u)ᗮ, ‖u x‖ = ‖x‖ := by
  constructor
  · intro hu x hx
    have hsq : ‖u x‖ ^ 2 = ‖x‖ ^ 2 := by
      rw [re_inner_star_mul_self, hu.star_mul_self_eq_starProjection]
      simp only [ContinuousLinearMap.coe_coe]
      rw [Submodule.starProjection_eq_self_iff.mpr hx,
        ← InnerProductSpace.norm_sq_eq_re_inner (𝕜 := 𝕜)]
    rw [← Real.sqrt_sq (norm_nonneg (u x)), ← Real.sqrt_sq (norm_nonneg x), hsq]
  · intro h
    have hinner : ∀ a ∈ (ker u)ᗮ, ∀ b ∈ (ker u)ᗮ, ⟪u a, u b⟫_𝕜 = ⟪a, b⟫_𝕜 := by
      have hg : ∀ w : ((ker u)ᗮ), ‖(u ∘ₗ ((ker u)ᗮ).subtype) w‖ = ‖w‖ := by
        intro w; simpa using h w.1 w.2
      intro a ha b hb
      have hmap := (LinearMap.norm_map_iff_inner_map_map
        (u ∘ₗ ((ker u)ᗮ).subtype)).mp hg ⟨a, ha⟩ ⟨b, hb⟩
      simpa using hmap
    ext x
    have hq : u.adjoint (u x) ∈ (ker u)ᗮ := by
      rw [LinearMap.orthogonal_ker]; exact LinearMap.mem_range_self _ _
    set P := ((ker u)ᗮ).starProjection with hP
    have hPx : P x ∈ (ker u)ᗮ := Submodule.starProjection_apply_mem _ _
    have hux : u x = u (P x) := by
      have hmem0 : x - P x ∈ ker u := by
        have h1 : x - P x ∈ ((ker u)ᗮ)ᗮ := by
          rw [hP]; exact Submodule.sub_starProjection_mem_orthogonal x
        rwa [Submodule.orthogonal_orthogonal] at h1
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hmem0
      exact hmem0
    have hqP : u.adjoint (u x) = P x := by
      have hmem : u.adjoint (u x) - P x ∈ (ker u)ᗮ := Submodule.sub_mem _ hq hPx
      set w := u.adjoint (u x) - P x with hw
      have hzero : ⟪w, w⟫_𝕜 = 0 := by
        have e1 : ⟪u.adjoint (u x), w⟫_𝕜 = ⟪P x, w⟫_𝕜 := by
          rw [LinearMap.adjoint_inner_left, hux, hinner (P x) hPx w hmem]
        calc ⟪w, w⟫_𝕜 = ⟪u.adjoint (u x), w⟫_𝕜 - ⟪P x, w⟫_𝕜 := by rw [hw, inner_sub_left]
          _ = 0 := by rw [e1, sub_self]
      have hw0 := inner_self_eq_zero.mp hzero
      rw [hw, sub_eq_zero] at hw0
      exact hw0
    rw [mul_assoc, Module.End.mul_apply, star_eq_adjoint, Module.End.mul_apply, hqP]
    exact hux.symm

/-- **Constructor** used by the polar decomposition: a linear map that is isometric on a submodule
`K` and vanishes on `Kᗮ` is a partial isometry with initial space `K`. Conway VI.3.9. -/
theorem isPartialIsometry_of_isometryOn {u : E →ₗ[𝕜] E} {K : Submodule 𝕜 E}
    (hker : ker u = Kᗮ) (hiso : ∀ x ∈ K, ‖u x‖ = ‖x‖) :
    IsPartialIsometry u := by
  rw [isPartialIsometry_iff_norm_map]
  intro x hx
  rw [hker, Submodule.orthogonal_orthogonal] at hx
  exact hiso x hx

end Operator
