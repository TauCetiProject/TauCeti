/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Riccardo Brasca
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Topology.ContinuousMap.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# The equator of a unit sphere orthogonal to a vector

For a vector `u` of a real inner product space `V`, the points of the unit sphere orthogonal to
`u` form the equator `TauCeti.sphereEquator u`. A linear isometry `e` of a real inner product space
`W` onto the orthogonal complement `(ℝ ∙ u)ᗮ` carries the unit sphere of `W` bijectively and
continuously onto this equator.

## Main declarations

* `TauCeti.sphereEquator u`: the points of the unit sphere orthogonal to `u`, with membership
  characterized by `TauCeti.mem_sphereEquator`.
* `LinearIsometryEquiv.sphereToEquator e`: the unit sphere carried onto the equator through a
  linear isometry `e` onto `(ℝ ∙ u)ᗮ`, with `LinearIsometryEquiv.injective_sphereToEquator` and
  `LinearIsometryEquiv.surjective_sphereToEquator`.
* `TauCeti.orthogonalSphereToEquator u`: its case `e = id`, the unit sphere of `u⊥` as the
  equator.
* `TauCeti.exists_ne_and_ne_neg_sphere`: in dimension at least two, the unit sphere has points
  other than `±p`, for instance the points of the equator orthogonal to `p`.
* `TauCeti.nonempty_unitSphere_inter_orthogonal_pair`: two great hyperspheres in a unit sphere
  of dimension at least two meet, with `TauCeti.nonempty_greatHyperspheres_fin` its Euclidean case.
-/

public section

noncomputable section

open Metric Module
open scoped RealInnerProductSpace

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [NormedAddCommGroup W]
  [InnerProductSpace ℝ W]

namespace TauCeti

variable (u : V) in
/-- The equator of the unit sphere orthogonal to `u`: the unit vectors orthogonal to `u`. For a
unit vector `p` orthogonal to `u` it is the equator through `p` orthogonal to `u`. -/
def sphereEquator : Set (sphere (0 : V) 1) :=
  {q | ⟪(q : V), u⟫ = 0}

variable {u : V}

@[simp]
theorem mem_sphereEquator {q : sphere (0 : V) 1} : q ∈ sphereEquator u ↔ ⟪(q : V), u⟫ = 0 :=
  Iff.rfl

end TauCeti

namespace LinearIsometryEquiv

open TauCeti

variable {u : V}

/-- A linear isometry onto the orthogonal complement of `u` carries the unit sphere onto the equator
orthogonal to `u`. -/
def sphereToEquator (e : W ≃ₗᵢ[ℝ] (ℝ ∙ u)ᗮ) : C(sphere (0 : W) 1, sphereEquator u) where
  toFun s := ⟨⟨(e s : V), by
      rw [mem_sphere_zero_iff_norm, Submodule.norm_coe, LinearIsometryEquiv.norm_map,
        norm_eq_of_mem_sphere]⟩,
    mem_sphereEquator.2 (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (e s).property)⟩
  continuous_toFun := by fun_prop

@[simp]
theorem coe_sphereToEquator (e : W ≃ₗᵢ[ℝ] (ℝ ∙ u)ᗮ) (s : sphere (0 : W) 1) :
    ((e.sphereToEquator s : sphere (0 : V) 1) : V) = e s :=
  (rfl)

/-- The map `LinearIsometryEquiv.sphereToEquator e` onto the equator is injective. -/
theorem injective_sphereToEquator (e : W ≃ₗᵢ[ℝ] (ℝ ∙ u)ᗮ) :
    Function.Injective e.sphereToEquator := fun _ _ h =>
  Subtype.ext (e.injective (Subtype.ext (congrArg (fun r : sphereEquator u =>
    ((r : sphere (0 : V) 1) : V)) h)))

/-- The map `LinearIsometryEquiv.sphereToEquator e` onto the equator is surjective. -/
theorem surjective_sphereToEquator (e : W ≃ₗᵢ[ℝ] (ℝ ∙ u)ᗮ) :
    Function.Surjective e.sphereToEquator := fun q =>
  ⟨⟨e.symm ⟨q.val.val, Submodule.mem_orthogonal_singleton_iff_inner_left.2
      (mem_sphereEquator.1 q.property)⟩, by simp [norm_eq_of_mem_sphere]⟩,
    Subtype.ext (Subtype.ext (by simp))⟩

end LinearIsometryEquiv

namespace TauCeti

variable (u : V) in
/-- The unit sphere of the orthogonal complement `u⊥` is the equator of the unit sphere orthogonal
to `u`: the map `LinearIsometryEquiv.sphereToEquator` of the identity of `u⊥`, sending a unit
vector of `u⊥` to itself. -/
def orthogonalSphereToEquator : C(sphere (0 : (ℝ ∙ u)ᗮ) 1, sphereEquator u) :=
  (LinearIsometryEquiv.refl ℝ _).sphereToEquator

@[simp]
theorem coe_orthogonalSphereToEquator (u : V) (s : sphere (0 : (ℝ ∙ u)ᗮ) 1) :
    ((orthogonalSphereToEquator u s : sphere (0 : V) 1) : V) = ((s : (ℝ ∙ u)ᗮ) : V) :=
  (rfl)

theorem injective_orthogonalSphereToEquator (u : V) :
    Function.Injective (orthogonalSphereToEquator u) :=
  (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).injective_sphereToEquator

theorem surjective_orthogonalSphereToEquator (u : V) :
    Function.Surjective (orthogonalSphereToEquator u) :=
  (LinearIsometryEquiv.refl ℝ (ℝ ∙ u)ᗮ).surjective_sphereToEquator

/-- **The unit sphere has points other than `±p`** in dimension at least two, for instance any unit
vector orthogonal to `p`. -/
theorem exists_ne_and_ne_neg_sphere (hV : 1 < finrank ℝ V) (p : sphere (0 : V) 1) :
    ∃ q : sphere (0 : V) 1, q ≠ p ∧ q ≠ -p := by
  obtain ⟨v, hv, hpv⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ)
    {(p : V)} (by simpa using hV)
  replace hpv : ⟪(p : V), v⟫ = 0 := hpv _ (Finset.mem_singleton_self _)
  -- `v = p` would give `⟪p, p⟫ = 0`, so `p = 0`; `v ≠ -p` since `v` is orthogonal to `p ≠ 0`.
  refine ⟨⟨v, by simpa using hv⟩, fun h ↦ ?_, fun h ↦ ?_⟩
  · refine ne_zero_of_mem_unit_sphere p (inner_self_eq_zero (𝕜 := ℝ).1 ?_)
    rwa [show v = p from Subtype.ext_iff.1 h] at hpv
  · exact ne_neg_of_inner_eq_zero (ne_zero_of_mem_unit_sphere p) (by rwa [real_inner_comm])
      (Subtype.ext_iff.1 h)

/-- Two great hyperspheres in a unit sphere of dimension at least two meet. The defining
normals may be equal or zero. -/
theorem nonempty_unitSphere_inter_orthogonal_pair
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (hdim : 2 < Module.finrank ℝ E) (a b : E) :
    (Metric.sphere (0 : E) 1 ∩ {x : E | ⟪x, a⟫ = 0} ∩
      {x : E | ⟪x, b⟫ = 0}).Nonempty := by
  classical
  obtain ⟨x, hx, horth⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank
    (𝕜 := ℝ) {a, b} (Finset.card_le_two.trans_lt hdim)
  refine ⟨x, ⟨⟨by simpa [Metric.mem_sphere] using hx, ?_⟩, ?_⟩⟩
  · simpa only [Set.mem_ofPred_eq, real_inner_comm] using horth a (by simp)
  · simpa only [Set.mem_ofPred_eq, real_inner_comm] using horth b (by simp)

/-- The great hyperspheres with normals `a` and `b` in `S^(n+1)` intersect for `n ≥ 1`. -/
theorem nonempty_greatHyperspheres_fin (n : ℕ) (hn : 0 < n)
    (a b : EuclideanSpace ℝ (Fin (n + 2))) :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 2))) 1 ∩
      {x | ⟪x, a⟫ = 0} ∩ {x | ⟪x, b⟫ = 0}).Nonempty := by
  apply nonempty_unitSphere_inter_orthogonal_pair
  rw [finrank_euclideanSpace_fin]
  omega

end TauCeti
