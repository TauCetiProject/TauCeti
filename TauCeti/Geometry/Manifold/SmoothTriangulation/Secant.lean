/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic

import TauCeti.Analysis.Convex.SecantEstimate

/-!
# Secant maps of smooth triangulations

The *secant map* of a map `f : |K| → E` from the realization of a simplicial complex into a real
normed space is the map which agrees with `f` at the vertices of `K` and is linear on every closed
simplex. Secant maps are how Whitehead and Munkres pass from smooth to piecewise-linear maps:
both the existence of smooth triangulations and their uniqueness up to linearly isomorphic
subdivisions (Munkres, Theorems 10.5 and 10.6) replace a smooth map, simplex by simplex, by its
secant map, and use that the secant map is again non-degenerate.

The estimate behind that replacement on a single simplex, in barycentric coordinates, is proved in
`TauCeti.Analysis.Convex.SecantEstimate`. Let `F : (σ → ℝ) → E` be differentiable within the
standard simplex, with derivative within `ε` of a fixed linear map `A` at every point of the
simplex. Then the linear map of barycentric coordinates that agrees with `F` at the vertices
differs from `A` by at most `ε * ∑ a, |v a|` on every direction `v` of the simplex (every vector
with coordinate sum zero). This file applies the estimate to secant maps. If moreover
`c * ∑ a, |v a| ≤ ‖A v‖` on these directions with `ε < c`, the secant map is injective on them,
so it is an immersion of the simplex. When `F` is `C¹` and `A` is its
derivative at one point of a small simplex, the first condition holds with small `ε` by uniform
continuity of the derivative, and the second holds when the simplex is not too thin; arranging
both for all simplices of a fine subdivision gives Munkres' secant approximation theorem.

## Main definitions

* `AbstractSimplicialComplex.secantMap K f`: the secant map of `f : Realization K → E`.

## Main results

* `AbstractSimplicialComplex.eq_secantMap`: a map that is linear in barycentric coordinates on
  every closed simplex, with the same vertex values as `f`, is the secant map of `f`.
* `AbstractSimplicialComplex.secantMap_eq_self_iff`: a map is its own secant map exactly when it is
  linear in barycentric coordinates on every closed simplex.
* `TauCeti.isSimplexImmersion_of_linearMap`: a map of a simplex that is linear in barycentric
  coordinates and injective on the directions of the simplex is an immersion of the simplex.
* `AbstractSimplicialComplex.isSimplexImmersion_secantMap_comp_faceInclusion`: the secant map of
  a map that is close to an injective linear map on a closed simplex is an immersion of that
  simplex.

## References

* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Section 9 (secant approximations) and Theorems 10.5–10.6.
-/

public section

noncomputable section

open Set Function AbstractSimplicialComplex TauCeti.SetLike
open scoped Manifold ContDiff

namespace TauCeti

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}

/-! ### Maps of a simplex that are linear in barycentric coordinates -/

/-- A map of a closed simplex into a normed space that is linear in barycentric coordinates, and
injective on the directions of the simplex, is a `Cⁿ` immersion of the simplex for every `n`. -/
theorem isSimplexImmersion_of_linearMap {σ : Finset ι} (L : (σ → ℝ) →ₗ[ℝ] E)
    (hL : ∀ v : σ → ℝ, ∑ a, v a = 0 → L v = 0 → v = 0) :
    IsSimplexImmersion 𝓘(ℝ, E) n fun x : StandardSimplex σ => L fun a => x.1 a := by
  -- The domain of `L` is finite dimensional, so `L` is continuous, and it is its own derivative.
  let L' : (σ → ℝ) →L[ℝ] E := L.toContinuousLinearMap
  exact isSimplexImmersion_iff.mpr ⟨L', fun _ => rfl, L'.contMDiff.contMDiffOn,
    fun _ => ⟨L', L'.hasMFDerivWithinAt, hL⟩⟩

end TauCeti

/-! ### The secant map of a map out of a realization -/

namespace AbstractSimplicialComplex

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : WithTop ℕ∞}
  (K : AbstractSimplicialComplex ι)

/-- The secant map of `f : |K| → E`: the map which agrees with `f` at the vertices of `K` and is
linear in barycentric coordinates on every closed simplex. -/
def secantMap (f : Realization K → E) (x : Realization K) : E :=
  Finsupp.linearCombination ℝ (fun v => f (vertex K v)) x.1

variable {K}

/-- The secant map evaluates a point of the realization as the combination, with its
barycentric coordinates as weights, of the values of `f` at the vertices. -/
theorem secantMap_apply (f : Realization K → E) (x : Realization K) :
    K.secantMap f x = x.1.sum fun v t => t • f (vertex K v) :=
  Finsupp.linearCombination_apply ℝ x.1

/-- The secant map agrees with `f` at every vertex. -/
@[simp]
theorem secantMap_vertex (f : Realization K → E) (v : ι) :
    K.secantMap f (vertex K v) = f (vertex K v) := by
  simp [secantMap_apply]

/-- On a closed simplex `σ`, the secant map is the combination of the values of `f` at the
vertices of `σ`, weighted by the barycentric coordinates. -/
theorem secantMap_faceInclusion (f : Realization K → E) (σ : Face K) (x : StandardSimplex σ.1) :
    K.secantMap f (faceInclusion K σ x) = ∑ a : σ.1, x.1 a • f (vertex K a) := by
  rw [secantMap_apply, faceInclusion_val, Finsupp.sum_of_support_subset x.1
    (StandardSimplex.support_subset x) (fun v t => t • f (vertex K v))
    fun _ _ => zero_smul ℝ _]
  exact (Finset.sum_coe_sort σ.1 fun a => x.1 a • f (vertex K a)).symm

/-- The secant map is continuous. -/
theorem continuous_secantMap (f : Realization K → E) : Continuous (K.secantMap f) := by
  refine continuous_iff_faceInclusion.mpr fun σ => ?_
  have hcoord (a : ι) : Continuous fun x : StandardSimplex σ.1 => x.1 a :=
    (continuous_apply a).comp continuous_induced_dom
  simp_rw [comp_def, secantMap_faceInclusion]
  exact continuous_finsetSum _ fun a _ => (hcoord a).smul continuous_const

/-- Taking secant maps is idempotent: the secant map of a secant map is itself. -/
@[simp]
theorem secantMap_secantMap (f : Realization K → E) :
    K.secantMap (K.secantMap f) = K.secantMap f := by
  funext x
  rw [secantMap_apply]
  simp only [secantMap_vertex]
  rw [secantMap_apply]

/-- **Uniqueness of secant maps.** A map that is linear in barycentric coordinates on every closed
simplex, and agrees with `f` at the vertices, is the secant map of `f`. -/
theorem eq_secantMap {f g : Realization K → E}
    (hg : ∀ (σ : Face K) (x : StandardSimplex σ.1),
      g (faceInclusion K σ x) = ∑ a : σ.1, x.1 a • g (vertex K a))
    (hfg : ∀ v : ι, g (vertex K v) = f (vertex K v)) :
    g = K.secantMap f := by
  funext x
  -- Every point of the realization lies in the closed simplex spanned by its carrier.
  obtain ⟨σ, y, rfl⟩ : ∃ (σ : Face K) (y : StandardSimplex σ.1), faceInclusion K σ y = x :=
    ⟨carrier K x, ⟨x.1, mem_convexHull_carrier K x⟩, Subtype.ext (faceInclusion_val _ _ _)⟩
  simp only [hg, secantMap_faceInclusion, hfg]

/-- A map is its own secant map exactly when it is linear in barycentric coordinates on every
closed simplex. -/
theorem secantMap_eq_self_iff {g : Realization K → E} :
    K.secantMap g = g ↔ ∀ (σ : Face K) (x : StandardSimplex σ.1),
      g (faceInclusion K σ x) = ∑ a : σ.1, x.1 a • g (vertex K a) :=
  ⟨fun h σ x => by
    conv_lhs => rw [← h]
    exact secantMap_faceInclusion g σ x,
   fun hg => (eq_secantMap hg fun _ => rfl).symm⟩

/-- **Non-degeneracy of secant maps.** Let `σ` be a closed simplex of `K`, and let
`F : (σ → ℝ) → E` take the values of `f` at the vertices of `σ`. If the derivative of `F` within
the simplex is everywhere within `ε` of a linear map `A` with `c * ∑ a, |v a| ≤ ‖A v‖` on the
directions `v` of the simplex, and `ε < c`, then the secant map of `f` is a `Cⁿ` immersion of
`σ`, for every `n`. -/
theorem isSimplexImmersion_secantMap_comp_faceInclusion [DecidableEq ι] {f : Realization K → E}
    {σ : Face K} {F : (σ.1 → ℝ) → E} (hFf : ∀ a : σ.1, F (Pi.single a 1) = f (vertex K a))
    {F' : (σ.1 → ℝ) → (σ.1 → ℝ) →L[ℝ] E} {A : (σ.1 → ℝ) →L[ℝ] E} {ε c : ℝ}
    (hF : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights,
      HasFDerivWithinAt F (F' y) (range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights) y)
    (hA : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ σ.1 => ⇑t.weights, ‖F' y - A‖ ≤ ε)
    (hc : ∀ v : σ.1 → ℝ, ∑ a, v a = 0 → c * ∑ a, |v a| ≤ ‖A v‖) (hεc : ε < c) :
    TauCeti.IsSimplexImmersion 𝓘(ℝ, E) n (K.secantMap f ∘ faceInclusion K σ) := by
  have hL : K.secantMap f ∘ faceInclusion K σ = fun x : StandardSimplex σ.1 =>
      Fintype.linearCombination ℝ (fun a => F (Pi.single a 1)) fun a => x.1 a := by
    funext x
    simp only [comp_apply, secantMap_faceInclusion, Fintype.linearCombination_apply, hFf]
  rw [hL]
  refine TauCeti.isSimplexImmersion_of_linearMap _ fun v hv hv0 => ?_
  -- The lower bound `(c - ε) * ∑ a, |v a|` on the secant map forces `v = 0`.
  have h := TauCeti.mul_sum_abs_le_norm_linearCombination hF hA hv (hc v hv)
  rw [hv0, norm_zero] at h
  have hsum : ∑ a, |v a| = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right h (sub_pos.mpr hεc))
      (Finset.sum_nonneg fun a _ => abs_nonneg _)
  funext a
  exact abs_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun b _ => abs_nonneg _).mp hsum a
    (Finset.mem_univ a))

end AbstractSimplicialComplex
