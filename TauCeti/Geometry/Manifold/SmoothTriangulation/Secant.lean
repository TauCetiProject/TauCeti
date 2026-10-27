/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Geometry.Convex.ConvexSpace.CompactSpaceStdSimplex
import TauCeti.Analysis.Convex.StdSimplex

/-!
# Secant maps of smooth triangulations

The *secant map* of a map `f : |K| → E` from the realization of a simplicial complex into a real
normed space is the map which agrees with `f` at the vertices of `K` and is linear on every closed
simplex. Secant maps are how Whitehead and Munkres pass from smooth to piecewise-linear maps:
both the existence of smooth triangulations and their uniqueness up to linearly isomorphic
subdivisions (Munkres, Theorems 10.5 and 10.6) replace a smooth map, simplex by simplex, by its
secant map, and use that the secant map is again non-degenerate.

This file proves the estimate behind that replacement on a single simplex, in barycentric
coordinates. Let `F : (σ → ℝ) → E` be differentiable within the standard simplex, with derivative
within `ε` of a fixed linear map `A` at every point of the simplex. Then the linear map of
barycentric coordinates that agrees with `F` at the vertices differs from `A` by at most
`ε * ∑ a, |v a|` on every direction `v` of the simplex (every vector with coordinate sum zero).
If moreover `c * ∑ a, |v a| ≤ ‖A v‖` on these directions with `ε < c`, the secant map is
injective on them, so it is an immersion of the simplex. When `F` is `C¹` and `A` is its
derivative at one point of a small simplex, the first condition holds with small `ε` by uniform
continuity of the derivative, and the second holds when the simplex is not too thin; arranging
both for all simplices of a fine subdivision gives Munkres' secant approximation theorem.

## Main definitions

* `AbstractSimplicialComplex.secantMap K f`: the secant map of `f : Realization K → E`.

## Main results

* `TauCeti.isSimplexImmersion_of_linearMap`: a map of a simplex that is linear in barycentric
  coordinates and injective on the directions of the simplex is an immersion of the simplex.
* `TauCeti.norm_linearCombination_sub_le`: the secant estimate on a simplex.
* `TauCeti.mul_sum_abs_le_norm_linearCombination`: the secant map inherits a lower bound on the
  directions of the simplex from the nearby linear map.
* `TauCeti.exists_pos_mul_sum_abs_le_norm`: a linear map injective on the directions of the
  simplex has such a lower bound.
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

/-! ### The secant estimate on a simplex -/

section Estimate

variable {α : Type*} [Fintype α]

/-- **The secant estimate.** Let `F` be differentiable within the standard simplex with derivative
within `ε` of a linear map `A` everywhere on it. Then the linear map of barycentric coordinates
that agrees with `F` at the vertices differs from `A` by at most `ε * ∑ a, |v a|` on every
direction `v` of the simplex. -/
theorem norm_linearCombination_sub_le [DecidableEq α] {F : (α → ℝ) → E}
    {F' : (α → ℝ) → (α → ℝ) →L[ℝ] E} {A : (α → ℝ) →L[ℝ] E} {ε : ℝ}
    (hF : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights,
      HasFDerivWithinAt F (F' y) (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) y)
    (hA : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights, ‖F' y - A‖ ≤ ε)
    {v : α → ℝ} (hv : ∑ a, v a = 0) :
    ‖Fintype.linearCombination ℝ (fun a => F (Pi.single a 1)) v - A v‖ ≤ ε * ∑ a, |v a| := by
  set S := range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights
  cases isEmpty_or_nonempty α with
  | inl _ =>
    simp [Subsingleton.elim v 0]
  | inr h =>
    -- Compare every vertex with one fixed vertex `p` of the simplex.
    obtain ⟨a₀⟩ := h
    have hS : Convex ℝ S := Convexity.StdSimplex.convex_range_toFun_comp_weights ℝ α
    have hvert (a : α) : Pi.single a 1 ∈ S :=
      ⟨.single a, by
        dsimp only
        rw [Convexity.StdSimplex.weights_single, Finsupp.single_eq_pi_single]⟩
    set p : α → ℝ := Pi.single a₀ 1
    -- The secant map minus `A`, on a direction, is a combination of the vertex errors.
    have hsplit : Fintype.linearCombination ℝ (fun a => F (Pi.single a 1)) v - A v =
        ∑ a, v a • (F (Pi.single a 1) - F p - A (Pi.single a 1 - p)) := by
      have hAv : A v = ∑ a, v a • A (Pi.single a 1) := by
        conv_lhs => rw [pi_eq_sum_univ' v]
        simp only [map_sum, map_smul]
      simp only [Fintype.linearCombination_apply, hAv, map_sub, smul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_smul, hv, zero_smul, sub_zero]
    rw [hsplit]
    refine (norm_sum_le _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [norm_smul, Real.norm_eq_abs, mul_comm ε]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    -- Each vertex error is bounded by the mean value inequality, since the simplex has diameter
    -- at most one.
    have hp : p ∈ S := hvert a₀
    have hmv := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le' hF hA hS hp (hvert a)
    have hε : 0 ≤ ε := (norm_nonneg _).trans (hA p hp)
    have hdist : ‖Pi.single a 1 - p‖ ≤ 1 := by
      rw [← dist_eq_norm]
      exact (Metric.dist_le_diam_of_mem
        (Convexity.StdSimplex.isBounded_range_toFun_comp_weights α) (hvert a) hp).trans
        (Convexity.StdSimplex.diam_range_toFun_comp_weights_subset_closedBall α)
    exact hmv.trans (mul_le_of_le_one_right hε hdist)

/-- A lower bound `c * ∑ a, |v a| ≤ ‖A v‖` at a direction `v` of the simplex passes, weakened by
`ε`, to the secant map of a map whose derivative is within `ε` of `A` on the simplex. -/
theorem mul_sum_abs_le_norm_linearCombination [DecidableEq α] {F : (α → ℝ) → E}
    {F' : (α → ℝ) → (α → ℝ) →L[ℝ] E} {A : (α → ℝ) →L[ℝ] E} {ε c : ℝ}
    (hF : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights,
      HasFDerivWithinAt F (F' y) (range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights) y)
    (hA : ∀ y ∈ range fun t : Convexity.StdSimplex ℝ α => ⇑t.weights, ‖F' y - A‖ ≤ ε)
    {v : α → ℝ} (hv : ∑ a, v a = 0) (hc : c * ∑ a, |v a| ≤ ‖A v‖) :
    (c - ε) * ∑ a, |v a| ≤ ‖Fintype.linearCombination ℝ (fun a => F (Pi.single a 1)) v‖ := by
  have h := norm_linearCombination_sub_le hF hA hv
  have h' := norm_sub_norm_le (A v) (A v - Fintype.linearCombination ℝ
    (fun a => F (Pi.single a 1)) v)
  rw [sub_sub_cancel, norm_sub_rev] at h'
  linarith

/-- A linear map which is injective on the directions of the simplex is bounded below on them:
there is `c > 0` with `c * ∑ a, |v a| ≤ ‖A v‖` for every vector `v` with coordinate sum zero. -/
theorem exists_pos_mul_sum_abs_le_norm (A : (α → ℝ) →L[ℝ] E)
    (hA : ∀ v : α → ℝ, ∑ a, v a = 0 → A v = 0 → v = 0) :
    ∃ c > 0, ∀ v : α → ℝ, ∑ a, v a = 0 → c * ∑ a, |v a| ≤ ‖A v‖ := by
  -- Restricted to the directions of the simplex, `A` is injective, hence antilipschitz.
  let D := LinearMap.ker (Fintype.linearCombination ℝ fun _ : α => (1 : ℝ))
  have hmem {v : α → ℝ} : v ∈ D ↔ ∑ a, v a = 0 := by
    simp [D, Fintype.linearCombination_apply]
  have hker : LinearMap.ker ((A : (α → ℝ) →ₗ[ℝ] E) ∘ₗ D.subtype) = ⊥ :=
    LinearMap.ker_eq_bot'.mpr fun w hw => Subtype.ext (hA w.1 (hmem.mp w.2) hw)
  obtain ⟨K, hK, hKA⟩ := ((A : (α → ℝ) →ₗ[ℝ] E) ∘ₗ D.subtype).exists_antilipschitzWith hker
  have hcard : (0 : ℝ) < (Fintype.card α + 1) * K := by positivity
  refine ⟨((Fintype.card α + 1) * K)⁻¹, inv_pos.mpr hcard, fun v hv => ?_⟩
  have hvA : ‖v‖ ≤ K * ‖A v‖ := by
    simpa using hKA.le_mul_norm_sub ⟨v, hmem.mpr hv⟩ 0
  have hsum : ∑ a, |v a| ≤ Fintype.card α * ‖v‖ := by
    simpa using Finset.sum_le_sum fun a (_ : a ∈ Finset.univ) => norm_le_pi_norm v a
  rw [inv_mul_le_iff₀ hcard]
  calc ∑ a, |v a| ≤ Fintype.card α * (K * ‖A v‖) := hsum.trans (by gcongr)
    _ ≤ (Fintype.card α + 1) * K * ‖A v‖ := by
      rw [← mul_assoc]
      gcongr
      linarith

end Estimate

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
