/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Perturbation

import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Topology.MetricSpace.Thickening
import TauCeti.AlgebraicTopology.SimplicialComplex.Subdivision.Edgewise.Approximation
import TauCeti.Geometry.Manifold.SmoothTriangulation.Edgewise

/-!
# Making an embedding of a complex rectilinear near a compact set

Let `f : |K| → E` be an injective `Cⁿ` star immersion, `1 ≤ n`, of a complex `K` on a finite
vertex type into a finite-dimensional real normed space, let `A` be a compact subset of `E` and
`U` an open neighbourhood of `A`. For all sufficiently fine edgewise subdivisions of `K` there is
an injective star immersion `g` of the subdivision, of class `min n ∞`, which

* is uniformly as close to `f` as desired,
* equals `f ∘ π` wherever `f ∘ π` lands outside `U`, where `π` is the canonical map from the
  realization of the subdivision onto `|K|`, and
* is rectilinear on every closed simplex of the subdivision whose image meets `A`: on such a
  simplex, `g` is the combination of its values at the vertices, with the barycentric coordinates
  as weights.

So every point of `A` in the image of `g` lies in the image of a closed simplex on which `g` is
linear, the convex hull of the images of its vertices, while `g` equals `f ∘ π` wherever `f ∘ π`
lands outside `U`: this is pointwise agreement, and no closed-support condition is asserted.
This is the step of Munkres' construction of a smooth triangulation in which
an embedded complex is straightened in a coordinate chart, before it is fitted together there with
a rectilinear triangulation of another part of the manifold.

The map `g` is the interpolation `AffineMap.lineMap (f (π x)) (s x) (ψ (f (π x)))` between `f` and
its secant map `s` on the subdivision, read through `π`, by a smooth cut-off `ψ` on `E` which is
one on a neighbourhood of `A` and whose support, the set where it is nonzero, is `U`. For fine
subdivisions it is an injective star immersion
(`TauCeti.IsStarImmersion.eventually_isStarImmersion_and_injective_lineMap_secantMap`). The closed
simplices of fine subdivisions are small, so `f ∘ π` varies little on each of them
(`Continuous.eventually_norm_sub_lt_edgewiseSubdivision`). A closed simplex whose image under `g`
meets `A` is therefore sent by `f ∘ π` into the neighbourhood of `A` where `ψ = 1`, and there `g`
is the secant map (`AbstractSimplicialComplex.lineMap_secantMap_faceInclusion_eq_sum`).

## Main results

* `TauCeti.IsStarImmersion.eventually_exists_isStarImmersion_and_injective_and_eq_sum`: an
  injective star immersion can be made rectilinear near a compact set, on all fine edgewise
  subdivisions, by a small perturbation which equals `f ∘ π` wherever `f ∘ π` lands outside a
  prescribed neighbourhood of that set.

## References

* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Section 10 (fitting together embedded complexes in coordinate charts).
* J. H. C. Whitehead, *On C¹-complexes*, Ann. of Math. 41 (1940), 809–824.
-/

public section

open Set Function Filter Metric Topology AbstractSimplicialComplex TauCeti.SetLike
open scoped ContDiff

namespace TauCeti

variable {ι : Type*} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K : AbstractSimplicialComplex ι} {n : WithTop ℕ∞} {f : Realization K → E}

namespace IsStarImmersion

/-- **Making an embedding rectilinear near a compact set.** Let `f` be an injective `Cⁿ` star
immersion, `1 ≤ n`, of a complex `K` on a finite vertex type into a finite-dimensional real normed
space, let `A` be compact and `U` an open neighbourhood of `A`, and let `ε > 0`. For all
sufficiently large `k`, the `k`-th edgewise subdivision of `K` has an injective star immersion `g`
of class `min n ∞` with the following properties, where `π` is the canonical map onto `|K|`:

* `g` is within `ε` of `f ∘ π`;
* `g` agrees with `f ∘ π` at every point that `f ∘ π` sends outside `U`;
* on every closed simplex of the subdivision whose image under `g` meets `A`, `g` is linear in
  barycentric coordinates: it is the combination of the values of `g` at the vertices of the
  simplex, with the barycentric coordinates as weights. -/
theorem eventually_exists_isStarImmersion_and_injective_and_eq_sum
    [Finite ι] [LinearOrder ι] [FiniteDimensional ℝ E] (h : IsStarImmersion n f) (hn : 1 ≤ n)
    (hf : Injective f) {A U : Set E} (hA : IsCompact A) (hU : IsOpen U) (hAU : A ⊆ U) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ k in atTop, ∃ g : Realization (K.edgewiseSubdivision k) → E,
      IsStarImmersion (min n ∞) g ∧ Injective g ∧
      (∀ x, ‖g x - f (edgewiseSubdivisionRealizationMap K k x)‖ < ε) ∧
      (∀ x, f (edgewiseSubdivisionRealizationMap K k x) ∉ U →
        g x = f (edgewiseSubdivisionRealizationMap K k x)) ∧
      ∀ ρ : Face (K.edgewiseSubdivision k),
        (∃ x : StandardSimplex ρ.val, g (faceInclusion _ ρ x) ∈ A) →
        ∀ x : StandardSimplex ρ.val,
          g (faceInclusion _ ρ x) = ∑ a : ρ.val, x.val a • g (vertex _ a) := by
  -- A smooth cut-off `ψ` with support `U`, equal to one exactly on a closed neighbourhood
  -- `cthickening r A` of `A`.
  obtain ⟨r, hr, hrU⟩ := hA.exists_cthickening_subset_open hU hAU
  obtain ⟨ψ, hψ, hψ01, hψU, hψ1⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := ⊤) hU isClosed_cthickening hrU
  set δ := min (r / 2) ε
  have hδ : 0 < δ := lt_min (half_pos hr) hε
  -- On every closed simplex, the cut-off `ψ ∘ f` is the restriction of a `C^(min n ∞)` map in
  -- barycentric coordinates.
  have hφ (σ : Face K) : ∃ Φ : (σ.val → ℝ) → ℝ,
      (∀ x : StandardSimplex σ.val, Φ (fun a => x.val a) = ψ (f (faceInclusion K σ x))) ∧
        ContDiffOn ℝ (min n ∞) Φ (range fun t : Convexity.StdSimplex ℝ σ.val => ⇑t.weights) := by
    obtain ⟨F, hFf, hF, -⟩ := isSimplexImmersion_iff.mp (h.isSimplexImmersion σ)
    exact ⟨ψ ∘ F, fun x => congrArg ψ (hFf x), (hψ.of_le (min_le_right _ _)).comp_contDiffOn
      ((contMDiffOn_iff_contDiffOn.mp hF).of_le (min_le_left _ _))⟩
  filter_upwards [h.eventually_isStarImmersion_and_injective_lineMap_secantMap hn hf
      (le_min hn (by exact_mod_cast le_top)) (φ := fun y => ψ (f y)) hφ,
    h.continuous.eventually_norm_secantMap_sub_lt_edgewiseSubdivision (toFinite K.faces) hδ,
    h.continuous.eventually_norm_sub_lt_edgewiseSubdivision (toFinite K.faces) hδ]
    with k ⟨hsi, hinj⟩ happrox hsmall
  set π := edgewiseSubdivisionRealizationMap K k
  set g := fun x => AffineMap.lineMap (f (π x)) ((K.edgewiseSubdivision k).secantMap (f ∘ π) x)
    (ψ (f (π x))) with hg
  -- The interpolation moves `f ∘ π` by at most the secant error, less than `δ`.
  have hclose (x : Realization (K.edgewiseSubdivision k)) : ‖g x - f (π x)‖ < δ := by
    have h01 := hψ01 (mem_range_self (f (π x)))
    rw [hg, ← vsub_eq_sub, AffineMap.lineMap_vsub_left, vsub_eq_sub, norm_smul,
      Real.norm_of_nonneg h01.1]
    exact (mul_le_of_le_one_left (norm_nonneg _) h01.2).trans_lt (happrox x)
  refine ⟨g, by rwa [← min_assoc, min_self] at hsi, hinj,
    fun x => (hclose x).trans_le (min_le_right _ _), fun x hx => ?_,
    fun ρ ⟨x₀, hx₀⟩ => lineMap_secantMap_faceInclusion_eq_sum (f := f ∘ π)
      (φ := fun y => ψ (f (π y))) ρ ?_⟩
  · have h0 : ψ (f (π x)) = 0 := notMem_support.mp (hψU ▸ hx)
    simp [hg, h0]
  -- On a closed simplex whose image under `g` meets `A`, `f ∘ π` stays within `2 * δ ≤ r` of `A`,
  -- where `ψ = 1`.
  rintro _ ⟨y, rfl⟩
  refine (hψ1 _).mp (mem_cthickening_of_dist_le _ _ _ _ hx₀ ?_)
  rw [dist_eq_norm, ← sub_add_sub_cancel _ (f (π (faceInclusion _ ρ x₀)))]
  refine (norm_add_le _ _).trans ?_
  rw [norm_sub_rev (f (π (faceInclusion _ ρ x₀)))]
  linarith [hsmall ρ y x₀, hclose (faceInclusion _ ρ x₀), min_le_left (r / 2) ε]

end IsStarImmersion

end TauCeti
