/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module

/-!
# Convex combinations: sub-convex combinations and the centroid

This file collects facts on three topics about finite convex combinations in a vector space over a
linearly ordered field: sub-convex combinations, the centroid, and the closed interiors of
simplices given in an affine chart.

A convex set containing `0` also contains every combination `∑ i, w i • z i` of its points with
nonnegative weights of total at most `1`, the missing weight being put on `0`
(`Convex.sum_mem_of_zero_mem`). If the set is moreover symmetric, the coefficients may have any
sign as long as their absolute values sum to at most `1` (`Convex.sum_mem_of_sum_abs_le_one`). In
particular such a set contains the weighted cross-polytope `{x | ∑ i, a i * |b.repr x i| ≤ 1}` as
soon as it contains each `(a i)⁻¹ • b i` for positive weights `a i`
(`Convex.weighted_crosspolytope_subset`). This containment is the step in the lower bound of
Minkowski's second theorem that places a cross-polytope spanned by vectors attaining the
successive minima inside the body; its volume is `OrthonormalBasis.volume_weighted_crosspolytope`.

Over a linearly ordered field there is no topology to speak of relative interiors, but the
centroid of a nonempty finite set `s` still behaves like a relative interior point of the convex
hull of `s`: for every point `p` of the affine span of `s`, the point slightly beyond the centroid
on the ray from `p` remains in the convex hull (`Finset.exists_lineMap_centroid_mem_convexHull`).

This is what makes a point outside a "visible" set lie off the affine span of every simplex in it,
as used for cones of geometric simplicial complexes. It also shows that an affine map injective on
the convex hull of a set is injective on its affine span
(`AffineMap.injOn_affineSpan_iff_injOn_convexHull`), so it carries an affinely independent family
to an affinely independent one as soon as it is injective on the convex hull of the family
(`AffineIndependent.map_of_injOn_convexHull`). A map which agrees with an affine map on the convex
hull of a set carries that hull onto the convex hull of the image (`Set.EqOn.image_convexHull`).
These are what make the image of a simplex under a map affine on it, and injective on it, again a
simplex.

The closed interior of a simplex is the convex hull of its vertices
(`Affine.Simplex.convexHull_eq_closedInterior`). When the vertices are the images of points `x i`
of a vector space under an injective affine map `f`, the closed interior is the image under `f` of
the convex hull of the `x i` (`Affine.Simplex.closedInterior_eq_image_convexHull`, and
`Affine.Triangle.closedInterior_eq_image_convexHull` for triangles), so questions about a simplex
can be settled in coordinates. In coordinates, a bound `f x ≤ w` by a linear map `f` that holds
at the vertices holds on the whole convex hull (`IsLinearMap.le_of_mem_convexHull`).

## References

* J.-H. Evertse, *Geometry of Numbers*, §2.3, Lemma 2.10 and the lower-bound proof of
  Theorem 2.9, printed pp.26–27: <https://pub.math.leidenuniv.nl/~evertsejh/dio19-2.pdf>.
-/

public section

open Finset
open scoped Pointwise

section LinearBound

variable {𝕜 E β : Type*} [Semiring 𝕜] [PartialOrder 𝕜] [AddCommMonoid E] [Module 𝕜 E]
  [AddCommMonoid β] [PartialOrder β] [IsOrderedAddMonoid β] [Module 𝕜 β] [PosSMulMono 𝕜 β]

/-- A bound `f q ≤ w` by a linear map `f` that holds on a set `s` holds on its convex hull. -/
theorem IsLinearMap.le_of_mem_convexHull {f : E → β} (hf : IsLinearMap 𝕜 f) {s : Set E} {w : β}
    (hs : ∀ q ∈ s, f q ≤ w) {p : E} (hp : p ∈ convexHull 𝕜 s) : f p ≤ w :=
  convexHull_min (t := {q | f q ≤ w}) hs (convex_halfSpace_le hf w) hp

end LinearBound

section EqOnAffine

variable {𝕜 E F : Type*} [Ring 𝕜] [PartialOrder 𝕜] [AddCommGroup E] [Module 𝕜 E] [AddCommGroup F]
  [Module 𝕜 F]

/-- A map which agrees with an affine map on the convex hull of a set `s` carries that convex hull
onto the convex hull of the image of `s`. -/
theorem Set.EqOn.image_convexHull {f : E → F} {g : E →ᵃ[𝕜] F} {s : Set E}
    (h : Set.EqOn f g (convexHull 𝕜 s)) : f '' convexHull 𝕜 s = convexHull 𝕜 (f '' s) := by
  rw [h.image_eq, g.image_convexHull, (h.mono (subset_convexHull 𝕜 s)).image_eq]

end EqOnAffine

variable {𝕜 E ι : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E]
  [Module 𝕜 E]

namespace Convex

variable {s : Set E}

/-- A convex set containing `0` contains every combination of its points with nonnegative
weights of total at most `1`. -/
theorem sum_mem_of_zero_mem (hs : Convex 𝕜 s) (h₀ : (0 : E) ∈ s) {t : Finset ι} {w : ι → 𝕜}
    {z : ι → E} (hw₀ : ∀ i ∈ t, 0 ≤ w i) (hw₁ : ∑ i ∈ t, w i ≤ 1) (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, w i • z i ∈ s := by
  -- Put the remaining weight `1 - ∑ i ∈ t, w i` on the point `0`.
  have h := hs.sum_mem (t := t.insertNone) (w := fun o ↦ o.elim (1 - ∑ i ∈ t, w i) w)
    (z := fun o ↦ o.elim 0 z) (by simpa [Option.forall] using ⟨hw₁, hw₀⟩) (by simp)
    (by simpa [Option.forall] using ⟨h₀, hz⟩)
  simpa using h

/-- A convex set containing `0` and symmetric about it contains every combination of its points
whose coefficients have absolute values of total at most `1`. -/
theorem sum_mem_of_sum_abs_le_one (hs : Convex 𝕜 s) (h₀ : (0 : E) ∈ s)
    (hneg : ∀ x ∈ s, -x ∈ s) {t : Finset ι} {c : ι → 𝕜} {z : ι → E}
    (hc : ∑ i ∈ t, |c i| ≤ 1) (hz : ∀ i ∈ t, z i ∈ s) :
    ∑ i ∈ t, c i • z i ∈ s := by
  classical
  -- Move the sign of each coefficient onto its vector.
  have h (i : ι) : c i • z i = |c i| • if 0 ≤ c i then z i else -z i := by
    split_ifs with hci
    · rw [abs_of_nonneg hci]
    · rw [abs_of_neg (not_le.1 hci), neg_smul, smul_neg, neg_neg]
  simp only [h]
  refine hs.sum_mem_of_zero_mem h₀ (fun i _ ↦ abs_nonneg _) hc fun i hi ↦ ?_
  split_ifs
  exacts [hz i hi, hneg _ (hz i hi)]

/-- **A weighted cross-polytope inside a symmetric convex set.** Let `s` be a convex set
containing `0` and symmetric about it, `b` a basis and `a` positive weights with `b i ∈ a i • s`
for every `i`. Then `s` contains the weighted cross-polytope
`{x | ∑ i, a i * |b.repr x i| ≤ 1}`. -/
theorem weighted_crosspolytope_subset [Fintype ι] (hs : Convex 𝕜 s) (h₀ : (0 : E) ∈ s)
    (hneg : ∀ x ∈ s, -x ∈ s) (b : Module.Basis ι 𝕜 E) {a : ι → 𝕜} (ha : ∀ i, 0 < a i)
    (hb : ∀ i, b i ∈ a i • s) :
    {x : E | ∑ i, a i * |b.repr x i| ≤ 1} ⊆ s := by
  intro x hx
  have hx' : x = ∑ i, (a i * b.repr x i) • (a i)⁻¹ • b i := by
    conv_lhs => rw [← b.sum_repr x]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    simp [smul_smul, mul_right_comm _ _ (a i)⁻¹, (ha i).ne']
  rw [hx']
  refine hs.sum_mem_of_sum_abs_le_one h₀ hneg ?_ fun i _ ↦
    (Set.mem_smul_set_iff_inv_smul_mem₀ (ha i).ne' _ _).1 (hb i)
  simpa [abs_mul, abs_of_pos (ha _)] using hx

end Convex

namespace Finset

/-- For every point `p` in the affine span of a nonempty finite set `s`, some point strictly beyond
the centroid of `s` on the ray from `p` still lies in the convex hull of `s`. -/
theorem exists_lineMap_centroid_mem_convexHull (s : Finset E) (hs : s.Nonempty) {p : E}
    (hp : p ∈ affineSpan 𝕜 (s : Set E)) :
    ∃ ε : 𝕜, 0 < ε ∧ AffineMap.lineMap p (s.centroid 𝕜 id) (1 + ε) ∈ convexHull 𝕜 (s : Set E) := by
  classical
  have hrange : (s : Set E) = Set.range ((↑) : s → E) := by simp
  rw [hrange] at hp
  obtain ⟨w, hw, hpw⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hp
  rw [affineCombination_eq_linear_combination _ _ _ hw] at hpw
  set n : 𝕜 := (#s : 𝕜)
  have hn : 0 < n := Nat.cast_pos.2 hs.card_pos
  have hc : s.centroid 𝕜 id = ∑ i : s, n⁻¹ • (i : E) := by
    rw [centroid_def, affineCombination_eq_linear_combination _ _ _
      (sum_centroidWeights_eq_one_of_nonempty 𝕜 _ hs)]
    simp only [centroidWeights_apply, id]
    exact (sum_coe_sort s fun i => n⁻¹ • i).symm
  -- `ε` is small enough that pushing past the centroid keeps every weight nonnegative
  set M : 𝕜 := ∑ i : s, |w i|
  have hM : 0 ≤ M := sum_nonneg fun i _ => abs_nonneg (w i)
  set ε : 𝕜 := (n * (M + 1))⁻¹
  have hε : 0 < ε := inv_pos.2 (mul_pos hn (by linarith))
  set μ : s → 𝕜 := fun i => (1 + ε) * n⁻¹ - ε * w i
  have hμ : ∀ i, 0 ≤ μ i := by
    intro i
    have hwi : ε * w i ≤ n⁻¹ := by
      calc ε * w i ≤ ε * M :=
            mul_le_mul_of_nonneg_left ((le_abs_self _).trans
              (single_le_sum (f := fun i : s => |w i|) (fun i _ => abs_nonneg _) (mem_univ i)))
              hε.le
        _ ≤ ε * (M + 1) := by nlinarith
        _ = n⁻¹ := by
            simp only [ε, mul_inv]
            field_simp
    have : 0 ≤ ε * n⁻¹ := (mul_pos hε (inv_pos.2 hn)).le
    simp only [μ]
    nlinarith
  have hμsum : ∑ i : s, μ i = 1 := by
    simp only [μ, sum_sub_distrib, ← mul_sum, hw, sum_const, card_univ, Fintype.card_coe,
      nsmul_eq_mul]
    field_simp
    ring
  refine ⟨ε, hε, ?_⟩
  have hq : AffineMap.lineMap p (s.centroid 𝕜 id) (1 + ε) = ∑ i : s, μ i • (i : E) := by
    rw [AffineMap.lineMap_apply_module', hc, hpw]
    simp only [μ, sub_smul, sum_sub_distrib, ← smul_sum, mul_smul]
    module
  rw [hq]
  exact (convex_convexHull 𝕜 _).sum_mem (fun i _ => hμ i) hμsum fun i _ => subset_convexHull 𝕜 _ i.2

end Finset

namespace AffineMap

variable {F : Type*} [AddCommGroup F] [Module 𝕜 F]

/-- An affine map whose linear part kills a direction `v` of the affine span of a set `s` is not
injective on the convex hull of `s`, unless `v = 0`. -/
theorem eq_zero_of_injOn_convexHull (f : E →ᵃ[𝕜] F) {s : Set E}
    (hf : Set.InjOn f (convexHull 𝕜 s)) {v : E} (hv : v ∈ vectorSpan 𝕜 s)
    (hfv : f.linear v = 0) : v = 0 := by
  classical
  -- `v` already lies in the vector span of a finite subset `t` of `s`
  obtain ⟨t, hts, hv⟩ : ∃ t : Finset E, (t : Set E) ⊆ s ∧ v ∈ vectorSpan 𝕜 (t : Set E) := by
    rcases s.eq_empty_or_nonempty with rfl | ⟨p, hp⟩
    · exact ⟨∅, by simp, by simpa using hv⟩
    rw [vectorSpan_eq_span_vsub_set_right (k := 𝕜) hp] at hv
    obtain ⟨u, hu, hvu⟩ := Submodule.mem_span_finite_of_mem_span hv
    obtain ⟨t, hts, rfl⟩ := Finset.subset_set_image_iff.1 hu
    refine ⟨insert p t, by simpa [Set.insert_subset_iff] using ⟨hp, hts⟩, ?_⟩
    rw [vectorSpan_eq_span_vsub_set_right (k := 𝕜) (mem_coe.2 (mem_insert_self p t))]
    refine Submodule.span_mono ?_ hvu
    rw [coe_image, coe_insert]
    exact Set.image_mono (Set.subset_insert _ _)
  replace hf := hf.mono (convexHull_mono hts)
  rcases t.eq_empty_or_nonempty with ht | ht
  · simpa [ht] using hv
  set c : E := t.centroid 𝕜 _root_.id
  have hc : c ∈ affineSpan 𝕜 (t : Set E) :=
    convexHull_subset_affineSpan _ (t.centroid_mem_convexHull ht)
  have hcv : c - v ∈ affineSpan 𝕜 (t : Set E) := by
    rw [sub_eq_neg_add]
    exact AffineSubspace.vadd_mem_of_mem_direction
      (by rw [direction_affineSpan]; exact neg_mem hv) hc
  obtain ⟨ε, hε, hmem⟩ := t.exists_lineMap_centroid_mem_convexHull ht hcv
  -- the point `c + ε • v` beyond the centroid lies in the hull and has the image of `c`
  have hpt : lineMap (c - v) c (1 + ε) = ε • v + c := by
    rw [lineMap_apply_module']
    module
  rw [hpt] at hmem
  have heq : ε • v + c = c := hf hmem (t.centroid_mem_convexHull ht) <| by
    rw [← vadd_eq_add, map_vadd, map_smul, hfv, smul_zero, zero_vadd]
  simpa [hε.ne'] using heq

/-- An affine map is injective on the affine span of a set as soon as it is injective on its convex
hull. -/
theorem injOn_affineSpan_iff_injOn_convexHull (f : E →ᵃ[𝕜] F) (s : Set E) :
    Set.InjOn f (affineSpan 𝕜 s) ↔ Set.InjOn f (convexHull 𝕜 s) := by
  refine ⟨fun h => h.mono (convexHull_subset_affineSpan _), fun h x hx y hy hxy => ?_⟩
  have hv : x -ᵥ y ∈ vectorSpan 𝕜 s := by
    rw [← direction_affineSpan]
    exact AffineSubspace.vsub_mem_direction hx hy
  have := f.eq_zero_of_injOn_convexHull h hv (by rw [linear_apply_vsub, hxy, vsub_self])
  rwa [vsub_eq_zero_iff_eq] at this

end AffineMap

/-- The image of an affinely independent family under an affine map is affinely independent as
soon as the map is injective on the convex hull of the family. -/
theorem AffineIndependent.map_of_injOn_convexHull {F : Type*} [AddCommGroup F] [Module 𝕜 F]
    {p : ι → E} (hp : AffineIndependent 𝕜 p) (f : E →ᵃ[𝕜] F)
    (hf : Set.InjOn f (convexHull 𝕜 (Set.range p))) : AffineIndependent 𝕜 (f ∘ p) := by
  rw [affineIndependent_iff] at hp ⊢
  intro s w hw hfw
  refine hp s w hw ?_
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp
  -- the combination `∑ w i • p i` is a direction of the affine span of the points `p i`
  have hsum : ∑ i ∈ s, w i • p i = ∑ i ∈ s, w i • (p i -ᵥ p i₀) := by
    simp [vsub_eq_sub, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw]
  have hv : ∑ i ∈ s, w i • p i ∈ vectorSpan 𝕜 (Set.range p) := by
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ <|
      vsub_mem_vectorSpan 𝕜 (Set.mem_range_self i) (Set.mem_range_self i₀)
  refine f.eq_zero_of_injOn_convexHull hf hv ?_
  have hlin : ∀ i, f.linear (p i) = f (p i) - f 0 := fun i => by
    rw [← vsub_eq_sub, ← f.linear_apply_vsub, vsub_eq_sub, sub_zero]
  simp only [map_sum, map_smul, hlin, smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hw,
    zero_smul, sub_zero]
  simpa using hfw

namespace Affine.Simplex

/-- The closed interior of a simplex whose vertices are the images of points `x i` of a vector space
under an injective affine map `f` is the image under `f` of the convex hull of the `x i`. -/
theorem closedInterior_eq_image_convexHull {V P : Type*} [AddCommGroup V] [Module 𝕜 V]
    [AddTorsor V P] {n : ℕ} (s : Simplex 𝕜 P n) {f : E →ᵃ[𝕜] P} (hf : Function.Injective f)
    {x : Fin (n + 1) → E} (hx : s.points = f ∘ x) :
    s.closedInterior = f '' convexHull 𝕜 (Set.range x) := by
  have hind : AffineIndependent 𝕜 x := AffineIndependent.of_comp f (hx ▸ s.independent)
  have hmap : s = (⟨x, hind⟩ : Simplex 𝕜 E n).map f hf := Simplex.ext fun j => congrFun hx j
  rw [hmap, closedInterior_map, ← convexHull_eq_closedInterior]

end Affine.Simplex

namespace Affine.Triangle

/-- A triangle whose vertices are the images of `x`, `y`, `z` under an injective affine map `f`
from a vector space has closed interior the image under `f` of the convex hull of `x`, `y`, `z`. -/
theorem closedInterior_eq_image_convexHull {V P : Type*} [AddCommGroup V] [Module 𝕜 V]
    [AddTorsor V P] (t : Triangle 𝕜 P) {f : E →ᵃ[𝕜] P} (hf : Function.Injective f) {x y z : E}
    (ht : t.points = ![f x, f y, f z]) :
    t.closedInterior = f '' convexHull 𝕜 {x, y, z} := by
  rw [Simplex.closedInterior_eq_image_convexHull t hf (x := ![x, y, z]) (by
      rw [ht]
      ext j
      fin_cases j <;> rfl),
    Matrix.range_cons, Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
    Set.singleton_union, Set.singleton_union]

end Affine.Triangle
