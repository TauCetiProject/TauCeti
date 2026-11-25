/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.Intrinsic
public import Mathlib.Analysis.Normed.Module.Basic
public import TauCeti.Analysis.Convex.StdSimplex
import TauCeti.Analysis.Convex.Intrinsic
import TauCeti.Analysis.Normed.Affine.AddTorsor.Bases

/-!
# Open simplices

The *open simplex* spanned by an affinely independent finite family `p` of points of a real
normed space is the intrinsic interior of its convex hull. This file
identifies it with the set of affine combinations of `p` with all weights positive
(`AffineIndependent.mem_intrinsicInterior_convexHull_iff`) — equivalently, the image of the open
standard simplex `TauCeti.openStdSimplex ℝ ι` under `w ↦ ∑ i, w i • p i`
(`AffineIndependent.intrinsicInterior_convexHull_eq_image_sum_smul`) — and shows that a proper face
misses it: a point of the open simplex lying in the convex hull of `p '' s` forces `s` to contain
every index (`AffineIndependent.eq_univ_of_mem_intrinsicInterior_convexHull`). The centroid of the
family lies in its open simplex (`AffineIndependent.centroid_mem_intrinsicInterior_convexHull`),
and its continuous affine barycentric coordinates assemble into a global affine map
`E →ᵃ[ℝ] (ι → ℝ)` mapping the closed and open simplices into the closed and open standard simplices
(`AffineIndependent.exists_affineMap_barycentricCoord`).

For the standard simplex in `ι → ℝ`, this identifies the intrinsic interior of the face spanned by
a set `t` of coordinate vertices `Pi.single i 1` with the points of that face whose coordinates in
`t` are strictly positive (`TauCeti.intrinsicInterior_convexHull_pi_single`), and in particular
identifies the intrinsic interior of the standard simplex with `TauCeti.openStdSimplex ℝ ι` and the
intrinsic interior of each facet opposite a vertex `i` with `TauCeti.openStdSimplexFacet ℝ i`
(`TauCeti.intrinsicInterior_range_toFun_comp_weights`,
`TauCeti.intrinsicInterior_facet_range_toFun_comp_weights`).

So the open simplices of the faces of a simplex partition it, which is what makes the open
simplices of a geometric simplicial complex disjoint
(`Geometry.SimplicialComplex.eq_of_mem_intrinsicInterior`).

The proofs read the weights through continuous barycentric coordinates: continuous affine
functions on the whole space which read off the weight of each point of `p` in every affine
combination (`AffineIndependent.exists_continuousAffineMap_apply_affineCombination`). The ambient
space need not be finite-dimensional.

## Main results

* `AffineIndependent.mem_intrinsicInterior_convexHull_iff`,
  `AffineIndependent.intrinsicInterior_convexHull_eq_image_sum_smul`: the intrinsic interior of the
  convex hull of an affinely independent finite family consists of its affine combinations with
  positive weights, i.e., the image of `TauCeti.openStdSimplex ℝ ι` under `w ↦ ∑ i, w i • p i`.
* `AffineIndependent.centroid_mem_intrinsicInterior_convexHull`: the centroid of a simplex lies
  in its intrinsic interior.
* `AffineIndependent.eq_univ_of_mem_intrinsicInterior_convexHull`: a proper face of a simplex
  misses its intrinsic interior.
* `AffineIndependent.exists_affineMap_barycentricCoord`: global affine barycentric coordinate map
  inverting `w ↦ ∑ i, w i • p i` on closed and open simplices.
* `TauCeti.intrinsicInterior_convexHull_pi_single`,
  `TauCeti.intrinsicInterior_range_toFun_comp_weights`,
  `TauCeti.intrinsicInterior_facet_range_toFun_comp_weights`: coordinate descriptions of the
  intrinsic interiors of coordinate faces, the standard simplex, and its facets.

## References

* R. T. Rockafellar, *Convex Analysis*, Princeton (1970), Theorem 6.9 (the relative interior of a
  convex hull).
* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (open simplices).
-/

public section

open Set Finset Filter Topology Convexity

section AffineIndependent

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E] {p : ι → E}

/-- **The open simplex.** A point lies in the intrinsic interior of the convex hull of an affinely
independent finite family exactly when it is an affine combination of the family with all weights
positive. -/
theorem AffineIndependent.mem_intrinsicInterior_convexHull_iff (hp : AffineIndependent ℝ p)
    {x : E} : x ∈ intrinsicInterior ℝ (convexHull ℝ (range p)) ↔
      ∃ w : ι → ℝ, (∀ i, 0 < w i) ∧ ∑ i, w i = 1 ∧ Finset.univ.affineCombination ℝ p w = x := by
  obtain ⟨f, hf, hfi, hfj⟩ := hp.exists_continuousAffineMap_apply_affineCombination
  -- The coordinates are nonnegative on the convex hull.
  have hnn : ∀ i, convexHull ℝ (range p) ⊆ {y | 0 ≤ f i y} := fun i =>
    convexHull_min (range_subset_iff.2 fun j => by
      rcases eq_or_ne i j with rfl | hij
      · simp [hfi]
      · simp [hfj i j hij]) ((convex_Ici 0).affine_preimage (f i).toAffineMap)
  rw [TauCeti.mem_intrinsicInterior_iff_eventually, affineSpan_convexHull]
  constructor
  · rintro ⟨hx, hev⟩
    obtain ⟨w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hx
    refine ⟨w, fun i => ?_, hw, rfl⟩
    set x := Finset.univ.affineCombination ℝ p w
    have hx0 : 0 ≤ w i := hf w hw i ▸ hnn i (hev.self_of_nhds hx)
    refine hx0.lt_of_ne fun hwi => ?_
    -- Moving from `x` slightly away from `p i` stays in the convex hull, where `f i ≥ 0`, but
    -- makes the weight of `p i` negative.
    have hcont : Tendsto (fun ε : ℝ => AffineMap.lineMap x (p i) ε) (𝓝 0) (𝓝 x) := by
      simpa using (AffineMap.lineMap_continuous (R := ℝ) (p := x) (q := p i)).tendsto (0 : ℝ)
    obtain ⟨ε, hε, hεneg⟩ := (((hcont.eventually hev).filter_mono nhdsWithin_le_nhds).and
      (self_mem_nhdsWithin (s := Iio 0))).exists
    have hmem : 0 ≤ f i (AffineMap.lineMap x (p i) ε) :=
      hnn i (hε (AffineMap.lineMap_mem _ hx (subset_affineSpan _ _ (mem_range_self i))))
    have hfx : f i x = 0 := (hf w hw i).trans hwi.symm
    rw [ContinuousAffineMap.apply_lineMap, hfx, hfi i, AffineMap.lineMap_apply_ring'] at hmem
    linarith [mem_Iio.1 hεneg]
  · rintro ⟨w, hw₀, hw₁, rfl⟩
    refine ⟨affineCombination_mem_affineSpan hw₁ p, ?_⟩
    have hev : ∀ᶠ y in 𝓝 (Finset.univ.affineCombination ℝ p w), ∀ i, 0 < f i y :=
      Filter.eventually_all.2 fun i => (f i).continuous.continuousAt.eventually
        (lt_mem_nhds (by rw [hf w hw₁ i]; exact hw₀ i))
    filter_upwards [hev] with y hy hyA
    obtain ⟨v, hv, rfl⟩ := eq_affineCombination_of_mem_affineSpan_of_fintype hyA
    exact affineCombination_mem_convexHull (fun i _ => (hf v hv i ▸ hy i).le) hv

/-- The barycentric combination map `w ↦ ∑ i, w i • p i` maps the open standard simplex onto the
open simplex `intrinsicInterior ℝ (convexHull ℝ (range p))`. -/
theorem AffineIndependent.intrinsicInterior_convexHull_eq_image_sum_smul
    (hp : AffineIndependent ℝ p) :
    intrinsicInterior ℝ (convexHull ℝ (range p)) =
      (fun w : ι → ℝ => ∑ i, w i • p i) '' TauCeti.openStdSimplex ℝ ι := by
  ext x
  rw [hp.mem_intrinsicInterior_convexHull_iff]
  constructor
  · rintro ⟨w, hw₀, hw₁, rfl⟩
    exact ⟨w, TauCeti.mem_openStdSimplex_iff.2
      ⟨StdSimplex.mem_range_toFun_comp_weights_iff.2 ⟨fun i => (hw₀ i).le, hw₁⟩, hw₀⟩,
      (Finset.affineCombination_eq_linear_combination _ _ _ hw₁).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hw, hw₀⟩ := TauCeti.mem_openStdSimplex_iff.1 hw
    obtain ⟨-, hw₁⟩ := StdSimplex.mem_range_toFun_comp_weights_iff.1 hw
    exact ⟨w, hw₀, hw₁, Finset.affineCombination_eq_linear_combination _ _ _ hw₁⟩

/-- The centroid of a nonempty affinely independent finite family lies in the open simplex it
spans. -/
theorem AffineIndependent.centroid_mem_intrinsicInterior_convexHull [Nonempty ι]
    (hp : AffineIndependent ℝ p) :
    Finset.univ.centroid ℝ p ∈ intrinsicInterior ℝ (convexHull ℝ (range p)) :=
  hp.mem_intrinsicInterior_convexHull_iff.2 ⟨_, fun _ => by
    simpa [Finset.centroidWeights_apply] using Fintype.card_pos,
    Finset.univ.sum_centroidWeights_eq_one_of_card_ne_zero ℝ Finset.univ_nonempty.card_pos.ne',
    rfl⟩

omit [Fintype ι] in
/-- **A proper face misses the open simplex.** If a point of the intrinsic interior of the convex
hull of an affinely independent finite family lies in the convex hull of the points indexed by
`s`, then `s` contains every index. -/
theorem AffineIndependent.eq_univ_of_mem_intrinsicInterior_convexHull [Finite ι]
    (hp : AffineIndependent ℝ p) {x : E} (hx : x ∈ intrinsicInterior ℝ (convexHull ℝ (range p)))
    {s : Set ι} (hs : x ∈ convexHull ℝ (p '' s)) : s = univ := by
  cases nonempty_fintype ι
  obtain ⟨f, hf, -, hfj⟩ := hp.exists_continuousAffineMap_apply_affineCombination
  obtain ⟨w, hw₀, hw₁, rfl⟩ := hp.mem_intrinsicInterior_convexHull_iff.1 hx
  refine eq_univ_of_forall fun i => by_contra fun hi => (hw₀ i).ne' ?_
  -- The weight of `p i` vanishes on the convex hull of the other points.
  have hsub : convexHull ℝ (p '' s) ⊆ {y | f i y = 0} :=
    convexHull_min (by rintro _ ⟨j, hj, rfl⟩; exact hfj i j fun hij => hi (hij ▸ hj))
      ((convex_singleton 0).affine_preimage (f i).toAffineMap)
  simpa [hf w hw₁ i] using hsub hs

/-- **Global affine barycentric coordinates.** For any affinely independent finite family
`p : ι → E` in a real normed space, there exists a global affine map `B : E →ᵃ[ℝ] (ι → ℝ)` which
inverts `w ↦ ∑ i, w i • p i` on `{w | ∑ i, w i = 1}`, maps `convexHull ℝ (range p)` into the
closed standard simplex as a right inverse to `w ↦ ∑ i, w i • p i`, and maps
`intrinsicInterior ℝ (convexHull ℝ (range p))` into `TauCeti.openStdSimplex ℝ ι`. -/
theorem AffineIndependent.exists_affineMap_barycentricCoord (hp : AffineIndependent ℝ p) :
    ∃ B : E →ᵃ[ℝ] (ι → ℝ),
      (∀ w : ι → ℝ, ∑ i, w i = 1 → B (∑ i, w i • p i) = w) ∧
      (∀ x ∈ convexHull ℝ (range p),
        B x ∈ (range fun s : StdSimplex ℝ ι => ⇑s.weights) ∧ ∑ i, B x i • p i = x) ∧
      (∀ x ∈ intrinsicInterior ℝ (convexHull ℝ (range p)),
        B x ∈ TauCeti.openStdSimplex ℝ ι) := by
  classical
  rcases isEmpty_or_nonempty ι with _ | _
  · refine ⟨AffineMap.const ℝ E 0, fun w hw => by simp at hw, ?_, ?_⟩
    · simp [range_eq_empty]
    · rw [range_eq_empty]
      simp
  · obtain ⟨f, hf, -, -⟩ := hp.exists_continuousAffineMap_apply_affineCombination
    let B : E →ᵃ[ℝ] (ι → ℝ) := AffineMap.pi fun i => (f i).toAffineMap
    have hleft (w : ι → ℝ) (hw : ∑ i, w i = 1) : B (∑ i, w i • p i) = w := by
      ext i
      have hcomb := Finset.univ.affineCombination_eq_linear_combination p w hw
      simpa [B, hcomb] using hf w hw i
    refine ⟨B, hleft, fun x hx => ?_, fun x hx => ?_⟩
    · rw [convexHull_range_eq_exists_affineCombination] at hx
      obtain ⟨s, w, hw₀, hw₁, rfl⟩ := hx
      have hw1' : ∑ i, (s : Set ι).indicator w i = 1 := by
        simpa [Finset.sum_indicator_subset _ s.subset_univ] using hw₁
      have hnn (i : ι) : 0 ≤ (s : Set ι).indicator w i := by
        by_cases hi : i ∈ s
        · simpa [hi] using hw₀ i hi
        · simp [hi]
      rw [Finset.affineCombination_indicator_subset _ _ s.subset_univ,
        Finset.affineCombination_eq_linear_combination _ _ _ hw1', hleft _ hw1']
      exact ⟨StdSimplex.mem_range_toFun_comp_weights_iff.2 ⟨hnn, hw1'⟩, rfl⟩
    · obtain ⟨w, hw₀, hw₁, rfl⟩ := hp.mem_intrinsicInterior_convexHull_iff.1 hx
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw₁, hleft _ hw₁]
      exact TauCeti.mem_openStdSimplex_iff.2
        ⟨StdSimplex.mem_range_toFun_comp_weights_iff.2 ⟨fun i => (hw₀ i).le, hw₁⟩, hw₀⟩

end AffineIndependent

namespace TauCeti

variable {ι : Type*} [Finite ι] [DecidableEq ι]

/-- **Open coordinate faces of the standard simplex.** The intrinsic interior of the face spanned
by a set `t` of coordinate vertices `Pi.single i 1` consists of the points of that face whose
coordinates in `t` are strictly positive. -/
theorem intrinsicInterior_convexHull_pi_single (t : Set ι) :
    intrinsicInterior ℝ (convexHull ℝ ((fun i : ι => (Pi.single i 1 : ι → ℝ)) '' t)) =
      {x ∈ convexHull ℝ ((fun i : ι => (Pi.single i 1 : ι → ℝ)) '' t) | ∀ i ∈ t, 0 < x i} := by
  classical
  cases nonempty_fintype ι
  ext x
  refine ⟨fun hx => ⟨intrinsicInterior_subset hx, ?_⟩, fun ⟨hx, hpos⟩ => ?_⟩
  · rw [Set.image_eq_range, (affineIndependent_pi_single ℝ t).mem_intrinsicInterior_convexHull_iff]
      at hx
    obtain ⟨w, hw0, hw1, rfl⟩ := hx
    intro i hi
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1, Finset.sum_apply,
      Finset.sum_eq_single ⟨i, hi⟩]
    · simpa using hw0 ⟨i, hi⟩
    · intro j _ hji
      simp [Pi.single_eq_of_ne' (fun h => hji (Subtype.ext h))]
    · simp
  · obtain ⟨hxS, hzero⟩ := mem_convexHull_pi_single_iff.mp hx
    obtain ⟨-, hsum⟩ := StdSimplex.mem_range_toFun_comp_weights_iff.mp hxS
    rw [Set.image_eq_range, (affineIndependent_pi_single ℝ t).mem_intrinsicInterior_convexHull_iff]
    have hw1 : ∑ j : t, x j.val = 1 := by
      have hsub : ∑ j : t, x j.val = ∑ i ∈ univ.filter (· ∈ t), x i :=
        (Finset.sum_subtype _ (fun _ => by simp) x).symm
      rw [hsub, Finset.sum_filter_of_ne fun i _ hxi => by_contra fun hit => hxi (hzero i hit),
        hsum]
    refine ⟨fun j => x j.val, fun j => hpos j.val j.property, hw1, ?_⟩
    rw [Finset.affineCombination_eq_linear_combination _ _ _ hw1]
    have hsub : ∑ j : t, x j.val • (Pi.single (j : ι) 1 : ι → ℝ) =
        ∑ i ∈ univ.filter (· ∈ t), x i • (Pi.single i 1 : ι → ℝ) :=
      (Finset.sum_subtype _ (fun _ => by simp) (fun i => x i • (Pi.single i 1 : ι → ℝ))).symm
    rw [hsub, Finset.sum_filter_of_ne fun i _ hxi =>
      by_contra fun hit => hxi (by simp [hzero i hit]), ← pi_eq_sum_univ']

omit [DecidableEq ι] in
/-- The intrinsic interior of the standard simplex is `TauCeti.openStdSimplex ℝ ι`. -/
theorem intrinsicInterior_range_toFun_comp_weights :
    intrinsicInterior ℝ (range fun s : StdSimplex ℝ ι => ⇑s.weights) = openStdSimplex ℝ ι := by
  classical
  rw [← convexHull_range_pi_single, ← image_univ, intrinsicInterior_convexHull_pi_single]
  ext x
  simp [image_univ, convexHull_range_pi_single]

omit [DecidableEq ι] in
/-- The intrinsic interior of the facet of the standard simplex opposite `i` is
`TauCeti.openStdSimplexFacet ℝ i`. -/
theorem intrinsicInterior_facet_range_toFun_comp_weights (i : ι) :
    intrinsicInterior ℝ {y ∈ range fun s : StdSimplex ℝ ι => ⇑s.weights | y i = 0} =
      openStdSimplexFacet ℝ i := by
  classical
  rw [← convexHull_pi_single_compl_singleton, intrinsicInterior_convexHull_pi_single,
    convexHull_pi_single_compl_singleton]
  ext y
  simp [and_assoc]

end TauCeti
