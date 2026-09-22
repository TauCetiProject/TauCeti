/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.NormLeOne
public import TauCeti.NumberTheory.NumberField.Units.Dirichlet
public import TauCeti.Topology.Frontier
public import TauCeti.Topology.MetricSpace.LipschitzParametrizable

/-!
# A Lipschitz parametrization of the frontier of the norm-≤-one region

`TauCeti.NumberTheory.GeometryOfNumbers.LatticePointCount` counts lattice points in a dilated
region with a power-saving error, but only for regions whose frontier is Lipschitz
parametrizable: `exists_abs_ncard_smul_inter_vadd_sub_le` takes
`IsLipschitzParametrizable (finrank ℝ E - 1) (frontier D)` as a hypothesis. Mathlib proves that
`frontier (normLeOne K)` is *null* (`volume_frontier_normLeOne`), which is what a rate-free limit
needs and is strictly weaker: a null frontier does not provide a quantitative or power-saving
error bound.

This file discharges that hypothesis for `normLeOne K`. Mathlib presents the region through
`expMapBasis`, a partial homeomorphism of `realSpace K` whose image of the box
`paramSet K = univ.pi fun w ↦ if w = w₀ then Iic 0 else Ico 0 1` is the norm-≤-one region up to
`normAtAllPlaces`. The frontier of a box is the union of its faces, so a Lipschitz cover of the
image reduces to parametrizing the image of each face — which is what the maps here do.

The `w₀` face is where the unbounded `Iic 0` direction is pinned at its endpoint; the side faces
pin one of the bounded `Ico 0 1` directions, and there the substitution `t = exp (x w₀)` turns the
unbounded direction into the freed cube coordinate.

## Main results

* `isLipschitzParametrizable_frontier_normLeOne`: the frontier of `normLeOne K` is Lipschitz
  parametrizable in dimension `finrank ℝ (mixedSpace K) - 1`, one less than that of the mixed
  space.
* `frontier_normLeOne_subset_preimage`: that frontier lies over the frontier of the box image,
  through `normAtAllPlaces`.
* `isLipschitzParametrizable_frontier_image_paramSet`: the frontier of the box image is Lipschitz
  parametrizable in dimension `rank K`, one less than that of `realSpace K`.
* `contDiff_expMapBasis`: the box parametrization is smooth.
* `closure_image_paramSet_subset`: the closure of the box image adds only the origin.
* `frontier_image_paramSet_subset`: the frontier of the box image lies in the image of the box's
  frontier, together with the origin.

The face maps that decompose the box's frontier, the lifts that cover the fibres of
`normAtAllPlaces`, and the lemmas supporting them, are `private`: they implement the
parametrization and are not independently reusable.

## References

* C. Birkbeck, [*AINTLIB*](https://github.com/CBirkbeck/AINTLIB) at commit
  `db14b34cc5e3d79603e67c205dfa86b7b989000c` (Apache-2.0),
  `projects/Chebotarev/CebotarevDensity/ForMathlib/NormLeOneLipschitz.lean`, from which the face
  decomposition is adapted: `faceMapZero`, `faceMapSide`, `contDiff_faceMapZero`,
  `contDiff_faceMapSide`, `frontier_image_subset_of_closure_subset` and
  `frontier_image_paramSet_subset` follow that file's declarations of the same names.
  `isLipschitzParametrizable_frontier_normLeOne` is that file's
  `normLeOne_frontier_lipschitz_cover`, and the circle direction of `liftMap` follows its
  `lipschitzWith_exp_ofReal_mul_I`; the sign and angle bookkeeping is arranged differently here,
  through a single globally `C¹` lift rather than that file's `cubeRelabel` scaffolding.
-/

public section

open Finset Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
  NumberField.Units dirichletUnitTheorem
open scoped NumberField

namespace NumberField.mixedEmbedding.fundamentalCone

variable (K : Type*) [Field K] [NumberField K]

/-- `expMapBasis` is `C^n` for every `n`: it is an exponential in the `w₀` coordinate times a
product of real powers of the positive reals `w (fundSystem ...)` in the others. -/
theorem contDiff_expMapBasis {n : WithTop ℕ∞} : ContDiff ℝ n (⇑(expMapBasis (K := K))) := by
  classical
  simp_rw [funext expMapBasis_apply']
  fun_prop (disch := exact fun x ↦ (InfinitePlace.pos_iff.mpr (by simp)).ne')

open scoped Classical in
/-- The face of `paramSet K` on which the unbounded `w₀` coordinate sits at its finite endpoint
`0`, parametrized by the remaining coordinates. -/
private noncomputable def faceMapZero (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  expMapBasis fun w ↦ if hw : w = w₀ then 0 else c ⟨w, hw⟩

open scoped Classical in
/-- The face of `paramSet K` on which the bounded coordinate `i` sits at the endpoint `a`,
parametrized by the remaining coordinates together with `t = exp (x w₀) ∈ (0, 1]` in the slot
that pinning `i` frees. -/
private noncomputable def faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ)
    (c : {w : InfinitePlace K // w ≠ w₀} → ℝ) : realSpace K :=
  c i • expMapBasis fun w ↦ if hw : w = w₀ then 0 else
    if (⟨w, hw⟩ : {w : InfinitePlace K // w ≠ w₀}) = i then a else c ⟨w, hw⟩

open scoped Classical in
/-- The `w₀` face map is `C¹`. -/
private theorem contDiff_faceMapZero : ContDiff ℝ 1 (faceMapZero K) := by
  refine (contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_)
  by_cases hw : w = w₀
  · simpa [hw] using contDiff_const
  · simpa [hw] using contDiff_apply ℝ ℝ _

open scoped Classical in
/-- A side face map is `C¹`. -/
private theorem contDiff_faceMapSide (i : {w : InfinitePlace K // w ≠ w₀}) (a : ℝ) :
    ContDiff ℝ 1 (faceMapSide K i a) := by
  refine (contDiff_apply ℝ ℝ i).smul ((contDiff_expMapBasis K).comp (contDiff_pi.mpr fun w ↦ ?_))
  by_cases hw : w = w₀
  · simpa [hw] using contDiff_const
  · simp only [hw, ↓reduceDIte]
    by_cases hi : (⟨w, hw⟩ : {w : InfinitePlace K // w ≠ w₀}) = i
    · simpa [hi] using contDiff_const
    · simpa [hi] using contDiff_apply ℝ ℝ _

/-- **The closure of the box image adds only the origin.** The origin is what the `w₀` coordinate
escapes to as it runs to `-∞`, and it is the sole reason the closure of the image is not the image
of the closure. -/
theorem closure_image_paramSet_subset :
    closure (expMapBasis '' paramSet K) ⊆ expMapBasis '' closure (paramSet K) ∪ {0} := by
  rw [← compactSet_eq_union]
  exact (isCompact_compactSet K).isClosed.closure_subset_iff.mpr
    ((Set.image_mono subset_closure).trans (expMapBasis_closure_subset_compactSet K))

/-- **The frontier of the box image lies in the image of the box boundary, plus the origin.**
This is the reduction the Lipschitz cover runs on: the boundary of a product of intervals is a
finite union of faces, so parametrizing it reduces to parametrizing each face. -/
theorem frontier_image_paramSet_subset :
    frontier (expMapBasis '' paramSet K) ⊆
      expMapBasis '' frontier (paramSet K) ∪ {0} :=
  TauCeti.frontier_image_subset_of_closure_subset
    (fun _ hs ↦ expMapBasis.isOpen_image_of_subset_source hs (by simp [expMapBasis_source]))
    (injective_expMapBasis K) (closure_image_paramSet_subset K)

variable {K}

open scoped Classical in
/-- **A point of the `w₀` face is hit by `faceMapZero`.** Its cube coordinates are the point's own
coordinates away from `w₀`, which lie in `Icc 0 1` because the point is in the closed box; the
pinned coordinate agrees because the point sits at the face's endpoint `x w₀ = 0`. -/
private theorem expMapBasis_mem_image_faceMapZero {x : realSpace K} (hx : x ∈ closure (paramSet K))
    (hx₀ : x w₀ = 0) :
    expMapBasis x ∈ faceMapZero K '' Set.Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 := by
  rw [closure_paramSet, Set.mem_univ_pi] at hx
  have hmem : ∀ i : {w : InfinitePlace K // w ≠ w₀}, x i ∈ Set.Icc (0 : ℝ) 1 :=
    fun i ↦ by simpa [i.2] using hx i
  refine ⟨fun i ↦ x i, ⟨fun i ↦ (hmem i).1, fun i ↦ (hmem i).2⟩, ?_⟩
  exact congrArg expMapBasis (funext fun w ↦ by by_cases hw : w = w₀ <;> simp [hw, hx₀])

open scoped Classical in
/-- **A point of the side face pinning `i` is hit by `faceMapSide`.** The substitution
`t = exp (x w₀) ∈ (0, 1]` moves the unbounded `w₀` direction into the cube coordinate freed by
pinning `i`, so the cube point is the original coordinates with `i` replaced by `t`. -/
private theorem expMapBasis_mem_image_faceMapSide {x : realSpace K} (hx : x ∈ closure (paramSet K))
    (i : {w : InfinitePlace K // w ≠ w₀}) :
    expMapBasis x ∈
      faceMapSide K i (x i) '' Set.Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 := by
  rw [closure_paramSet, Set.mem_univ_pi] at hx
  have hx₀ : x w₀ ≤ 0 := by simpa using hx w₀
  have hmem : ∀ j : {w : InfinitePlace K // w ≠ w₀}, x j ∈ Set.Icc (0 : ℝ) 1 :=
    fun j ↦ by simpa [j.2] using hx j
  refine ⟨Function.update (fun j : {w : InfinitePlace K // w ≠ w₀} ↦ x j) i (Real.exp (x w₀)),
    ⟨fun j ↦ ?_, fun j ↦ ?_⟩, ?_⟩
  · rcases eq_or_ne j i with rfl | hj
    · simpa using (Real.exp_pos (x w₀)).le
    · simpa [Function.update_of_ne hj] using (hmem j).1
  · rcases eq_or_ne j i with rfl | hj
    · simpa using Real.exp_le_one_iff.2 hx₀
    · simpa [Function.update_of_ne hj] using (hmem j).2
  · rw [faceMapSide, Function.update_self, expMapBasis_apply'' x]
    refine congrArg (fun z : realSpace K ↦ Real.exp (x w₀) • expMapBasis z) (funext fun w ↦ ?_)
    by_cases hw : w = w₀
    · simp [hw]
    · by_cases hwi : (⟨w, hw⟩ : {w : InfinitePlace K // w ≠ w₀}) = i
      · simp [hw, hwi, ← Subtype.ext_iff.mp hwi]
      · simp [hw, hwi]

variable (K)

open scoped Classical in
/-- **The boundary of the box is covered by the faces.** A point of the closed box that misses the
open box has some coordinate at an endpoint: the `w₀` coordinate at `0`, or a bounded coordinate at
`0` or `1`. Those are exactly the faces parametrized by `faceMapZero` and `faceMapSide`. -/
private theorem image_frontier_paramSet_subset :
    expMapBasis '' frontier (paramSet K) ⊆
      faceMapZero K '' Set.Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 ∪
        ⋃ p : {w : InfinitePlace K // w ≠ w₀} × Bool,
          faceMapSide K p.1 (if p.2 then 1 else 0) ''
            Set.Icc (0 : {w : InfinitePlace K // w ≠ w₀} → ℝ) 1 := by
  rintro _ ⟨x, ⟨hxc, hxi⟩, rfl⟩
  have hbox := (closure_paramSet K).subset hxc
  rw [Set.mem_univ_pi] at hbox
  rw [interior_paramSet] at hxi
  have hsome : ∃ w : InfinitePlace K,
      x w ∉ (if w = w₀ then Set.Iio (0 : ℝ) else Set.Ioo 0 1) := by
    by_contra hcon
    push Not at hcon
    exact hxi (Set.mem_univ_pi.2 hcon)
  obtain ⟨w, hw⟩ := hsome
  by_cases hw₀ : w = w₀
  · subst hw₀
    have hge : (0 : ℝ) ≤ x w₀ := by simpa using hw
    exact Or.inl (expMapBasis_mem_image_faceMapZero hxc
      (le_antisymm (by simpa using hbox w₀) hge))
  · have hnot : x w ∉ Set.Ioo (0 : ℝ) 1 := by simpa [hw₀] using hw
    have hmem : x w ∈ Set.Icc (0 : ℝ) 1 := by simpa [hw₀] using hbox w
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hnot
    refine Or.inr ?_
    rcases hnot with h | h
    · exact Set.mem_iUnion.2 ⟨(⟨w, hw₀⟩, false), by
        simpa [le_antisymm h hmem.1] using expMapBasis_mem_image_faceMapSide hxc ⟨w, hw₀⟩⟩
    · exact Set.mem_iUnion.2 ⟨(⟨w, hw₀⟩, true), by
        simpa [le_antisymm hmem.2 h] using expMapBasis_mem_image_faceMapSide hxc ⟨w, hw₀⟩⟩

private theorem isLipschitzParametrizable_image_frontier_paramSet :
    TauCeti.IsLipschitzParametrizable (rank K)
      (expMapBasis '' frontier (paramSet K)) := by
  classical
  have hcard : Fintype.card {w : InfinitePlace K // w ≠ w₀} = rank K :=
    (Fintype.card_congr equivFinRank).symm.trans (Fintype.card_fin _)
  refine .mono ?_ (image_frontier_paramSet_subset K)
  refine .union
    (.image_unitCube_of_contDiffOn hcard (ContDiff.contDiffOn (contDiff_faceMapZero K))) ?_
  exact .iUnion fun p ↦ .image_unitCube_of_contDiffOn hcard
    (ContDiff.contDiffOn (contDiff_faceMapSide K p.1 _))

/-- **The frontier of the box image is Lipschitz parametrizable in codimension one.** This is the
hypothesis `TauCeti.IsLipschitzParametrizable.exists_ncard_smul_add_inter_le` needs to turn a
lattice-point count into a count with a power-saving error term; Mathlib's
`volume_frontier_normLeOne` gives only that the frontier is null, which yields a rate-free
asymptotic but no quantitative error bound.

The dimension is `rank K = #(InfinitePlace K) - 1`, one less than that of `realSpace K`. -/
theorem isLipschitzParametrizable_frontier_image_paramSet :
    TauCeti.IsLipschitzParametrizable (rank K) (frontier (expMapBasis '' paramSet K)) :=
  .mono ((isLipschitzParametrizable_image_frontier_paramSet K).union (.singleton 0)) <|
    frontier_image_paramSet_subset K

/-- **The frontier of the norm-≤-one region sits over the frontier of the box image.**
`normLeOne K` is the preimage of `expMapBasis '' paramSet K` under the continuous
`normAtAllPlaces`, and the frontier of a preimage lies in the preimage of the frontier. -/
theorem frontier_normLeOne_subset_preimage :
    frontier (normLeOne K) ⊆ normAtAllPlaces ⁻¹' frontier (expMapBasis '' paramSet K) := by
  rw [normLeOne_eq_preimage]
  exact (continuous_normAtAllPlaces K).frontier_preimage_subset _

/-- The lift of a point of `realSpace K` to the mixed space, given a choice of sign `s w` at each
real place and of angle at each complex place. The angles range over the unit cube and are
rescaled to `[-π, π]`, so that `liftMap` inverts `normAtAllPlaces` on the nose: every `x` is
`liftMap K s (normAtAllPlaces x, θ)` for the sign vector recording the signs of `x` at the real
places and the `θ` recording its arguments at the complex ones.

This is not `(polarSpaceCoord K).symm`: that inverts a partial homeomorphism, so it is available
only for positive radii and angles in the open interval `(-π, π)`, and it keeps the signed value
at a real place instead of its norm. The cover below needs a map defined — and `C¹` — on the whole
closed cube, and needs the real places to carry a separate choice of sign. -/
private noncomputable def liftMap (s : {w : InfinitePlace K // IsReal w} → Bool)
    (p : realSpace K × ({w : InfinitePlace K // IsComplex w} → ℝ)) : mixedSpace K :=
  (fun w ↦ (if s w then 1 else -1) * p.1 w.1,
    fun w ↦ p.1 w.1 • Complex.exp ((2 * Real.pi * p.2 w - Real.pi) • Complex.I))

open scoped Classical in
/-- Each lift is `C¹`: it is linear at the real places, and a product of a coordinate with a
complex exponential at the complex ones. -/
private theorem contDiff_liftMap (s : {w : InfinitePlace K // IsReal w} → Bool) :
    ContDiff ℝ 1 (liftMap K s) := by
  unfold liftMap
  fun_prop

omit [NumberField K] in
/-- **The lifts cover every fibre of `normAtAllPlaces`.** A point of the mixed space is recovered
from its vector of norms by choosing a sign at each real place and an argument at each complex
place, so the preimage of any `S` is covered by the `2 ^ r₁` lifts of `S` times the cube of
angles. -/
private theorem preimage_subset_iUnion_image_liftMap (S : Set (realSpace K)) :
    normAtAllPlaces ⁻¹' S ⊆ ⋃ s : {w : InfinitePlace K // IsReal w} → Bool,
      liftMap K s '' (S ×ˢ Set.Icc (0 : {w : InfinitePlace K // IsComplex w} → ℝ) 1) := by
  intro x hx
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  -- The sign bit at `w` records whether `x` is nonnegative there, and the cube coordinate at a
  -- complex place is the argument of `x w`, rescaled from `[-π, π]` to `[0, 1]`.
  refine Set.mem_iUnion.2 ⟨fun w ↦ decide (0 ≤ x.1 w), ⟨normAtAllPlaces x,
    fun w ↦ (Complex.arg (x.2 w) + Real.pi) / (2 * Real.pi)⟩, ⟨hx, ⟨fun w ↦ ?_, fun w ↦ ?_⟩⟩, ?_⟩
  · exact div_nonneg (by linarith [Complex.neg_pi_lt_arg (x.2 w)]) hpi.le
  · exact (div_le_one hpi).2 (by linarith [Complex.arg_le_pi (x.2 w)])
  refine Prod.ext (funext fun w ↦ ?_) (funext fun w ↦ ?_)
  · have hnorm : normAtAllPlaces x w.1 = ‖x.1 w‖ := normAtPlace_apply_of_isReal w.2 x
    by_cases h : 0 ≤ x.1 w
    · simp [liftMap, hnorm, h, Real.norm_of_nonneg h]
    · simp [liftMap, hnorm, h, Real.norm_of_nonpos (not_le.1 h).le]
  · have hnorm : normAtAllPlaces x w.1 = ‖x.2 w‖ := normAtPlace_apply_of_isComplex w.2 x
    have hang : 2 * Real.pi * ((Complex.arg (x.2 w) + Real.pi) / (2 * Real.pi)) - Real.pi
        = Complex.arg (x.2 w) := by
      field_simp
      ring
    simp only [liftMap, hnorm, hang, Complex.real_smul]
    exact Complex.norm_mul_exp_arg_mul_I _

open scoped Classical in
/-- **The frontier of the norm-≤-one region is Lipschitz parametrizable in codimension one.**
This discharges the boundary hypothesis of `TauCeti.exists_abs_ncard_smul_inter_vadd_sub_le` for
`normLeOne K`, whose frontier Mathlib knows only to be null (`volume_frontier_normLeOne`) — a
null frontier supports a rate-free limit but gives no quantitative or power-saving error bound.

The frontier lies over the frontier of the box image, which is parametrizable in dimension
`rank K`; each fibre of `normAtAllPlaces` adds the `r₂` angles at the complex places and a choice
of sign at each of the `r₁` real places, and `rank K + r₂ = finrank ℝ (mixedSpace K) - 1`. -/
theorem isLipschitzParametrizable_frontier_normLeOne :
    TauCeti.IsLipschitzParametrizable (finrank ℝ (mixedSpace K) - 1) (frontier (normLeOne K)) := by
  have hcube : TauCeti.IsLipschitzParametrizable (nrComplexPlaces K)
      (Set.Icc (0 : {w : InfinitePlace K // IsComplex w} → ℝ) 1) := by
    simpa using TauCeti.IsLipschitzParametrizable.image_unitCube_of_contDiffOn
      (d := nrComplexPlaces K) (f := id) rfl contDiffOn_id
  -- `rank K + r₂` is the codimension-one dimension: the identity is
  -- `NumberField.rank_add_nrComplexPlaces_add_one`, transported across `mixedEmbedding.finrank`.
  have hdim : rank K + nrComplexPlaces K = finrank ℝ (mixedSpace K) - 1 := by
    rw [mixedEmbedding.finrank, ← rank_add_nrComplexPlaces_add_one K]
    omega
  rw [← hdim]
  refine .mono (.iUnion fun s ↦ .image_of_locallyLipschitz (contDiff_liftMap K s).locallyLipschitz
    ((isLipschitzParametrizable_frontier_image_paramSet K).prod hcube)) ?_
  exact (frontier_normLeOne_subset_preimage K).trans
    (preimage_subset_iUnion_image_liftMap K _)

end NumberField.mixedEmbedding.fundamentalCone
