/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.AlgebraicTopology.SemilocallySimplyConnected.Basic
public import TauCeti.Topology.Algebra.Module.LocallyConvex

/-!
# The thrice-punctured sphere

The thrice-punctured sphere `ℙ¹(ℂ) ∖ {0, 1, ∞}` is the base of the three-point covers classified
by permutation triples and dessins d'enfants. This file fixes its affine model
`TauCeti.ThricePuncturedSphere := {z : ℂ // z ≠ 0 ∧ z ≠ 1}`, together with the point-set facts the
computation of its fundamental group and the classification of its finite covers run on.

* **The space.** It is an open subset of `ℂ`, hence Hausdorff, second countable, strongly locally
  contractible, locally path-connected and semilocally simply connected; it is path-connected
  because the complement of a countable set in `ℂ` is. The inclusion into the Riemann sphere
  `OnePoint ℂ` is an open embedding whose range is the complement of `{0, 1, ∞}`, which is what
  makes the name honest.
* **The basepoint** `b = 1/2`, on the real segment between the punctures `0` and `1`.
* **The standard two-set cover** by `A = {z | re z < 1}` and `B = {z | 0 < re z}`. The set `A`
  is the convex half-plane `re z < 1` with the puncture `0` removed, `B` is the half-plane
  `0 < re z` with the puncture `1` removed, and `A ∩ B` is the open vertical strip
  `0 < re z < 1`, with no point removed because both punctures lie on its boundary lines. The
  strip is convex, so `A ∩ B` is path-connected and simply connected, and it contains `b`. These
  are the hypotheses on the intersection in the Seifert–van Kampen theorem for two open sets with
  simply connected intersection, through which `π₁` of the thrice-punctured sphere is computed to
  be free of rank two.

## Main declarations

* `TauCeti.ThricePuncturedSphere`: the space `ℂ ∖ {0, 1}`.
* `TauCeti.ThricePuncturedSphere.range_coe`, `TauCeti.ThricePuncturedSphere.isOpenEmbedding_coe`:
  the open embedding into `ℂ`, with range `{0, 1}ᶜ`.
* `TauCeti.ThricePuncturedSphere.toOnePoint`, `isOpenEmbedding_toOnePoint`,
  `range_toOnePoint`: the open embedding into the Riemann sphere, with range `{0, 1, ∞}ᶜ`.
* `TauCeti.ThricePuncturedSphere.basePt`: the basepoint `1/2`.
* `TauCeti.ThricePuncturedSphere.leftOpen`, `TauCeti.ThricePuncturedSphere.rightOpen`: the open
  sets `A` and `B` of the standard cover, with `leftOpen_union_rightOpen`, `image_coe_leftOpen`,
  `image_coe_rightOpen`, `image_coe_leftOpen_inter_rightOpen`,
  `isSimplyConnected_leftOpen_inter_rightOpen` and `isPathConnected_leftOpen_inter_rightOpen`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  §2.4 (the thrice-punctured sphere as the base of three-point covers).
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 1.20 (the
  Seifert–van Kampen theorem whose hypotheses the standard cover satisfies).
-/

public section

open Set Topology OnePoint

namespace TauCeti

/-- The **thrice-punctured sphere** `ℙ¹(ℂ) ∖ {0, 1, ∞}`, in its affine model `ℂ ∖ {0, 1}`. The
point `∞` is removed by working in `ℂ`; `TauCeti.ThricePuncturedSphere.range_toOnePoint` identifies
it with the complement of `{0, 1, ∞}` in the Riemann sphere `OnePoint ℂ`. -/
abbrev ThricePuncturedSphere : Type := {z : ℂ // z ≠ 0 ∧ z ≠ 1}

namespace ThricePuncturedSphere

/-- A point of the thrice-punctured sphere is not the puncture `0`. -/
@[simp]
theorem ne_zero (z : ThricePuncturedSphere) : (z : ℂ) ≠ 0 := z.2.1

/-- A point of the thrice-punctured sphere is not the puncture `1`. -/
@[simp]
theorem ne_one (z : ThricePuncturedSphere) : (z : ℂ) ≠ 1 := z.2.2

/-- The points of `ℂ` underlying the thrice-punctured sphere are those other than `0` and `1`. -/
theorem range_coe : range ((↑) : ThricePuncturedSphere → ℂ) = {0, 1}ᶜ := by
  ext z
  simp [Subtype.range_coe_subtype, not_or]

/-- The inclusion of the thrice-punctured sphere into `ℂ` is an open embedding. -/
theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ThricePuncturedSphere → ℂ) :=
  (isOpen_ne.inter isOpen_ne : IsOpen {z : ℂ | z ≠ 0 ∧ z ≠ 1}).isOpenEmbedding_subtypeVal

/-- The thrice-punctured sphere is strongly locally contractible, being an open subset of `ℂ`. In
particular it is locally path-connected and semilocally simply connected. -/
instance : StronglyLocallyContractibleSpace ThricePuncturedSphere :=
  isOpenEmbedding_coe.stronglyLocallyContractibleSpace

/-- The thrice-punctured sphere is path-connected: the complement of a countable set in `ℂ` is
path-connected, since `ℂ` has real dimension two. -/
instance : PathConnectedSpace ThricePuncturedSphere := by
  rw [pathConnectedSpace_iff_univ, isOpenEmbedding_coe.isInducing.isPathConnected_iff, image_univ,
    range_coe]
  refine (Set.toFinite _).countable.isPathConnected_compl_of_one_lt_rank ?_
  rw [Complex.rank_real_complex]
  exact Nat.one_lt_ofNat

/-! ### The Riemann sphere -/

/-- The inclusion of the thrice-punctured sphere into the Riemann sphere `OnePoint ℂ`. -/
def toOnePoint (z : ThricePuncturedSphere) : OnePoint ℂ := (z : ℂ)

@[simp]
theorem toOnePoint_apply (z : ThricePuncturedSphere) : toOnePoint z = ((z : ℂ) : OnePoint ℂ) :=
  (rfl)

/-- The thrice-punctured sphere is an open subspace of the Riemann sphere. -/
theorem isOpenEmbedding_toOnePoint : IsOpenEmbedding toOnePoint :=
  OnePoint.isOpenEmbedding_coe.comp isOpenEmbedding_coe

/-- The range of the inclusion into the Riemann sphere is the complement of the three punctures
`0`, `1` and `∞`. -/
theorem range_toOnePoint :
    range toOnePoint =
      ({((0 : ℂ) : OnePoint ℂ), ((1 : ℂ) : OnePoint ℂ), ∞} : Set (OnePoint ℂ))ᶜ := by
  ext w
  induction w using OnePoint.rec with
  | infty => simp [toOnePoint]
  | coe z => simp [toOnePoint, not_or]

/-! ### The basepoint -/

/-- The basepoint `b = 1/2` of the thrice-punctured sphere, on the real segment between the
punctures `0` and `1`. -/
noncomputable def basePt : ThricePuncturedSphere :=
  ⟨1 / 2, by norm_num, by norm_num⟩

@[simp]
theorem coe_basePt : (basePt : ℂ) = 1 / 2 :=
  (rfl)

/-! ### The standard two-set cover -/

/-- The open set `A = {z | re z < 1}` of the standard two-set cover of the thrice-punctured sphere:
the half-plane `re z < 1` with the puncture `0` removed. -/
def leftOpen : Set ThricePuncturedSphere :=
  {z | (z : ℂ).re < 1}

/-- The open set `B = {z | 0 < re z}` of the standard two-set cover of the thrice-punctured sphere:
the half-plane `0 < re z` with the puncture `1` removed. -/
def rightOpen : Set ThricePuncturedSphere :=
  {z | 0 < (z : ℂ).re}

@[simp]
theorem mem_leftOpen {z : ThricePuncturedSphere} : z ∈ leftOpen ↔ (z : ℂ).re < 1 :=
  Iff.rfl

@[simp]
theorem mem_rightOpen {z : ThricePuncturedSphere} : z ∈ rightOpen ↔ 0 < (z : ℂ).re :=
  Iff.rfl

/-- The set `leftOpen` is open in the thrice-punctured sphere. -/
theorem isOpen_leftOpen : IsOpen leftOpen :=
  isOpen_lt (Complex.continuous_re.comp continuous_subtype_val) continuous_const

/-- The set `rightOpen` is open in the thrice-punctured sphere. -/
theorem isOpen_rightOpen : IsOpen rightOpen :=
  isOpen_lt continuous_const (Complex.continuous_re.comp continuous_subtype_val)

/-- The two open sets `A` and `B` cover the thrice-punctured sphere: a point with `re z < 1` lies
in `A`, and otherwise `re z ≥ 1 > 0` puts it in `B`. -/
@[simp]
theorem leftOpen_union_rightOpen : leftOpen ∪ rightOpen = univ := by
  refine eq_univ_of_forall fun z ↦ ?_
  by_cases h : (z : ℂ).re < 1
  · exact Or.inl h
  · exact Or.inr (by simp only [mem_rightOpen]; linarith)

/-- In `ℂ`, the set `A` is the half-plane `re z < 1` with the puncture `0` removed. The point `1`
is not removed, as it does not lie in the half-plane. -/
theorem image_coe_leftOpen : (↑) '' leftOpen = {z : ℂ | z.re < 1} \ {0} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.ne_zero⟩
  · rintro ⟨hz, hz0 : z ≠ 0⟩
    refine ⟨⟨z, hz0, ?_⟩, hz, rfl⟩
    rintro rfl
    simp at hz

/-- In `ℂ`, the set `B` is the half-plane `0 < re z` with the puncture `1` removed. The point `0`
is not removed, as it does not lie in the half-plane. -/
theorem image_coe_rightOpen : (↑) '' rightOpen = {z : ℂ | 0 < z.re} \ {1} := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨hw, w.ne_one⟩
  · rintro ⟨hz, hz1 : z ≠ 1⟩
    refine ⟨⟨z, ?_, hz1⟩, hz, rfl⟩
    rintro rfl
    simp at hz

/-- In `ℂ`, the intersection `A ∩ B` is the open vertical strip `0 < re z < 1`, with no point
removed: both punctures lie on the boundary lines of the strip. -/
theorem image_coe_leftOpen_inter_rightOpen :
    (↑) '' (leftOpen ∩ rightOpen) = {z : ℂ | 0 < z.re ∧ z.re < 1} := by
  ext z
  constructor
  · rintro ⟨w, ⟨hw₁, hw₂⟩, rfl⟩
    exact ⟨hw₂, hw₁⟩
  · rintro ⟨hz₀, hz₁⟩
    refine ⟨⟨z, ?_, ?_⟩, ⟨hz₁, hz₀⟩, rfl⟩
    · rintro rfl
      simp at hz₀
    · rintro rfl
      simp at hz₁

/-- The intersection `A ∩ B` of the standard two-set cover is simply connected: it is
homeomorphic to the open vertical strip `0 < re z < 1`, which is convex and nonempty, hence
contractible. -/
theorem isSimplyConnected_leftOpen_inter_rightOpen :
    IsSimplyConnected (leftOpen ∩ rightOpen) := by
  rw [← isOpenEmbedding_coe.isEmbedding.isSimplyConnected_image,
    image_coe_leftOpen_inter_rightOpen]
  have hconv : Convex ℝ {z : ℂ | 0 < z.re ∧ z.re < 1} :=
    (convex_halfSpace_re_gt 0).inter (convex_halfSpace_re_lt 1)
  have := hconv.contractibleSpace ⟨1 / 2, by norm_num, by norm_num⟩
  exact SimplyConnectedSpace.ofContractible _

/-- The intersection `A ∩ B` of the standard two-set cover is path-connected. -/
theorem isPathConnected_leftOpen_inter_rightOpen :
    IsPathConnected (leftOpen ∩ rightOpen) :=
  isSimplyConnected_leftOpen_inter_rightOpen.isPathConnected

/-- The basepoint `1/2` lies in `leftOpen`. -/
theorem basePt_mem_leftOpen : basePt ∈ leftOpen := by
  simp only [mem_leftOpen, coe_basePt]
  norm_num

/-- The basepoint `1/2` lies in `rightOpen`. -/
theorem basePt_mem_rightOpen : basePt ∈ rightOpen := by
  simp only [mem_rightOpen, coe_basePt]
  norm_num

/-- The basepoint `1/2` lies in the strip `A ∩ B`. -/
theorem basePt_mem_leftOpen_inter_rightOpen : basePt ∈ leftOpen ∩ rightOpen :=
  ⟨basePt_mem_leftOpen, basePt_mem_rightOpen⟩

end ThricePuncturedSphere

end TauCeti
