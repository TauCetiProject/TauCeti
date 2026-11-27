/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Iterated function systems and their attractors

An iterated function system `F : TauCeti.IFS ι X` on a metric space `X` is a family of maps
`F i : X → X`, indexed by `i : ι`, together with numbers `F.ratio i` in the open interval `(0, 1)`
such that `F i` is Lipschitz with constant `F.ratio i`. The ratio is data: it is a prescribed upper
bound for the Lipschitz constant, not the Lipschitz constant itself. An attractor of `F` is a
nonempty compact set `K` with `⋃ i, F i '' K = K` (`TauCeti.IFS.IsAttractor`).

A word `w = [i₁, …, iₙ]` has the composite `F.wordMap w = F i₁ ∘ ⋯ ∘ F iₙ` (the first letter is
applied last) and the ratio `F.wordRatio w = F.ratio i₁ * ⋯ * F.ratio iₙ`; the empty word has the
identity and the ratio `1`. The composite of a word is Lipschitz with the ratio of the word
(`TauCeti.IFS.lipschitzWith_wordMap`), and the ratio of a word of length `n` is at most
`F.maxRatio ^ n`, where `F.maxRatio` is the supremum of the ratios
(`TauCeti.IFS.wordRatio_le_maxRatio_pow`).

An attractor is the union of its images under the words of each fixed length
(`TauCeti.IFS.IsAttractor.iUnion_wordMap_image_eq`), and the image of a set under the word `w`
has diameter at most `F.wordRatio w` times the diameter of the set
(`TauCeti.IFS.ediam_wordMap_image_le`, `TauCeti.IFS.diam_wordMap_image_le`).
An empty index type has no attractor (`TauCeti.IFS.not_isAttractor_of_isEmpty`), and a singleton
is an attractor exactly when its point is fixed by every map
(`TauCeti.IFS.isAttractor_singleton_iff`).

## References

* J. E. Hutchinson, *Fractals and self similarity*, Indiana Univ. Math. J. 30 (1981), 713–747,
  section 3.1.
* C. J. Bishop and Y. Peres, *Fractals in Probability and Analysis*, section 2.1.
-/

public section

open Function Metric Set
open scoped NNReal ENNReal

namespace TauCeti

/-- An iterated function system on a metric space `X` indexed by `ι`: a family of maps
`toFun i : X → X`, each Lipschitz with a prescribed constant `ratio i` in the open interval
`(0, 1)`. -/
structure IFS (ι X : Type*) [MetricSpace X] where
  /-- The maps of the system. -/
  toFun : ι → X → X
  /-- The prescribed contraction ratios, upper bounds for the Lipschitz constants of the maps. -/
  ratio : ι → ℝ≥0
  /-- Every ratio is positive. -/
  ratio_pos : ∀ i, 0 < ratio i
  /-- Every ratio is less than one. -/
  ratio_lt_one : ∀ i, ratio i < 1
  /-- Each map is Lipschitz with its prescribed ratio. -/
  lipschitz : ∀ i, LipschitzWith (ratio i) (toFun i)

namespace IFS

variable {ι X : Type*} [MetricSpace X] (F : IFS ι X)

attribute [coe] toFun

/-- An iterated function system is used as the family of its maps. -/
instance : CoeFun (IFS ι X) fun _ ↦ ι → X → X := ⟨toFun⟩

/-- Two iterated function systems with the same maps and the same ratios are equal. -/
@[ext]
theorem ext {F G : IFS ι X} (h : ∀ i, F i = G i) (hr : ∀ i, F.ratio i = G.ratio i) : F = G := by
  cases F
  cases G
  congr
  · exact funext h
  · exact funext hr

/-- Each map of an iterated function system is a contraction with its prescribed ratio. -/
theorem contractingWith (i : ι) : ContractingWith (F.ratio i) (F i) :=
  ⟨F.ratio_lt_one i, F.lipschitz i⟩

/-- Each map of an iterated function system is continuous. -/
protected theorem continuous (i : ι) : Continuous (F i) :=
  (F.lipschitz i).continuous

theorem ratio_ne_zero (i : ι) : F.ratio i ≠ 0 :=
  (F.ratio_pos i).ne'

theorem ratio_le_one (i : ι) : F.ratio i ≤ 1 :=
  (F.ratio_lt_one i).le

/-! ### The largest ratio -/

/-- The largest ratio of an iterated function system: the supremum of the ratios, which is `0` for
an empty index type. -/
noncomputable def maxRatio : ℝ≥0 :=
  ⨆ i, F.ratio i

theorem bddAbove_range_ratio : BddAbove (range F.ratio) :=
  ⟨1, forall_mem_range.2 F.ratio_le_one⟩

theorem ratio_le_maxRatio (i : ι) : F.ratio i ≤ F.maxRatio :=
  le_ciSup F.bddAbove_range_ratio i

theorem maxRatio_le_iff {c : ℝ≥0} : F.maxRatio ≤ c ↔ ∀ i, F.ratio i ≤ c :=
  ciSup_le_iff' F.bddAbove_range_ratio

theorem maxRatio_le_one : F.maxRatio ≤ 1 :=
  F.maxRatio_le_iff.2 F.ratio_le_one

theorem maxRatio_pos [Nonempty ι] : 0 < F.maxRatio :=
  (F.ratio_pos (Classical.arbitrary ι)).trans_le (F.ratio_le_maxRatio _)

theorem maxRatio_eq_zero [IsEmpty ι] : F.maxRatio = 0 := by
  simp [maxRatio]

/-- For a finite index type the largest ratio is less than one; this fails for infinitely many
ratios accumulating at `1`. -/
theorem maxRatio_lt_one [Finite ι] : F.maxRatio < 1 := by
  cases isEmpty_or_nonempty ι
  · simp [F.maxRatio_eq_zero]
  · obtain ⟨i, hi⟩ := exists_eq_ciSup_of_finite (f := F.ratio)
    rw [maxRatio, ← hi]
    exact F.ratio_lt_one i

/-! ### Words -/

/-- The composite `F i₁ ∘ ⋯ ∘ F iₙ` of the maps along the word `w = [i₁, …, iₙ]`; the first letter
is applied last, and the empty word gives the identity. -/
def wordMap (w : List ι) : X → X :=
  w.foldr (fun i g ↦ F i ∘ g) id

/-- The ratio `F.ratio i₁ * ⋯ * F.ratio iₙ` of the word `w = [i₁, …, iₙ]`; the empty word has ratio
`1`. -/
def wordRatio (w : List ι) : ℝ≥0 :=
  (w.map F.ratio).prod

@[simp]
theorem wordMap_nil : F.wordMap [] = id :=
  (rfl)

@[simp]
theorem wordMap_cons (i : ι) (w : List ι) : F.wordMap (i :: w) = F i ∘ F.wordMap w :=
  (rfl)

@[simp]
theorem wordMap_append (v w : List ι) : F.wordMap (v ++ w) = F.wordMap v ∘ F.wordMap w := by
  induction v with
  | nil => simp
  | cons i v ih => simp [ih, comp_assoc]

@[simp]
theorem wordRatio_nil : F.wordRatio [] = 1 :=
  (rfl)

@[simp]
theorem wordRatio_cons (i : ι) (w : List ι) : F.wordRatio (i :: w) = F.ratio i * F.wordRatio w :=
  List.prod_cons

@[simp]
theorem wordRatio_append (v w : List ι) : F.wordRatio (v ++ w) = F.wordRatio v * F.wordRatio w := by
  simp [wordRatio]

theorem wordRatio_pos (w : List ι) : 0 < F.wordRatio w := by
  induction w with
  | nil => simp
  | cons i w ih => simpa using mul_pos (F.ratio_pos i) ih

theorem wordRatio_le_one (w : List ι) : F.wordRatio w ≤ 1 := by
  induction w with
  | nil => simp
  | cons i w ih => simpa using mul_le_one' (F.ratio_le_one i) ih

/-- The ratio of a word of length `n` is at most the `n`-th power of the largest ratio. -/
theorem wordRatio_le_maxRatio_pow (w : List ι) : F.wordRatio w ≤ F.maxRatio ^ w.length := by
  induction w with
  | nil => simp
  | cons i w ih =>
    simpa [pow_succ'] using mul_le_mul' (F.ratio_le_maxRatio i) ih

/-- The composite of the maps along a word is Lipschitz with the ratio of the word. -/
theorem lipschitzWith_wordMap (w : List ι) : LipschitzWith (F.wordRatio w) (F.wordMap w) := by
  induction w with
  | nil => simpa using LipschitzWith.id
  | cons i w ih => simpa using (F.lipschitz i).comp ih

/-- The image of a set under the composite of a word has extended diameter at most the ratio of
the word times the extended diameter of the set. -/
theorem ediam_wordMap_image_le (w : List ι) (s : Set X) :
    ediam (F.wordMap w '' s) ≤ F.wordRatio w * ediam s :=
  (F.lipschitzWith_wordMap w).ediam_image_le s

/-- The image of a bounded set under the composite of a word has diameter at most the ratio of the
word times the diameter of the set. -/
theorem diam_wordMap_image_le (w : List ι) {s : Set X} (hs : Bornology.IsBounded s) :
    diam (F.wordMap w '' s) ≤ F.wordRatio w * diam s :=
  (F.lipschitzWith_wordMap w).diam_image_le s hs

/-! ### Attractors -/

/-- An attractor of an iterated function system `F` is a nonempty compact set `K` equal to the
union `⋃ i, F i '' K` of its images under the maps of the system. -/
structure IsAttractor (K : Set X) : Prop where
  /-- An attractor is compact. -/
  isCompact : IsCompact K
  /-- An attractor is nonempty. -/
  nonempty : K.Nonempty
  /-- An attractor is the union of its images under the maps of the system. -/
  iUnion_image_eq : ⋃ i, F i '' K = K

variable {F} {K : Set X}

theorem isAttractor_iff : F.IsAttractor K ↔ IsCompact K ∧ K.Nonempty ∧ ⋃ i, F i '' K = K :=
  ⟨fun h ↦ ⟨h.isCompact, h.nonempty, h.iUnion_image_eq⟩, fun h ↦ ⟨h.1, h.2.1, h.2.2⟩⟩

namespace IsAttractor

/-- An iterated function system with an attractor has a nonempty index type. -/
theorem nonempty_index (hK : F.IsAttractor K) : Nonempty ι := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := hK.iUnion_image_eq
  rw [iUnion_of_empty] at this
  exact hK.nonempty.ne_empty this.symm

theorem image_subset (hK : F.IsAttractor K) (i : ι) : F i '' K ⊆ K := by
  conv_rhs => rw [← hK.iUnion_image_eq]
  exact subset_iUnion (fun i ↦ F i '' K) i

theorem mapsTo (hK : F.IsAttractor K) (i : ι) : MapsTo (F i) K K :=
  mapsTo_iff_image_subset.2 (hK.image_subset i)

theorem wordMap_image_subset (hK : F.IsAttractor K) (w : List ι) : F.wordMap w '' K ⊆ K := by
  induction w with
  | nil => simp
  | cons i w ih =>
    rw [wordMap_cons, image_comp]
    exact (image_mono ih).trans (hK.image_subset i)

/-- Every point of an attractor lies in the image of the attractor under some word of each given
length. -/
theorem exists_mem_wordMap_image (hK : F.IsAttractor K) {x : X} (hx : x ∈ K) (n : ℕ) :
    ∃ w : List ι, w.length = n ∧ x ∈ F.wordMap w '' K := by
  induction n generalizing x with
  | zero => exact ⟨[], rfl, by simpa using hx⟩
  | succ n ih =>
    rw [← hK.iUnion_image_eq, mem_iUnion] at hx
    obtain ⟨i, y, hy, rfl⟩ := hx
    obtain ⟨w, hw, hyw⟩ := ih hy
    refine ⟨i :: w, by simp [hw], ?_⟩
    rw [wordMap_cons, image_comp]
    exact mem_image_of_mem _ hyw

/-- An attractor is the union of its images under the words of each fixed length
(Hutchinson 1981, 3.1(1)). -/
theorem iUnion_wordMap_image_eq (hK : F.IsAttractor K) (n : ℕ) :
    ⋃ (w : List ι) (_ : w.length = n), F.wordMap w '' K = K := by
  refine (iUnion₂_subset fun w _ ↦ hK.wordMap_image_subset w).antisymm fun x hx ↦ ?_
  obtain ⟨w, hw, hxw⟩ := hK.exists_mem_wordMap_image hx n
  exact mem_iUnion₂.2 ⟨w, hw, hxw⟩

/-- The image of an attractor under a word has diameter at most the ratio of the word times the
diameter of the attractor (Hutchinson 1981, 3.1(3)(ii)). -/
theorem diam_wordMap_image_le (hK : F.IsAttractor K) (w : List ι) :
    diam (F.wordMap w '' K) ≤ F.wordRatio w * diam K :=
  F.diam_wordMap_image_le w hK.isCompact.isBounded

end IsAttractor

/-- For an empty index type the union of the images is empty, so there is no attractor. -/
theorem not_isAttractor_of_isEmpty [IsEmpty ι] (F : IFS ι X) (K : Set X) : ¬ F.IsAttractor K :=
  fun hK ↦ have := hK.nonempty_index; not_isEmpty_of_nonempty ι ‹_›

/-- For a nonempty index type, a singleton `{x}` is an attractor exactly when `x` is a fixed point
of every map of the system. -/
theorem isAttractor_singleton_iff [Nonempty ι] {x : X} :
    F.IsAttractor {x} ↔ ∀ i, F i x = x := by
  simp only [isAttractor_iff, isCompact_singleton, singleton_nonempty, image_singleton,
    iUnion_singleton_eq_range, true_and, Set.ext_iff, mem_range, mem_singleton_iff]
  refine ⟨fun h i ↦ (h (F i x)).1 ⟨i, rfl⟩, fun h y ↦ ⟨?_, ?_⟩⟩
  · rintro ⟨i, rfl⟩
    exact h i
  · rintro rfl
    exact ⟨Classical.arbitrary ι, h _⟩

end IFS

end TauCeti
