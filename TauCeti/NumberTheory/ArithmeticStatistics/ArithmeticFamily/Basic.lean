/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Order.Northcott.Basic
public import Mathlib.NumberTheory.Height.NumberField

/-!
# Arithmetic families and finite height counts

An `ArithmeticFamily ι` equips its carrier with a real-valued Northcott height. The carrier
specifies the objects being counted: use a quotient carrier to count isomorphism classes,
and a pullback with its explicit fibre multiplicities to count representatives.

Inclusive counts, strict counts and weighted counts are finite at every real cutoff.
Finite-fibre pullbacks and positive rescalings preserve this finiteness; a quotient height
defines a family once its own Northcott finiteness is supplied.
Natural-valued heights recover `TauCeti.normLE` and `TauCeti.summatory`; multiplicative Weil
height gives a family on the elements of a number field.
-/

public section

namespace TauCeti

/-- A family of objects with a real-valued height having finite inclusive sublevels.
The carrier already incorporates any equivalence relation used in counting the objects. -/
@[ext]
structure ArithmeticFamily (ι : Type*) where
  /-- The height of an object. -/
  height : ι → ℝ
  /-- Every bounded-height subfamily is finite. -/
  northcott : Northcott height

attribute [instance] ArithmeticFamily.northcott

namespace ArithmeticFamily

variable {ι κ : Type*} (F : ArithmeticFamily ι)

/-- Every inclusive height sublevel is finite. -/
theorem finite_height_le (X : ℝ) : {i | F.height i ≤ X}.Finite :=
  Northcott.finite_le X

/-- The finite carrier at an inclusive real cutoff. -/
noncomputable def heightLE (X : ℝ) : Finset ι := (F.finite_height_le X).toFinset

/-- Membership in the inclusive carrier is exactly the height inequality. -/
@[simp, grind =]
theorem mem_heightLE {i : ι} {X : ℝ} : i ∈ F.heightLE X ↔ F.height i ≤ X := by
  simp [heightLE]

/-- The finite carrier represents the inclusive height sublevel set. -/
@[simp]
theorem coe_heightLE (X : ℝ) : (F.heightLE X : Set ι) = {i | F.height i ≤ X} := by
  ext
  simp

/-- Enlarging the cutoff enlarges the finite carrier. -/
theorem heightLE_mono : Monotone F.heightLE := fun _ _ h _ hi ↦
  (mem_heightLE F).mpr (((mem_heightLE F).mp hi).trans h)

/-- Every finite collection of objects is eventually included in the height carrier. -/
theorem tendsto_heightLE_atTop : Filter.Tendsto F.heightLE Filter.atTop Filter.atTop :=
  Filter.tendsto_atTop_finset_of_monotone F.heightLE_mono fun i ↦
    ⟨F.height i, (mem_heightLE F).mpr le_rfl⟩

/-- Sum a weight over the inclusive height sublevel. -/
noncomputable def weightedCount {M : Type*} [AddCommMonoid M] (w : ι → M) (X : ℝ) : M :=
  ∑ i ∈ F.heightLE X, w i

/-- Evaluate a weighted count as a finite sum over its inclusive height carrier. -/
theorem weightedCount_apply {M : Type*} [AddCommMonoid M] (w : ι → M) (X : ℝ) :
    F.weightedCount w X = ∑ i ∈ F.heightLE X, w i := by
  rw [weightedCount]

/-- Count the members of a subfamily at an inclusive height cutoff. -/
noncomputable def count (S : Set ι) (X : ℝ) : ℕ := by
  classical
  exact ((F.heightLE X).filter (· ∈ S)).card

/-- Count the members of a subfamily at a strict height cutoff. -/
noncomputable def countLT (S : Set ι) (X : ℝ) : ℕ := by
  classical
  exact ((F.heightLE X).filter fun i ↦ i ∈ S ∧ F.height i < X).card

/-- The inclusive count is the cardinality of the indicated finite set. -/
theorem count_eq_ncard (S : Set ι) (X : ℝ) :
    F.count S X = {i ∈ S | F.height i ≤ X}.ncard := by
  classical
  rw [count, ← Set.ncard_coe_finset]
  congr 1
  ext
  simp [and_comm]

/-- The strict count is the cardinality of the indicated finite set. -/
theorem countLT_eq_ncard (S : Set ι) (X : ℝ) :
    F.countLT S X = {i ∈ S | F.height i < X}.ncard := by
  classical
  rw [countLT, ← Set.ncard_coe_finset]
  congr 1
  ext
  simp only [Finset.mem_coe, Finset.mem_filter, mem_heightLE, Set.mem_ofPred_eq]
  grind

/-- The empty subfamily has inclusive count zero. -/
@[simp]
theorem count_empty (X : ℝ) : F.count ∅ X = 0 := by
  simp [count]

/-- The empty subfamily has strict count zero. -/
@[simp]
theorem countLT_empty (X : ℝ) : F.countLT ∅ X = 0 := by
  simp [countLT]

/-- Counting is weighted counting with an indicator weight. -/
theorem count_eq_weightedCount_indicator (S : Set ι) (X : ℝ) :
    (F.count S X : ℝ) = F.weightedCount (S.indicator (fun _ ↦ (1 : ℝ))) X := by
  classical
  simp [count, weightedCount, Set.indicator_apply]

/-- Inclusion of subfamilies gives an inequality of counts. -/
theorem count_mono_set {S T : Set ι} (h : S ⊆ T) (X : ℝ) : F.count S X ≤ F.count T X := by
  classical
  exact Finset.card_le_card fun i hi ↦ Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hi).1, h (Finset.mem_filter.mp hi).2⟩

/-- Inclusive counts are monotone in the cutoff. -/
theorem count_mono (S : Set ι) : Monotone (F.count S) := by
  classical
  intro X Y h
  exact Finset.card_le_card (Finset.filter_subset_filter _ (F.heightLE_mono h))

/-- Counts add on disjoint subfamilies. -/
theorem count_union_of_disjoint {S T : Set ι} (h : Disjoint S T) (X : ℝ) :
    F.count (S ∪ T) X = F.count S X + F.count T X := by
  classical
  simp only [count, Set.mem_union, Finset.filter_or]
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_left.mpr fun i hi hj ↦
    Set.disjoint_left.mp h (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hj).2

/-- Counts are subadditive. -/
theorem count_union_le (S T : Set ι) (X : ℝ) :
    F.count (S ∪ T) X ≤ F.count S X + F.count T X := by
  classical
  simp only [count, Set.mem_union, Finset.filter_or]
  exact Finset.card_union_le _ _

/-- A count splits into the parts inside and outside a second subfamily. -/
theorem count_inter_add_count_sdiff (S T : Set ι) (X : ℝ) :
    F.count (S ∩ T) X + F.count (S \ T) X = F.count S X := by
  rw [← count_union_of_disjoint _ Set.disjoint_sdiff_inter.symm, Set.inter_union_sdiff]

/-- A finite subfamily has count at most its cardinality. -/
theorem count_le_ncard {S : Set ι} (hS : S.Finite) (X : ℝ) : F.count S X ≤ S.ncard := by
  rw [count_eq_ncard]
  exact Set.ncard_le_ncard (Set.sep_subset _ _) hS

/-- A nonempty subfamily has positive count at every large enough cutoff. -/
theorem eventually_count_pos {S : Set ι} (hS : S.Nonempty) :
    ∀ᶠ X in Filter.atTop, 0 < F.count S X := by
  obtain ⟨i, hi⟩ := hS
  filter_upwards [Filter.eventually_ge_atTop (F.height i)] with X hX
  have hfin : {j ∈ S | F.height j ≤ X}.Finite := (F.finite_height_le X).subset fun _ hj ↦ hj.2
  rw [count_eq_ncard, Set.ncard_pos hfin]
  exact ⟨i, hi, hX⟩

/-- Below a uniform lower bound for the height, every subfamily has count zero. -/
theorem count_eq_zero_of_lt {b X : ℝ} (hb : ∀ i, b ≤ F.height i) (hX : X < b)
    (S : Set ι) : F.count S X = 0 := by
  classical
  have : F.heightLE X = ∅ := Finset.eq_empty_of_forall_notMem fun i hi ↦
    (hX.not_ge ((hb i).trans ((mem_heightLE F).mp hi)))
  simp [count, this]

/-- An infinite subfamily has counts tending to infinity. -/
theorem tendsto_count_atTop {S : Set ι} (hS : S.Infinite) :
    Filter.Tendsto (F.count S) Filter.atTop Filter.atTop := by
  classical
  apply Filter.tendsto_atTop.2
  intro n
  obtain ⟨s, hs, hcard⟩ := hS.exists_subset_card_eq n
  filter_upwards [F.tendsto_heightLE_atTop.eventually (Filter.eventually_ge_atTop s)] with X hX
  rw [← hcard]
  exact Finset.card_le_card fun i hi ↦ Finset.mem_filter.mpr ⟨hX hi, hs hi⟩

/-- The strict count never exceeds the inclusive count at the same cutoff. -/
theorem countLT_le_count (S : Set ι) (X : ℝ) : F.countLT S X ≤ F.count S X := by
  classical
  exact Finset.card_le_card fun i hi ↦ Finset.mem_filter.mpr
    ⟨(Finset.mem_filter.mp hi).1, (Finset.mem_filter.mp hi).2.1⟩

/-- Inclusion of subfamilies gives an inequality of strict counts. -/
theorem countLT_mono_set {S T : Set ι} (h : S ⊆ T) (X : ℝ) :
    F.countLT S X ≤ F.countLT T X := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hiX, hiS, hi⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hiX, h hiS, hi⟩

/-- Strict counts are monotone in the cutoff. -/
theorem countLT_mono (S : Set ι) : Monotone (F.countLT S) := by
  classical
  intro X Y h
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hiX, hiS, hi⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨F.heightLE_mono h hiX, hiS, hi.trans_le h⟩

/-- Strict counts add on disjoint subfamilies. -/
theorem countLT_union_of_disjoint {S T : Set ι} (h : Disjoint S T) (X : ℝ) :
    F.countLT (S ∪ T) X = F.countLT S X + F.countLT T X := by
  classical
  simp only [countLT, Set.mem_union, or_and_right, Finset.filter_or]
  apply Finset.card_union_of_disjoint
  exact Finset.disjoint_left.mpr fun i hi hj ↦
    Set.disjoint_left.mp h (Finset.mem_filter.mp hi).2.1 (Finset.mem_filter.mp hj).2.1

/-- An inclusive count is bounded by a strict count at any larger cutoff. -/
theorem count_le_countLT_of_lt (S : Set ι) {X Y : ℝ} (h : X < Y) :
    F.count S X ≤ F.countLT S Y := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hiX, hiS⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr
    ⟨F.heightLE_mono h.le hiX, hiS, ((mem_heightLE F).mp hiX).trans_lt h⟩

/-- Descend an invariant height to a quotient, requiring finiteness on the quotient itself.
Finiteness of representatives is neither required nor implied. -/
def ofQuotient (s : Setoid ι) (h : ι → ℝ) (hinv : ∀ i j, s.r i j → h i = h j)
    (hfin : Northcott (Quotient.lift h hinv)) : ArithmeticFamily (Quotient s) where
  height := Quotient.lift h hinv
  northcott := hfin

/-- The descended height evaluates to the height of any representative. -/
@[simp]
theorem height_ofQuotient_mk (s : Setoid ι) (h : ι → ℝ)
    (hinv : ∀ i j, s.r i j → h i = h j) (hfin : Northcott (Quotient.lift h hinv))
    (i : ι) : (ofQuotient s h hinv hfin).height ⟦i⟧ = h i := (rfl)

/-- Pull back the height along a map with finite fibres. The new carrier counts each
representative separately. -/
def comap (f : κ → ι) [Filter.TendstoCofinite f] : ArithmeticFamily κ where
  height := F.height ∘ f
  northcott := Northcott.comp_of_finite_fibers f F.height

/-- The pullback height evaluates at the image of a representative. -/
@[simp]
theorem height_comap (f : κ → ι) [Filter.TendstoCofinite f] (k : κ) :
    (F.comap f).height k = F.height (f k) := (rfl)

/-- Pullback counts retain the cardinality of each fibre as its multiplicity. -/
theorem count_comap (f : κ → ι) [Filter.TendstoCofinite f] (S : Set ι) (X : ℝ) :
    (F.comap f).count (f ⁻¹' S) X =
      F.weightedCount (S.indicator (fun i ↦ Nat.card {k // f k = i})) X := by
  classical
  let s := ((F.comap f).heightLE X).filter (· ∈ f ⁻¹' S)
  let t := (F.heightLE X).filter (· ∈ S)
  have hmap : (s : Set κ).MapsTo f t := by
    intro k hk
    simpa [s, t] using hk
  calc
    (F.comap f).count (f ⁻¹' S) X = ∑ i ∈ t, (s.filter (f · = i)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ = ∑ i ∈ t, Nat.card {k // f k = i} := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Set.ncard_coe_finset, ← Set.ncard_ofPred]
      congr 1
      ext k
      have hi' : F.height i ≤ X ∧ i ∈ S := by simpa [t] using hi
      simp only [Finset.mem_coe, Finset.mem_filter, s, mem_heightLE, height_comap,
        Set.mem_preimage, Set.mem_ofPred_eq]
      grind
    _ = F.weightedCount (S.indicator (fun i ↦ Nat.card {k // f k = i})) X := by
      simp [t, weightedCount, Finset.sum_filter, Set.indicator_apply]

/-- Multiply a height by a positive constant. -/
def rescale (c : ℝ) (hc : 0 < c) : ArithmeticFamily ι where
  height i := c * F.height i
  northcott := ⟨fun X ↦ by
    simpa only [← le_div_iff₀' hc] using F.finite_height_le (X / c)⟩

/-- A rescaled height evaluates by multiplying the original height. -/
@[simp]
theorem height_rescale (c : ℝ) (hc : 0 < c) (i : ι) :
    (F.rescale c hc).height i = c * F.height i := (rfl)

/-- Rescaling the height divides the inclusive cutoff by the same constant. -/
theorem heightLE_rescale (c : ℝ) (hc : 0 < c) (X : ℝ) :
    (F.rescale c hc).heightLE X = F.heightLE (X / c) := by
  ext
  simp [← le_div_iff₀' hc]

/-- The count for a rescaled height is the original count at the divided cutoff. -/
theorem count_rescale (c : ℝ) (hc : 0 < c) (S : Set ι) (X : ℝ) :
    (F.rescale c hc).count S X = F.count S (X / c) := by
  simp [count, heightLE_rescale]

/-- A natural-valued Northcott height, viewed as a real-valued family height. -/
def ofNat (N : ι → ℕ) [Northcott N] : ArithmeticFamily ι where
  height i := N i
  northcott := ⟨finite_setOf_natCast_le N⟩

/-- The natural-height adapter evaluates by casting to the reals. -/
@[simp]
theorem height_ofNat (N : ι → ℕ) [Northcott N] (i : ι) :
    (ofNat N).height i = (N i : ℝ) := (rfl)

/-- The natural-height adapter has exactly the existing inclusive carrier. -/
theorem heightLE_ofNat (N : ι → ℕ) [Northcott N] (X : ℝ) :
    (ofNat N).heightLE X = normLE N X := by
  ext
  simp

/-- Natural-height weighted counts agree with the existing summatory function. -/
theorem weightedCount_ofNat (N : ι → ℕ) [Northcott N] {M : Type*} [AddCommMonoid M]
    (w : ι → M) (X : ℝ) : (ofNat N).weightedCount w X = summatory N w X := by
  simp [weightedCount, heightLE_ofNat, summatory_apply]

/-- The elements of a number field, ordered by multiplicative Weil height. -/
noncomputable def ofMulHeight (K : Type*) [Field K] [NumberField K] : ArithmeticFamily K where
  height := Height.mulHeight₁
  northcott := inferInstance

/-- The number-field family uses multiplicative Weil height. -/
@[simp]
theorem height_ofMulHeight (K : Type*) [Field K] [NumberField K] (x : K) :
    (ofMulHeight K).height x = Height.mulHeight₁ x := (rfl)

end ArithmeticFamily

end TauCeti
