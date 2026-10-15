/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
public import Mathlib.Data.Nat.Pairing

/-!
# Countably rectifiable sets

A countably `k`-rectifiable set is covered, up to a null set for normalized Euclidean
Hausdorff measure `μHE[k]`, by countably many Lipschitz images of subsets of
`EuclideanSpace ℝ (Fin k)`. The domains need not be measurable, and neither measurability
nor local finiteness of Hausdorff measure is part of rectifiability.

We prove closure under subsets, countable unions and null modifications, and transport
by maps Lipschitz on the set. These operations allow rectifiable sets to be localized
and their parametrizations to be composed without imposing regularity on the exceptional set.
Patches are maps from subtypes, so even an empty target requires no arbitrary base point.

The image estimates use `LipschitzOnWith.euclideanHausdorffMeasure_image_le`, which
explicitly compares the normalized measure with Mathlib's raw Hausdorff measure.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (countably rectifiable sets).
-/

public section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace TauCeti

variable {X Y : Type*} [EMetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [EMetricSpace Y] [MeasurableSpace Y] [BorelSpace Y] {k : ℕ} {s t : Set X}

/-- A set is countably `k`-rectifiable if countably many Lipschitz patches cover it up to
`μHE[k]`-measure zero. No measurability or measure finiteness is required. -/
def CountablyRectifiable (k : ℕ) (s : Set X) : Prop :=
  ∃ (A : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ∀ i, A i → X),
    (∀ i, ∃ K : ℝ≥0, LipschitzWith K (f i)) ∧
      μHE[k] (s \ ⋃ i, range (f i)) = 0

/-- The Lipschitz-patch characterization of countable rectifiability. -/
theorem countablyRectifiable_iff : CountablyRectifiable k s ↔
    ∃ (A : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ∀ i, A i → X),
      (∀ i, ∃ K : ℝ≥0, LipschitzWith K (f i)) ∧
        μHE[k] (s \ ⋃ i, range (f i)) = 0 := Iff.rfl

namespace CountablyRectifiable

/-- Every `μHE[k]`-null set is countably `k`-rectifiable. -/
theorem of_null (hs : μHE[k] s = 0) : CountablyRectifiable k s := by
  refine ⟨fun _ ↦ ∅, fun _ x ↦ False.elim x.property, ?_, ?_⟩
  · exact fun _ ↦ ⟨0, fun x ↦ False.elim x.property⟩
  · simpa only [Set.range_eq_empty, iUnion_empty, sdiff_empty] using hs

@[simp]
theorem empty : CountablyRectifiable k (∅ : Set X) := of_null measure_empty

/-- An almost everywhere subset of a rectifiable set is rectifiable. -/
theorem mono_ae (hs : CountablyRectifiable k s) (ht : t ≤ᵐ[μHE[k]] s) :
    CountablyRectifiable k t := by
  obtain ⟨A, f, hf, hcover⟩ := hs
  exact ⟨A, f, hf, ae_le_set.mp (ht.trans (ae_le_set.mpr hcover))⟩

/-- Arbitrary subsets of rectifiable sets are rectifiable; in particular this allows
restriction to measurable sets without an additional measurability assumption. -/
theorem mono (hs : CountablyRectifiable k s) (ht : t ⊆ s) : CountablyRectifiable k t :=
  hs.mono_ae ht.eventuallyLE

/-- Countable rectifiability is independent of the representative modulo `μHE[k]`. -/
theorem congr (hs : CountablyRectifiable k s) (hst : s =ᵐ[μHE[k]] t) :
    CountablyRectifiable k t :=
  hs.mono_ae hst.symm.le

/-- A single Lipschitz patch is countably rectifiable. -/
theorem of_lipschitzWith {A : Set (EuclideanSpace ℝ (Fin k))} {f : A → X} {K : ℝ≥0}
    (hf : LipschitzWith K f) : CountablyRectifiable k (Set.range f) :=
  ⟨fun _ ↦ A, fun _ ↦ f, fun _ ↦ ⟨K, hf⟩,
    by simp only [iUnion_const, sdiff_self, measure_empty]⟩

/-- A Lipschitz image of a subset of `k`-dimensional Euclidean space is countably
`k`-rectifiable. -/
theorem of_lipschitzOnWith {A : Set (EuclideanSpace ℝ (Fin k))}
    {f : EuclideanSpace ℝ (Fin k) → X} {K : ℝ≥0} (hf : LipschitzOnWith K f A) :
    CountablyRectifiable k (f '' A) := by
  simpa only [Set.range_domRestrict] using of_lipschitzWith hf.to_restrict

/-- Every subset of `k`-dimensional Euclidean space is countably `k`-rectifiable. -/
theorem euclidean (A : Set (EuclideanSpace ℝ (Fin k))) : CountablyRectifiable k A := by
  simpa only [image_id] using
    of_lipschitzOnWith (f := id) (K := 1) (LipschitzWith.id.lipschitzOnWith)

private theorem iUnion_nat {s : ℕ → Set X} (hs : ∀ n, CountablyRectifiable k (s n)) :
    CountablyRectifiable k (⋃ n, s n) := by
  classical
  choose A f hf hcover using hs
  refine ⟨fun n ↦ A (Nat.unpair n).1 (Nat.unpair n).2,
    fun n ↦ f (Nat.unpair n).1 (Nat.unpair n).2,
    fun n ↦ hf (Nat.unpair n).1 (Nat.unpair n).2, ?_⟩
  apply ae_le_set.mp
  have hc : ∀ n, s n ≤ᵐ[μHE[k]] ⋃ i, Set.range (f n i) :=
    fun n ↦ ae_le_set.mpr (hcover n)
  filter_upwards [ae_all_iff.mpr hc] with x hx
  intro hxs
  obtain ⟨n, hn⟩ := mem_iUnion.mp hxs
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hx n hn)
  refine mem_iUnion.mpr ⟨Nat.pair n i, ?_⟩
  rw [Nat.unpair_pair]
  exact hi

/-- A countable collection of rectifiable sets has rectifiable union. -/
theorem sUnion {S : Set (Set X)} (hS : S.Countable)
    (hs : ∀ s ∈ S, CountablyRectifiable k s) : CountablyRectifiable k (⋃₀ S) := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  obtain ⟨s, rfl⟩ := hS.exists_eq_range hne
  simpa only [sUnion_range] using iUnion_nat (fun n ↦ hs (s n) (mem_range_self n))

/-- Unions indexed by any countable type preserve rectifiability, including an empty index. -/
theorem iUnion {ι : Type*} [Countable ι] {s : ι → Set X}
    (hs : ∀ i, CountablyRectifiable k (s i)) : CountablyRectifiable k (⋃ i, s i) := by
  simpa only [sUnion_range] using
    sUnion (countable_range s) (by rintro _ ⟨i, rfl⟩; exact hs i)

/-- Binary unions of rectifiable sets are rectifiable. -/
theorem union (hs : CountablyRectifiable k s) (ht : CountablyRectifiable k t) :
    CountablyRectifiable k (s ∪ t) := by
  simpa only [sUnion_pair] using
    sUnion (to_countable {s, t}) (by simp only [mem_insert_iff, mem_singleton_iff]; aesop)

/-- A map Lipschitz on a rectifiable set has rectifiable image. No measurability of the
set or its patch domains is needed. -/
theorem image (hs : CountablyRectifiable k s) {g : X → Y} {K : ℝ≥0}
    (hg : LipschitzOnWith K g s) : CountablyRectifiable k (g '' s) := by
  classical
  obtain ⟨A, f, hf, hcover⟩ := hs
  choose L hL using hf
  let B (i : ℕ) : Set (EuclideanSpace ℝ (Fin k)) :=
    {x | ∃ hx : x ∈ A i, f i ⟨x, hx⟩ ∈ s}
  let p (i : ℕ) (x : B i) : A i := ⟨x, x.property.choose⟩
  have hp (i : ℕ) (x : B i) : f i (p i x) ∈ s := x.property.choose_spec
  let F (i : ℕ) : B i → Y := fun x ↦ g (f i (p i x))
  have hF (i : ℕ) : LipschitzWith (K * L i) (F i) := by
    intro x y
    calc
      edist (F i x) (F i y) ≤ K * edist (f i (p i x)) (f i (p i y)) := hg (hp i x) (hp i y)
      _ ≤ K * (L i * edist (p i x) (p i y)) := mul_le_mul_right (hL i _ _) _
      _ = (K * L i : ℝ≥0) * edist x y := by
        simp only [p, Subtype.edist_eq, ENNReal.coe_mul, mul_assoc]
  refine ⟨B, F, fun i ↦ ⟨K * L i, hF i⟩, ?_⟩
  have hnull : μHE[k] (g '' (s \ ⋃ i, Set.range (f i))) = 0 := by
    have h := LipschitzOnWith.euclideanHausdorffMeasure_image_le
      (hg.mono (sdiff_subset (t := ⋃ i, Set.range (f i)))) k
    simpa only [hcover, mul_zero, nonpos_iff_eq_zero] using h
  apply measure_mono_null (t := g '' (s \ ⋃ i, Set.range (f i))) ?_ hnull
  rintro y ⟨⟨x, hxs, rfl⟩, hy⟩
  refine ⟨x, ⟨hxs, ?_⟩, rfl⟩
  intro hx
  obtain ⟨i, z, rfl⟩ := mem_iUnion.mp hx
  exact hy (mem_iUnion.mpr ⟨i, ⟨⟨z, ⟨z.property, hxs⟩⟩, rfl⟩⟩)

/-- Isometric embeddings preserve and reflect countable rectifiability, without requiring
surjectivity or a nonempty source. -/
theorem isometry_image_iff {f : X → Y} (hf : Isometry f) :
    CountablyRectifiable k (f '' s) ↔ CountablyRectifiable k s := by
  classical
  constructor
  · intro hs
    rcases isEmpty_or_nonempty X with hX | hX
    · simpa only [eq_empty_of_isEmpty s] using (empty (X := X) (k := k))
    have hinv : RightInvOn (Function.invFun f) f (f '' s) :=
      fun _ hy ↦ Function.invFun_eq (image_subset_range f s hy)
    have hLip : LipschitzOnWith 1 (Function.invFun f) (f '' s) :=
      lipschitzOnWith_iff_restrict.mpr (hf.antilipschitzWith.to_rightInvOn hinv)
    simpa only [← image_comp, Function.invFun_comp hf.injective, image_id] using hs.image hLip
  · exact fun hs ↦ hs.image hf.lipschitzWith.lipschitzOnWith

/-- Isometric equivalences preserve countable rectifiability in both directions. -/
@[simp]
theorem isometryEquiv_image_iff (e : X ≃ᵢ Y) :
    CountablyRectifiable k (e '' s) ↔ CountablyRectifiable k s :=
  isometry_image_iff e.isometry

end CountablyRectifiable

/-- Countable rectifiability is invariant under equality almost everywhere for normalized
Hausdorff measure, without a measurability assumption on either representative. -/
theorem countablyRectifiable_congr (hst : s =ᵐ[μHE[k]] t) :
    CountablyRectifiable k s ↔ CountablyRectifiable k t :=
  ⟨fun hs ↦ hs.congr hst, fun ht ↦ ht.congr hst.symm⟩

end TauCeti
