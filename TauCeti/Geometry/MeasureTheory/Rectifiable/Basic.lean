/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Measure.Haar.Lipschitz
public import Mathlib.Data.Nat.Pairing
import Mathlib.Analysis.Normed.Module.FiniteDimension
import TauCeti.Geometry.Euclidean.Volume.Measure

/-!
# Countably rectifiable sets

A countably `k`-rectifiable set is covered, up to a null set for normalized Euclidean
Hausdorff measure `μHE[k]`, by countably many Lipschitz images of subsets of
`EuclideanSpace ℝ (Fin k)`. The domains need not be measurable, and neither measurability
nor local finiteness of Hausdorff measure is part of rectifiability.

We prove closure under subsets, countable unions and null modifications, upward monotonicity
in the dimension `k`, countable sets in every dimension, pushforward by maps Lipschitz on the
set, and pullback by maps antilipschitz on the set. These operations allow rectifiable sets to be
localized and their parametrizations to be composed without imposing regularity on the exceptional
set. Patches are maps from subtypes, so even an empty target requires no arbitrary base point.
In a finite-dimensional real normed space, the patches extend to Lipschitz maps defined
on all of `EuclideanSpace ℝ (Fin k)` (`TauCeti.CountablyRectifiable.exists_lipschitzWith_cover`).

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
  exact ⟨A, f, hf, ae_subset.mp (ht.trans (ae_subset.mpr hcover))⟩

/-- Arbitrary subsets of rectifiable sets are rectifiable; in particular this allows
restriction to measurable sets without an additional measurability assumption. -/
theorem mono (hs : CountablyRectifiable k s) (ht : t ⊆ s) : CountablyRectifiable k t :=
  hs.mono_ae ht.eventuallySubset

/-- Countable rectifiability is independent of the representative modulo `μHE[k]`. -/
theorem congr (hs : CountablyRectifiable k s) (hst : s =ᵐ[μHE[k]] t) :
    CountablyRectifiable k t :=
  hs.mono_ae hst.symm.subset

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
  apply ae_subset.mp
  have hc : ∀ n, s n ≤ᵐ[μHE[k]] ⋃ i, Set.range (f n i) :=
    fun n ↦ ae_subset.mpr (hcover n)
  rw [Set.iUnion_unpair (fun n i ↦ Set.range (f n i))]
  exact Filter.EventuallySubset.countable_iUnion hc

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
    have hpi : LipschitzWith 1 (p i) :=
      (LipschitzWith.subtypeVal (B i)).subtype_mk (fun x ↦ x.property.choose)
    simpa only [mul_one, Function.comp_def, Set.domRestrict_apply, F] using
      hg.to_restrict.comp (((hL i).comp hpi).subtype_mk (hp i))
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

/-- A set whose image under a map antilipschitz on it is countably rectifiable is itself countably
rectifiable. -/
theorem of_antilipschitzWith {f : X → Y} {K : ℝ≥0} (hs : CountablyRectifiable k (f '' s))
    (hf : AntilipschitzWith K (s.domRestrict f)) : CountablyRectifiable k s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, _⟩
  · exact empty
  have : Nonempty X := ⟨x₀⟩
  have hmaps : MapsTo (Function.invFunOn f s) (f '' s) s := fun _ hy ↦ Function.invFunOn_mem hy
  have hinv : RightInvOn (Function.invFunOn f s) f (f '' s) := fun _ hy ↦ Function.invFunOn_eq hy
  have hlip : LipschitzOnWith K (Function.invFunOn f s) (f '' s) :=
    lipschitzOnWith_iff_restrict.2 (hf.to_rightInvOn' hmaps hinv)
  have hinj : InjOn f s := Set.injOn_iff_injective.2 hf.injective
  simpa only [hinj.invFunOn_image Subset.rfl] using hs.image hlip

/-- Isometric embeddings preserve and reflect countable rectifiability, without requiring
surjectivity or a nonempty source. -/
theorem isometry_image_iff {f : X → Y} (hf : Isometry f) :
    CountablyRectifiable k (f '' s) ↔ CountablyRectifiable k s :=
  ⟨fun hs ↦ hs.of_antilipschitzWith (hf.antilipschitzWith.domRestrict s),
    fun hs ↦ hs.image hf.lipschitzWith.lipschitzOnWith⟩

/-- Isometric equivalences preserve countable rectifiability in both directions. -/
@[simp]
theorem isometryEquiv_image_iff {e : X ≃ᵢ Y} :
    CountablyRectifiable k (e '' s) ↔ CountablyRectifiable k s :=
  isometry_image_iff e.isometry

/-- Every singleton is countably `k`-rectifiable. -/
@[simp]
theorem singleton (x : X) : CountablyRectifiable k ({x} : Set X) := by
  simpa only [range_const] using
    of_lipschitzWith (A := univ) (f := fun _ ↦ x) (K := 0) (LipschitzWith.const' x)

/-- Countable rectifiability is monotone in the dimension: every countably `m`-rectifiable set is
countably `k`-rectifiable for every `k ≥ m`. -/
theorem mono_dim {m : ℕ} (hs : CountablyRectifiable m s) (hmk : m ≤ k) :
    CountablyRectifiable k s := by
  classical
  obtain ⟨A, f, hf, hcover⟩ := hs
  choose K hK using hf
  let ι := LinearIsometry.piLpExtendByZero 2 ℝ ℝ (Fin.castLEEmb hmk)
  let e (i : ℕ) := (ι.isometry.comp (isometry_subtypeVal (s := A i))).isometryEquivOnRange
  let B (i : ℕ) : Set (EuclideanSpace ℝ (Fin k)) := range fun x : A i ↦ ι x
  let g (i : ℕ) : B i → X := f i ∘ (e i).symm
  refine ⟨B, g, fun i ↦ ⟨K i, ?_⟩, ?_⟩
  · simpa only [mul_one] using (hK i).comp (e i).symm.isometry.lipschitzWith
  · have hrange (i : ℕ) : range (g i) = range (f i) := (e i).symm.surjective.range_comp (f i)
    simp_rw [hrange]
    rw [Measure.euclideanHausdorffMeasure_eq_zero_iff] at hcover ⊢
    exact nonpos_iff_eq_zero.1
      ((Measure.hausdorffMeasure_mono (Nat.cast_le.2 hmk) _).trans hcover.le)

end CountablyRectifiable

/-- Countable rectifiability is invariant under equality almost everywhere for normalized
Hausdorff measure, without a measurability assumption on either representative. -/
theorem countablyRectifiable_congr (hst : s =ᵐ[μHE[k]] t) :
    CountablyRectifiable k s ↔ CountablyRectifiable k t :=
  ⟨fun hs ↦ hs.congr hst, fun ht ↦ ht.congr hst.symm⟩

section FiniteDimensional

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- A countably `k`-rectifiable subset of a finite-dimensional real normed space is covered, up
to a `μHE[k]`-null set, by the ranges of countably many Lipschitz maps defined on all of
`EuclideanSpace ℝ (Fin k)`. -/
theorem CountablyRectifiable.exists_lipschitzWith_cover {k : ℕ} {s : Set V}
    (hs : CountablyRectifiable k s) :
    ∃ F : ℕ → EuclideanSpace ℝ (Fin k) → V, (∀ n, ∃ K : ℝ≥0, LipschitzWith K (F n)) ∧
      μHE[k] (s \ ⋃ n, range (F n)) = 0 := by
  classical
  obtain ⟨A, f, hf, hnull⟩ := countablyRectifiable_iff.mp hs
  choose K hK using hf
  have hext (n : ℕ) : ∃ F : EuclideanSpace ℝ (Fin k) → V,
      (∃ K' : ℝ≥0, LipschitzWith K' F) ∧ ∀ x : A n, F x = f n x := by
    -- Extend subtype-valued patches to the whole parameter space.
    let g : EuclideanSpace ℝ (Fin k) → V := Function.extend Subtype.val (f n) (fun _ ↦ 0)
    have hg (x : A n) : g x = f n x := Subtype.val_injective.extend_apply _ _ x
    have hlip : LipschitzOnWith (K n) g (A n) := fun x hx y hy ↦ by
      simpa only [hg ⟨x, hx⟩, hg ⟨y, hy⟩, Subtype.edist_eq] using hK n ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨F, hF, hFeq⟩ := hlip.extend_finite_dimension
    exact ⟨F, ⟨_, hF⟩, fun x ↦ (hFeq x.property).symm.trans (hg x)⟩
  choose F hF hFf using hext
  refine ⟨F, hF, measure_mono_null (sdiff_subset_sdiff_right (iUnion_mono fun n ↦ ?_)) hnull⟩
  rintro _ ⟨x, rfl⟩
  exact ⟨x, hFf n x⟩

end FiniteDimensional

end TauCeti

/-- Every countable set in an extended metric Borel space is countably `k`-rectifiable in every
dimension `k`. -/
protected theorem Set.Countable.countablyRectifiable {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X] {k : ℕ} {s : Set X} (hs : s.Countable) :
    TauCeti.CountablyRectifiable k s := by
  have := hs.to_subtype
  have h : s = ⋃ x : s, ({(x : X)} : Set X) := by ext; simp
  rw [h]
  exact TauCeti.CountablyRectifiable.iUnion fun x : s ↦ .singleton (x : X)
