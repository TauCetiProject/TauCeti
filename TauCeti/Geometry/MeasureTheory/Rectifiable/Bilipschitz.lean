/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
public import TauCeti.Analysis.Calculus.FDeriv.Bilipschitz
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import TauCeti.Analysis.InnerProductSpace.NormDet

/-!
# Bi-Lipschitz parametrizations of rectifiable sets

In finite-dimensional real inner product spaces, countable rectifiability is equivalent to
coverage, up to normalized Hausdorff measure zero, by countably many bi-Lipschitz patches
with Borel domains. No measurability or local finiteness of the rectifiable set is assumed.
The patches may extend beyond the set, as in `CountablyRectifiable` itself.

Bi-Lipschitz patches have Lipschitz inverse coordinates, allowing measure and density estimates
to be transferred between a rectifiable set and its parameter domains. A Lipschitz map is
decomposed on its regular points using
`TauCeti.exists_partition_bilipschitz_of_hasFDerivWithinAt`. The discarded image is null by
`LipschitzWith.euclideanHausdorffMeasure_image_compl_setOf_regular`, which combines Rademacher's
theorem and the zero-Jacobian image theorem.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (rectifiable sets).
* H. Federer, *Geometric Measure Theory*, §3.2 (decomposition of parametrizations).
-/

public section

open Set MeasureTheory
open scoped ENNReal NNReal Function

namespace TauCeti

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The image of a Lipschitz map is covered up to a null set by images of countably many
disjoint Borel sets on which the map has a Lipschitz inverse. The forward Lipschitz bound
is inherited from the original map. -/
theorem exists_bilipschitz_cover_of_lipschitzWith {f : E → V} {K : ℝ≥0}
    (hf : LipschitzWith K f) :
    ∃ A : ℕ → Set E, (∀ n, MeasurableSet (A n)) ∧ Pairwise (Disjoint on A) ∧
      (∀ n, ∃ L : ℝ≥0, AntilipschitzWith L ((A n).domRestrict f)) ∧
      μHE[Module.finrank ℝ E] (range f \ ⋃ n, f '' A n) = 0 := by
  let G := {x | DifferentiableAt ℝ f x ∧ (fderiv ℝ f x).normDet ≠ 0}
  have hG : MeasurableSet G := (measurableSet_of_differentiableAt ℝ f).inter
    (measurableSet_eq_fun (ContinuousLinearMap.continuous_normDet.measurable.comp
      (measurable_fderiv ℝ f)) measurable_const).compl
  have hi (x : E) (hx : x ∈ G) : Function.Injective (fderiv ℝ f x) := by
    exact LinearMap.ker_eq_bot.mp
      (not_not.mp (mt LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hx.2))
  obtain ⟨t, ht, htm, hcover, hbi⟩ :=
    exists_partition_bilipschitz_of_hasFDerivWithinAt
      (fun x (hx : x ∈ G) ↦ hx.1.hasFDerivAt.hasFDerivWithinAt) hi
  choose K' L' hLip hAnti using hbi
  refine ⟨fun n ↦ G ∩ t n, fun n ↦ hG.inter (htm n),
    fun i j hij ↦ (ht hij).mono inter_subset_right inter_subset_right,
    fun n ↦ ⟨L' n, hAnti n⟩, ?_⟩
  refine measure_mono_null ?_ hf.euclideanHausdorffMeasure_image_compl_setOf_regular
  rintro y ⟨⟨x, rfl⟩, hy⟩
  refine ⟨x, ?_, rfl⟩
  intro hx
  obtain ⟨n, hn⟩ := mem_iUnion.mp (hcover hx)
  exact hy (mem_iUnion.mpr ⟨n, x, ⟨hx, hn⟩, rfl⟩)

/-- A countably rectifiable set in a Euclidean space admits countably many bi-Lipschitz
patches with Borel domains, covering it up to normalized Hausdorff measure zero. Neither
measurability nor local finiteness of the set is needed. -/
theorem CountablyRectifiable.exists_bilipschitz_cover {k : ℕ} {s : Set V}
    (hs : CountablyRectifiable k s) :
    ∃ (A : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ∀ n, A n → V),
      (∀ n, MeasurableSet (A n)) ∧
      (∀ n, ∃ K L : ℝ≥0, LipschitzWith K (f n) ∧ AntilipschitzWith L (f n)) ∧
      μHE[k] (s \ ⋃ n, range (f n)) = 0 := by
  classical
  obtain ⟨B, g, hg, hnull⟩ := countablyRectifiable_iff.mp hs
  choose K hK using hg
  -- Extend subtype-valued patches to the whole parameter space before applying Rademacher.
  let g' (n : ℕ) : EuclideanSpace ℝ (Fin k) → V :=
    Function.extend Subtype.val (g n) (fun _ ↦ 0)
  have hg' (n : ℕ) (x : B n) : g' n x = g n x :=
    Subtype.val_injective.extend_apply _ _ x
  have hlip (n : ℕ) : LipschitzOnWith (K n) (g' n) (B n) := by
    intro x hx y hy
    simpa only [hg' n ⟨x, hx⟩, hg' n ⟨y, hy⟩, Subtype.edist_eq] using
      hK n ⟨x, hx⟩ ⟨y, hy⟩
  choose F hF hFeq using fun n ↦ (hlip n).extend_finite_dimension
  have hFg (n : ℕ) (x : B n) : F n x = g n x := (hFeq n x.property).symm.trans (hg' n x)
  have hex (n : ℕ) : ∃ A : ℕ → Set (EuclideanSpace ℝ (Fin k)),
      (∀ j, MeasurableSet (A j)) ∧
      (∀ j, ∃ L : ℝ≥0, AntilipschitzWith L ((A j).domRestrict (F n))) ∧
      μHE[k] (range (F n) \ ⋃ j, F n '' A j) = 0 := by
    obtain ⟨A, hAm, -, hAnti, hnull⟩ :=
      exists_bilipschitz_cover_of_lipschitzWith (hF n)
    exact ⟨A, hAm, hAnti, by simpa only [finrank_euclideanSpace_fin] using hnull⟩
  choose A hAm hAanti hAnull using hex
  let f (p : ℕ × ℕ) : A p.1 p.2 → V := (A p.1 p.2).domRestrict (F p.1)
  have hcover (n : ℕ) : range (g n) ≤ᵐ[μHE[k]] ⋃ j, range (f (n, j)) := by
    have hn : range (F n) ≤ᵐ[μHE[k]] ⋃ j, range (f (n, j)) := by
      simpa only [range_domRestrict, f] using
        ae_le_set.mpr (hAnull n)
    exact (show range (g n) ⊆ range (F n) from by
      rintro _ ⟨x, rfl⟩; exact ⟨x, hFg n x⟩).eventuallyLE.trans hn
  refine ⟨fun n ↦ A (Nat.unpair n).1 (Nat.unpair n).2,
    fun n ↦ f (Nat.unpair n), fun n ↦ hAm _ _, fun n ↦ ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hAanti (Nat.unpair n).1 (Nat.unpair n).2
    exact ⟨_, L, (hF (Nat.unpair n).1).restrict _, hL⟩
  · apply ae_le_set.mp
    rw [Set.iUnion_unpair (fun n j ↦ range (f (n, j)))]
    exact (ae_le_set.mpr hnull).trans
      (Filter.EventuallySubset.countable_iUnion hcover)

/-- Countable rectifiability in a finite-dimensional Euclidean target is equivalent to
coverage up to a null set by bi-Lipschitz patches with Borel domains. -/
theorem countablyRectifiable_iff_bilipschitz {k : ℕ} {s : Set V} :
    CountablyRectifiable k s ↔
      ∃ (A : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ∀ n, A n → V),
        (∀ n, MeasurableSet (A n)) ∧
        (∀ n, ∃ K L : ℝ≥0, LipschitzWith K (f n) ∧ AntilipschitzWith L (f n)) ∧
        μHE[k] (s \ ⋃ n, range (f n)) = 0 := by
  refine ⟨fun hs ↦ hs.exists_bilipschitz_cover, ?_⟩
  rintro ⟨A, f, -, hf, hnull⟩
  choose K L hLip hAnti using hf
  exact countablyRectifiable_iff.mpr
    ⟨A, f, fun n ↦ ⟨K n, hLip n⟩, hnull⟩

end TauCeti
