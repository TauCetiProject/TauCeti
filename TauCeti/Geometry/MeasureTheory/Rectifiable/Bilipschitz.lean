/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz

/-!
# Bi-Lipschitz parametrizations of rectifiable sets

In finite-dimensional real inner product spaces, countable rectifiability is equivalent to
coverage, up to normalized Hausdorff measure zero, by countably many bi-Lipschitz patches
with Borel domains. No measurability or local finiteness of the rectifiable set is assumed.
The patches may extend beyond the set, as in `CountablyRectifiable` itself.

Equivalently, the patches may be taken to be Lipschitz maps defined on all of
`EuclideanSpace ℝ (Fin k)` (`TauCeti.CountablyRectifiable.exists_lipschitzWith_cover`).
Bi-Lipschitz patches have Lipschitz inverse coordinates, allowing measure and density estimates
to be transferred between a rectifiable set and its parameter domains. A Lipschitz map is
decomposed on its regular points using
`TauCeti.exists_partition_lipschitz_antilipschitz_of_hasFDerivWithinAt`.
The discarded image is null by
`LipschitzWith.euclideanHausdorffMeasure_image_compl_setOf_regular`, which combines Rademacher's
theorem and the zero-Jacobian image theorem.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §11 (rectifiable sets).
* H. Federer, *Geometric Measure Theory*, §3.2 (decomposition of parametrizations).
-/

public section

open Set MeasureTheory
open scoped ENNReal NNReal Function

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

namespace TauCeti

/-- A countably `k`-rectifiable subset of a finite-dimensional inner product space is covered, up
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

/-- A countably rectifiable set in a Euclidean space admits countably many bi-Lipschitz
patches with Borel domains, covering it up to normalized Hausdorff measure zero. Neither
measurability nor local finiteness of the set is needed. -/
theorem CountablyRectifiable.exists_bilipschitz_cover {k : ℕ} {s : Set V}
    (hs : CountablyRectifiable k s) :
    ∃ (A : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ∀ n, A n → V),
      (∀ n, MeasurableSet (A n)) ∧
      (∀ n, ∃ K L : ℝ≥0, LipschitzWith K (f n) ∧ AntilipschitzWith L (f n)) ∧
      μHE[k] (s \ ⋃ n, range (f n)) = 0 := by
  obtain ⟨F, hF, hnull⟩ := hs.exists_lipschitzWith_cover
  choose K hK using hF
  have hex (n : ℕ) : ∃ A : ℕ → Set (EuclideanSpace ℝ (Fin k)),
      (∀ j, MeasurableSet (A j)) ∧
      (∀ j, ∃ L : ℝ≥0, AntilipschitzWith L ((A j).domRestrict (F n))) ∧
      μHE[k] (range (F n) \ ⋃ j, F n '' A j) = 0 := by
    obtain ⟨A, hAm, -, hAnti, hnull⟩ := (hK n).exists_bilipschitz_cover
    exact ⟨A, hAm, hAnti, by simpa only [finrank_euclideanSpace_fin] using hnull⟩
  choose A hAm hAanti hAnull using hex
  let f (p : ℕ × ℕ) : A p.1 p.2 → V := (A p.1 p.2).domRestrict (F p.1)
  have hcover (n : ℕ) : range (F n) ≤ᵐ[μHE[k]] ⋃ j, range (f (n, j)) := by
    simpa only [range_domRestrict, f] using ae_le_set.mpr (hAnull n)
  refine ⟨fun n ↦ A (Nat.unpair n).1 (Nat.unpair n).2,
    fun n ↦ f (Nat.unpair n), fun n ↦ hAm _ _, fun n ↦ ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hAanti (Nat.unpair n).1 (Nat.unpair n).2
    exact ⟨_, L, (hK (Nat.unpair n).1).restrict _, hL⟩
  · apply ae_le_set.mp
    rw [Set.iUnion_unpair (fun n j ↦ range (f (n, j)))]
    exact (ae_le_set.mpr hnull).trans
      (Filter.EventuallySubset.countable_iUnion hcover)

/-- Countable rectifiability in a finite-dimensional Euclidean target is equivalent to
coverage up to a null set by bi-Lipschitz patches with Borel domains. -/
theorem countablyRectifiable_iff_exists_bilipschitz_cover {k : ℕ} {s : Set V} :
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
