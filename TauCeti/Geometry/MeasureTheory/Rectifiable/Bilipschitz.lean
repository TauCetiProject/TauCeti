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

The construction starts from a cover by countably many Lipschitz maps defined on all of
`EuclideanSpace ℝ (Fin k)` (`TauCeti.CountablyRectifiable.exists_lipschitzWith_cover`).
Bi-Lipschitz patches have Lipschitz inverse coordinates, allowing measure and density estimates
to be transferred between a rectifiable set and its parameter domains. A Lipschitz map is
decomposed on its regular points using `LipschitzWith.exists_bilipschitz_cover`.
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

/-- A countably rectifiable set in a Euclidean space admits countably many bi-Lipschitz
patches with Borel domains, covering it up to normalized Hausdorff measure zero. The
parametrizations are Lipschitz on the whole parameter space and inverse-Lipschitz on each
domain. Neither measurability nor local finiteness of the set is needed. -/
theorem CountablyRectifiable.exists_bilipschitz_cover {k : ℕ} {s : Set V}
    (hs : CountablyRectifiable k s) :
    ∃ (A : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ℕ → EuclideanSpace ℝ (Fin k) → V),
      (∀ n, MeasurableSet (A n)) ∧
      (∀ n, ∃ K L : ℝ≥0,
        LipschitzWith K (f n) ∧ AntilipschitzWith L ((A n).domRestrict (f n))) ∧
      μHE[k] (s \ ⋃ n, f n '' A n) = 0 := by
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
    obtain ⟨A, hAm, -, hAnti, hnull⟩ := (hF n).exists_bilipschitz_cover
    exact ⟨A, hAm, hAnti, by simpa only [finrank_euclideanSpace_fin] using hnull⟩
  choose A hAm hAanti hAnull using hex
  let f (p : ℕ × ℕ) : A p.1 p.2 → V := (A p.1 p.2).domRestrict (F p.1)
  have hcover (n : ℕ) : range (F n) ≤ᵐ[μHE[k]] ⋃ j, range (f (n, j)) := by
    simpa only [range_domRestrict, f] using ae_le_set.mpr (hAnull n)
  refine ⟨fun n ↦ A (Nat.unpair n).1 (Nat.unpair n).2,
    fun n ↦ F (Nat.unpair n).1, fun n ↦ hAm _ _, fun n ↦ ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hAanti (Nat.unpair n).1 (Nat.unpair n).2
    exact ⟨_, L, hF (Nat.unpair n).1, hL⟩
  · apply ae_le_set.mp
    rw [Set.iUnion_unpair (fun n j ↦ F n '' A n j)]
    simp_rw [← range_domRestrict]
    exact (ae_le_set.mpr hnull).trans
      ((Filter.EventuallySubset.countable_iUnion fun n ↦
        Filter.Eventually.of_forall (fun _ hx ↦ by
          rcases hx with ⟨x, rfl⟩
          exact ⟨x, hFg n x⟩)).trans
        (Filter.EventuallySubset.countable_iUnion hcover))

/-- Countable rectifiability in a finite-dimensional Euclidean target is equivalent to
coverage up to a null set by bi-Lipschitz patches with Borel domains and parametrizations
that are Lipschitz on the whole parameter space. -/
theorem countablyRectifiable_iff_exists_bilipschitz_cover {k : ℕ} {s : Set V} :
    CountablyRectifiable k s ↔
      ∃ (A : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ℕ → EuclideanSpace ℝ (Fin k) → V),
        (∀ n, MeasurableSet (A n)) ∧
        (∀ n, ∃ K L : ℝ≥0,
          LipschitzWith K (f n) ∧ AntilipschitzWith L ((A n).domRestrict (f n))) ∧
        μHE[k] (s \ ⋃ n, f n '' A n) = 0 := by
  refine ⟨fun hs ↦ hs.exists_bilipschitz_cover, ?_⟩
  rintro ⟨A, f, -, hf, hnull⟩
  choose K L hLip hAnti using hf
  exact countablyRectifiable_iff.mpr
    ⟨A, fun n ↦ (A n).domRestrict (f n), fun n ↦ ⟨K n, (hLip n).restrict _⟩,
      by simpa only [range_domRestrict] using hnull⟩

end TauCeti
