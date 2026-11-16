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
The patches may extend beyond the set, as in `CountablyRectifiable` itself; when the set is
`μHE[k]`-null-measurable, intersecting with a Borel kernel refines the patches to lie inside the
set (`TauCeti.CountablyRectifiable.exists_bilipschitz_subset_cover`).

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
    simpa only [range_domRestrict, f] using ae_subset.mpr (hAnull n)
  refine ⟨fun n ↦ A (Nat.unpair n).1 (Nat.unpair n).2,
    fun n ↦ F (Nat.unpair n).1, fun n ↦ hAm _ _, fun n ↦ ?_, ?_⟩
  · obtain ⟨L, hL⟩ := hAanti (Nat.unpair n).1 (Nat.unpair n).2
    exact ⟨_, L, hF (Nat.unpair n).1, hL⟩
  · apply ae_subset.mp
    rw [Set.iUnion_unpair (fun n j ↦ F n '' A n j)]
    simp_rw [← range_domRestrict]
    exact (ae_subset.mpr hnull).trans
      ((Filter.EventuallySubset.countable_iUnion fun n ↦
        Filter.Eventually.of_forall (fun _ hx ↦ by
          rcases hx with ⟨x, rfl⟩
          exact ⟨x, hFg n x⟩)).trans
        (Filter.EventuallySubset.countable_iUnion hcover))

/-- A `μHE[k]`-null-measurable countably `k`-rectifiable set admits countably many bi-Lipschitz
Borel patches contained in the set itself (`f n '' A n ⊆ s`) covering it up to `μHE[k]`-measure
zero. -/
theorem CountablyRectifiable.exists_bilipschitz_subset_cover {k : ℕ} {s : Set V}
    (hs : CountablyRectifiable k s) (hsm : NullMeasurableSet s μHE[k]) :
    ∃ (A : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ℕ → EuclideanSpace ℝ (Fin k) → V),
      (∀ n, MeasurableSet (A n)) ∧ (∀ n, f n '' A n ⊆ s) ∧
      (∀ n, ∃ K L : ℝ≥0,
        LipschitzWith K (f n) ∧ AntilipschitzWith L ((A n).domRestrict (f n))) ∧
      μHE[k] (s \ ⋃ n, f n '' A n) = 0 := by
  obtain ⟨s₀, hs₀s, hs₀m, hs₀ae⟩ := hsm.exists_measurable_subset_ae_eq
  obtain ⟨A, f, hAm, hbi, hcover⟩ := (hs.congr hs₀ae.symm).exists_bilipschitz_cover
  choose K L hLip hAnti using hbi
  refine ⟨fun n => A n ∩ f n ⁻¹' s₀, f,
    fun n => (hAm n).inter (hs₀m.preimage (hLip n).continuous.measurable),
    fun n => image_subset_iff.2 fun _ hx => hs₀s hx.2,
    fun n => ⟨K n, L n, hLip n, fun x y => hAnti n ⟨x, x.2.1⟩ ⟨y, y.2.1⟩⟩, ?_⟩
  refine measure_mono_null (fun y ⟨hys, hyU⟩ => ?_)
    (measure_union_null (ae_eq_set.1 hs₀ae.symm).1 hcover)
  by_cases hys₀ : y ∈ s₀
  · refine Or.inr ⟨hys₀, fun hyA => ?_⟩
    obtain ⟨n, x, hx, rfl⟩ := mem_iUnion.1 hyA
    exact hyU (mem_iUnion.2 ⟨n, x, ⟨hx, hys₀⟩, rfl⟩)
  · exact Or.inl ⟨hys, hys₀⟩

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
  choose K L hLip _ using hf
  exact countablyRectifiable_iff.mpr
    ⟨A, fun n ↦ (A n).domRestrict (f n), fun n ↦ ⟨K n, (hLip n).restrict _⟩,
      by simpa only [range_domRestrict] using hnull⟩

end TauCeti
