/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.Basic
import TauCeti.MeasureTheory.Function.AreaFormula.Lipschitz
import TauCeti.Topology.EMetricSpace.Lipschitz

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

When `s` is `μHE[k]`-null-measurable,
`CountablyRectifiable.exists_disjoint_measurable_bilipschitz_cover` refines the cover to pairwise
disjoint Borel bi-Lipschitz images inside `s`, and for `LocallyLipschitzOn s g` into a
finite-dimensional real normed space,
`LocallyLipschitzOn.exists_disjoint_measurable_bilipschitz_extension_cover` further refines the
patches so that `g` agrees on each patch with a globally Lipschitz map.

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

/-- **Disjoint Borel bi-Lipschitz patch decomposition** up to a `μHE[k]`-null set. -/
theorem CountablyRectifiable.exists_disjoint_measurable_bilipschitz_cover {k : ℕ} {s : Set V}
    (hs : CountablyRectifiable k s) (hsm : NullMeasurableSet s μHE[k]) :
    ∃ (B : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ℕ → EuclideanSpace ℝ (Fin k) → V)
      (K_f L_f : ℕ → ℝ≥0), (∀ n, MeasurableSet (B n)) ∧ (∀ n, MeasurableSet (f n '' B n)) ∧
      (∀ n, LipschitzWith (K_f n) (f n) ∧ AntilipschitzWith (L_f n) ((B n).domRestrict (f n))) ∧
      Pairwise (Disjoint on fun n ↦ f n '' B n) ∧ (∀ n, f n '' B n ⊆ s) ∧
      (⋃ n, f n '' B n : Set V) =ᵐ[μHE[k]] s := by
  classical
  obtain ⟨s₀, hs₀_sub, hs₀m, hs₀_ae⟩ := hsm.exists_measurable_subset_ae_eq
  obtain ⟨A, f, hAm, hbi, hc⟩ := hs.exists_bilipschitz_cover; choose K_f L_f hLip hAnti using hbi
  let S (n : ℕ) : Set V := (f n '' A n) ∩ s₀
  have hSm (n : ℕ) := ((hAm n).image_of_continuousOn_injOn (hLip n).continuous.continuousOn
    (injOn_iff_injective.mpr (hAnti n).injective)).inter hs₀m
  let B (n : ℕ) := A n ∩ (f n) ⁻¹' disjointed S n
  have hBm (n : ℕ) := (hAm n).inter ((MeasurableSet.disjointed hSm n).preimage
    (hLip n).continuous.measurable)
  have himg (n : ℕ) : f n '' B n = disjointed S n := (image_inter_preimage _ _ _).trans <|
    inter_eq_self_of_subset_right ((disjointed_subset S n).trans inter_subset_left)
  have hUnion : (⋃ n, f n '' B n) = (⋃ n, f n '' A n) ∩ s₀ := by
    simp_rw [himg]; rw [iUnion_disjointed, ← iUnion_inter]
  have hsub_s : (⋃ n, f n '' B n) ⊆ s := hUnion ▸ inter_subset_right.trans hs₀_sub
  refine ⟨B, f, K_f, L_f, hBm, fun n ↦ (himg n).symm ▸ MeasurableSet.disjointed hSm n,
    fun n ↦ ⟨hLip n, fun u v ↦ (hAnti n) ⟨u, u.property.1⟩ ⟨v, v.property.1⟩⟩,
    fun m n hmn ↦ by simpa only [Function.onFun, himg] using disjoint_disjointed S hmn,
    fun n ↦ (subset_iUnion (fun m ↦ f m '' B m) n).trans hsub_s, ?_⟩
  refine Filter.EventuallySubset.antisymm (Filter.Eventually.of_forall fun _ hx ↦ hsub_s hx) ?_
  simpa only [inter_self, hUnion] using (ae_subset.mpr hc).inter hs₀_ae.symm.subset

end TauCeti

/-- Disjoint Borel bi-Lipschitz patch cover of `E` with globally Lipschitz patchwise extensions of
`g` for `hg : LocallyLipschitzOn E g`. -/
theorem LocallyLipschitzOn.exists_disjoint_measurable_bilipschitz_extension_cover
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    {k : ℕ} {E : Set V} {g : V → W} (hg : LocallyLipschitzOn E g)
    (hE : TauCeti.CountablyRectifiable k E) (hEm : NullMeasurableSet E μHE[k]) :
    ∃ (B : ℕ → Set (EuclideanSpace ℝ (Fin k))) (f : ℕ → EuclideanSpace ℝ (Fin k) → V)
      (gExt : ℕ → V → W) (K_f L_f K_g : ℕ → ℝ≥0),
      (∀ n, MeasurableSet (B n)) ∧ (∀ n, MeasurableSet (f n '' B n)) ∧
      (∀ n, LipschitzWith (K_f n) (f n) ∧ AntilipschitzWith (L_f n) ((B n).domRestrict (f n))) ∧
      (∀ n, LipschitzWith (K_g n) (gExt n) ∧ EqOn g (gExt n) (f n '' B n)) ∧
      Pairwise (Disjoint on fun n ↦ f n '' B n) ∧
      (∀ n, f n '' B n ⊆ E) ∧ (⋃ n, f n '' B n) =ᵐ[μHE[k]] E := by
  obtain ⟨O, _, hO, hcov, hLip⟩ := hg.exists_open_cover_lipschitzOnWith (.of_separableSpace E)
  choose gExt₀ hgExt_lip hgExt_eq using fun m ↦ (hLip m).extend_finite_dimension
  let U := disjointed O
  have hDm (m : ℕ) : MeasurableSet (U m) :=
    MeasurableSet.disjointed (fun j ↦ (hO j).measurableSet) m
  obtain ⟨B₀, f₀, K₀, L₀, hBm₀, hTm₀, hbi₀, hdisj₀, hsub₀, hcov_ae₀⟩ :=
    hE.exists_disjoint_measurable_bilipschitz_cover hEm
  let B (n : ℕ) := B₀ n.unpair.1 ∩ f₀ n.unpair.1 ⁻¹' U n.unpair.2
  let f (n : ℕ) := f₀ n.unpair.1
  have himg (n : ℕ) : f n '' B n = f₀ n.unpair.1 '' B₀ n.unpair.1 ∩ U n.unpair.2 :=
    Set.image_inter_preimage _ _ _
  have hunion : (⋃ n, f n '' B n) = ⋃ i, f₀ i '' B₀ i := Subset.antisymm
    (iUnion_subset fun n ↦
      himg n ▸ inter_subset_left.trans (subset_iUnion (fun i ↦ f₀ i '' B₀ i) n.unpair.1))
    (iUnion_subset fun i x hx ↦ by
      obtain ⟨m, hxm⟩ := mem_iUnion.mp (by
        simpa only [U, iUnion_disjointed] using hcov (hsub₀ i hx) : x ∈ ⋃ m, U m)
      exact mem_iUnion.mpr ⟨Nat.pair i m, by rw [himg, Nat.unpair_pair]; exact ⟨hx, hxm⟩⟩)
  refine ⟨B, f, fun n ↦ gExt₀ n.unpair.2, fun n ↦ K₀ n.unpair.1, fun n ↦ L₀ n.unpair.1,
    fun n ↦ _, fun n ↦ (hBm₀ _).inter ((hDm _).preimage (hbi₀ _).1.continuous.measurable),
    fun n ↦ himg n ▸ (hTm₀ _).inter (hDm _),
    fun n ↦ ⟨(hbi₀ _).1, fun u v ↦ (hbi₀ _).2 ⟨u.val, u.property.1⟩ ⟨v.val, v.property.1⟩⟩,
    fun n ↦ ⟨hgExt_lip _, (hgExt_eq _).mono (himg n ▸ inter_subset_inter (hsub₀ _)
      (disjointed_subset O _))⟩,
    fun m n hmn ↦ ?_, fun n ↦ himg n ▸ inter_subset_left.trans (hsub₀ _), hunion ▸ hcov_ae₀⟩
  rw [Function.onFun, himg m, himg n]
  by_cases h1 : m.unpair.1 = n.unpair.1
  · exact (disjoint_disjointed O fun h2 ↦ hmn (by rw [← Nat.pair_unpair m, ← Nat.pair_unpair n,
      h1, h2])).mono inter_subset_right inter_subset_right
  · exact (hdisj₀ h1).mono inter_subset_left inter_subset_left
