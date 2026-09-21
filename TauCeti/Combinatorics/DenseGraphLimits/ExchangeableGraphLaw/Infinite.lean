/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Coordinates
public import TauCeti.Combinatorics.DenseGraphLimits.ExchangeableGraphLaw.Defs
import Mathlib.Logic.Equiv.Fintype
import TauCeti.MeasureTheory.Measure.ProjectiveLimit.Countable

/-!
# Exchangeable laws on infinite graphs

An exchangeable random graph on the labels `ℕ` is a probability law on `SimpleGraph ℕ` that is
invariant under relabelling along every permutation of `ℕ`. Its windows — the laws of the
restrictions to the labels `Fin k` — form an `ExchangeableGraphLaw`: restricting along an
injection `Fin k ↪ Fin l` is, on the infinite graph, relabelling by a permutation of `ℕ` extending
the injection, followed by taking the smaller window. Conversely every `ExchangeableGraphLaw` is
the family of windows of exactly one such law, so the two presentations of an exchangeable random
graph agree (`exchangeableGraphLawEquivInfinite`).

Uniqueness holds because a finite measure on `SimpleGraph ℕ` is determined by its windows
(`measure_ext_of_map_restrictFin`). Existence is Kolmogorov's extension theorem: reading an
infinite graph through its Boolean edge coordinates `graphCoordEquiv`, the level-`n` marginals
prescribe a projective family of laws on the finitely many coordinates below any bound, and a
projective limit on the countable product of the coordinates exists. The extension is exchangeable
because each window of a relabelled extension is a restriction of a larger window along an
injection, which the consistency of the marginals controls.

## Main definitions

* `TauCeti.DenseGraphLimits.InfiniteExchangeableGraphLaw` — a relabelling-invariant probability law
  on the graphs on `ℕ`;
* `TauCeti.DenseGraphLimits.exchangeableGraphLawEquivInfinite` — consistent finite marginals are
  the same thing as an exchangeable law on infinite graphs.

## Main results

* `TauCeti.DenseGraphLimits.exchangeableGraphLawEquivInfinite_law_map_restrictFin` — the windows of
  the infinite law attached to an exchangeable graph law are its marginals;
* `TauCeti.DenseGraphLimits.exchangeableGraphLawEquivInfinite_symm_law` — conversely the marginals
  attached to an infinite law are its windows.

## References

* P. Diaconis, S. Janson, *Graph limits and exchangeable random graphs*, Rend. Mat. Appl. (7) 28
  (2008), 33--61, Section 5.
* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/InfiniteLaw.lean` and
  `Graphon/InfiniteExchangeability.lean`, a prior formalization of the same equivalence between
  consistent marginals and exchangeable laws on infinite graphs.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace DenseGraphLimits

/-- A window of a graph on `Fin n` embedded in `ℕ` is a restriction along the inclusion. -/
private theorem restrictFin_map_valEmbedding {m n : ℕ} (H : SimpleGraph (Fin n)) (h : m ≤ n) :
    (H.map Fin.valEmbedding).restrictFin m = H.comap (Fin.castLEEmb h) := by
  ext a b
  rw [SimpleGraph.restrictFin_adj, SimpleGraph.comap_adj,
    ← SimpleGraph.map_adj_apply (f := Fin.valEmbedding)]
  simp

/-- The graph on `Fin n` embedded in `ℕ` has that graph as its window below `n`. -/
private theorem restrictFin_map_valEmbedding_self {n : ℕ} (H : SimpleGraph (Fin n)) :
    (H.map Fin.valEmbedding).restrictFin n = H := by
  rw [restrictFin_map_valEmbedding H le_rfl]
  ext a b
  simp

/-- Two graphs on `ℕ` have the same window below `n` exactly when their edge coordinates agree
below `n`. -/
private theorem restrictFin_eq_restrictFin_iff {n : ℕ} {G G' : SimpleGraph ℕ} :
    G.restrictFin n = G'.restrictFin n ↔
      ∀ e ∈ edgeWindow n, graphCoordEquiv G e = graphCoordEquiv G' e := by
  refine ⟨fun h e he => by
    rw [graphCoordEquiv_eq_windowCoord G he, graphCoordEquiv_eq_windowCoord G' he, h],
    fun h => ?_⟩
  ext a b
  rw [SimpleGraph.restrictFin_adj, SimpleGraph.restrictFin_adj]
  by_cases hab : a = b
  · subst hab
    simp
  have hs : ¬ s((a : ℕ), (b : ℕ)).IsDiag := by
    simpa [Sym2.mk_isDiag_iff, Fin.val_inj] using hab
  have he : (⟨s((a : ℕ), (b : ℕ)), hs⟩ : EdgeIndex) ∈ edgeWindow n := by
    refine mem_edgeWindow.2 fun c hc => ?_
    rcases Sym2.mem_iff.1 hc with rfl | rfl
    exacts [a.2, b.2]
  have := h _ he
  rwa [Bool.eq_iff_iff, SimpleGraph.graphCoordEquiv_apply,
    SimpleGraph.graphCoordEquiv_apply] at this

/-- Restricting a graph on `Fin n` to a smaller window does not change its edge coordinates below
the smaller bound. -/
private theorem windowCoord_comap_castLEEmb {m n : ℕ} (h : m ≤ n) (H : SimpleGraph (Fin n))
    {e : EdgeIndex} (he : e ∈ edgeWindow m) :
    windowCoord (H.comap (Fin.castLEEmb h)) e = windowCoord H e := by
  rw [← restrictFin_map_valEmbedding H h, ← graphCoordEquiv_eq_windowCoord _ he,
    windowCoord_apply]

/-! ### The extension of consistent marginals -/

namespace ExchangeableGraphLaw

variable (L : ExchangeableGraphLaw)

/-- The law of the edge coordinates in `J` of the level-`n` sample. -/
private def coordLaw (n : ℕ) (J : Finset EdgeIndex) : Measure (∀ _ : J, Bool) :=
  (L.law n).map fun H => J.restrict (windowCoord H)

/-- The law of the coordinates in `J` does not depend on the level, as long as the level bounds
the endpoints of `J`. -/
private theorem coordLaw_eq_of_le {J : Finset EdgeIndex} {m n : ℕ} (hJ : J ⊆ edgeWindow m)
    (h : m ≤ n) : L.coordLaw n J = L.coordLaw m J := by
  rw [coordLaw, coordLaw, ← L.consistent (Fin.castLEEmb h),
    Measure.map_map (measurable_of_countable _) (SimpleGraph.measurable_comap _)]
  congr 1
  funext H
  ext e
  exact (windowCoord_comap_castLEEmb h H (hJ e.2)).symm

private theorem coordLaw_eq {J : Finset EdgeIndex} {m n : ℕ} (hm : J ⊆ edgeWindow m)
    (hn : J ⊆ edgeWindow n) : L.coordLaw m J = L.coordLaw n J := by
  rw [← L.coordLaw_eq_of_le hm (le_max_left m n), L.coordLaw_eq_of_le hn (le_max_right m n)]

/-- The marginals prescribe the law of every finite set of edge coordinates. -/
private def coordFamily (J : Finset EdgeIndex) : Measure (∀ _ : J, Bool) :=
  L.coordLaw (windowBound J) J

private instance (J : Finset EdgeIndex) : IsProbabilityMeasure (L.coordFamily J) := by
  unfold coordFamily coordLaw
  infer_instance

private theorem isProjectiveMeasureFamily_coordFamily :
    IsProjectiveMeasureFamily (α := fun _ : EdgeIndex => Bool) L.coordFamily := by
  intro I J hJI
  have hJ := (subset_edgeWindow_windowBound J)
  have hI := (subset_edgeWindow_windowBound I)
  rw [coordFamily, coordFamily, L.coordLaw_eq hJ (hJI.trans hI), coordLaw, coordLaw,
    Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  -- Restricting the coordinates in `I` to `J` is restricting to `J` (`restrict₂_comp_restrict`).
  rfl

/-- **Kolmogorov extension** of the coordinate laws prescribed by the marginals. -/
private theorem exists_isProjectiveLimit_coordFamily :
    ∃ μ : Measure (EdgeIndex → Bool), IsProbabilityMeasure μ ∧ IsProjectiveLimit μ L.coordFamily :=
  TauCeti.Measure.exists_isProjectiveLimit_of_countable (X := fun _ : EdgeIndex => Bool)
    L.coordFamily L.isProjectiveMeasureFamily_coordFamily

/-- The law of the edge coordinates of the extension: the projective limit of `coordFamily`. -/
private def coordLimit : Measure (EdgeIndex → Bool) :=
  L.exists_isProjectiveLimit_coordFamily.choose

private instance : IsProbabilityMeasure L.coordLimit :=
  L.exists_isProjectiveLimit_coordFamily.choose_spec.1

private theorem isProjectiveLimit_coordLimit : IsProjectiveLimit L.coordLimit L.coordFamily :=
  L.exists_isProjectiveLimit_coordFamily.choose_spec.2

/-- The law on infinite graphs extending the marginals. -/
private def extensionLaw : Measure (SimpleGraph ℕ) :=
  L.coordLimit.map graphCoordEquiv.symm

private instance : IsProbabilityMeasure L.extensionLaw := by
  unfold extensionLaw
  infer_instance

/-- The windows of the extension are the marginals. -/
private theorem extensionLaw_map_restrictFin (n : ℕ) :
    L.extensionLaw.map (·.restrictFin n) = L.law n := by
  classical
  refine Measure.ext_of_singleton fun H => ?_
  -- The event that the window is `H` is a cylinder on the coordinates below `n`.
  have hpre : (fun G : SimpleGraph ℕ => G.restrictFin n) ∘ graphCoordEquiv.symm ⁻¹' {H} =
      (edgeWindow n).restrict (π := fun _ => Bool) ⁻¹'
        ({(edgeWindow n).restrict (windowCoord H)} : Set (edgeWindow n → Bool)) := by
    ext x
    simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, funext_iff,
      Finset.restrict, Subtype.forall]
    rw [← restrictFin_map_valEmbedding_self H, restrictFin_eq_restrictFin_iff,
      restrictFin_map_valEmbedding_self]
    simp [windowCoord_apply]
  have hwin : ∀ H' : SimpleGraph (Fin n),
      (edgeWindow n).restrict (windowCoord H') = (edgeWindow n).restrict (windowCoord H) ↔
        H' = H := fun H' => by
    rw [← restrictFin_map_valEmbedding_self H', ← restrictFin_map_valEmbedding_self H,
      restrictFin_eq_restrictFin_iff, restrictFin_map_valEmbedding_self,
      restrictFin_map_valEmbedding_self, funext_iff]
    simp [windowCoord_apply, Finset.restrict]
  rw [extensionLaw, Measure.map_map (SimpleGraph.measurable_restrictFin n)
      measurable_graphCoordEquiv_symm,
    Measure.map_apply ((SimpleGraph.measurable_restrictFin n).comp
      measurable_graphCoordEquiv_symm) (measurableSet_singleton H), hpre,
    ← Measure.map_apply (Finset.measurable_restrict _) (measurableSet_singleton _),
    L.isProjectiveLimit_coordLimit, coordFamily,
    L.coordLaw_eq (subset_edgeWindow_windowBound _) subset_rfl, coordLaw,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  congr 1
  ext H'
  exact hwin H'

/-- The extension is invariant under every relabelling: a window of the relabelled extension is a
restriction of a larger window along an injection of labels. -/
private theorem extensionLaw_map_comap (σ : Equiv.Perm ℕ) :
    L.extensionLaw.map (SimpleGraph.comap ⇑σ) = L.extensionLaw := by
  refine measure_ext_of_map_restrictFin fun n => ?_
  obtain ⟨m, hm⟩ := Finset.exists_nat_subset_range (Finset.univ.image fun i : Fin n => σ i)
  have hlt : ∀ i : Fin n, σ i < m := fun i =>
    Finset.mem_range.1 (hm (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  let f : Fin n ↪ Fin m :=
    ⟨fun i => ⟨σ i, hlt i⟩, fun i j hij => Fin.ext (σ.injective (Fin.mk.inj_iff.1 hij))⟩
  have hwin : (fun G : SimpleGraph ℕ => G.restrictFin n) ∘ SimpleGraph.comap ⇑σ =
      SimpleGraph.comap ⇑f ∘ fun G : SimpleGraph ℕ => G.restrictFin m := by
    funext G
    ext a b
    simp only [Function.comp_apply, SimpleGraph.restrictFin_adj, SimpleGraph.comap_adj]
    -- The label `f a` below `m` is `σ a`, read in `Fin m`.
    exact Iff.rfl
  rw [Measure.map_map (SimpleGraph.measurable_restrictFin n) (SimpleGraph.measurable_comap _),
    hwin, ← Measure.map_map (SimpleGraph.measurable_comap _) (SimpleGraph.measurable_restrictFin m),
    L.extensionLaw_map_restrictFin, L.consistent, L.extensionLaw_map_restrictFin]

end ExchangeableGraphLaw

/-! ### Exchangeable laws on infinite graphs -/

/-- An **exchangeable law on infinite graphs**: a probability law on the graphs on `ℕ` invariant
under relabelling along every permutation of `ℕ`. -/
structure InfiniteExchangeableGraphLaw where
  /-- The law on infinite graphs. -/
  law : Measure (SimpleGraph ℕ)
  /-- It is a probability measure. -/
  prob : IsProbabilityMeasure law
  /-- Invariance under every relabelling. -/
  exchangeable : ∀ σ : Equiv.Perm ℕ, law.map (SimpleGraph.comap ⇑σ) = law

attribute [simp] InfiniteExchangeableGraphLaw.exchangeable

namespace InfiniteExchangeableGraphLaw

instance instIsProbabilityMeasureLaw (L : InfiniteExchangeableGraphLaw) :
    IsProbabilityMeasure L.law := L.prob

/-- An exchangeable law on infinite graphs is determined by its law: the other fields are
propositions. -/
@[ext]
theorem ext {L L' : InfiniteExchangeableGraphLaw} (h : L.law = L'.law) : L = L' := by
  cases L
  cases L'
  congr

/-- The windows of an exchangeable law on infinite graphs are consistent along every injection of
labels: an injection `Fin k ↪ Fin l` is the restriction of a permutation of `ℕ`, under which the
law is invariant. -/
private theorem map_restrictFin_map_comap (L : InfiniteExchangeableGraphLaw) {k l : ℕ}
    (f : Fin k ↪ Fin l) :
    (L.law.map (·.restrictFin l)).map (SimpleGraph.comap ⇑f) = L.law.map (·.restrictFin k) := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair (fun i : Fin k => (i : ℕ))
    (fun i => (f i : ℕ)) Fin.val_injective (Fin.val_injective.comp f.injective)
  have hwin : SimpleGraph.comap ⇑f ∘ (fun G : SimpleGraph ℕ => G.restrictFin l) =
      (fun G : SimpleGraph ℕ => G.restrictFin k) ∘ SimpleGraph.comap ⇑σ := by
    funext G
    ext a b
    simp [hσ]
  rw [Measure.map_map (SimpleGraph.measurable_comap _) (SimpleGraph.measurable_restrictFin l),
    hwin, ← Measure.map_map (SimpleGraph.measurable_restrictFin k) (SimpleGraph.measurable_comap _),
    L.exchangeable]

end InfiniteExchangeableGraphLaw

/-- **Consistent finite marginals are an exchangeable law on infinite graphs.** An exchangeable
graph law extends to a unique relabelling-invariant law on the graphs on `ℕ` whose windows are its
marginals; conversely the windows of such a law are consistent marginals. -/
def exchangeableGraphLawEquivInfinite : ExchangeableGraphLaw ≃ InfiniteExchangeableGraphLaw where
  toFun L := ⟨L.extensionLaw, inferInstance, L.extensionLaw_map_comap⟩
  invFun L :=
    { law := fun k => L.law.map (·.restrictFin k)
      prob := fun _ => inferInstance
      consistent := L.map_restrictFin_map_comap }
  left_inv L := ExchangeableGraphLaw.ext fun k => L.extensionLaw_map_restrictFin k
  right_inv _ := InfiniteExchangeableGraphLaw.ext <| measure_ext_of_map_restrictFin fun n =>
    ExchangeableGraphLaw.extensionLaw_map_restrictFin _ n

/-- **The windows of the extension are the marginals.** The level-`k` window of the infinite law
attached to an exchangeable graph law is its level-`k` marginal. -/
@[simp]
theorem exchangeableGraphLawEquivInfinite_law_map_restrictFin (L : ExchangeableGraphLaw) (k : ℕ) :
    (exchangeableGraphLawEquivInfinite L).law.map (·.restrictFin k) = L.law k :=
  L.extensionLaw_map_restrictFin k

/-- The marginals attached to an exchangeable law on infinite graphs are its windows. -/
@[simp]
theorem exchangeableGraphLawEquivInfinite_symm_law (L : InfiniteExchangeableGraphLaw) (k : ℕ) :
    (exchangeableGraphLawEquivInfinite.symm L).law k = L.law.map (·.restrictFin k) :=
  (rfl)

end DenseGraphLimits

end TauCeti
