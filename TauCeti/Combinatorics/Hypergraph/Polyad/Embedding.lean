/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Polyad.TopRegular
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Top regularity under vertex embeddings

An embedding into a larger host sends a subpolyad to the images of its three pair graphs.
Its supported triples, and unions of such supports, are exactly the images of the original
supports. Thus arbitrary subpolyad-union tests on a smaller host are legitimate tests on the
larger host.

Top regularity restricts with the usual slicing loss when the smaller polyad retains an
`α`-fraction of the original support. This is the local regularity estimate needed when
auxiliary vertices are removed after a divisibility padding argument. The palettes and
partitions on the two hosts may differ; only inclusion of the three mapped pair graphs is
required.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the padding and restriction setting.
* J. Komlós and M. Simonovits, *Szemerédi's regularity lemma and its applications in graph
  theory*, in Combinatorics, Paul Erdős is Eighty, Vol. 2 (1996), Fact 1.5 (slicing).
-/

open Finset

public section

namespace TauCeti

variable {κ κ₂ κ₂' V W : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  {S : PairSkeleton3 κ₂ V} {T : PairSkeleton3 κ₂' W} {P : Polyad3 S} {P' : Polyad3 T}

namespace Subpolyad3

variable (f : V ↪ W)
  (h₀₁ : P.pairSupport₀₁.map f.distinctPairMap ⊆ P'.pairSupport₀₁)
  (h₀₂ : P.pairSupport₀₂.map f.distinctPairMap ⊆ P'.pairSupport₀₂)
  (h₁₂ : P.pairSupport₁₂.map f.distinctPairMap ⊆ P'.pairSupport₁₂)

/-- Map the selected pairs of a subpolyad into a polyad on a larger host. -/
def map (Q : Subpolyad3 P) : Subpolyad3 P' where
  pair₀₁ := Q.pair₀₁.map f.distinctPairMap
  pair₀₂ := Q.pair₀₂.map f.distinctPairMap
  pair₁₂ := Q.pair₁₂.map f.distinctPairMap
  pair₀₁_sub := (map_subset_map.2 Q.pair₀₁_sub).trans h₀₁
  pair₀₂_sub := (map_subset_map.2 Q.pair₀₂_sub).trans h₀₂
  pair₁₂_sub := (map_subset_map.2 Q.pair₁₂_sub).trans h₁₂

@[simp]
theorem map_pair₀₁ (Q : Subpolyad3 P) :
    (Q.map f h₀₁ h₀₂ h₁₂).pair₀₁ = Q.pair₀₁.map f.distinctPairMap := (rfl)

@[simp]
theorem map_pair₀₂ (Q : Subpolyad3 P) :
    (Q.map f h₀₁ h₀₂ h₁₂).pair₀₂ = Q.pair₀₂.map f.distinctPairMap := (rfl)

@[simp]
theorem map_pair₁₂ (Q : Subpolyad3 P) :
    (Q.map f h₀₁ h₀₂ h₁₂).pair₁₂ = Q.pair₁₂.map f.distinctPairMap := (rfl)

/-- Mapping a subpolyad maps its supported injective triples exactly. -/
@[simp]
theorem support_map (Q : Subpolyad3 P) :
    (Q.map f h₀₁ h₀₂ h₁₂).support = Q.support.map f.injectiveMap := by
  ext y
  constructor
  · intro hy
    obtain ⟨hy₀₁, hy₀₂, hy₁₂⟩ := (mem_support_iff_coordPair_mem _ _).1 hy
    simp only [map_pair₀₁, map_pair₀₂, map_pair₁₂] at hy₀₁ hy₀₂ hy₁₂
    obtain ⟨a, -, hea⟩ := mem_map.1 hy₀₁
    obtain ⟨b, -, heb⟩ := mem_map.1 hy₀₂
    have h₀ : f a.1.1 = y.1 0 := by
      simpa using congrArg (fun p ↦ p.1.1) hea
    have h₁ : f a.1.2 = y.1 1 := by
      simpa using congrArg (fun p ↦ p.1.2) hea
    have h₂ : f b.1.2 = y.1 2 := by
      simpa using congrArg (fun p ↦ p.1.2) heb
    let x : Fin 3 → V := ![a.1.1, a.1.2, b.1.2]
    have hxval : f ∘ x = y.1 := by
      ext i
      fin_cases i <;> assumption
    have hx : Function.Injective x := by
      intro i j hij
      apply y.2
      rw [← hxval]
      exact congrArg f hij
    have hxy : f.injectiveMap ⟨x, hx⟩ = y := by
      apply Subtype.ext
      simpa only [Function.Embedding.injectiveMap_apply] using hxval
    refine mem_map.2 ⟨⟨x, hx⟩, ?_, hxy⟩
    rw [mem_support_iff_coordPair_mem]
    have hpair (i j : Fin 3) (hij : i ≠ j) :
        f.distinctPairMap (coordPair ⟨x, hx⟩ i j hij) = coordPair y i j hij := by
      rw [← Function.Embedding.coordPair_injectiveMap, hxy]
    exact ⟨by simpa only [← hpair 0 1 (by decide), mem_map'] using hy₀₁,
      by simpa only [← hpair 0 2 (by decide), mem_map'] using hy₀₂,
      by simpa only [← hpair 1 2 (by decide), mem_map'] using hy₁₂⟩
  · intro hy
    obtain ⟨x, hx, rfl⟩ := mem_map.1 hy
    rw [mem_support_iff_coordPair_mem] at hx ⊢
    simpa using hx

/-- Mapping a finite family of subpolyads maps its union support exactly. -/
@[simp]
theorem unionSupport_map {ι : Type*} [Fintype ι] (Q : ι → Subpolyad3 P) :
    unionSupport (fun i ↦ (Q i).map f h₀₁ h₀₂ h₁₂) = (unionSupport Q).map f.injectiveMap := by
  ext y
  simp only [mem_unionSupport, support_map, mem_map]
  aesop

end Subpolyad3

namespace Colored3Graph

variable [DecidableEq κ] {H : Colored3Graph κ W} {δ : ℝ} {r : ℕ}
  (f : V ↪ W)
  (h₀₁ : P.pairSupport₀₁.map f.distinctPairMap ⊆ P'.pairSupport₀₁)
  (h₀₂ : P.pairSupport₀₂.map f.distinctPairMap ⊆ P'.pairSupport₀₂)
  (h₁₂ : P.pairSupport₁₂.map f.distinctPairMap ⊆ P'.pairSupport₁₂)

include h₀₁ h₀₂ h₁₂

/-- A retained polyad whose image passes the original size threshold inherits each color's
density up to the original regularity parameter. -/
theorem IsTopRegularOverPolyad.abs_relativeDensity_comap_sub_le
    (h : H.IsTopRegularOverPolyad P' δ r) (hr : 1 ≤ r)
    (hsize : δ * #P'.support ≤ (#P.support : ℝ)) (c : κ) :
    |((H.comap f).relativeDensity c P : ℝ) - H.relativeDensity c P'| ≤ δ := by
  have htest := isTopRegularOverPolyad_one_iff.1 (h.of_rank_le hr) c
    ((Subpolyad3.ofSubcells P P.c₀ P.c₁ P.c₂).map f h₀₁ h₀₂ h₁₂)
    (by simpa using hsize)
  simpa only [Subpolyad3.support_map, Subpolyad3.support_ofSubcells_cells,
    ← relDensityOn_comap, ← relativeDensity_def] using htest

/-- If the mapped support is the whole original support, restriction preserves top regularity
at the same parameter and rank, including rank zero. -/
theorem IsTopRegularOverPolyad.comap
    (h : H.IsTopRegularOverPolyad P' δ r)
    (hsupport : P.support.map f.injectiveMap = P'.support) :
    (H.comap f).IsTopRegularOverPolyad P δ r := by
  rw [isTopRegularOverPolyad_iff]
  intro c Q hQ
  have hcard : #P'.support = #P.support := by rw [← hsupport, card_map]
  have htest := isTopRegularOverPolyad_iff.1 h c (fun i ↦ (Q i).map f h₀₁ h₀₂ h₁₂)
    (by simpa [hcard] using hQ)
  simpa only [Subpolyad3.unionSupport_map, ← hsupport, ← relDensityOn_comap,
    relativeDensity_def] using htest

/-- **Restriction after padding.** Top regularity on a larger host passes to a smaller polyad
whose mapped pair graphs are included and whose support retains at least an `α`-fraction of
the original support. The parameter becomes `max (2δ) (δ / α)` and the positive rank is preserved.
The vertex cells and the pair palettes on the two hosts may differ. -/
theorem IsTopRegularOverPolyad.comap_of_card_support_le
    (h : H.IsTopRegularOverPolyad P' δ r) (hr : 1 ≤ r) {α : ℝ} (hα : 0 < α)
    (hsize : α * #P'.support ≤ (#P.support : ℝ)) :
    (H.comap f).IsTopRegularOverPolyad P (max (2 * δ) (δ / α)) r := by
  rw [isTopRegularOverPolyad_iff]
  intro c Q hQ
  have hδ : 0 ≤ δ := haveI : Nonempty κ := ⟨c⟩; h.nonneg
  obtain hαδ | hδα := lt_or_ge α δ
  · exact isTopRegularOverPolyad_iff.1
      (isTopRegularOverPolyad_of_one_le P (H.comap f) r
        (le_max_of_le_right ((one_lt_div hα).2 hαδ).le)) c Q hQ
  have hU : δ * #P'.support ≤
      (#(Subpolyad3.unionSupport fun i ↦ (Q i).map f h₀₁ h₀₂ h₁₂) : ℝ) := by
    rw [Subpolyad3.unionSupport_map, card_map]
    calc δ * #P'.support = δ / α * (α * #P'.support) := by
          rw [← mul_assoc, div_mul_cancel₀ δ hα.ne']
      _ ≤ δ / α * #P.support := mul_le_mul_of_nonneg_left hsize (div_nonneg hδ hα.le)
      _ ≤ max (2 * δ) (δ / α) * #P.support := by gcongr; exact le_max_right _ _
      _ ≤ _ := hQ
  have h₁ := isTopRegularOverPolyad_iff.1 h c _ hU
  rw [Subpolyad3.unionSupport_map, ← relDensityOn_comap] at h₁
  have h₂ := h.abs_relativeDensity_comap_sub_le f h₀₁ h₀₂ h₁₂ hr
    ((mul_le_mul_of_nonneg_right hδα (Nat.cast_nonneg _)).trans hsize) c
  rw [abs_sub_comm] at h₂
  calc _ ≤ _ := abs_sub_le _ (H.relativeDensity c P' : ℝ) _
    _ ≤ 2 * δ := by linarith
    _ ≤ _ := le_max_left _ _

end Colored3Graph

end TauCeti
