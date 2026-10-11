/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Claude
-/
module

public import Mathlib.MeasureTheory.Constructions.SimpleGraph
public import Mathlib.MeasureTheory.PiSystem
public import TauCeti.Combinatorics.SimpleGraph.Maps

/-!
# Measurability of individual simple graphs and of relabelling

Mathlib equips `SimpleGraph V` with the sigma-algebra induced by all adjacency coordinates. When
`V` is countable, an individual graph is measurable because its edge set is a measurable point in
the countable product space. This supplies the discrete integration API for finite random graphs.

Each adjacency coordinate of a graph pulled back along a map of vertex types is a single
adjacency coordinate of the source graph, so the pullback is measurable with no hypothesis on
either vertex type. This is what lets a random graph be restricted to a window of labels: the
window `SimpleGraph.restrictFin` is the special case along `Fin.val`.

For graphs on `ℕ` the windows carve out the *window cylinders*, the events that a prescribed
finite window occurs. Two cylinders meet in a cylinder, and every adjacency coordinate is read
off a long enough window, so the cylinders are a π-system generating the sigma-algebra. That is
the test family for the two standard reductions on infinite graphs: a finite measure is
determined by its values on cylinders, and a family of probability measures is measurable once
its cylinder masses are.

## Main definitions

* `SimpleGraph.restrictFinCylinders` — the window cylinders of graphs on `ℕ`.

## Main results

* `SimpleGraph.instMeasurableSingletonClass` — singletons of graphs on a countable vertex type are
  measurable;
* `SimpleGraph.measurable_comap` — pulling back along a map of vertex types is measurable;
* `SimpleGraph.measurable_restrictFin` — taking a window is measurable;
* `SimpleGraph.isPiSystem_restrictFinCylinders` and
  `SimpleGraph.generateFrom_restrictFinCylinders` — the window cylinders are a π-system
  generating the sigma-algebra on `SimpleGraph ℕ`.

## Reference

* C. Freer, `cameronfreer/graphon` at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, Apache-2.0, `Graphon/SamplingLaw.lean`. The
  instance is adapted from its measurable singleton instance; the proof here goes through
  Mathlib's `SimpleGraph.measurableEmbedding_edgeSet`.
-/

public section

open MeasureTheory

namespace SimpleGraph

variable {V : Type*}

/-- The canonical measurable space on simple graphs over a countable vertex type has measurable
singletons. -/
instance instMeasurableSingletonClass [Countable V] :
    MeasurableSingletonClass (SimpleGraph V) where
  measurableSet_singleton G := by
    rw [← measurableEmbedding_edgeSet.measurableSet_image, Set.image_singleton]
    exact MeasurableSet.singleton _

variable {W : Type*}

/-- Pulling a simple graph back along a map of vertex types is measurable: each adjacency
coordinate of the pullback is an adjacency coordinate of the source. -/
@[fun_prop]
theorem measurable_comap (f : V → W) :
    Measurable (SimpleGraph.comap f : SimpleGraph W → SimpleGraph V) :=
  measurable_iff_adj.2 fun u v => measurable_iff_adj.1 measurable_id (f u) (f v)

/-- Taking a window is measurable. -/
@[fun_prop]
theorem measurable_restrictFin (n : ℕ) :
    Measurable fun G : SimpleGraph ℕ => G.restrictFin n :=
  -- The adjacency equation `restrictFin_adj` is used rather than unfolding `restrictFin` to the
  -- pullback it is defined as.
  measurable_iff_adj.2 fun u v => by
    simp only [restrictFin_adj]
    exact measurable_iff_adj.1 measurable_id (u : ℕ) v

open Classical in
/-- Reading a graph as its adjacency array is measurable. -/
@[fun_prop]
theorem measurable_adjArray {V : Type*} :
    Measurable (adjArray : SimpleGraph V → V × V → Bool) :=
  Measurable.of_eval fun ⟨i, j⟩ => by
    simp only [adjArray_apply]
    exact (measurable_of_countable (fun q : Prop => decide q)).comp
      (measurable_iff_adj.1 measurable_id i j)

/-! ### Window cylinders -/

/-- The **window cylinders** of graphs on `ℕ`: the events that the window spanned by the first
`n` labels is a prescribed finite graph. -/
def restrictFinCylinders : Set (Set (SimpleGraph ℕ)) :=
  {s | ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
    s = (fun G : SimpleGraph ℕ => G.restrictFin n) ⁻¹' {H}}

/-- Membership in the window cylinders unfolds to a window and a prescribed finite graph. -/
theorem mem_restrictFinCylinders {s : Set (SimpleGraph ℕ)} :
    s ∈ restrictFinCylinders ↔ ∃ (n : ℕ) (H : SimpleGraph (Fin n)),
      s = (fun G : SimpleGraph ℕ => G.restrictFin n) ⁻¹' {H} := Iff.rfl

/-- The event that the length-`n` window is `H` is a window cylinder. -/
theorem preimage_restrictFin_mem_restrictFinCylinders (n : ℕ) (H : SimpleGraph (Fin n)) :
    (fun G : SimpleGraph ℕ => G.restrictFin n) ⁻¹' {H} ∈ restrictFinCylinders := ⟨n, H, rfl⟩

/-- Window cylinders are measurable, since taking a window is measurable and singletons of
finite graphs are measurable. -/
theorem measurableSet_of_mem_restrictFinCylinders {s : Set (SimpleGraph ℕ)}
    (hs : s ∈ restrictFinCylinders) : MeasurableSet s := by
  obtain ⟨n, H, rfl⟩ := hs
  exact measurable_restrictFin n (measurableSet_singleton H)

/-- **The window cylinders are a π-system.** Of two cylinders that meet, the one at the longer
window is contained in the other, because the shorter window is a window of the longer one. -/
theorem isPiSystem_restrictFinCylinders : IsPiSystem restrictFinCylinders := by
  -- The ordered case; the general case follows by symmetry.
  have key : ∀ {m n : ℕ} (_ : m ≤ n) (H : SimpleGraph (Fin m)) (H' : SimpleGraph (Fin n)),
      ((fun G : SimpleGraph ℕ => G.restrictFin m) ⁻¹' {H} ∩
          (fun G : SimpleGraph ℕ => G.restrictFin n) ⁻¹' {H'}).Nonempty →
      (fun G : SimpleGraph ℕ => G.restrictFin m) ⁻¹' {H} ∩
          (fun G : SimpleGraph ℕ => G.restrictFin n) ⁻¹' {H'} =
        (fun G : SimpleGraph ℕ => G.restrictFin n) ⁻¹' {H'} := by
    rintro m n hmn H H' ⟨G₀, hG₀m, hG₀n⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hG₀m hG₀n
    refine Set.inter_eq_right.2 fun G hG => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hG ⊢
    rw [← comap_restrictFin_castLE G hmn, hG, ← hG₀n, comap_restrictFin_castLE, hG₀m]
  rintro _ ⟨m, H, rfl⟩ _ ⟨n, H', rfl⟩ hne
  rcases le_total m n with hmn | hnm
  · rw [key hmn H H' hne]
    exact ⟨n, H', rfl⟩
  · rw [Set.inter_comm] at hne ⊢
    rw [key hnm H' H hne]
    exact ⟨m, H, rfl⟩

/-- **The window cylinders generate the sigma-algebra on infinite graphs.** Every adjacency
coordinate is read off the window spanned by the first `max u v + 1` labels, and that window takes
countably many values. -/
theorem generateFrom_restrictFinCylinders :
    MeasurableSpace.generateFrom restrictFinCylinders =
      (inferInstance : MeasurableSpace (SimpleGraph ℕ)) := by
  refine le_antisymm (MeasurableSpace.generateFrom_le fun s hs =>
    measurableSet_of_mem_restrictFinCylinders hs) ?_
  have hid : Measurable[MeasurableSpace.generateFrom restrictFinCylinders]
      (id : SimpleGraph ℕ → SimpleGraph ℕ) := by
    refine measurable_iff_adj.2 fun u v => ?_
    -- The fibres of the window map are cylinders and the graphs on `Fin (max u v + 1)` form a
    -- countable type.  The sigma-algebra on the source is supplied explicitly because it is the
    -- generated one, not the ambient instance.
    have hwin : Measurable[MeasurableSpace.generateFrom restrictFinCylinders]
        fun G : SimpleGraph ℕ => G.restrictFin (max u v + 1) :=
      @measurable_to_countable' _ _ _ _ (MeasurableSpace.generateFrom restrictFinCylinders) _
        fun H => MeasurableSpace.measurableSet_generateFrom
          (preimage_restrictFin_mem_restrictFinCylinders _ H)
    have hu : u < max u v + 1 := Nat.lt_succ_of_le (le_max_left u v)
    have hv : v < max u v + 1 := Nat.lt_succ_of_le (le_max_right u v)
    simpa using measurable_iff_adj.1 hwin ⟨u, hu⟩ ⟨v, hv⟩
  simpa using measurable_iff_comap_le.1 hid

end SimpleGraph
