/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

/-!
# Adjacency of actual connected components

The vertices are Mathlib's connected components of a subset. Two distinct
components are adjacent when their ambient closures share a point of a
specified regular set. A continuous curve leaving the subset only at finitely
many parameters, with regular values at those parameters, gives a finite graph walk.

This criterion turns curves with finitely many crossings into connectivity
results for component adjacency graphs, such as chamber graphs of wall complements.
No local connectedness or separation assumption on the ambient space is needed.

## Attribution

Adapted in full from `Mei/Topology/Connected/Basic.lean` and
`Mei/Topology/Connected/Adjacency.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), at
`9cf969cdee9748087aae45dbf4888a130890655c` (Apache 2.0).
Original author credit is retained; the new file uses the requested Tau Ceti copyright header.
-/

public section

open Set

namespace IsPreconnected

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A limiting value of a continuous image of a preconnected set lies in the
closure of the component containing the image of any point of that set. -/
theorem mem_closure_connectedComponentIn_image {s : Set X} {u : Set Y} {f : X → Y}
    (hs : IsPreconnected s) (hf : ContinuousOn f s) {x t : X} (hx : x ∈ s)
    (ht : t ∈ closure s) (hft : ContinuousWithinAt f s t) (hu : MapsTo f s u) :
    f t ∈ closure (_root_.connectedComponentIn u (f x)) := by
  exact hft.mem_closure ht (image_subset_iff.mp ((hs.image f hf).subset_connectedComponentIn
    (mem_image_of_mem f hx) (image_subset_iff.mpr hu)))

end IsPreconnected


namespace ConnectedComponents

variable {X : Type*} [TopologicalSpace X] {s : Set X}

/-- The ambient carrier of a connected component of a subset. -/
def carrier (c : ConnectedComponents s) : Set X :=
  Subtype.val '' {x : s | ConnectedComponents.mk x = c}

/-- A point belongs to a component's ambient carrier exactly when it lies in
the subset and represents that component. -/
theorem mem_carrier_iff {c : ConnectedComponents s} {x : X} :
    x ∈ c.carrier ↔ ∃ hx : x ∈ s, ConnectedComponents.mk ⟨x, hx⟩ = c := by
  constructor
  · rintro ⟨⟨y, hy⟩, hc, rfl⟩
    exact ⟨hy, hc⟩
  · rintro ⟨hx, hc⟩
    exact ⟨⟨x, hx⟩, hc, rfl⟩

/-- At a represented component the carrier is the actual `connectedComponentIn`. -/
@[simp]
theorem carrier_mk (x : s) :
    (ConnectedComponents.mk x).carrier = connectedComponentIn s x.val := by
  rw [carrier, connectedComponentIn_eq_image x.property]
  congr 1
  ext y
  exact ConnectedComponents.coe_eq_coe'

/-- A point lies in the carriers of at most one connected component of a subset. -/
theorem eq_of_mem_carrier {c c' : ConnectedComponents s} {z : X} (hz : z ∈ c.carrier)
    (hz' : z ∈ c'.carrier) : c = c' := by
  obtain ⟨_, rfl⟩ := mem_carrier_iff.mp hz
  obtain ⟨_, rfl⟩ := mem_carrier_iff.mp hz'
  rfl

/-- A preconnected subset lies in the carrier of any component containing one of its points. -/
theorem subset_carrier_of_isPreconnected {A : Set X} (hA : IsPreconnected A)
    (hAs : A ⊆ s) {z : X} (hz : z ∈ A) {c : ConnectedComponents s}
    (hzc : z ∈ c.carrier) : A ⊆ c.carrier := by
  obtain ⟨hzs, rfl⟩ := mem_carrier_iff.mp hzc
  rw [carrier_mk]
  exact hA.subset_connectedComponentIn hz hAs

/-- Equality of component vertices is membership in the ambient component carrier. -/
theorem mk_eq_mk_iff_mem_connectedComponentIn {x y : s} :
    ConnectedComponents.mk x = ConnectedComponents.mk y ↔
      x.val ∈ connectedComponentIn s y.val := by
  rw [← carrier_mk y]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨z, hz, hzx⟩
    have hzx' : z = x := Subtype.ext hzx
    simpa only [mem_ofPred_eq, hzx'] using hz

end ConnectedComponents

namespace TauCeti

variable {X : Type*} [TopologicalSpace X]

/-- The graph of actual components, with adjacency witnessed by a common
ambient closure point in the prescribed regular set. -/
def componentAdjacencyGraph (s R : Set X) : SimpleGraph (ConnectedComponents s) where
  Adj c d := c ≠ d ∧ ∃ x ∈ R, x ∈ closure c.carrier ∧ x ∈ closure d.carrier
  symm := ⟨fun _ _ ⟨hne, x, hx, hc, hd⟩ => ⟨hne.symm, x, hx, hd, hc⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ => hne rfl⟩

/-- Adjacency is exactly a regular common closure point between distinct components. -/
theorem componentAdjacencyGraph_adj {s R : Set X} {c d : ConnectedComponents s} :
    (componentAdjacencyGraph s R).Adj c d ↔
      c ≠ d ∧ ∃ x ∈ R, x ∈ closure c.carrier ∧ x ∈ closure d.carrier := Iff.rfl

/-- A continuous curve with only finitely many exceptional parameters gives
a finite adjacency walk between its endpoint components. Only values at
exceptional parameters need to lie in the regular set.
The curve may be constant and the endpoints may belong to the same component. -/
theorem componentAdjacencyGraph_reachable_of_finite_exceptions
    {s R : Set X} {f : ℝ → X} (T : Finset ℝ)
    {a b : ℝ} (hf : ContinuousOn f (Icc a b)) (hab : a ≤ b) (ha : f a ∈ s) (hb : f b ∈ s)
    (hR : ∀ t ∈ Icc a b, f t ∉ s → f t ∈ R)
    (hT : ∀ t ∈ Icc a b, f t ∉ s → t ∈ T) :
    (componentAdjacencyGraph s R).Reachable
      (ConnectedComponents.mk ⟨f a, ha⟩) (ConnectedComponents.mk ⟨f b, hb⟩) := by
  classical
  induction T using Finset.strongInductionOn generalizing a b with
  | _ T ih =>
    by_cases hall : ∀ t ∈ Icc a b, f t ∈ s
    · have hconn : IsPreconnected (f '' Icc a b) :=
        isPreconnected_Icc.image f hf
      have hsub : f '' Icc a b ⊆ s := by
        rintro _ ⟨t, ht, rfl⟩
        exact hall t ht
      have hmem : f b ∈ connectedComponentIn s (f a) :=
        hconn.subset_connectedComponentIn ⟨a, ⟨le_rfl, hab⟩, rfl⟩ hsub
          ⟨b, ⟨hab, le_rfl⟩, rfl⟩
      have heq := (ConnectedComponents.mk_eq_mk_iff_mem_connectedComponentIn
        (x := (⟨f b, hb⟩ : s)) (y := ⟨f a, ha⟩)).mpr hmem
      rw [heq]
    · push Not at hall
      obtain ⟨t, ht, hbad⟩ := hall
      have htT : t ∈ T := hT t ht hbad
      have hat : a < t := lt_of_le_of_ne ht.1 (by rintro rfl; exact hbad ha)
      have htb : t < b := lt_of_le_of_ne ht.2 (by rintro rfl; exact hbad hb)
      have hnot : t ∈ ((T.erase t : Finset ℝ) : Set ℝ)ᶜ := by simp
      obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (T.erase t).isClosed.isOpen_compl t hnot
      let δ := min r (min (t - a) (b - t)) / 2
      have hδ : 0 < δ := half_pos (lt_min hr (lt_min (sub_pos.mpr hat) (sub_pos.mpr htb)))
      have hδr : δ < r := by
        have := min_le_left r (min (t - a) (b - t))
        dsimp only [δ]
        linarith
      have hδa : δ < t - a := by
        have := (min_le_right r (min (t - a) (b - t))).trans (min_le_left _ _)
        dsimp only [δ]
        linarith
      have hδb : δ < b - t := by
        have := (min_le_right r (min (t - a) (b - t))).trans (min_le_right _ _)
        dsimp only [δ]
        linarith
      have _hleft : a ≤ t - δ := by linarith
      have _hright : t + δ ≤ b := by linarith
      have hlocal (u : ℝ) (hu : u ∈ Icc (t - δ) (t + δ)) (hut : u ≠ t) : f u ∈ s := by
        by_contra hus
        have huT : u ∈ T := hT u ⟨by linarith [hu.1], by linarith [hu.2]⟩ hus
        have huball : u ∈ Metric.ball t r := by
          rw [Metric.mem_ball, Real.dist_eq, abs_lt]
          constructor <;> linarith [hu.1, hu.2]
        exact hball huball (Finset.mem_erase.mpr ⟨hut, huT⟩)
      have hs : f (t - δ) ∈ s := hlocal _ ⟨le_rfl, by linarith⟩ (by linarith)
      have hu : f (t + δ) ∈ s := hlocal _ ⟨by linarith, le_rfl⟩ (by linarith)
      have hbefore := ih (T.erase t) (Finset.erase_ssubset htT)
        (hf.mono (fun u hu => ⟨hu.1, by linarith [hu.2]⟩)) (by linarith : a ≤ t - δ)
        ha hs (fun u hu => hR u ⟨hu.1, by linarith [hu.2]⟩)
        (fun u hu hus => Finset.mem_erase.mpr
          ⟨by linarith [hu.2], hT u ⟨hu.1, by linarith [hu.2]⟩ hus⟩)
      have hafter := ih (T.erase t) (Finset.erase_ssubset htT)
        (hf.mono (fun u hu => ⟨by linarith [hu.1], hu.2⟩)) (by linarith : t + δ ≤ b)
        hu hb (fun u hu => hR u ⟨by linarith [hu.1], hu.2⟩)
        (fun u hu hus => Finset.mem_erase.mpr
          ⟨by linarith [hu.1], hT u ⟨by linarith [hu.1], hu.2⟩ hus⟩)
      have hcl : f t ∈ closure (connectedComponentIn s (f (t - δ))) := by
        apply isPreconnected_Ico.mem_closure_connectedComponentIn_image
          (s := Ico (t - δ) t)
          (hf.mono (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩))
          ⟨le_rfl, by linarith⟩
          (by rw [closure_Ico (by linarith : t - δ ≠ t)]; exact ⟨by linarith, le_rfl⟩)
          (hf.continuousAt (Icc_mem_nhds hat htb)).continuousWithinAt
        exact fun u hu => hlocal u ⟨hu.1, by linarith [hu.2]⟩ hu.2.ne
      have hcr : f t ∈ closure (connectedComponentIn s (f (t + δ))) := by
        apply isPreconnected_Ioc.mem_closure_connectedComponentIn_image
          (s := Ioc t (t + δ))
          (hf.mono (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2]⟩))
          ⟨by linarith, le_rfl⟩
          (by rw [closure_Ioc (by linarith : t ≠ t + δ)]; exact ⟨le_rfl, by linarith⟩)
          (hf.continuousAt (Icc_mem_nhds hat htb)).continuousWithinAt
        exact fun u hu => hlocal u ⟨by linarith [hu.1], hu.2⟩ hu.1.ne'
      have hmiddle : (componentAdjacencyGraph s R).Reachable
          (ConnectedComponents.mk ⟨f (t - δ), hs⟩) (ConnectedComponents.mk ⟨f (t + δ), hu⟩) := by
        by_cases heq : ConnectedComponents.mk (⟨f (t - δ), hs⟩ : s) =
            ConnectedComponents.mk (⟨f (t + δ), hu⟩ : s)
        · rw [heq]
        · apply SimpleGraph.Adj.reachable
          apply componentAdjacencyGraph_adj.mpr
          exact ⟨heq, f t, hR t ht hbad,
            by rwa [ConnectedComponents.carrier_mk], by rwa [ConnectedComponents.carrier_mk]⟩
      exact hbefore.trans (hmiddle.trans hafter)

end TauCeti
