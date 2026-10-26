/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Constructions

/-!
# Products of infinitely many nontrivial spaces are perfect

A product of infinitely many nontrivial topological spaces has no isolated points: a
neighbourhood of a point in the product topology constrains only finitely many coordinates, so
changing a coordinate outside them moves the point without leaving the neighbourhood. No
separation axiom is needed. In particular Cantor space `ℕ → Bool` and Baire space `ℕ → ℕ` are
perfect.

## Main results

* `perfectSpace_pi`: a product of infinitely many nontrivial spaces is a perfect space.

## References

* The argument for Cantor space follows `accPt_univ_natBool` in
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Descriptive/PerfectAntichain.lean`; here it is stated for arbitrary infinite
  products of nontrivial spaces.
-/

public section

open Set Topology

universe u v

/-- **A product of infinitely many nontrivial spaces is perfect.** A neighbourhood of a point
constrains only finitely many coordinates; changing a coordinate outside them gives a different
point in the neighbourhood. -/
instance perfectSpace_pi {ι : Type u} {π : ι → Type v} [∀ i, TopologicalSpace (π i)]
    [Infinite ι] [∀ i, Nontrivial (π i)] : PerfectSpace (∀ i, π i) := by
  classical
  refine ⟨preperfect_iff_nhds.2 fun x _ U hU => ?_⟩
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, V, hV, hVU⟩ := hU
  obtain ⟨n, -, hn⟩ := infinite_univ.exists_notMem_finite hI
  obtain ⟨z, hz⟩ := exists_ne (x n)
  refine ⟨Function.update x n z, ⟨hVU fun i hi => ?_, trivial⟩, fun h => hz ?_⟩
  · rw [Function.update_of_ne fun h : i = n => hn (h ▸ hi)]
    exact mem_of_mem_nhds (hV i)
  · simpa using congrFun h n
