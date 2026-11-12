/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Perfect
public import Mathlib.Topology.Constructions
public import Mathlib.Topology.DerivedSet

/-!
# Perfect sets: homeomorphic images and products

A homeomorphism carries perfect sets exactly onto perfect sets (`Homeomorph.perfect_image`), so
statements about perfect sets can be transported along homeomorphisms of the ambient spaces.

A product of infinitely many nontrivial topological spaces has no isolated points: a
neighbourhood of a point in the product topology constrains only finitely many coordinates, so
changing a coordinate outside them moves the point without leaving the neighbourhood. No
separation axiom is needed. In particular Cantor space `ℕ → Bool` and Baire space `ℕ → ℕ` are
perfect.

## Main results

* `Homeomorph.perfect_image`: the image of a set under a homeomorphism is perfect exactly when
  the set is.
* `TauCeti.perfectSpace_pi`: a product of infinitely many nontrivial spaces is a perfect space.

## References

* The argument for Cantor space follows `accPt_univ_natBool` in
  `cameronfreer/infinitary-logic` at commit `518a366cba97b1ae8c4dc64a297a396939bc3e0b`,
  `InfinitaryLogic/Descriptive/PerfectAntichain.lean`; here it is stated for arbitrary infinite
  products of nontrivial spaces.
-/

public section

open Set Topology

universe u v

namespace Homeomorph

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

private theorem perfect_image_of_perfect (h : X ≃ₜ Y) {C : Set X} (hC : Perfect C) :
    Perfect (h '' C) :=
  ⟨h.isClosed_image.2 hC.closed, by
    rintro _ ⟨x, hx, rfl⟩
    simpa [Filter.map_principal] using
      AccPt.map (hC.acc x hx) h.continuous.continuousAt h.injective⟩

/-- The image of a set under a homeomorphism is perfect exactly when the set is perfect. -/
@[simp]
theorem perfect_image (h : X ≃ₜ Y) {C : Set X} : Perfect (h '' C) ↔ Perfect C := by
  refine ⟨fun hC => ?_, perfect_image_of_perfect h⟩
  simpa [Set.image_image] using perfect_image_of_perfect h.symm hC

end Homeomorph

namespace TauCeti

/-- **A product of infinitely many nontrivial spaces is perfect**, with no separation assumption on
the factors. In particular Cantor space `ℕ → Bool` and Baire space `ℕ → ℕ` are perfect. -/
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

end TauCeti
