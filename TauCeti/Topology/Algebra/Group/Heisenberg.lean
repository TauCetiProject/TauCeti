/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg

/-!
# The topology of the Heisenberg group

For a topological ring `R`, the Heisenberg group `HeisenbergGroup R` of triples `(x, y, z)` with
`(x, y, z) * (x', y', z') = (x + x', y + y', z + z' + x * y')` carries the product topology of
`R × R × R`, transported along the coordinate equivalence `HeisenbergGroup.equivProd`. The group
law and the inversion are polynomial in the coordinates, so this makes the Heisenberg group a
topological group. Compactness, Hausdorffness and total disconnectedness pass from `R` to the
Heisenberg group through the coordinate homeomorphism.

Over the `p`-adic integers this is a compact, totally disconnected group of nilpotency class two;
it is pro-`p` by `TauCeti.HeisenbergGroup.isProP_padicInt`, and it detects the commutators of two
generators of a free pro-`p` group.

## Main definitions

* `TauCeti.HeisenbergGroup.instTopologicalSpace`: the topology induced from `R × R × R`.
* `TauCeti.HeisenbergGroup.homeomorphProd`: the coordinate equivalence as a homeomorphism
  `HeisenbergGroup R ≃ₜ R × R × R`.

## Main results

* `TauCeti.HeisenbergGroup.continuous_x`, `continuous_y`, `continuous_z`: the coordinates are
  continuous.
* `TauCeti.HeisenbergGroup.continuous_iff`: a map into the Heisenberg group is continuous exactly
  when its three coordinates are.
* The instances `IsTopologicalGroup`, `CompactSpace`, `T2Space`, `DiscreteTopology` and
  `TotallyDisconnectedSpace` on `HeisenbergGroup R`, inherited from `R`.
-/

public section

namespace TauCeti

namespace HeisenbergGroup

variable {R : Type*} [TopologicalSpace R]

/-- The topology on the Heisenberg group over a topological space `R`: the product topology of
`R × R × R`, pulled back along the coordinate equivalence. -/
instance instTopologicalSpace : TopologicalSpace (HeisenbergGroup R) :=
  TopologicalSpace.induced equivProd inferInstance

/-- The coordinate equivalence `HeisenbergGroup R ≃ R × R × R` is a homeomorphism. -/
def homeomorphProd : HeisenbergGroup R ≃ₜ R × R × R :=
  equivProd.toHomeomorphOfIsInducing ⟨rfl⟩

@[continuity, fun_prop]
theorem continuous_x : Continuous (x : HeisenbergGroup R → R) :=
  (continuous_fst.comp homeomorphProd.continuous).congr fun _ ↦ by
    simp [homeomorphProd]

@[continuity, fun_prop]
theorem continuous_y : Continuous (y : HeisenbergGroup R → R) :=
  (continuous_fst.comp (continuous_snd.comp homeomorphProd.continuous)).congr fun _ ↦ by
    simp [homeomorphProd]

@[continuity, fun_prop]
theorem continuous_z : Continuous (z : HeisenbergGroup R → R) :=
  (continuous_snd.comp (continuous_snd.comp homeomorphProd.continuous)).congr fun _ ↦ by
    simp [homeomorphProd]

/-- A map into the Heisenberg group is continuous exactly when its three coordinates are. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → HeisenbergGroup R} :
    Continuous f ↔
      Continuous (fun a ↦ (f a).x) ∧ Continuous (fun a ↦ (f a).y) ∧
        Continuous (fun a ↦ (f a).z) := by
  refine ⟨fun hf ↦ ⟨continuous_x.comp hf, continuous_y.comp hf, continuous_z.comp hf⟩, ?_⟩
  rintro ⟨hx, hy, hz⟩
  exact homeomorphProd.isInducing.continuous_iff.mpr
    ((hx.prodMk (hy.prodMk hz)).congr fun _ ↦ by simp [homeomorphProd])

instance [CompactSpace R] : CompactSpace (HeisenbergGroup R) :=
  homeomorphProd.symm.compactSpace

instance [T2Space R] : T2Space (HeisenbergGroup R) :=
  homeomorphProd.symm.t2Space

instance [DiscreteTopology R] : DiscreteTopology (HeisenbergGroup R) :=
  homeomorphProd.symm.discreteTopology

instance [TotallyDisconnectedSpace R] : TotallyDisconnectedSpace (HeisenbergGroup R) :=
  homeomorphProd.symm.totallyDisconnectedSpace

/-- Over a topological ring the Heisenberg group is a topological group: its multiplication and
inversion are polynomial in the coordinates. -/
instance [Ring R] [IsTopologicalRing R] : IsTopologicalGroup (HeisenbergGroup R) where
  continuous_mul := continuous_iff.mpr ⟨by simp only [mul_x]; fun_prop,
    by simp only [mul_y]; fun_prop, by simp only [mul_z]; fun_prop⟩
  continuous_inv := continuous_iff.mpr ⟨by simp only [inv_x]; fun_prop,
    by simp only [inv_y]; fun_prop, by simp only [inv_z]; fun_prop⟩

end HeisenbergGroup

end TauCeti
