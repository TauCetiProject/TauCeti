/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homeomorph.TransferInstance
public import TauCeti.GroupTheory.SpecificGroups.Heisenberg
public import TauCeti.Topology.Algebra.Group.LowerCentralSeries.Closed

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
generators of a free pro-`p` group. What makes the detection work is that, over any Hausdorff
topological ring, the closed lower central series of the Heisenberg group stops at `γ_2 = 1`.

## Main definitions

* `TauCeti.HeisenbergGroup.instTopologicalSpace`: the topology induced from `R × R × R`.
* `TauCeti.HeisenbergGroup.homeomorphProd`: the coordinate equivalence as a homeomorphism
  `HeisenbergGroup R ≃ₜ R × R × R`.

## Main results

* `TauCeti.HeisenbergGroup.continuous_x`, `continuous_y`, `continuous_z`: the coordinates are
  continuous.
* `TauCeti.HeisenbergGroup.continuous_iff`: a map into the Heisenberg group is continuous exactly
  when its three coordinates are.
* `TauCeti.HeisenbergGroup.continuous_map`: a continuous ring homomorphism induces a continuous
  homomorphism of Heisenberg groups.
* The instances `IsTopologicalGroup`, `CompactSpace`, `T2Space`, `DiscreteTopology` and
  `TotallyDisconnectedSpace` on `HeisenbergGroup R`, inherited from `R`.
* `TauCeti.HeisenbergGroup.isClosed_zAxis`: over a Hausdorff ring the `z`-axis is closed.
* `TauCeti.HeisenbergGroup.closedLowerCentralSeries_one_le_zAxis`,
  `TauCeti.HeisenbergGroup.closedLowerCentralSeries_two_eq_bot`: over a Hausdorff topological
  ring, `γ_1` of the closed lower central series lies in the `z`-axis and `γ_2` is trivial.
-/

public section

namespace TauCeti

namespace HeisenbergGroup

variable {R : Type*} [TopologicalSpace R]

/-- The topology on the Heisenberg group over a topological space `R`: the product topology of
`R × R × R`, pulled back along the coordinate equivalence. -/
instance instTopologicalSpace : TopologicalSpace (HeisenbergGroup R) :=
  equivProd.topologicalSpace

/-- The coordinate equivalence `HeisenbergGroup R ≃ R × R × R` is a homeomorphism. -/
def homeomorphProd : HeisenbergGroup R ≃ₜ R × R × R :=
  equivProd.homeomorph

@[simp]
theorem homeomorphProd_apply (a : HeisenbergGroup R) :
    homeomorphProd a = (a.x, a.y, a.z) :=
  equivProd_apply a

@[simp]
theorem homeomorphProd_symm_apply (a : R × R × R) :
    homeomorphProd.symm a = ⟨a.1, a.2.1, a.2.2⟩ :=
  equivProd_symm_apply a

/-- The `x` coordinate is continuous for the transported product topology. -/
@[continuity, fun_prop]
theorem continuous_x : Continuous (x : HeisenbergGroup R → R) :=
  (continuous_fst.comp homeomorphProd.continuous).congr fun _ ↦ by
    simp only [Function.comp_apply, homeomorphProd_apply]

/-- The `y` coordinate is continuous for the transported product topology. -/
@[continuity, fun_prop]
theorem continuous_y : Continuous (y : HeisenbergGroup R → R) :=
  (continuous_fst.comp (continuous_snd.comp homeomorphProd.continuous)).congr fun _ ↦ by
    simp only [Function.comp_apply, homeomorphProd_apply]

/-- The `z` coordinate is continuous for the transported product topology. -/
@[continuity, fun_prop]
theorem continuous_z : Continuous (z : HeisenbergGroup R → R) :=
  (continuous_snd.comp (continuous_snd.comp homeomorphProd.continuous)).congr fun _ ↦ by
    simp only [Function.comp_apply, homeomorphProd_apply]

/-- A map into the Heisenberg group is continuous exactly when its three coordinates are. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → HeisenbergGroup R} :
    Continuous f ↔
      Continuous (fun a ↦ (f a).x) ∧ Continuous (fun a ↦ (f a).y) ∧
        Continuous (fun a ↦ (f a).z) := by
  refine ⟨fun hf ↦ ⟨continuous_x.comp hf, continuous_y.comp hf, continuous_z.comp hf⟩, ?_⟩
  rintro ⟨hx, hy, hz⟩
  exact homeomorphProd.isInducing.continuous_iff.mpr
    ((hx.prodMk (hy.prodMk hz)).congr fun _ ↦ by
      simp only [Function.comp_apply, homeomorphProd_apply])

/-- The homomorphism of Heisenberg groups induced by a continuous ring homomorphism is
continuous. -/
theorem continuous_map {S : Type*} [Ring R] [Ring S] [TopologicalSpace S] (f : R →+* S)
    (hf : Continuous f) : Continuous (map f) :=
  continuous_iff.mpr <| by
    simp only [map_apply]
    exact ⟨hf.comp continuous_x, hf.comp continuous_y, hf.comp continuous_z⟩

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

section ClosedLowerCentralSeries

variable [Ring R] [IsTopologicalRing R] [T2Space R]

omit [IsTopologicalRing R] in
/-- The `z`-axis of the Heisenberg group over a ring with a Hausdorff topology is closed. -/
theorem isClosed_zAxis :
    IsClosed ((zAxis : Subgroup (HeisenbergGroup R)) : Set (HeisenbergGroup R)) := by
  have h : ((zAxis : Subgroup (HeisenbergGroup R)) : Set (HeisenbergGroup R)) =
      {a | a.x = 0} ∩ {a | a.y = 0} := by
    ext a
    simp
  rw [h]
  exact (isClosed_eq continuous_x continuous_const).inter
    (isClosed_eq continuous_y continuous_const)

/-- The first term `γ_1` of the closed lower central series of the Heisenberg group over a
Hausdorff topological ring lies in the `z`-axis. -/
theorem closedLowerCentralSeries_one_le_zAxis :
    closedLowerCentralSeries (HeisenbergGroup R) 1 ≤ zAxis := by
  rw [closedLowerCentralSeries_one]
  exact Subgroup.topologicalClosure_minimal _
    (Subgroup.commutator_le.mpr fun a _ b _ ↦ commutatorElement_mem_zAxis a b) isClosed_zAxis

/-- The closed lower central series of the Heisenberg group over a Hausdorff topological ring
stops at `γ_2 = 1`. -/
theorem closedLowerCentralSeries_two_eq_bot :
    closedLowerCentralSeries (HeisenbergGroup R) 2 = ⊥ := by
  rw [closedLowerCentralSeries_succ, eq_bot_iff]
  refine Subgroup.topologicalClosure_minimal _ (Subgroup.commutator_le.mpr fun a ha b _ ↦ ?_)
    (by simp)
  rw [commutatorElement_eq_one_of_mem_zAxis (closedLowerCentralSeries_one_le_zAxis ha)]
  exact one_mem _

end ClosedLowerCentralSeries

end HeisenbergGroup

end TauCeti
