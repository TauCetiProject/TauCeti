/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.CharP.Two

/-!
# Incidence boundaries and cycle modules of Serre graphs

For any chosen set of darts, the signed incidence boundary sends a dart from `u` to `v` to
`δ_v - δ_u`. Its integral kernel is the lattice of finite integral cycles. The same construction
over `ZMod 2` gives the binary cycle space; its boundary sends an edge to the sum of its endpoints.
A loop has zero boundary over either ring, while parallel edges remain separate coordinates.

The edge coordinates are the actual chosen darts. In particular, an orientation chooses one dart
from each reversal pair, but the construction also works for an arbitrary subset of darts. These
modules are the input to spanning-forest cycle bases and to the comparison with graph path groups.

The incidence boundary commutes with graph morphisms and with enlarging the chosen dart set.
Consequently cycles push forward along these maps. An injective vertex map and a surjective
map on the chosen darts give equality of the image cycle modules; this includes graph
isomorphisms carrying one chosen dart set onto the other.

## References

* A. Hatcher, *Algebraic Topology*, §2.2 (cellular incidence boundaries).
* R. Diestel, *Graph Theory*, §1.9 (binary cycle spaces).
-/

public section

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph) (O : Set Γ.E)

/-- The signed incidence boundary of a finitely supported edge chain. A chosen dart is an edge
coordinate even when its reverse is chosen as well. -/
noncomputable def incidenceBoundary (R : Type*) [Ring R] :
    (O →₀ R) →ₗ[R] (Γ.V →₀ R) :=
  Finsupp.linearCombination R fun e => Finsupp.single (Γ.tgt e.1) 1 -
    Finsupp.single (Γ.src e.1) 1

/-- The integral incidence boundary of the chosen darts. -/
noncomputable abbrev integralCycleBoundary : (O →₀ ℤ) →ₗ[ℤ] (Γ.V →₀ ℤ) :=
  Γ.incidenceBoundary O ℤ

/-- Finite integral edge chains with zero incidence boundary. -/
noncomputable def cycleLattice : Submodule ℤ (O →₀ ℤ) :=
  (Γ.integralCycleBoundary O).ker

/-- The binary incidence boundary of the chosen darts. -/
noncomputable abbrev modTwoCycleBoundary : (O →₀ ZMod 2) →ₗ[ZMod 2] (Γ.V →₀ ZMod 2) :=
  Γ.incidenceBoundary O (ZMod 2)

/-- The binary cycle space, with actual darts as its edge coordinates. -/
noncomputable def modTwoCycleSpace : Submodule (ZMod 2) (O →₀ ZMod 2) :=
  (Γ.modTwoCycleBoundary O).ker

variable {Γ O}

@[simp] theorem incidenceBoundary_single (R : Type*) [Ring R] (e : O) (r : R) :
    Γ.incidenceBoundary O R (Finsupp.single e r) =
      r • (Finsupp.single (Γ.tgt e.1) 1 - Finsupp.single (Γ.src e.1) 1) := by
  simp [incidenceBoundary]

/-- A chain is an integral cycle exactly when its signed incidence boundary vanishes. -/
@[simp] theorem mem_cycleLattice_iff (c : O →₀ ℤ) :
    c ∈ Γ.cycleLattice O ↔ Γ.integralCycleBoundary O c = 0 :=
  LinearMap.mem_ker

/-- A binary chain is a cycle exactly when its incidence boundary vanishes. -/
@[simp] theorem mem_modTwoCycleSpace_iff (c : O →₀ ZMod 2) :
    c ∈ Γ.modTwoCycleSpace O ↔ Γ.modTwoCycleBoundary O c = 0 :=
  LinearMap.mem_ker

/-- The incidence column of a loop vanishes over any ring. -/
theorem incidenceBoundary_single_eq_zero_of_loop (R : Type*) [Ring R] (e : O)
    (h : Γ.src e.1 = Γ.tgt e.1) :
    Γ.incidenceBoundary O R (Finsupp.single e 1) = 0 := by
  rw [incidenceBoundary_single, one_smul, ← h, sub_self]

/-- Over a nontrivial ring, a single dart has zero incidence boundary exactly when it is a loop. -/
theorem incidenceBoundary_single_eq_zero_iff (R : Type*) [Ring R] [Nontrivial R]
    (e : O) :
    Γ.incidenceBoundary O R (Finsupp.single e 1) = 0 ↔
      Γ.src e.1 = Γ.tgt e.1 := by
  rw [incidenceBoundary_single, one_smul, sub_eq_zero]
  exact (Finsupp.single_left_inj (one_ne_zero : (1 : R) ≠ 0)).trans eq_comm

/-- An individual dart is an integral cycle exactly when it is a loop. -/
theorem single_mem_cycleLattice_iff (e : O) :
    Finsupp.single e (1 : ℤ) ∈ Γ.cycleLattice O ↔ Γ.src e.1 = Γ.tgt e.1 := by
  rw [mem_cycleLattice_iff]
  exact incidenceBoundary_single_eq_zero_iff ℤ e

/-- An individual dart is a binary cycle exactly when it is a loop. -/
theorem single_mem_modTwoCycleSpace_iff (e : O) :
    Finsupp.single e (1 : ZMod 2) ∈ Γ.modTwoCycleSpace O ↔ Γ.src e.1 = Γ.tgt e.1 := by
  rw [mem_modTwoCycleSpace_iff]
  exact incidenceBoundary_single_eq_zero_iff (ZMod 2) e

/-- Reversing a dart negates its signed incidence column. -/
theorem incidenceBoundary_rev (R : Type*) [Ring R] (e : Γ.E)
    (he : e ∈ O) (hre : Γ.rev e ∈ O) :
    Γ.incidenceBoundary O R (Finsupp.single ⟨Γ.rev e, hre⟩ 1) =
      -Γ.incidenceBoundary O R (Finsupp.single ⟨e, he⟩ 1) := by
  simp [Γ.tgt_rev, Γ.src_rev, neg_sub]

/-- In characteristic two, reversing a dart preserves its incidence column. -/
theorem incidenceBoundary_rev_of_charTwo (R : Type*) [Ring R] [CharP R 2]
    (e : Γ.E) (he : e ∈ O) (hre : Γ.rev e ∈ O) :
    Γ.incidenceBoundary O R (Finsupp.single ⟨Γ.rev e, hre⟩ 1) =
      Γ.incidenceBoundary O R (Finsupp.single ⟨e, he⟩ 1) := by
  rw [incidenceBoundary_rev R e he hre]
  ext v
  exact CharTwo.neg_eq _

/-- In characteristic two the direction of a dart does not change its binary incidence column. -/
theorem modTwoCycleBoundary_rev (e : Γ.E) (he : e ∈ O) (hre : Γ.rev e ∈ O) :
    Γ.modTwoCycleBoundary O (Finsupp.single ⟨Γ.rev e, hre⟩ 1) =
      Γ.modTwoCycleBoundary O (Finsupp.single ⟨e, he⟩ 1) :=
  incidenceBoundary_rev_of_charTwo (ZMod 2) e he hre

/-- Incidence boundaries commute with the pushforward of chains along a graph morphism. -/
theorem Hom.incidenceBoundary_mapDomain {Δ : SerreGraph} (f : Γ.Hom Δ)
    {O' : Set Δ.E} (hO : Set.MapsTo f.mapE O O') (R : Type*) [Ring R] (c : O →₀ R) :
    Δ.incidenceBoundary O' R
        (Finsupp.mapDomain (fun e : O ↦ ⟨f.mapE e.1, hO e.2⟩ : O → O') c) =
      Finsupp.mapDomain f.mapV (Γ.incidenceBoundary O R c) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd => simp only [Finsupp.mapDomain_add, map_add, hc, hd]
  | single e r => simp [Finsupp.mapDomain_sub, Finsupp.mapDomain_smul]

/-- A graph morphism carries cycles to cycles over any coefficient ring. -/
theorem Hom.map_ker_incidenceBoundary_le {Δ : SerreGraph} (f : Γ.Hom Δ)
    {O' : Set Δ.E} (hO : Set.MapsTo f.mapE O O') (R : Type*) [Ring R] :
    Submodule.map (Finsupp.lmapDomain R R
        (fun e : O ↦ ⟨f.mapE e.1, hO e.2⟩ : O → O')) (Γ.incidenceBoundary O R).ker ≤
      (Δ.incidenceBoundary O' R).ker := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hy
  rw [LinearMap.mem_ker, Finsupp.lmapDomain_apply,
    f.incidenceBoundary_mapDomain hO R, LinearMap.mem_ker.mp hc, Finsupp.mapDomain_zero]

/-- If the vertex map is injective and every chosen target dart has a preimage, every target
cycle is a pushforward. In particular this applies to graph isomorphisms carrying `O` onto `O'`. -/
theorem Hom.map_ker_incidenceBoundary_eq {Δ : SerreGraph} (f : Γ.Hom Δ)
    {O' : Set Δ.E} (hO : Set.MapsTo f.mapE O O') (R : Type*) [Ring R]
    (hV : Function.Injective f.mapV)
    (hE : Function.Surjective (fun e : O ↦ ⟨f.mapE e.1, hO e.2⟩ : O → O')) :
    Submodule.map (Finsupp.lmapDomain R R
        (fun e : O ↦ ⟨f.mapE e.1, hO e.2⟩ : O → O')) (Γ.incidenceBoundary O R).ker =
      (Δ.incidenceBoundary O' R).ker := by
  refine le_antisymm (f.map_ker_incidenceBoundary_le hO R) ?_
  intro c hc
  obtain ⟨b, rfl⟩ := Finsupp.mapDomain_surjective hE c
  refine Submodule.mem_map.mpr ⟨b, LinearMap.mem_ker.mpr ?_, rfl⟩
  apply Finsupp.mapDomain_injective hV
  rw [Finsupp.mapDomain_zero]
  exact (f.incidenceBoundary_mapDomain hO R b).symm.trans (LinearMap.mem_ker.mp hc)

/-- Integral cycles push forward along graph morphisms. -/
theorem Hom.map_cycleLattice_le {Δ : SerreGraph} (f : Γ.Hom Δ)
    {O' : Set Δ.E} (hO : Set.MapsTo f.mapE O O') :
    Submodule.map (Finsupp.lmapDomain ℤ ℤ
        (fun e : O ↦ ⟨f.mapE e.1, hO e.2⟩ : O → O')) (Γ.cycleLattice O) ≤
      Δ.cycleLattice O' :=
  f.map_ker_incidenceBoundary_le hO ℤ

/-- Binary cycles push forward along graph morphisms. -/
theorem Hom.map_modTwoCycleSpace_le {Δ : SerreGraph} (f : Γ.Hom Δ)
    {O' : Set Δ.E} (hO : Set.MapsTo f.mapE O O') :
    Submodule.map (Finsupp.lmapDomain (ZMod 2) (ZMod 2)
        (fun e : O ↦ ⟨f.mapE e.1, hO e.2⟩ : O → O')) (Γ.modTwoCycleSpace O) ≤
      Δ.modTwoCycleSpace O' :=
  f.map_ker_incidenceBoundary_le hO (ZMod 2)

/-- An injective vertex map and a surjective map on chosen darts give equality of the image
integral cycle lattice with the target lattice. -/
theorem Hom.map_cycleLattice_eq {Δ : SerreGraph} (f : Γ.Hom Δ)
    {O' : Set Δ.E} (hO : Set.MapsTo f.mapE O O') (hV : Function.Injective f.mapV)
    (hE : Function.Surjective (fun e : O ↦ ⟨f.mapE e.1, hO e.2⟩ : O → O')) :
    Submodule.map (Finsupp.lmapDomain ℤ ℤ
        (fun e : O ↦ ⟨f.mapE e.1, hO e.2⟩ : O → O')) (Γ.cycleLattice O) =
      Δ.cycleLattice O' :=
  f.map_ker_incidenceBoundary_eq hO ℤ hV hE

/-- An injective vertex map and a surjective map on chosen darts give equality of the image
binary cycle space with the target space. -/
theorem Hom.map_modTwoCycleSpace_eq {Δ : SerreGraph} (f : Γ.Hom Δ)
    {O' : Set Δ.E} (hO : Set.MapsTo f.mapE O O') (hV : Function.Injective f.mapV)
    (hE : Function.Surjective (fun e : O ↦ ⟨f.mapE e.1, hO e.2⟩ : O → O')) :
    Submodule.map (Finsupp.lmapDomain (ZMod 2) (ZMod 2)
        (fun e : O ↦ ⟨f.mapE e.1, hO e.2⟩ : O → O')) (Γ.modTwoCycleSpace O) =
      Δ.modTwoCycleSpace O' :=
  f.map_ker_incidenceBoundary_eq hO (ZMod 2) hV hE

/-- Enlarging the chosen dart set does not change the boundary of an existing chain. -/
theorem incidenceBoundary_mapDomain_inclusion {O' : Set Γ.E} (h : O ⊆ O')
    (R : Type*) [Ring R] (c : O →₀ R) :
    Γ.incidenceBoundary O' R (Finsupp.mapDomain (Set.inclusion h) c) =
      Γ.incidenceBoundary O R c := by
  have hO : Set.MapsTo (Hom.id Γ).mapE O O' := by
    intro e he
    simpa only [Hom.id_mapE, id_eq] using h he
  simpa only [Hom.id_mapE, Hom.id_mapV, id_eq, Finsupp.mapDomain_id] using
    (Hom.id Γ).incidenceBoundary_mapDomain hO R c

/-- Enlarging the dart set includes its integral cycle lattice in the larger lattice. -/
theorem map_cycleLattice_le_of_subset {O' : Set Γ.E} (h : O ⊆ O') :
    Submodule.map (Finsupp.lmapDomain ℤ ℤ (Set.inclusion h)) (Γ.cycleLattice O) ≤
      Γ.cycleLattice O' := by
  have hO : Set.MapsTo (Hom.id Γ).mapE O O' := by
    intro e he
    simpa only [Hom.id_mapE, id_eq] using h he
  simpa only [Hom.id_mapE, id_eq] using (Hom.id Γ).map_cycleLattice_le hO

/-- Enlarging the dart set includes its binary cycle space in the larger space. -/
theorem map_modTwoCycleSpace_le_of_subset {O' : Set Γ.E} (h : O ⊆ O') :
    Submodule.map (Finsupp.lmapDomain (ZMod 2) (ZMod 2) (Set.inclusion h))
        (Γ.modTwoCycleSpace O) ≤ Γ.modTwoCycleSpace O' := by
  have hO : Set.MapsTo (Hom.id Γ).mapE O O' := by
    intro e he
    simpa only [Hom.id_mapE, id_eq] using h he
  simpa only [Hom.id_mapE, id_eq] using (Hom.id Γ).map_modTwoCycleSpace_le hO

end SerreGraph
end TauCeti
