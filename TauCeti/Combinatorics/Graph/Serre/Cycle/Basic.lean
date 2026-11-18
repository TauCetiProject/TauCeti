/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Cycle.Forest
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

/-- The integral cycle lattice is the kernel of the integral incidence boundary. -/
theorem cycleLattice_def : Γ.cycleLattice O = (Γ.incidenceBoundary O ℤ).ker := (rfl)

/-- The binary cycle space is the kernel of incidence over `ZMod 2`. -/
theorem modTwoCycleSpace_def :
    Γ.modTwoCycleSpace O = (Γ.incidenceBoundary O (ZMod 2)).ker := (rfl)

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

/-- The incidence boundary vanishes identically when every chosen dart is a loop. -/
theorem incidenceBoundary_eq_zero (R : Type*) [Ring R] (h : ∀ e ∈ O, Γ.src e = Γ.tgt e) :
    Γ.incidenceBoundary O R = 0 := by
  apply Finsupp.lhom_ext
  intro e r
  simp [h e.1 e.2]

/-- Over a nontrivial ring, the incidence boundary vanishes identically exactly when every
chosen dart is a loop. Thus a single dart that is not a loop excludes zero incidence. -/
theorem incidenceBoundary_eq_zero_iff (R : Type*) [Ring R] [Nontrivial R] :
    Γ.incidenceBoundary O R = 0 ↔ ∀ e ∈ O, Γ.src e = Γ.tgt e :=
  ⟨fun h e he => (incidenceBoundary_single_eq_zero_iff R ⟨e, he⟩).mp (by simp [h]),
    incidenceBoundary_eq_zero R⟩

/-- The difference of two parallel darts, with the same source and the same target, is a
cycle over any ring. -/
theorem single_sub_single_mem_ker_incidenceBoundary (R : Type*) [Ring R] {e f : O}
    (hsrc : Γ.src f.1 = Γ.src e.1) (htgt : Γ.tgt f.1 = Γ.tgt e.1) :
    Finsupp.single f (1 : R) - Finsupp.single e 1 ∈ (Γ.incidenceBoundary O R).ker := by
  simp [hsrc, htgt]

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

section

variable {R : Type*} [Ring R]

/-- Taking integer coefficients into a ring commutes with the signed incidence boundary. -/
theorem incidenceBoundary_mapRange_intCast (Γ : SerreGraph) (O : Set Γ.E) (c : O →₀ ℤ) :
    Γ.incidenceBoundary O R (c.mapRange (Int.cast : ℤ → R) Int.cast_zero) =
      (Γ.incidenceBoundary O ℤ c).mapRange (Int.cast : ℤ → R) Int.cast_zero := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c d hc hd =>
    simp only [Finsupp.mapRange_add (f := (Int.cast : ℤ → R)) (fun x y =>
      Int.cast_add x y), map_add, hc, hd]
  | single e n =>
    ext v
    simp [incidenceBoundary_single, Finsupp.mapRange_single, Finsupp.single_apply,
      smul_sub, Int.cast_sub, Int.cast_ite]

/-- The chain obtained by taking the coefficients of an integral cycle into a ring
is again a cycle. -/
theorem mapRange_intCast_mem_ker_incidenceBoundary (Γ : SerreGraph) (O : Set Γ.E)
    (c : (Γ.incidenceBoundary O ℤ).ker) :
    c.val.mapRange (Int.cast : ℤ → R) Int.cast_zero ∈ (Γ.incidenceBoundary O R).ker := by
  rw [LinearMap.mem_ker, Γ.incidenceBoundary_mapRange_intCast, LinearMap.mem_ker.mp c.property]
  simp

end

/-- Incidence boundaries commute with the pushforward of chains along a graph morphism. -/
theorem Hom.incidenceBoundary_mapDomain {Δ : SerreGraph} (f : Γ.Hom Δ)
    {O' : Set Δ.E} (hO : Set.MapsTo f.mapE O O') (R : Type*) [Ring R] (c : O →₀ R) :
    Δ.incidenceBoundary O' R
        (Finsupp.mapDomain (fun e : O ↦ ⟨f.mapE e.1, hO e.2⟩ : O → O') c) =
      Finsupp.mapDomain f.mapV (Γ.incidenceBoundary O R c) := by
  classical
  let mapE : O → O' := fun e => ⟨f.mapE e.1, hO e.2⟩
  have hcol (e : O) :
      (Finsupp.lmapDomain R R f.mapV)
          (Finsupp.single (Γ.tgt e.1) 1 - Finsupp.single (Γ.src e.1) 1) =
        Finsupp.single (Δ.tgt (mapE e).1) 1 -
          Finsupp.single (Δ.src (mapE e).1) 1 := by
    simp [mapE, Finsupp.lmapDomain_apply, Finsupp.mapDomain_sub]
  simpa only [incidenceBoundary, LinearMap.comp_apply, Finsupp.lmapDomain_apply, mapE] using
    congrArg (fun g => g c)
      (Finsupp.lmapDomain_linearCombination R mapE
        (Finsupp.lmapDomain R R f.mapV) hcol)

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
  simp only [incidenceBoundary, Finsupp.linearCombination_mapDomain]
  rfl

section

variable {F : Set Γ.E} {R : Type*} [Ring R]

/-- The difference of two vertex unit chains is a boundary whenever the vertices are
connected in the support graph. No acyclicity hypothesis is needed. -/
theorem single_sub_single_mem_range_incidenceBoundary {a b : Γ.V}
    (h : (Γ.supportGraph F).Reachable a b) :
    Finsupp.single b (1 : R) - Finsupp.single a 1 ∈
      LinearMap.range (Γ.incidenceBoundary F R) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => simp
  | @cons a b c hab p ih =>
    have hedge : Finsupp.single b (1 : R) - Finsupp.single a 1 ∈
        LinearMap.range (Γ.incidenceBoundary F R) := by
      rcases (Γ.supportGraph_adj F a b).mp hab with ⟨-, h | h⟩
      · obtain ⟨e, he, rfl, rfl⟩ := h
        exact ⟨Finsupp.single ⟨e, he⟩ 1, by simp⟩
      · obtain ⟨e, he, rfl, rfl⟩ := h
        exact ⟨-Finsupp.single ⟨e, he⟩ 1, by simp [neg_sub]⟩
    convert (LinearMap.range (Γ.incidenceBoundary F R)).add_mem ih hedge using 1
    exact (sub_add_sub_cancel _ _ _).symm

/-- A boundary-zero chain supported on a dart set with injective boundary vanishes.
The chain may be written in any ambient dart set. -/
theorem eq_zero_of_incidenceBoundary_eq_zero
    (hinj : Function.Injective (Γ.incidenceBoundary F R)) (c : O →₀ R)
    (hc : Γ.incidenceBoundary O R c = 0) (hs : ∀ e ∈ c.support, e.val ∈ F) :
    c = 0 := by
  classical
  let b := Finsupp.comapDomain (Set.inclusion (Set.inter_subset_left : O ∩ F ⊆ O)) c
    (Set.inclusion_injective _).injOn
  have hb : Finsupp.mapDomain (Set.inclusion (Set.inter_subset_left : O ∩ F ⊆ O)) b = c := by
    apply Finsupp.mapDomain_comapDomain _ (Set.inclusion_injective _) c
    intro e he
    exact ⟨⟨e.1, e.2, hs e he⟩, rfl⟩
  have hboundary : Γ.incidenceBoundary F R
      (Finsupp.mapDomain (Set.inclusion (Set.inter_subset_right : O ∩ F ⊆ F)) b) = 0 := by
    rw [incidenceBoundary_mapDomain_inclusion, ← incidenceBoundary_mapDomain_inclusion
      (Set.inter_subset_left : O ∩ F ⊆ O), hb, hc]
  have hbzero : b = 0 :=
    Finsupp.mapDomain_injective (Set.inclusion_injective _)
      (by simpa using hinj (hboundary.trans (map_zero _).symm))
  rw [← hb, hbzero, Finsupp.mapDomain_zero]

/-- If the boundary is injective on a dart subset, chains in any ambient dart set are
determined by their boundaries and their coordinates outside that subset. -/
theorem eq_of_incidenceBoundary_eq_of_forall_notMem
    (hinj : Function.Injective (Γ.incidenceBoundary F R)) (c d : O →₀ R)
    (hboundary : Γ.incidenceBoundary O R c = Γ.incidenceBoundary O R d)
    (hchord : ∀ e : O, e.val ∉ F → c e = d e) : c = d := by
  apply sub_eq_zero.mp
  apply eq_zero_of_incidenceBoundary_eq_zero hinj (c - d)
  · simp [hboundary]
  · intro e he
    by_contra h
    have hzero : (c - d) e = 0 := by simp [hchord e h]
    exact (Finsupp.mem_support_iff.mp he) hzero

end

/-- Enlarging the chosen dart set carries boundary-zero chains to boundary-zero chains over
any coefficient ring. -/
theorem map_ker_incidenceBoundary_le_of_subset {O' : Set Γ.E} (h : O ⊆ O')
    (R : Type*) [Ring R] :
    Submodule.map (Finsupp.lmapDomain R R (Set.inclusion h))
        (Γ.incidenceBoundary O R).ker ≤ (Γ.incidenceBoundary O' R).ker := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hy
  rw [LinearMap.mem_ker, Finsupp.lmapDomain_apply, incidenceBoundary_mapDomain_inclusion]
  exact LinearMap.mem_ker.mp hc

/-- Enlarging the dart set includes its integral cycle lattice in the larger lattice. -/
theorem map_cycleLattice_le_of_subset {O' : Set Γ.E} (h : O ⊆ O') :
    Submodule.map (Finsupp.lmapDomain ℤ ℤ (Set.inclusion h)) (Γ.cycleLattice O) ≤
      Γ.cycleLattice O' :=
  map_ker_incidenceBoundary_le_of_subset h ℤ

/-- Enlarging the dart set includes its binary cycle space in the larger space. -/
theorem map_modTwoCycleSpace_le_of_subset {O' : Set Γ.E} (h : O ⊆ O') :
    Submodule.map (Finsupp.lmapDomain (ZMod 2) (ZMod 2) (Set.inclusion h))
        (Γ.modTwoCycleSpace O) ≤ Γ.modTwoCycleSpace O' :=
  map_ker_incidenceBoundary_le_of_subset h (ZMod 2)

end SerreGraph
end TauCeti
