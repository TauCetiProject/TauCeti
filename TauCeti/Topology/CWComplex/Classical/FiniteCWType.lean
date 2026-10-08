/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.CWComplex.Classical.Finite
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Spaces of finite CW type

A topological space has *finite CW type* (`TauCeti.FiniteCWType`) if it is homotopy equivalent to
a finite CW complex, that is, to a subspace `C` of a Hausdorff space carrying one of Mathlib's
classical `CWComplex` structures with finitely many cells. The model lives in the same universe
as the space, which is where singular homology compares the two.

Finite CW type is the finiteness hypothesis under which homotopy invariants are computed from
cells: it is inherited along homotopy equivalences and homeomorphisms, and holds for finite CW
complexes themselves. The discrete CW structure on a space makes every finite discrete space
a finite CW complex, so finite discrete spaces and contractible spaces, being homotopy equivalent
to a point, have finite CW type.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0.
-/

public section

open Topology Topology.RelCWComplex Set

universe w

namespace TauCeti

section Discrete

variable {X : Type w} [TopologicalSpace X] [DiscreteTopology X]

/-- In the discrete CW structure on a discrete space there are no cells of positive dimension. -/
instance isEmpty_cell_univ_succ (n : ℕ) :
    IsEmpty (cell (univ : Set X) (n + 1)) :=
  inferInstanceAs (IsEmpty PEmpty)

/-- The zero-cells of the discrete CW structure on a discrete space are its points. -/
theorem nat_card_cell_univ_zero :
    Nat.card (cell (univ : Set X) 0) = Nat.card X :=
  Nat.card_univ

/-- The discrete CW structure on a discrete space is finite-dimensional. -/
instance finiteDimensional_univ_of_discreteTopology : FiniteDimensional (univ : Set X) where
  eventually_isEmpty_cell := Filter.eventually_atTop.2 ⟨1, fun n hn ↦ by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hn
    infer_instance⟩

/-- The discrete CW structure on a finite discrete space is a finite CW complex. -/
instance finite_univ_of_discreteTopology [_root_.Finite X] :
    RelCWComplex.Finite (univ : Set X) where
  toFiniteDimensional := finiteDimensional_univ_of_discreteTopology
  finite_cell n := by
    cases n with
    | zero => exact inferInstanceAs (_root_.Finite (univ : Set X))
    | succ n => infer_instance

end Discrete

/-- A topological space has **finite CW type** if it is homotopy equivalent to a finite CW
complex: a subspace `C` of a Hausdorff space `Y` in the same universe, with a classical CW
structure having finitely many cells. -/
class FiniteCWType (X : Type w) [TopologicalSpace X] : Prop where
  /-- A finite CW complex homotopy equivalent to the space. -/
  exists_homotopyEquiv : ∃ (Y : Type w) (_ : TopologicalSpace Y) (_ : T2Space Y) (C : Set Y)
    (_ : CWComplex C) (_ : RelCWComplex.Finite C), Nonempty (ContinuousMap.HomotopyEquiv X C)

/-- A finite CW complex has finite CW type. -/
instance FiniteCWType.of_cwComplex {Y : Type w} [TopologicalSpace Y] [T2Space Y] (C : Set Y)
    [CWComplex C] [RelCWComplex.Finite C] : FiniteCWType C :=
  ⟨⟨Y, _, ‹_›, C, ‹_›, ‹_›, ⟨.refl C⟩⟩⟩

/-- A space homotopy equivalent to a space of finite CW type has finite CW type. -/
theorem _root_.ContinuousMap.HomotopyEquiv.finiteCWType {X Y : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] [h : FiniteCWType Y] (e : ContinuousMap.HomotopyEquiv X Y) :
    FiniteCWType X := by
  obtain ⟨Z, _, _, C, _, _, ⟨e'⟩⟩ := h.exists_homotopyEquiv
  exact ⟨⟨Z, _, ‹_›, C, ‹_›, ‹_›, ⟨e.trans e'⟩⟩⟩

/-- A space homeomorphic to a space of finite CW type has finite CW type. -/
theorem _root_.Homeomorph.finiteCWType {X Y : Type w} [TopologicalSpace X] [TopologicalSpace Y]
    [FiniteCWType Y] (e : X ≃ₜ Y) : FiniteCWType X :=
  e.toHomotopyEquiv.finiteCWType

/-- Two homotopy equivalent spaces either both have finite CW type or both do not. -/
theorem _root_.ContinuousMap.HomotopyEquiv.finiteCWType_iff {X Y : Type w} [TopologicalSpace X]
    [TopologicalSpace Y] (e : ContinuousMap.HomotopyEquiv X Y) :
    FiniteCWType X ↔ FiniteCWType Y :=
  ⟨fun _ ↦ e.symm.finiteCWType, fun _ ↦ e.finiteCWType⟩

/-- A finite discrete space has finite CW type: it is a finite CW complex with only zero-cells. -/
instance FiniteCWType.of_discreteTopology (X : Type w) [TopologicalSpace X] [DiscreteTopology X]
    [_root_.Finite X] : FiniteCWType X :=
  (Homeomorph.Set.univ X).symm.finiteCWType

/-- A contractible space has finite CW type: it is homotopy equivalent to a point, the discrete
CW complex with a single zero-cell. -/
instance FiniteCWType.of_contractibleSpace (X : Type w) [TopologicalSpace X]
    [ContractibleSpace X] : FiniteCWType X :=
  (ContractibleSpace.hequiv X (univ : Set PUnit.{w + 1})).some.finiteCWType

end TauCeti
