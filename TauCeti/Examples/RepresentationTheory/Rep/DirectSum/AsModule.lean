/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Rep.DirectSum.AsModule
public import TauCeti.RepresentationTheory.LinearCharacter.Basic
public import Mathlib.Basic.Complex.Basic

/-!
# Checks for the group-algebra module of a direct sum

These examples exercise `Representation.directSumAsModuleEquiv` on three small families.

* The empty family: both sides are the zero module, of dimension `0`.
* One trivial summand on `k²`: the vector `(1, 0)` corresponds to `(1, 0)` in both directions,
  and is not sent to `0`.
* The trivial and sign characters of `C₂ = ℤˣ` over `ℂ`: the vector `(2, 3)` corresponds to
  `(2, 3)`, and the generator `-1` sends it to `(2, -3)` on both sides. Swapping the two summands
  without reindexing the vector instead gives `(-2, 3)`.
-/

public section

open Representation DirectSum
open scoped MonoidAlgebra

namespace TauCeti.Examples.RepresentationTheory.DirectSumAsModule

/-! ### The empty family -/

/-- Both sides of the comparison for an empty family have dimension `0`. -/
example {k G : Type*} [Field k] [Monoid G] (V : Empty → Type*) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (ρ : ∀ i, Representation k G (V i)) :
    Module.finrank k (directSum ρ).asModule = 0 ∧
      Module.finrank k (Π₀ i, (ρ i).asModule) = 0 :=
  ⟨(directSum ρ).asModuleEquiv.finrank_eq.trans Module.finrank_zero_of_subsingleton,
    Module.finrank_zero_of_subsingleton⟩

/-! ### One trivial summand on `k²` -/

section Trivial

variable {k G : Type*} [Field k] [Monoid G]

/-- The single trivial summand on `k²`. -/
local notation "τ" => fun _ : Fin 1 ↦ (1 : Representation k G (Fin 2 → k))

/-- The vector `(1, 0)` of the single summand goes to the component `(1, 0)`. -/
example :
    directSumAsModuleEquiv τ
        ((directSum τ).asModuleEquiv.symm (lof k (Fin 1) (fun _ ↦ Fin 2 → k) 0 ![1, 0])) =
      DFinsupp.single 0 ((1 : Representation k G (Fin 2 → k)).asModuleEquiv.symm ![1, 0]) :=
  directSumAsModuleEquiv_lof _ 0 _

/-- The component `(1, 0)` goes back to the vector `(1, 0)` of the single summand. -/
example :
    (directSumAsModuleEquiv τ).symm
        (DFinsupp.single 0 ((1 : Representation k G (Fin 2 → k)).asModuleEquiv.symm ![1, 0])) =
      (directSum τ).asModuleEquiv.symm (lof k (Fin 1) (fun _ ↦ Fin 2 → k) 0 ![1, 0]) := by
  rw [directSumAsModuleEquiv_symm_single, LinearEquiv.apply_symm_apply]

/-- The comparison is not the zero map: the vector `(1, 0)` has a nonzero image. -/
example :
    directSumAsModuleEquiv τ
        ((directSum τ).asModuleEquiv.symm (lof k (Fin 1) (fun _ ↦ Fin 2 → k) 0 ![1, 0])) ≠ 0 := by
  rw [directSumAsModuleEquiv_lof, Ne, DFinsupp.single_eq_zero, LinearEquiv.map_eq_zero_iff]
  intro h
  simpa using congrFun h 0

end Trivial

/-! ### The trivial and sign characters of `C₂` over `ℂ` -/

section SignCharacter

/-- The sign character of `ℤˣ`, the cyclic group of order `2`, with values in `ℂˣ`. -/
noncomputable abbrev sign : ℤˣ →* ℂˣ :=
  Units.map (Int.castRingHom ℂ).toMonoidHom

/-- The trivial and the sign representations of `ℤˣ` on `ℂ`, in this order. -/
noncomputable abbrev trivialSign : Fin 2 → Representation ℂ ℤˣ ℂ :=
  ![ofLinearCharacter 1, ofLinearCharacter sign]

/-- The trivial and sign summands with their order swapped, without reindexing. -/
noncomputable abbrev signTrivial : Fin 2 → Representation ℂ ℤˣ ℂ :=
  fun i ↦ trivialSign (Equiv.swap 0 1 i)

/-- The vector `(2, 3)` of `ℂ ⊕ ℂ`. -/
noncomputable abbrev twoThree : ⨁ _ : Fin 2, ℂ :=
  lof ℂ (Fin 2) (fun _ ↦ ℂ) 0 2 + lof ℂ (Fin 2) (fun _ ↦ ℂ) 1 3

/-- The vector `(2, 3)` of the direct sum corresponds to the components `(2, 3)`. -/
example :
    directSumAsModuleEquiv trivialSign ((directSum trivialSign).asModuleEquiv.symm twoThree) =
      DFinsupp.single 0 ((trivialSign 0).asModuleEquiv.symm 2) +
        DFinsupp.single 1 ((trivialSign 1).asModuleEquiv.symm 3) := by
  rw [map_add, map_add, directSumAsModuleEquiv_lof, directSumAsModuleEquiv_lof]

/-- The generator `-1` sends `(2, 3)` to `(2, -3)` in the direct-sum representation. -/
example :
    directSum trivialSign (-1) twoThree =
      lof ℂ (Fin 2) (fun _ ↦ ℂ) 0 2 + lof ℂ (Fin 2) (fun _ ↦ ℂ) 1 (-3) := by
  simp [twoThree, DirectSum.lmap_lof, sign]

/-- The generator `-1` sends the components `(2, 3)` to `(2, -3)` in the direct sum of the
group-algebra modules. -/
example :
    MonoidAlgebra.of ℂ ℤˣ (-1) •
        (DFinsupp.single 0 ((trivialSign 0).asModuleEquiv.symm 2) +
          DFinsupp.single 1 ((trivialSign 1).asModuleEquiv.symm 3) :
            Π₀ i, (trivialSign i).asModule) =
      DFinsupp.single 0 ((trivialSign 0).asModuleEquiv.symm 2) +
        DFinsupp.single 1 ((trivialSign 1).asModuleEquiv.symm (-3)) := by
  rw [smul_add, ← DFinsupp.single_smul, ← DFinsupp.single_smul, ← asModuleEquiv_symm_map_rho,
    ← asModuleEquiv_symm_map_rho]
  simp [sign]

/-- With the summands swapped but the vector `(2, 3)` kept, the generator gives `(-2, 3)`. -/
example :
    directSum signTrivial (-1) twoThree =
      lof ℂ (Fin 2) (fun _ ↦ ℂ) 0 (-2) + lof ℂ (Fin 2) (fun _ ↦ ℂ) 1 3 := by
  simp [twoThree, signTrivial, DirectSum.lmap_lof, sign]

end SignCharacter

end TauCeti.Examples.RepresentationTheory.DirectSumAsModule
