/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Algebra.Group.Defs

/-!
# One-dimensional representations and their characters

A representation `ρ` of a group `G` on a one-dimensional vector space `V` over a field `k` acts by
scalars: every `ρ g` is multiplication by a unit `χ g` of `k`, and `g ↦ χ g` is a homomorphism
`G →* kˣ`, the **character of the line** `Representation.lineCharacter ρ h`
(`Representation.lineCharacter_smul`). If `G` and `k` are topological and every matrix
coefficient `g ↦ f (ρ g v)` is continuous, the character is continuous
(`Representation.continuous_lineCharacter`).

## Main definitions

* `Representation.lineCharacter ρ h`: the character `G →* kˣ` by which `G` acts on the
  one-dimensional space `V`.

## Main results

* `Representation.lineCharacter_smul`: `ρ g v = lineCharacter ρ h g • v`.
* `Representation.lineCharacter_eq_of_forall_smul`: the character is determined by this
  property.
* `Representation.continuous_lineCharacter`: continuous matrix coefficients give a continuous
  character.
-/

public section

namespace Representation

open Module

variable {k G V : Type*} [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The scalars `k` are the endomorphism algebra of a one-dimensional vector space. -/
noncomputable def endEquivOfFinrankEqOne (h : finrank k V = 1) : k ≃ₐ[k] Module.End k V :=
  haveI : FiniteDimensional k V := Module.finite_of_finrank_eq_succ h
  AlgEquiv.ofBijective (Algebra.ofId k (Module.End k V)) <|
    Module.Free.bijective_algebraMap_of_finrank_eq_one (by rw [Module.finrank_linearMap, h])

/-- A scalar `c` acts on a one-dimensional space as multiplication by `c`. -/
theorem endEquivOfFinrankEqOne_apply (h : finrank k V = 1) (c : k) (v : V) :
    endEquivOfFinrankEqOne h c v = c • v := by
  rw [endEquivOfFinrankEqOne]
  exact Module.algebraMap_end_apply k k V c v

/-- The **character of a one-dimensional representation**: every `ρ g` is multiplication by the
unit `lineCharacter ρ h g`. -/
noncomputable def lineCharacter (ρ : Representation k G V) (h : finrank k V = 1) : G →* kˣ :=
  (Units.map (endEquivOfFinrankEqOne h).symm.toMonoidHom).comp ρ.asGroupHom

/-- A group acts on a one-dimensional representation by its character. -/
theorem lineCharacter_smul (ρ : Representation k G V) (h : finrank k V = 1) (g : G) (v : V) :
    ρ g v = (ρ.lineCharacter h g : k) • v := by
  rw [← endEquivOfFinrankEqOne_apply h]
  simp [lineCharacter, asGroupHom_apply]

/-- The character of a one-dimensional representation is the only map `G → k` by which `G`
acts. -/
theorem lineCharacter_eq_of_forall_smul (ρ : Representation k G V) (h : finrank k V = 1)
    {χ : G → k} (hχ : ∀ g v, ρ g v = χ g • v) (g : G) : (ρ.lineCharacter h g : k) = χ g := by
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ h
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (h ▸ Nat.one_pos : 0 < finrank k V)
  have := (ρ.lineCharacter_smul h g v).symm.trans (hχ g v)
  rwa [← sub_eq_zero, ← sub_smul, smul_eq_zero, sub_eq_zero, or_iff_left hv] at this

/-- A one-dimensional representation whose matrix coefficients `g ↦ f (ρ g v)` are continuous has
a continuous character. -/
theorem continuous_lineCharacter [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace k]
    (ρ : Representation k G V) (h : finrank k V = 1)
    (hρ : ∀ (v : V) (f : Dual k V), Continuous fun g ↦ f (ρ g v)) :
    Continuous (ρ.lineCharacter h) := by
  have : FiniteDimensional k V := Module.finite_of_finrank_eq_succ h
  obtain ⟨v, hv⟩ := Module.finrank_pos_iff_exists_ne_zero.mp (h ▸ Nat.one_pos : 0 < finrank k V)
  obtain ⟨f, hf⟩ : ∃ f : Dual k V, f v = 1 := by
    obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero k hv
    exact ⟨(f v)⁻¹ • f, by simp [hf]⟩
  have hval : ∀ g, (ρ.lineCharacter h g : k) = f (ρ g v) := fun g ↦ by
    rw [lineCharacter_smul, map_smul, hf, smul_eq_mul, mul_one]
  have hc : Continuous fun g ↦ (ρ.lineCharacter h g : k) := by
    simpa only [hval] using hρ v f
  refine Units.continuous_iff.mpr ⟨hc, ?_⟩
  simpa only [Function.comp_def, ← Units.val_inv_eq_inv_val, ← map_inv] using
    hc.comp continuous_inv

end Representation
