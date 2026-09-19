/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic

/-!
# Torsion in a subgroup of finite order, and maps reflecting torsion

A subgroup of an additive commutative group consists of torsion points as soon as it is finite:
its cardinality annihilates each of its elements, so a subgroup `H` is contained in the
`Nat.card H`-torsion subgroup. For finite `H` this says that a subgroup with `n` elements is
`n`-torsion; for infinite `H` one has `Nat.card H = 0` and the statement is the trivial
`H ≤ A[0]`.

A linear map `f` with a left inverse up to multiplication by a nonzerodivisor `a`, that is
`g ∘ f = a • id`, reflects torsion: if `f x` is torsion then so is `x`.

## Main results

* `AddSubgroup.le_torsionBy_natCard`: a subgroup `H` is contained in the `Nat.card H`-torsion
  subgroup.
* `Submodule.comap_torsion_le_of_comp_eq_smul`: a linear map with a left inverse up to a
  nonzerodivisor reflects torsion.
-/

public section

namespace AddSubgroup

/-- A subgroup `H` consists of `Nat.card H`-torsion points; for finite `H` this is the statement
that a subgroup with `n` elements is `n`-torsion, and for infinite `H` it is the trivial
`H ≤ A[0]`. -/
theorem le_torsionBy_natCard {A : Type*} [AddCommGroup A] {H : AddSubgroup A} :
    H ≤ A[(Nat.card H : ℤ)] := fun x hx ↦
  torsionBy.nsmul_iff.mpr <| by
    have : Nat.card H • (⟨x, hx⟩ : H) = 0 := card_nsmul_eq_zero'
    exact congrArg Subtype.val this

end AddSubgroup

open scoped nonZeroDivisors

namespace Submodule

variable {R M N : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- A linear map `f` for which some `g` satisfies `g ∘ f = a • id` with `a` a nonzerodivisor
reflects torsion: an element whose image is torsion is itself torsion. -/
theorem comap_torsion_le_of_comp_eq_smul {f : M →ₗ[R] N} {g : N →ₗ[R] M} {a : R} (ha : a ∈ R⁰)
    (hgf : ∀ x, g (f x) = a • x) : (torsion R N).comap f ≤ torsion R M := by
  intro x hx
  obtain ⟨b, hb⟩ := (mem_torsion_iff _).mp (mem_comap.mp hx)
  refine (mem_torsion_iff x).mpr ⟨b * ⟨a, ha⟩, ?_⟩
  rw [mul_smul, Submonoid.smul_def ⟨a, ha⟩, ← hgf, Submonoid.smul_def, ← map_smul,
    ← Submonoid.smul_def, hb, map_zero]

end Submodule
