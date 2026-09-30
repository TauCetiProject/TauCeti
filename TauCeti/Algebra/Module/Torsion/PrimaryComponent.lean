/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Submodule.Defs
public import Mathlib.GroupTheory.Torsion

/-!
# The `p`-power torsion of a module over an arbitrary ring

For a natural number `p` and a module `M` over an arbitrary, possibly noncommutative, semiring
`A`, the elements of `M` killed by some power of `p` form an `A`-submodule: multiplication by
`p ^ n` is additive, so it commutes with every scalar. As an additive submonoid it is Mathlib's
`p`-primary component `AddCommMonoid.primaryComponent M p`.

Mathlib's `Submodule.torsion'` requires a commutative base ring. Here the ring is typically a
group algebra `ℤ_p[G]` of a nonabelian group, whose modules — such as the `p`-completed units of a
Galois extension of `p`-adic fields — have a `p`-power torsion that must be compared as
`ℤ_p[G]`-modules (NSW (7.4.1)).

## Main definitions

* `TauCeti.pPowerTorsion`: the `A`-submodule of elements killed by a power of `p`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, proof of (7.4.1).
-/

public section

namespace TauCeti

variable (p : ℕ) (A : Type*) [Semiring A] (M : Type*) [AddCommMonoid M] [Module A M]

/-- The `p`-power torsion of an `A`-module `M`: the `A`-submodule of elements killed by some power
of `p`. Its underlying additive submonoid is the `p`-primary component of `M`. -/
def pPowerTorsion : Submodule A M :=
  { AddCommMonoid.primaryComponent M p with
    smul_mem' a x := fun ⟨k, hk⟩ ↦ ⟨k, by rw [smul_comm, hk, smul_zero]⟩ }

variable {p A M}

/-- An element lies in the `p`-power torsion exactly when some power of `p` kills it. -/
@[simp]
theorem mem_pPowerTorsion_iff {x : M} : x ∈ pPowerTorsion p A M ↔ ∃ k : ℕ, p ^ k • x = 0 :=
  .rfl

variable (p A M)

/-- The additive submonoid underlying the `p`-power torsion is the `p`-primary component. -/
@[simp]
theorem toAddSubmonoid_pPowerTorsion :
    (pPowerTorsion p A M).toAddSubmonoid = AddCommMonoid.primaryComponent M p :=
  AddSubmonoid.ext fun _ ↦ .rfl

end TauCeti
