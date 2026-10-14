/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Finiteness for submodules and quotients

`Submodule.toAddSubgroup` is reducible and keeps the carrier set, so `p` and `p.toAddSubgroup`
have the same elements and the same `ℤ`-module structure. Instance search is nevertheless keyed
on the head symbol, so a `Module.Finite ℤ p` instance is never tried against the goal
`Module.Finite ℤ p.toAddSubgroup`. This file records that transfer once, for every `ℤ`-submodule,
rather than at each lattice presented to an API that reads additive subgroups.

For compatible actions of a semiring `A` and a ring `R`, an `R`-submodule `N` and its
quotient being finite over `A` implies that the ambient module is finite over `A`. The
quotient is formed over `R`; the scalar semiring `A` need not be a ring. This is the
scalar-restriction version of Mathlib's `Module.Finite.of_submodule_quotient`.

## Main declarations

* `Module.Finite.of_restrictScalars_submodule_quotient`: finiteness of a submodule and quotient
  over a compatible semiring implies finiteness of the ambient module.
* `TauCeti.instModuleFiniteToAddSubgroup`: a finitely generated `ℤ`-submodule stays finitely
  generated when read as an additive subgroup.
-/

public section

namespace TauCeti

/-- A finitely generated `ℤ`-submodule is still finitely generated when read as an additive
subgroup, the two being the same type. -/
instance instModuleFiniteToAddSubgroup {M : Type*} [AddCommGroup M] (p : Submodule ℤ M)
    [Module.Finite ℤ p] : Module.Finite ℤ p.toAddSubgroup :=
  inferInstanceAs (Module.Finite ℤ p)

end TauCeti

/-- If an `R`-submodule and its quotient are finite over a compatible scalar semiring `A`,
then so is the ambient module. The quotient is formed over the ring `R`, so `A` need not
be a ring or commutative. -/
theorem Module.Finite.of_restrictScalars_submodule_quotient
    {A R M : Type*} [Semiring A] [Ring R] [AddCommGroup M]
    [Module A M] [Module R M] [SMul A R] [IsScalarTower A R M]
    (N : Submodule R M) [Module.Finite A N] [Module.Finite A (M ⧸ N)] :
    Module.Finite A M := by
  have : Module.Finite A (N.restrictScalars A) :=
    Module.Finite.equiv ((N.restrictScalarsEquiv A).restrictScalars A).symm
  classical
  -- Lift a finite set of quotient generators; together with the finite kernel they span.
  obtain ⟨s, hs⟩ := Module.finite_def.mp
    (inferInstance : Module.Finite A (M ⧸ N))
  choose lift hlift using N.mkQ_surjective
  let P := Submodule.span A (lift '' (s : Set (M ⧸ N)))
  have hP : P.map (N.mkQ.restrictScalars A) = ⊤ := by
    rw [Submodule.map_span, ← Set.image_comp]
    simpa only [Function.comp_def, LinearMap.restrictScalars_apply, hlift,
      Set.image_id'] using hs
  have htop : P ⊔ N.restrictScalars A = ⊤ := by
    refine top_unique fun x _ ↦ ?_
    have hx : N.mkQ x ∈ P.map (N.mkQ.restrictScalars A) := by rw [hP]; trivial
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [LinearMap.restrictScalars_apply] at hyx
    -- The restricted kernel has the same carrier; quotient equality detects its differences.
    exact Submodule.mem_sup.mpr
      ⟨y, hy, x - y, (Submodule.Quotient.eq N).mp hyx.symm, add_sub_cancel _ _⟩
  refine ⟨?_⟩
  rw [← htop]
  exact (Submodule.fg_span (s.finite_toSet.image lift)).sup
    (Module.Finite.iff_fg.mp inferInstance)
