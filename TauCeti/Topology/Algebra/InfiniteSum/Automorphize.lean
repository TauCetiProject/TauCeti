/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Evaluating an automorphized function

`MulAction.automorphize f` sums `f` over the orbits of a group action: at the class of a point
`a` it is the orbit sum `∑' g, f (g • a)`. Similarly `QuotientGroup.automorphize f` sums `f` over
the orbits of a subgroup `Γ`. At the class of a point `g` it is the orbit sum `∑' γ, f (γ • g)`,
where `γ` ranges over the opposite subgroup `Γ.op` acting on `G` by right multiplication.
-/

public section

variable {M : Type*} [TopologicalSpace M] [AddCommMonoid M]

/-- The automorphization of `f`, evaluated at the orbit of `a`, is the sum of `f` over that
orbit. -/
@[to_additive /-- The automorphization of `f`, evaluated at the orbit of `a`, is the sum of `f`
over that orbit. -/]
theorem MulAction.automorphize_mk {G α : Type*} [Group G] [MulAction G α] (f : α → M) (a : α) :
    automorphize f (Quotient.mk (orbitRel G α) a) = ∑' g : G, f (g • a) :=
  rfl

variable {G : Type*} [Group G] {Γ : Subgroup G}

/-- The automorphization of `f`, evaluated at the class of `g`, is the sum of `f` over the orbit
of `g` under right multiplication by `Γ`. -/
@[to_additive /-- The automorphization of `f`, evaluated at the class of `g`, is the sum of `f`
over the orbit of `g` under right addition by `Γ`. -/]
theorem QuotientGroup.automorphize_mk (f : G → M) (g : G) :
    QuotientGroup.automorphize f (g : G ⧸ Γ) = ∑' γ : Γ.op, f (γ • g) :=
  rfl
