/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Reductive.CompleteReducibility
public import TauCeti.Algebra.Coalgebra.Comodule.Cohomology.Averaging

/-!
# Vanishing of algebraic cohomology for reductive groups in characteristic zero

For a reductive affine group of finite type over a field of characteristic zero, its
coordinate Hopf algebra admits a normalized invariant integral. Algebraic averaging then
annihilates the positive-degree cohomology of the Hochschild complex for every rational
module. The degree-two case supplies primitives for the cocycles of vector extensions,
and the degree-one case supplies primitives for differences of splittings.
-/

public section

namespace TauCeti.reductiveCommHopfAlgProperty

universe u

/-- Every positive-degree algebraic cohomology group of a reductive affine group in
characteristic zero vanishes, with arbitrary rational coefficients. -/
theorem isZero_cohomology_succ {k : Type u} [Field k] [CharZero k]
    {G : FiniteTypeCommHopfAlgCat.{u, u} k} (hG : reductiveCommHopfAlgProperty k G)
    (M : Type u) [AddCommGroup M] [Module k M] [Comodule k G M] (n : ℕ) :
    CategoryTheory.Limits.IsZero (Comodule.Cohomology.cohomology k G M (n + 1)) := by
  have h := (linearlyReductiveCommHopfAlgProperty_iff k G.obj).mp hG.linearlyReductive
  exact h.isZero_cohomology_succ M n

end TauCeti.reductiveCommHopfAlgProperty
