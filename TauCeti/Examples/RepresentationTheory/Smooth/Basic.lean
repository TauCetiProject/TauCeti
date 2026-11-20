/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Checks for smooth representations and smooth vectors

These examples exercise `Representation.IsSmooth` and `Representation.smoothVectors` on the
additive group `ℤ_[p]` of `p`-adic integers, written multiplicatively as
`Multiplicative ℤ_[p]`, and on discrete groups.

* The trivial representation of any topological group is smooth.
* The left regular representation of `ℤ_[p]` on `ℤ[ℤ_[p]]` is not smooth: the stabilizer of a
  basis vector is trivial, and `{0}` is not open in `ℤ_[p]`. In fact its only smooth vector is
  `0`, since a nonzero finitely supported function can only be fixed by a finite subgroup.
* For `U = p ^ n ℤ_[p]` the permutation representation `ℤ[ℤ_[p] ⧸ U]` is smooth, and `U` fixes
  every vector.
* Every vector of a representation of a discrete group is smooth.
-/

public section

open Representation
open scoped MonoidAlgebra

namespace TauCeti.Examples.RepresentationTheory.Smooth

/-! ### The trivial representation and discrete groups -/

/-- The trivial representation of any topological group is smooth. -/
example {A G V : Type*} [Semiring A] [Group G] [TopologicalSpace G] [AddCommMonoid V]
    [Module A V] : IsSmooth (trivial A G V) :=
  inferInstance

/-- For a discrete group every vector is smooth. -/
example {A G V : Type*} [Semiring A] [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [AddCommMonoid V] [Module A V] (ρ : Representation A G V) : ρ.smoothVectors = ⊤ := by
  simp

/-! ### The left regular representation of `ℤ_[p]` -/

variable (p : ℕ) [Fact p.Prime]

/-- The left regular representation of `ℤ_[p]` on `ℤ[ℤ_[p]]` is not smooth. -/
theorem not_isSmooth_leftRegular_padicInt :
    ¬IsSmooth (leftRegular ℤ (Multiplicative ℤ_[p])) := by
  rw [leftRegular, isSmooth_ofMulAction_iff]
  exact fun h ↦ PadicInt.not_isOpen_singleton_one_multiplicative (by simpa using h 1)

/-- The only smooth vector of the left regular representation of `ℤ_[p]` on `ℤ[ℤ_[p]]` is `0`. -/
theorem smoothVectors_leftRegular_padicInt_eq_bot :
    (leftRegular ℤ (Multiplicative ℤ_[p])).smoothVectors = ⊥ :=
  smoothVectors_leftRegular_eq_bot PadicInt.not_isOpen_singleton_one_multiplicative

/-! ### Permutation representations on `ℤ_[p] ⧸ p ^ n ℤ_[p]` -/

/-- The permutation representation `ℤ[ℤ_[p] ⧸ p ^ n ℤ_[p]]` is smooth. -/
example (n : ℕ) :
    IsSmooth (ofMulAction ℤ (Multiplicative ℤ_[p])
      (Multiplicative ℤ_[p] ⧸ (TauCeti.padicIntLevel p n).toSubgroup)) :=
  inferInstance

/-- Every vector of `ℤ[ℤ_[p] ⧸ p ^ n ℤ_[p]]` is fixed by `p ^ n ℤ_[p]`: the group is commutative,
so `p ^ n ℤ_[p]` fixes every coset. -/
example (n : ℕ)
    (f : ℤ[Multiplicative ℤ_[p] ⧸ (TauCeti.padicIntLevel p n).toSubgroup])
    (u : Multiplicative ℤ_[p]) (hu : u ∈ (TauCeti.padicIntLevel p n).toSubgroup) :
    ofMulAction ℤ (Multiplicative ℤ_[p]) _ u f = f := by
  ext y
  simp [coeff_ofMulAction, TauCeti.smul_quotient_eq_self_of_mem (inv_mem hu)]

end TauCeti.Examples.RepresentationTheory.Smooth
