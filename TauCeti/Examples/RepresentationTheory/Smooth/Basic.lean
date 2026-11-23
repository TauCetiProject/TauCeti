/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.NumberTheory.Padics.PadicIntegers
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.Group.Quotient
import TauCeti.GroupTheory.QuotientGroup.Basic

/-!
# Examples of smooth representations

For an open subgroup `U` of a topological group, the permutation representation on `A[G ⧸ U]` is
smooth and its basis vector at the base coset has stabilizer `U`. Every representation of a discrete
group is smooth, and so is every trivial representation. The left regular representation of the
nondiscrete group `ℚ₂`, written multiplicatively, has no nonzero smooth vector.

For the additive group `ℤ_[p]` of `p`-adic integers, written multiplicatively as
`Multiplicative ℤ_[p]`, the left regular representation on `ℤ[ℤ_[p]]` is not smooth and its only
smooth vector is `0`, while for `U = p ^ n ℤ_[p]` the permutation representation `ℤ[ℤ_[p] ⧸ U]` is
smooth and `U` fixes every vector.
-/

public section

open Representation

namespace TauCeti

variable {A G V : Type*} [CommRing A] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module A V]

example (U : OpenSubgroup G) : IsSmooth (ofMulAction A G (G ⧸ (U : Subgroup G))) :=
  inferInstance

example [Nontrivial A] (U : OpenSubgroup G) :
    (ofMulAction A G (G ⧸ (U : Subgroup G))).stabilizer
      (MonoidAlgebra.single (QuotientGroup.mk 1) 1) = U := by
  rw [stabilizer_ofMulAction_single _ one_ne_zero, MulAction.stabilizer_quotient]

example : IsSmooth (trivial A G V) := inferInstance

example [DiscreteTopology G] (ρ : Representation A G V) : ρ.smoothVectors = ⊤ := by simp

example : (leftRegular ℤ (Multiplicative ℚ_[2])).smoothVectors = ⊥ := by
  refine smoothVectors_leftRegular_eq_bot fun h ↦ ?_
  -- `Multiplicative ℚ_[2]` carries the topology of `ℚ_[2]` by definition, so `h` is
  -- discreteness of `ℚ_[2]` itself.
  have : DiscreteTopology ℚ_[2] := h
  exact (NormedField.nhdsNE_neBot (0 : ℚ_[2])).ne (discreteTopology_iff_nhds_ne.1 this 0)

/-! ### The left regular representation of `ℤ_[p]` -/

section PadicInt

open scoped MonoidAlgebra

variable (p : ℕ) [Fact p.Prime]

/-- The left regular representation of `ℤ_[p]` on `ℤ[ℤ_[p]]` is not smooth. -/
theorem not_isSmooth_leftRegular_padicInt :
    ¬IsSmooth (leftRegular ℤ (Multiplicative ℤ_[p])) := by
  rw [leftRegular, isSmooth_ofMulAction_iff]
  exact fun h ↦ PadicInt.not_isOpen_singleton_one_multiplicative (by simpa using h 1)

/-- The only smooth vector of the left regular representation of `ℤ_[p]` on `ℤ[ℤ_[p]]` is `0`. -/
theorem smoothVectors_leftRegular_padicInt_eq_bot :
    (leftRegular ℤ (Multiplicative ℤ_[p])).smoothVectors = ⊥ :=
  smoothVectors_leftRegular_eq_bot fun _ ↦
    PadicInt.not_isOpen_singleton_one_multiplicative (p := p) (isOpen_discrete _)

/-! ### Permutation representations on `ℤ_[p] ⧸ p ^ n ℤ_[p]` -/

/-- The permutation representation `ℤ[ℤ_[p] ⧸ p ^ n ℤ_[p]]` is smooth. -/
example (n : ℕ) :
    IsSmooth (ofMulAction ℤ (Multiplicative ℤ_[p])
      (Multiplicative ℤ_[p] ⧸ (padicIntLevel p n).toSubgroup)) :=
  inferInstance

/-- Every vector of `ℤ[ℤ_[p] ⧸ p ^ n ℤ_[p]]` is fixed by `p ^ n ℤ_[p]`: the group is commutative,
so `p ^ n ℤ_[p]` fixes every coset. -/
example (n : ℕ) (f : ℤ[Multiplicative ℤ_[p] ⧸ (padicIntLevel p n).toSubgroup])
    (u : Multiplicative ℤ_[p]) (hu : u ∈ (padicIntLevel p n).toSubgroup) :
    ofMulAction ℤ (Multiplicative ℤ_[p]) _ u f = f := by
  ext y
  simp [coeff_ofMulAction, smul_quotient_eq_self_of_mem (inv_mem hu)]

end PadicInt

end TauCeti
