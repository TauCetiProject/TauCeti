/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Semisimple
public import TauCeti.RepresentationTheory.Character.Twist
import TauCeti.RepresentationTheory.AsAlgebraHom
import TauCeti.RepresentationTheory.Subrepresentation.Semisimple

/-!
# Semisimplicity under a linear character twist

A unit-valued character rescales each group operator without changing their linear span or
which subspaces they preserve. Consequently a twist preserves both semisimplicity and
nondegeneracy of the multiplication–trace pairing on the span. The tensor-product form applies
when twisting a representation while rescaling its Frobenius characteristic polynomials.

The trace-pairing assertion is the basis-free form of `New.IsTraceNondeg.twist` in
[lsernau/grh-lean](https://github.com/lsernau/grh-lean) (`72fead1`,
`grh/src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean`).
-/

public section

namespace Representation

variable {k G V : Type*} [Monoid G]

section CommSemiring

variable [CommSemiring k] [AddCommMonoid V] [Module k V]

/-- Twisting by a unit-valued character does not change the linear span of the operators. -/
@[simp] theorem span_range_charTwist (χ : G →* kˣ) (ρ : Representation k G V) :
    Submodule.span k (Set.range (charTwist χ ρ)) = Submodule.span k (Set.range ρ) := by
  rw [← toSubmodule_range_asAlgebraHom, ← toSubmodule_range_asAlgebraHom,
    asAlgebraHom_charTwist, AlgHom.range_comp,
    (AlgHom.range_eq_top _).mpr (MonoidAlgebra.charTwist χ).surjective, Algebra.map_top]

/-- Nondegeneracy of the trace pairing on the span of a representation, tested against the
spanning family of operators, is unchanged by a linear character twist. -/
theorem trace_nondegenerate_charTwist_iff (χ : G →* kˣ) (ρ : Representation k G V) :
    (∀ x ∈ Submodule.span k (Set.range (charTwist χ ρ)),
      (∀ g, LinearMap.trace k V (x * charTwist χ ρ g) = 0) → x = 0) ↔
    (∀ x ∈ Submodule.span k (Set.range ρ),
      (∀ g, LinearMap.trace k V (x * ρ g) = 0) → x = 0) := by
  simp only [span_range_charTwist, charTwist_apply, mul_smul_comm, map_smul, smul_eq_mul,
    Units.mul_right_eq_zero]

end CommSemiring

section Field

variable [Field k] [AddCommGroup V] [Module k V]

/-- Twisting by a linear character preserves and reflects semisimplicity. -/
@[simp] theorem isSemisimpleRepresentation_charTwist_iff (χ : G →* kˣ)
    (ρ : Representation k G V) :
    (charTwist χ ρ).IsSemisimpleRepresentation ↔ ρ.IsSemisimpleRepresentation :=
  (subrepresentationCharTwistOrderIso χ ρ).complementedLattice_iff

/-- The twist of a semisimple representation is semisimple. -/
instance isSemisimpleRepresentation_charTwist (χ : G →* kˣ) (ρ : Representation k G V)
    [ρ.IsSemisimpleRepresentation] : (charTwist χ ρ).IsSemisimpleRepresentation :=
  (isSemisimpleRepresentation_charTwist_iff χ ρ).mpr ‹_›

/-- Tensoring with a unit-valued character on the coefficient line preserves and reflects
semisimplicity. -/
@[simp] theorem isSemisimpleRepresentation_ofLinearCharacter_tprod_iff (χ : G →* kˣ)
    (ρ : Representation k G V) :
    ((ofLinearCharacter χ).tprod ρ).IsSemisimpleRepresentation ↔
      ρ.IsSemisimpleRepresentation := by
  let e := tprodEquivCharTwist χ ρ
  rw [← isSemisimpleRepresentation_charTwist_iff χ ρ]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact e.toIntertwiningMap.isSemisimpleRepresentation_of_surjective e.surjective
  · exact e.symm.toIntertwiningMap.isSemisimpleRepresentation_of_surjective e.symm.surjective

end Field

end Representation
