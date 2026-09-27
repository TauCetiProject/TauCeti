/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Basic
import TauCeti.Algebra.MonoidAlgebra.FaithfullyFlat
import TauCeti.Algebra.MonoidAlgebra.Finite
public import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra

/-!
# Central isogenies of diagonalizable groups

The morphism `D(N) → D(M)` induced by a homomorphism `p : M →* N` is a central
isogeny exactly when `p` is injective with finite cokernel, over a nonzero commutative
base ring. The sufficient direction also holds over the zero ring. Neither character
group needs to be finitely generated, and there is no smoothness or characteristic
restriction: this criterion includes inseparable isogenies.

The finiteness and faithful-flatness criteria for group-algebra maps supply the isogeny
conditions. Cocommutativity of the target coordinate algebra makes its kernel central.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12, especially Theorem 12.9.
-/

public section

namespace TauCeti.DiagonalizableGroup

universe u v

variable (R : Type u) [CommRing R]
variable {M N : Type v} [CommGroup M] [CommGroup N] (p : M →* N)

/-- An injective character homomorphism with finite cokernel induces a central isogeny
of diagonalizable groups over any commutative base ring. -/
theorem isCentralIsogeny_mapDomainBialgHom_of_injective_of_finite_quotient
    (hp : Function.Injective p) [Finite (N ⧸ p.range)] :
    CommHopfAlgCat.IsCentralIsogeny
      (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R p)) := by
  rw [CommHopfAlgCat.isCentralIsogeny_iff]
  refine ⟨?_, ?_, (HopfIdeal.isCentral_bot_iff_isCocomm.mpr inferInstance).mono bot_le⟩
  · exact MonoidAlgebra.mapDomainRingHom_finite_of_finite_quotient R p
  · exact MonoidAlgebra.faithfullyFlat_mapDomainRingHom_of_injective R p hp

/-- Over a nonzero commutative ring, a morphism of diagonalizable groups is a central
isogeny if and only if its character homomorphism is injective with finite cokernel. -/
@[simp]
theorem isCentralIsogeny_mapDomainBialgHom_iff [Nontrivial R] :
    CommHopfAlgCat.IsCentralIsogeny
        (CommHopfAlgCat.ofHom (MonoidAlgebra.mapDomainBialgHom R p)) ↔
      Function.Injective p ∧ Finite (N ⧸ p.range) := by
  constructor
  · intro hp
    exact ⟨(MonoidAlgebra.faithfullyFlat_mapDomainRingHom_iff R p).mp hp.faithfullyFlat,
      (MonoidAlgebra.mapDomainRingHom_finite_iff_finite_quotient R p).mp hp.finite⟩
  · rintro ⟨hp, hfinite⟩
    exact isCentralIsogeny_mapDomainBialgHom_of_injective_of_finite_quotient R p hp

end TauCeti.DiagonalizableGroup
