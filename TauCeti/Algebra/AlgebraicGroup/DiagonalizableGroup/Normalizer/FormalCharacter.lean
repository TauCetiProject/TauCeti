/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.WeylGroup
public import TauCeti.Algebra.Coalgebra.Comodule.MonoidAlgebra.Character

/-!
# Weyl invariance of formal characters

Let `G = Spec H` be an affine group scheme over a field `k` and let `D(X) → G` be a closed
diagonalizable subgroup, given by a surjective morphism `π : H →ₐc[k] k[X]` of coordinate Hopf
algebras. A finite-dimensional representation `V` of `G` restricts along `π` to a representation
of `D(X)`, whose formal character `∑ₓ dim Vₓ · x ∈ ℤ[X]` records its weight multiplicities
(`TauCeti.Comodule.formalCharacter`).

A rational point normalizing `D(X)` carries the weight space `Vₓ` isomorphically onto `V_{wx}`,
where `w` is the automorphism of `X` it induces. Consequently the formal character is invariant
under the Weyl group `BialgHom.weylGroup π hπ`, acting on `ℤ[X]` through its action on `X`. When
`D(X)` is a split maximal torus of a reductive group, this group is classically the Weyl group `W`
of the root datum, and the statement says that characters of rational representations are
`W`-invariant elements of `ℤ[X]`, as Weyl characters are.

Normalization is scheme-theoretic, so the statement holds for nonreduced `G` and over every
field, including finite fields.

## Main results

* `BialgHom.mapDomain_formalCharacter_of_mem_weylGroup`: the formal character of a
  finite-dimensional representation, restricted to `D(X)`, is fixed by every element of the
  Weyl group.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed. (2003), Part II, §§1.4 and 5.1.
* J. S. Milne, *Algebraic Groups* (2017), §21.1.
-/

public section

open TauCeti

namespace BialgHom

universe u v w x

variable {k : Type u} {H : Type v} {X : Type w} [Field k] [CommRing H] [HopfAlgebra k H]
  [CommGroup X]
variable (π : H →ₐc[k] MonoidAlgebra k X) (hπ : Function.Surjective π)
variable (V : Type x) [AddCommGroup V] [Module k V] [Comodule k H V] [FiniteDimensional k V]

/-- **The formal character of a representation is invariant under the Weyl group.** Restrict a
finite-dimensional representation `V` of `G` to the closed diagonalizable subgroup `D(X)`, by
corestricting its coaction along `π`. Then relabelling the weights of `V` by an element of the
Weyl group `BialgHom.weylGroup π hπ` leaves its formal character unchanged. -/
theorem mapDomain_formalCharacter_of_mem_weylGroup {w : MulAut X} (hw : w ∈ weylGroup π hπ) :
    letI : Comodule k (MonoidAlgebra k X) V := Comodule.Corestrict (M := V) π.toCoalgHom
    MonoidAlgebra.mapDomain w (Comodule.formalCharacter k X V) =
      Comodule.formalCharacter k X V := by
  let : Comodule k (MonoidAlgebra k X) V := Comodule.Corestrict (M := V) π.toCoalgHom
  refine MonoidAlgebra.coeff_injective (Finsupp.ext fun y ↦ ?_)
  obtain ⟨x, rfl⟩ := w.surjective y
  have hx := finrank_weightSpace_apply_of_mem_weylGroup π hπ (V := V) hw x
  rw [DiagonalizableGroup.weightSpace_eq_comoduleWeightSpace,
    DiagonalizableGroup.weightSpace_eq_comoduleWeightSpace] at hx
  rw [MonoidAlgebra.coeff_mapDomain, Finsupp.mapDomain_apply_of_injective w.injective,
    Comodule.formalCharacter_coeff, Comodule.formalCharacter_coeff, hx]

end BialgHom
