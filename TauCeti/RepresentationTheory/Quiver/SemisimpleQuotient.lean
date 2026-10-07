/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.SimpleModule.Basic
public import TauCeti.RepresentationTheory.Quiver.Radical
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.TrivialCoeff
public import TauCeti.RingTheory.Semisimple.BasicAlgebra

/-!
# The semisimple quotient of a path algebra

Killing the arrows of a quiver leaves its vertices. This file makes that precise at the level of
algebras: reading off the coordinates of an element of `pathAlgebra k Q` on the trivial paths is an
algebra homomorphism `TauCeti.PathAlgebra.trivialCoeff` onto the product algebra `Q → k`, and its
kernel is exactly the arrow ideal. So the arrow ideal is the kernel of a map onto a product of
copies of the base semiring. Over a commutative ring this induces the equivalence

`pathAlgebra k Q ⧸ arrowIdeal k Q ≃ₐ[k] (Q → k)`.

Multiplicativity is the one point that needs an argument, and it is the length filtration again:
concatenation adds lengths, so a product of paths is trivial only when both factors are, and the
coordinate of `f * g` on the trivial path at `v` is the product of the coordinates of `f` and of
`g` there.

For a **finite acyclic** quiver over a field the arrow ideal is the Jacobson radical
(`TauCeti.jacobson_pathAlgebra_eq_arrowIdeal`), so the displayed equivalence becomes

`pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q) ≃ₐ[k] (Q → k)`,

which is the Wedderburn decomposition of the semisimple quotient: one block for each vertex, and
every block is the base field itself. In particular the semisimple quotient is commutative and
reduced -- the path algebra of a finite acyclic quiver is a **basic** algebra, with every matrix
block of size one -- and its dimension is the number of vertices.

## Main definitions

* `TauCeti.PathAlgebra.trivialCoeff`: the algebra homomorphism `pathAlgebra k Q →ₐ[k] (Q → k)`
  reading off the coordinates on the trivial paths.
* `TauCeti.PathAlgebra.quotientArrowIdealAlgEquiv`: the induced equivalence
  `pathAlgebra k Q ⧸ arrowIdeal k Q ≃ₐ[k] (Q → k)`.
* `TauCeti.PathAlgebra.quotientJacobsonAlgEquiv`: the same equivalence for a finite acyclic quiver
  over a field, stated for the Jacobson radical.

## Main results

* `TauCeti.PathAlgebra.trivialCoeff_surjective` and `TauCeti.PathAlgebra.ker_trivialCoeff`: the
  trivial-coefficient map is onto `Q → k` with kernel the arrow ideal.
* `TauCeti.PathAlgebra.isSemisimpleRing_quotient_jacobson`,
  `TauCeti.PathAlgebra.isReduced_quotient_jacobson` and `TauCeti.PathAlgebra.isBasic`: the quotient
  by the radical is semisimple and reduced, that is, **the path algebra of a finite acyclic quiver
  is a basic algebra**.
* `TauCeti.PathAlgebra.finrank_quotient_jacobson`: the semisimple quotient has dimension the number
  of vertices.

## Implementation notes

The trivial-coefficient homomorphism and its characteristic formulas are defined in
`TauCeti.RepresentationTheory.Quiver.PathAlgebra.TrivialCoeff`; this file identifies its kernel
and constructs the induced quotient equivalences. The map needs no acyclicity and no field:
it is stated for a commutative base semiring and a quiver with finitely many vertices, which may
have infinitely many paths. Acyclicity enters only to identify the arrow ideal with the Jacobson
radical, which is imported.

## References

* I. Assem, D. Simson, A. Skowronski, *Elements of the Representation Theory of Associative
  Algebras I*, CUP (2006), Chapters II and III.
-/

public section

universe u v w

namespace TauCeti

namespace PathAlgebra

/-! ### The kernel of the trivial-coefficient homomorphism -/

section TrivialCoeff

variable (k : Type w) (Q : Type u) [CommSemiring k] [Quiver.{v} Q] [Finite Q]

/-- **The kernel of the trivial-coefficient homomorphism is the arrow ideal**: an element has all
its trivial coordinates zero exactly when it is supported on the paths of positive length. -/
theorem ker_trivialCoeff : RingHom.ker (trivialCoeff k Q) = arrowIdeal k Q := by
  ext f
  rw [RingHom.mem_ker, mem_arrowIdeal_iff_repr_nil, funext_iff]
  simp only [trivialCoeff_apply, Pi.zero_apply]

end TrivialCoeff

/-! ### The quotient by the arrow ideal -/

section Quotient

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q] [Finite Q]

/-- **Killing the arrows leaves the vertices**: the quotient of the path algebra by the arrow ideal
is the product of one copy of the base ring for each vertex. -/
noncomputable def quotientArrowIdealAlgEquiv :
    (pathAlgebra k Q ⧸ arrowIdeal k Q) ≃ₐ[k] (Q → k) :=
  (Ideal.quotientEquivAlgOfEq k (ker_trivialCoeff k Q).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (trivialCoeff_surjective k Q))

/-- The equivalence out of the quotient by the arrow ideal is the trivial-coefficient
homomorphism. -/
@[simp]
theorem quotientArrowIdealAlgEquiv_mk (f : pathAlgebra k Q) :
    quotientArrowIdealAlgEquiv k Q (Ideal.Quotient.mk (arrowIdeal k Q) f) =
      trivialCoeff k Q f := by
  rw [quotientArrowIdealAlgEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    Ideal.quotientKerAlgEquivOfSurjective_mk]

end Quotient

/-! ### Trivial coefficients modulo relations -/

section Relations

variable {k : Type w} {Q : Type u} [CommRing k] [Quiver.{v} Q] [Finite Q]
variable {I : Ideal (pathAlgebra k Q)} [I.IsTwoSided]

/-- The trivial-coefficient map descends through any ideal of relations contained
in the arrow ideal. -/
noncomputable def quotientTrivialCoeff (hI : I ≤ arrowIdeal k Q) :
    (pathAlgebra k Q ⧸ I) →ₐ[k] (Q → k) :=
  Ideal.Quotient.liftₐ I (trivialCoeff k Q) fun _ ha =>
    RingHom.mem_ker.1 ((ker_trivialCoeff k Q).symm ▸ hI ha)

/-- Trivial coefficients are unchanged by passage to the quotient by relations. -/
@[simp]
theorem quotientTrivialCoeff_mk (hI : I ≤ arrowIdeal k Q) (a : pathAlgebra k Q) :
    quotientTrivialCoeff hI (Ideal.Quotient.mk I a) = trivialCoeff k Q a :=
  (rfl)

/-- Every family of vertex coordinates occurs in the quotient by relations. -/
theorem quotientTrivialCoeff_surjective (hI : I ≤ arrowIdeal k Q) :
    Function.Surjective (quotientTrivialCoeff hI) := by
  exact Ideal.Quotient.lift_surjective_of_surjective _ _ (trivialCoeff_surjective k Q)

/-- The kernel of the descended trivial-coefficient map is the image of the arrow ideal. -/
theorem ker_quotientTrivialCoeff (hI : I ≤ arrowIdeal k Q) :
    RingHom.ker (quotientTrivialCoeff hI) = (arrowIdeal k Q).map (Ideal.Quotient.mk I) := by
  -- `liftₐ` and `lift` have the same underlying ring homomorphism.
  exact (Ideal.ker_quotient_lift (trivialCoeff k Q).toRingHom
    (hI.trans_eq (ker_trivialCoeff k Q).symm)).trans
      (congrArg (Ideal.map (Ideal.Quotient.mk I)) (ker_trivialCoeff k Q))

end Relations

/-! ### The semisimple quotient -/

section Jacobson

variable (k : Type w) (Q : Type u) [Field k] [Quiver.{v} Q] [Finite Q]

/-- **The semisimple quotient of the path algebra of a finite acyclic quiver is a product of copies
of the base field, one for each vertex.** This is its Wedderburn decomposition: every block is the
base field, so every block is one-dimensional, matching the vertex simple modules. -/
noncomputable def quotientJacobsonAlgEquiv (h : Quiver.IsAcyclic Q) :
    (pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q)) ≃ₐ[k] (Q → k) :=
  (Ideal.quotientEquivAlgOfEq k
    (jacobson_pathAlgebra_eq_arrowIdeal k Q (IsSemisimpleRing.jacobson_eq_bot k) h)).trans
    (quotientArrowIdealAlgEquiv k Q)

/-- The equivalence out of the semisimple quotient is the trivial-coefficient homomorphism. -/
@[simp]
theorem quotientJacobsonAlgEquiv_mk (h : Quiver.IsAcyclic Q) (f : pathAlgebra k Q) :
    quotientJacobsonAlgEquiv k Q h (Ideal.Quotient.mk (Ring.jacobson (pathAlgebra k Q)) f) =
      trivialCoeff k Q f := by
  rw [quotientJacobsonAlgEquiv, AlgEquiv.trans_apply, Ideal.quotientEquivAlgOfEq_mk,
    quotientArrowIdealAlgEquiv_mk]

/-- The semisimple quotient of the path algebra of a finite acyclic quiver is indeed semisimple:
a finite product of fields is a semisimple ring. -/
theorem isSemisimpleRing_quotient_jacobson (h : Quiver.IsAcyclic Q) :
    IsSemisimpleRing (pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q)) :=
  (quotientJacobsonAlgEquiv k Q h).toRingEquiv.symm.isSemisimpleRing

/-- The semisimple quotient of the path algebra of a finite acyclic quiver is reduced: no Wedderburn
block of it is a matrix algebra of size greater than one. -/
theorem isReduced_quotient_jacobson (h : Quiver.IsAcyclic Q) :
    IsReduced (pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q)) :=
  isReduced_of_injective (quotientJacobsonAlgEquiv k Q h).toRingEquiv
    (quotientJacobsonAlgEquiv k Q h).toRingEquiv.injective

/-- **The path algebra of a finite acyclic quiver is a basic algebra.**  This is the previous two
results read through `TauCeti.IsBasic`: by `TauCeti.isBasic_iff_pi_divisionRing` the quotient by the
radical is then a product of division rings -- here, one copy of `k` for each vertex -- so the
vertices index the simple modules and the indecomposable projectives without repetition. -/
theorem isBasic (h : Quiver.IsAcyclic Q) : IsBasic (pathAlgebra k Q) :=
  (isBasic_def _).mpr
    ⟨isSemisimpleRing_quotient_jacobson k Q h, isReduced_quotient_jacobson k Q h⟩

/-- The semisimple quotient of the path algebra of a finite acyclic quiver is commutative. -/
theorem mul_comm_quotient_jacobson (h : Quiver.IsAcyclic Q)
    (x y : pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q)) :
    x * y = y * x :=
  (quotientJacobsonAlgEquiv k Q h).injective (by
    rw [map_mul, map_mul, mul_comm])

/-- The semisimple quotient of the path algebra of a finite acyclic quiver has dimension the number
of vertices: one for each vertex simple module. -/
theorem finrank_quotient_jacobson (h : Quiver.IsAcyclic Q) :
    Module.finrank k (pathAlgebra k Q ⧸ Ring.jacobson (pathAlgebra k Q)) = Nat.card Q := by
  let := Fintype.ofFinite Q
  rw [(quotientJacobsonAlgEquiv k Q h).toLinearEquiv.finrank_eq,
    Module.finrank_fintype_fun_eq_card, Nat.card_eq_fintype_card]

end Jacobson

end PathAlgebra

end TauCeti
