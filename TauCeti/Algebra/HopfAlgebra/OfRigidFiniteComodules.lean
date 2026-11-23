/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Finite.ScalarExtension.EndOfPoint
public import TauCeti.Algebra.Coalgebra.Subcomodule.PointsAction
public import TauCeti.Algebra.HopfAlgebra.OfBijectiveEndOfPoint

/-!
# Antipodes from rigidity of finite comodules

Let `B` be a commutative bialgebra over a commutative semiring `R`, projective as an `R`-module
(for instance, any commutative bialgebra over a field). If every finitely generated `B`-comodule
has a left dual in the monoidal category `FGComoduleCat R B`, then `B` has an antipode, so it is a
Hopf algebra (`TauCeti.HopfAlgebra.ofLeftRigid`). This is the step of neutral Tannakian
reconstruction that produces the inverse of the reconstructed monoid scheme from the duals of
the category, before tensor endomorphisms are identified with tensor automorphisms.

Every point acts bijectively on the scalar extension of a finite comodule with a left dual
(`TauCeti.FGComoduleCat.bijective_endOfPoint_of_hasLeftDual`). The regular comodule `B` is the
directed union of its finite subcomodules. When `B` is projective, so that finite subcomodules
cover every element, and the value algebra is flat, bijectivity passes from finite subcomodules
to the whole comodule (`TauCeti.Comodule.bijective_endOfPoint_of_forall_finite`). Applied to the
universal point `AlgHom.id R B`, this makes the universal point action on `B` bijective, and
`TauCeti.HopfAlgebra.ofBijective` turns its inverse into an antipode.

## Main declarations

* `TauCeti.HopfAlgebra.bijective_endOfPoint_id_of_leftRigid`: the universal point acts
  bijectively on the regular comodule of a left-rigid projective commutative bialgebra.
* `TauCeti.HopfAlgebra.ofLeftRigid`: the resulting Hopf algebra structure.
* `TauCeti.HopfAlgebra.exists_antipode_of_rigid_finite_comodules`: the two antipode identities.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, in *Hodge cycles, motives, and Shimura
  varieties*, Lecture Notes in Math. 900 (1982), Proposition 2.16 and the proof of
  Theorem 2.11, pp. 125–131.
* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory

namespace TauCeti.HopfAlgebra

universe u

variable (R : Type u) [CommSemiring R] (B : Type u) [CommSemiring B] [Bialgebra R B]
  [Module.Projective R B] [LeftRigidCategory (FGComoduleCat.{u, u, u} R B)]

/-- If every finite comodule over a projective commutative bialgebra `B` has a left dual, the
universal point `AlgHom.id R B` acts bijectively on the regular comodule `B`. -/
theorem bijective_endOfPoint_id_of_leftRigid :
    Function.Bijective (Comodule.endOfPoint B (AlgHom.id R B)) :=
  Comodule.bijective_endOfPoint_of_forall_finite _ fun N hN ↦
    FGComoduleCat.bijective_endOfPoint_of_hasLeftDual
      (⟨ComoduleCat.of R B N, hN⟩ : FGComoduleCat.{u, u, u} R B) (AlgHom.id R B)

/-- A projective commutative bialgebra whose finite comodules have left duals is a Hopf algebra.
Its antipode is `TauCeti.HopfAlgebra.antipodeOfBijective`, the counit evaluation of the inverse
universal point action. This is not an instance, since `B` may already carry an antipode. -/
-- Exposed so that, once installed with `letI`, its bialgebra structure is recognised as the given
-- one by instance synthesis.
@[expose, instance_reducible]
noncomputable def ofLeftRigid : HopfAlgebra R B :=
  ofBijective (bijective_endOfPoint_id_of_leftRigid R B)

/-- The antipode of `TauCeti.HopfAlgebra.ofLeftRigid` is
`TauCeti.HopfAlgebra.antipodeOfBijective`. -/
@[simp]
theorem antipode_ofLeftRigid :
    letI := ofLeftRigid R B
    HopfAlgebra.antipode R (A := B) =
      antipodeOfBijective (bijective_endOfPoint_id_of_leftRigid R B) :=
  rfl

/-- A projective commutative bialgebra (for instance, a commutative bialgebra over a field) whose
finite comodules have left duals, in particular one whose category of finite comodules is rigid,
has an antipode satisfying both convolution identities. -/
theorem exists_antipode_of_rigid_finite_comodules :
    ∃ S : B →ₗ[R] B,
      LinearMap.mul' R B ∘ₗ S.rTensor B ∘ₗ Coalgebra.comul =
        Algebra.linearMap R B ∘ₗ Coalgebra.counit ∧
      LinearMap.mul' R B ∘ₗ S.lTensor B ∘ₗ Coalgebra.comul =
        Algebra.linearMap R B ∘ₗ Coalgebra.counit :=
  ⟨_, mul_antipodeOfBijective_rTensor_comul _,
    mul_antipodeOfBijective_lTensor_comul (bijective_endOfPoint_id_of_leftRigid R B)⟩

end TauCeti.HopfAlgebra
