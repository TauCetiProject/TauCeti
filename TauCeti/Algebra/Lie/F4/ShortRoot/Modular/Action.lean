/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Modular.Basis

/-!
# The adjoint action on the modular F₄ short-root ideal

This file restricts the adjoint action of the full Chevalley lattice reduced modulo two to its
twenty-six-dimensional short-root ideal. It expresses that representation in the canonical basis
of short-root vectors and the two short simple coroots.

This is the representation used to recover the quotient of the modular Chevalley algebra by its
short-root ideal. In the construction of the characteristic-two exceptional isogeny, the ambient
group acts on this represented quotient and the result is read back in the short-root module.

## Main definitions

* `TauCeti.DynkinType.f4ShortRootLieIdealBasis`: the canonical basis of the short-root ideal.
* `TauCeti.DynkinType.f4ShortRootAdjoint`: the restricted adjoint representation.
* `TauCeti.DynkinType.f4ShortRootAdjointMatrix`: its matrix in the canonical basis.
* `TauCeti.DynkinType.f4ShortRootSimpleAdjoint`: the operators at the positive and negative
  simple roots.

## Main results

* `TauCeti.DynkinType.f4ShortRootLieIdealBasis_repr` compares ideal and ambient coordinates.
* `TauCeti.DynkinType.f4ShortRootAdjoint_root_edge`,
  `TauCeti.DynkinType.coe_f4ShortRootAdjoint_opposite`, and
  `TauCeti.DynkinType.coe_f4ShortRootAdjoint_simpleCoroot` compute the action on the three
  forms of basis interaction used downstream.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.

The declaration order and proofs are adapted from the project's `cfsg/a0-integration-reference`
branch, commit `b2a9572a2`.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra LieModule

noncomputable section

/-- The coordinate basis of the modular short-root Lie ideal. -/
noncomputable def f4ShortRootLieIdealBasis :
    Module.Basis (Fin 26) (ZMod 2) f4ShortRootLieIdeal :=
  f4ShortRootBasis.map
    (LinearEquiv.ofEq _ _ f4ShortRootLieIdeal_toSubmodule.symm)

/-- The ideal basis has the same ambient Chevalley coordinates as the short-root subspace basis. -/
@[simp] theorem coe_f4ShortRootLieIdealBasis (a : Fin 26) :
    (f4ShortRootLieIdealBasis a : f4ModularChevalleyLieAlgebra) =
      f4ModularChevalleyBasis (f4ShortRootBasisCoordinate a) := by
  exact (LinearEquiv.coe_ofEq_apply f4ShortRootLieIdeal_toSubmodule.symm
    (f4ShortRootBasis a)).trans (coe_f4ShortRootBasis a)

/-- A nonzero-weight ideal basis vector is the corresponding modular short-root vector. -/
theorem coe_f4ShortRootLieIdealBasis_symm_inl (i : F4ShortRootIndex) :
    (f4ShortRootLieIdealBasis (f4ShortRootWeightIndexEquiv.symm (Sum.inl i)) :
      f4ModularChevalleyLieAlgebra) = f4ModularRootVector i := by
  rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis]
  exact coe_f4ShortRootBasis_symm_inl i

/-- Coordinate twelve of the ideal basis is the first short simple coroot. -/
theorem coe_f4ShortRootLieIdealBasis_twelve :
    (f4ShortRootLieIdealBasis 12 : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm (2 : Fin 4)) := by
  rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis]
  exact coe_f4ShortRootBasis_twelve

/-- Coordinate thirteen of the ideal basis is the second short simple coroot. -/
theorem coe_f4ShortRootLieIdealBasis_thirteen :
    (f4ShortRootLieIdealBasis 13 : f4ModularChevalleyLieAlgebra) =
      f4ModularSimpleCoroot (Fin.cast rank_F4.symm (3 : Fin 4)) := by
  rw [coe_f4ShortRootLieIdealBasis, ← coe_f4ShortRootBasis]
  exact coe_f4ShortRootBasis_thirteen

/-- The adjoint action of the reduced Chevalley Lie algebra on its modular short-root ideal. -/
noncomputable def f4ShortRootAdjoint :=
  LieModule.toEnd (ZMod 2) f4ModularChevalleyLieAlgebra f4ShortRootLieIdeal

/-- The restricted adjoint action is the ambient Lie bracket after coercion from the ideal. -/
@[simp] theorem coe_f4ShortRootAdjoint_apply
    (x : f4ModularChevalleyLieAlgebra) (y : f4ShortRootLieIdeal) :
    (f4ShortRootAdjoint x y : f4ModularChevalleyLieAlgebra) =
      ⁅x, (y : f4ModularChevalleyLieAlgebra)⁆ := by
  rfl

/-- Coordinates in the ideal basis agree with the corresponding ambient Chevalley coordinates. -/
theorem f4ShortRootLieIdealBasis_repr (y : f4ShortRootLieIdeal) (i : Fin 26) :
    f4ShortRootLieIdealBasis.repr y i =
      f4ModularChevalleyBasis.repr (y : f4ModularChevalleyLieAlgebra)
        (f4ShortRootBasisCoordinate i) := by
  classical
  let f : f4ShortRootLieIdeal →ₗ[ZMod 2] ZMod 2 :=
    (Finsupp.lapply i).comp f4ShortRootLieIdealBasis.repr.toLinearMap
  let g : f4ShortRootLieIdeal →ₗ[ZMod 2] ZMod 2 :=
    (Finsupp.lapply (f4ShortRootBasisCoordinate i)).comp
      (f4ModularChevalleyBasis.repr.toLinearMap.comp
        f4ShortRootLieIdeal.toSubmodule.subtype)
  -- Both sides are evaluations of the indicated coordinate linear maps.
  change f y = g y
  apply LinearMap.congr_fun (f4ShortRootLieIdealBasis.ext fun j => ?_) y
  simp only [f, g, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    Finsupp.lapply_apply, Module.Basis.repr_self, Finsupp.single_apply]
  -- The submodule inclusion and the Lie-ideal coercion are the same underlying map.
  rw [show f4ShortRootLieIdeal.toSubmodule.subtype (f4ShortRootLieIdealBasis j) =
      (f4ShortRootLieIdealBasis j : f4ModularChevalleyLieAlgebra) by rfl,
    coe_f4ShortRootLieIdealBasis, f4ModularChevalleyBasis.repr_self,
    Finsupp.single_apply]
  by_cases hji : j = i
  · simp [hji]
  · have hcoord : f4ShortRootBasisCoordinate j ≠ f4ShortRootBasisCoordinate i :=
      fun h => hji (f4ShortRootBasisCoordinate_injective h)
    simp [hji, hcoord]

/-- Matrix of the modular short-root adjoint action in its integral-weight basis. -/
noncomputable abbrev f4ShortRootAdjointMatrix
    (X : f4ModularChevalleyLieAlgebra) : Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
    (f4ShortRootAdjoint X)

/-- An entry of the adjoint matrix is the corresponding ambient bracket coordinate. -/
theorem f4ShortRootAdjointMatrix_apply
    (X : f4ModularChevalleyLieAlgebra) (i j : Fin 26) :
    f4ShortRootAdjointMatrix X i j =
      f4ModularChevalleyBasis.repr
        ⁅X, (f4ShortRootLieIdealBasis j : f4ModularChevalleyLieAlgebra)⁆
        (f4ShortRootBasisCoordinate i) := by
  calc
    _ = f4ShortRootLieIdealBasis.repr
        (f4ShortRootAdjoint X (f4ShortRootLieIdealBasis j)) i :=
      LinearMap.toMatrix_apply _ _ _ _ _
    _ = f4ModularChevalleyBasis.repr
        (f4ShortRootAdjoint X (f4ShortRootLieIdealBasis j) :
          f4ModularChevalleyLieAlgebra)
        (f4ShortRootBasisCoordinate i) :=
      f4ShortRootLieIdealBasis_repr _ _
    _ = _ := congrArg
      (fun Y : f4ModularChevalleyLieAlgebra =>
        f4ModularChevalleyBasis.repr Y (f4ShortRootBasisCoordinate i))
      (coe_f4ShortRootAdjoint_apply X (f4ShortRootLieIdealBasis j))

/-- The pinned root index of a positive or negative simple root. -/
def f4SignedSimpleRootIndex : Fin 4 ⊕ Fin 4 → Fin 48
  | .inl i => Fin.castAdd 44 i
  | .inr i => f4OppositeRootIndex (Fin.castAdd 44 i)

/-- A positive simple-root label is its pinned root index. -/
@[simp] theorem f4SignedSimpleRootIndex_inl (i : Fin 4) :
    f4SignedSimpleRootIndex (.inl i) = Fin.castAdd 44 i := (rfl)

/-- A negative simple-root label is the index opposite to the corresponding positive root. -/
@[simp] theorem f4SignedSimpleRootIndex_inr (i : Fin 4) :
    f4SignedSimpleRootIndex (.inr i) = f4OppositeRootIndex (Fin.castAdd 44 i) := (rfl)

/-- A pinned positive or negative simple root vector in the reduced Chevalley lattice. -/
noncomputable def f4ModularSignedSimpleRootVector (k : Fin 4 ⊕ Fin 4) :
    f4ModularChevalleyLieAlgebra :=
  f4ModularRootVector (f4SignedSimpleRootIndex k)

/-- The simple-root adjoint operator restricted to the modular short-root ideal. -/
noncomputable def f4ShortRootSimpleAdjoint (k : Fin 4 ⊕ Fin 4) :
    Module.End (ZMod 2) f4ShortRootLieIdeal :=
  f4ShortRootAdjoint (f4ModularSignedSimpleRootVector k)

/-- The simple-root adjoint operator is the bracket with its signed simple root vector. -/
@[simp] theorem coe_f4ShortRootSimpleAdjoint_apply
    (k : Fin 4 ⊕ Fin 4) (y : f4ShortRootLieIdeal) :
    (f4ShortRootSimpleAdjoint k y : f4ModularChevalleyLieAlgebra) =
      ⁅f4ModularRootVector (f4SignedSimpleRootIndex k),
        (y : f4ModularChevalleyLieAlgebra)⁆ := by
  rfl

/-- The matrix of the simple-root adjoint operator in the canonical short-root basis. -/
noncomputable def f4ShortRootSimpleAdjointMatrix (k : Fin 4 ⊕ Fin 4) :
    Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
    (f4ShortRootSimpleAdjoint k)

/-- Entries of a simple-root adjoint matrix are the corresponding ideal-basis coordinates. -/
@[simp] theorem f4ShortRootSimpleAdjointMatrix_apply
    (k : Fin 4 ⊕ Fin 4) (a b : Fin 26) :
    f4ShortRootSimpleAdjointMatrix k a b =
      (f4ShortRootLieIdealBasis.repr
        (f4ShortRootSimpleAdjoint k (f4ShortRootLieIdealBasis b))) a := by
  -- Unfold the named adjoint matrix to apply the general matrix-entry formula.
  change (LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
    (f4ShortRootSimpleAdjoint k)) a b = _
  exact LinearMap.toMatrix_apply _ _ _ _ _

/-- On a short-root basis column whose translate is again short, the restricted adjoint action
is the translated short-root basis vector with coefficient one. -/
theorem f4ShortRootAdjoint_root_edge (alpha beta gamma : Fin 48)
    (hbeta : f4Length beta = 1) (hgamma : f4Length gamma = 1)
    (h : f4SimplyConnectedRootDatum.root gamma =
      f4SimplyConnectedRootDatum.root beta + f4SimplyConnectedRootDatum.root alpha) :
    f4ShortRootAdjoint (f4ModularRootVector alpha)
        (f4ShortRootLieIdealBasis
          (f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨beta, hbeta⟩))) =
      f4ShortRootLieIdealBasis
        (f4ShortRootWeightIndexEquiv.symm (Sum.inl ⟨gamma, hgamma⟩)) := by
  apply Subtype.ext
  simp only [coe_f4ShortRootAdjoint_apply, coe_f4ShortRootLieIdealBasis_symm_inl]
  exact f4Modular_lie_rootVector_of_add_eq_short alpha beta gamma hbeta hgamma h

/-- On the root coordinate opposite a short root, the restricted adjoint action lands in the
corresponding modular coroot. -/
theorem coe_f4ShortRootAdjoint_opposite (alpha : Fin 48)
    (hopp : f4Length (f4OppositeRootIndex alpha) = 1) :
    (f4ShortRootAdjoint (f4ModularRootVector alpha)
        (f4ShortRootLieIdealBasis
          (f4ShortRootWeightIndexEquiv.symm
            (Sum.inl ⟨f4OppositeRootIndex alpha, hopp⟩))) :
      f4ModularChevalleyLieAlgebra) = f4ModularCoroot alpha := by
  rw [coe_f4ShortRootAdjoint_apply, coe_f4ShortRootLieIdealBasis_symm_inl]
  exact f4Modular_lie_rootVector_opposite alpha

/-- On either short simple-coroot coordinate, the restricted adjoint action is the root vector
scaled by the reduced Cartan integer (with the bracket-order sign). -/
theorem coe_f4ShortRootAdjoint_simpleCoroot (alpha : Fin 48) (i : Fin F4.rank)
    (hi : Fin.cast rank_F4 i = 2 ∨ Fin.cast rank_F4 i = 3) :
    (f4ShortRootAdjoint (f4ModularRootVector alpha)
        ⟨f4ModularSimpleCoroot i,
          (mem_f4ShortRootLieIdeal_iff).mpr
            (f4ModularSimpleCoroot_mem_shortRootSubspace i hi)⟩ :
      f4ModularChevalleyLieAlgebra) =
      -(f4SimplyConnectedRootDatum.pairing alpha
        (Fin.castAdd 44 (Fin.cast rank_F4 i)) : ZMod 2) • f4ModularRootVector alpha := by
  -- The adjoint endomorphism is the ambient bracket, restricted to the ideal.
  change ⁅f4ModularRootVector alpha, f4ModularSimpleCoroot i⁆ = _
  rw [← lie_skew, f4Modular_lie_simpleCoroot_rootVector, neg_smul]

end

end TauCeti.DynkinType
