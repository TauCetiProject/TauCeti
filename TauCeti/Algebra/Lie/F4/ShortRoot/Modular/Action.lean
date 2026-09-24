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

This restricted action `ρ : L → End(I)` is the input to the represented quotient
`ρ(L) / ρ(I)` used in the construction of the characteristic-two exceptional isogeny. Only the
action on the ideal is defined here; identifying that represented quotient with the quotient of
the modular Chevalley algebra by its short-root ideal needs a later theorem.

## Main definitions

* `TauCeti.DynkinType.f4ShortRootAdjoint`: the restricted adjoint representation.
* `TauCeti.DynkinType.f4ShortRootAdjointMatrix`: its matrix in the canonical basis
  `f4ShortRootLieIdealBasis`.
* `TauCeti.DynkinType.f4ShortRootSignedSimpleAdjoint`: the operators at the positive and negative
  simple roots.

## Main results

* `TauCeti.DynkinType.f4ShortRootAdjointMatrix_apply` computes matrix entries as ambient
  bracket coordinates.
* `TauCeti.DynkinType.f4ShortRootAdjoint_rootVector_of_add_eq_short`,
  `TauCeti.DynkinType.coe_f4ShortRootAdjoint_opposite`, and
  `TauCeti.DynkinType.coe_f4ShortRootAdjoint_simpleCoroot` compute the action on the three
  forms of basis interaction used downstream.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Memoirs AMS **80** (1968), §11.
* R. W. Carter, *Simple Groups of Lie Type*, §12.3.
-/

public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra LieModule

noncomputable section

/-- The adjoint action of the reduced Chevalley Lie algebra on its modular short-root ideal. -/
noncomputable def f4ShortRootAdjoint :=
  LieModule.toEnd (ZMod 2) f4ModularChevalleyLieAlgebra f4ShortRootLieIdeal

/-- The restricted adjoint action is the ambient Lie bracket after coercion from the ideal. -/
@[simp] theorem coe_f4ShortRootAdjoint_apply
    (x : f4ModularChevalleyLieAlgebra) (y : f4ShortRootLieIdeal) :
    (f4ShortRootAdjoint x y : f4ModularChevalleyLieAlgebra) =
      ⁅x, (y : f4ModularChevalleyLieAlgebra)⁆ := by
  rfl

/-- Matrix of the modular short-root adjoint action in its integral-weight basis. -/
noncomputable def f4ShortRootAdjointMatrix
    (X : f4ModularChevalleyLieAlgebra) : Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
    (f4ShortRootAdjoint X)

/-- Base change of a modular short-root adjoint matrix to a value algebra. -/
noncomputable abbrev f4ShortRootAdjointMatrixBaseChange
    {A : Type*} [CommRing A] [Algebra (ZMod 2) A]
    (X : f4ModularChevalleyLieAlgebra) : Matrix (Fin 26) (Fin 26) A :=
  (f4ShortRootAdjointMatrix X).map (algebraMap (ZMod 2) A)

/-- An entry of the adjoint matrix is the corresponding ambient bracket coordinate. -/
@[simp] theorem f4ShortRootAdjointMatrix_apply
    (X : f4ModularChevalleyLieAlgebra) (i j : Fin 26) :
    f4ShortRootAdjointMatrix X i j =
      f4ModularChevalleyBasis.repr
        ⁅X, (f4ShortRootLieIdealBasis j : f4ModularChevalleyLieAlgebra)⁆
        (f4ShortRootBasisCoordinate i) := by
  calc
    _ = f4ShortRootLieIdealBasis.repr
        (f4ShortRootAdjoint X (f4ShortRootLieIdealBasis j)) i := by
      -- Unfold the named adjoint matrix to apply the general matrix-entry formula.
      change (LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
        (f4ShortRootAdjoint X)) i j = _
      exact LinearMap.toMatrix_apply _ _ _ _ _
    _ = f4ModularChevalleyBasis.repr
        (f4ShortRootAdjoint X (f4ShortRootLieIdealBasis j) :
          f4ModularChevalleyLieAlgebra)
        (f4ShortRootBasisCoordinate i) :=
      f4ShortRootLieIdealBasis_repr_apply _ _
    _ = _ := congrArg
      (fun Y : f4ModularChevalleyLieAlgebra =>
        f4ModularChevalleyBasis.repr Y (f4ShortRootBasisCoordinate i))
      (coe_f4ShortRootAdjoint_apply X (f4ShortRootLieIdealBasis j))

/-- The named adjoint matrix is the matrix of the restricted adjoint endomorphism. -/
theorem f4ShortRootAdjointMatrix_eq_toMatrix (X : f4ModularChevalleyLieAlgebra) :
    f4ShortRootAdjointMatrix X =
      LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
        (f4ShortRootAdjoint X) := by
  rfl

/-- The signed simple-root adjoint operator restricted to the modular short-root ideal. -/
noncomputable def f4ShortRootSignedSimpleAdjoint (k : Fin 4 ⊕ Fin 4) :
    Module.End (ZMod 2) f4ShortRootLieIdeal :=
  f4ShortRootAdjoint (f4ModularSignedSimpleRootVector k)

/-- The signed simple-root adjoint operator is the bracket with its signed simple root vector. -/
theorem coe_f4ShortRootSignedSimpleAdjoint_apply
    (k : Fin 4 ⊕ Fin 4) (y : f4ShortRootLieIdeal) :
    (f4ShortRootSignedSimpleAdjoint k y : f4ModularChevalleyLieAlgebra) =
      ⁅f4ModularRootVector (f4SignedSimpleRootIndex k),
        (y : f4ModularChevalleyLieAlgebra)⁆ := by
  simp only [f4ShortRootSignedSimpleAdjoint, coe_f4ShortRootAdjoint_apply,
    f4ModularSignedSimpleRootVector_eq]

/-- The signed simple-root operator is the restricted adjoint action of its root vector. -/
@[simp] theorem f4ShortRootSignedSimpleAdjoint_apply (k : Fin 4 ⊕ Fin 4)
    (y : f4ShortRootLieIdeal) :
    f4ShortRootSignedSimpleAdjoint k y =
      f4ShortRootAdjoint (f4ModularRootVector (f4SignedSimpleRootIndex k)) y :=
  Subtype.ext ((coe_f4ShortRootSignedSimpleAdjoint_apply k y).trans
    (coe_f4ShortRootAdjoint_apply _ y).symm)

/-- The matrix of the signed simple-root adjoint operator in the canonical short-root basis. -/
noncomputable def f4ShortRootSignedSimpleAdjointMatrix (k : Fin 4 ⊕ Fin 4) :
    Matrix (Fin 26) (Fin 26) (ZMod 2) :=
  LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
    (f4ShortRootSignedSimpleAdjoint k)

/-- Entries of a signed simple-root adjoint matrix are the corresponding ideal-basis
coordinates. -/
@[simp] theorem f4ShortRootSignedSimpleAdjointMatrix_apply
    (k : Fin 4 ⊕ Fin 4) (a b : Fin 26) :
    f4ShortRootSignedSimpleAdjointMatrix k a b =
      (f4ShortRootLieIdealBasis.repr
        (f4ShortRootSignedSimpleAdjoint k (f4ShortRootLieIdealBasis b))) a := by
  -- Unfold the named adjoint matrix to apply the general matrix-entry formula.
  change (LinearMap.toMatrix f4ShortRootLieIdealBasis f4ShortRootLieIdealBasis
    (f4ShortRootSignedSimpleAdjoint k)) a b = _
  exact LinearMap.toMatrix_apply _ _ _ _ _

/-- On a short-root basis column whose translate is again short, the restricted adjoint action
is the translated short-root basis vector with coefficient one. -/
theorem f4ShortRootAdjoint_rootVector_of_add_eq_short (alpha beta gamma : Fin 48)
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
  exact f4Modular_lie_rootVector_of_add_of_length_eq alpha beta gamma
    (hbeta.trans hgamma.symm) h

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
  rw [coe_f4ShortRootAdjoint_apply, Subtype.coe_mk,
    f4Modular_lie_rootVector_simpleCoroot]

end

end TauCeti.DynkinType
