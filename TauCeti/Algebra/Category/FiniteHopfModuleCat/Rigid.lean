/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteHopfModuleCat.RightRigid
public import TauCeti.Algebra.HopfAlgebra.Module.LeftDual

/-!
# Left duals of finite-dimensional Hopf algebra modules

Let `H` be a Hopf algebra over a field `k` whose antipode `S` is bijective. This file equips the
monoidal category `FiniteHopfModuleCat k H` of finite-dimensional `H`-modules with left duals,
and so with a rigid structure. The left dual of `M` is its inverse-antipode contragredient
`leftDual hS M`, the linear dual on which `H` acts by `(a φ)(m) = φ(S⁻¹(a) m)`. Its evaluation
`M ⊗ ᘁM ⟶ 𝟙_` is `m ⊗ φ ↦ φ m`, which is `H`-linear by the identity `S⁻¹(a₂) a₁ = ε(a) 1`.

The zigzag identities of `ᘁM` with `M` are transported, by `exactPairingCongrRight`, from the
right duality of `ᘁM` with its contragredient `(ᘁM)ᘁ` along the evaluation isomorphism
`M ≅ (ᘁM)ᘁ`, which is `H`-linear because the twists by `S⁻¹` and by `S` cancel. This is the same
construction as for the left duals of finite-dimensional vector spaces in
`FGModuleCat.leftExactPairing`.

The bijectivity of the antipode is an explicit hypothesis `hS`, and the left duals depend on it
through the action of `S⁻¹`. The rigid structure `rigidCategory hS` is therefore a definition and
not an instance; statements about its left duals install it locally. No commutativity or
finite-dimensionality hypothesis is imposed on `H`. The right duals are those of
`instRightRigidCategory`.

## Main declarations

* `TauCeti.FiniteHopfModuleCat.leftDual`: the inverse-antipode contragredient of a
  finite-dimensional module.
* `TauCeti.FiniteHopfModuleCat.leftDualEvalIso`: the evaluation isomorphism `M ≅ (ᘁM)ᘁ`.
* `TauCeti.FiniteHopfModuleCat.leftDualEvaluation` and
  `TauCeti.FiniteHopfModuleCat.leftDualCoevaluation`: evaluation `M ⊗ ᘁM ⟶ 𝟙_` and
  coevaluation `𝟙_ ⟶ ᘁM ⊗ M`.
* `TauCeti.FiniteHopfModuleCat.leftExactPairing`: the inverse-antipode contragredient is an
  exact left dual.
* `TauCeti.FiniteHopfModuleCat.rigidCategory`: finite-dimensional modules over a Hopf algebra
  with bijective antipode form a rigid monoidal category.

## References

See C. Kassel, *Quantum Groups*, Chapter XIV, and Etingof--Gelaki--Nikshych--Ostrik,
*Tensor Categories*, Section 2.10, for left and right duals of modules over a Hopf algebra.
-/

public noncomputable section

open CategoryTheory MonoidalCategory

namespace TauCeti.FiniteHopfModuleCat

open BialgebraModule

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H]
  (hS : Function.Bijective (HopfAlgebra.antipode k : H →ₗ[k] H))

/-- The inverse-antipode contragredient of a finite-dimensional module: its linear dual, on
which `H` acts through the inverse of the antipode. -/
-- Expose the body so that the carrier is definitionally the contragredient carrier, while the
-- semireducible definition keeps instance search on the category's own module instances.
@[expose]
def leftDual (M : FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H :=
  of (LeftDual k H M hS)

/-- Evaluation identifies a finite-dimensional module with the contragredient of its
inverse-antipode contragredient. -/
def leftDualEvalIso (M : FiniteHopfModuleCat k H) : M ≅ dual (leftDual hS M) :=
  (leftDualEvalEquiv k H M hS).toFiniteHopfModuleCatIso

/-- The underlying map of the evaluation isomorphism is the module-level evaluation
equivalence. -/
@[simp]
theorem leftDualEvalIso_hom_hom (M : FiniteHopfModuleCat k H) :
    (leftDualEvalIso hS M).hom.hom.hom = (leftDualEvalEquiv k H M hS).toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_hom_hom _

/-- The underlying map of the inverse evaluation isomorphism is the inverse module-level
evaluation equivalence. -/
@[simp]
theorem leftDualEvalIso_inv_hom (M : FiniteHopfModuleCat k H) :
    (leftDualEvalIso hS M).inv.hom.hom = (leftDualEvalEquiv k H M hS).symm.toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_inv_hom _

/-- Evaluation `m ⊗ φ ↦ φ m` of the inverse-antipode contragredient, as a morphism
`M ⊗ ᘁM ⟶ 𝟙_`: the evaluation of the right duality of `ᘁM`, precomposed with the
evaluation isomorphism. -/
def leftDualEvaluation (M : FiniteHopfModuleCat k H) :
    M ⊗ leftDual hS M ⟶ 𝟙_ (FiniteHopfModuleCat k H) :=
  (leftDualEvalIso hS M).hom ▷ leftDual hS M ≫ dualEvaluation (leftDual hS M)

/-- Evaluation of the inverse-antipode contragredient applies the functional to the vector. -/
@[simp]
theorem leftDualEvaluation_tmul (M : FiniteHopfModuleCat k H) (m : M) (φ : leftDual hS M) :
    (leftDualEvaluation hS M).hom.hom (tmul k H m φ) =
      (trivialEquiv k H).symm (leftDualEquiv k H M hS φ m) := by
  rw [leftDualEvaluation, hom_hom_comp, LinearMap.comp_apply, whiskerRight_tmul,
    dualEvaluation_tmul, leftDualEvalIso_hom_hom]
  -- The carrier of `leftDual hS M` is definitionally `LeftDual k H M hS`, but not syntactically.
  exact congrArg _ (dualEquiv_leftDualEvalEquiv_apply k H M hS m φ)

/-- Coevaluation into the tensor product of the inverse-antipode contragredient with the
module, as a morphism `𝟙_ ⟶ ᘁM ⊗ M`: the coevaluation of the right duality of `ᘁM`, followed
by the inverse evaluation isomorphism on the second factor. -/
def leftDualCoevaluation (M : FiniteHopfModuleCat k H) :
    𝟙_ (FiniteHopfModuleCat k H) ⟶ leftDual hS M ⊗ M :=
  dualCoevaluation (leftDual hS M) ≫ leftDual hS M ◁ (leftDualEvalIso hS M).inv

/-- The underlying map of the left coevaluation is the module-level coevaluation `dualCoeval`
of the inverse-antipode contragredient, followed by inverse evaluation on the second factor. -/
@[simp]
theorem leftDualCoevaluation_hom_hom (M : FiniteHopfModuleCat k H) :
    (leftDualCoevaluation hS M).hom.hom =
      tensorMap k H LinearMap.id (leftDualEvalEquiv k H M hS).symm.toLinearMap ∘ₗ
        dualCoeval k H (leftDual hS M) := by
  rw [leftDualCoevaluation, hom_hom_comp, whiskerLeft_hom_hom, leftDualEvalIso_inv_hom,
    dualCoevaluation_hom_hom]
  -- The two sides differ only in the presentation of the carriers' module instances, which
  -- agree definitionally.
  rfl

/-- The inverse-antipode contragredient is an exact left dual of a finite-dimensional module.
The zigzag identities are transported by `exactPairingCongrRight` from the right duality of
`ᘁM` along the evaluation isomorphism `M ≅ (ᘁM)ᘁ`. -/
@[instance_reducible]
def leftExactPairing (M : FiniteHopfModuleCat k H) : ExactPairing (leftDual hS M) M where
  evaluation' := leftDualEvaluation hS M
  coevaluation' := leftDualCoevaluation hS M
  evaluation_coevaluation' :=
    (exactPairingCongrRight (leftDualEvalIso hS M)).evaluation_coevaluation'
  coevaluation_evaluation' :=
    (exactPairingCongrRight (leftDualEvalIso hS M)).coevaluation_evaluation'

/-- Finite-dimensional modules over a Hopf algebra with bijective antipode form a rigid monoidal
category. The left dual of `M` is its inverse-antipode contragredient `leftDual hS M`, with
evaluation `leftDualEvaluation` and coevaluation `leftDualCoevaluation`. The right duals are the
contragredients of `instRightRigidCategory`. Not an instance, as the left duals depend on the
explicit bijectivity hypothesis `hS`. -/
@[expose, instance_reducible]
def rigidCategory : RigidCategory (FiniteHopfModuleCat k H) where
  toRightRigidCategory := instRightRigidCategory
  leftDual M := { leftDual := leftDual hS M, exact := leftExactPairing hS M }

/-- The chosen left dual is the inverse-antipode contragredient. -/
@[simp]
theorem rigidCategory_leftDual (M : FiniteHopfModuleCat k H) :
    letI := rigidCategory hS
    (ᘁM) = leftDual hS M :=
  (rfl)

/-- The evaluation of the chosen left dual is `leftDualEvaluation`. -/
@[simp]
theorem rigidCategory_evaluation (M : FiniteHopfModuleCat k H) :
    letI := rigidCategory hS
    ε_ (ᘁM) M = leftDualEvaluation hS M :=
  (rfl)

/-- The coevaluation of the chosen left dual is `leftDualCoevaluation`. -/
@[simp]
theorem rigidCategory_coevaluation (M : FiniteHopfModuleCat k H) :
    letI := rigidCategory hS
    η_ (ᘁM) M = leftDualCoevaluation hS M :=
  (rfl)

end TauCeti.FiniteHopfModuleCat
