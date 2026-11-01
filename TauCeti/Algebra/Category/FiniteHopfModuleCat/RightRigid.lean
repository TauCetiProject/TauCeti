/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Monoidal
public import TauCeti.Algebra.HopfAlgebra.Module.Dual

/-!
# Right duals of finite-dimensional Hopf algebra modules

Let `H` be a Hopf algebra over a field `k`. This file equips the monoidal category
`FiniteHopfModuleCat k H` of finite-dimensional `H`-modules with right duals. The right dual of
`M` is its contragredient `dual M`, the linear dual on which `H` acts by
`(a φ)(m) = φ(S(a) m)`. Evaluation `φ ⊗ m ↦ φ m` and coevaluation `1 ↦ ∑ i, b i ⊗ b^i` are the
ordinary finite-dimensional linear maps `BialgebraModule.dualEval` and
`BialgebraModule.dualCoeval`, which are `H`-linear by the two antipode identities. The zigzag
identities are their module-level zigzag identities, transported along the identification of
the monoidal structure with `BialgebraModule.assoc`, `lid` and `rid`.

No commutativity or finite-dimensionality hypothesis is imposed on `H`, and the antipode need not
be bijective. Left duals, which use the inverse of the antipode, are not constructed here.

## Main declarations

* `TauCeti.FiniteHopfModuleCat.dual`: the contragredient of a finite-dimensional module.
* `TauCeti.FiniteHopfModuleCat.dualEvaluation`: evaluation `dual M ⊗ M ⟶ 𝟙_`.
* `TauCeti.FiniteHopfModuleCat.dualCoevaluation`: coevaluation `𝟙_ ⟶ M ⊗ dual M`.
* `TauCeti.FiniteHopfModuleCat.instRightRigidCategory`: finite-dimensional modules over a Hopf
  algebra form a right rigid monoidal category.

## References

See C. Kassel, *Quantum Groups*, Chapter XIV, and Etingof--Gelaki--Nikshych--Ostrik,
*Tensor Categories*, Section 2.10, for duals of modules over a Hopf algebra. The construction
parallels Mathlib's right duals in `FGModuleCat` and Tau Ceti's right duals of
finite-dimensional comodules.
-/

public noncomputable section

open CategoryTheory MonoidalCategory

namespace TauCeti.FiniteHopfModuleCat

open BialgebraModule

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H]

/-- The contragredient of a finite-dimensional module: its linear dual, on which `H` acts
through the antipode. -/
-- Expose the body so that the carrier is definitionally the contragredient carrier, while the
-- semireducible definition keeps instance search on the category's own module instances.
@[expose]
def dual (M : FiniteHopfModuleCat k H) : FiniteHopfModuleCat k H :=
  of (Dual k H M)

/-- Evaluation of the contragredient against a finite-dimensional module, as a morphism. -/
def dualEvaluation (M : FiniteHopfModuleCat k H) :
    dual M ⊗ M ⟶ 𝟙_ (FiniteHopfModuleCat k H) :=
  ofHom (dualEval k H M)

/-- The underlying map of evaluation is the module-level evaluation `dualEval`. -/
@[simp]
theorem dualEvaluation_hom_hom (M : FiniteHopfModuleCat k H) :
    (dualEvaluation M).hom.hom = dualEval k H M := (rfl)

/-- Evaluation applies the functional to the vector. -/
theorem dualEvaluation_tmul (M : FiniteHopfModuleCat k H) (φ : dual M) (m : M) :
    (dualEvaluation M).hom.hom (tmul k H φ m) = (trivialEquiv k H).symm (dualEquiv k H M φ m) :=
  dualEval_tmul k H M φ m

/-- The finite-dimensional coevaluation into the tensor product with the contragredient, as a
morphism. -/
def dualCoevaluation (M : FiniteHopfModuleCat k H) :
    𝟙_ (FiniteHopfModuleCat k H) ⟶ M ⊗ dual M :=
  ofHom (dualCoeval k H M)

/-- The underlying map of coevaluation is the module-level coevaluation `dualCoeval`. -/
@[simp]
theorem dualCoevaluation_hom_hom (M : FiniteHopfModuleCat k H) :
    (dualCoevaluation M).hom.hom = dualCoeval k H M := (rfl)

/-- The contragredient is an exact right dual of a finite-dimensional module. -/
instance instExactPairingDual (M : FiniteHopfModuleCat k H) : ExactPairing M (dual M) where
  coevaluation' := dualCoevaluation M
  evaluation' := dualEvaluation M
  coevaluation_evaluation' := by
    rw [Iso.eq_comp_inv]
    apply hom_ext
    simp only [hom_hom_comp, whiskerLeft_hom_hom, whiskerRight_hom_hom, associator_inv_hom,
      leftUnitor_hom_hom, rightUnitor_hom_hom, dualCoevaluation_hom_hom,
      dualEvaluation_hom_hom]
    -- The goal differs from the module-level identity only in the bracketing of composition
    -- and in the presentation of the carriers' module instances, both definitional.
    exact lid_comp_dualEval_assoc_dualCoeval k H M
  evaluation_coevaluation' := by
    rw [Iso.eq_comp_inv]
    apply hom_ext
    simp only [hom_hom_comp, whiskerLeft_hom_hom, whiskerRight_hom_hom, associator_hom_hom,
      leftUnitor_hom_hom, rightUnitor_hom_hom, dualCoevaluation_hom_hom,
      dualEvaluation_hom_hom]
    -- The goal differs from the module-level identity only in the bracketing of composition
    -- and in the presentation of the carriers' module instances, both definitional.
    exact rid_comp_dualEval_assoc_dualCoeval k H M

/-- Every finite-dimensional module over a Hopf algebra has its contragredient as a right
dual. -/
instance instHasRightDual (M : FiniteHopfModuleCat k H) : HasRightDual M :=
  ⟨dual M⟩

/-- Finite-dimensional modules over a Hopf algebra form a right rigid monoidal category. -/
instance instRightRigidCategory : RightRigidCategory (FiniteHopfModuleCat k H) where

end TauCeti.FiniteHopfModuleCat
