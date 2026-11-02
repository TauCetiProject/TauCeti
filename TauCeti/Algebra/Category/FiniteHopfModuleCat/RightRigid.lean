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
* `TauCeti.FiniteHopfModuleCat.evaluation_tmul`,
  `TauCeti.FiniteHopfModuleCat.dualEquiv_rightAdjointMate_apply` and
  `TauCeti.FiniteHopfModuleCat.tensor_evaluation_tmul`: on elements, evaluation applies a
  functional, the right adjoint mate of a morphism is its transpose, and the tensor product
  pairing of `(X₁, X₁ᘁ)` and `(X₂, X₂ᘁ)` multiplies the two evaluations. These reduce identities
  between morphisms out of tensor products with duals to computations with linear functionals.

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

/-- Evaluation of the right dual applies the functional to the vector. -/
@[simp]
theorem evaluation_tmul (M : FiniteHopfModuleCat k H) (φ : (Mᘁ : FiniteHopfModuleCat k H))
    (m : M) :
    (ε_ M Mᘁ).hom.hom (tmul k H φ m) = (trivialEquiv k H).symm (dualEquiv k H M φ m) := by
  -- The evaluation of the right dual is `dualEvaluation M`, by definition of the instance.
  rw [show ε_ M Mᘁ = dualEvaluation M from rfl, dualEvaluation_hom_hom]
  exact dualEval_tmul k H M φ m

/-- The right adjoint mate of a morphism is its transpose. -/
@[simp]
theorem dualEquiv_rightAdjointMate_apply {M N : FiniteHopfModuleCat k H} (f : M ⟶ N)
    (φ : (Nᘁ : FiniteHopfModuleCat k H)) (m : M) :
    dualEquiv k H M ((fᘁ).hom.hom φ) m = dualEquiv k H N φ (f.hom.hom m) := by
  have h := LinearMap.congr_fun
    (congrArg (fun u => u.hom.hom) (rightAdjointMate_comp_evaluation f)) (tmul k H φ m)
  simp only [hom_hom_comp, LinearMap.comp_apply] at h
  rw [whiskerRight_tmul, whiskerLeft_tmul, evaluation_tmul, evaluation_tmul] at h
  exact (trivialEquiv k H).symm.injective h

omit [HopfAlgebra k H] in
/-- The evaluation of a tensor product pairing, written with the module-level maps on the
native carriers. -/
private theorem dualEval_tensorMap_assoc_tmul [HopfAlgebra k H] {V W : Type*} [AddCommGroup V]
    [Module k V] [Module H V] [IsScalarTower k H V] [AddCommGroup W] [Module k W] [Module H W]
    [IsScalarTower k H W] (β : Dual k H W) (α : Dual k H V) (v : V) (w : W) :
    dualEval k H W (tensorMap k H LinearMap.id (lid k H W).toLinearMap
      (tensorMap k H LinearMap.id (tensorMap k H (dualEval k H V) LinearMap.id)
        (tensorMap k H LinearMap.id (assoc k H (Dual k H V) V W).symm.toLinearMap
          (assoc k H (Dual k H W) (Dual k H V) (Tensor k H V W)
            (tmul k H (tmul k H β α) (tmul k H v w)))))) =
      (trivialEquiv k H).symm (dualEquiv k H V α v * dualEquiv k H W β w) := by
  simp [← LinearEquiv.map_smul]

/-- The evaluation of the tensor product pairing of `(X₁, X₁ᘁ)` and `(X₂, X₂ᘁ)` sends
`(β ⊗ α) ⊗ (x₁ ⊗ x₂)` to `α(x₁) β(x₂)`. -/
@[simp]
theorem tensor_evaluation_tmul (X₁ X₂ : FiniteHopfModuleCat k H)
    (β : (X₂ᘁ : FiniteHopfModuleCat k H)) (α : (X₁ᘁ : FiniteHopfModuleCat k H))
    (x₁ : X₁) (x₂ : X₂) :
    (ε_ (X₁ ⊗ X₂) (X₂ᘁ ⊗ X₁ᘁ)).hom.hom
        (tmul k H (tmul k H β α : ↑(X₂ᘁ ⊗ X₁ᘁ)) (tmul k H x₁ x₂ : ↑(X₁ ⊗ X₂))) =
      (trivialEquiv k H).symm (dualEquiv k H X₁ α x₁ * dualEquiv k H X₂ β x₂) := by
  have h : ε_ (X₁ ⊗ X₂) (X₂ᘁ ⊗ X₁ᘁ) = (α_ _ _ _).hom ≫
      (X₂ᘁ : FiniteHopfModuleCat k H) ◁ (α_ _ _ _).inv ≫
      (X₂ᘁ : FiniteHopfModuleCat k H) ◁ (ε_ X₁ X₁ᘁ ▷ X₂) ≫
      (X₂ᘁ : FiniteHopfModuleCat k H) ◁ (λ_ X₂).hom ≫ ε_ X₂ X₂ᘁ := by
    rw [ExactPairing.tensor_evaluation]; monoidal
  rw [h, show ε_ X₁ X₁ᘁ = dualEvaluation X₁ from rfl, show ε_ X₂ X₂ᘁ = dualEvaluation X₂ from rfl]
  simp only [hom_hom_comp, whiskerLeft_hom_hom, whiskerRight_hom_hom, associator_hom_hom,
    associator_inv_hom, leftUnitor_hom_hom, dualEvaluation_hom_hom]
  -- The carriers of the categorical tensor products and duals agree with the module-level
  -- carriers only up to unfolding.
  exact dualEval_tensorMap_assoc_tmul β α x₁ x₂

end TauCeti.FiniteHopfModuleCat
