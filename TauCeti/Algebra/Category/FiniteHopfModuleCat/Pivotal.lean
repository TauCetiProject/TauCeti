/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Coalgebra.GroupLike
public import TauCeti.Algebra.Category.FiniteHopfModuleCat.RightRigid
public import TauCeti.CategoryTheory.Monoidal.Rigid.DualFunctor

import TauCeti.CategoryTheory.Monoidal.Rigid.Mate

/-!
# Monoidal trivializations of the double dual of finite-dimensional Hopf modules

Let `H` be a Hopf algebra over a field `k` and let `g` be a unit of `H` implementing the square of
the antipode, `S²(a) = g a g⁻¹`. For every finite-dimensional `H`-module `M`, the map
`j_M : m ↦ (φ ↦ φ(g m))` is an isomorphism `M ≅ Mᘁᘁ` with the double right dual of
`instRightRigidCategory`, and these isomorphisms are natural in `M`. This is
`unitEvalNatIso g hg : 𝟭 _ ≅ doubleRightDualFunctor _`.

If `g` is moreover group-like, `Δg = g ⊗ g` and `ε(g) = 1`, then `j` is compatible with the tensor
and unit comparisons of the strong monoidal double right dual functor, so that it is a monoidal
natural isomorphism (`unitEvalNatIso_isMonoidal`). This is the datum of a pivotal structure on
finite-dimensional `H`-modules: Tau Ceti's `PivotalCategory` asks for exactly such a monoidal
natural isomorphism, for any rigid structure extending `instRightRigidCategory`. The bijectivity
of the antipode needed for left duals follows from the same hypothesis on `g`, by
`TauCeti.HopfAlgebra.antipode_bijective_of_antipode_antipode`. For `U_q(sl₂)` the element
`g = K⁻¹` satisfies both hypotheses.

The proofs test morphisms into a double dual against evaluation (`ExactPairing.rightHom_ext`) and
compute evaluations on pure tensors. The element forms of evaluation, of right adjoint mates and
of the evaluation of a tensor product pairing are recorded along the way.

## Main declarations

* `TauCeti.FiniteHopfModuleCat.evaluation_tmul`,
  `TauCeti.FiniteHopfModuleCat.dualEquiv_rightAdjointMate_apply`,
  `TauCeti.FiniteHopfModuleCat.tensor_evaluation_tmul`: evaluation, transposition and the tensor
  product pairing on elements.
* `TauCeti.FiniteHopfModuleCat.unitEvalIso`: the isomorphism `M ≅ Mᘁᘁ`, `m ↦ (φ ↦ φ(g m))`.
* `TauCeti.FiniteHopfModuleCat.unitEvalNatIso`: these isomorphisms as a natural isomorphism
  `𝟭 _ ≅ doubleRightDualFunctor _`.
* `TauCeti.FiniteHopfModuleCat.unitEvalIso_unit_hom`,
  `TauCeti.FiniteHopfModuleCat.unitEvalIso_tensor_hom` and
  `TauCeti.FiniteHopfModuleCat.unitEvalNatIso_isMonoidal`: for group-like `g`, the natural
  isomorphism is monoidal.

## References

* C. Kassel, *Quantum Groups*, Graduate Texts in Mathematics 155, Chapter XIV, for duals and
  the double dual of modules over a Hopf algebra.
* P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*, Mathematical Surveys and
  Monographs 205, Sections 2.10 and 4.7, for the pivotal structure on modules over a Hopf
  algebra given by a group-like element implementing `S²`.
-/

public noncomputable section

open CategoryTheory MonoidalCategory ExactPairing Functor.LaxMonoidal

namespace TauCeti.FiniteHopfModuleCat

open BialgebraModule

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [HopfAlgebra k H]

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

variable (g : Hˣ) (hg : ∀ a : H, HopfAlgebra.antipode k (HopfAlgebra.antipode k a) = g * a * ↑g⁻¹)

/-- If the unit `g` implements the square of the antipode, `m ↦ (φ ↦ φ(g m))` is an isomorphism
of a finite-dimensional module with its double right dual. -/
def unitEvalIso (M : FiniteHopfModuleCat k H) : M ≅ (Mᘁ)ᘁ :=
  (unitEvalEquiv k H M g hg).toFiniteHopfModuleCatIso

/-- The underlying map of the double dual comparison is the module-level comparison
`BialgebraModule.unitEvalEquiv`. -/
theorem unitEvalIso_hom_hom (M : FiniteHopfModuleCat k H) :
    (unitEvalIso g hg M).hom.hom.hom = (unitEvalEquiv k H M g hg).toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_hom_hom _

/-- The underlying map of the inverse double dual comparison is the inverse module-level
comparison. -/
theorem unitEvalIso_inv_hom (M : FiniteHopfModuleCat k H) :
    (unitEvalIso g hg M).inv.hom.hom = (unitEvalEquiv k H M g hg).symm.toLinearMap :=
  LinearEquiv.toFiniteHopfModuleCatIso_inv_hom _

/-- The double dual comparison sends `m` to the functional `φ ↦ φ(g m)`. -/
@[simp]
theorem dualEquiv_unitEvalIso_hom_apply (M : FiniteHopfModuleCat k H) (m : M)
    (φ : (Mᘁ : FiniteHopfModuleCat k H)) :
    dualEquiv k H (Mᘁ : FiniteHopfModuleCat k H) ((unitEvalIso g hg M).hom.hom.hom m) φ =
      dualEquiv k H M φ ((g : H) • m) := by
  rw [unitEvalIso_hom_hom]
  exact dualEquiv_unitEvalEquiv_apply k H M g hg m φ

/-- The double dual comparison is natural: the double mate of `f` is its conjugate by the
comparison. -/
@[reassoc]
theorem unitEvalIso_hom_naturality {M N : FiniteHopfModuleCat k H} (f : M ⟶ N) :
    f ≫ (unitEvalIso g hg N).hom = (unitEvalIso g hg M).hom ≫ fᘁᘁ := by
  refine rightHom_ext (X := Nᘁ) ?_
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc]
  ext m φ
  rw [hom_hom_comp, LinearMap.comp_apply, hom_hom_comp, LinearMap.comp_apply, hom_hom_comp,
    LinearMap.comp_apply, hom_hom_comp, LinearMap.comp_apply, whiskerRight_tmul, whiskerRight_tmul,
    whiskerLeft_tmul, whiskerRight_tmul, evaluation_tmul, evaluation_tmul,
    dualEquiv_unitEvalIso_hom_apply, dualEquiv_unitEvalIso_hom_apply,
    dualEquiv_rightAdjointMate_apply, f.hom.hom.map_smul]

/-- The double dual comparisons `m ↦ (φ ↦ φ(g m))` as a natural isomorphism from the identity
functor to the double right dual functor. -/
def unitEvalNatIso : 𝟭 (FiniteHopfModuleCat k H) ≅ doubleRightDualFunctor _ :=
  NatIso.ofComponents (unitEvalIso g hg) (unitEvalIso_hom_naturality g hg)

/-- The components of `unitEvalNatIso` are the double dual comparisons. -/
@[simp]
theorem unitEvalNatIso_hom_app (M : FiniteHopfModuleCat k H) :
    (unitEvalNatIso g hg).hom.app M = (unitEvalIso g hg M).hom :=
  (rfl)

/-- The inverse components of `unitEvalNatIso` are the inverse double dual comparisons. -/
@[simp]
theorem unitEvalNatIso_inv_app (M : FiniteHopfModuleCat k H) :
    (unitEvalNatIso g hg).inv.app M = (unitEvalIso g hg M).inv :=
  (rfl)

variable {g}

/-- For group-like `g`, the double dual comparison at the unit object is the unit comparison of
the double right dual functor. -/
theorem unitEvalIso_unit_hom (hg₁ : IsGroupLikeElem k (g : H)) :
    (unitEvalIso g hg (𝟙_ (FiniteHopfModuleCat k H))).hom =
      ε (doubleRightDualFunctor (FiniteHopfModuleCat k H)) := by
  refine Eq.trans ?_ (doubleRightDualFunctor_ε _).symm
  -- The right dual of the unit is the one chosen by the rigid structure.
  refine rightHom_ext
    (X := (RightRigidCategory.rightDual (𝟙_ (FiniteHopfModuleCat k H))).rightDual) ?_
  -- Both sides become maps `𝟙_ ⊗ (𝟙_)ᘁ ⟶ 𝟙_`; the right side is the left unitor followed by the
  -- identification `(𝟙_)ᘁ ≅ 𝟙_`.
  rw [comp_whiskerRight, Category.assoc, rightMate_comp_evaluation, ← whisker_exchange_assoc,
    rightDualIso_inv_whiskerRight_evaluation, ExactPairing.unit_evaluation, ← unitors_equal,
    leftUnitor_naturality]
  ext c ψ
  rw [hom_hom_comp, LinearMap.comp_apply, whiskerRight_tmul, evaluation_tmul,
    dualEquiv_unitEvalIso_hom_apply, hom_hom_comp, LinearMap.comp_apply, leftUnitor_hom_tmul]
  -- The identification `(𝟙_)ᘁ ≅ 𝟙_` evaluates a functional at the unit of `k`.
  have hu := LinearMap.congr_fun (congrArg (fun f => f.hom.hom)
    (rightDualIso_hom_whiskerRight_evaluation
      (RightRigidCategory.rightDual (𝟙_ (FiniteHopfModuleCat k H))).exact exactPairingUnit))
    (tmul k H ((trivialEquiv k H) c • ψ) ((trivialEquiv k H).symm 1 :
      ↑(𝟙_ (FiniteHopfModuleCat k H))))
  rw [ExactPairing.unit_evaluation] at hu
  simp only [hom_hom_comp, LinearMap.comp_apply] at hu
  rw [whiskerRight_tmul, rightUnitor_hom_tmul, evaluation_tmul, LinearEquiv.apply_symm_apply,
    one_smul] at hu
  rw [hu]
  refine congrArg _ ?_
  -- `g` acts on the unit object by its counit, which is `1`.
  have hgc : (g : H) • c = (trivialEquiv k H) c • (trivialEquiv k H).symm 1 :=
    (trivialEquiv k H).injective <| by
      rw [trivialEquiv_smul, hg₁.counit_eq_one, one_mul, map_smul, LinearEquiv.apply_symm_apply,
        smul_eq_mul, mul_one]
  rw [hgc, map_smul]
  -- The scalar actions on `(𝟙_)ᘁ` and on the contragredient carrier agree definitionally.
  exact (LinearMap.congr_fun (map_smul (dualEquiv k H _) _ ψ) _).symm

/-- For group-like `g`, the double dual comparison of a tensor product is the tensor product of
the comparisons, followed by the tensor comparison of the double right dual functor. -/
theorem unitEvalIso_tensor_hom (hg₁ : IsGroupLikeElem k (g : H))
    (X Y : FiniteHopfModuleCat k H) :
    (unitEvalIso g hg (X ⊗ Y)).hom =
      ((unitEvalIso g hg X).hom ⊗ₘ (unitEvalIso g hg Y).hom) ≫
        μ (doubleRightDualFunctor _) X Y := by
  refine Eq.trans ?_ (congrArg (_ ≫ ·) (doubleRightDualFunctor_μ _ X Y).symm)
  refine rightHom_ext (X := (X ⊗ Y)ᘁ) ?_
  -- Evaluate both sides against `(X ⊗ Y)ᘁ`. On the right, the comparison
  -- `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` moves to the front and the evaluation becomes that of the tensor product
  -- pairing of `(Yᘁ, Yᘁᘁ)` and `(Xᘁ, Xᘁᘁ)`.
  rw [comp_whiskerRight, comp_whiskerRight, Category.assoc, Category.assoc,
    rightAdjointMate_comp_evaluation, ← whisker_exchange_assoc,
    rightDualTensorIso_inv_whiskerRight_evaluation, ← whisker_exchange_assoc]
  ext z ψ
  induction z using Tensor.inductionOn (R := k) (H := H) (M := X) (N := Y) with
  | hadd z z' hz hz' => rw [add_tmul, map_add, map_add, hz, hz']
  | htmul x y =>
    -- After the comparisons, the tensor product pairing of the double duals is the tensor product
    -- pairing of `(X, Xᘁ)` and `(Y, Yᘁ)` evaluated at `g x ⊗ g y`.
    have key (w : ↑((Yᘁ : FiniteHopfModuleCat k H) ⊗ (Xᘁ : FiniteHopfModuleCat k H))) :
        (ε_ ((Yᘁ : FiniteHopfModuleCat k H) ⊗ (Xᘁ : FiniteHopfModuleCat k H))
            (((Xᘁ : FiniteHopfModuleCat k H)ᘁ : FiniteHopfModuleCat k H) ⊗
              ((Yᘁ : FiniteHopfModuleCat k H)ᘁ : FiniteHopfModuleCat k H))).hom.hom
            (tmul k H (tmul k H ((unitEvalIso g hg X).hom.hom.hom x)
              ((unitEvalIso g hg Y).hom.hom.hom y)) w) =
          (ε_ (X ⊗ Y) ((Yᘁ : FiniteHopfModuleCat k H) ⊗ (Xᘁ : FiniteHopfModuleCat k H))).hom.hom
            (tmul k H w (tmul k H ((g : H) • x) ((g : H) • y) : ↑(X ⊗ Y))) := by
      induction w using Tensor.inductionOn (R := k) (H := H)
        (M := (Yᘁ : FiniteHopfModuleCat k H)) (N := (Xᘁ : FiniteHopfModuleCat k H)) with
      | hadd w w' hw hw' => rw [tmul_add, add_tmul, map_add, map_add, hw, hw']
      | htmul β α =>
        rw [tensor_evaluation_tmul, tensor_evaluation_tmul, dualEquiv_unitEvalIso_hom_apply,
          dualEquiv_unitEvalIso_hom_apply, mul_comm]
    -- The comparison `(X ⊗ Y)ᘁ ≅ Yᘁ ⊗ Xᘁ` carries the tensor product pairing to the evaluation
    -- of `(X ⊗ Y, (X ⊗ Y)ᘁ)`.
    have hψ := LinearMap.congr_fun (congrArg (fun f => f.hom.hom)
      (rightDualTensorIso_hom_whiskerRight_evaluation X Y))
      (tmul k H ψ (tmul k H ((g : H) • x) ((g : H) • y) : ↑(X ⊗ Y)))
    simp only [hom_hom_comp, LinearMap.comp_apply] at hψ
    rw [whiskerRight_tmul, evaluation_tmul] at hψ
    -- A group-like element acts diagonally on a tensor product.
    have hgxy : (g : H) • (tmul k H x y : ↑(X ⊗ Y)) = tmul k H ((g : H) • x) ((g : H) • y) :=
      (tensorEquiv k H X Y).injective <| by
        rw [tensorEquiv_smul_of_comul_eq_tmul hg₁.comul_eq_tmul_self]
        simp
    rw [hom_hom_comp, LinearMap.comp_apply, whiskerRight_tmul, evaluation_tmul,
      dualEquiv_unitEvalIso_hom_apply, hom_hom_comp, hom_hom_comp, LinearMap.comp_apply,
      LinearMap.comp_apply, whiskerLeft_tmul, whiskerRight_tmul, tensorHom_tmul, key, hψ, hgxy]

/-- For a group-like unit `g` implementing the square of the antipode, the double dual
comparisons `m ↦ (φ ↦ φ(g m))` form a monoidal natural isomorphism from the identity functor to
the double right dual functor. -/
theorem unitEvalNatIso_isMonoidal (hg₁ : IsGroupLikeElem k (g : H)) :
    NatTrans.IsMonoidal (unitEvalNatIso g hg).hom where
  -- The unit and tensor comparisons of the identity functor are identities.
  unit := (Category.id_comp _).trans (unitEvalIso_unit_hom hg hg₁)
  tensor X Y := (Category.id_comp _).trans (unitEvalIso_tensor_hom hg hg₁ X Y)

end TauCeti.FiniteHopfModuleCat
