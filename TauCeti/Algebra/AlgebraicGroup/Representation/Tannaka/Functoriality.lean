/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Map
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Representation.Tannaka.Equivalence
public import TauCeti.Algebra.Coalgebra.Convolution
public import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# Functoriality of Tannakian reconstruction in tensor functors

Let `U : FGComoduleCat R H₁ ⥤ FGComoduleCat R H₂` be a lax monoidal functor between categories
of finite comodules, together with a monoidal isomorphism

```text
e : U ⋙ forget₂ _ (SemimoduleCat R) ≅ forget₂ _ (SemimoduleCat R)
```

identifying the fibre of `U M` with the fibre of `M`. Conjugating by `e` transports a tensor
automorphism of scalar extension on `H₂`-comodules to one on `H₁`-comodules: its component at
`M` is the component at `U M`, read through `A ⊗ e_M`. This gives a group homomorphism
`tensorAutRestrict U e A`, compatible with change of the value algebra `A`; only the bialgebra
structures are used.

For commutative Hopf algebras over a field, tensor automorphisms of scalar extension are the
points of the coordinate Hopf algebra (`TauCeti.Tannaka.fgPointTensorIsoEquiv`). Restriction
along `U` therefore becomes a map of points `G₂(A) → G₁(A)`, natural in `A`, and so comes from a
bialgebra morphism `bialgHomOfFunctor U e : H₁ →ₐc[k] H₂` of coordinate algebras: on points it
is precomposition (`tensorAutRestrict_fgPointTensorIso`). Equivalently,
`bialgHomOfFunctor U e` is the unique bialgebra morphism `φ` for which every comparison `e_M` is
a comodule map from `U M` to `M` with coaction pushed forward along `φ`
(`eq_bialgHomOfFunctor_iff`). The identity functor gives the identity, and composing functors
composes the coordinate maps in the same order (`bialgHomOfFunctor_comp`), while the maps of
points, being precompositions, compose in the opposite order (`tensorAutRestrict_comp`,
`BialgHom.mapDomain_comp`).

## Main declarations

* `TauCeti.Tannaka.fiberLinearEquiv`: the fibre comparison of `e` at a comodule.
* `TauCeti.Tannaka.tensorAutRestrict`: restriction of tensor automorphisms along `U`.
* `TauCeti.Tannaka.tensorAutRestrict_id` and `TauCeti.Tannaka.tensorAutRestrict_comp`: its
  identity and composition laws.
* `TauCeti.Tannaka.bialgHomOfFunctor`: the induced morphism of coordinate Hopf algebras.
* `TauCeti.Tannaka.tensorAutRestrict_fgPointTensorIso` and
  `TauCeti.Tannaka.mapDomain_bialgHomOfFunctor`: on points it is restriction along `U`.
* `TauCeti.Tannaka.eq_bialgHomOfFunctor_iff`: its characterization by the coactions.
* `TauCeti.Tannaka.bialgHomOfFunctor_id` and `TauCeti.Tannaka.bialgHomOfFunctor_comp`: its
  identity and composition laws.

## References

* P. Deligne and J. S. Milne, *Tannakian categories*, §2, Corollary 2.9 and Proposition 2.21.
* J. S. Milne, *Algebraic Groups* (2017), §9.4.
-/

public section

open CategoryTheory MonoidalCategory WithConv
open scoped TensorProduct

namespace TauCeti.Tannaka

universe u v w x

section Restrict

variable {R : Type u} [CommSemiring R]
variable {H₁ : Type v} [Semiring H₁] [Bialgebra R H₁]
variable {H₂ : Type w} [Semiring H₂] [Bialgebra R H₂]
variable (U : FGComoduleCat.{u, v, u} R H₁ ⥤ FGComoduleCat.{u, w, u} R H₂)
variable (e : U ⋙ forget₂ (FGComoduleCat.{u, w, u} R H₂) (SemimoduleCat.{u} R) ≅
    forget₂ (FGComoduleCat.{u, v, u} R H₁) (SemimoduleCat.{u} R))

/-- The fibre comparison `e_M : U M ≃ M` of a natural isomorphism of fibre functors, as a linear
equivalence between the underlying modules of the comodules `U M` and `M`. -/
noncomputable def fiberLinearEquiv (M : FGComoduleCat.{u, v, u} R H₁) : U.obj M ≃ₗ[R] M :=
  (e.app M).toLinearEquivₛ

/-- The fibre comparison is the component of the natural isomorphism. -/
theorem fiberLinearEquiv_toLinearMap (M : FGComoduleCat.{u, v, u} R H₁) :
    (fiberLinearEquiv U e M).toLinearMap = (e.hom.app M).hom :=
  (rfl)

/-- Evaluation form of `fiberLinearEquiv_toLinearMap`. -/
theorem fiberLinearEquiv_apply (M : FGComoduleCat.{u, v, u} R H₁) (x : U.obj M) :
    fiberLinearEquiv U e M x = (e.hom.app M).hom x :=
  (rfl)

/-- The fibre comparisons are natural: they intertwine `U g` with `g`. -/
theorem fiberLinearEquiv_comp_map {M N : FGComoduleCat.{u, v, u} R H₁} (g : M ⟶ N) :
    (fiberLinearEquiv U e N).toLinearMap ∘ₗ (U.map g).hom.toLinearMap =
      g.hom.toLinearMap ∘ₗ (fiberLinearEquiv U e M).toLinearMap := by
  simpa [fiberLinearEquiv_toLinearMap] using
    congrArg SemimoduleCat.Hom.hom (e.hom.naturality g)

/-- For a monoidal comparison, the fibre comparison at `M ⊗ N` turns the tensorator of `U` into
the tensor product of the fibre comparisons at `M` and `N`. -/
theorem fiberLinearEquiv_comp_μ [U.LaxMonoidal] [NatTrans.IsMonoidal e.hom]
    (M N : FGComoduleCat.{u, v, u} R H₁) :
    (fiberLinearEquiv U e (M ⊗ N)).toLinearMap ∘ₗ
        (Functor.LaxMonoidal.μ U M N).hom.toLinearMap =
      TensorProduct.map (fiberLinearEquiv U e M).toLinearMap
        (fiberLinearEquiv U e N).toLinearMap := by
  have h := congrArg SemimoduleCat.Hom.hom (NatTrans.IsMonoidal.tensor (τ := e.hom) M N)
  -- The monoidal structure of the forgetful functors is induced, with identity tensorators.
  have hμ₂ (X Y : FGComoduleCat.{u, w, u} R H₂) :
      Functor.LaxMonoidal.μ (forget₂ (FGComoduleCat.{u, w, u} R H₂) (SemimoduleCat.{u} R)) X Y =
        𝟙 _ :=
    (rfl)
  have hμ₁ (X Y : FGComoduleCat.{u, v, u} R H₁) :
      Functor.LaxMonoidal.μ (forget₂ (FGComoduleCat.{u, v, u} R H₁) (SemimoduleCat.{u} R)) X Y =
        𝟙 _ :=
    (rfl)
  simp only [Functor.LaxMonoidal.comp_μ, hμ₁, hμ₂] at h
  -- After removing the identity tensorators, both sides are the stated linear maps up to the
  -- definitional identification of a comodule tensor product with the module tensor product.
  exact h

variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- The component at `M` of the restriction of a tensor automorphism `η` along `U`: the
component of `η` at `U M`, transported along `A ⊗ e_M`. -/
private noncomputable def restrictComponentGL
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H₂ A))
    (M : FGComoduleCat.{u, v, u} R H₁) :
    LinearMap.GeneralLinearGroup A (A ⊗[R] M) :=
  LinearMap.GeneralLinearGroup.congrLinearEquiv ((fiberLinearEquiv U e M).baseChange R A _ _)
    (scalarExtensionComponentGL R H₂ A η (U.obj M))

/-- The restricted component intertwines the original component at `U M` along `A ⊗ e_M`. -/
private theorem restrictComponentGL_comp_baseChange
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H₂ A))
    (M : FGComoduleCat.{u, v, u} R H₁) :
    (restrictComponentGL U e A η M : Module.End A (A ⊗[R] M)) ∘ₗ
        (fiberLinearEquiv U e M).toLinearMap.baseChange A =
      (fiberLinearEquiv U e M).toLinearMap.baseChange A ∘ₗ
        scalarExtensionComponent R H₂ A η (U.obj M) := by
  refine LinearMap.ext fun x => ?_
  have h := LinearEquiv.coe_baseChange R A _ _ (fiberLinearEquiv U e M)
  simp only [restrictComponentGL, LinearMap.GeneralLinearGroup.congrLinearEquiv_apply,
    LinearMap.GeneralLinearGroup.coe_ofLinearEquiv, LinearMap.coe_comp, Function.comp_apply]
  rw [← h]
  simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearMap.GeneralLinearGroup.coe_toLinearEquiv, scalarExtensionComponentGL_coe]

/-- The restricted components are natural in the comodule. -/
private theorem restrictComponentGL_natural
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H₂ A))
    {M N : FGComoduleCat.{u, v, u} R H₁} (g : M ⟶ N) :
    g.hom.toLinearMap.baseChange A ∘ₗ
        (restrictComponentGL U e A η M : Module.End A (A ⊗[R] M)) =
      (restrictComponentGL U e A η N : Module.End A (A ⊗[R] N)) ∘ₗ
        g.hom.toLinearMap.baseChange A := by
  refine (LinearMap.cancel_right
    (LinearMap.baseChange_surjective A (fiberLinearEquiv U e M).surjective)).mp ?_
  have hmap : (fiberLinearEquiv U e N).toLinearMap.baseChange A ∘ₗ
      (U.map g).hom.toLinearMap.baseChange A =
        g.hom.toLinearMap.baseChange A ∘ₗ (fiberLinearEquiv U e M).toLinearMap.baseChange A := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, fiberLinearEquiv_comp_map]
  refine LinearMap.ext fun y => ?_
  have h₁ := LinearMap.congr_fun (restrictComponentGL_comp_baseChange U e A η M) y
  have h₂ := LinearMap.congr_fun (restrictComponentGL_comp_baseChange U e A η N)
    ((U.map g).hom.toLinearMap.baseChange A y)
  have h₃ := LinearMap.congr_fun hmap y
  have h₄ := LinearMap.congr_fun hmap (scalarExtensionComponent R H₂ A η (U.obj M) y)
  have h₅ := LinearMap.congr_fun (scalarExtensionComponent_natural R H₂ A η (U.map g)) y
  simp only [LinearMap.coe_comp, Function.comp_apply] at h₁ h₂ h₃ h₄ h₅ ⊢
  rw [h₁, ← h₄, h₅, ← h₂, h₃]

/-- For a monoidal comparison, the restricted components are compatible with the tensor
comparison of scalar extensions. -/
private theorem restrictComponentGL_tensor [U.LaxMonoidal] [NatTrans.IsMonoidal e.hom]
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H₂ A))
    (M N : FGComoduleCat.{u, v, u} R H₁) :
    (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap.comp
        (TensorProduct.map (restrictComponentGL U e A η M : Module.End A (A ⊗[R] M))
          (restrictComponentGL U e A η N : Module.End A (A ⊗[R] N))) =
      (restrictComponentGL U e A η (M ⊗ N) :
        Module.End A (A ⊗[R] ((M ⊗ N : FGComoduleCat R H₁) : Type u))).comp
          (TensorProduct.AlgebraTensorModule.distribBaseChange R A M N).symm.toLinearMap := by
  refine TensorProduct.ext' fun x y => ?_
  obtain ⟨x, rfl⟩ := LinearMap.baseChange_surjective A (fiberLinearEquiv U e M).surjective x
  obtain ⟨y, rfl⟩ := LinearMap.baseChange_surjective A (fiberLinearEquiv U e N).surjective y
  have hμ (z : A ⊗[R] (U.obj M ⊗ U.obj N : FGComoduleCat R H₂)) :
      (TensorProduct.map (fiberLinearEquiv U e M).toLinearMap
          (fiberLinearEquiv U e N).toLinearMap).baseChange A z =
        (fiberLinearEquiv U e (M ⊗ N)).toLinearMap.baseChange A
          ((Functor.LaxMonoidal.μ U M N).hom.toLinearMap.baseChange A z) := by
    rw [← fiberLinearEquiv_comp_μ, LinearMap.baseChange_comp, LinearMap.comp_apply]
  have h₁ := LinearMap.congr_fun (restrictComponentGL_comp_baseChange U e A η M) x
  have h₂ := LinearMap.congr_fun (restrictComponentGL_comp_baseChange U e A η N) y
  have h₃ := LinearMap.congr_fun (restrictComponentGL_comp_baseChange U e A η (M ⊗ N))
    ((Functor.LaxMonoidal.μ U M N).hom.toLinearMap.baseChange A
      ((TensorProduct.AlgebraTensorModule.distribBaseChange R A _ _).symm (x ⊗ₜ[A] y)))
  have h₄ := LinearMap.congr_fun
    (scalarExtensionComponent_natural R H₂ A η (Functor.LaxMonoidal.μ U M N))
    ((TensorProduct.AlgebraTensorModule.distribBaseChange R A _ _).symm (x ⊗ₜ[A] y))
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    TensorProduct.map_tmul] at h₁ h₂ h₃ h₄ ⊢
  -- Move both fibre comparisons out through the tensor comparison, then use the tensor law and
  -- the naturality of `η` along the tensorator of `U`.
  rw [h₁, h₂,
    TensorProduct.AlgebraTensorModule.distribBaseChange_symm_baseChange_tmul_baseChange,
    TensorProduct.AlgebraTensorModule.distribBaseChange_symm_baseChange_tmul_baseChange, hμ, hμ,
    h₃, ← scalarExtensionComponent_tensor, h₄]

variable [U.LaxMonoidal] [NatTrans.IsMonoidal e.hom]

/-- Restriction of tensor automorphisms of scalar extension along a lax monoidal functor `U`
whose fibres are identified with the original fibres by the monoidal isomorphism `e`: the
component at `M` is the component at `U M`, transported along `A ⊗ e_M`. -/
noncomputable def tensorAutRestrict :
    Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H₂ A) →*
      Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H₁ A) where
  toFun η := monoidalAutOfComponents R H₁ A (restrictComponentGL U e A η)
    (restrictComponentGL_natural U e A η) (restrictComponentGL_tensor U e A η)
  map_one' := by
    refine scalarExtensionComponent_ext _ _ _ _ _ fun M => ?_
    refine (LinearMap.cancel_right
      (LinearMap.baseChange_surjective A (fiberLinearEquiv U e M).surjective)).mp ?_
    rw [scalarExtensionComponent_monoidalAutOfComponents, restrictComponentGL_comp_baseChange,
      scalarExtensionComponent_one, scalarExtensionComponent_one, LinearMap.id_comp,
      LinearMap.comp_id]
  map_mul' η θ := by
    refine scalarExtensionComponent_ext _ _ _ _ _ fun M => ?_
    refine (LinearMap.cancel_right
      (LinearMap.baseChange_surjective A (fiberLinearEquiv U e M).surjective)).mp ?_
    rw [scalarExtensionComponent_mul, scalarExtensionComponent_monoidalAutOfComponents,
      scalarExtensionComponent_monoidalAutOfComponents,
      scalarExtensionComponent_monoidalAutOfComponents, restrictComponentGL_comp_baseChange,
      LinearMap.comp_assoc, restrictComponentGL_comp_baseChange, ← LinearMap.comp_assoc,
      restrictComponentGL_comp_baseChange, scalarExtensionComponent_mul, LinearMap.comp_assoc]

/-- The characteristic property of restriction: the component at `M` of the restricted tensor
automorphism corresponds to the component at `U M` along `A ⊗ e_M`. Since `A ⊗ e_M` is
surjective, this determines the restriction. -/
theorem scalarExtensionComponent_tensorAutRestrict_comp_baseChange
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H₂ A))
    (M : FGComoduleCat.{u, v, u} R H₁) :
    scalarExtensionComponent R H₁ A (tensorAutRestrict U e A η) M ∘ₗ
        (fiberLinearEquiv U e M).toLinearMap.baseChange A =
      (fiberLinearEquiv U e M).toLinearMap.baseChange A ∘ₗ
        scalarExtensionComponent R H₂ A η (U.obj M) := by
  rw [tensorAutRestrict, MonoidHom.coe_mk, OneHom.coe_mk,
    scalarExtensionComponent_monoidalAutOfComponents, restrictComponentGL_comp_baseChange]

/-- The component at `M` of the restricted tensor automorphism is the component at `U M`,
conjugated by `A ⊗ e_M`. -/
@[simp]
theorem scalarExtensionComponent_tensorAutRestrict
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H₂ A))
    (M : FGComoduleCat.{u, v, u} R H₁) :
    scalarExtensionComponent R H₁ A (tensorAutRestrict U e A η) M =
      ((fiberLinearEquiv U e M).baseChange R A _ _).toLinearMap ∘ₗ
        scalarExtensionComponent R H₂ A η (U.obj M) ∘ₗ
          ((fiberLinearEquiv U e M).baseChange R A _ _).symm.toLinearMap := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨y, rfl⟩ := ((fiberLinearEquiv U e M).baseChange R A _ _).surjective y
  have h := LinearMap.congr_fun
    (scalarExtensionComponent_tensorAutRestrict_comp_baseChange U e A η M) y
  rw [← LinearEquiv.coe_baseChange] at h
  simpa only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply] using h

variable (B : Type u) [CommSemiring B] [Algebra R B]

/-- Restriction along `U` commutes with base change of tensor automorphisms along a morphism of
value algebras. -/
theorem tensorAutMapValue_tensorAutRestrict (f : A →ₐ[R] B)
    (η : Aut (FGComoduleCat.scalarExtensionMonoidalFunctor R H₂ A)) :
    tensorAutMapValue R H₁ A B f (tensorAutRestrict U e A η) =
      tensorAutRestrict U e B (tensorAutMapValue R H₂ A B f η) := by
  refine scalarExtensionComponent_ext _ _ _ _ _ fun M => ?_
  refine ((LinearMap.cancel_right
    (LinearMap.baseChange_surjective B (fiberLinearEquiv U e M).surjective)).mp ?_).symm
  rw [scalarExtensionComponent_tensorAutRestrict_comp_baseChange,
    scalarExtensionComponent_tensorAutMapValue, scalarExtensionComponent_tensorAutMapValue]
  exact Module.End.baseChange_comp_mapValue f _ _ _
    (scalarExtensionComponent_tensorAutRestrict_comp_baseChange U e A η M).symm

end Restrict

section Laws

variable {R : Type u} [CommSemiring R]
variable {H₁ : Type v} [Semiring H₁] [Bialgebra R H₁]
variable {H₂ : Type w} [Semiring H₂] [Bialgebra R H₂]
variable {H₃ : Type x} [Semiring H₃] [Bialgebra R H₃]
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- The fibre comparison of the identity functor is the identity. -/
@[simp]
theorem fiberLinearEquiv_id (M : FGComoduleCat.{u, v, u} R H₁) :
    fiberLinearEquiv (𝟭 _) (Functor.leftUnitor _) M = LinearEquiv.refl R M := by
  ext x
  rw [fiberLinearEquiv_apply, Functor.leftUnitor_hom_app]
  simp

variable (U₁ : FGComoduleCat.{u, v, u} R H₁ ⥤ FGComoduleCat.{u, w, u} R H₂)
  (e₁ : U₁ ⋙ forget₂ (FGComoduleCat.{u, w, u} R H₂) (SemimoduleCat.{u} R) ≅
    forget₂ (FGComoduleCat.{u, v, u} R H₁) (SemimoduleCat.{u} R))
  (U₂ : FGComoduleCat.{u, w, u} R H₂ ⥤ FGComoduleCat.{u, x, u} R H₃)
  (e₂ : U₂ ⋙ forget₂ (FGComoduleCat.{u, x, u} R H₃) (SemimoduleCat.{u} R) ≅
    forget₂ (FGComoduleCat.{u, w, u} R H₂) (SemimoduleCat.{u} R))

/-- The fibre comparison of a composite functor is the composite of the fibre comparisons. -/
@[simp]
theorem fiberLinearEquiv_comp (M : FGComoduleCat.{u, v, u} R H₁) :
    fiberLinearEquiv (U₁ ⋙ U₂)
        (Functor.associator U₁ U₂ _ ≪≫ Functor.isoWhiskerLeft U₁ e₂ ≪≫ e₁) M =
      (fiberLinearEquiv U₂ e₂ (U₁.obj M)).trans (fiberLinearEquiv U₁ e₁ M) := by
  ext x
  simp [fiberLinearEquiv_apply]

/-- The composite of monoidal fibre comparisons is monoidal. -/
instance isMonoidal_comp_fiberIso [U₁.LaxMonoidal] [NatTrans.IsMonoidal e₁.hom] [U₂.LaxMonoidal]
    [NatTrans.IsMonoidal e₂.hom] :
    NatTrans.IsMonoidal
      (Functor.associator U₁ U₂ _ ≪≫ Functor.isoWhiskerLeft U₁ e₂ ≪≫ e₁).hom := by
  rw [Iso.trans_hom, Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

/-- Restriction along the identity functor is the identity. -/
@[simp]
theorem tensorAutRestrict_id :
    tensorAutRestrict (𝟭 (FGComoduleCat.{u, v, u} R H₁)) (Functor.leftUnitor _) A =
      MonoidHom.id _ := by
  refine MonoidHom.ext fun η => scalarExtensionComponent_ext _ _ _ _ _ fun M => ?_
  have h := scalarExtensionComponent_tensorAutRestrict_comp_baseChange (𝟭 _)
    (Functor.leftUnitor _) A η M
  rw [← LinearEquiv.coe_baseChange, fiberLinearEquiv_id] at h
  simpa using h

/-- Restriction along a composite functor is the composite of the restrictions, in the opposite
order. -/
theorem tensorAutRestrict_comp [U₁.LaxMonoidal] [NatTrans.IsMonoidal e₁.hom] [U₂.LaxMonoidal]
    [NatTrans.IsMonoidal e₂.hom] :
    tensorAutRestrict (U₁ ⋙ U₂)
        (Functor.associator U₁ U₂ _ ≪≫ Functor.isoWhiskerLeft U₁ e₂ ≪≫ e₁) A =
      (tensorAutRestrict U₁ e₁ A).comp (tensorAutRestrict U₂ e₂ A) := by
  refine MonoidHom.ext fun η => scalarExtensionComponent_ext _ _ _ _ _ fun M => ?_
  refine (LinearMap.cancel_right (LinearMap.baseChange_surjective A
    (fiberLinearEquiv (U₁ ⋙ U₂)
      (Functor.associator U₁ U₂ _ ≪≫ Functor.isoWhiskerLeft U₁ e₂ ≪≫ e₁) M).surjective)).mp ?_
  rw [scalarExtensionComponent_tensorAutRestrict_comp_baseChange, fiberLinearEquiv_comp,
    LinearEquiv.coe_trans, LinearMap.baseChange_comp, MonoidHom.comp_apply]
  conv_rhs => rw [← LinearMap.comp_assoc,
    scalarExtensionComponent_tensorAutRestrict_comp_baseChange, LinearMap.comp_assoc,
    scalarExtensionComponent_tensorAutRestrict_comp_baseChange]
  -- The two sides differ only by `(U₁ ⋙ U₂).obj M = U₂.obj (U₁.obj M)`, which holds by
  -- definition of composition of functors.
  rfl

end Laws

section PointEnd

variable {R : Type u} [CommSemiring R]
variable {H₁ : Type v} [Semiring H₁] [Bialgebra R H₁]
variable {H₂ : Type w} [Semiring H₂] [Bialgebra R H₂]
variable (U : FGComoduleCat.{u, v, u} R H₁ ⥤ FGComoduleCat.{u, w, u} R H₂)
variable (e : U ⋙ forget₂ (FGComoduleCat.{u, w, u} R H₂) (SemimoduleCat.{u} R) ≅
    forget₂ (FGComoduleCat.{u, v, u} R H₁) (SemimoduleCat.{u} R))
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- If the fibre comparison `e_M` is a comodule map from `U M` to `M` with coaction pushed
forward along `ψ`, then it intertwines the action of a point `g` on `U M` with the action of
`g ∘ ψ` on `M`. -/
theorem baseChange_comp_endOfPoint_of_coact (ψ : H₁ →ₐc[R] H₂)
    (M : FGComoduleCat.{u, v, u} R H₁)
    (hψ : ∀ x : U.obj M,
      (fiberLinearEquiv U e M).toLinearMap.rTensor H₂ (Comodule.coact (R := R) (C := H₂) x) =
        (ψ : H₁ →ₗ[R] H₂).lTensor M
          (Comodule.coact (R := R) (C := H₁) (fiberLinearEquiv U e M x)))
    (g : H₂ →ₐ[R] A) :
    (fiberLinearEquiv U e M).toLinearMap.baseChange A ∘ₗ Comodule.endOfPoint (U.obj M) g =
      Comodule.endOfPoint M (g.comp (ψ : H₁ →ₐ[R] H₂)) ∘ₗ
        (fiberLinearEquiv U e M).toLinearMap.baseChange A := by
  let : Comodule R H₂ M := Comodule.Corestrict ψ.toCoalgHom
  have hψ' : (ψ.toCoalgHom : H₁ →ₗ[R] H₂) = (ψ : H₁ →ₗ[R] H₂) :=
    LinearMap.ext fun x => BialgHom.toCoalgHom_apply ψ x
  -- The hypothesis says that `e_M` is a comodule morphism to the corestriction of `M`.
  let f : Comodule.Hom R H₂ (U.obj M) M :=
    { toLinearMap := (fiberLinearEquiv U e M).toLinearMap
      map_coact := LinearMap.ext fun x => by
        simpa [Comodule.corestrict_coact_apply, LinearMap.rTensor, LinearMap.lTensor, hψ']
          using hψ x }
  have h := Comodule.baseChange_comp_endOfPoint (A := A) f g
  rwa [Comodule.endOfPoint_corestrict] at h

end PointEnd

section Points

variable {R : Type u} [CommSemiring R]
variable {H₁ : Type v} [Semiring H₁] [HopfAlgebra R H₁]
variable {H₂ : Type w} [Semiring H₂] [HopfAlgebra R H₂]
variable (U : FGComoduleCat.{u, v, u} R H₁ ⥤ FGComoduleCat.{u, w, u} R H₂)
variable (e : U ⋙ forget₂ (FGComoduleCat.{u, w, u} R H₂) (SemimoduleCat.{u} R) ≅
    forget₂ (FGComoduleCat.{u, v, u} R H₁) (SemimoduleCat.{u} R))
variable (A : Type u) [CommSemiring A] [Algebra R A]

/-- If every fibre comparison `e_M` is a comodule map from `U M` to `M` with coaction pushed
forward along `ψ`, then restriction along `U` acts on points by precomposition with `ψ`. -/
theorem tensorAutRestrict_fgPointTensorIso_of_coact [U.LaxMonoidal] [NatTrans.IsMonoidal e.hom]
    (ψ : H₁ →ₐc[R] H₂)
    (hψ : ∀ (M : FGComoduleCat.{u, v, u} R H₁) (x : U.obj M),
      (fiberLinearEquiv U e M).toLinearMap.rTensor H₂ (Comodule.coact (R := R) (C := H₂) x) =
        (ψ : H₁ →ₗ[R] H₂).lTensor M
          (Comodule.coact (R := R) (C := H₁) (fiberLinearEquiv U e M x)))
    (g : WithConv (H₂ →ₐ[R] A)) :
    tensorAutRestrict U e A (fgPointTensorIso R H₂ A g) =
      fgPointTensorIso R H₁ A (ψ.mapDomain g) := by
  refine scalarExtensionComponent_ext _ _ _ _ _ fun M => ?_
  refine (LinearMap.cancel_right
    (LinearMap.baseChange_surjective A (fiberLinearEquiv U e M).surjective)).mp ?_
  rw [scalarExtensionComponent_tensorAutRestrict_comp_baseChange,
    scalarExtensionComponent_fgPointTensorIso, scalarExtensionComponent_fgPointTensorIso,
    Comodule.pointsAction_toLinearMap, Comodule.pointsAction_toLinearMap,
    BialgHom.mapDomain_apply, WithConv.ofConv_toConv]
  exact baseChange_comp_endOfPoint_of_coact U e A ψ M (hψ M) g.ofConv

end Points

section Field

variable {k : Type u} [Field k]
variable {H₁ : Type u} [CommRing H₁] [HopfAlgebra k H₁]
variable {H₂ : Type u} [CommRing H₂] [HopfAlgebra k H₂]
variable (U : FGComoduleCat.{u, u, u} k H₁ ⥤ FGComoduleCat.{u, u, u} k H₂) [U.LaxMonoidal]
variable (e : U ⋙ forget₂ (FGComoduleCat.{u, u, u} k H₂) (SemimoduleCat.{u} k) ≅
    forget₂ (FGComoduleCat.{u, u, u} k H₁) (SemimoduleCat.{u} k)) [NatTrans.IsMonoidal e.hom]

/-- The algebra map underlying `bialgHomOfFunctor`: the point of `H₁` with values in `H₂`
reconstructed from the restriction of the universal point of `H₂`. -/
private noncomputable def algHomOfFunctor : H₁ →ₐ[k] H₂ :=
  (reconstructedPoint k H₁ H₂
    (tensorAutRestrict U e H₂ (fgPointTensorIso k H₂ H₂ (toConv (AlgHom.id k H₂))))).ofConv

private theorem tensorAutRestrict_fgPointTensorIso_algHomOfFunctor
    (A : Type u) [CommRing A] [Algebra k A] (g : WithConv (H₂ →ₐ[k] A)) :
    tensorAutRestrict U e A (fgPointTensorIso k H₂ A g) =
      fgPointTensorIso k H₁ A (toConv (g.ofConv.comp (algHomOfFunctor U e))) := by
  -- `g` is the base change of the universal point along `g` itself.
  have hg : AlgHom.mapValue g.ofConv (toConv (AlgHom.id k H₂)) = g := by
    rw [AlgHom.mapValue_apply, ofConv_toConv, AlgHom.comp_id, toConv_ofConv]
  conv_lhs => rw [← hg]
  rw [← tensorAutMapValue_fgPointTensorIso, ← tensorAutMapValue_tensorAutRestrict,
    ← fgPointTensorIso_reconstructedPoint k H₁ H₂
      (tensorAutRestrict U e H₂ (fgPointTensorIso k H₂ H₂ (toConv (AlgHom.id k H₂)))),
    tensorAutMapValue_fgPointTensorIso, AlgHom.mapValue_apply, ofConv_toConv, algHomOfFunctor]

private theorem counitAlgHom_comp_algHomOfFunctor :
    (Bialgebra.counitAlgHom k H₂).comp (algHomOfFunctor U e) = Bialgebra.counitAlgHom k H₁ := by
  have h := tensorAutRestrict_fgPointTensorIso_algHomOfFunctor U e k 1
  rw [← fgPointTensorIsoHom_apply, map_one, map_one, ← map_one (fgPointTensorIsoHom k H₁ k),
    fgPointTensorIsoHom_apply] at h
  have h' := congrArg ofConv
    (Function.LeftInverse.injective (reconstructedPoint_fgPointTensorIso k H₁ k) h)
  rwa [ofConv_toConv, Bialgebra.ofConv_one_eq_counitAlgHom,
    Bialgebra.ofConv_one_eq_counitAlgHom, eq_comm] at h'

private theorem map_comp_comulAlgHom_algHomOfFunctor :
    (Algebra.TensorProduct.map (algHomOfFunctor U e) (algHomOfFunctor U e)).comp
        (Bialgebra.comulAlgHom k H₁) =
      (Bialgebra.comulAlgHom k H₂).comp (algHomOfFunctor U e) := by
  let l : WithConv (H₂ →ₐ[k] H₂ ⊗[k] H₂) := toConv Algebra.TensorProduct.includeLeft
  let r : WithConv (H₂ →ₐ[k] H₂ ⊗[k] H₂) := toConv Algebra.TensorProduct.includeRight
  -- Restriction is multiplicative, so it carries the product `l * r` of the two universal points,
  -- which is the comultiplication, to the product of the restrictions of `l` and `r`.
  have hmul : tensorAutRestrict U e (H₂ ⊗[k] H₂) (fgPointTensorIso k H₂ _ (l * r)) =
      fgPointTensorIso k H₁ _ (toConv (l.ofConv.comp (algHomOfFunctor U e)) *
        toConv (r.ofConv.comp (algHomOfFunctor U e))) := by
    rw [← fgPointTensorIsoHom_apply, map_mul, map_mul, fgPointTensorIsoHom_apply,
      fgPointTensorIsoHom_apply, tensorAutRestrict_fgPointTensorIso_algHomOfFunctor,
      tensorAutRestrict_fgPointTensorIso_algHomOfFunctor, ← fgPointTensorIsoHom_apply,
      ← fgPointTensorIsoHom_apply, ← map_mul, fgPointTensorIsoHom_apply]
  have h := Function.LeftInverse.injective (reconstructedPoint_fgPointTensorIso k H₁ _)
    ((tensorAutRestrict_fgPointTensorIso_algHomOfFunctor U e _ (l * r)).symm.trans hmul)
  rw [← Bialgebra.comulPoint_eq_include_mul, ofConv_toConv] at h
  rw [← ofConv_toConv ((Algebra.TensorProduct.map _ _).comp _), Bialgebra.toConv_comp_comulAlgHom,
    Algebra.TensorProduct.map_comp_includeLeft, Algebra.TensorProduct.map_comp_includeRight]
  exact congrArg ofConv h.symm

/-- The morphism of coordinate Hopf algebras induced by a lax monoidal functor
`U : FGComoduleCat k H₁ ⥤ FGComoduleCat k H₂` with a monoidal identification `e` of fibre
functors. On points it is restriction of tensor automorphisms along `U`
(`tensorAutRestrict_fgPointTensorIso`), and it is characterized by the coactions in
`eq_bialgHomOfFunctor_iff`. -/
noncomputable def bialgHomOfFunctor : H₁ →ₐc[k] H₂ :=
  BialgHom.ofAlgHom (algHomOfFunctor U e) (counitAlgHom_comp_algHomOfFunctor U e)
    (map_comp_comulAlgHom_algHomOfFunctor U e)

private theorem toAlgHom_bialgHomOfFunctor :
    (bialgHomOfFunctor U e : H₁ →ₐ[k] H₂) = algHomOfFunctor U e :=
  AlgHom.ext fun x => by simp [bialgHomOfFunctor]

/-- Restriction along `U` acts on points by precomposition with `bialgHomOfFunctor U e`. -/
@[simp]
theorem tensorAutRestrict_fgPointTensorIso (A : Type u) [CommRing A] [Algebra k A]
    (g : WithConv (H₂ →ₐ[k] A)) :
    tensorAutRestrict U e A (fgPointTensorIso k H₂ A g) =
      fgPointTensorIso k H₁ A ((bialgHomOfFunctor U e).mapDomain g) := by
  rw [BialgHom.mapDomain_apply, toAlgHom_bialgHomOfFunctor]
  exact tensorAutRestrict_fgPointTensorIso_algHomOfFunctor U e A g

/-- The map of points induced by `bialgHomOfFunctor U e` is restriction of tensor automorphisms
along `U`, read through Tannakian reconstruction. -/
theorem mapDomain_bialgHomOfFunctor (A : Type u) [CommRing A] [Algebra k A] :
    (bialgHomOfFunctor U e).mapDomain =
      ((fgPointTensorIsoEquiv k H₁ A).symm.toMonoidHom.comp (tensorAutRestrict U e A)).comp
        (fgPointTensorIsoEquiv k H₂ A).toMonoidHom := by
  refine MonoidHom.ext fun g => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.coe_toMonoidHom, fgPointTensorIsoEquiv_apply, tensorAutRestrict_fgPointTensorIso,
    ← fgPointTensorIsoEquiv_apply, MulEquiv.symm_apply_apply]

/-- Every fibre comparison `e_M` is a comodule map from `U M` to `M` with coaction pushed forward
along `bialgHomOfFunctor U e`. -/
theorem rTensor_coact_fiberLinearEquiv (M : FGComoduleCat.{u, u, u} k H₁) (x : U.obj M) :
    (fiberLinearEquiv U e M).toLinearMap.rTensor H₂ (Comodule.coact (R := k) (C := H₂) x) =
      (bialgHomOfFunctor U e : H₁ →ₗ[k] H₂).lTensor M
        (Comodule.coact (R := k) (C := H₁) (fiberLinearEquiv U e M x)) := by
  -- Evaluate the action of the universal point of `H₂` on `U M` at `1 ⊗ x`: it is the coaction.
  have h := LinearMap.congr_fun (scalarExtensionComponent_tensorAutRestrict_comp_baseChange U e H₂
    (fgPointTensorIso k H₂ H₂ (toConv (AlgHom.id k H₂))) M) (1 ⊗ₜ[k] x)
  rw [tensorAutRestrict_fgPointTensorIso, scalarExtensionComponent_fgPointTensorIso,
    scalarExtensionComponent_fgPointTensorIso] at h
  have hφ : (bialgHomOfFunctor U e : H₁ →ₐ[k] H₂).toLinearMap =
      (bialgHomOfFunctor U e : H₁ →ₗ[k] H₂) :=
    BialgHom.toAlgHom_toLinearMap _
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
    Comodule.pointsAction_toLinearMap, LinearMap.baseChange_tmul, Comodule.endOfPoint_tmul,
    one_smul, BialgHom.mapDomain_apply, AlgHom.id_comp, AlgHom.toLinearMap_id,
    LinearMap.lTensor_id, LinearMap.id_apply, hφ] at h
  rw [LinearMap.baseChange_eq_lTensor, LinearMap.lTensor_comm] at h
  exact (TensorProduct.comm k _ _).injective h.symm

/-- `bialgHomOfFunctor U e` is the unique bialgebra morphism `ψ` for which every fibre comparison
`e_M` is a comodule map from `U M` to `M` with coaction pushed forward along `ψ`. -/
theorem eq_bialgHomOfFunctor_iff (ψ : H₁ →ₐc[k] H₂) :
    ψ = bialgHomOfFunctor U e ↔ ∀ (M : FGComoduleCat.{u, u, u} k H₁) (x : U.obj M),
      (fiberLinearEquiv U e M).toLinearMap.rTensor H₂ (Comodule.coact (R := k) (C := H₂) x) =
        (ψ : H₁ →ₗ[k] H₂).lTensor M
          (Comodule.coact (R := k) (C := H₁) (fiberLinearEquiv U e M x)) := by
  refine ⟨fun h => h ▸ rTensor_coact_fiberLinearEquiv U e, fun hψ => ?_⟩
  -- Both maps induce the same restriction of the universal point of `H₂`.
  have h := congrArg ofConv
    (Function.LeftInverse.injective (reconstructedPoint_fgPointTensorIso k H₁ H₂)
      ((tensorAutRestrict_fgPointTensorIso_of_coact U e H₂ ψ hψ
          (toConv (AlgHom.id k H₂))).symm.trans
        (tensorAutRestrict_fgPointTensorIso U e H₂ (toConv (AlgHom.id k H₂)))))
  simp only [BialgHom.mapDomain_apply, ofConv_toConv, AlgHom.id_comp] at h
  exact BialgHom.ext fun x => DFunLike.congr_fun h x

/-- The identity functor induces the identity of coordinate Hopf algebras. -/
@[simp]
theorem bialgHomOfFunctor_id :
    bialgHomOfFunctor (𝟭 (FGComoduleCat.{u, u, u} k H₁)) (Functor.leftUnitor _) =
      BialgHom.id k H₁ := by
  refine ((eq_bialgHomOfFunctor_iff _ _ _).mpr fun M x => ?_).symm
  have hid : ((BialgHom.id k H₁ : H₁ →ₐc[k] H₁) : H₁ →ₗ[k] H₁) = LinearMap.id :=
    LinearMap.ext fun _ => by simp
  simp [hid]

variable {H₃ : Type u} [CommRing H₃] [HopfAlgebra k H₃]

/-- A composite of functors induces the composite of the coordinate maps, in the same order. -/
theorem bialgHomOfFunctor_comp
    (U₁ : FGComoduleCat.{u, u, u} k H₁ ⥤ FGComoduleCat.{u, u, u} k H₂) [U₁.LaxMonoidal]
    (e₁ : U₁ ⋙ forget₂ (FGComoduleCat.{u, u, u} k H₂) (SemimoduleCat.{u} k) ≅
      forget₂ (FGComoduleCat.{u, u, u} k H₁) (SemimoduleCat.{u} k)) [NatTrans.IsMonoidal e₁.hom]
    (U₂ : FGComoduleCat.{u, u, u} k H₂ ⥤ FGComoduleCat.{u, u, u} k H₃) [U₂.LaxMonoidal]
    (e₂ : U₂ ⋙ forget₂ (FGComoduleCat.{u, u, u} k H₃) (SemimoduleCat.{u} k) ≅
      forget₂ (FGComoduleCat.{u, u, u} k H₂) (SemimoduleCat.{u} k)) [NatTrans.IsMonoidal e₂.hom] :
    bialgHomOfFunctor (U₁ ⋙ U₂)
        (Functor.associator U₁ U₂ _ ≪≫ Functor.isoWhiskerLeft U₁ e₂ ≪≫ e₁) =
      (bialgHomOfFunctor U₂ e₂).comp (bialgHomOfFunctor U₁ e₁) := by
  refine ((eq_bialgHomOfFunctor_iff _ _ _).mpr fun M x => ?_).symm
  rw [fiberLinearEquiv_comp, LinearEquiv.coe_trans, LinearMap.rTensor_comp, LinearMap.comp_apply,
    rTensor_coact_fiberLinearEquiv]
  have hcomp : (((bialgHomOfFunctor U₂ e₂).comp (bialgHomOfFunctor U₁ e₁) : H₁ →ₐc[k] H₃) :
      H₁ →ₗ[k] H₃) = (bialgHomOfFunctor U₂ e₂ : H₂ →ₗ[k] H₃) ∘ₗ
        (bialgHomOfFunctor U₁ e₁ : H₁ →ₗ[k] H₂) :=
    LinearMap.ext fun _ => by simp
  -- Commute the fibre comparison of `U₁` past the coordinate map of `U₂`.
  have hswap := LinearMap.congr_fun ((LinearMap.rTensor_comp_lTensor
      (f := (fiberLinearEquiv U₁ e₁ M).toLinearMap)
      (g := (bialgHomOfFunctor U₂ e₂ : H₂ →ₗ[k] H₃))).trans
    (LinearMap.lTensor_comp_rTensor (f := (fiberLinearEquiv U₁ e₁ M).toLinearMap)
      (g := (bialgHomOfFunctor U₂ e₂ : H₂ →ₗ[k] H₃))).symm)
    (Comodule.coact (R := k) (C := H₂) (fiberLinearEquiv U₂ e₂ (U₁.obj M) x))
  rw [LinearMap.comp_apply, LinearMap.comp_apply] at hswap
  rw [hswap, rTensor_coact_fiberLinearEquiv, hcomp, LinearMap.lTensor_comp, LinearMap.comp_apply,
    LinearEquiv.trans_apply]

end Field

end TauCeti.Tannaka
