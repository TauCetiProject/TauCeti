/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Finite
public import TauCeti.Algebra.Coalgebra.Comodule.Hom
public import TauCeti.Algebra.HopfAlgebra.FiniteDual.Basic
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# Modules over a finite algebra as comodules over its dual coalgebra

Let `A` be an algebra over a commutative semiring `R` which is finite and projective as an
`R`-module. Its linear dual `ConvolutionDual R A` is a coalgebra, with comultiplication and counit
transposed from the multiplication and unit of `A`. This file identifies left `A`-modules with
right comodules over this dual coalgebra. A left module `M` gets the coaction

```text
ρ(m) = ∑ᵢ eᵢ • m ⊗ eᵢ^∨
```

for any basis `eᵢ` of `A` (when `A` is free) with dual basis `eᵢ^∨`. The coaction is defined
without a basis: it is the unique coaction whose contraction against evaluation at `x : A` is
`m ↦ x • m`. Conversely, contracting a coaction against evaluation at `x` defines the action of
`x`. Both directions come from `TauCeti.Comodule.convolutionActionEquiv`, which identifies
coactions of a finite projective coalgebra with actions of its convolution dual, and from
`TauCeti.ConvolutionDual.evalAlgEquiv`, which identifies `A` with the convolution dual of
`ConvolutionDual R A`.

These are the local pieces of the passage from representations of a finite diagram to finite
comodules: the compatible endomorphism algebra of a finite piece of a diagram representation is a
finite-dimensional algebra, and its modules are recovered as comodules over its dual coalgebra.

## Main declarations

* `TauCeti.Comodule.finiteAlgebraActionEquiv`: coactions of the dual coalgebra correspond to
  algebra actions of `A`.
* `TauCeti.Comodule.ofFiniteAlgebraModule`: the right comodule attached to a left `A`-module.
* `TauCeti.Comodule.ofFiniteAlgebraModule_coact_eq_sum`: the coaction in a basis of `A`.
* `TauCeti.Comodule.finiteAlgebraModule`: the left `A`-module attached to a right comodule.
* `TauCeti.Comodule.Hom.finiteAlgebraLinearEquiv`: comodule morphisms are the `A`-linear maps.

The categorical form, the equivalence between left `A`-modules and right comodules over the dual
coalgebra of `A` over a commutative ring, is `TauCeti.ComoduleCat.equivalenceModuleCat` in
`TauCeti.Algebra.Coalgebra.Comodule.Convolution.DualCoalgebra`.

## References

* A. Huber and S. Müller-Stach, *Periods and Nori motives* (2017), §7.2, the module/comodule
  correspondence for the dual coalgebra of a finite-dimensional algebra.
* M. Sweedler, *Hopf Algebras*, Chapter 2, comodules and modules over the dual algebra.
-/

public noncomputable section

open scoped TensorProduct
open TensorProduct WithConv

namespace TauCeti.Comodule

section Semiring

variable {R A M N : Type*} [CommSemiring R] [Semiring A] [Algebra R A]
  [Module.Finite R A] [Module.Projective R A]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

variable (R A M) in
/-- Right coactions of the dual coalgebra of a finite projective algebra `A` correspond bijectively
to algebra actions of `A`. -/
def finiteAlgebraActionEquiv :
    Comodule R (ConvolutionDual R A) M ≃ (A →ₐ[R] Module.End R M) :=
  (convolutionActionEquiv R (ConvolutionDual R A) M).trans
    ((ConvolutionDual.evalAlgEquiv R A).symm.arrowCongr AlgEquiv.refl)

/-- The action attached to a coaction contracts the coaction against evaluation at `x`. -/
@[simp]
theorem finiteAlgebraActionEquiv_apply_apply (σ : Comodule R (ConvolutionDual R A) M) (x : A)
    (m : M) :
    finiteAlgebraActionEquiv R A M σ x m =
      LinearMap.tensorComponent (ConvolutionDual.evalAlgEquiv R A x).ofConv (σ.coact m) := by
  rw [finiteAlgebraActionEquiv, Equiv.trans_apply, convolutionActionEquiv_apply]
  exact convolutionAction_apply _ m

/-- The coaction attached to an action of `A` is characterized by its contractions: contracting
against `φ` acts by the element of `A` corresponding to `φ` under double duality. -/
@[simp]
theorem tensorComponent_finiteAlgebraActionEquiv_symm_coact (ρ : A →ₐ[R] Module.End R M)
    (φ : Module.Dual R (ConvolutionDual R A)) (m : M) :
    LinearMap.tensorComponent φ (((finiteAlgebraActionEquiv R A M).symm ρ).coact m) =
      ρ ((ConvolutionDual.evalAlgEquiv R A).symm (toConv φ)) m := by
  rw [finiteAlgebraActionEquiv, Equiv.symm_trans_apply, AlgEquiv.arrowCongr_symm,
    convolutionActionEquiv_symm_apply, tensorComponent_ofConvolutionAction]
  simp only [AlgEquiv.arrowCongr_apply, AlgHom.comp_apply, AlgEquiv.symm_symm,
    AlgEquiv.coe_toAlgHom, AlgEquiv.refl_symm, AlgEquiv.coe_refl, id_eq]

section OfModule

variable [Module A M] [IsScalarTower R A M]

/-- A left module over a finite projective algebra `A`, as a right comodule over the dual
coalgebra of `A`. Its coaction is `m ↦ ∑ᵢ eᵢ • m ⊗ eᵢ^∨` in any basis
(`ofFiniteAlgebraModule_coact_eq_sum`). This structure is not installed globally. -/
@[implicit_reducible]
def ofFiniteAlgebraModule : Comodule R (ConvolutionDual R A) M :=
  (finiteAlgebraActionEquiv R A M).symm (Algebra.lsmul R R M)

/-- Contracting the coaction of a left module against `φ` acts by the element of `A`
corresponding to `φ` under double duality. -/
theorem tensorComponent_ofFiniteAlgebraModule_coact (φ : Module.Dual R (ConvolutionDual R A))
    (m : M) :
    LinearMap.tensorComponent φ ((ofFiniteAlgebraModule (R := R) (A := A) (M := M)).coact m) =
      (ConvolutionDual.evalAlgEquiv R A).symm (toConv φ) • m :=
  tensorComponent_finiteAlgebraActionEquiv_symm_coact _ φ m

/-- Contracting the coaction of a left module against evaluation at `x` is the action of `x`. -/
theorem tensorComponent_evalAlgEquiv_ofFiniteAlgebraModule_coact (x : A) (m : M) :
    LinearMap.tensorComponent (ConvolutionDual.evalAlgEquiv R A x).ofConv
        ((ofFiniteAlgebraModule (R := R) (A := A) (M := M)).coact m) = x • m := by
  simp

/-- **The coaction of a left module in a basis**: `ρ(m) = ∑ᵢ eᵢ • m ⊗ eᵢ^∨`, where `eᵢ^∨` is the
`i`-th coordinate functional of the basis, viewed in the dual coalgebra. -/
theorem ofFiniteAlgebraModule_coact_eq_sum {ι : Type*} [Fintype ι] (b : Module.Basis ι R A)
    (m : M) :
    (ofFiniteAlgebraModule (R := R) (A := A) (M := M)).coact m =
      ∑ i, (b i • m) ⊗ₜ[R] toConv (b.coord i) := by
  apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
  intro φ
  obtain ⟨x, rfl⟩ : ∃ x, (ConvolutionDual.evalAlgEquiv R A x).ofConv = φ :=
    ⟨(ConvolutionDual.evalAlgEquiv R A).symm (toConv φ), by simp⟩
  have hx : ∀ i, (ConvolutionDual.evalAlgEquiv R A x).ofConv (toConv (b.coord i)) = b.coord i x :=
    fun i ↦ ConvolutionDual.evalAlgEquiv_apply_apply R A x _
  rw [tensorComponent_evalAlgEquiv_ofFiniteAlgebraModule_coact, map_sum]
  simp only [LinearMap.tensorComponent_tmul, hx, Module.Basis.coord_apply, ← smul_assoc,
    ← Finset.sum_smul, b.sum_repr]

end OfModule

section ToModule

variable [Comodule R (ConvolutionDual R A) M] [Comodule R (ConvolutionDual R A) N]

variable (R A M) in
/-- The left `A`-module underlying a right comodule over the dual coalgebra of `A`: the action of
`x` contracts the coaction against evaluation at `x` (`finiteAlgebraModule_smul`). This structure
is not installed globally. -/
abbrev finiteAlgebraModule : Module A M :=
  Module.compHom M (finiteAlgebraActionEquiv R A M inferInstance).toRingHom

/-- The action of `x : A` on a comodule contracts the coaction against evaluation at `x`. -/
theorem finiteAlgebraModule_smul (x : A) (m : M) :
    (letI := finiteAlgebraModule R A M; x • m) =
      LinearMap.tensorComponent (ConvolutionDual.evalAlgEquiv R A x).ofConv
        (coact (R := R) (C := ConvolutionDual R A) m) :=
  finiteAlgebraActionEquiv_apply_apply _ x m

variable (R A M) in
/-- The `A`-module structure of a comodule extends its ground-ring action. -/
theorem finiteAlgebraModule_isScalarTower :
    letI := finiteAlgebraModule R A M; IsScalarTower R A M :=
  letI := finiteAlgebraModule R A M
  IsScalarTower.of_algebraMap_smul fun r m ↦
    DFunLike.congr_fun ((finiteAlgebraActionEquiv R A M inferInstance).commutes r) m

/-- The algebra map acts on a comodule through the ground ring. -/
theorem algebraMap_finiteAlgebraModule_smul (r : R) (m : M) :
    (letI := finiteAlgebraModule R A M; algebraMap R A r • m) = r • m :=
  letI := finiteAlgebraModule R A M
  haveI := finiteAlgebraModule_isScalarTower R A M
  algebraMap_smul A r m

/-- Recovering a coaction from its `A`-module structure gives back the original coaction. -/
@[simp]
theorem ofFiniteAlgebraModule_finiteAlgebraModule :
    (letI := finiteAlgebraModule R A M; haveI := finiteAlgebraModule_isScalarTower R A M;
      ofFiniteAlgebraModule (R := R) (A := A) (M := M)) =
      ‹Comodule R (ConvolutionDual R A) M› := by
  let := finiteAlgebraModule R A M
  have := finiteAlgebraModule_isScalarTower R A M
  refine Comodule.ext (LinearMap.ext fun m ↦ ?_)
  refine TensorProduct.tensor_eq_of_forall_tensorComponent_eq fun φ ↦ ?_
  rw [tensorComponent_ofFiniteAlgebraModule_coact, finiteAlgebraModule_smul,
    AlgEquiv.apply_symm_apply, ofConv_toConv]

/-- A comodule morphism commutes with contracting the coaction against evaluation at `x`. -/
private theorem Hom.map_tensorComponent_evalAlgEquiv (f : Hom R (ConvolutionDual R A) M N) (x : A)
    (m : M) :
    f (LinearMap.tensorComponent (ConvolutionDual.evalAlgEquiv R A x).ofConv
        (coact (R := R) (C := ConvolutionDual R A) m)) =
      LinearMap.tensorComponent (ConvolutionDual.evalAlgEquiv R A x).ofConv
        (coact (R := R) (C := ConvolutionDual R A) (f m)) := by
  rw [← convolutionAction_apply, ← convolutionAction_apply, Hom.map_convolutionAction]

/-- A comodule morphism is `A`-linear for the attached module structures. -/
theorem Hom.map_finiteAlgebraModule_smul (f : Hom R (ConvolutionDual R A) M N) (x : A) (m : M) :
    f (letI := finiteAlgebraModule R A M; x • m) =
      (letI := finiteAlgebraModule R A N; x • f m) := by
  rw [finiteAlgebraModule_smul, finiteAlgebraModule_smul, Hom.map_tensorComponent_evalAlgEquiv]

end ToModule

/-- The action of `A` on a left module is recovered from the attached comodule. -/
theorem finiteAlgebraModule_ofFiniteAlgebraModule_smul [Module A M] [IsScalarTower R A M] (x : A)
    (m : M) :
    (letI := ofFiniteAlgebraModule (R := R) (A := A) (M := M);
      letI := finiteAlgebraModule R A M; x • m) = x • m :=
  letI := ofFiniteAlgebraModule (R := R) (A := A) (M := M)
  (finiteAlgebraModule_smul x m).trans
    (tensorComponent_evalAlgEquiv_ofFiniteAlgebraModule_coact x m)

/-- Viewing a left module as a comodule and then as a module recovers the original action. -/
@[simp]
theorem finiteAlgebraModule_ofFiniteAlgebraModule [inst : Module A M] [IsScalarTower R A M] :
    (letI := ofFiniteAlgebraModule (R := R) (A := A) (M := M);
      finiteAlgebraModule R A M) = inst :=
  Module.ext' _ _ (finiteAlgebraModule_ofFiniteAlgebraModule_smul (R := R))

section Hom

variable [Module A M] [IsScalarTower R A M] [Module A N] [IsScalarTower R A N]

attribute [local instance] ofFiniteAlgebraModule

/-- An `A`-linear map between left modules is a morphism of the attached comodules. -/
def _root_.LinearMap.toFiniteAlgebraComoduleHom (f : M →ₗ[A] N) :
    Hom R (ConvolutionDual R A) M N where
  toLinearMap := f.restrictScalars R
  map_coact := by
    ext m
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro φ
    simp [LinearMap.tensorComponent_map]

/-- The comodule morphism attached to an `A`-linear map has the same values. -/
@[simp]
theorem _root_.LinearMap.toFiniteAlgebraComoduleHom_apply (f : M →ₗ[A] N) (m : M) :
    f.toFiniteAlgebraComoduleHom (R := R) m = f m := (rfl)

/-- The comodule morphism attached to a composite of `A`-linear maps is the composite. -/
@[simp]
theorem _root_.LinearMap.toFiniteAlgebraComoduleHom_comp {P : Type*} [AddCommMonoid P]
    [Module R P] [Module A P] [IsScalarTower R A P] (g : N →ₗ[A] P) (f : M →ₗ[A] N) :
    (g ∘ₗ f).toFiniteAlgebraComoduleHom (R := R) =
      g.toFiniteAlgebraComoduleHom.comp f.toFiniteAlgebraComoduleHom :=
  (rfl)

/-- A morphism between the comodules attached to left modules is `A`-linear. -/
def Hom.toFiniteAlgebraLinearMap (f : Hom R (ConvolutionDual R A) M N) : M →ₗ[A] N where
  toFun := f
  map_add' := f.map_add
  map_smul' x m := by
    rw [RingHom.id_apply,
      ← tensorComponent_evalAlgEquiv_ofFiniteAlgebraModule_coact (R := R) x m,
      ← tensorComponent_evalAlgEquiv_ofFiniteAlgebraModule_coact (R := R) x (f m),
      Hom.map_tensorComponent_evalAlgEquiv]

/-- The `A`-linear map attached to a comodule morphism has the same values. -/
@[simp]
theorem Hom.toFiniteAlgebraLinearMap_apply (f : Hom R (ConvolutionDual R A) M N) (m : M) :
    f.toFiniteAlgebraLinearMap m = f m := (rfl)

variable (R) in
/-- **Morphisms of left `A`-modules are the morphisms of the attached comodules** over the dual
coalgebra of `A`. -/
def Hom.finiteAlgebraLinearEquiv : Hom R (ConvolutionDual R A) M N ≃ₗ[R] (M →ₗ[A] N) where
  toFun := Hom.toFiniteAlgebraLinearMap
  invFun := LinearMap.toFiniteAlgebraComoduleHom
  left_inv f := by ext; rfl
  right_inv f := by ext; rfl
  map_add' f g := by ext; rfl
  map_smul' r f := by ext; rfl

/-- The forward comparison of morphisms keeps the values of the comodule morphism. -/
@[simp]
theorem Hom.finiteAlgebraLinearEquiv_apply (f : Hom R (ConvolutionDual R A) M N) :
    Hom.finiteAlgebraLinearEquiv R f = f.toFiniteAlgebraLinearMap := (rfl)

/-- The inverse comparison of morphisms keeps the values of the `A`-linear map. -/
@[simp]
theorem Hom.finiteAlgebraLinearEquiv_symm_apply (f : M →ₗ[A] N) :
    (Hom.finiteAlgebraLinearEquiv R).symm f = f.toFiniteAlgebraComoduleHom := (rfl)

end Hom

end Semiring

end TauCeti.Comodule
