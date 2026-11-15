/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Convolution.Finite
public import TauCeti.Algebra.HopfAlgebra.Cointegral.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfModule.Basic
import TauCeti.LinearAlgebra.TensorProduct.Basis

/-!
# The dual of a finite projective Hopf algebra as a right Hopf module

For a finite projective Hopf algebra `H` over a commutative semiring `R`, the linear dual
`Module.Dual R H` carries a right `H`-Hopf module structure, packaged here on the type synonym
`TauCeti.DualHopfModule R H` so as not to install competing global instances on `H →ₗ[R] R`:

* the right `H`-action `(MulOpposite.op h • φ)(x) = φ(x * S(h))` comes from right multiplication on
  `H` twisted by the antipode;
* the right `H`-coaction is reconstructed by `TauCeti.Comodule.ofConvolutionAction` from left
  convolution multiplication `ψ ↦ (φ ↦ ψ * φ)`.

The Hopf-module compatibility `coact (φ · h) = coact(φ) · h` follows from the coalgebraic
anti-endomorphism property of `S` together with the antipode cancellation `∑ S(h₂) * h₃ = ε(h₂) 1`.
The coinvariant subcomodule `Comodule.fixedSubcomodule R H (DualHopfModule R H)` identifies with
`TauCeti.leftCointegrals R H`. Applying the Fundamental Theorem of Hopf Modules (`hopfModuleEquiv`)
produces the Larson–Sweedler linear isomorphism
`leftCointegralsTensorEquiv : leftCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H`,
sending `φ ⊗ h` to `x ↦ φ(x * S(h))`, without assuming that `R` is a ring or a field or that `S`
is invertible.

## Main declarations

* `TauCeti.DualHopfModule`: type synonym of `Module.Dual R H` for the right Hopf module structure.
* `TauCeti.DualHopfModule.instIsRightHopfModule`: `DualHopfModule R H` is a right `H`-Hopf module.
* `TauCeti.DualHopfModule.fixedSubcomoduleEquiv`: linear isomorphism between the coinvariants of
  `DualHopfModule R H` and `leftCointegrals R H`.
* `TauCeti.leftCointegralsTensorEquiv`: the Larson–Sweedler isomorphism
  `leftCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H`.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Theorem 2.1.3.
-/

public noncomputable section

open scoped TensorProduct
open TensorProduct WithConv

namespace TauCeti

universe u v

/-- Type synonym of `Module.Dual R H` carrying the right `H`-Hopf module structure on the dual of a
Hopf algebra: `(MulOpposite.op h • φ)(x) = φ(x * S(h))` and coaction dual to left convolution
multiplication. -/
def DualHopfModule (R : Type u) (H : Type v) [CommSemiring R] [AddCommMonoid H] [Module R H] :
    Type (max u v) :=
  Module.Dual R H

namespace DualHopfModule

section Module

variable (R : Type u) (H : Type v) [CommSemiring R] [AddCommMonoid H] [Module R H]

instance : AddCommMonoid (DualHopfModule R H) :=
  inferInstanceAs (AddCommMonoid (Module.Dual R H))

instance {R : Type u} {H : Type v} [CommRing R] [AddCommGroup H] [Module R H] :
    AddCommGroup (DualHopfModule R H) :=
  inferInstanceAs (AddCommGroup (Module.Dual R H))

instance : Module R (DualHopfModule R H) :=
  inferInstanceAs (Module R (Module.Dual R H))

/-- The underlying `R`-linear identification of `DualHopfModule R H` with `Module.Dual R H`. -/
def equiv : DualHopfModule R H ≃ₗ[R] Module.Dual R H :=
  LinearEquiv.refl R (Module.Dual R H)

variable {R H}

@[ext]
theorem ext {φ ψ : DualHopfModule R H} (h : ∀ x : H, equiv R H φ x = equiv R H ψ x) : φ = ψ :=
  (equiv R H).injective (LinearMap.ext h)

instance [Module.Projective R H] [Module.Finite R H] : Module.Finite R (DualHopfModule R H) :=
  Module.Finite.equiv (equiv R H).symm

end Module

section Coaction

variable (R : Type u) (H : Type v) [CommSemiring R] [AddCommMonoid H] [Module R H] [Coalgebra R H]

/-- Left convolution multiplication on `Module.Dual R H` packaged as an algebra representation of
`WithConv (Module.Dual R H)`. -/
def convLeftAction : WithConv (Module.Dual R H) →ₐ[R] Module.End R (DualHopfModule R H) where
  toFun ψ := (equiv R H).symm.toLinearMap ∘ₗ
    (WithConv.linearEquiv R (Module.Dual R H)).toLinearMap ∘ₗ
      LinearMap.mulLeft R ψ ∘ₗ (WithConv.linearEquiv R (Module.Dual R H)).symm.toLinearMap ∘ₗ
        (equiv R H).toLinearMap
  map_one' := by
    ext φ x
    change ((1 * toConv (equiv R H φ)).ofConv) x = equiv R H φ x
    rw [one_mul, ofConv_toConv]
  map_mul' ψ₁ ψ₂ := by
    ext φ x
    change (((ψ₁ * ψ₂) * toConv (equiv R H φ)).ofConv) x =
      ((ψ₁ * toConv ((ψ₂ * toConv (equiv R H φ)).ofConv)).ofConv) x
    rw [toConv_ofConv, mul_assoc]
  map_zero' := by
    ext φ x
    change ((0 * toConv (equiv R H φ)).ofConv) x = 0
    simp
  map_add' ψ₁ ψ₂ := by
    ext φ x
    change (((ψ₁ + ψ₂) * toConv (equiv R H φ)).ofConv) x =
      ((ψ₁ * toConv (equiv R H φ)).ofConv) x + ((ψ₂ * toConv (equiv R H φ)).ofConv) x
    rw [add_mul, ofConv_add, LinearMap.add_apply]
  commutes' r := by
    ext φ x
    change ((algebraMap R (WithConv (Module.Dual R H)) r * toConv (equiv R H φ)).ofConv) x =
      r • equiv R H φ x
    rw [← Algebra.smul_def, ofConv_smul, ofConv_toConv, LinearMap.smul_apply]

@[simp]
theorem equiv_convLeftAction_apply (ψ : WithConv (Module.Dual R H)) (φ : DualHopfModule R H) :
    equiv R H (convLeftAction R H ψ φ) = (ψ * toConv (equiv R H φ)).ofConv :=
  (rfl)

variable [Module.Finite R H] [Module.Projective R H]

/-- The right `H`-comodule structure on `DualHopfModule R H` reconstructed from left convolution
multiplication. -/
instance instComodule : Comodule R H (DualHopfModule R H) :=
  Comodule.ofConvolutionAction (convLeftAction R H)

variable {R H}

/-- Contracting the coaction of `DualHopfModule R H` against `ψ : Module.Dual R H` is left
convolution multiplication by `ψ`. -/
theorem equiv_tensorComponent_coact (ψ : Module.Dual R H) (φ : DualHopfModule R H) :
    equiv R H (LinearMap.tensorComponent ψ (Comodule.coact (R := R) (C := H) φ)) =
      (toConv ψ * toConv (equiv R H φ)).ofConv := by
  change equiv R H
      (LinearMap.tensorComponent ψ ((Comodule.ofConvolutionAction (convLeftAction R H)).coact φ)) =
    _
  rw [Comodule.tensorComponent_ofConvolutionAction, equiv_convLeftAction_apply]

/-- The coinvariants of `DualHopfModule R H` are precisely the left cointegrals on `H`. -/
theorem mem_fixedSubcomodule_iff [One H] (φ : DualHopfModule R H) :
    φ ∈ Comodule.fixedSubcomodule R H (DualHopfModule R H) ↔ IsLeftCointegral (equiv R H φ) := by
  rw [Comodule.mem_fixedSubcomodule, isLeftCointegral_iff_convMul]
  constructor
  · intro hcoact ψ
    apply WithConv.ofConv_injective
    have hψ := congrArg (fun z ↦ equiv R H (LinearMap.tensorComponent ψ.ofConv z)) hcoact
    simpa only [equiv_tensorComponent_coact, toConv_ofConv, LinearMap.tensorComponent_tmul,
      map_smul, ofConv_smul, ofConv_toConv] using hψ
  · intro hconv
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro ψ
    apply (equiv R H).injective
    have hψ := congrArg WithConv.ofConv (hconv (toConv ψ))
    simpa only [equiv_tensorComponent_coact, LinearMap.tensorComponent_tmul, map_smul,
      ofConv_smul, ofConv_toConv] using hψ

variable (R H) in
/-- The coinvariant subcomodule of `DualHopfModule R H` is canonically linearly isomorphic to
`leftCointegrals R H`. -/
def fixedSubcomoduleEquiv [One H] :
    Comodule.fixedSubcomodule R H (DualHopfModule R H) ≃ₗ[R] leftCointegrals R H where
  toFun φ := ⟨equiv R H φ.1, (mem_leftCointegrals _).mpr ((mem_fixedSubcomodule_iff φ.1).mp φ.2)⟩
  map_add' φ ψ := Subtype.ext (map_add (equiv R H) φ.1 ψ.1)
  map_smul' r φ := Subtype.ext (map_smul (equiv R H) r φ.1)
  invFun φ :=
    ⟨(equiv R H).symm φ.1,
      (mem_fixedSubcomodule_iff _).mpr (by simpa using (mem_leftCointegrals _).mp φ.2)⟩
  left_inv φ := Subtype.ext ((equiv R H).symm_apply_apply φ.1)
  right_inv φ := Subtype.ext ((equiv R H).apply_symm_apply φ.1)

@[simp]
theorem fixedSubcomoduleEquiv_coe [One H]
    (φ : Comodule.fixedSubcomodule R H (DualHopfModule R H)) :
    (fixedSubcomoduleEquiv R H φ : Module.Dual R H) = equiv R H φ.1 :=
  (rfl)

@[simp]
theorem fixedSubcomoduleEquiv_symm_coe [One H] (φ : leftCointegrals R H) :
    ((fixedSubcomoduleEquiv R H).symm φ : DualHopfModule R H) = (equiv R H).symm φ.1 :=
  (rfl)

end Coaction

section HopfModule

variable (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- The right `H`-action on `Module.Dual R H` sending `(MulOpposite.op h, φ)` to
`x ↦ φ(x * S(h))`. -/
def rightAction : Hᵐᵒᵖ →ₐ[R] Module.End R (Module.Dual R H) where
  toFun a := Module.Dual.transpose (LinearMap.mulRight R (HopfAlgebra.antipode R a.unop))
  map_one' := by
    ext φ x
    simp [Module.Dual.transpose_apply]
  map_mul' a b := by
    ext φ x
    simp [Module.Dual.transpose_apply, HopfAlgebra.antipode_mul_antidistrib,
      _root_.mul_apply_eq_comp]
  map_zero' := by
    ext φ x
    simp
  map_add' a b := by
    ext φ x
    simp [Module.Dual.transpose_apply, mul_add]
  commutes' r := by
    ext φ x
    simp [Module.Dual.transpose_apply, Algebra.algebraMap_eq_smul_one]

@[no_expose] noncomputable instance instModuleOp : Module Hᵐᵒᵖ (DualHopfModule R H) :=
  Module.compHom (Module.Dual R H) (rightAction R H).toRingHom

instance instIsScalarTowerOp : IsScalarTower R Hᵐᵒᵖ (DualHopfModule R H) :=
  IsScalarTower.of_algebraMap_smul fun r φ ↦
    LinearMap.congr_fun ((rightAction R H).commutes r) φ

variable {R H}

@[simp]
theorem equiv_smul_apply (h : H) (φ : DualHopfModule R H) (x : H) :
    equiv R H (MulOpposite.op h • φ) x = equiv R H φ (x * HopfAlgebra.antipode R h) :=
  (rfl)

private theorem lid_rTensor_mul_one_tmul (ψ : Module.Dual R H) (z : H ⊗[R] H) (y : H) :
    TensorProduct.lid R H (ψ.rTensor H (z * ((1 : H) ⊗ₜ[R] y))) =
      TensorProduct.lid R H (ψ.rTensor H z) * y := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => simp only [add_mul, map_add, hz₁, hz₂]
  | tmul p q =>
    rw [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one, LinearMap.rTensor_tmul, lid_tmul,
      LinearMap.rTensor_tmul, lid_tmul, smul_mul_assoc]

private theorem lid_rTensor_mul_tmul_one (ψ : Module.Dual R H) (z : H ⊗[R] H) (b : H) :
    TensorProduct.lid R H (ψ.rTensor H (z * (b ⊗ₜ[R] (1 : H)))) =
      TensorProduct.lid R H ((ψ ∘ₗ LinearMap.mulRight R b).rTensor H z) := by
  induction z using TensorProduct.inductionOn with
  | add z₁ z₂ hz₁ hz₂ => simp only [add_mul, map_add, hz₁, hz₂]
  | tmul p q =>
    rw [_root_.Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    simp

private theorem map_mul_antipode_rTensor_assoc_rTensor_comul (h : H) :
    TensorProduct.map LinearMap.id
        (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H)
        (TensorProduct.assoc R H H H
          ((Coalgebra.comul (R := R)).rTensor H (Coalgebra.comul h))) =
      h ⊗ₜ[R] (1 : H) := by
  have hcoassoc :
      TensorProduct.assoc R H H H ((Coalgebra.comul (R := R)).rTensor H (Coalgebra.comul h)) =
        (Coalgebra.comul (R := R)).lTensor H (Coalgebra.comul h) := by
    rw [← Coalgebra.coassoc_symm_apply, LinearEquiv.apply_symm_apply]
  have hcancel :
      LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H ∘ₗ Coalgebra.comul =
        Algebra.linearMap R H ∘ₗ Coalgebra.counit :=
    LinearMap.ext HopfAlgebra.mul_antipode_rTensor_comul_apply
  rw [hcoassoc, ← LinearMap.lTensor_def, ← LinearMap.lTensor_comp_apply, LinearMap.comp_assoc,
    hcancel, LinearMap.lTensor_comp_apply, Coalgebra.lTensor_counit_comul, LinearMap.lTensor_tmul,
    Algebra.linearMap_apply, map_one]

private theorem equiv_tensorComponent_tensorPairAction_apply
    (ψ : Module.Dual R H) (a b : H) (w : DualHopfModule R H ⊗[R] H) (x : H) :
    equiv R H
        (LinearMap.tensorComponent ψ
          (BialgebraModule.tensorPairAction R (A := Hᵐᵒᵖ) (B := Hᵐᵒᵖ) (DualHopfModule R H) H
            (MulOpposite.op a ⊗ₜ[R] MulOpposite.op b) w)) x =
      equiv R H (LinearMap.tensorComponent (ψ ∘ₗ LinearMap.mulRight R b) w)
        (x * HopfAlgebra.antipode R a) := by
  induction w using TensorProduct.inductionOn with
  | add w₁ w₂ hw₁ hw₂ => simp only [map_add, LinearMap.add_apply, hw₁, hw₂]
  | tmul α c =>
    rw [BialgebraModule.tensorPairAction_tmul, LinearMap.tensorComponent_tmul,
      LinearMap.tensorComponent_tmul]
    change equiv R H (ψ (c * b) • (MulOpposite.op a • α)) x = _
    simp

variable [Module.Finite R H] [Module.Projective R H]

/-- `DualHopfModule R H` is a right `H`-Hopf module over any finite projective Hopf algebra `H`. -/
instance instIsRightHopfModule : IsRightHopfModule R H (DualHopfModule R H) where
  coact_smul h φ := by
    apply TensorProduct.tensor_eq_of_forall_tensorComponent_eq
    intro ψ
    apply (equiv R H).injective
    ext x
    -- Package `(u, c) ↦ φ(lid(ψ.rTensor(Δ(x) * (c ⊗ S(u)))))` as an `R`-linear functional on
    -- `H ⊗[R] H` so the cancellation `∑ S(h₂) * h₃ = ε(h₂) 1` collapses the RHS to `h ⊗ 1`.
    let Γ : H ⊗[R] H →ₗ[R] R :=
      equiv R H φ ∘ₗ (TensorProduct.lid R H).toLinearMap ∘ₗ ψ.rTensor H ∘ₗ
        LinearMap.mulLeft R (Coalgebra.comul (R := R) x) ∘ₗ
          (TensorProduct.comm R H H).toLinearMap ∘ₗ (HopfAlgebra.antipode R).rTensor H
    let F : (H ⊗[R] H) ⊗[R] H →ₗ[R] H ⊗[R] H :=
      TensorProduct.map LinearMap.id
        (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H) ∘ₗ
        (TensorProduct.assoc R H H H).toLinearMap
    have hlhs :
        equiv R H (LinearMap.tensorComponent ψ
            (Comodule.coact (R := R) (C := H) (MulOpposite.op h • φ))) x =
          Γ (h ⊗ₜ[R] (1 : H)) := by
      rw [equiv_tensorComponent_coact, ConvolutionDual.mul_apply_eq_rTensor, ofConv_toConv,
        ofConv_toConv, equiv_smul_apply]
      simp only [Γ, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearEquiv.coe_coe, comm_tmul,
        LinearMap.mulLeft_apply, lid_rTensor_mul_one_tmul]
    have hrhs_gen (t : H ⊗[R] H) :
        equiv R H (LinearMap.tensorComponent ψ
            (BialgebraModule.tensorPairAction R (A := Hᵐᵒᵖ) (B := Hᵐᵒᵖ) (DualHopfModule R H) H
              ((_root_.Algebra.TensorProduct.opAlgEquiv R R H H).symm (MulOpposite.op t))
              (Comodule.coact (R := R) (C := H) φ))) x =
          Γ (F ((Coalgebra.comul (R := R)).rTensor H t)) := by
      induction t using TensorProduct.inductionOn with
      | add t₁ t₂ ht₁ ht₂ =>
        simp only [MulOpposite.op_add, map_add, LinearMap.add_apply, ht₁, ht₂]
      | tmul a b =>
        rw [_root_.Algebra.TensorProduct.opAlgEquiv_symm_tmul,
          equiv_tensorComponent_tensorPairAction_apply, equiv_tensorComponent_coact,
          ConvolutionDual.mul_apply_eq_rTensor, ofConv_toConv, ofConv_toConv,
          Bialgebra.comul_mul, ← lid_rTensor_mul_tmul_one, mul_assoc,
          TauCeti.HopfAlgebra.antipode_comul_antidistrib_apply, LinearMap.rTensor_tmul]
        induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
        | add z₁ z₂ hz₁ hz₂ =>
          simp only [map_add, mul_add, add_mul, add_tmul, hz₁, hz₂]
        | tmul u v =>
          simp only [F, Γ, comm_tmul, map_tmul, _root_.Algebra.TensorProduct.tmul_mul_tmul,
            mul_one, LinearMap.comp_apply, LinearEquiv.coe_coe, assoc_tmul, LinearMap.id_apply,
            LinearMap.rTensor_tmul, LinearMap.mul'_apply, LinearMap.mulLeft_apply]
    have hrhs :
        equiv R H (LinearMap.tensorComponent ψ
            (rightTensorAction R H (DualHopfModule R H) (MulOpposite.op h)
              (Comodule.coact (R := R) (C := H) φ))) x =
          Γ (F ((Coalgebra.comul (R := R)).rTensor H (Coalgebra.comul h))) := by
      rw [rightTensorAction_apply, hrhs_gen]
    rw [hlhs, hrhs]
    exact congrArg Γ (map_mul_antipode_rTensor_assoc_rTensor_comul h).symm

end HopfModule

end DualHopfModule

section LarsonSweedler

variable (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [Module.Finite R H] [Module.Projective R H]

/-- **Larson–Sweedler Cointegral Decomposition.** For any finite projective Hopf algebra `H` over a
commutative semiring `R`, the linear dual `Module.Dual R H` is isomorphic as an `R`-module to
`leftCointegrals R H ⊗[R] H` via `φ ⊗ h ↦ (x ↦ φ(x * S(h)))`. -/
def leftCointegralsTensorEquiv :
    leftCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H :=
  TensorProduct.congr (DualHopfModule.fixedSubcomoduleEquiv R H).symm (LinearEquiv.refl R H) ≪≫ₗ
    hopfModuleEquiv R H (DualHopfModule R H) ≪≫ₗ
    DualHopfModule.equiv R H

variable {R H}

@[simp]
theorem leftCointegralsTensorEquiv_tmul_apply (φ : leftCointegrals R H) (h x : H) :
    leftCointegralsTensorEquiv R H (φ ⊗ₜ[R] h) x =
      (φ : Module.Dual R H) (x * HopfAlgebra.antipode R h) := by
  simp [leftCointegralsTensorEquiv]

end LarsonSweedler

end TauCeti
