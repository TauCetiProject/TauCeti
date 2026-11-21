/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.Algebra.HopfAlgebra.Cointegral.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfModule.Basic
import TauCeti.LinearAlgebra.Dual.RightAction

/-!
# The dual Hopf module and the cointegral decomposition

For a finite projective Hopf algebra `H` over a commutative semiring `R`, the linear dual
`Module.Dual R H` is a right `H`-Hopf module:

* its right `H`-module structure (`dualRightModule`) is precomposition with left multiplication,
  `(op h • φ) y = φ (h * y)` (matching Mathlib's `DomMulAct.mk h • φ`);
* its right `H`-comodule structure is `Comodule.dual R H H` for the regular right comodule `H`,
  characterized by `dualTensorHom R H H (dualCoact φ) y = S(matrixCoefficient φ y)`.

Both the right Hopf-module compatibility (`isRightHopfModule_dual`) and the identification of the
coinvariant subcomodule with `rightCointegrals R H` (`mem_fixedSubcomodule_dual_iff`) hold over any
commutative semiring `R`, without assuming bijectivity of the antipode or choosing a basis.
Specializing the Fundamental Theorem of Hopf Modules (`RightHopfModule.coinvariantTensorEquiv`) to
`Module.Dual R H` yields Larson and Sweedler's **cointegral decomposition**
(`rightCointegralsTensorEquivDual`):

`rightCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H`,

sending `φ ⊗ h` to `DomMulAct.mk h • φ` (`x ↦ φ (h * x)`). As an immediate consequence over any
commutative semiring `R`, `rightCointegrals R H` is a finitely generated projective `R`-module.

## Main declarations

* `TauCeti.RightHopfModule.dualRightModule`, `TauCeti.RightHopfModule.isRightHopfModule_dual`: the
  right `H`-Hopf module structure on `Module.Dual R H`.
* `TauCeti.RightHopfModule.mem_fixedSubcomodule_dual_iff` and
  `TauCeti.RightHopfModule.dualFixedEquivRightCointegrals`: coinvariants of `Module.Dual R H` are
  precisely the right cointegrals on `H`.
* `TauCeti.rightCointegralsTensorEquivDual`: the canonical `R`-linear isomorphism
  `rightCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H`, equivariant for right `H`-multiplication.
* `TauCeti.instModuleProjectiveRightCointegrals`, `TauCeti.instModuleFiniteRightCointegrals`:
  `rightCointegrals R H` is finitely generated and projective over `R`.
* `TauCeti.exists_isRightCointegral_ne_zero`: existence of a nonzero right cointegral over any
  nontrivial commutative semiring.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94, Proposition 1 and Theorem 1.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, CBMS Regional Conference Series in
  Mathematics 82, 1993, Theorem 2.1.3.
-/

public noncomputable section

open scoped TensorProduct Coalgebra

namespace TauCeti

universe u v

namespace RightHopfModule

section DualHopfModule

variable (R : Type u) (H : Type v) [CommSemiring R] [Semiring H]

/-- The right `H`-module structure on `Module.Dual R H` dual to left multiplication on `H`:
`(op h • φ) y = φ (h * y)`.

Like `Comodule.dual`, this is an explicit definition rather than a global instance so it does not
compete with other `Hᵐᵒᵖ`-actions on linear-map spaces. -/
@[implicit_reducible]
def dualRightModule [Algebra R H] : Module Hᵐᵒᵖ (Module.Dual R H) :=
  have : SMulCommClass H R H := SMulCommClass.symm R H H
  Module.compHom (Module.Dual R H) (linearMapOpAction R H R)

section Algebra

variable [Algebra R H]

attribute [local instance] dualRightModule

variable {R H} in
/-- Pointwise formula for the right `H`-action on `Module.Dual R H`: `(op h • φ) y = φ (h * y)`. -/
@[simp]
theorem dualRightModule_op_smul_apply (h : H) (φ : Module.Dual R H) (y : H) :
    (MulOpposite.op h • φ) y = φ (h * y) := by
  have : SMulCommClass H R H := SMulCommClass.symm R H H
  exact linearMapOpAction_apply_apply R H R (MulOpposite.op h) φ y

variable {R H} in
/-- The right `H`-action `op h • φ` on `Module.Dual R H` agrees with Mathlib's domain action
`DomMulAct.mk h • φ`. -/
theorem dualRightModule_op_smul_eq_domMulAct (h : H) (φ : Module.Dual R H) :
    MulOpposite.op h • φ = DomMulAct.mk h • φ :=
  LinearMap.ext fun y => by
    rw [dualRightModule_op_smul_apply, DomMulAct.mk_smul_linearMap_apply, smul_eq_mul]

/-- Scalar compatibility of `dualRightModule` with `R`. -/
instance dualRightIsScalarTower : IsScalarTower R Hᵐᵒᵖ (Module.Dual R H) :=
  IsScalarTower.of_algebraMap_smul fun r φ => LinearMap.ext fun y => by
    rw [MulOpposite.algebraMap_apply, dualRightModule_op_smul_apply, ← Algebra.smul_def,
      map_smul, LinearMap.smul_apply]

end Algebra

section HopfAlgebra

variable [_root_.HopfAlgebra R H]

attribute [local instance] Comodule.dual dualRightModule

private theorem dualTensorHom_rTensor_opSMulTensor_tensorCombine
    (z : Module.Dual R H ⊗[R] H) (w : H ⊗[R] H) (y : H) :
    dualTensorHom R H H
        ((opSMulTensor R H (Module.Dual R H)).rTensor H
          (Comodule.tensorCombine (R := R) (C := H) (M := Module.Dual R H) (N := H)
            (z ⊗ₜ[R] w))) y =
      LinearMap.mul' R H ((dualTensorHom R H H z ∘ₗ LinearMap.mulRight R y).rTensor H w) := by
  induction z using TensorProduct.inductionOn with
  | add u v hu hv =>
    simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, LinearMap.add_comp,
      LinearMap.rTensor_add, hu, hv]
  | tmul ψ a =>
    induction w using TensorProduct.inductionOn with
    | add u v hu hv =>
      simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hu, hv]
    | tmul h₁ h₂ =>
      simp [dualTensorHom_apply]

/-- Universal cancellation for matrix coefficients of the regular right `H`-comodule:
`∑ S(matrixCoefficient φ x₁) * x₂ = ∑ φ(x₁) • (S(x₂₁) * x₂₂) = φ(x) • 1`. -/
private theorem mul_rTensor_antipode_comp_matrixCoefficientLinear_comul
    (φ : Module.Dual R H) (x : H) :
    LinearMap.mul' R H
        ((HopfAlgebra.antipode R ∘ₗ
          Comodule.matrixCoefficientLinear (R := R) (C := H) (M := H) φ).rTensor H
          (Coalgebra.comul (R := R) x)) =
      φ x • (1 : H) := by
  let Ω : H ⊗[R] (H ⊗[R] H) →ₗ[R] H :=
    (TensorProduct.lid R H).toLinearMap ∘ₗ
      TensorProduct.map φ (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H)
  have hΩ_left (w : H ⊗[R] H) :
      LinearMap.mul' R H
        ((HopfAlgebra.antipode R ∘ₗ
          Comodule.matrixCoefficientLinear (R := R) (C := H) (M := H) φ).rTensor H w) =
        Ω (TensorProduct.assoc R H H H ((Coalgebra.comul (R := R)).rTensor H w)) := by
    induction w using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, hu, hv]
    | tmul a b =>
      simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply,
        Comodule.matrixCoefficientLinear_apply, Comodule.matrixCoefficient_def,
        Comodule.instSelf_coact]
      induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
      | add u v hu hv => simp only [map_add, TensorProduct.add_tmul, hu, hv]
      | tmul a₁ a₂ => simp [Ω]
  have hΩ_right (w : H ⊗[R] H) :
      Ω ((Coalgebra.comul (R := R)).lTensor H w) =
        φ (TensorProduct.rid R H ((Coalgebra.counit (R := R)).lTensor H w)) • (1 : H) := by
    induction w using TensorProduct.inductionOn with
    | add u v hu hv => simp only [map_add, add_smul, hu, hv]
    | tmul u v =>
      simp [Ω, Algebra.algebraMap_eq_smul_one, mul_smul]
  rw [hΩ_left, Coalgebra.coassoc_apply, hΩ_right, Coalgebra.lTensor_counit_comul,
    TensorProduct.rid_tmul, one_smul]

variable [Module.Finite R H] [Module.Projective R H]

/-- The linear dual `Module.Dual R H` of a finite projective Hopf algebra `H` is a right
`H`-Hopf module for `dualRightModule` and `Comodule.dual R H H`. -/
theorem isRightHopfModule_dual : IsRightHopfModule R H (Module.Dual R H) where
  coact_op_smul h φ := by
    apply (dualTensorHom_bijective (R := R) (M := H) (N := H)).1
    ext y
    rw [Comodule.dual_coact, Comodule.dualTensorHom_dualCoact_apply,
      dualTensorHom_rTensor_opSMulTensor_tensorCombine, Comodule.dualTensorHom_dualCoact]
    have hRHS :
        (HopfAlgebra.antipode R (A := H)).comp
          (Comodule.matrixCoefficientBilinear (R := R) (C := H) (M := H) φ) ∘ₗ
            LinearMap.mulRight R y =
          HopfAlgebra.antipode R ∘ₗ (TensorProduct.lid R H).toLinearMap ∘ₗ
            φ.rTensor H ∘ₗ LinearMap.mulRight R (Coalgebra.comul (R := R) y) ∘ₗ
              Coalgebra.comul (R := R) :=
      LinearMap.ext fun x => by
        simp [Comodule.matrixCoefficient_def, Comodule.instSelf_coact, LinearMap.rTensor_def,
          Bialgebra.comul_mul]
    rw [hRHS, Comodule.matrixCoefficient_def, Comodule.instSelf_coact]
    induction Coalgebra.comul (R := R) y using TensorProduct.inductionOn with
    | add u v hu hv =>
      have hmul_add :
          LinearMap.mulRight R (u + v) = LinearMap.mulRight R u + LinearMap.mulRight R v :=
        LinearMap.ext fun z => mul_add z u v
      simp only [map_add, hmul_add, LinearMap.comp_add, LinearMap.add_comp, LinearMap.rTensor_add,
        LinearMap.add_apply, hu, hv]
    | tmul y₁ y₂ =>
      -- Pull left multiplication by `S(y₂)` out of the coproduct contraction and cancel via
      -- `mul_rTensor_antipode_comp_matrixCoefficientLinear_comul` on `φ ∘ mulRight y₁`.
      have hstep :
          HopfAlgebra.antipode R ∘ₗ (TensorProduct.lid R H).toLinearMap ∘ₗ
            φ.rTensor H ∘ₗ LinearMap.mulRight R (y₁ ⊗ₜ[R] y₂) ∘ₗ Coalgebra.comul (R := R) =
          LinearMap.mulLeft R (HopfAlgebra.antipode R y₂) ∘ₗ
            (HopfAlgebra.antipode R ∘ₗ
              Comodule.matrixCoefficientLinear (R := R) (C := H) (M := H)
                (φ ∘ₗ LinearMap.mulRight R y₁)) :=
        LinearMap.ext fun a => by
          simp only [LinearMap.comp_apply, Comodule.matrixCoefficientLinear_apply,
            Comodule.matrixCoefficient_def, Comodule.instSelf_coact]
          induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
          | add u v hu hv => simp only [map_add, hu, hv]
          | tmul a₁ a₂ => simp [_root_.HopfAlgebra.antipode_mul_antidistrib]
      have hmulLeft (w : H ⊗[R] H) :
          LinearMap.mul' R H ((LinearMap.mulLeft R (HopfAlgebra.antipode R y₂)).rTensor H w) =
            HopfAlgebra.antipode R y₂ * LinearMap.mul' R H w := by
        induction w using TensorProduct.inductionOn with
        | add u v hu hv => simp only [map_add, mul_add, hu, hv]
        | tmul a b => simp [mul_assoc]
      rw [hstep, LinearMap.rTensor_comp_apply, hmulLeft,
        mul_rTensor_antipode_comp_matrixCoefficientLinear_comul]
      simp

variable {R H} in
/-- Coinvariants of the dual right `H`-comodule `Module.Dual R H` are precisely right cointegrals on
`H`. Neither subtraction on `R` nor bijectivity of the antipode is needed. -/
theorem mem_fixedSubcomodule_dual_iff (φ : Module.Dual R H) :
    φ ∈ Comodule.fixedSubcomodule R H (Module.Dual R H) ↔ IsRightCointegral φ := by
  rw [Comodule.mem_fixedSubcomodule, Comodule.dual_coact, isRightCointegral_def,
    ← (dualTensorHom_bijective (R := R) (M := H) (N := H)).1.eq_iff, LinearMap.ext_iff]
  simp only [Comodule.dualTensorHom_dualCoact_apply, dualTensorHom_apply]
  constructor
  · intro hφ x
    have hmap :
        HopfAlgebra.antipode R ∘ₗ
            Comodule.matrixCoefficientLinear (R := R) (C := H) (M := H) φ =
          LinearMap.toSpanSingleton R H 1 ∘ₗ φ :=
      LinearMap.ext hφ
    have hcancel := mul_rTensor_antipode_comp_matrixCoefficientLinear_comul R H φ x
    rw [hmap, LinearMap.rTensor_comp_apply] at hcancel
    have hlid (z : R ⊗[R] H) :
        LinearMap.mul' R H ((LinearMap.toSpanSingleton R H 1).rTensor H z) =
          TensorProduct.lid R H z := by
      induction z using TensorProduct.inductionOn with
      | add u v hu hv => simp only [map_add, hu, hv]
      | tmul r b => simp [Algebra.smul_def]
    exact (hlid _).symm.trans hcancel
  · intro hφ y
    rw [Comodule.matrixCoefficient_def, Comodule.instSelf_coact, ← LinearMap.rTensor_def, hφ y,
      map_smul, _root_.HopfAlgebra.antipode_one]

/-- The fixed subcomodule of `Module.Dual R H` is `R`-linearly equivalent to `rightCointegrals R H`
via the identity on underlying functionals. -/
def dualFixedEquivRightCointegrals :
    Comodule.fixedSubcomodule R H (Module.Dual R H) ≃ₗ[R] rightCointegrals R H :=
  LinearEquiv.ofEq (Comodule.fixedSubcomodule R H (Module.Dual R H)).toSubmodule
    (rightCointegrals R H)
    (Submodule.ext fun φ => (mem_fixedSubcomodule_dual_iff φ).trans (mem_rightCointegrals φ).symm)

variable {R H} in
/-- `dualFixedEquivRightCointegrals` preserves the underlying linear functional. -/
@[simp]
theorem coe_dualFixedEquivRightCointegrals
    (φ : Comodule.fixedSubcomodule R H (Module.Dual R H)) :
    (dualFixedEquivRightCointegrals R H φ : Module.Dual R H) = φ :=
  LinearEquiv.coe_ofEq_apply _ φ

variable {R H} in
/-- `(dualFixedEquivRightCointegrals R H).symm` preserves the underlying linear functional. -/
@[simp]
theorem coe_dualFixedEquivRightCointegrals_symm (φ : rightCointegrals R H) :
    ((dualFixedEquivRightCointegrals R H).symm φ : Module.Dual R H) = φ :=
  (coe_dualFixedEquivRightCointegrals _).symm.trans
    (congrArg Subtype.val ((dualFixedEquivRightCointegrals R H).apply_symm_apply φ))

end HopfAlgebra

end DualHopfModule

end RightHopfModule

section CointegralDecomposition

variable (R : Type u) (H : Type v) [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]
  [Module.Finite R H] [Module.Projective R H]

/-- **Larson–Sweedler Cointegral Decomposition**: for any finite projective Hopf algebra `H` over a
commutative semiring `R`, the right-action map `φ ⊗ h ↦ DomMulAct.mk h • φ` (`x ↦ φ (h * x)`) is an
`R`-linear equivalence `rightCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H`. -/
def rightCointegralsTensorEquivDual :
    rightCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H :=
  letI := Comodule.dual R H H
  letI := RightHopfModule.dualRightModule R H
  haveI := RightHopfModule.isRightHopfModule_dual R H
  (TensorProduct.congr (RightHopfModule.dualFixedEquivRightCointegrals R H).symm
    (LinearEquiv.refl R H)).trans
    (RightHopfModule.coinvariantTensorEquiv R H (Module.Dual R H))

variable {R H}

/-- On pure tensors, `rightCointegralsTensorEquivDual` translates the cointegral by
`DomMulAct.mk h`. -/
@[simp]
theorem rightCointegralsTensorEquivDual_tmul (φ : rightCointegrals R H) (h : H) :
    rightCointegralsTensorEquivDual R H (φ ⊗ₜ[R] h) = DomMulAct.mk h • (φ : Module.Dual R H) := by
  let := Comodule.dual R H H
  let := RightHopfModule.dualRightModule R H
  have := RightHopfModule.isRightHopfModule_dual R H
  simp [rightCointegralsTensorEquivDual, RightHopfModule.dualRightModule_op_smul_eq_domMulAct]

/-- Pointwise evaluation of `rightCointegralsTensorEquivDual` on a pure tensor:
`rightCointegralsTensorEquivDual (φ ⊗ h) x = φ (h * x)`. -/
theorem rightCointegralsTensorEquivDual_tmul_apply (φ : rightCointegrals R H) (h x : H) :
    rightCointegralsTensorEquivDual R H (φ ⊗ₜ[R] h) x = (φ : Module.Dual R H) (h * x) := by
  rw [rightCointegralsTensorEquivDual_tmul, DomMulAct.mk_smul_linearMap_apply, smul_eq_mul]

/-- `rightCointegralsTensorEquivDual` is equivariant for right multiplication on the `H` factor and
`DomMulAct` on `Module.Dual R H`. -/
theorem rightCointegralsTensorEquivDual_tmul_mul (φ : rightCointegrals R H) (x h : H) :
    rightCointegralsTensorEquivDual R H (φ ⊗ₜ[R] (x * h)) =
      DomMulAct.mk h • rightCointegralsTensorEquivDual R H (φ ⊗ₜ[R] x) := by
  ext y
  rw [rightCointegralsTensorEquivDual_tmul_apply, DomMulAct.mk_smul_linearMap_apply,
    rightCointegralsTensorEquivDual_tmul_apply, smul_eq_mul, mul_assoc]

/-- The right-cointegral submodule of a finite projective `R`-Hopf algebra is projective over
`R`. -/
instance instModuleProjectiveRightCointegrals : Module.Projective R (rightCointegrals R H) :=
  letI := Comodule.dual R H H
  letI := RightHopfModule.dualRightModule R H
  haveI := RightHopfModule.isRightHopfModule_dual R H
  haveI := RightHopfModule.projective_fixedSubcomodule R H (Module.Dual R H)
  Module.Projective.of_equiv (RightHopfModule.dualFixedEquivRightCointegrals R H)

/-- The right-cointegral submodule of a finite projective `R`-Hopf algebra is finitely generated
over `R`. -/
instance instModuleFiniteRightCointegrals : Module.Finite R (rightCointegrals R H) :=
  letI := Comodule.dual R H H
  letI := RightHopfModule.dualRightModule R H
  haveI := RightHopfModule.isRightHopfModule_dual R H
  haveI := RightHopfModule.finite_fixedSubcomodule R H (Module.Dual R H)
  Module.Finite.equiv (RightHopfModule.dualFixedEquivRightCointegrals R H)

variable (R H) in
/-- Every finite projective Hopf algebra over a nontrivial commutative semiring admits a nonzero
right cointegral. -/
theorem exists_isRightCointegral_ne_zero [Nontrivial R] :
    ∃ φ : Module.Dual R H, IsRightCointegral φ ∧ φ ≠ 0 := by
  by_contra h
  push Not at h
  have hsub (x : rightCointegrals R H) : x = 0 :=
    Subtype.ext (h x.val ((mem_rightCointegrals _).mp x.property))
  have hzero (t : rightCointegrals R H ⊗[R] H) : t = 0 := by
    induction t using TensorProduct.inductionOn with
    | add t₁ t₂ ht₁ ht₂ => simp [ht₁, ht₂]
    | tmul x y => rw [hsub x, TensorProduct.zero_tmul]
  have hcounit : Coalgebra.counit (R := R) (A := H) = 0 := by
    have hsymm := hzero ((rightCointegralsTensorEquivDual R H).symm
      (Coalgebra.counit (R := R) (A := H)))
    simpa [hsymm] using
      ((rightCointegralsTensorEquivDual R H).apply_symm_apply
        (Coalgebra.counit (R := R) (A := H))).symm
  have h1 := LinearMap.congr_fun hcounit (1 : H)
  simp at h1

end CointegralDecomposition

end TauCeti
