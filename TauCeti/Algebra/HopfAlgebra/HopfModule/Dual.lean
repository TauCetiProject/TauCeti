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

Both the right Hopf-module compatibility (`dualIsRightHopfModule`) and the identification of the
coinvariant subcomodule with `rightCointegrals R H` (`mem_dual_fixedSubcomodule_iff`) hold over any
commutative semiring `R`, without assuming bijectivity of the antipode or choosing a basis.
Specializing the Fundamental Theorem of Hopf Modules (`RightHopfModule.coinvariantTensorEquiv`) to
`Module.Dual R H` yields Larson and Sweedler's **cointegral decomposition**
(`rightCointegralsTensorEquivDual`):

`rightCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H`,

sending `φ ⊗ h` to `DomMulAct.mk h • φ` (`x ↦ φ (h * x)`). As an immediate consequence over any
commutative semiring `R`, `rightCointegrals R H` is a finitely generated projective `R`-module.

## Main declarations

* `TauCeti.RightHopfModule.dualRightModule`, `TauCeti.RightHopfModule.dualIsRightHopfModule`: the
  right `H`-Hopf module structure on `Module.Dual R H`.
* `TauCeti.RightHopfModule.mem_dual_fixedSubcomodule_iff` and
  `TauCeti.RightHopfModule.dualFixedEquivRightCointegrals`: coinvariants of `Module.Dual R H` are
  precisely the right cointegrals on `H`.
* `TauCeti.rightCointegralsTensorEquivDual`: the canonical `R`-linear isomorphism
  `rightCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H`, equivariant for right `H`-multiplication.
* `TauCeti.instModuleProjectiveRightCointegrals`, `TauCeti.instModuleFiniteRightCointegrals`:
  `rightCointegrals R H` is finitely generated and projective over `R`.

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
    rw [dualRightModule_op_smul_apply]
    rfl

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

variable [Module.Finite R H] [Module.Projective R H]

/-- The linear dual `Module.Dual R H` of a finite projective Hopf algebra `H` is a right
`H`-Hopf module for `dualRightModule` and `Comodule.dual R H H`. -/
theorem dualIsRightHopfModule : IsRightHopfModule R H (Module.Dual R H) where
  coact_op_smul h φ := by
    apply (dualTensorHom_bijective (R := R) (M := H) (N := H)).1
    ext y
    rw [Comodule.dual_coact, Comodule.dualTensorHom_dualCoact_apply,
      dualTensorHom_rTensor_opSMulTensor_tensorCombine, Comodule.dualTensorHom_dualCoact]
    -- Expand `matrixCoefficient` on both sides and induct on `Δ(y)` so `y` enters via pure
    -- coproduct factors `y₁ ⊗ y₂`.
    have hRHS_mc (x : H) :
        ((HopfAlgebra.antipode R (A := H)).comp
          (Comodule.matrixCoefficientBilinear (R := R) (C := H) (M := H) φ) ∘ₗ
            LinearMap.mulRight R y) x =
          HopfAlgebra.antipode R
            (TensorProduct.lid R H
              (φ.rTensor H (Coalgebra.comul (R := R) x * Coalgebra.comul (R := R) y))) := by
      simp [Comodule.matrixCoefficient_def, Comodule.instSelf_coact, LinearMap.rTensor_def,
        Bialgebra.comul_mul]
    have hRHS_ext :
        (HopfAlgebra.antipode R (A := H)).comp
          (Comodule.matrixCoefficientBilinear (R := R) (C := H) (M := H) φ) ∘ₗ
            LinearMap.mulRight R y =
          HopfAlgebra.antipode R ∘ₗ (TensorProduct.lid R H).toLinearMap ∘ₗ
            φ.rTensor H ∘ₗ LinearMap.mulRight R (Coalgebra.comul (R := R) y) ∘ₗ
              Coalgebra.comul (R := R) :=
      LinearMap.ext hRHS_mc
    rw [hRHS_ext, Comodule.matrixCoefficient_def, Comodule.instSelf_coact]
    generalize Coalgebra.comul (R := R) y = cy
    induction cy using TensorProduct.inductionOn with
    | add u v hu hv =>
      have hmul_add :
          LinearMap.mulRight R (u + v) = LinearMap.mulRight R u + LinearMap.mulRight R v :=
        LinearMap.ext fun z => mul_add z u v
      simp only [map_add, hmul_add, LinearMap.comp_add, LinearMap.add_comp, LinearMap.rTensor_add,
        LinearMap.add_apply, hu, hv]
    | tmul y₁ y₂ =>
      -- Build `Ξ : H ⊗[R] (H ⊗[R] H) →ₗ[R] H` sending `a ⊗ (b₁ ⊗ b₂)` to
      -- `φ(a * y₁) • (S(y₂) * (S(b₁) * b₂))`; coassociativity cancels `S(h₂₁) * h₂₂` to `ε(h₂)`.
      let Ξ : H ⊗[R] (H ⊗[R] H) →ₗ[R] H :=
        (TensorProduct.lid R H).toLinearMap ∘ₗ
          TensorProduct.map
            (φ ∘ₗ LinearMap.mulRight R y₁)
            (LinearMap.mulLeft R (HopfAlgebra.antipode R y₂) ∘ₗ
              LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H)
      have hΞ_right (w : H ⊗[R] H) :
          LinearMap.mul' R H
            ((HopfAlgebra.antipode R ∘ₗ (TensorProduct.lid R H).toLinearMap ∘ₗ
              φ.rTensor H ∘ₗ LinearMap.mulRight R (y₁ ⊗ₜ[R] y₂) ∘ₗ
                Coalgebra.comul (R := R)).rTensor H w) =
            Ξ (TensorProduct.assoc R H H H ((Coalgebra.comul (R := R)).rTensor H w)) := by
        induction w using TensorProduct.inductionOn with
        | add u v hu hv => simp only [map_add, hu, hv]
        | tmul h₁ h₂ =>
          simp only [LinearMap.rTensor_tmul, LinearMap.comp_apply]
          generalize Coalgebra.comul (R := R) h₁ = ch₁
          induction ch₁ using TensorProduct.inductionOn with
          | add u v hu hv =>
            simp only [LinearMap.mulRight_apply] at hu hv ⊢
            simp only [add_mul, map_add, TensorProduct.add_tmul, hu, hv]
          | tmul h₁₁ h₁₂ =>
            simp only [Ξ, LinearMap.mulRight_apply, Algebra.TensorProduct.tmul_mul_tmul,
              LinearMap.rTensor_tmul, LinearEquiv.coe_coe, TensorProduct.lid_tmul, map_smul,
              _root_.HopfAlgebra.antipode_mul_antidistrib, LinearMap.mul'_apply, smul_mul_assoc,
              mul_assoc, LinearMap.comp_apply, TensorProduct.assoc_tmul, TensorProduct.map_tmul,
              LinearMap.mulLeft_apply]
      rw [hΞ_right, Coalgebra.coassoc_apply]
      have hΞ_left (w : H ⊗[R] H) :
          Ξ ((Coalgebra.comul (R := R)).lTensor H w) =
            φ (TensorProduct.rid R H ((Coalgebra.counit (R := R)).lTensor H w) * y₁) •
              HopfAlgebra.antipode R y₂ := by
        induction w using TensorProduct.inductionOn with
        | add u v hu hv =>
          simp only [map_add, add_mul, add_smul, hu, hv]
        | tmul h₁ h₂ =>
          simp only [Ξ, LinearMap.lTensor_tmul, LinearMap.comp_apply, TensorProduct.map_tmul,
            LinearMap.mulRight_apply, _root_.HopfAlgebra.mul_antipode_rTensor_comul_apply,
            LinearMap.mulLeft_apply, Algebra.algebraMap_eq_smul_one, mul_one,
            LinearEquiv.coe_coe, TensorProduct.lid_tmul, smul_assoc, TensorProduct.rid_tmul,
            smul_mul_assoc, map_smul]
          rw [smul_comm]
      have hrid :
          TensorProduct.rid R H
            ((Coalgebra.counit (R := R)).lTensor H (Coalgebra.comul (R := R) h)) = h :=
        Comodule.rid_lTensor_counit_coact (R := R) (C := H) h
      rw [hΞ_left, hrid]
      simp

variable {R H} in
/-- Coinvariants of the dual right `H`-comodule `Module.Dual R H` are precisely right cointegrals on
`H`. Neither subtraction on `R` nor bijectivity of the antipode is needed. -/
theorem mem_dual_fixedSubcomodule_iff (φ : Module.Dual R H) :
    φ ∈ Comodule.fixedSubcomodule R H (Module.Dual R H) ↔ IsRightCointegral φ := by
  rw [Comodule.mem_fixedSubcomodule, Comodule.dual_coact, isRightCointegral_def,
    ← (dualTensorHom_bijective (R := R) (M := H) (N := H)).1.eq_iff, LinearMap.ext_iff]
  simp only [Comodule.dualTensorHom_dualCoact_apply, dualTensorHom_apply]
  constructor
  · intro hφ x
    -- Let `Ψ` contract `a ⊗ b` to `S(matrixCoefficient φ a) * b`: by `hφ` this evaluates on `Δ(x)`
    -- to `∑ φ(x₁) • x₂`, while by coassociativity `S(x₁₂) * x₂` cancels to `ε(x₂) • 1`.
    let Ψ : H ⊗[R] H →ₗ[R] H :=
      LinearMap.mul' R H ∘ₗ
        (HopfAlgebra.antipode R ∘ₗ
          Comodule.matrixCoefficientLinear (R := R) (C := H) (M := H) φ).rTensor H
    have hΨ_lhs (w : H ⊗[R] H) :
        Ψ w = TensorProduct.lid R H (φ.rTensor H w) := by
      induction w using TensorProduct.inductionOn with
      | add u v hu hv => simp only [map_add, hu, hv]
      | tmul a b =>
        simp only [Ψ, LinearMap.comp_apply, LinearMap.rTensor_tmul,
          Comodule.matrixCoefficientLinear_apply, hφ a, LinearMap.mul'_apply, smul_mul_assoc,
          one_mul, TensorProduct.lid_tmul]
    let Ω : H ⊗[R] (H ⊗[R] H) →ₗ[R] H :=
      (TensorProduct.lid R H).toLinearMap ∘ₗ
        TensorProduct.map φ (LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R).rTensor H)
    have hΨ_omega (w : H ⊗[R] H) :
        Ψ w = Ω (TensorProduct.assoc R H H H ((Coalgebra.comul (R := R)).rTensor H w)) := by
      induction w using TensorProduct.inductionOn with
      | add u v hu hv => simp only [map_add, hu, hv]
      | tmul a b =>
        simp only [Ψ, LinearMap.comp_apply, LinearMap.rTensor_tmul,
          Comodule.matrixCoefficientLinear_apply, Comodule.matrixCoefficient_def,
          Comodule.instSelf_coact]
        generalize Coalgebra.comul (R := R) a = ca
        induction ca using TensorProduct.inductionOn with
        | add u v hu hv =>
          simp only [map_add, TensorProduct.add_tmul, hu, hv]
        | tmul a₁ a₂ =>
          simp [Ω]
    have hΩ_rhs (w : H ⊗[R] H) :
        Ω ((Coalgebra.comul (R := R)).lTensor H w) =
          φ (TensorProduct.rid R H ((Coalgebra.counit (R := R)).lTensor H w)) • (1 : H) := by
      induction w using TensorProduct.inductionOn with
      | add u v hu hv => simp only [map_add, add_smul, hu, hv]
      | tmul u v =>
        simp only [Ω, LinearMap.lTensor_tmul, LinearMap.comp_apply, TensorProduct.map_tmul,
          _root_.HopfAlgebra.mul_antipode_rTensor_comul_apply, Algebra.algebraMap_eq_smul_one,
          LinearEquiv.coe_coe, TensorProduct.lid_tmul, TensorProduct.rid_tmul, map_smul,
          smul_eq_mul]
        rw [← mul_smul, mul_comm]
    have hrid :
        TensorProduct.rid R H
          ((Coalgebra.counit (R := R)).lTensor H (Coalgebra.comul (R := R) x)) = x :=
      Comodule.rid_lTensor_counit_coact (R := R) (C := H) x
    rw [← hΨ_lhs, hΨ_omega, Coalgebra.coassoc_apply, hΩ_rhs, hrid]
  · intro hφ y
    have hy : Comodule.matrixCoefficient (R := R) (C := H) φ y = φ y • (1 : H) := hφ y
    rw [hy, map_smul, _root_.HopfAlgebra.antipode_one]

/-- The fixed subcomodule of `Module.Dual R H` is `R`-linearly equivalent to `rightCointegrals R H`
via the identity on underlying functionals. -/
def dualFixedEquivRightCointegrals :
    Comodule.fixedSubcomodule R H (Module.Dual R H) ≃ₗ[R] rightCointegrals R H where
  toFun φ := ⟨φ.1, (mem_rightCointegrals φ.1).mpr ((mem_dual_fixedSubcomodule_iff φ.1).mp φ.2)⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl
  invFun φ := ⟨φ.1, (mem_dual_fixedSubcomodule_iff φ.1).mpr ((mem_rightCointegrals φ.1).mp φ.2)⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

variable {R H} in
@[simp]
theorem coe_dualFixedEquivRightCointegrals
    (φ : Comodule.fixedSubcomodule R H (Module.Dual R H)) :
    (dualFixedEquivRightCointegrals R H φ : Module.Dual R H) = φ := (rfl)

variable {R H} in
@[simp]
theorem coe_dualFixedEquivRightCointegrals_symm (φ : rightCointegrals R H) :
    ((dualFixedEquivRightCointegrals R H).symm φ : Module.Dual R H) = φ := (rfl)

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
  haveI := RightHopfModule.dualIsRightHopfModule R H
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
  have := RightHopfModule.dualIsRightHopfModule R H
  simp [rightCointegralsTensorEquivDual, RightHopfModule.dualRightModule_op_smul_eq_domMulAct]

/-- Pointwise evaluation of `rightCointegralsTensorEquivDual` on a pure tensor:
`rightCointegralsTensorEquivDual (φ ⊗ h) x = φ (h * x)`. -/
theorem rightCointegralsTensorEquivDual_tmul_apply (φ : rightCointegrals R H) (h x : H) :
    rightCointegralsTensorEquivDual R H (φ ⊗ₜ[R] h) x = (φ : Module.Dual R H) (h * x) := by
  rw [rightCointegralsTensorEquivDual_tmul]
  rfl

/-- `rightCointegralsTensorEquivDual` is equivariant for right multiplication on the `H` factor and
`DomMulAct` on `Module.Dual R H`. -/
theorem rightCointegralsTensorEquivDual_tmul_mul (φ : rightCointegrals R H) (x h : H) :
    rightCointegralsTensorEquivDual R H (φ ⊗ₜ[R] (x * h)) =
      DomMulAct.mk h • rightCointegralsTensorEquivDual R H (φ ⊗ₜ[R] x) := by
  let := RightHopfModule.dualRightModule R H
  ext y
  rw [rightCointegralsTensorEquivDual_tmul_apply,
    ← RightHopfModule.dualRightModule_op_smul_eq_domMulAct,
    RightHopfModule.dualRightModule_op_smul_apply, rightCointegralsTensorEquivDual_tmul_apply,
    mul_assoc]

/-- The right-cointegral submodule of a finite projective `R`-Hopf algebra is projective over
`R`. -/
instance instModuleProjectiveRightCointegrals : Module.Projective R (rightCointegrals R H) := by
  -- `φ ↦ φ ⊗ 1` splits `rightCointegrals R H` off `rightCointegrals R H ⊗[R] H` via `ε`.
  have : Module.Projective R (rightCointegrals R H ⊗[R] H) :=
    Module.Projective.of_equiv (rightCointegralsTensorEquivDual R H).symm
  refine Module.Projective.of_split
    ((TensorProduct.mk R (rightCointegrals R H) H).flip (1 : H))
    ((TensorProduct.rid R (rightCointegrals R H)).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := H)).lTensor (rightCointegrals R H)) ?_
  ext φ
  simp

/-- The right-cointegral submodule of a finite projective `R`-Hopf algebra is finitely generated
over `R`. -/
instance instModuleFiniteRightCointegrals : Module.Finite R (rightCointegrals R H) := by
  have : Module.Finite R (rightCointegrals R H ⊗[R] H) :=
    Module.Finite.equiv (rightCointegralsTensorEquivDual R H).symm
  refine Module.Finite.of_surjective
    ((TensorProduct.rid R (rightCointegrals R H)).toLinearMap ∘ₗ
      (Coalgebra.counit (R := R) (A := H)).lTensor (rightCointegrals R H))
    (fun φ => ⟨φ ⊗ₜ[R] (1 : H), by simp⟩)

end CointegralDecomposition

end TauCeti
