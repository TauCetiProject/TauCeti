/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.FiniteType
import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.Algebra.HopfAlgebra.Cointegral.Basic
public import TauCeti.Algebra.HopfAlgebra.Frobenius
import TauCeti.Algebra.HopfAlgebra.HopfModule
public import TauCeti.Algebra.HopfAlgebra.InverseAntipode
import TauCeti.Algebra.Module.Injective.Frobenius

/-!
# The Larson–Sweedler theorem and Frobenius property of finite Hopf algebras

For any finite projective Hopf algebra `H` over a commutative semiring `R`, the linear dual
`Module.Dual R H` with its dual comodule structure `TauCeti.Comodule.dual R H H` and the right
`H`-action `(φ · x)(h) = φ(x * h)` forms a right-right Hopf module. Its coinvariants are
precisely the right cointegrals `TauCeti.rightCointegrals R H`, so the fundamental theorem of
Hopf modules yields a canonical `R`-linear equivalence

```text
rightCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H,    φ ⊗ x ↦ (h ↦ φ(x * h)).
```

In particular, whenever `R` is nontrivial, `H` admits a nonzero right cointegral.

Over a field `k`, for any finite-dimensional Hopf algebra `H`:

* `rightCointegrals k H`, `leftCointegrals k H`, `leftIntegral k H`, and `rightIntegral k H` are
  all one-dimensional;
* every nonzero right or left cointegral is a Frobenius functional
  (`LinearMap.IsFrobeniusFunctional`), so `H` is a Frobenius algebra, self-injective on both
  sides, and its projective and injective modules coincide;
* the antipode `HopfAlgebra.antipode k` is bijective.

Over an arbitrary commutative semiring (and for the partner formulas, any commutative ring),
normalized integrals and cointegrals provide explicit basis-free Frobenius dual-basis
reconstruction formulas without assuming finite-dimensionality or a base field. We also identify
the cointegral submodules of any finite projective bialgebra `H` with the integral submodules of
its convolution dual `TauCeti.ConvolutionDual R H`.

## Main declarations

* `TauCeti.isRightCointegral_iff_isRightInvariantIntegral` and
  `TauCeti.isLeftCointegral_iff_isLeftInvariantIntegral`: bridge between cointegrals and invariant
  integrals.
* `TauCeti.rightCointegralsEquivRightIntegral` and `TauCeti.leftCointegralsEquivLeftIntegral`:
  identifications of cointegrals of `H` with integrals of `ConvolutionDual R H`.
* `TauCeti.rightCointegralsTensorEquivDual`: the canonical isomorphism
  `rightCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H` for a finite projective Hopf algebra.
* `TauCeti.exists_isRightCointegral_ne_zero`: existence of a nonzero right cointegral over any
  nontrivial commutative semiring.
* `TauCeti.finrank_rightCointegrals`, `TauCeti.finrank_leftCointegrals`,
  `TauCeti.finrank_leftIntegral`, `TauCeti.finrank_rightIntegral`: all four integral and
  cointegral spaces are one-dimensional over a field.
* `TauCeti.IsRightCointegral.isFrobeniusFunctional`,
  `TauCeti.IsLeftCointegral.isFrobeniusFunctional`, `TauCeti.exists_isFrobeniusFunctional`:
  nonzero cointegrals are Frobenius functionals and exist unconditionally.
* `TauCeti.antipode_bijective`: bijectivity of the antipode in finite dimension.
* `TauCeti.moduleInjective_self`, `TauCeti.moduleInjective_op_self`, and
  `TauCeti.moduleProjective_iff_moduleInjective`: two-sided self-injectivity and coincidence of
  projective and injective modules over a finite-dimensional Hopf algebra.
* `TauCeti.IsRightCointegral.sum_apply_mul_smul_antipode`,
  `TauCeti.IsRightCointegral.sum_apply_antipode_mul_smul`,
  `TauCeti.IsLeftCointegral.sum_apply_mul_smul_antipode`,
  `TauCeti.IsLeftCointegral.sum_apply_mul_antipode_smul`,
  `TauCeti.IsRightCointegral.sum_apply_mul_smul_inverseAntipode`, and
  `TauCeti.IsRightCointegral.sum_apply_mul_inverseAntipode_smul`: basis-free Frobenius dual-basis
  reconstruction formulas from normalized integrals and cointegrals.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, AMS, 1993, Chapter 2.
* D. Fischman, S. Montgomery, and H.-J. Schneider, *Frobenius extensions of subalgebras of Hopf
  algebras*, Trans. Amer. Math. Soc. 349 (1997), 4857–4895, Lemma 1.5.
-/

public section

open scoped TensorProduct Coalgebra

namespace TauCeti

universe u v w

/-! ## Cointegrals, invariant integrals, and integrals of the convolution dual -/

section BialgebraBridge

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [Bialgebra R H]

/-- A right cointegral is equivalently a right invariant integral in the sense of
`LinearMap.IsRightInvariantIntegral`. -/
theorem isRightCointegral_iff_isRightInvariantIntegral {φ : Module.Dual R H} :
    IsRightCointegral φ ↔ φ.IsRightInvariantIntegral :=
  (isRightCointegral_def φ).trans LinearMap.isRightInvariantIntegral_iff.symm

/-- A left cointegral is equivalently a left invariant integral in the sense of
`LinearMap.IsLeftInvariantIntegral`. -/
theorem isLeftCointegral_iff_isLeftInvariantIntegral {φ : Module.Dual R H} :
    IsLeftCointegral φ ↔ φ.IsLeftInvariantIntegral :=
  (isLeftCointegral_def φ).trans LinearMap.isLeftInvariantIntegral_iff.symm

variable [Module.Finite R H] [Module.Projective R H]

/-- A functional on a finite projective bialgebra is a right cointegral if and only if it is a
right integral of the convolution dual bialgebra. -/
theorem isRightCointegral_iff_mem_rightIntegral_convolutionDual {φ : Module.Dual R H} :
    IsRightCointegral φ ↔ WithConv.toConv φ ∈ rightIntegral R (ConvolutionDual R H) := by
  rw [isRightCointegral_iff_convMul, mem_rightIntegral_iff]
  simp only [ConvolutionDual.counit_apply]

/-- A functional on a finite projective bialgebra is a left cointegral if and only if it is a
left integral of the convolution dual bialgebra. -/
theorem isLeftCointegral_iff_mem_leftIntegral_convolutionDual {φ : Module.Dual R H} :
    IsLeftCointegral φ ↔ WithConv.toConv φ ∈ leftIntegral R (ConvolutionDual R H) := by
  rw [isLeftCointegral_iff_convMul, mem_leftIntegral_iff]
  simp only [ConvolutionDual.counit_apply]

variable (R H) in
/-- The linear equivalence identifying right cointegrals of `H` with right integrals of
`ConvolutionDual R H`. -/
noncomputable def rightCointegralsEquivRightIntegral :
    rightCointegrals R H ≃ₗ[R] rightIntegral R (ConvolutionDual R H) :=
  (WithConv.linearEquiv R (Module.Dual R H)).symm.ofSubmodules _ _ (by
    ext ψ
    rw [Submodule.mem_map_equiv]
    simp [isRightCointegral_iff_mem_rightIntegral_convolutionDual])

variable (R H) in
/-- The linear equivalence identifying left cointegrals of `H` with left integrals of
`ConvolutionDual R H`. -/
noncomputable def leftCointegralsEquivLeftIntegral :
    leftCointegrals R H ≃ₗ[R] leftIntegral R (ConvolutionDual R H) :=
  (WithConv.linearEquiv R (Module.Dual R H)).symm.ofSubmodules _ _ (by
    ext ψ
    rw [Submodule.mem_map_equiv]
    simp [isLeftCointegral_iff_mem_leftIntegral_convolutionDual])

@[simp]
theorem rightCointegralsEquivRightIntegral_apply (φ : rightCointegrals R H) :
    (rightCointegralsEquivRightIntegral R H φ : ConvolutionDual R H) = WithConv.toConv φ.1 :=
  (rfl)

@[simp]
theorem rightCointegralsEquivRightIntegral_symm_apply
    (ψ : rightIntegral R (ConvolutionDual R H)) :
    ((rightCointegralsEquivRightIntegral R H).symm ψ : Module.Dual R H) = ψ.1.ofConv :=
  (rfl)

@[simp]
theorem leftCointegralsEquivLeftIntegral_apply (φ : leftCointegrals R H) :
    (leftCointegralsEquivLeftIntegral R H φ : ConvolutionDual R H) = WithConv.toConv φ.1 :=
  (rfl)

@[simp]
theorem leftCointegralsEquivLeftIntegral_symm_apply
    (ψ : leftIntegral R (ConvolutionDual R H)) :
    ((leftCointegralsEquivLeftIntegral R H).symm ψ : Module.Dual R H) = ψ.1.ofConv :=
  (rfl)

end BialgebraBridge

/-! ## The right Hopf module structure on the linear dual -/

section DualHopfModule

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- The right `H`-action `(φ · x)(h) = φ(x * h)` on `Module.Dual R H`, installed locally to
equip `Module.Dual R H` with a right-right Hopf module structure over `H`. -/
private local instance instDualOpSMul : SMul Hᵐᵒᵖ (Module.Dual R H) where
  smul x φ := φ ∘ₗ LinearMap.mulLeft R x.unop

@[simp]
private theorem dualOpSmul_apply (x : Hᵐᵒᵖ) (φ : Module.Dual R H) (h : H) :
    (x • φ) h = φ (x.unop * h) :=
  (rfl)

private local instance instDualOpModule : Module Hᵐᵒᵖ (Module.Dual R H) where
  one_smul φ := LinearMap.ext fun h ↦ by simp
  mul_smul x y φ := LinearMap.ext fun h ↦ by simp [mul_assoc]
  smul_zero x := LinearMap.ext fun h ↦ by simp
  smul_add x φ ψ := LinearMap.ext fun h ↦ by simp
  add_smul x y φ := LinearMap.ext fun h ↦ by simp [add_mul]
  zero_smul φ := LinearMap.ext fun h ↦ by simp

private local instance instDualOpScalarTower : IsScalarTower R Hᵐᵒᵖ (Module.Dual R H) where
  smul_assoc r x φ := LinearMap.ext fun h ↦ by simp

/-- Helper contraction `u ⊗ v ↦ S(∑ φ(u * h₁) • h₂) * v` for Hopf-module compatibility on the
linear dual. -/
private noncomputable def dualCompatStep (φ : Module.Dual R H) (h : H) : H ⊗[R] H →ₗ[R] H :=
  TensorProduct.lift
    { toFun := fun u ↦
        LinearMap.mulLeft R
          (HopfAlgebra.antipode R
            (TensorProduct.lid R H
              ((φ ∘ₗ LinearMap.mulLeft R u).rTensor H (Coalgebra.comul (R := R) h))))
      map_add' := fun u₁ u₂ ↦ by
        ext v
        have hadd :
            φ ∘ₗ LinearMap.mulLeft R (u₁ + u₂) =
              φ ∘ₗ LinearMap.mulLeft R u₁ + φ ∘ₗ LinearMap.mulLeft R u₂ := by
          ext a
          simp [add_mul]
        dsimp only [LinearMap.add_apply, LinearMap.mulLeft_apply]
        rw [hadd, LinearMap.rTensor_add]
        simp [add_mul]
      map_smul' := fun r u ↦ by
        ext v
        have hsmul :
            φ ∘ₗ LinearMap.mulLeft R (r • u) = r • (φ ∘ₗ LinearMap.mulLeft R u) := by
          ext a
          simp
        dsimp only [RingHom.id_apply, LinearMap.smul_apply, LinearMap.mulLeft_apply]
        rw [hsmul, LinearMap.rTensor_smul]
        simp }

private theorem dualCompatStep_tmul (φ : Module.Dual R H) (h u v : H) :
    dualCompatStep φ h (u ⊗ₜ[R] v) =
      HopfAlgebra.antipode R
          (TensorProduct.lid R H
            ((φ ∘ₗ LinearMap.mulLeft R u).rTensor H (Coalgebra.comul (R := R) h))) * v :=
  (rfl)

/-- Helper evaluating the RHS of `RightHopfModule.coact_op_smul` after applying `dualTensorHom`. -/
private theorem dualTensorHom_rhs_compat
    (w : Module.Dual R H ⊗[R] H) (z : H ⊗[R] H) (h : H) :
    dualTensorHom R H H
        (TensorProduct.map (RightHopfModule.rightAct R H (Module.Dual R H))
          (LinearMap.mul' R H)
          (TensorProduct.tensorTensorTensorComm R (Module.Dual R H) H H H
            (w ⊗ₜ[R] z))) h =
      LinearMap.mul' R H ((dualTensorHom R H H w ∘ₗ LinearMap.mulRight R h).rTensor H z) := by
  induction w using TensorProduct.inductionOn with
  | add w₁ w₂ hw₁ hw₂ =>
    simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply,
      LinearMap.add_comp, LinearMap.rTensor_add, hw₁, hw₂]
  | tmul ψ a =>
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ =>
      simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hz₁, hz₂]
    | tmul x₁ x₂ =>
      simp [RightHopfModule.rightAct_tmul]

/-- Matrix-coefficient characterization of right cointegrals via the antipode:
`S(c(φ, h)) = φ(h) • 1` for all `h` if and only if `φ` is a right cointegral. -/
private theorem forall_antipode_matrixCoefficient_iff_isRightCointegral (φ : Module.Dual R H) :
    (∀ h : H, HopfAlgebra.antipode R (Comodule.matrixCoefficient (R := R) (C := H) φ h) =
        φ h • (1 : H)) ↔
      IsRightCointegral φ := by
  rw [isRightCointegral_def]
  have hmc (h : H) :
      Comodule.matrixCoefficient (R := R) (C := H) φ h =
        TensorProduct.lid R H (φ.rTensor H (Coalgebra.comul (R := R) h)) := by
    rw [Comodule.matrixCoefficient_def, Comodule.instSelf_coact, LinearMap.rTensor_def]
  refine ⟨fun hφ h ↦ ?_, fun hφ h ↦ by rw [hmc, hφ h, map_smul, HopfAlgebra.antipode_one]⟩
  let F : H ⊗[R] H →ₗ[R] H :=
    LinearMap.mul' R H ∘ₗ
      (HopfAlgebra.antipode R (A := H) ∘ₗ
        Comodule.matrixCoefficientLinear (R := R) (C := H) φ).rTensor H
  have hF1 (z : H ⊗[R] H) : F z = TensorProduct.lid R H (φ.rTensor H z) := by
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
    | tmul a b =>
      simp [F, hφ a]
  have hF2 (z : H ⊗[R] H) :
      F z = TensorProduct.lid R H
        (φ.rTensor H
          ((LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R (A := H)).rTensor H).lTensor H
            (TensorProduct.assoc R H H H
              ((Coalgebra.comul (R := R) (A := H)).rTensor H z)))) := by
    induction z using TensorProduct.inductionOn with
    | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
    | tmul a b =>
      simp only [F, LinearMap.comp_apply, LinearMap.rTensor_tmul, LinearMap.mul'_apply,
        Comodule.matrixCoefficientLinear_apply, hmc]
      induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
      | add a₁ a₂ ha₁ ha₂ => simp only [TensorProduct.add_tmul, map_add, add_mul, ha₁, ha₂]
      | tmul a₁ a₂ => simp
  rw [← hF1, hF2, Coalgebra.coassoc_apply, ← LinearMap.lTensor_comp_apply, LinearMap.comp_assoc,
    HopfAlgebra.mul_antipode_rTensor_comul, LinearMap.lTensor_comp_apply,
    Coalgebra.lTensor_counit_comul]
  simp

section FiniteProjective

variable [Module.Finite R H] [Module.Projective R H]

attribute [local instance] Comodule.dual

/-- `Module.Dual R H` with `Comodule.dual R H H` and `(φ · x)(h) = φ(x * h)` is a right-right
Hopf module. -/
private noncomputable local instance instDualRightHopfModule :
    RightHopfModule R H (Module.Dual R H) where
  coact_op_smul φ x := by
    apply (dualTensorHom_bijective (R := R) (M := H) (N := H)).1
    ext h
    rw [Comodule.dual_coact, Comodule.dualTensorHom_dualCoact_apply, dualTensorHom_rhs_compat]
    have hfactor (z : H ⊗[R] H) :
        LinearMap.mul' R H
            ((dualTensorHom R H H (Comodule.dualCoact (R := R) (H := H) (M := H) φ) ∘ₗ
              LinearMap.mulRight R h).rTensor H z) =
          dualCompatStep φ h
            ((LinearMap.mul' R H ∘ₗ (HopfAlgebra.antipode R (A := H)).rTensor H).lTensor H
              (TensorProduct.assoc R H H H
                ((Coalgebra.comul (R := R) (A := H)).rTensor H z))) := by
      induction z using TensorProduct.inductionOn with
      | add z₁ z₂ hz₁ hz₂ => simp only [map_add, hz₁, hz₂]
      | tmul a c =>
        simp only [LinearMap.rTensor_tmul, LinearMap.mul'_apply, LinearMap.comp_apply,
          LinearMap.mulRight_apply, Comodule.dualTensorHom_dualCoact_apply,
          Comodule.matrixCoefficient_def, Comodule.instSelf_coact, Bialgebra.comul_mul]
        induction Coalgebra.comul (R := R) a using TensorProduct.inductionOn with
        | add a₁ a₂ ha₁ ha₂ =>
          simp only [TensorProduct.add_tmul, map_add, add_mul, ha₁, ha₂]
        | tmul a₁ a₂ =>
          simp only [TensorProduct.assoc_tmul, LinearMap.lTensor_tmul, LinearMap.comp_apply,
            LinearMap.rTensor_tmul, LinearMap.mul'_apply, dualCompatStep_tmul]
          induction Coalgebra.comul (R := R) h using TensorProduct.inductionOn with
          | add h₁ h₂ hh₁ hh₂ => simp only [mul_add, add_mul, map_add, hh₁, hh₂]
          | tmul h₁ h₂ =>
            simp [Algebra.TensorProduct.tmul_mul_tmul, HopfAlgebra.antipode_mul_antidistrib,
              mul_assoc]
    rw [hfactor, Coalgebra.coassoc_apply, ← LinearMap.lTensor_comp_apply, LinearMap.comp_assoc,
      HopfAlgebra.mul_antipode_rTensor_comul, LinearMap.lTensor_comp_apply,
      Coalgebra.lTensor_counit_comul]
    simp only [LinearMap.lTensor_tmul, Algebra.linearMap_apply, map_one, dualCompatStep_tmul,
      mul_one, Comodule.matrixCoefficient_def, Comodule.instSelf_coact, LinearMap.rTensor_def]
    have hsmul : MulOpposite.op x • φ = φ ∘ₗ LinearMap.mulLeft R x :=
      LinearMap.ext fun a ↦ by simp
    rw [hsmul]

/-- The coinvariants of the dual right Hopf module `Module.Dual R H` are precisely the right
cointegrals. -/
private noncomputable def fixedEquivRightCointegrals :
    Comodule.fixedSubcomodule R H (Module.Dual R H) ≃ₗ[R] rightCointegrals R H where
  toFun φ :=
    ⟨φ.1, by
      rw [mem_rightCointegrals, ← forall_antipode_matrixCoefficient_iff_isRightCointegral]
      intro h
      have hfix := congrArg (dualTensorHom R H H) (Comodule.mem_fixedSubcomodule.mp φ.2)
      have heval := LinearMap.congr_fun hfix h
      rw [Comodule.dual_coact, Comodule.dualTensorHom_dualCoact_apply] at heval
      simpa using heval⟩
  invFun φ :=
    ⟨φ.1, by
      rw [Comodule.mem_fixedSubcomodule]
      apply (dualTensorHom_bijective (R := R) (M := H) (N := H)).1
      ext h
      rw [Comodule.dual_coact, Comodule.dualTensorHom_dualCoact_apply]
      simpa using
        (forall_antipode_matrixCoefficient_iff_isRightCointegral φ.1).mpr
          ((mem_rightCointegrals _).mp φ.2) h⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

variable (R H) in
/-- **Fundamental theorem of Hopf modules for the linear dual**: for any finite projective Hopf
algebra `H` over a commutative semiring `R`, the space of right cointegrals tensored with `H` is
canonically isomorphic to `Module.Dual R H` via `φ ⊗ x ↦ (h ↦ φ (x * h))`. -/
noncomputable def rightCointegralsTensorEquivDual :
    rightCointegrals R H ⊗[R] H ≃ₗ[R] Module.Dual R H :=
  (TensorProduct.congr (fixedEquivRightCointegrals (R := R) (H := H)).symm
      (LinearEquiv.refl R H)).trans
    (RightHopfModule.coinvariantEquiv R H (Module.Dual R H))

/-- Evaluating `rightCointegralsTensorEquivDual` on a pure tensor gives
`(φ ⊗ x)(h) = φ (x * h)`. -/
@[simp]
theorem rightCointegralsTensorEquivDual_tmul_apply (φ : rightCointegrals R H) (x h : H) :
    rightCointegralsTensorEquivDual R H (φ ⊗ₜ[R] x) h = (φ : Module.Dual R H) (x * h) := by
  simp [rightCointegralsTensorEquivDual, fixedEquivRightCointegrals]

variable (R H) in
/-- **Larson–Sweedler existence theorem**: every finite projective Hopf algebra over a nontrivial
commutative semiring admits a nonzero right cointegral. -/
theorem exists_isRightCointegral_ne_zero [Nontrivial R] :
    ∃ φ : Module.Dual R H, IsRightCointegral φ ∧ φ ≠ 0 := by
  by_contra h
  push Not at h
  have hsub (x : rightCointegrals R H) : x = 0 :=
    Subtype.ext (h x.1 ((mem_rightCointegrals _).mp x.2))
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

end FiniteProjective

end DualHopfModule

/-! ## Larson–Sweedler theorems over a field -/

section Field

variable {k : Type u} {H : Type v} [Field k] [Ring H] [HopfAlgebra k H]

/-- A nonzero right cointegral on a finite-dimensional Hopf algebra is a Frobenius functional. -/
theorem IsRightCointegral.isFrobeniusFunctional [FiniteDimensional k H]
    {φ : Module.Dual k H} (hφ : IsRightCointegral φ) (h0 : φ ≠ 0) :
    φ.IsFrobeniusFunctional :=
  (isRightCointegral_iff_isRightInvariantIntegral.mp hφ).isFrobeniusFunctional h0

/-- A nonzero left cointegral on a finite-dimensional Hopf algebra is a Frobenius functional. -/
theorem IsLeftCointegral.isFrobeniusFunctional [FiniteDimensional k H]
    {φ : Module.Dual k H} (hφ : IsLeftCointegral φ) (h0 : φ ≠ 0) :
    φ.IsFrobeniusFunctional :=
  (isLeftCointegral_iff_isLeftInvariantIntegral.mp hφ).isFrobeniusFunctional h0

variable (k H) [FiniteDimensional k H]

/-- **Larson–Sweedler**: the space of right cointegrals of a finite-dimensional Hopf algebra over
a field is one-dimensional. -/
theorem finrank_rightCointegrals : Module.finrank k (rightCointegrals k H) = 1 := by
  have : Nontrivial H := (Bialgebra.counitAlgHom k H).toRingHom.domain_nontrivial
  have : Module.Free k (rightCointegrals k H) :=
    Module.Free.of_divisionRing k (rightCointegrals k H)
  have hdim := (rightCointegralsTensorEquivDual k H).finrank_eq
  rw [Module.finrank_tensorProduct, Subspace.dual_finrank_eq] at hdim
  exact Nat.eq_of_mul_eq_mul_right Module.finrank_pos (by simpa using hdim)

/-- **Larson–Sweedler Frobenius theorem**: every finite-dimensional Hopf algebra over a field
admits a Frobenius functional. -/
theorem exists_isFrobeniusFunctional : ∃ φ : H →ₗ[k] k, φ.IsFrobeniusFunctional := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero k H
  exact ⟨φ, hφ.isFrobeniusFunctional h0⟩

/-- **Larson–Sweedler**: the space of left integrals of a finite-dimensional Hopf algebra over a
field is one-dimensional. -/
theorem finrank_leftIntegral : Module.finrank k (leftIntegral k H) = 1 := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional k H
  exact hφ.finrank_leftIntegral

/-- **Larson–Sweedler**: the space of right integrals of a finite-dimensional Hopf algebra over a
field is one-dimensional. -/
theorem finrank_rightIntegral : Module.finrank k (rightIntegral k H) = 1 := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional k H
  exact hφ.finrank_rightIntegral

/-- **Larson–Sweedler**: the space of left cointegrals of a finite-dimensional Hopf algebra over
a field is one-dimensional. -/
theorem finrank_leftCointegrals : Module.finrank k (leftCointegrals k H) = 1 :=
  (leftCointegralsEquivLeftIntegral k H).finrank_eq.trans
    (finrank_leftIntegral k (ConvolutionDual k H))

/-- Every finite-dimensional Hopf algebra over a field admits a nonzero left cointegral. -/
theorem exists_isLeftCointegral_ne_zero :
    ∃ φ : Module.Dual k H, IsLeftCointegral φ ∧ φ ≠ 0 := by
  have hpos : 0 < Module.finrank k (leftCointegrals k H) := by
    rw [finrank_leftCointegrals]
    exact Nat.one_pos
  have : Nontrivial (leftCointegrals k H) := Module.nontrivial_of_finrank_pos hpos
  obtain ⟨φ, hφ⟩ := exists_ne (0 : leftCointegrals k H)
  exact ⟨φ.1, (mem_leftCointegrals _).mp φ.2, fun h ↦ hφ (Subtype.ext h)⟩

/-- **Larson–Sweedler**: the antipode of a finite-dimensional Hopf algebra over a field is
bijective. -/
theorem antipode_bijective : Function.Bijective (HopfAlgebra.antipode k (A := H)) := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero k H
  exact (isRightCointegral_iff_isRightInvariantIntegral.mp hφ).antipode_bijective h0

include k in
/-- Every finite-dimensional Hopf algebra over a field is left self-injective. -/
theorem moduleInjective_self : Module.Injective H H := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional k H
  exact hφ.moduleInjective_self

include k in
/-- Every finite-dimensional Hopf algebra over a field is right self-injective. -/
theorem moduleInjective_op_self : Module.Injective Hᵐᵒᵖ H := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional k H
  exact hφ.moduleInjective_op_self

include k in
/-- Over a finite-dimensional Hopf algebra, a left module (not necessarily finitely generated) is
projective if and only if it is injective. -/
theorem moduleProjective_iff_moduleInjective [Small.{w} H] (M : Type w) [AddCommGroup M]
    [Module H M] : Module.Projective H M ↔ Module.Injective H M := by
  obtain ⟨_, hφ⟩ := exists_isFrobeniusFunctional k H
  exact hφ.moduleProjective_iff_moduleInjective M

end Field

/-! ## Frobenius dual-basis reconstruction formulas -/

section DualBasis

section Semiring

variable {R : Type u} {H : Type v} [CommSemiring R] [Semiring H] [HopfAlgebra R H]

/-- Reconstruction from a right cointegral and a normalized left integral:
`∑ φ (x * t₁) • S(t₂) = x`. -/
theorem IsRightCointegral.sum_apply_mul_smul_antipode {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * r.left i) • HopfAlgebra.antipode R (r.right i) = x :=
  (isRightCointegral_iff_isRightInvariantIntegral.mp hφ).sum_apply_mul_smul_antipode ht htφ r x

/-- Reconstruction from a left cointegral and a normalized right integral:
`∑ φ (t₂ * x) • S(t₁) = x`. -/
theorem IsLeftCointegral.sum_apply_mul_smul_antipode {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (r.right i * x) • HopfAlgebra.antipode R (r.left i) = x := by
  classical
  have htx (y : H) : φ (t * y) = Coalgebra.counit (R := R) y := by
    simp [(mem_rightIntegral_iff.mp ht) y, htφ]
  rw [← (isLeftCointegral_iff_isLeftInvariantIntegral.mp hφ).strong_invariance (ℛ R x) r]
  simpa only [htx] using Coalgebra.sum_smul_counit (ℛ R x)

/-- Applying strong right invariance to a normalized right integral yields the antipode:
`∑ φ (t₁ * x) • t₂ = S(x)`. -/
theorem IsRightCointegral.sum_apply_mul_smul_eq_antipode {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (r.left i * x) • r.right i = HopfAlgebra.antipode R x := by
  classical
  have htx (y : H) : φ (t * y) = Coalgebra.counit (R := R) y := by
    simp [(mem_rightIntegral_iff.mp ht) y, htφ]
  rw [(isRightCointegral_iff_isRightInvariantIntegral.mp hφ).strong_invariance r (ℛ R x)]
  simpa only [htx, ← map_smul, ← map_sum] using
    congrArg (HopfAlgebra.antipode R) (Coalgebra.sum_counit_smul (ℛ R x))

/-- Reconstruction from a right cointegral and a normalized right integral using the inverse
antipode: `∑ φ (t₁ * x) • S⁻¹(t₂) = x`. -/
theorem IsRightCointegral.sum_apply_mul_smul_inverseAntipode {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (r.left i * x) • TauCeti.HopfAlgebra.inverseAntipode hS (r.right i) = x := by
  have h := congrArg (TauCeti.HopfAlgebra.inverseAntipode hS)
    (hφ.sum_apply_mul_smul_eq_antipode ht htφ r x)
  simpa only [map_sum, map_smul, TauCeti.HopfAlgebra.inverseAntipode_antipode] using h

end Semiring

section CommRingDualBasis

variable {R : Type u} {H : Type v} [CommRing R] [Semiring H] [HopfAlgebra R H]

/-- If a bilinear form `B` on an `R`-module `M` over a commutative ring satisfies a finite
left-side reconstruction formula `∑ B (a i) y • b i = y`, then it satisfies the partner formula
`∑ B x (b i) • a i = x`. -/
private theorem dualBasis_partner {M : Type v} [AddCommMonoid M] [Module R M]
    (B : M →ₗ[R] M →ₗ[R] R) {ι : Type*} (s : Finset ι) (a b : ι → M)
    (h : ∀ y : M, ∑ i ∈ s, B (a i) y • b i = y) (x : M) :
    ∑ i ∈ s, B x (b i) • a i = x := by
  have : Module.Finite R M :=
    Module.Finite.of_surjective (Fintype.linearCombination R fun i : s ↦ b i.1)
      fun y ↦ ⟨fun i ↦ B (a i.1) y, by
        rw [Fintype.linearCombination_apply, Finset.univ_eq_attach,
          s.sum_attach fun i ↦ B (a i) y • b i]
        exact h y⟩
  let Ψ : Module.Dual R M →ₗ[R] M :=
    { toFun := fun α ↦ ∑ i ∈ s, α (a i) • b i
      map_add' := fun α β ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r α ↦ by simp [smul_smul, Finset.smul_sum] }
  let Ψ' : Module.Dual R M →ₗ[R] M :=
    { toFun := fun β ↦ ∑ i ∈ s, β (b i) • a i
      map_add' := fun α β ↦ by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun r α ↦ by simp [smul_smul, Finset.smul_sum] }
  have hΨ : Function.Surjective Ψ := fun y ↦ ⟨B.flip y, h y⟩
  have hBΨ' (β : Module.Dual R M) : B (Ψ' β) = β := by
    ext y
    calc
      B (∑ i ∈ s, β (b i) • a i) y
        = ∑ i ∈ s, β (b i) * B (a i) y := by simp [map_sum]
      _ = β (∑ i ∈ s, B (a i) y • b i) := by simp [map_sum, mul_comm]
      _ = β y := by rw [h y]
  have hB : Function.Surjective B := fun β ↦ ⟨Ψ' β, hBΨ' β⟩
  have hinj : Function.Injective (Ψ ∘ₗ B) :=
    OrzechProperty.injective_of_surjective_endomorphism (Ψ ∘ₗ B) (hΨ.comp hB)
  exact hinj (congrArg Ψ (hBΨ' (B x)))

/-- Dual-basis partner of `IsRightCointegral.sum_apply_mul_smul_antipode`: for a right cointegral
`φ` and a left integral `t` with `φ t = 1`, `∑ φ (S(t₂) * x) • t₁ = x`. -/
theorem IsRightCointegral.sum_apply_antipode_mul_smul {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ leftIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (HopfAlgebra.antipode R (r.right i) * x) • r.left i = x :=
  dualBasis_partner ((LinearMap.mul R H).flip.compr₂ φ) r.index r.left
    (fun i ↦ HopfAlgebra.antipode R (r.right i))
    (hφ.sum_apply_mul_smul_antipode ht htφ r) x

/-- Dual-basis partner of `IsLeftCointegral.sum_apply_mul_smul_antipode`: for a left cointegral
`φ` and a right integral `t` with `φ t = 1`, `∑ φ (x * S(t₁)) • t₂ = x`. -/
theorem IsLeftCointegral.sum_apply_mul_antipode_smul {φ : Module.Dual R H}
    (hφ : IsLeftCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * HopfAlgebra.antipode R (r.left i)) • r.right i = x :=
  dualBasis_partner ((LinearMap.mul R H).compr₂ φ) r.index r.right
    (fun i ↦ HopfAlgebra.antipode R (r.left i))
    (hφ.sum_apply_mul_smul_antipode ht htφ r) x

/-- Dual-basis partner of `IsRightCointegral.sum_apply_mul_smul_inverseAntipode`: for a right
cointegral `φ` and a right integral `t` with `φ t = 1`, `∑ φ (x * S⁻¹(t₂)) • t₁ = x`. -/
theorem IsRightCointegral.sum_apply_mul_inverseAntipode_smul {φ : Module.Dual R H}
    (hφ : IsRightCointegral φ) {t : H} (ht : t ∈ rightIntegral R H) (htφ : φ t = 1)
    (hS : Function.Bijective (HopfAlgebra.antipode R : H →ₗ[R] H))
    {ι : Type*} (r : Coalgebra.Repr R t ι) (x : H) :
    ∑ i ∈ r.index, φ (x * TauCeti.HopfAlgebra.inverseAntipode hS (r.right i)) • r.left i = x :=
  dualBasis_partner ((LinearMap.mul R H).compr₂ φ) r.index r.left
    (fun i ↦ TauCeti.HopfAlgebra.inverseAntipode hS (r.right i))
    (hφ.sum_apply_mul_smul_inverseAntipode ht htφ hS r) x

end CommRingDualBasis

end DualBasis

end TauCeti
