/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.HopfModule
public import TauCeti.Algebra.HopfAlgebra.Cointegral.Basic
public import TauCeti.Algebra.HopfAlgebra.Frobenius

/-!
# Existence and uniqueness of cointegrals

Let `H` be a Hopf algebra which is finite projective over `R`. Its linear dual `H*` is a right
`H`-comodule, the dual `TauCeti.Comodule.dual` of the regular comodule, with coaction
characterized by `Σ φ₀(x) φ₁ = S(Σ φ(x₁) x₂)`. It is also a right `H`-module through
precomposition with left multiplication, `(φ • h)(x) = φ(h x)`. These two structures make `H*`
a right Hopf module (`TauCeti.isHopfModuleAction_dualMulLeftAct`), and its fixed vectors are
exactly the right cointegrals (`TauCeti.mem_fixedSubcomodule_dual_iff`).

Over a field the fundamental theorem of Hopf modules then gives
`dim H = dim H* = dim (right cointegrals) · dim H`, so the right cointegrals of a
finite-dimensional Hopf algebra form a line (`TauCeti.finrank_rightCointegrals`). This is the
theorem of Larson and Sweedler. Right and left cointegrals are the right and left invariant
integrals of `TauCeti.Algebra.HopfAlgebra.Integral`, so the results of
`TauCeti.Algebra.HopfAlgebra.Frobenius` apply: every nonzero cointegral is a Frobenius functional
(`TauCeti.IsRightCointegral.isFrobeniusFunctional`, `TauCeti.exists_isFrobeniusFunctional`), the
antipode is bijective (`TauCeti.HopfAlgebra.antipode_bijective_of_finiteDimensional`) and the
left and right integrals form lines (`TauCeti.finrank_leftIntegral`,
`TauCeti.finrank_rightIntegral`). The left cointegrals are the left integrals of the
finite-dimensional Hopf algebra `TauCeti.ConvolutionDual k H`, so they form a line too
(`TauCeti.finrank_leftCointegrals`).

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf algebras*,
  Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, Theorem 2.1.3.
-/

public section

open scoped TensorProduct
open TensorProduct

namespace TauCeti

open Comodule

attribute [local instance] Comodule.dual

section CommSemiring

variable {R H : Type*} [CommSemiring R] [Semiring H]

section Algebra

variable [Algebra R H]

/-- The right action of `H` on its linear dual by precomposition with left multiplication,
`φ ⊗ h ↦ (x ↦ φ (h * x))`. -/
noncomputable def dualMulLeftAct : Module.Dual R H ⊗[R] H →ₗ[R] Module.Dual R H :=
  TensorProduct.lift ((LinearMap.llcomp R H H R).compl₂ (LinearMap.mul R H))

@[simp]
theorem dualMulLeftAct_tmul_apply (φ : Module.Dual R H) (h x : H) :
    dualMulLeftAct (φ ⊗ₜ h) x = φ (h * x) := by
  simp [dualMulLeftAct]

end Algebra

section Bialgebra

variable [Bialgebra R H]

/-- Right cointegrals are exactly the right invariant integrals: both predicates state
`Σ φ(h₁) h₂ = φ(h) 1`. -/
theorem isRightCointegral_iff_isRightInvariantIntegral {φ : Module.Dual R H} :
    IsRightCointegral φ ↔ φ.IsRightInvariantIntegral := by
  rw [isRightCointegral_def, LinearMap.isRightInvariantIntegral_iff]

/-- Left cointegrals are exactly the left invariant integrals: both predicates state
`Σ φ(h₂) h₁ = φ(h) 1`. -/
theorem isLeftCointegral_iff_isLeftInvariantIntegral {φ : Module.Dual R H} :
    IsLeftCointegral φ ↔ φ.IsLeftInvariantIntegral := by
  rw [isLeftCointegral_def, LinearMap.isLeftInvariantIntegral_iff]

end Bialgebra

variable [HopfAlgebra R H]

/-- The antipode applied to the right contraction of the coproduct with `φ`,
`y ↦ S(Σ φ(y₁) y₂)`. Under `dualTensorHom` this is the coaction of `φ` in `H*`. -/
private noncomputable abbrev antipodeContract (φ : Module.Dual R H) : H →ₗ[R] H :=
  HopfAlgebra.antipode R ∘ₗ matrixCoefficientBilinear (R := R) (C := H) (M := H) φ

private theorem antipodeContract_apply (φ : Module.Dual R H) (y : H) :
    antipodeContract φ y =
      HopfAlgebra.antipode R (TensorProduct.lid R H (φ.rTensor H (Coalgebra.comul y))) := by
  simp only [antipodeContract, LinearMap.comp_apply, matrixCoefficientBilinear_apply_apply,
    matrixCoefficient_def, instSelf_coact, LinearMap.rTensor]

/-- For `t = Σ ψ ⊗ c` and `w = Σ a ⊗ b`, the tensor `Σ (ψ • a) ⊗ c b` evaluates at `x` to
`Σ (Σ ψ(a x) c) b`. -/
private theorem dualTensorHom_rTensor_dualMulLeftAct_tensorCombine
    (t : Module.Dual R H ⊗[R] H) (w : H ⊗[R] H) (x : H) :
    dualTensorHom R H H (dualMulLeftAct.rTensor H (tensorCombine (t ⊗ₜ w))) x =
      LinearMap.mul' R H ((dualTensorHom R H H t ∘ₗ LinearMap.mulRight R x).rTensor H w) := by
  induction t with
  | add t t' ht ht' => simp only [add_tmul, map_add, LinearMap.add_apply, ht, ht',
      LinearMap.add_comp, LinearMap.rTensor_add, LinearMap.add_apply]
  | tmul ψ c =>
    induction w with
    | add w w' hw hw' => simp only [tmul_add, map_add, LinearMap.add_apply, hw, hw']
    | tmul a b => simp [dualTensorHom_apply]

/-- The contraction of a product: `S(Σ φ((y x)₁) (y x)₂) = Σ g(y₁) S(y₂)`, where
`g(u) = S(Σ φ(u x₁) x₂)` is the contraction of `φ • u` at `x`. -/
private theorem antipodeContract_mul (φ : Module.Dual R H) (x y : H) :
    antipodeContract φ (y * x) =
      LinearMap.mul' R H (TensorProduct.map
        (HopfAlgebra.antipode R ∘ₗ (matrixCoefficientBilinear (R := R) (C := H) (M := H)).flip x ∘ₗ
          dualMulLeftAct ∘ₗ TensorProduct.mk R _ H φ)
        (HopfAlgebra.antipode R) (Coalgebra.comul y)) := by
  rw [antipodeContract_apply, Bialgebra.comul_mul]
  induction Coalgebra.comul (R := R) y with
  | add u v hu hv => simp only [add_mul, map_add, hu, hv]
  | tmul a b =>
    simp only [LinearMap.comp_apply, LinearMap.flip_apply, TensorProduct.mk_apply,
      matrixCoefficientBilinear_apply_apply, matrixCoefficient_def, instSelf_coact,
      TensorProduct.map_tmul, LinearMap.mul'_apply]
    induction Coalgebra.comul (R := R) x with
    | add u v hu hv => simp only [mul_add, map_add, add_mul, hu, hv]
    | tmul c d => simp [HopfAlgebra.antipode_mul_antidistrib]

/-- Evaluating at `1` after acting by `Σ φ • h₁ ⊗ h₂` gives `Σ φ(h₁) h₂`. -/
private theorem dualTensorHom_rTensor_dualMulLeftAct_mk_one (φ : Module.Dual R H)
    (w : H ⊗[R] H) :
    dualTensorHom R H H ((dualMulLeftAct ∘ₗ TensorProduct.mk R _ H φ).rTensor H w) 1 =
      TensorProduct.lid R H (φ.rTensor H w) := by
  induction w with
  | add w w' hw hw' => simp only [map_add, LinearMap.add_apply, hw, hw']
  | tmul a b => simp [dualTensorHom_apply]

variable [Module.Finite R H] [Module.Projective R H]

/-- The linear dual `H*` is a right Hopf module: the dual of the regular comodule, with `H` acting
by precomposition with left multiplication. -/
theorem isHopfModuleAction_dualMulLeftAct :
    IsHopfModuleAction (dualMulLeftAct (R := R) (H := H)) where
  act_one φ := by ext x; simp
  act_act φ a b := by ext x; simp [mul_assoc]
  coact_act φ h := by
    apply (dualTensorHom_bijective (R := R) (M := H) (N := H)).1
    ext x
    rw [tensorCoact_tmul, instSelf_coact, dualTensorHom_rTensor_dualMulLeftAct_tensorCombine,
      dual_coact, dualTensorHom_dualCoact, dualTensorHom_dualCoact]
    have hg : antipodeContract φ ∘ₗ LinearMap.mulRight R x =
        LinearMap.mul' R H ∘ₗ TensorProduct.map
          (HopfAlgebra.antipode R ∘ₗ
            (matrixCoefficientBilinear (R := R) (C := H) (M := H)).flip x ∘ₗ
              dualMulLeftAct ∘ₗ TensorProduct.mk R _ H φ)
          (HopfAlgebra.antipode R) ∘ₗ Coalgebra.comul := by
      ext y
      exact antipodeContract_mul φ x y
    rw [hg, TauCeti.HopfAlgebra.mul'_rTensor_mul'_map_antipode_comul]
    simp

/-- The fixed vectors of the Hopf module `H*` are exactly the right cointegrals. A fixed vector
`φ` satisfies `S(Σ φ(x₁) x₂) = φ(x) 1`; colinearity of the action at `x = 1` removes the
antipode. -/
theorem mem_fixedSubcomodule_dual_iff {φ : Module.Dual R H} :
    φ ∈ fixedSubcomodule R H (Module.Dual R H) ↔ IsRightCointegral φ := by
  rw [isRightCointegral_def]
  constructor
  · intro hφ h
    have hcoact := congrArg (fun t ↦ dualTensorHom R H H t 1)
      (isHopfModuleAction_dualMulLeftAct.coact_act_of_mem_fixedSubcomodule hφ h)
    simp only [dual_coact, dualTensorHom_dualCoact, antipodeContract_apply, Bialgebra.comul_one,
      Algebra.TensorProduct.one_def, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
      dualMulLeftAct_tmul_apply, mul_one, map_smul, HopfAlgebra.antipode_one,
      dualTensorHom_rTensor_dualMulLeftAct_mk_one] at hcoact
    exact hcoact.symm
  · intro hφ
    rw [mem_fixedSubcomodule]
    apply (dualTensorHom_bijective (R := R) (M := H) (N := H)).1
    ext x
    rw [dual_coact, dualTensorHom_dualCoact, antipodeContract_apply, hφ x]
    simp [dualTensorHom_apply]

/-- The fixed subcomodule of the Hopf module `H*` is the submodule of right cointegrals. -/
theorem toSubmodule_fixedSubcomodule_dual :
    (fixedSubcomodule R H (Module.Dual R H)).toSubmodule = rightCointegrals R H := by
  ext φ
  rw [Subcomodule.mem_toSubmodule, mem_rightCointegrals, mem_fixedSubcomodule_dual_iff]

end CommSemiring

section Field

variable {k H : Type*} [Field k] [Ring H] [HopfAlgebra k H] [FiniteDimensional k H]

/-- **Larson–Sweedler.** The right cointegrals of a finite-dimensional Hopf algebra over a field
form a one-dimensional space. -/
@[simp]
theorem finrank_rightCointegrals : Module.finrank k (rightCointegrals k H) = 1 := by
  have h := (isHopfModuleAction_dualMulLeftAct (R := k) (H := H)).finrank_eq
  rw [Subspace.dual_finrank_eq, ← Subcomodule.finrank_toSubmodule,
    toSubmodule_fixedSubcomodule_dual] at h
  have : Nontrivial H := Bialgebra.nontrivial k
  exact (Nat.eq_of_mul_eq_mul_right Module.finrank_pos (h.symm.trans (one_mul _).symm))

/-- A finite-dimensional Hopf algebra over a field has a nonzero right cointegral. -/
theorem exists_isRightCointegral_ne_zero :
    ∃ φ : Module.Dual k H, IsRightCointegral φ ∧ φ ≠ 0 := by
  have hne : rightCointegrals k H ≠ ⊥ := by
    intro h
    have h1 := finrank_rightCointegrals (k := k) (H := H)
    rw [h, finrank_bot] at h1
    exact zero_ne_one h1
  obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨φ, (mem_rightCointegrals φ).mp hφ, h0⟩

/-- A nonzero right cointegral of a finite-dimensional Hopf algebra over a field is a Frobenius
functional. -/
theorem IsRightCointegral.isFrobeniusFunctional {φ : Module.Dual k H}
    (hφ : IsRightCointegral φ) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  (isRightCointegral_iff_isRightInvariantIntegral.mp hφ).isFrobeniusFunctional h0

/-- A nonzero left cointegral of a finite-dimensional Hopf algebra over a field is a Frobenius
functional. -/
theorem IsLeftCointegral.isFrobeniusFunctional {φ : Module.Dual k H}
    (hφ : IsLeftCointegral φ) (h0 : φ ≠ 0) : φ.IsFrobeniusFunctional :=
  (isLeftCointegral_iff_isLeftInvariantIntegral.mp hφ).isFrobeniusFunctional h0

/-- A finite-dimensional Hopf algebra over a field is a Frobenius algebra: it has a Frobenius
functional, namely any nonzero right cointegral. -/
theorem exists_isFrobeniusFunctional : ∃ φ : Module.Dual k H, φ.IsFrobeniusFunctional := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero (k := k) (H := H)
  exact ⟨φ, hφ.isFrobeniusFunctional h0⟩

/-- **Larson–Sweedler.** The antipode of a finite-dimensional Hopf algebra over a field is
bijective. -/
theorem HopfAlgebra.antipode_bijective_of_finiteDimensional :
    Function.Bijective (HopfAlgebra.antipode k : H → H) := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero (k := k) (H := H)
  exact (isRightCointegral_iff_isRightInvariantIntegral.mp hφ).antipode_bijective h0

/-- The left integrals of a finite-dimensional Hopf algebra over a field form a one-dimensional
space. -/
@[simp]
theorem finrank_leftIntegral : Module.finrank k (leftIntegral k H) = 1 := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero (k := k) (H := H)
  exact (hφ.isFrobeniusFunctional h0).finrank_leftIntegral

/-- The right integrals of a finite-dimensional Hopf algebra over a field form a one-dimensional
space. -/
@[simp]
theorem finrank_rightIntegral : Module.finrank k (rightIntegral k H) = 1 := by
  obtain ⟨φ, hφ, h0⟩ := exists_isRightCointegral_ne_zero (k := k) (H := H)
  exact (hφ.isFrobeniusFunctional h0).finrank_rightIntegral

/-- The left cointegrals of a finite-dimensional Hopf algebra over a field form a
one-dimensional space: they are the left integrals of `ConvolutionDual k H`. -/
@[simp]
theorem finrank_leftCointegrals : Module.finrank k (leftCointegrals k H) = 1 := by
  have h : (leftIntegral k (ConvolutionDual k H)).map
      (WithConv.linearEquiv k (Module.Dual k H)).toLinearMap = leftCointegrals k H := by
    ext φ
    rw [Submodule.mem_map_equiv, mem_leftCointegrals, isLeftCointegral_iff_convMul,
      mem_leftIntegral_iff]
    simp
  rw [← h, LinearEquiv.finrank_map_eq, finrank_leftIntegral]

end Field

end TauCeti
