/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.HopfAlgebra.HopfModule
public import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.MatrixCoefficient.Regular
public import TauCeti.Algebra.HopfAlgebra.Cointegral.Basic

/-!
# Existence of cointegrals

Every finite projective Hopf algebra `H` over a nontrivial commutative semiring has a nonzero
right cointegral. The linear dual `H*` is a right Hopf module: its coaction is the dual
`TauCeti.Comodule.dual` of the regular comodule, characterized by `Σ φ₀(x) φ₁ = Σ φ(x₁) S(x₂)`,
and `H` acts by `(φ ↼ h)(x) = φ(h x)`. The vectors fixed by this coaction are exactly the right
cointegrals, and the coinvariant projection of `TauCeti.Algebra.HopfAlgebra.HopfModule` shows
that a nonzero Hopf module has nonzero fixed vectors.

Over a field, `TauCeti.Algebra.HopfAlgebra.Frobenius` uses this to show that a
finite-dimensional Hopf algebra is a Frobenius algebra with bijective antipode and
one-dimensional integral and cointegral spaces.

## Main declarations

* `TauCeti.mem_fixedSubcomodule_dual_iff_isRightCointegral`: the fixed vectors of the dual of
  the regular comodule are the right cointegrals.
* `TauCeti.exists_isRightCointegral_ne_zero`: existence of a nonzero right cointegral.

## References

* R. G. Larson and M. E. Sweedler, *An associative orthogonal bilinear form for Hopf
  algebras*, Amer. J. Math. 91 (1969), 75–94.
* S. Montgomery, *Hopf Algebras and Their Actions on Rings*, §2.1.
-/

public section

open TensorProduct Coalgebra HopfAlgebra
open scoped Coalgebra

namespace TauCeti

variable {R H : Type*} [CommSemiring R] [Semiring H] [_root_.HopfAlgebra R H]

noncomputable section

variable (R H) in
/-- The right action `(φ ↼ h)(x) = φ(h x)` of `H` on its dual. -/
private def dualAct : Module.Dual R H →ₗ[R] H →ₗ[R] Module.Dual R H :=
  (LinearMap.llcomp R H H R).compl₂ (LinearMap.mul R H)

private theorem dualAct_apply (φ : Module.Dual R H) (h x : H) :
    dualAct R H φ h x = φ (h * x) := rfl

/-- Under `dualTensorHom`, the Hopf-module right side `Σ t₀ ↼ h₁ ⊗ t₁ h₂` evaluates at `x` to
`Σ t(h₁ x) h₂`. -/
private theorem dualTensorHom_map_dualAct (t : Module.Dual R H ⊗[R] H) (h x : H) :
    dualTensorHom R H H (TensorProduct.map (TensorProduct.lift (dualAct R H))
      (LinearMap.mul' R H) (TensorProduct.tensorTensorTensorComm R _ H H H
        (t ⊗ₜ comul h))) x =
      LinearMap.mul' R H
        ((dualTensorHom R H H t ∘ₗ LinearMap.mulRight R x).rTensor H (comul h)) := by
  induction t using TensorProduct.inductionOn with
  | add s t hs ht => simp only [TensorProduct.add_tmul, map_add, LinearMap.add_apply, hs, ht,
      LinearMap.add_comp, LinearMap.rTensor_add]
  | tmul φ c =>
    induction comul (R := R) h using TensorProduct.inductionOn with
    | add y z hy hz => simp only [TensorProduct.tmul_add, map_add, LinearMap.add_apply, hy, hz]
    | tmul a b => simp [dualTensorHom_apply, dualAct_apply]

/-- For the regular comodule, `Σ S(c(ψ, h₁)) h₂ = ψ(h) 1`, where `c(ψ, y) = Σ ψ(y₁) y₂`. -/
private theorem mul'_rTensor_antipode_matrixCoefficient (ψ : Module.Dual R H) (h : H) :
    LinearMap.mul' R H ((antipode R ∘ₗ
      Comodule.matrixCoefficientLinear (C := H) (M := H) ψ).rTensor H (comul h)) = ψ h • 1 := by
  let r := ℛ R h
  -- `T (a ⊗ (b ⊗ d)) = ψ(a) S(b) d`; coassociativity moves the double coproduct from the left
  -- leg of `Δ h` to its right leg, where the antipode axiom applies.
  let T : H ⊗[R] (H ⊗[R] H) →ₗ[R] H :=
    (TensorProduct.lid R H).toLinearMap ∘ₗ
      TensorProduct.map ψ (LinearMap.mul' R H ∘ₗ (antipode R).rTensor H)
  have h1 : LinearMap.mul' R H ((antipode R ∘ₗ
      Comodule.matrixCoefficientLinear (C := H) (M := H) ψ).rTensor H (comul h)) =
      ∑ i ∈ r.index, ∑ j ∈ (ℛ R (r.left i)).index,
        T ((ℛ R (r.left i)).left j ⊗ₜ ((ℛ R (r.left i)).right j ⊗ₜ r.right i)) := by
    rw [← r.eq]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [T, Comodule.matrixCoefficient_def, Comodule.instSelf_coact, ← (ℛ R (r.left i)).eq,
      TensorProduct.sum_tmul, map_sum]
  have h2 := congrArg T
    (Coalgebra.sum_tmul_tmul_eq r (fun i => ℛ R (r.left i)) (fun i => ℛ R (r.right i)))
  simp only [map_sum] at h2
  rw [h1, h2]
  simp only [T, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    TensorProduct.map_tmul, LinearMap.rTensor_tmul, LinearMap.mul'_apply, TensorProduct.lid_tmul]
  have h3 := congrArg (TensorProduct.lid R R)
    (Coalgebra.sum_map_tmul_counit_eq (R := R) ψ h (repr := r))
  rw [map_sum] at h3
  simp only [TensorProduct.lid_tmul, smul_eq_mul, mul_one] at h3
  simp_rw [← Finset.smul_sum, HopfAlgebra.sum_antipode_mul_eq_smul, smul_smul,
    ← Finset.sum_smul, h3]

/-- The identity `Σ S(c(φ, h₁ x)) h₂ = S(c(φ ↼ h, x))` behind the Hopf-module compatibility of
the dual. -/
private theorem mul'_rTensor_antipode_matrixCoefficient_mulRight (φ : Module.Dual R H) (h x : H) :
    LinearMap.mul' R H ((antipode R ∘ₗ Comodule.matrixCoefficientLinear (C := H) (M := H) φ ∘ₗ
        LinearMap.mulRight R x).rTensor H (comul h)) =
      antipode R (Comodule.matrixCoefficient (C := H) (dualAct R H φ h) x) := by
  let rx := ℛ R x
  have key (z : H ⊗[R] H) : LinearMap.mul' R H ((antipode R ∘ₗ
      Comodule.matrixCoefficientLinear (C := H) (M := H) φ ∘ₗ LinearMap.mulRight R x).rTensor H z) =
      ∑ l ∈ rx.index, antipode R (rx.right l) * LinearMap.mul' R H ((antipode R ∘ₗ
        Comodule.matrixCoefficientLinear (C := H) (M := H)
          (φ ∘ₗ LinearMap.mulRight R (rx.left l))).rTensor H z) := by
    induction z using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb, mul_add, Finset.sum_add_distrib]
    | tmul a b =>
      simp [Comodule.matrixCoefficient_mul φ a x rx, HopfAlgebra.antipode_mul_antidistrib,
        Finset.sum_mul, mul_assoc]
  rw [key]
  simp only [mul'_rTensor_antipode_matrixCoefficient]
  rw [Comodule.matrixCoefficient_def, Comodule.instSelf_coact, ← rx.eq]
  simp [dualAct_apply]

section FiniteProjective

variable [Module.Finite R H] [Module.Projective R H]

attribute [local instance] Comodule.dual

/-- The dual of the regular comodule is a right Hopf module for `↼`. -/
private theorem coact_dualAct (φ : Module.Dual R H) (h : H) :
    Comodule.coact (R := R) (C := H) (dualAct R H φ h) =
      TensorProduct.map (TensorProduct.lift (dualAct R H)) (LinearMap.mul' R H)
        (TensorProduct.tensorTensorTensorComm R _ H H H (Comodule.coact φ ⊗ₜ comul h)) := by
  apply (dualTensorHom_bijective (R := R) (M := H) (N := H)).1
  ext x
  rw [dualTensorHom_map_dualAct, Comodule.dual_coact, Comodule.dualTensorHom_dualCoact,
    Comodule.dualTensorHom_dualCoact, Comodule.matrixCoefficientBilinear_apply,
    Comodule.matrixCoefficientBilinear_apply, LinearMap.comp_assoc]
  exact (mul'_rTensor_antipode_matrixCoefficient_mulRight φ h x).symm

/-- A functional on `H` is coinvariant for the dual of the regular comodule exactly when it
is a right cointegral. -/
theorem mem_fixedSubcomodule_dual_iff_isRightCointegral (φ : Module.Dual R H) :
    φ ∈ Comodule.fixedSubcomodule R H (Module.Dual R H) ↔ IsRightCointegral φ := by
  have hdual : φ ∈ Comodule.fixedSubcomodule R H (Module.Dual R H) ↔
      ∀ x, antipode R (Comodule.matrixCoefficient (C := H) φ x) = φ x • 1 := by
    rw [Comodule.mem_fixedSubcomodule, Comodule.dual_coact,
      ← (dualTensorHom_bijective (R := R) (M := H) (N := H)).1.eq_iff, LinearMap.ext_iff]
    simp
  have hmc (x : H) : Comodule.matrixCoefficient (C := H) φ x =
      TensorProduct.lid R H (φ.rTensor H (comul x)) := by
    rw [Comodule.matrixCoefficient_def, Comodule.instSelf_coact, LinearMap.rTensor_def]
  rw [hdual, isRightCointegral_def]
  constructor
  · intro hφ x
    have hS : antipode R ∘ₗ Comodule.matrixCoefficientLinear (C := H) (M := H) φ =
        Algebra.linearMap R H ∘ₗ φ := LinearMap.ext fun y => by
      simp [hφ y, Algebra.algebraMap_eq_smul_one]
    rw [← mul'_rTensor_antipode_matrixCoefficient φ x, hS]
    induction comul (R := R) x using TensorProduct.inductionOn with
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul a b => simp [Algebra.smul_def]
  · intro hφ x
    rw [hmc, hφ x]
    simp

variable (R H) in
/-- A finite projective Hopf algebra over a nontrivial commutative semiring has a nonzero
right cointegral. -/
theorem exists_isRightCointegral_ne_zero [Nontrivial R] :
    ∃ φ : Module.Dual R H, IsRightCointegral φ ∧ φ ≠ 0 := by
  have : Nontrivial (Module.Dual R H) :=
    ⟨⟨counit, 0, fun h => one_ne_zero (α := R) (by simpa using congr($h 1))⟩⟩
  obtain ⟨φ, hφ, h0⟩ := Subcomodule.ne_bot_iff.mp
    (Comodule.fixedSubcomodule_ne_bot_of_hopfModule (dualAct R H)
      (fun φ => LinearMap.ext fun x => by simp [dualAct_apply])
      (fun φ a b => LinearMap.ext fun x => by simp [dualAct_apply, mul_assoc])
      coact_dualAct)
  exact ⟨φ, (mem_fixedSubcomodule_dual_iff_isRightCointegral φ).mp hφ, h0⟩

end FiniteProjective

end

end TauCeti
