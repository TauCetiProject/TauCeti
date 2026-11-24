/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.BaseChange
public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic

/-!
# Graded tensor product of Clifford algebra actions over an extension of scalars

Let `R` be a commutative ring with `2` invertible, `A` a commutative `R`-algebra, `Q₁` and `Q₂`
quadratic forms on `R`-modules `M₁` and `M₂`, and `E` and `F` `A`-modules carrying `R`-algebra maps
`ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End A E` and `ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End A F`.
Given an `A`-linear grading involution `γ : Module.End A E` anticommuting with every `ρ₁ (ι Q₁ v)`,
extending `ρ₁` and `ρ₂` to `CliffordAlgebra (Qᵢ.baseChange A)` via `CliffordAlgebra.liftBaseChange`
and forming their `A`-linear graded tensor product `AlgHom.cliffordProdTensor` along
`QuadraticForm.baseChangeProd` restricts back to an `R`-algebra action of
`CliffordAlgebra (Q₁.prod Q₂)` on `E ⊗[A] F` (`AlgHom.cliffordProdBaseChange`), under which `(v, w)`
acts by `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`.

For `R = ℝ` and `A = ℂ`, this gives the complex graded tensor product of real Clifford actions on
`E ⊗[ℂ] F`.

## Main definitions

* `AlgHom.cliffordProdBaseChange`: the `R`-algebra action of `CliffordAlgebra (Q₁.prod Q₂)` on
  `E ⊗[A] F` induced by `AlgHom.cliffordProdTensor` over `A`.

## Main results

* `AlgHom.cliffordProdBaseChange_ι`: `(v, w)` acts by
  `(ρ₁ (ι Q₁ v)).rTensor F + TensorProduct.map γ (ρ₂ (ι Q₂ w))`.
* `AlgHom.cliffordProdBaseChange_map_inl`: `CliffordAlgebra Q₁` acts through the first factor.
* `AlgHom.cliffordProdBaseChange_map_inr_of_mem_evenOdd`: an element of `CliffordAlgebra Q₂` of
  parity `j` acts by `γ ^ j ⊗ ρ₂ (·)`.
* `AlgHom.map_mul_cliffordProdBaseChange_ι`: the tensor grading `γ ⊗ γ₂` anticommutes with every
  generator.
-/

public section

noncomputable section

open CliffordAlgebra
open scoped TensorProduct

namespace AlgHom

variable {R A M₁ M₂ E F : Type*} [CommRing R] [Invertible (2 : R)] [CommRing A] [Algebra R A]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [Module A E] [IsScalarTower R A E]
  [AddCommGroup F] [Module R F] [Module A F] [IsScalarTower R A F]
  (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End A E) (γ : Module.End A E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End A F)

/-- **The graded `A`-tensor product of `R`-Clifford actions**: given `R`-algebra maps
`ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End A E` (with an `A`-linear grading involution `γ`
anticommuting with `c₁(v)`) and `ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End A F`, `(v, w)` acts on
`E ⊗[A] F` by `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`. Constructed from `AlgHom.cliffordProdTensor` over `A` via
`CliffordAlgebra.liftBaseChangeEquiv` and `QuadraticForm.baseChangeProd`. -/
def cliffordProdBaseChange :
    CliffordAlgebra (Q₁.prod Q₂) →ₐ[R] Module.End A (E ⊗[A] F) :=
  (liftBaseChangeEquiv A (Q₁.prod Q₂)).symm <|
    (AlgHom.cliffordProdTensor (liftBaseChange A Q₁ ρ₁) γ hγ
        (mul_liftBaseChange_ι_eq_neg ρ₁ γ hγρ) (liftBaseChange A Q₂ ρ₂)).comp
      (equivOfIsometry (QuadraticForm.baseChangeProd Q₁ Q₂)).toAlgHom

/-- Evaluation of `AlgHom.cliffordProdBaseChange` on a generator `(v, w)`. -/
@[simp]
theorem cliffordProdBaseChange_ι (x : M₁ × M₂) :
    ρ₁.cliffordProdBaseChange γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) x) =
      (ρ₁ (ι Q₁ x.1)).rTensor F + TensorProduct.map γ (ρ₂ (ι Q₂ x.2)) := by
  simp [cliffordProdBaseChange, equivOfIsometry_apply, cliffordProdTensor_ι]

/-- **The first Clifford algebra acts through the first factor**: an element `a` of
`CliffordAlgebra Q₁`, included along `QuadraticMap.Isometry.inl`, acts by `ρ₁ a ⊗ 1`. -/
@[simp]
theorem cliffordProdBaseChange_map_inl (a : CliffordAlgebra Q₁) :
    ρ₁.cliffordProdBaseChange γ hγ hγρ ρ₂ (map (QuadraticMap.Isometry.inl Q₁ Q₂) a) =
      (ρ₁ a).rTensor F := by
  have hinl := map_map_baseChange_eq (QuadraticForm.baseChangeProd (A := A) Q₁ Q₂).toIsometry
    (QuadraticMap.Isometry.inl Q₁ Q₂)
    (QuadraticMap.Isometry.inl (Q₁.baseChange A) (Q₂.baseChange A))
    (fun v ↦ by simp) (ofBaseChangeAux A Q₁ a)
  simp [cliffordProdBaseChange, equivOfIsometry_apply, hinl]

include hγ in
/-- **Homogeneous elements of the second summand act through the grading**: an element `b` of
`CliffordAlgebra Q₂` of parity `j` acts on `E ⊗[A] F` by `γ ^ j ⊗ ρ₂ b`. -/
theorem cliffordProdBaseChange_map_inr_of_mem_evenOdd {j : ZMod 2} {b : CliffordAlgebra Q₂}
    (hb : b ∈ evenOdd Q₂ j) :
    ρ₁.cliffordProdBaseChange γ hγ hγρ ρ₂ (map (QuadraticMap.Isometry.inr Q₁ Q₂) b) =
      TensorProduct.map (γ ^ j.val) (ρ₂ b) := by
  have hinr := map_map_baseChange_eq (QuadraticForm.baseChangeProd (A := A) Q₁ Q₂).toIsometry
    (QuadraticMap.Isometry.inr Q₁ Q₂)
    (QuadraticMap.Isometry.inr (Q₁.baseChange A) (Q₂.baseChange A))
    (fun w ↦ by simp) (ofBaseChangeAux A Q₂ b)
  simp [cliffordProdBaseChange, equivOfIsometry_apply, hinr,
    cliffordProdTensor_map_inr_of_mem_evenOdd _ _ _ _ _
      (ofBaseChangeAux_mem_evenOdd (A := A) hb)]

/-- **The tensor product of graded actions is graded**: if `γ₂` is an `A`-linear grading operator
of `F` anticommuting with every `c₂(w)`, then `γ ⊗ γ₂` anticommutes with every generator of
`Q₁.prod Q₂` under `AlgHom.cliffordProdBaseChange`. -/
theorem map_mul_cliffordProdBaseChange_ι (γ₂ : Module.End A F)
    (hγ₂ρ : ∀ w, γ₂ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * γ₂)) (x : M₁ × M₂) :
    TensorProduct.map γ γ₂ * ρ₁.cliffordProdBaseChange γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) x) =
      -(ρ₁.cliffordProdBaseChange γ hγ hγρ ρ₂ (ι (Q₁.prod Q₂) x) * TensorProduct.map γ γ₂) := by
  simpa [cliffordProdTensor_ι] using map_mul_cliffordProdTensor_ι
    (liftBaseChange A Q₁ ρ₁) γ hγ (mul_liftBaseChange_ι_eq_neg ρ₁ γ hγρ)
    (liftBaseChange A Q₂ ρ₂) γ₂ (mul_liftBaseChange_ι_eq_neg ρ₂ γ₂ hγ₂ρ) (1 ⊗ₜ x.1, 1 ⊗ₜ x.2)

end AlgHom
