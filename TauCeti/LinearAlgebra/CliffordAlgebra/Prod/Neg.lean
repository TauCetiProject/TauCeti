/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Prod.Basic

/-!
# Negating the grading in the graded tensor product of Clifford modules

The graded tensor product `AlgHom.cliffordProdTensor` of `E` and `F` depends on the grading `γ`
of `E`: a vector `(v, w)` acts by `c₁(v) ⊗ 1 + γ ⊗ c₂(w)`. Replacing `γ` by `-γ` changes the sign
of the second summand. If `δ` is an operator on `F` anticommuting with every `c₂(w)`, for instance
a grading of `F`, then `1 ⊗ δ` commutes with `c₁(v) ⊗ 1` and carries `γ ⊗ c₂(w)` to
`-γ ⊗ c₂(w)`, so it intertwines the two graded tensor products
(`AlgHom.lTensor_mul_cliffordProdTensor_of_eq_neg`). When `δ` is an involution this is a
conjugation (`AlgHom.cliffordProdTensor_of_eq_neg`).

For spinor modules graded by their chirality, reversing the orientation of the first space negates
its chirality, so this is the orientation-reversal law of the graded product; see
`TauCeti/LinearAlgebra/CliffordAlgebra/VolumeElement/Prod.lean`. No finiteness or invertibility of
two is needed.

## Main results

* `AlgHom.lTensor_mul_cliffordProdTensor_of_eq_neg`: `1 ⊗ δ` intertwines the graded tensor
  products for `γ` and `-γ`.
* `AlgHom.cliffordProdTensor_of_eq_neg`: for an involution `δ`, the graded tensor product for
  `-γ` is the conjugate of that for `γ` by `1 ⊗ δ`.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §1 and §5.
* M. F. Atiyah, R. Bott and A. Shapiro, *Clifford modules*, Topology 3 (1964), §1.
-/

public section

open TensorProduct CliffordAlgebra

namespace AlgHom

variable {R M₁ M₂ E F : Type*} [CommRing R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
  (ρ₁ : CliffordAlgebra Q₁ →ₐ[R] Module.End R E) (γ : Module.End R E)
  (hγ : γ * γ = 1) (hγρ : ∀ v, γ * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ))
  (γ' : Module.End R E) (hγ' : γ' * γ' = 1) (hγ'ρ : ∀ v, γ' * ρ₁ (ι Q₁ v) = -(ρ₁ (ι Q₁ v) * γ'))
  (ρ₂ : CliffordAlgebra Q₂ →ₐ[R] Module.End R F) {δ : Module.End R F}
  (hδρ : ∀ w, δ * ρ₂ (ι Q₂ w) = -(ρ₂ (ι Q₂ w) * δ))

include hδρ in
/-- **Negating the grading of the first factor.** If `γ' = -γ` and `δ` anticommutes with every
vector acting on `F`, then `1 ⊗ δ` intertwines the graded tensor product for the grading `γ` with
that for `γ'`: on a vector, it carries `c₁(v) ⊗ 1 + γ ⊗ c₂(w)` to `c₁(v) ⊗ 1 - γ ⊗ c₂(w)`. -/
theorem lTensor_mul_cliffordProdTensor_of_eq_neg (h : γ' = -γ)
    (a : CliffordAlgebra (Q₁.prod Q₂)) :
    δ.lTensor E * cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a =
      cliffordProdTensor ρ₁ γ' hγ' hγ'ρ ρ₂ a * δ.lTensor E := by
  subst h
  induction a using CliffordAlgebra.induction with
  | algebraMap r => simp [Algebra.algebraMap_eq_smul_one]
  | ι x =>
    refine TensorProduct.ext' fun e f ↦ ?_
    have hf := LinearMap.congr_fun (hδρ x.2) f
    simp only [mul_apply_eq_comp, LinearMap.neg_apply] at hf
    simp [cliffordProdTensor_ι_tmul, hf, TensorProduct.tmul_neg, TensorProduct.neg_tmul]
  | add a b ha hb => rw [map_add, map_add, mul_add, add_mul, ha, hb]
  | mul a b ha hb => rw [map_mul, map_mul, ← mul_assoc, ha, mul_assoc, hb, mul_assoc]

include hδρ in
/-- **Negating the grading of the first factor is a conjugation.** If `γ' = -γ` and `δ` is an
involution anticommuting with every vector acting on `F`, then the graded tensor product for the
grading `γ'` is the conjugate of that for `γ` by `1 ⊗ δ`. -/
theorem cliffordProdTensor_of_eq_neg (hδ : δ * δ = 1) (h : γ' = -γ)
    (a : CliffordAlgebra (Q₁.prod Q₂)) :
    cliffordProdTensor ρ₁ γ' hγ' hγ'ρ ρ₂ a =
      δ.lTensor E * cliffordProdTensor ρ₁ γ hγ hγρ ρ₂ a * δ.lTensor E := by
  have hδE : δ.lTensor E * δ.lTensor E = 1 := by
    rw [← LinearMap.lTensor_mul, hδ]
    exact LinearMap.lTensor_id E F
  rw [lTensor_mul_cliffordProdTensor_of_eq_neg ρ₁ γ hγ hγρ γ' hγ' hγ'ρ ρ₂ hδρ h, mul_assoc, hδE,
    mul_one]

end AlgHom
