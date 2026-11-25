/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.Dual
public import TauCeti.Algebra.Coalgebra.Comodule.LeftRegular

/-!
# Matrix coefficients under the left regular coaction

Let `M` be a finite projective right comodule over a Hopf algebra `H`. The matrix coefficient
`c(φ, m) = (φ ⊗ id) ρ(m)` is the function `g ↦ φ(g m)`. Right translation of functions,
`(g · f)(x) = f(x g)`, acts on it through the vector `m`: this is the comultiplication formula
`TauCeti.Comodule.comul_matrixCoefficient`. Left translation by the inverse,
`(g · f)(x) = f(g⁻¹ x)`, which is the left regular coaction
`TauCeti.Comodule.leftRegularCoact`, acts through the functional `φ` by the contragredient
action, that is, by the dual coaction `TauCeti.Comodule.dualCoact`:

```text
leftRegularCoact (c(φ, m)) = ∑ c(φ₀, m) ⊗ φ₁,   where dualCoact φ = ∑ φ₀ ⊗ φ₁.
```

So the coefficient map `M* ⊗ M → H` intertwines the dual coaction on the first factor with the
left regular coaction, and the coaction on the second factor with the comultiplication. This is
the two-sided equivariance `(a, b) · f = (g ↦ f(a⁻¹ g b))` of the algebraic Peter–Weyl
decomposition, the first factor acting on `M*` and the second on `M`.

## Main declarations

* `TauCeti.Comodule.leftRegularCoact_matrixCoefficient`: the basis-free formula.
* `TauCeti.Comodule.leftRegularCoact_matrixCoefficient_eq_sum`: in a basis `(eⱼ)`,
  `leftRegularCoact (c(φ, m)) = ∑ⱼ c(eⱼ*, m) ⊗ S(c(φ, eⱼ))`.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed., I.2.7 and I.2.13.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable {R : Type u} {H : Type v} {M : Type w}
variable [CommSemiring R] [Semiring H] [HopfAlgebra R H]
variable [AddCommMonoid M] [Module R M] [Comodule R H M]

/-- Pairing the vector `m` against the functional leg of a tensor `t = ∑ ψⱼ ⊗ hⱼ` in `M* ⊗ H`
gives `∑ c(ψⱼ, m) ⊗ hⱼ`, which is the coaction of `m` with the linear map `x ↦ ∑ ψⱼ(x) hⱼ`
applied to its vector leg. -/
private theorem map_flip_matrixCoefficientBilinear (t : Module.Dual R M ⊗[R] H) (m : M) :
    TensorProduct.map ((matrixCoefficientBilinear (R := R) (C := H) (M := M)).flip m)
        LinearMap.id t =
      TensorProduct.comm R H H
        (TensorProduct.map (dualTensorHom R M H t) LinearMap.id (coact (R := R) (C := H) m)) := by
  induction t using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, TensorProduct.map_add_left, hx, hy]
  | tmul ψ h =>
    simp only [TensorProduct.map_tmul, LinearMap.flip_apply,
      matrixCoefficientBilinear_apply_apply, LinearMap.id_apply, matrixCoefficient_def]
    induction coact (R := R) (C := H) m using TensorProduct.inductionOn with
    | tmul x c => simp [dualTensorHom_apply, TensorProduct.smul_tmul]
    | add x y hx hy => simp only [map_add, TensorProduct.add_tmul, hx, hy]

variable [Module.Finite R M] [Module.Projective R M]

/-- **Left translation of matrix coefficients.** The left regular coaction of a matrix
coefficient `c(φ, m)` is obtained by applying the coefficient map `ψ ↦ c(ψ, m)` to the functional
leg of the dual coaction of `φ`: on points, `x ↦ φ(g⁻¹ x m)` is the coefficient of `m` against
the contragredient translate `g · φ = φ ∘ g⁻¹`. -/
theorem leftRegularCoact_matrixCoefficient (φ : Module.Dual R M) (m : M) :
    leftRegularCoact R H (matrixCoefficient (C := H) φ m) =
      TensorProduct.map ((matrixCoefficientBilinear (R := R) (C := H) (M := M)).flip m)
        LinearMap.id (dualCoact (H := H) φ) := by
  rw [map_flip_matrixCoefficientBilinear, dualTensorHom_dualCoact, leftRegularCoact_apply,
    comul_matrixCoefficient]
  induction coact (R := R) (C := H) m using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul x c => simp

omit [Module.Finite R M] [Module.Projective R M] in
/-- **Left translation of matrix coefficients in a basis.** For a basis `(eⱼ)` of `M`, the left
regular coaction of `c(φ, m)` is `∑ⱼ c(eⱼ*, m) ⊗ S(c(φ, eⱼ))`. -/
theorem leftRegularCoact_matrixCoefficient_eq_sum {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι R M) (φ : Module.Dual R M) (m : M) :
    leftRegularCoact R H (matrixCoefficient (C := H) φ m) =
      ∑ j, matrixCoefficient (C := H) (b.dualBasis j) m ⊗ₜ[R]
        HopfAlgebra.antipode R (matrixCoefficient (C := H) φ (b j)) := by
  have := Module.Finite.of_basis b
  have := Module.Projective.of_basis b
  simp [leftRegularCoact_matrixCoefficient, dualCoact_eq_sum b]

end TauCeti.Comodule
