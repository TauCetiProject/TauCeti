/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import TauCeti.LinearAlgebra.ExteriorPower.BaseChange
public import TauCeti.LinearAlgebra.ExteriorPower.Prod.Basic

/-!
# Scalar extension of the exterior sum comparison

For a commutative `R`-algebra `A`, scalar extension identifies `A ⊗[R] (M × N)` with
`(A ⊗[R] M) × (A ⊗[R] N)` (`TensorProduct.prodRight`) and `A ⊗[R] ⋀ⁿ M` with
`⋀ⁿ_A (A ⊗[R] M)` (`TauCeti.exteriorPower.equivBaseChange`). This file shows that the ordered
wedge products `⋀ᵖ M ⊗ ⋀^q N → ⋀ⁿ (M × N)` and the degree-`n` exterior sum comparison
`⋀ⁿ (M × N) ≃ ⨁ᵢ ⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N` commute with these identifications, over arbitrary commutative
rings and without any finiteness, flatness or projectivity hypothesis. Thus the module form of
the sum formula `λⁿ(x + y) = ∑ᵢ λⁱ(x) λⁿ⁻ⁱ(y)` is compatible with arbitrary base change.

## Main declarations

* `TauCeti.exteriorPower.wedgeTensor_equivBaseChange_symm_tmul_tmul`: the scalar extension of
  `a ∧ b` is the wedge product of the scalar extensions of `a` and `b`.
* `TauCeti.exteriorPower.prodEquivTensor_map_prodRight_equivBaseChange_symm`: the exterior sum
  comparison over `A` agrees with the scalar extension of the exterior sum comparison over `R`.

## References

* C. A. Weibel, *The K-book: an introduction to algebraic K-theory*, Graduate Studies in
  Mathematics 145, American Mathematical Society, 2013, Chapter I, §3 and Chapter II, §4.
-/

public section

noncomputable section

open scoped DirectSum TensorProduct

namespace TauCeti

namespace exteriorPower

open TensorProduct.AlgebraTensorModule (distribBaseChange distribBaseChange_tmul)

variable {R : Type*} (A : Type*) {M N : Type*}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-- The ordered wedge product commutes with scalar extension: for `a ∈ ⋀ᵖ M`, `b ∈ ⋀^q N` and
scalars `c, d ∈ A`, the wedge product over `A` of `c ⊗ a` and `d ⊗ b` is the scalar extension
`(c d) ⊗ (a ∧ b)`, transported along `A ⊗[R] (M × N) ≃ (A ⊗[R] M) × (A ⊗[R] N)`. -/
theorem wedgeTensor_equivBaseChange_symm_tmul_tmul (p q n : ℕ) (h : p + q = n) (c d : A)
    (a : ⋀[R]^p M) (b : ⋀[R]^q N) :
    wedgeTensor A (A ⊗[R] M) (A ⊗[R] N) p q n h
        ((equivBaseChange A p).symm (c ⊗ₜ a) ⊗ₜ (equivBaseChange A q).symm (d ⊗ₜ b)) =
      _root_.exteriorPower.map n (TensorProduct.prodRight R A A M N).toLinearMap
        ((equivBaseChange A n).symm ((c * d) ⊗ₜ wedgeTensor R M N p q n h (a ⊗ₜ b))) := by
  have hinl : (TensorProduct.prodRight R A A M N).toLinearMap ∘ₗ
      (LinearMap.inl R M N).baseChange A = LinearMap.inl A (A ⊗[R] M) (A ⊗[R] N) :=
    TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ by simp
  have hinr : (TensorProduct.prodRight R A A M N).toLinearMap ∘ₗ
      (LinearMap.inr R M N).baseChange A = LinearMap.inr A (A ⊗[R] M) (A ⊗[R] N) :=
    TensorProduct.AlgebraTensorModule.ext fun _ _ ↦ by simp
  apply Subtype.ext
  simp only [coe_wedgeTensor_tmul, coe_equivBaseChange_symm_tmul, _root_.exteriorPower.coe_map,
    ← Algebra.TensorProduct.tmul_mul_tmul, map_mul, ← hinl, ← hinr, ← ExteriorAlgebra.map_comp_map,
    AlgHom.comp_apply, ExteriorAlgebra.map_baseChange_baseChangeEquiv,
    Algebra.TensorProduct.map_tmul, AlgHom.id_apply]

/-- **The exterior sum comparison commutes with scalar extension.** For a commutative
`R`-algebra `A`, the comparison `⋀ⁿ_A ((A ⊗[R] M) × (A ⊗[R] N)) ≃ ⨁ᵢ ⋀ⁱ_A (A ⊗[R] M) ⊗[A]
⋀ⁿ⁻ⁱ_A (A ⊗[R] N)` agrees with the scalar extension of `prodEquivTensor R M N n`, when its source
is identified with `A ⊗[R] ⋀ⁿ (M × N)` and its target with `A ⊗[R] ⨁ᵢ ⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N` by
`equivBaseChange`, `TensorProduct.prodRight`, `TensorProduct.directSumRight` and
`TensorProduct.AlgebraTensorModule.distribBaseChange`. -/
theorem prodEquivTensor_map_prodRight_equivBaseChange_symm (n : ℕ)
    (x : A ⊗[R] ⋀[R]^n (M × N)) :
    prodEquivTensor A (A ⊗[R] M) (A ⊗[R] N) n
        (_root_.exteriorPower.map n (TensorProduct.prodRight R A A M N).toLinearMap
          ((equivBaseChange A n).symm x)) =
      DirectSum.lmap (fun i : Fin (n + 1) ↦
          TensorProduct.map (equivBaseChange A i).symm.toLinearMap
              (equivBaseChange A (n - i)).symm.toLinearMap ∘ₗ
            (distribBaseChange R A (⋀[R]^(i : ℕ) M) (⋀[R]^(n - i) N)).toLinearMap)
        (TensorProduct.directSumRight R A A
          (fun i : Fin (n + 1) ↦ ⋀[R]^(i : ℕ) M ⊗[R] ⋀[R]^(n - i) N)
          ((prodEquivTensor R M N n).toLinearMap.baseChange A x)) := by
  -- Both sides are additive in `x`; reduce to `c ⊗ y` with `y` the wedge product of a summand
  -- `⋀ⁱ M ⊗ ⋀ⁿ⁻ⁱ N`, where both sides are computed by `wedgeTensor_equivBaseChange_symm_tmul_tmul`.
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul c y =>
    rw [← (prodEquivTensor R M N n).symm_apply_apply y]
    induction prodEquivTensor R M N n y using DirectSum.induction_on with
    | zero => simp
    | add z z' hz hz' => simp only [map_add, TensorProduct.tmul_add, hz, hz']
    | of i t =>
      induction t using TensorProduct.inductionOn with
      | add t t' ht ht' => simp only [map_add, TensorProduct.tmul_add, ht, ht']
      | tmul a b =>
        have h := wedgeTensor_equivBaseChange_symm_tmul_tmul A i (n - i) n (by omega) c 1 a b
        rw [mul_one] at h
        simp only [← DirectSum.lof_eq_of R, LinearMap.baseChange_tmul, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply, TensorProduct.directSumRight_tmul_lof, DirectSum.lmap_lof,
          LinearMap.comp_apply, distribBaseChange_tmul, TensorProduct.map_tmul]
        -- The one real step: by `h`, the wedge product over `A` of the scalar extensions of `a`
        -- and `b` is the scalar extension of `a ∧ b`.
        rw [prodEquivTensor_symm_lof, ← h, ← prodEquivTensor_symm_lof, LinearEquiv.apply_symm_apply]

end exteriorPower

end TauCeti
