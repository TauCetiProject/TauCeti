/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import TauCeti.LinearAlgebra.ExteriorPower.Projection
import TauCeti.LinearAlgebra.ExteriorPower.WedgePairing

/-!
# Exterior powers of a product

For modules `M` and `N`, the wedge product `a ⊗ b ↦ a ∧ b` maps `⋀ᵖ M ⊗ ⋀^q N` to
`⋀ⁿ (M × N)` whenever `p + q = n`. These maps are the bigraded pieces of Mathlib's algebra
isomorphism `ExteriorAlgebra.prodEquivTensor` between `⋀ (M × N)` and the graded tensor product of
`⋀ M` and `⋀ N`.

## Main declarations

* `TauCeti.exteriorPower.wedgeTensor`: the wedge product `⋀ᵖ M ⊗ ⋀^q N → ⋀ⁿ (M × N)`.
* `TauCeti.exteriorPower.sum_coe_wedgeTensor_map_proj`: the degree-`n` component of an element
  of `⋀ (M × N)` is the sum of the wedge products of its bidegree-`(i, n - i)` components.
-/

public section

noncomputable section

open scoped TensorProduct

namespace TauCeti

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

variable (R M N) in
/-- The wedge product `⋀ᵖ M ⊗ ⋀^q N → ⋀ⁿ (M × N)`, `a ⊗ b ↦ a ∧ b`, for `p + q = n`. -/
def wedgeTensor (p q n : ℕ) (h : p + q = n) :
    ⋀[R]^p M ⊗[R] ⋀[R]^q N →ₗ[R] ⋀[R]^n (M × N) :=
  (LinearEquiv.ofEq _ _ (by rw [h])).toLinearMap ∘ₗ
    TensorProduct.lift ((_root_.exteriorPower.wedge R (M × N) p q).compl₁₂
      (_root_.exteriorPower.map p (LinearMap.inl R M N))
      (_root_.exteriorPower.map q (LinearMap.inr R M N)))

/-- `wedgeTensor` sends `a ⊗ b` to the product of the images of `a` and `b` in `⋀ (M × N)`. -/
@[simp]
theorem coe_wedgeTensor_tmul (p q n : ℕ) (h : p + q = n) (a : ⋀[R]^p M) (b : ⋀[R]^q N) :
    (wedgeTensor R M N p q n h (a ⊗ₜ b) : ExteriorAlgebra R (M × N)) =
      ExteriorAlgebra.map (LinearMap.inl R M N) a *
        ExteriorAlgebra.map (LinearMap.inr R M N) b := by
  simp [wedgeTensor]

/-- In degree `n`, the wedge products of the bidegree-`(i, n - i)` components of an element of
`⋀ M ⊗ ⋀ N` add up to the degree-`n` component of its image in `⋀ (M × N)` under
`ExteriorAlgebra.prodEquivTensor`. -/
theorem sum_coe_wedgeTensor_map_proj (n : ℕ) (y : ExteriorAlgebra R M ⊗[R] ExteriorAlgebra R N) :
    ∑ i : Fin (n + 1), (wedgeTensor R M N i (n - i) n (by omega)
        (TensorProduct.map (proj R M i) (proj R N (n - i)) y) : ExteriorAlgebra R (M × N)) =
      proj R (M × N) n
        ((ExteriorAlgebra.prodEquivTensor R M N).symm (GradedTensorProduct.of R _ _ y)) := by
  induction y using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Submodule.coe_add, Finset.sum_add_distrib, hx, hy]
  | tmul a b =>
    induction a using DirectSum.Decomposition.inductionOn (fun i ↦ ⋀[R]^i M) with
    | zero => simp
    | add a a' ha ha' =>
      simp only [TensorProduct.add_tmul, map_add, Submodule.coe_add, Finset.sum_add_distrib, ha,
        ha']
    | @homogeneous p a =>
      induction b using DirectSum.Decomposition.inductionOn (fun i ↦ ⋀[R]^i N) with
      | zero => simp
      | add b b' hb hb' =>
        simp only [TensorProduct.tmul_add, map_add, Submodule.coe_add, Finset.sum_add_distrib, hb,
          hb']
      | @homogeneous q b =>
        have hab : ExteriorAlgebra.map (LinearMap.inl R M N) (a : ExteriorAlgebra R M) *
            ExteriorAlgebra.map (LinearMap.inr R M N) (b : ExteriorAlgebra R N) ∈
              ⋀[R]^(p + q) (M × N) := by
          rw [← _root_.exteriorPower.coe_map, ← _root_.exteriorPower.coe_map]
          exact SetLike.mul_mem_graded (Submodule.coe_mem _) (Submodule.coe_mem _)
        simp only [TensorProduct.map_tmul, coe_wedgeTensor_tmul, coe_proj_of_mem a.2,
          coe_proj_of_mem b.2]
        rw [← GradedTensorProduct.tmul, ExteriorAlgebra.prodEquivTensor_symm_tmul,
          coe_proj_of_mem hab]
        by_cases hpq : p + q = n
        · rw [ite_eq_left hpq, Finset.sum_eq_single ⟨p, by omega⟩]
          · simp [show q = n - p by omega]
          · rintro i - hi
            have : p ≠ i := fun h ↦ hi (Fin.ext h.symm)
            simp [this]
          · simp
        · rw [ite_eq_right hpq]
          refine Finset.sum_eq_zero fun i _ ↦ ?_
          by_cases hi : p = i
          · have : q ≠ n - i := by omega
            simp [this]
          · simp [hi]

end exteriorPower

end TauCeti
