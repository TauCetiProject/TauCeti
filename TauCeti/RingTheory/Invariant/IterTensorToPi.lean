/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PiTensorProduct
public import TauCeti.RingTheory.Invariant.Free
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.TensorProduct.Pi
import TauCeti.LinearAlgebra.PiTensorProduct.Option

/-!
# The iterated Galois map of a group action

Let a monoid `G` act on a commutative `R`-algebra `A` by `R`-algebra endomorphisms. The Galois map
`TauCeti.MulSemiringAction.tensorToPi R A G : A ⊗[R] A → (G → A)` sends `a ⊗ b` to
`g ↦ a * g • b`. This file constructs its iterate on the `(k + 1)`-fold tensor power,

  `A^{⊗(k+1)} → (G^k → A)`,  `a₀ ⊗ a₁ ⊗ ⋯ ⊗ aₖ ↦ ((gᵢ)ᵢ ↦ a₀ * g₀ • a₁ * ⋯ * gₖ₋₁ • aₖ)`,

and proves that it is bijective whenever `tensorToPi` is and `G` is finite. When `A` is a finite
étale `G`-torsor over `R`, so that `Spec A → Spec R` is a torsor under the constant group `G`, this
identifies the `(k + 1)`-fold fibre power of the cover with `G^k` copies of `Spec A`: the copy
indexed by `(g₀, …, gₖ₋₁)` consists of the points `(x, g₀⁻¹ • x, …, gₖ₋₁⁻¹ • x)`. The cases
`k = 0, 1, 2` are the cover, its fibre square and its fibre cube, which carry descent data along
the cover. The tensor power is Mathlib's `PiTensorProduct` indexed by `Fin (k + 1)`, and the
group coordinates are indexed by `Fin k`; every group coordinate is measured from the zeroth
tensor factor, so the map is in vertex rather than edge coordinates.

## Main definitions

* `TauCeti.MulSemiringAction.iterTensorToPi R A G k`: the `R`-algebra map
  `(⨂[R] _ : Fin (k + 1), A) →ₐ[R] ((Fin k → G) → A)`.

## Main results

* `TauCeti.MulSemiringAction.iterTensorToPi_tprod`: the value on pure tensors,
  `a₀ * ∏ i, gᵢ • aᵢ₊₁`.
* `TauCeti.MulSemiringAction.iterTensorToPi_bijective`: for a finite group `G`, if `tensorToPi` is
  bijective then so is every `iterTensorToPi`.

## References

* S. U. Chase, D. K. Harrison and A. Rosenberg, *Galois theory and Galois cohomology of
  commutative rings*, Mem. Amer. Math. Soc. **52** (1965), 15–33, §1.
-/

public section

open TensorProduct PiTensorProduct

namespace TauCeti.MulSemiringAction

variable (R A G : Type*) [CommSemiring R] [CommSemiring A] [Algebra R A] [Monoid G]
  [MulSemiringAction G A] [SMulCommClass G R A]

/-- The iterated Galois map `A^{⊗(k+1)} → (G^k → A)`, sending `a₀ ⊗ a₁ ⊗ ⋯ ⊗ aₖ` to
`(gᵢ)ᵢ ↦ a₀ * ∏ i, gᵢ • aᵢ₊₁`. The `j`-th tensor factor is moved by the `j`-th vertex
`Fin.cons 1 g j`, so every group coordinate is measured from the zeroth factor. For `k = 1` its
value `a₀ * g • a₁` on `a₀ ⊗ a₁` at `g` is that of `tensorToPi R A G`. -/
noncomputable def iterTensorToPi (k : ℕ) : (⨂[R] _ : Fin (k + 1), A) →ₐ[R] ((Fin k → G) → A) :=
  liftAlgHom
    (MultilinearMap.pi fun g : Fin k → G ↦
      (MultilinearMap.mkPiAlgebra R (Fin (k + 1)) A).compLinearMap fun j ↦
        (MulSemiringAction.toAlgHom R A (Fin.cons (α := fun _ ↦ G) 1 g j)).toLinearMap)
    (by ext; simp)
    (fun _ _ ↦ by ext; simp [Finset.prod_mul_distrib])

variable {R A G}

/-- The iterated Galois map on a pure tensor `a₀ ⊗ a₁ ⊗ ⋯ ⊗ aₖ`. -/
@[simp]
theorem iterTensorToPi_tprod {k : ℕ} (a : Fin (k + 1) → A) (g : Fin k → G) :
    iterTensorToPi R A G k (tprod R a) g = a 0 * ∏ i, g i • a i.succ := by
  simp [iterTensorToPi, Fin.prod_univ_succ]

/-- If the Galois map `tensorToPi R A G` of a finite group is bijective, so is every iterated Galois
map `A^{⊗(k+1)} → (G^k → A)`. -/
theorem iterTensorToPi_bijective [Finite G] (h : Function.Bijective (tensorToPi R A G)) (k : ℕ) :
    Function.Bijective (iterTensorToPi R A G k) := by
  classical
  have := Fintype.ofFinite G
  -- In each case `iterTensorToPi` is the underlying map of a composite of linear equivalences.
  induction k with
  | zero =>
    -- Instance search does not see that `Fin (0 + 1)` is `Fin 1`.
    have : Subsingleton (Fin (0 + 1)) := inferInstanceAs (Subsingleton (Fin 1))
    let F : (⨂[R] _ : Fin (0 + 1), A) ≃ₗ[R] ((Fin 0 → G) → A) :=
      subsingletonEquiv 0 ≪≫ₗ (LinearEquiv.funUnique (Fin 0 → G) R A).symm
    have hF : (iterTensorToPi R A G 0).toLinearMap = F.toLinearMap := by
      ext a g
      simp [F]
    exact (congrArg DFunLike.coe hF) ▸ F.bijective
  | succ k ih =>
    -- Split off the last tensor factor and the last group coordinate: the map is
    -- `iterTensorToPi R A G k ⊗ id`, followed by `(G^k → A) ⊗[R] A ≃ (G^k → A ⊗[R] A)` and
    -- `tensorToPi R A G` in each coordinate.
    -- `e` splits off the last tensor factor.
    let e : (⨂[R] _ : Fin (k + 1 + 1), A) ≃ₗ[R] (⨂[R] _ : Fin (k + 1), A) ⊗[R] A :=
      reindex R (fun _ ↦ A) finSuccEquivLast ≪≫ₗ optionEquiv (fun _ ↦ A)
    let γ : A ⊗[R] A ≃ₗ[R] (G → A) := (AlgEquiv.ofBijective _ h).toLinearEquiv.restrictScalars R
    let s : (Fin (k + 1) → G) ≃ (Fin k → G) × G :=
      (Fin.snocEquiv fun _ ↦ G).symm.trans (Equiv.prodComm _ _)
    let F : (⨂[R] _ : Fin (k + 1 + 1), A) ≃ₗ[R] ((Fin (k + 1) → G) → A) :=
      e ≪≫ₗ TensorProduct.congr (AlgEquiv.ofBijective _ ih).toLinearEquiv (LinearEquiv.refl R A) ≪≫ₗ
        TensorProduct.piLeft R A (fun _ : Fin k → G ↦ A) ≪≫ₗ
        LinearEquiv.piCongrRight (fun _ ↦ γ) ≪≫ₗ
        (LinearEquiv.curry R A (Fin k → G) G).symm ≪≫ₗ LinearEquiv.funCongrLeft R A s
    have hF : (iterTensorToPi R A G (k + 1)).toLinearMap = F.toLinearMap := by
      refine PiTensorProduct.ext <| MultilinearMap.ext fun (a : Fin (k + 1 + 1) → A) ↦ ?_
      ext g
      simp [F, e, γ, s, Fin.init, Fin.prod_univ_castSucc, finSuccEquivLast_symm_some, mul_assoc]
    exact (congrArg DFunLike.coe hF) ▸ F.bijective

end TauCeti.MulSemiringAction
