/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.HeisenbergModel.Basic
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Algebra.Star.SelfAdjoint
import TauCeti.LinearAlgebra.Matrix.DotProduct

/-!
# The Heisenberg datum of a skew-hermitian form

Let `A` be a topological ring with a continuous star operation, `ψ` a continuous additive
character of `A` with values in the unit circle that is trivial on the skew-adjoint elements
(`star a = -a`), and `S` a skew-hermitian matrix over `A` (`Sᴴ = -S`). Then

`β (x, y) = ψ (y* S x)`, with `y* S x = star y ⬝ᵥ S *ᵥ x`,

is a Heisenberg datum on `ι → A`: it is additive in `x` and, as `star` is additive, in `y`; it has
values of modulus one; and `β (x, x) = 1` since `x* S x` is skew-adjoint.

Over the adeles of a CM field `E` with the standard character `ψ`, this gives the adelic
Heisenberg datum `ψ (½ j · y* ε x)` of a purely imaginary `j ∈ E` and a hermitian matrix `ε`, from
which the reproducing model of the adelic Weil representation is built.

## Main definitions

* `TauCeti.HeisenbergDatum.ofSkewHermitian ψ hψ hψ₁ S hS`: the Heisenberg datum
  `(x, y) ↦ ψ (y* S x)` on `ι → A`.

## References

* A. Weil, *Sur certains groupes d'opérateurs unitaires*, Acta Math. 111 (1964), 143–211.
-/

public section

open Matrix

namespace TauCeti

namespace HeisenbergDatum

variable {ι A : Type*} [Fintype ι] [Ring A] [StarRing A] [TopologicalSpace A]
  [IsTopologicalSemiring A] [ContinuousStar A]

/-- The Heisenberg datum `β (x, y) = ψ (y* S x)` on `ι → A` of a skew-hermitian matrix `S`, for a
continuous additive character `ψ : A → 𝕊¹` that is trivial on the skew-adjoint elements. -/
noncomputable def ofSkewHermitian (ψ : AddChar A Circle) (hψ : Continuous ψ)
    (hψ₁ : ∀ a ∈ skewAdjoint A, ψ a = 1) (S : Matrix ι ι A)
    (hS : S ∈ skewAdjoint (Matrix ι ι A)) : HeisenbergDatum (ι → A) where
  toFun x y := ψ (star y ⬝ᵥ S *ᵥ x)
  map_add_left' x x' y := by
    rw [mulVec_add, dotProduct_add, AddChar.map_add_eq_mul, Circle.coe_mul]
  map_add_right' x y y' := by
    rw [star_add, add_dotProduct, AddChar.map_add_eq_mul, Circle.coe_mul]
  apply_self' x := by
    rw [hψ₁ _ (star_dotProduct_mulVec_self_mem_skewAdjoint hS x), Circle.coe_one]
  norm_apply' x y := Circle.norm_coe _
  continuous_uncurry' := by
    have hS' : Continuous fun _ : (ι → A) × (ι → A) ↦ S := continuous_const
    exact continuous_subtypeVal.comp <| hψ.comp <|
      (continuous_star.comp continuous_snd).dotProduct (hS'.matrix_mulVec continuous_fst)

variable (ψ : AddChar A Circle) (hψ : Continuous ψ) (hψ₁ : ∀ a ∈ skewAdjoint A, ψ a = 1)
  (S : Matrix ι ι A) (hS : S ∈ skewAdjoint (Matrix ι ι A))

@[simp]
theorem ofSkewHermitian_apply (x y : ι → A) :
    ofSkewHermitian ψ hψ hψ₁ S hS x y = ψ (star y ⬝ᵥ S *ᵥ x) :=
  (rfl)

end HeisenbergDatum

end TauCeti
