/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.MaxTensor.Norm

/-!
# Functoriality and flip invariance of the maximal C*-norm

Let `A`, `A'` and `B`, `B'` be C*-algebras. A commuting pair of representations `(π, ρ)` of `A'`
and `B'` pulls back along star homomorphisms `φ : A → A'` and `ψ : B → B'` to the commuting pair
`(π ∘ φ, ρ ∘ ψ)` of `A` and `B` (`TauCeti.CommutingRepresentationPair.comp`), whose integrated form
is that of `(π, ρ)` composed with `φ ⊗ ψ : A ⊗[ℂ] B → A' ⊗[ℂ] B'`
(`TauCeti.CommutingRepresentationPair.tensorHom_comp`). Taking suprema, `φ ⊗ ψ` is
**contractive for the maximal norms**, `‖(φ ⊗ ψ)(x)‖_max ≤ ‖x‖_max`
(`TauCeti.maxTensorNorm_mapNonUnitalStarAlgHom_le`).

Swapping the two representations of a commuting pair of `A` and `B` gives a commuting pair of `B`
and `A` (`TauCeti.CommutingRepresentationPair.swap`), whose integrated form agrees with the
original one along the flip `A ⊗[ℂ] B ≃ B ⊗[ℂ] A` because the two ranges commute. So the maximal
norm is **invariant under the flip** (`TauCeti.maxTensorNorm_comm`).

The Hilbert spaces of commuting pairs range over the universe `max u v` for `A : Type u` and
`B : Type v`, so the functoriality is stated for `A, A' : Type u` and `B, B' : Type v`.

## Main declarations

* `TauCeti.CommutingRepresentationPair.comp`: the pullback of a commuting pair.
* `TauCeti.CommutingRepresentationPair.swap`: the swapped commuting pair.
* `TauCeti.maxTensorNorm_mapNonUnitalStarAlgHom_le`: `‖(φ ⊗ ψ)(x)‖_max ≤ ‖x‖_max`.
* `TauCeti.maxTensorNorm_comm`: `‖τ(x)‖_max = ‖x‖_max` for the flip `τ`.

## References

* B. Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*,
  II.9.2.5–II.9.2.6 (functoriality of C*-tensor products).
-/

public section

noncomputable section

open TensorProduct

universe u v

namespace TauCeti

namespace CommutingRepresentationPair

variable {A A' : Type u} {B B' : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A']
  [NonUnitalCStarAlgebra B] [NonUnitalCStarAlgebra B']

/-- The **pullback** of a commuting pair `(π, ρ)` of `A'` and `B'` along star homomorphisms
`φ : A → A'` and `ψ : B → B'`: the commuting pair `(π ∘ φ, ρ ∘ ψ)` of `A` and `B` on the same
Hilbert space. -/
abbrev comp (p : CommutingRepresentationPair A' B') (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') :
    CommutingRepresentationPair A B where
  H := p.H
  left := p.left.comp φ
  right := p.right.comp ψ
  commute a b := p.commute (φ a) (ψ b)

/-- The left representation of the pullback is `π ∘ φ`. -/
@[simp]
theorem comp_left_apply (p : CommutingRepresentationPair A' B') (φ : A →⋆ₙₐ[ℂ] A')
    (ψ : B →⋆ₙₐ[ℂ] B') (a : A) : (p.comp φ ψ).left a = p.left (φ a) :=
  (rfl)

/-- The right representation of the pullback is `ρ ∘ ψ`. -/
@[simp]
theorem comp_right_apply (p : CommutingRepresentationPair A' B') (φ : A →⋆ₙₐ[ℂ] A')
    (ψ : B →⋆ₙₐ[ℂ] B') (b : B) : (p.comp φ ψ).right b = p.right (ψ b) :=
  (rfl)

/-- The integrated form of the pullback is the integrated form of `(π, ρ)` composed with
`φ ⊗ ψ`. -/
theorem tensorHom_comp (p : CommutingRepresentationPair A' B') (φ : A →⋆ₙₐ[ℂ] A')
    (ψ : B →⋆ₙₐ[ℂ] B') (x : A ⊗[ℂ] B) :
    (p.comp φ ψ).tensorHom x =
      p.tensorHom (Algebra.TensorProduct.mapNonUnitalStarAlgHom φ ψ x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add (p.comp φ ψ).tensorHom, hx, hy,
      map_add (Algebra.TensorProduct.mapNonUnitalStarAlgHom φ ψ), map_add p.tensorHom]
  | tmul a b => simp

end CommutingRepresentationPair

namespace CommutingRepresentationPair

variable {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]

/-- The **swap** of a commuting pair `(π, ρ)` of `A` and `B`: the commuting pair `(ρ, π)` of `B`
and `A` on the same Hilbert space. -/
abbrev swap (p : CommutingRepresentationPair A B) : CommutingRepresentationPair B A where
  H := p.H
  left := p.right
  right := p.left
  commute b a := (p.commute a b).symm

/-- The left representation of the swapped pair is `ρ`. -/
@[simp]
theorem swap_left_apply (p : CommutingRepresentationPair A B) (b : B) :
    p.swap.left b = p.right b :=
  (rfl)

/-- The right representation of the swapped pair is `π`. -/
@[simp]
theorem swap_right_apply (p : CommutingRepresentationPair A B) (a : A) :
    p.swap.right a = p.left a :=
  (rfl)

/-- Swapping twice gives back the original commuting pair. -/
@[simp]
theorem swap_swap (p : CommutingRepresentationPair A B) : p.swap.swap = p :=
  (rfl)

/-- The integrated form of the swapped pair, composed with the flip, is the integrated form of
the original pair: `ρ b * π a = π a * ρ b` because the two ranges commute. -/
theorem tensorHom_swap_comm (p : CommutingRepresentationPair A B) (x : A ⊗[ℂ] B) :
    p.swap.tensorHom (TensorProduct.comm ℂ A B x) = p.tensorHom x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add (TensorProduct.comm ℂ A B), map_add p.swap.tensorHom, hx, hy,
      map_add p.tensorHom]
  | tmul a b => simpa using (p.commute a b).symm.eq

end CommutingRepresentationPair

open CommutingRepresentationPair

/-- **Functoriality of the maximal norm**: star homomorphisms `φ : A → A'` and `ψ : B → B'` give
`‖(φ ⊗ ψ)(x)‖_max ≤ ‖x‖_max`. -/
theorem maxTensorNorm_mapNonUnitalStarAlgHom_le {A A' : Type u} {B B' : Type v}
    [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra A'] [NonUnitalCStarAlgebra B]
    [NonUnitalCStarAlgebra B'] (φ : A →⋆ₙₐ[ℂ] A') (ψ : B →⋆ₙₐ[ℂ] B') (x : A ⊗[ℂ] B) :
    maxTensorNorm A' B' (Algebra.TensorProduct.mapNonUnitalStarAlgHom φ ψ x) ≤
      maxTensorNorm A B x :=
  maxTensorNorm_le_of_forall fun p ↦ by
    rw [← tensorHom_comp]
    exact norm_tensorHom_le_maxTensorNorm _ x

/-- **Flip invariance of the maximal norm**: `‖τ(x)‖_max = ‖x‖_max` for the flip
`τ : A ⊗[ℂ] B ≃ B ⊗[ℂ] A`. -/
@[simp]
theorem maxTensorNorm_comm {A : Type u} {B : Type v} [NonUnitalCStarAlgebra A]
    [NonUnitalCStarAlgebra B] (x : A ⊗[ℂ] B) :
    maxTensorNorm B A (TensorProduct.comm ℂ A B x) = maxTensorNorm A B x := by
  refine le_antisymm (maxTensorNorm_le_of_forall fun p ↦ ?_)
    (maxTensorNorm_le_of_forall fun p ↦ ?_)
  · rw [← p.swap_swap, tensorHom_swap_comm]
    exact norm_tensorHom_le_maxTensorNorm _ x
  · rw [← tensorHom_swap_comm]
    exact norm_tensorHom_le_maxTensorNorm _ _

end TauCeti
