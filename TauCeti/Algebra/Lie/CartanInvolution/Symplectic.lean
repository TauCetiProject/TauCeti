/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.Lie.CartanInvolution.Basic
public import TauCeti.Algebra.Lie.Symplectic.Cartan
import TauCeti.Algebra.Lie.Symplectic.Killing

/-!
# Cartan involution theory on the symplectic Lie algebra

Composed with the Killing form `κ(X, Y) = (2 n + 2) trace (X * Y)` of `sp l K`, the negative
transpose involution `θ Y = -Yᵀ` (`LieAlgebra.Symplectic.cartanInvolution`) gives
`-κ(X, θ X) = (2 n + 2) trace (X * Xᵀ)`, the sum of the squares of the entries of `X` times
`2 n + 2`. Over an ordered field it is positive for every nonzero `X`, so `θ` is a Cartan
involution of the symplectic Lie algebra, and for nonempty `l` the identity is not.

## Main results

* `LieAlgebra.Symplectic.killingForm_cartanInvolution_apply`:
  `κ(X, θ Y) = -((2 n + 2) trace (X * Yᵀ))`.
* `LieAlgebra.Symplectic.killingForm_cartanInvolution_self_neg`: `κ(X, θ X) < 0` for nonzero `X`
  over an ordered field.
* `LieAlgebra.Symplectic.isCartanInvolution_cartanInvolution`: `θ` is a Cartan involution
  (`LieEquiv.IsCartanInvolution`) over an ordered field.
* `LieAlgebra.Symplectic.not_isCartanInvolution_refl`: for nonempty `l`, the identity is not a
  Cartan involution of `sp l K`.

## References

* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, second edition.
* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter VI, Section 1 (Cartan involutions).
-/

public section

namespace LieAlgebra.Symplectic

open Matrix

variable {l : Type*} [Fintype l] [DecidableEq l]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The Killing form of `sp l K` twisted by the involution `θ Y = -Yᵀ`:
`κ(X, θ Y) = -((2 n + 2) trace (X * Yᵀ))`. -/
theorem killingForm_cartanInvolution_apply {K : Type*} [Field K] [NeZero (2 : K)]
    (X Y : sp l K) :
    killingForm K (sp l K) X (cartanInvolution l K Y) =
      -((2 * Fintype.card l + 2) *
        ((X : Matrix (l ⊕ l) (l ⊕ l) K) * (Y : Matrix (l ⊕ l) (l ⊕ l) K)ᵀ).trace) := by
  rw [killingForm_apply, coe_cartanInvolution, mul_neg, trace_neg, mul_neg]

/-- Over an ordered field, `κ(X, θ X) < 0` for every nonzero `X ∈ sp l K`, where `θ X = -Xᵀ`,
since `-κ(X, θ X)` is `2 n + 2` times the sum of the squares of the entries of `X`. -/
theorem killingForm_cartanInvolution_self_neg {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] {X : sp l K} (hX : X ≠ 0) :
    killingForm K (sp l K) X (cartanInvolution l K X) < 0 := by
  rw [killingForm_cartanInvolution_apply, neg_lt_zero]
  obtain ⟨i, j, hij⟩ : ∃ i j, (X : Matrix (l ⊕ l) (l ⊕ l) K) i j ≠ 0 := by
    by_contra! h
    exact hX (Subtype.ext (Matrix.ext h))
  have htrace : 0 < ((X : Matrix (l ⊕ l) (l ⊕ l) K) * (X : Matrix (l ⊕ l) (l ⊕ l) K)ᵀ).trace := by
    simp only [Matrix.trace, diag_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_pos' (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ mul_self_nonneg _)
      ⟨i, Finset.mem_univ _, Finset.sum_pos' (fun _ _ ↦ mul_self_nonneg _)
        ⟨j, Finset.mem_univ _, mul_self_pos.mpr hij⟩⟩
  positivity

/-- **`θ X = -Xᵀ` is a Cartan involution of `sp l K`** over an ordered field. -/
theorem isCartanInvolution_cartanInvolution {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] : (cartanInvolution l K).IsCartanInvolution :=
  LieEquiv.isCartanInvolution_iff.mpr
    ⟨cartanInvolution_cartanInvolution, fun _ ↦ killingForm_cartanInvolution_self_neg⟩

/-- For nonempty `l`, the symplectic Lie algebra `sp l K` over an ordered field is noncompact: the
identity automorphism is not a Cartan involution. -/
theorem not_isCartanInvolution_refl [Nonempty l] {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] :
    ¬ (LieEquiv.refl : sp l K ≃ₗ⁅K⁆ sp l K).IsCartanInvolution := by
  intro hrefl
  let Hmat : Matrix (l ⊕ l) (l ⊕ l) K := Matrix.fromBlocks 1 0 0 (-1)
  have hHmem : Hmat ∈ sp l K := by
    simp [Hmat, mem_sp, Matrix.J, Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_neg]
  let H : sp l K := ⟨Hmat, hHmem⟩
  have hHne : H ≠ 0 := by
    intro h0
    have hval := congrArg (fun M : sp l K ↦
      (M : Matrix (l ⊕ l) (l ⊕ l) K) (Sum.inl (Classical.arbitrary l))
        (Sum.inl (Classical.arbitrary l))) h0
    simp [H, Hmat] at hval
  have hHp : H ∈ (cartanInvolution l K).cartanP := by
    simp [H, Hmat, Matrix.fromBlocks_transpose]
  have hpos : 0 < killingForm K (sp l K) H H :=
    (isCartanInvolution_cartanInvolution).killingForm_apply_self_pos_of_mem_cartanP hHp hHne
  have hneg : killingForm K (sp l K) H H < 0 :=
    (LieEquiv.isCartanInvolution_refl_iff.mp hrefl) H hHne
  exact lt_asymm hpos hneg

end LieAlgebra.Symplectic
