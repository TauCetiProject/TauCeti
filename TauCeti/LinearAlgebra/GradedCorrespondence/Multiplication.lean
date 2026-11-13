/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.GradedCorrespondence.Basic
public import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# Multiplication of homogeneous transfers

When the opposite span map preserves a product of chosen lifts, transfer of that
homogeneous product is the finite convolution of the transfers of its factors. The
sum uses the two actual output supports, so no finiteness assumption on the fibers
of addition in the grading monoid is needed. Joint injectivity of the span and
multiplication on the middle module are not needed.

The proof uses Mathlib's `DirectSum.decompose_mul` and `DirectSum.coe_mul_apply`.

Adapted from `Mei/LinearAlgebra/GradedCorrespondence/Multiplication.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`3d2e9c869ee44c41ae9c7b5c6e2042898430d0ca` (Apache 2.0).
-/

public section

namespace TauCeti.GradedCorrespondence

variable {R B U V ι κ : Type*} [Semiring R]
  [AddCommMonoid B] [Module R B]
  [AddCommMonoid U] [Module R U] [Mul U]
  [Semiring V] [Module R V] [Add ι] [AddMonoid κ] [DecidableEq κ]
  {𝒰 : ι → Submodule R U} {𝒱 : κ → Submodule R V}
  [SetLike.GradedMul 𝒰] [GradedRing 𝒱] {I : Set ι} {J : Set κ}

/-- A transferred homogeneous product is the convolution of the two transferred factors.
Only the indicated product of lifts and its image need to be multiplicative. In particular,
these hypotheses hold for multiplicative admissible lifts and an algebra-homomorphism leg.
The admissible set need not be closed under addition: admissibility of the sum is explicit.
The reverse-crossing formula is this theorem applied to `C.symm`. -/
theorem transfer_mul (C : TauCeti.GradedCorrespondence (B := B) 𝒰 𝒱 I J)
    (i j : I) (hij : (i : ι) + (j : ι) ∈ I) (a : 𝒰 i) (b : 𝒰 j)
    (hmul : C.right (C.liftLeft ⟨(i : ι) + (j : ι), hij⟩
      ⟨(a : U) * (b : U), SetLike.mul_mem_graded a.property b.property⟩) =
      C.right (C.liftLeft i a) * C.right (C.liftLeft j b))
    [∀ k (v : 𝒱 k), Decidable (v ≠ 0)] (k : κ) :
    (C.transfer ⟨(i : ι) + (j : ι), hij⟩ k
      ⟨(a : U) * (b : U), SetLike.mul_mem_graded a.property b.property⟩ : V) =
      ∑ p ∈ (DirectSum.decompose 𝒱 (C.right (C.liftLeft i a))).support ×ˢ
        (DirectSum.decompose 𝒱 (C.right (C.liftLeft j b))).support
        with p.1 + p.2 = k, (C.transfer i p.1 a : V) * (C.transfer j p.2 b : V) := by
  simp only [transfer_apply, hmul, DirectSum.decompose_mul]
  exact DirectSum.coe_mul_apply 𝒱 _ _ k

end TauCeti.GradedCorrespondence
