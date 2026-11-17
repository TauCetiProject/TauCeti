/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Filtration.Tail
public import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Multiplicative total-degree tensor filtration tails

The total-degree tensor filtration tail of two multiplicative submodule families is
multiplicative. If both degree-zero terms are full, every term is a two-sided ideal,
even for noncommutative coefficient algebras. These ideals can be used to form quotient
towers and completed tensor products.

The multiplication estimate uses `Submodule.map₂_tmul_mul_le`. The input is expressed as
submodule families so it applies to ideal filtrations after restriction of scalars,
without imposing flatness or choosing tensor representatives.

Adapted from `yuma-mizuno-lean/Mei`, commit
`2f6cbcc81315ba2d32fd3e4bfc4c592476cf5471`,
`Mei/RingTheory/TensorProduct/Filtration.lean` (Apache 2.0).
-/

public section

namespace TauCeti

open scoped TensorProduct

variable {R A B : Type*} [CommSemiring R] [Semiring A] [Semiring B]
  [Algebra R A] [Algebra R B]
  (F : ℕ → Submodule R A) (G : ℕ → Submodule R B)

/-- The total-degree tensor filtration tail of multiplicative families is multiplicative. -/
theorem tensorFiltrationTail_mul_le
    (hF : ∀ a b, F a * F b ≤ F (a + b))
    (hG : ∀ a b, G a * G b ≤ G (a + b)) (n m : ℕ) :
    tensorFiltrationTail F G n * tensorFiltrationTail F G m ≤
      tensorFiltrationTail F G (n + m) := by
  rw [tensorFiltrationTail_def F G n, tensorFiltrationTail_def F G m]
  simp only [Submodule.iSup_mul, Submodule.mul_iSup, iSup_le_iff]
  intro c d hcd a b hab
  exact (Submodule.map₂_tmul_mul_le (F a) (F c) (G b) (G d)).trans
    ((Submodule.map₂_le_map₂ (hF a c) (hG b d)).trans
      (map₂_le_tensorFiltrationTail F G (n := n + m) (by omega)))

variable (hF : ∀ a b, F a * F b ≤ F (a + b))
  (hG : ∀ a b, G a * G b ≤ G (a + b))
  (hF0 : F 0 = ⊤) (hG0 : G 0 = ⊤)

/-- Each term of a full, multiplicative tensor filtration tail is a left ideal. -/
def tensorFiltrationTailIdeal (n : ℕ) : Ideal (A ⊗[R] B) where
  __ := (tensorFiltrationTail F G n).toAddSubmonoid
  smul_mem' x y hy := by
    have hx : x ∈ tensorFiltrationTail F G 0 := by simp [hF0, hG0]
    simpa using tensorFiltrationTail_mul_le F G hF hG 0 n (Submodule.mul_mem_mul hx hy)

/-- The underlying scalar submodule is exactly the original tensor filtration tail. -/
@[simp]
theorem tensorFiltrationTailIdeal_restrictScalars (n : ℕ) :
    (tensorFiltrationTailIdeal F G hF hG hF0 hG0 n).restrictScalars R =
      tensorFiltrationTail F G n := (rfl)

/-- Membership in a tensor filtration ideal is membership in its total-degree submodule. -/
@[simp]
theorem mem_tensorFiltrationTailIdeal {n : ℕ} {x : A ⊗[R] B} :
    x ∈ tensorFiltrationTailIdeal F G hF hG hF0 hG0 n ↔
      x ∈ tensorFiltrationTail F G n := Iff.rfl

/-- The tensor filtration tail ideals are two-sided, without commutativity of either factor. -/
instance tensorFiltrationTailIdeal_isTwoSided (n : ℕ) :
    (tensorFiltrationTailIdeal F G hF hG hF0 hG0 n).IsTwoSided where
  mul_mem_of_left x hy := by
    have hx : x ∈ tensorFiltrationTail F G 0 := by simp [hF0, hG0]
    simpa using tensorFiltrationTail_mul_le F G hF hG n 0 (Submodule.mul_mem_mul hy hx)

/-- Tensor filtration tail ideals decrease with the order. -/
theorem tensorFiltrationTailIdeal_antitone :
    Antitone (tensorFiltrationTailIdeal F G hF hG hF0 hG0) := by
  intro n m h x hx
  exact tensorFiltrationTail_antitone F G h hx

/-- The degree-zero tensor ideal is the full ring. -/
@[simp]
theorem tensorFiltrationTailIdeal_zero :
    tensorFiltrationTailIdeal F G hF hG hF0 hG0 0 = ⊤ := by
  ext x
  simp [hF0, hG0]

/-- Total-degree tensor ideals carry the standard multiplicative filtration. -/
instance tensorFiltrationTailIdeal_isRingFiltration :
    IsRingFiltration
      (fun n : ℕᵒᵈ => tensorFiltrationTailIdeal F G hF hG hF0 hG0 n.ofDual)
      (fun n : ℕᵒᵈ => tensorFiltrationTailIdeal F G hF hG hF0 hG0 (n.ofDual + 1)) where
  mono _ _ h := tensorFiltrationTailIdeal_antitone F G hF hG hF0 hG0 h
  is_le h := tensorFiltrationTailIdeal_antitone F G hF hG hF0 hG0 (Nat.succ_le_of_lt h)
  is_sup P n h := h (OrderDual.toDual (n.ofDual + 1)) (by exact Nat.lt_succ_self _)
  one_mem := by simp
  mul_mem i j x y hx hy := tensorFiltrationTail_mul_le F G hF hG i.ofDual j.ofDual
    (Submodule.mul_mem_mul hx hy)

end TauCeti
