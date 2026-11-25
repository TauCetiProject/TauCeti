/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.Idempotent
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Basic.Finite.Sum
public import TauCeti.Algebra.Algebra.Prod

/-!
# Product rings

Over a ring with invertible `2`, the half-sum and half-difference of a pair
have sum and difference equal to that pair.

Since `(1, 0)` is idempotent, a ring homomorphism from a product `E₁ × E₂` to a semiring without
zero divisors sends it to `0` or `1`, so it factors through one of the two projections
(`RingHom.exists_eq_comp_fst_or_snd`, from `AlgHom.prodFirst` applied to the homomorphism as an
`ℕ`-algebra map), and through only one when the target is nontrivial
(`RingHom.comp_fst_ne_comp_snd`, `RingHom.disjoint_image_comp_fst_image_comp_snd`,
`RingHom.comp_fst_mem_union_iff`, `RingHom.comp_snd_mem_union_iff`). So finitely many
homomorphisms out of each factor give finitely many out of the product
(`RingHom.instFiniteProd`).
-/

public section

namespace Prod

variable {R : Type*} [Ring R] [Invertible (2 : R)]

/-- The pair `(⅟2 (x + y), ⅟2 (x - y))` is sent back to `(x, y)` by `(a, b) ↦ (a + b, a - b)`. -/
theorem invOf_two_mul_add_sub (z : R × R) :
    (⅟(2 : R) * (z.1 + z.2) + ⅟(2 : R) * (z.1 - z.2),
      ⅟(2 : R) * (z.1 + z.2) - ⅟(2 : R) * (z.1 - z.2)) = z := by
  ext <;> simp [← mul_add, ← mul_sub, ← two_mul]

end Prod

namespace RingHom

variable {E₁ E₂ K : Type*} [Semiring E₁] [Semiring E₂] [Semiring K]

/-- Precomposition with the first projection is injective on ring homomorphisms. -/
theorem comp_fst_injective :
    Function.Injective fun ψ : E₁ →+* K ↦ ψ.comp (RingHom.fst E₁ E₂) :=
  fun _ _ h ↦ (RingHom.cancel_right Prod.fst_surjective).mp h

/-- Precomposition with the second projection is injective on ring homomorphisms. -/
theorem comp_snd_injective :
    Function.Injective fun ψ : E₂ →+* K ↦ ψ.comp (RingHom.snd E₁ E₂) :=
  fun _ _ h ↦ (RingHom.cancel_right Prod.snd_surjective).mp h

/-- No ring homomorphism from `E₁ × E₂` to a nontrivial semiring factors through both
projections. -/
theorem comp_fst_ne_comp_snd [Nontrivial K] (ψ₁ : E₁ →+* K) (ψ₂ : E₂ →+* K) :
    ψ₁.comp (RingHom.fst E₁ E₂) ≠ ψ₂.comp (RingHom.snd E₁ E₂) := fun h ↦ by
  simpa using congr($h (1, 0))

/-- Homomorphisms factoring through `fst` and homomorphisms factoring through `snd` form disjoint
sets of ring homomorphisms from `E₁ × E₂` to a nontrivial semiring. -/
theorem disjoint_image_comp_fst_image_comp_snd [Nontrivial K] (s₁ : Set (E₁ →+* K))
    (s₂ : Set (E₂ →+* K)) :
    Disjoint ((fun ψ : E₁ →+* K ↦ ψ.comp (RingHom.fst E₁ E₂)) '' s₁)
      ((fun ψ : E₂ →+* K ↦ ψ.comp (RingHom.snd E₁ E₂)) '' s₂) :=
  Set.disjoint_left.mpr fun _ ⟨ψ₁, _, h₁⟩ ⟨ψ₂, _, h₂⟩ ↦
    comp_fst_ne_comp_snd ψ₁ ψ₂ (h₁.trans h₂.symm)

/-- `ψ ∘ fst` lies in the union of the images of `s₁` under `· ∘ fst` and of `s₂` under `· ∘ snd`
exactly when `ψ ∈ s₁`. -/
theorem comp_fst_mem_union_iff [Nontrivial K] {s₁ : Set (E₁ →+* K)} {s₂ : Set (E₂ →+* K)}
    {ψ : E₁ →+* K} :
    ψ.comp (RingHom.fst E₁ E₂) ∈ (fun ψ : E₁ →+* K ↦ ψ.comp (RingHom.fst E₁ E₂)) '' s₁ ∪
      (fun ψ : E₂ →+* K ↦ ψ.comp (RingHom.snd E₁ E₂)) '' s₂ ↔ ψ ∈ s₁ := by
  simp only [Set.mem_union, Set.mem_image, comp_fst_injective.eq_iff, exists_eq_right]
  exact or_iff_left fun ⟨ψ₂, _, h⟩ ↦ comp_fst_ne_comp_snd ψ ψ₂ h.symm

/-- `ψ ∘ snd` lies in the union of the images of `s₁` under `· ∘ fst` and of `s₂` under `· ∘ snd`
exactly when `ψ ∈ s₂`. -/
theorem comp_snd_mem_union_iff [Nontrivial K] {s₁ : Set (E₁ →+* K)} {s₂ : Set (E₂ →+* K)}
    {ψ : E₂ →+* K} :
    ψ.comp (RingHom.snd E₁ E₂) ∈ (fun ψ : E₁ →+* K ↦ ψ.comp (RingHom.fst E₁ E₂)) '' s₁ ∪
      (fun ψ : E₂ →+* K ↦ ψ.comp (RingHom.snd E₁ E₂)) '' s₂ ↔ ψ ∈ s₂ := by
  simp only [Set.mem_union, Set.mem_image, comp_snd_injective.eq_iff, exists_eq_right]
  exact or_iff_right fun ⟨ψ₁, _, h⟩ ↦ comp_fst_ne_comp_snd ψ₁ ψ h

/-- **A ring homomorphism from a product to a semiring without zero divisors factors through a
projection.** The image of the idempotent `(1, 0)` is `0` or `1`; when it is `1`,
`AlgHom.prodFirst` gives the factorization through `fst`, and when it is `0` the image of `(0, 1)`
is `1` and the same applies after swapping the factors. -/
theorem exists_eq_comp_fst_or_snd [IsLeftCancelMulZero K] (φ : E₁ × E₂ →+* K) :
    (∃ ψ : E₁ →+* K, φ = ψ.comp (RingHom.fst E₁ E₂)) ∨
      ∃ ψ : E₂ →+* K, φ = ψ.comp (RingHom.snd E₁ E₂) := by
  have hidem : IsIdempotentElem (φ (1, 0)) := by
    rw [IsIdempotentElem, ← map_mul, Prod.mk_mul_mk, one_mul, zero_mul]
  rcases IsIdempotentElem.iff_eq_zero_or_one.mp hidem with h | h
  · -- `φ (0, 1) = 1`, so `φ ∘ swap` factors through `fst` and `φ` through `snd`
    have h1 : φ (0, 1) = 1 := by
      rw [← map_one φ, show (1 : E₁ × E₂) = (1, 0) + (0, 1) by ext <;> simp, map_add, h, zero_add]
    let φ' := (φ.comp (RingEquiv.prodComm (R := E₂) (S := E₁)).toRingHom).toNatAlgHom
    have h1' : φ' (1, 0) = 1 := by simpa [φ'] using h1
    exact .inr ⟨(φ'.prodFirst h1').toRingHom,
      RingHom.ext fun x ↦ (DFunLike.congr_fun (φ'.prodFirst_comp_fst h1') x.swap).symm⟩
  · exact .inl ⟨(φ.toNatAlgHom.prodFirst h).toRingHom,
      RingHom.ext fun x ↦ (DFunLike.congr_fun (φ.toNatAlgHom.prodFirst_comp_fst h) x).symm⟩

/-- A product of semirings with finitely many homomorphisms to a semiring without zero divisors
has finitely many. -/
instance instFiniteProd [IsLeftCancelMulZero K] [_root_.Finite (E₁ →+* K)]
    [_root_.Finite (E₂ →+* K)] : _root_.Finite (E₁ × E₂ →+* K) :=
  _root_.Finite.of_surjective
    (Sum.elim (fun ψ : E₁ →+* K ↦ ψ.comp (RingHom.fst E₁ E₂))
      (fun ψ : E₂ →+* K ↦ ψ.comp (RingHom.snd E₁ E₂)))
    fun φ : E₁ × E₂ →+* K ↦ by
      rcases φ.exists_eq_comp_fst_or_snd with ⟨ψ, rfl⟩ | ⟨ψ, rfl⟩
      exacts [⟨.inl ψ, rfl⟩, ⟨.inr ψ, rfl⟩]

end RingHom
