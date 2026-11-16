/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.NonUnitalSubalgebra

/-!
# Self-adjoint core of a left-absorbing submodule

For a left-absorbing `R`-submodule `L` of a nonunital `⋆`-algebra `A`, the intersection
`L ∩ star ⁻¹' L` is closed under addition, scalar multiplication, involution, and multiplication
(`x * y ∈ L` by left absorption on `y ∈ L`, and `star (x * y) = star y * star x ∈ L` by left
absorption on `star x ∈ L`). Moreover, it is the largest nonunital `⋆`-subalgebra contained in `L`
and satisfies the two-sided sandwich law `b₁ * a * b₂ ∈ L ∩ star ⁻¹' L`.

In C⋆-algebras, this construction forms the algebraic half of the order-preserving bijection between
closed complex left ideals and closed hereditary C⋆-subalgebras.

## Main declarations

* `Submodule.starCore`: the self-adjoint core `L ∩ star ⁻¹' L` of a left-absorbing `R`-submodule `L`
  of `A`, bundled as a `NonUnitalStarSubalgebra R A`.
* `Submodule.le_starCore_iff`: universal property characterizing `L.starCore hL` as the greatest
  nonunital `⋆`-subalgebra contained in `L`.
* `Submodule.mul_mul_mem_starCore`: hereditary sandwich closure `b₁ * a * b₂ ∈ L.starCore hL`.
* `Submodule.starCore_mono`, `Submodule.starCore_bot`, and `Submodule.starCore_top`: monotonicity
  and lattice boundary lemmas.
-/

public section

namespace Submodule

section Star

variable {R A : Type*} [CommSemiring R] [Star R] [NonUnitalSemiring A] [StarRing A]
  [Module R A] [StarModule R A]

/-- The self-adjoint core `L ∩ star ⁻¹' L` of a left-absorbing `R`-submodule `L` of `A`, bundled as
a nonunital `⋆`-subalgebra. -/
def starCore (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    NonUnitalStarSubalgebra R A where
  carrier := {x : A | x ∈ L ∧ star x ∈ L}
  mul_mem' {x y} hx hy :=
    ⟨hL x y hy.1, by rw [star_mul]; exact hL (star y) (star x) hx.2⟩
  add_mem' {x y} hx hy := ⟨L.add_mem hx.1 hy.1, by rw [star_add]; exact L.add_mem hx.2 hy.2⟩
  zero_mem' := ⟨L.zero_mem, by rw [star_zero]; exact L.zero_mem⟩
  smul_mem' c {x} hx := ⟨L.smul_mem c hx.1, by rw [star_smul]; exact L.smul_mem (star c) hx.2⟩
  star_mem' {x} hx := ⟨hx.2, by rw [star_star]; exact hx.1⟩

@[simp]
theorem mem_starCore (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) {x : A} :
    x ∈ L.starCore hL ↔ x ∈ L ∧ star x ∈ L :=
  Iff.rfl

@[simp]
theorem coe_starCore (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    (L.starCore hL : Set A) = (L : Set A) ∩ star ⁻¹' (L : Set A) :=
  (rfl)

/-- The self-adjoint core `L.starCore hL` is contained in `L`. -/
theorem starCore_subset (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    (L.starCore hL : Set A) ⊆ L :=
  fun _ hx ↦ hx.1

/-- `L.starCore hL` is the largest nonunital `⋆`-subalgebra of `A` contained in `L`. -/
theorem le_starCore_iff {S : NonUnitalStarSubalgebra R A} (L : Submodule R A)
    (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) :
    S ≤ L.starCore hL ↔ (S : Set A) ⊆ L :=
  ⟨fun h _ hx ↦ (h hx).1, fun h _ hx ↦ ⟨h hx, h (star_mem hx)⟩⟩

/-- The self-adjoint core of a left-absorbing submodule satisfies the hereditary sandwich property
`b₁ * a * b₂ ∈ L.starCore hL`. -/
theorem mul_mul_mem_starCore (L : Submodule R A) (hL : ∀ a : A, ∀ x ∈ L, a * x ∈ L) {b₁ : A}
    (hb₁ : b₁ ∈ L.starCore hL) (a : A) {b₂ : A} (hb₂ : b₂ ∈ L.starCore hL) :
    b₁ * a * b₂ ∈ L.starCore hL := by
  rw [mem_starCore] at hb₁ hb₂ ⊢
  refine ⟨by rw [mul_assoc]; exact hL b₁ (a * b₂) (hL a b₂ hb₂.1), ?_⟩
  rw [star_mul, star_mul, ← mul_assoc]
  exact hL (star b₂ * star a) (star b₁) hb₁.2

/-- `Submodule.starCore` is monotone with respect to inclusion of left ideals. -/
theorem starCore_mono {L₁ L₂ : Submodule R A} {hL₁ : ∀ a : A, ∀ x ∈ L₁, a * x ∈ L₁}
    {hL₂ : ∀ a : A, ∀ x ∈ L₂, a * x ∈ L₂} (h : L₁ ≤ L₂) :
    L₁.starCore hL₁ ≤ L₂.starCore hL₂ :=
  fun _ hx ↦ ⟨h hx.1, h hx.2⟩

end Star

section Lattice

variable {R A : Type*} [CommSemiring R] [StarRing R] [NonUnitalSemiring A] [StarRing A]
  [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] [StarModule R A]

@[simp]
theorem starCore_bot (hL : ∀ a : A, ∀ x ∈ (⊥ : Submodule R A), a * x ∈ (⊥ : Submodule R A)) :
    (⊥ : Submodule R A).starCore hL = ⊥ := by
  ext x
  simp [NonUnitalStarAlgebra.mem_bot]

@[simp]
theorem starCore_top (hL : ∀ a : A, ∀ x ∈ (⊤ : Submodule R A), a * x ∈ (⊤ : Submodule R A)) :
    (⊤ : Submodule R A).starCore hL = ⊤ := by
  ext x
  simp

end Lattice

end Submodule
