/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# Range and codomain restrictions of `⋆`-algebra homomorphisms

Mathlib defines `codRestrict` and `rangeRestrict` for `NonUnitalStarAlgHom`
(`Mathlib/Algebra/Star/NonUnitalSubalgebra.lean`) and `StarAlgHom`
(`Mathlib/Algebra/Star/Subalgebra.lean`), but omits surjectivity of `rangeRestrict` and
compatibility of `TwoSidedIdeal.ker` with codomain and range restriction. We supply both in
nonunital and unital generality, mirroring `AlgHom.rangeRestrict_surjective` and
`AlgHom.ker_rangeRestrict`.

## Main results

* `NonUnitalStarAlgHom.rangeRestrict_surjective` and `StarAlgHom.rangeRestrict_surjective`:
  restricting a `⋆`-algebra homomorphism to its `⋆`-subalgebra range yields a surjective map.
* `NonUnitalStarAlgHom.ker_codRestrict`, `NonUnitalStarAlgHom.ker_rangeRestrict`,
  `StarAlgHom.ker_codRestrict`, and `StarAlgHom.ker_rangeRestrict`: restricting the codomain or
  range preserves `TwoSidedIdeal.ker`.
* `Submodule.starCore`: the self-adjoint core `L ∩ star ⁻¹' L` of a left-absorbing `R`-submodule `L`
  of a nonunital star algebra `A`, bundled as a `NonUnitalStarSubalgebra R A`, together with the
  sandwich property `Submodule.mul_mul_mem_starCore` and monotonicity `Submodule.starCore_mono`.

## Implementation notes

`NonUnitalStarAlgHom.rangeRestrict` is an `abbrev` for `NonUnitalStarAlgHom.codRestrict`, so
`@[simp]` is placed on `NonUnitalStarAlgHom.ker_codRestrict` (which already simplifies
`TwoSidedIdeal.ker f.rangeRestrict`), whereas `StarAlgHom.rangeRestrict` is an irreducible `def` and
receives its own `@[simp]` attribute.
-/

public section

namespace NonUnitalStarAlgHom

section RangeRestrict

variable {R A B : Type*} [CommSemiring R]
  [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
  [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

/-- Restricting a nonunital `⋆`-algebra homomorphism to its range gives a surjective map. -/
theorem rangeRestrict_surjective (f : A →⋆ₙₐ[R] B) : Function.Surjective f.rangeRestrict :=
  fun ⟨_, a, ha⟩ => ⟨a, Subtype.ext ha⟩

end RangeRestrict

section Ker

variable {R A B : Type*} [CommSemiring R]
  [NonUnitalNonAssocRing A] [Module R A] [Star A]
  [NonUnitalNonAssocSemiring B] [Module R B] [Star B]

/-- Restricting the codomain of a nonunital `⋆`-algebra homomorphism to a nonunital `⋆`-subalgebra
preserves its two-sided ideal kernel. -/
@[simp]
theorem ker_codRestrict (f : A →⋆ₙₐ[R] B) (S : NonUnitalStarSubalgebra R B)
    (hf : ∀ x, f x ∈ S) :
    TwoSidedIdeal.ker (f.codRestrict S hf) = TwoSidedIdeal.ker f := by
  ext a
  rw [TwoSidedIdeal.mem_ker, TwoSidedIdeal.mem_ker, Subtype.ext_iff]
  rfl

/-- Restricting a nonunital `⋆`-algebra homomorphism to its range preserves its two-sided ideal
kernel. -/
theorem ker_rangeRestrict (f : A →⋆ₙₐ[R] B) :
    TwoSidedIdeal.ker f.rangeRestrict = TwoSidedIdeal.ker f :=
  f.ker_codRestrict f.range f.mem_range_self

end Ker

end NonUnitalStarAlgHom

namespace StarAlgHom

section RangeRestrict

variable {R A B : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [Algebra R A] [StarRing A]
  [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- Restricting a unital `⋆`-algebra homomorphism to its range gives a surjective map. -/
theorem rangeRestrict_surjective (f : A →⋆ₐ[R] B) : Function.Surjective f.rangeRestrict :=
  f.toAlgHom.rangeRestrict_surjective

end RangeRestrict

section Ker

variable {R A B : Type*} [CommSemiring R] [StarRing R]
  [Ring A] [Algebra R A] [StarRing A]
  [Semiring B] [Algebra R B] [StarRing B] [StarModule R B]

/-- Restricting the codomain of a unital `⋆`-algebra homomorphism to a `⋆`-subalgebra preserves its
two-sided ideal kernel. -/
@[simp]
theorem ker_codRestrict (f : A →⋆ₐ[R] B) (S : StarSubalgebra R B) (hf : ∀ x, f x ∈ S) :
    TwoSidedIdeal.ker (f.codRestrict S hf) = TwoSidedIdeal.ker f :=
  f.toNonUnitalStarAlgHom.ker_codRestrict S.toNonUnitalStarSubalgebra hf

/-- Restricting a unital `⋆`-algebra homomorphism to its range preserves its two-sided ideal kernel.
-/
@[simp]
theorem ker_rangeRestrict (f : A →⋆ₐ[R] B) :
    TwoSidedIdeal.ker f.rangeRestrict = TwoSidedIdeal.ker f :=
  f.ker_codRestrict f.range fun x => ⟨x, rfl⟩

end Ker

end StarAlgHom

namespace Submodule

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

end Submodule
