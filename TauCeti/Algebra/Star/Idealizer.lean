/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
import TauCeti.Algebra.Star.Basic

/-!
# The idealizer of a nonunital `⋆`-subalgebra

Given `S : NonUnitalStarSubalgebra R A` in a unital `⋆`-algebra `A`, its *idealizer*
`S.idealizer : StarSubalgebra R A` is `{a : A | ∀ x ∈ S, a * x ∈ S ∧ x * a ∈ S}`, the largest
unital `⋆`-subalgebra of `A` containing `S` as a two-sided `⋆`-ideal (`S.le_idealizer`). By
`star`-invariance, two-sided absorption reduces to left absorption of `a` and `star a`
(`mem_idealizer_iff_mul_mem_left`), and `S.idealizer = ⊤` iff `S` absorbs ambient left
multiplication (`idealizer_eq_top_iff`).

## References

* Gerd K. Pedersen, *C*-Algebras and their Automorphism Groups*, §3.12.
* Bruce Blackadar, *Operator Algebras: Theory of C*-Algebras and von Neumann Algebras*, II.7.3.
-/

public section

namespace NonUnitalStarSubalgebra

variable {R A : Type*} [CommSemiring R] [StarRing R] [Semiring A] [StarRing A] [Algebra R A]
  [StarModule R A] (S : NonUnitalStarSubalgebra R A)

/-- The *idealizer* of a nonunital `⋆`-subalgebra `S` in a unital `⋆`-algebra `A`: the unital
`⋆`-subalgebra `{a : A | ∀ x ∈ S, a * x ∈ S ∧ x * a ∈ S}` in which `S` sits as a two-sided ideal. -/
def idealizer : StarSubalgebra R A where
  carrier := {a : A | ∀ x ∈ S, a * x ∈ S ∧ x * a ∈ S}
  add_mem' {a b} ha hb x hx := ⟨add_mul a b x ▸ add_mem (ha x hx).1 (hb x hx).1,
    mul_add x a b ▸ add_mem (ha x hx).2 (hb x hx).2⟩
  zero_mem' _ _ := ⟨by simp, by simp⟩
  mul_mem' {a b} ha hb x hx := ⟨mul_assoc a b x ▸ (ha _ (hb x hx).1).1,
    (mul_assoc x a b).symm ▸ (hb _ (ha x hx).2).2⟩
  one_mem' _ hx := ⟨by simpa using hx, by simpa using hx⟩
  algebraMap_mem' r x hx :=
    have hrx : algebraMap R A r * x ∈ S := Algebra.smul_def r x ▸ SMulMemClass.smul_mem r hx
    ⟨hrx, Algebra.commutes r x ▸ hrx⟩
  star_mem' {a} ha x hx := ⟨by simpa [star_mul] using star_mem (ha (star x) (star_mem hx)).2,
    by simpa [star_mul] using star_mem (ha (star x) (star_mem hx)).1⟩

variable {S}

@[simp] theorem mem_idealizer {a : A} : a ∈ S.idealizer ↔ ∀ x ∈ S, a * x ∈ S ∧ x * a ∈ S := Iff.rfl

/-- Because `S` is `star`-invariant, `a ∈ S.idealizer` iff `a` and `star a` multiply `S` into
itself on the left. -/
theorem mem_idealizer_iff_mul_mem_left {a : A} :
    a ∈ S.idealizer ↔ ∀ x ∈ S, a * x ∈ S ∧ star a * x ∈ S :=
  ⟨fun ha x hx => ⟨(ha x hx).1, ((star_mem ha : star a ∈ S.idealizer) x hx).1⟩,
    fun ha x hx => ⟨(ha x hx).1, by simpa [star_mul] using star_mem (ha (star x) (star_mem hx)).2⟩⟩

theorem mul_mem_of_mem_idealizer_left {a x : A} (ha : a ∈ S.idealizer) (hx : x ∈ S) : a * x ∈ S :=
  (S.mem_idealizer.mp ha x hx).1

theorem mul_mem_of_mem_idealizer_right {a x : A} (ha : a ∈ S.idealizer) (hx : x ∈ S) : x * a ∈ S :=
  (S.mem_idealizer.mp ha x hx).2

/-- Every nonunital `⋆`-subalgebra is contained in its idealizer. -/
theorem le_idealizer : S ≤ S.idealizer.toNonUnitalStarSubalgebra :=
  fun _ ha _ hx => ⟨mul_mem ha hx, mul_mem hx ha⟩

theorem subset_idealizer : (S : Set A) ⊆ S.idealizer := S.le_idealizer

@[simp] theorem idealizer_top : (⊤ : NonUnitalStarSubalgebra R A).idealizer = ⊤ :=
  StarSubalgebra.ext fun _ => by simp

/-- The idealizer of `S` is all of `A` if and only if `S` absorbs left multiplication by `A`. -/
theorem idealizer_eq_top_iff : S.idealizer = ⊤ ↔ ∀ (a : A), ∀ x ∈ S, a * x ∈ S :=
  ⟨fun h _ _ hx => S.mul_mem_of_mem_idealizer_left (h ▸ StarSubalgebra.mem_top) hx,
    fun h => StarSubalgebra.ext fun a => ⟨fun _ => StarSubalgebra.mem_top, fun _ =>
      S.mem_idealizer.mpr fun x hx =>
        ⟨h a x hx, StarMemClass.mul_mem_right_of_mul_mem_left h a hx⟩⟩⟩

end NonUnitalStarSubalgebra
