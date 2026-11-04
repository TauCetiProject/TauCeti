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
