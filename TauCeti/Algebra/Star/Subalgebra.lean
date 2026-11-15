/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel
import Mathlib.Algebra.Algebra.Subalgebra.Pointwise

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
* `StarSubalgebra.toSubmodule_sup_of_commute`: for elementwise commuting `⋆`-subalgebras `S` and
  `T`, the underlying submodule of `S ⊔ T` is `S.toSubmodule * T.toSubmodule`.
* `StarAlgebra.adjoin_eq_span_of_mul_mem`: for a self-adjoint multiplicatively closed set `s`,
  `StarAlgebra.adjoin R s` has underlying submodule `Submodule.span R (insert 1 s)`.

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

namespace StarSubalgebra

variable {R A : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- If every element of `S` commutes with every element of `T`, the underlying submodule of the
`⋆`-subalgebra join `S ⊔ T` is the submodule product `S.toSubmodule * T.toSubmodule`. -/
theorem toSubmodule_sup_of_commute {S T : StarSubalgebra R A}
    (hcomm : ∀ a ∈ S, ∀ b ∈ T, Commute a b) :
    (S ⊔ T).toSubmodule = S.toSubmodule * T.toSubmodule := by
  let P : Submodule R A := S.toSubmodule * T.toSubmodule
  have hle : P ≤ (S ⊔ T).toSubmodule :=
    (S.toSubalgebra.mul_toSubmodule_le T.toSubalgebra).trans
      (sup_le (toSubalgebra_le_iff.mpr le_sup_left) (toSubalgebra_le_iff.mpr le_sup_right))
  refine le_antisymm ?_ hle
  have hmul : ∀ u ∈ P, ∀ v ∈ P, u * v ∈ P := fun u hu =>
    Submodule.mul_induction_on hu
      (fun a₁ ha₁ b₁ hb₁ v hv =>
        Submodule.mul_induction_on hv
          (fun a₂ ha₂ b₂ hb₂ => by
            have hba : b₁ * a₂ = a₂ * b₁ := (hcomm a₂ ha₂ b₁ hb₁).symm.eq
            have key : a₁ * b₁ * (a₂ * b₂) = (a₁ * a₂) * (b₁ * b₂) := by
              calc
                a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by simp only [mul_assoc]
                _ = a₁ * (a₂ * b₁) * b₂ := by rw [hba]
                _ = (a₁ * a₂) * (b₁ * b₂) := by simp only [mul_assoc]
            rw [key]
            exact Submodule.mul_mem_mul (S.mul_mem ha₁ ha₂) (T.mul_mem hb₁ hb₂))
          fun x y hx hy => by rw [mul_add]; exact P.add_mem hx hy)
      fun x y hx hy v hv => by rw [add_mul]; exact P.add_mem (hx v hv) (hy v hv)
  let U : StarSubalgebra R A :=
    { P with
      one_mem' := mul_one (1 : A) ▸ Submodule.mul_mem_mul S.one_mem T.one_mem
      mul_mem' := fun {u v} hu hv => hmul u hu v hv
      algebraMap_mem' := fun r => by
        rw [Algebra.algebraMap_eq_smul_one]
        exact P.smul_mem r (mul_one (1 : A) ▸ Submodule.mul_mem_mul S.one_mem T.one_mem)
      star_mem' := fun {u} hu =>
        Submodule.mul_induction_on hu
          (fun a ha b hb => by
            rw [star_mul, (hcomm (star a) (S.star_mem' ha) (star b) (T.star_mem' hb)).symm.eq]
            exact Submodule.mul_mem_mul (S.star_mem' ha) (T.star_mem' hb))
          fun x y hx hy => by rw [star_add]; exact P.add_mem hx hy }
  have hSU : S ≤ U := fun a ha => mul_one a ▸ Submodule.mul_mem_mul ha T.one_mem
  have hTU : T ≤ U := fun b hb => one_mul b ▸ Submodule.mul_mem_mul S.one_mem hb
  exact sup_le hSU hTU

end StarSubalgebra

namespace StarAlgebra

open scoped Pointwise

variable {R A : Type*} [CommSemiring R] [StarRing R]
  [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- For a self-adjoint multiplicatively closed subset `s`, the `⋆`-algebra it generates has
underlying submodule `Submodule.span R (insert 1 s)`. -/
theorem adjoin_eq_span_of_mul_mem {s : Set A} (hstar : star s ⊆ s)
    (hmul : ∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) :
    (adjoin R s).toSubmodule = Submodule.span R (insert 1 s) := by
  let sg : Subsemigroup A := ⟨s, fun {a b} ha hb => hmul a ha b hb⟩
  have hsg : (Subsemigroup.closure s : Set A) = s :=
    congrArg SetLike.coe
      (Subsemigroup.closure_eq_of_le (S := sg) subset_rfl Subsemigroup.subset_closure)
  rw [adjoin_eq_span, Set.union_eq_left.2 hstar, Submonoid.closure_eq_one_union, hsg,
    Set.singleton_union]
end StarAlgebra
