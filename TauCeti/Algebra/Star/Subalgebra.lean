/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Subalgebra
public import Mathlib.RingTheory.TwoSidedIdeal.Kernel

/-!
# Range restrictions and surjective descent of `⋆`-algebra homomorphisms

Mathlib defines `codRestrict` and `rangeRestrict` for `NonUnitalStarAlgHom`
(`Mathlib/Algebra/Star/NonUnitalSubalgebra.lean`) and `StarAlgHom`
(`Mathlib/Algebra/Star/Subalgebra.lean`), but omits surjectivity of `rangeRestrict`,
compatibility of `TwoSidedIdeal.ker` with codomain and range restriction, and descent along a
surjective `⋆`-homomorphism. We supply these in nonunital and unital generality, mirroring
`AlgHom.rangeRestrict_surjective`, `AlgHom.ker_rangeRestrict`, and `AlgHom.liftOfSurjective`.

## Main results

* `NonUnitalStarAlgHom.rangeRestrict_surjective` and `StarAlgHom.rangeRestrict_surjective`:
  restricting a `⋆`-algebra homomorphism to its `⋆`-subalgebra range yields a surjective map.
* `NonUnitalStarAlgHom.ker_codRestrict`, `NonUnitalStarAlgHom.ker_rangeRestrict`,
  `StarAlgHom.ker_codRestrict`, and `StarAlgHom.ker_rangeRestrict`: restricting the codomain or
  range preserves `TwoSidedIdeal.ker`.
* `NonUnitalStarAlgHom.liftOfSurjective` and `StarAlgHom.liftOfSurjective`: descend a `⋆`-algebra
  homomorphism along a surjective `⋆`-algebra homomorphism whose two-sided ideal kernel is
  contained in the target map's kernel.

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

section LiftOfSurjective

variable {R A B C : Type*} [Monoid R]
  [NonUnitalNonAssocRing A] [DistribMulAction R A] [Star A]
  [NonUnitalNonAssocSemiring B] [DistribMulAction R B] [Star B]
  [NonUnitalNonAssocSemiring C] [DistribMulAction R C] [Star C]

private theorem map_surjInv_eq {f : A →⋆ₙₐ[R] B} (hf : Function.Surjective f)
    {g : A →⋆ₙₐ[R] C} (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g) (a : A) :
    g (Function.surjInv hf (f a)) = g a :=
  TwoSidedIdeal.ringCon_le_iff.mp hg (Function.surjInv_eq hf (f a))

/-- Descend a nonunital `⋆`-algebra homomorphism `g : A →⋆ₙₐ[R] C` along a surjective nonunital
`⋆`-algebra homomorphism `f : A →⋆ₙₐ[R] B` when `ker f ≤ ker g`. -/
noncomputable def liftOfSurjective (f : A →⋆ₙₐ[R] B) (hf : Function.Surjective f)
    (g : A →⋆ₙₐ[R] C) (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g) : B →⋆ₙₐ[R] C where
  toFun b := g (Function.surjInv hf b)
  map_smul' r b := by
    obtain ⟨a, rfl⟩ := hf b
    rw [MonoidHom.id_apply, ← map_smul f, map_surjInv_eq hf hg, map_surjInv_eq hf hg, map_smul g]
  map_zero' := by
    rw [← map_zero f, map_surjInv_eq hf hg, map_zero g]
  map_add' b₁ b₂ := by
    obtain ⟨a₁, rfl⟩ := hf b₁
    obtain ⟨a₂, rfl⟩ := hf b₂
    rw [← map_add f, map_surjInv_eq hf hg, map_surjInv_eq hf hg, map_surjInv_eq hf hg, map_add g]
  map_mul' b₁ b₂ := by
    obtain ⟨a₁, rfl⟩ := hf b₁
    obtain ⟨a₂, rfl⟩ := hf b₂
    rw [← map_mul f, map_surjInv_eq hf hg, map_surjInv_eq hf hg, map_surjInv_eq hf hg, map_mul g]
  map_star' b := by
    obtain ⟨a, rfl⟩ := hf b
    rw [← map_star f, map_surjInv_eq hf hg, map_surjInv_eq hf hg, map_star g]

@[simp]
theorem liftOfSurjective_apply (f : A →⋆ₙₐ[R] B) (hf : Function.Surjective f)
    (g : A →⋆ₙₐ[R] C) (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g) (a : A) :
    f.liftOfSurjective hf g hg (f a) = g a :=
  map_surjInv_eq hf hg a

@[simp]
theorem liftOfSurjective_comp (f : A →⋆ₙₐ[R] B) (hf : Function.Surjective f)
    (g : A →⋆ₙₐ[R] C) (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g) :
    (f.liftOfSurjective hf g hg).comp f = g :=
  ext <| f.liftOfSurjective_apply hf g hg

theorem eq_liftOfSurjective_iff {f : A →⋆ₙₐ[R] B} (hf : Function.Surjective f)
    {g : A →⋆ₙₐ[R] C} (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g) {h : B →⋆ₙₐ[R] C} :
    h = f.liftOfSurjective hf g hg ↔ h.comp f = g := by
  refine ⟨fun hh => hh ▸ f.liftOfSurjective_comp hf g hg, fun hh => ext fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hf b
  exact (DFunLike.congr_fun hh a).trans (f.liftOfSurjective_apply hf g hg a).symm

theorem liftOfSurjective_injective {f : A →⋆ₙₐ[R] B} (hf : Function.Surjective f)
    {g : A →⋆ₙₐ[R] C} (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g)
    (hker : TwoSidedIdeal.ker g ≤ TwoSidedIdeal.ker f) :
    Function.Injective (f.liftOfSurjective hf g hg) := by
  intro b₁ b₂ h
  obtain ⟨a₁, rfl⟩ := hf b₁
  obtain ⟨a₂, rfl⟩ := hf b₂
  rw [liftOfSurjective_apply, liftOfSurjective_apply] at h
  exact TwoSidedIdeal.ringCon_le_iff.mp hker h

theorem liftOfSurjective_surjective {f : A →⋆ₙₐ[R] B} (hf : Function.Surjective f)
    {g : A →⋆ₙₐ[R] C} (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g)
    (hg_surj : Function.Surjective g) :
    Function.Surjective (f.liftOfSurjective hf g hg) :=
  .of_comp (g := f) <| by rwa [← coe_comp, liftOfSurjective_comp]

end LiftOfSurjective

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

section LiftOfSurjective

variable {R A B C : Type*} [CommSemiring R]
  [Ring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B]
  [Semiring C] [Algebra R C] [Star C]

/-- Descend a unital `⋆`-algebra homomorphism `g : A →⋆ₐ[R] C` along a surjective unital
`⋆`-algebra homomorphism `f : A →⋆ₐ[R] B` when `ker f ≤ ker g`. -/
noncomputable def liftOfSurjective (f : A →⋆ₐ[R] B) (hf : Function.Surjective f)
    (g : A →⋆ₐ[R] C) (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g) : B →⋆ₐ[R] C :=
  let lift := f.toNonUnitalStarAlgHom.liftOfSurjective hf g.toNonUnitalStarAlgHom hg
  have hone : lift 1 = 1 := by
    simpa only [lift, coe_toNonUnitalStarAlgHom, map_one] using
      f.toNonUnitalStarAlgHom.liftOfSurjective_apply hf g.toNonUnitalStarAlgHom hg 1
  { toFun := lift
    map_one' := hone
    map_mul' := map_mul lift
    map_zero' := map_zero lift
    map_add' := map_add lift
    commutes' r := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, map_smul lift, hone]
    map_star' := map_star lift }

@[simp]
theorem toNonUnitalStarAlgHom_liftOfSurjective (f : A →⋆ₐ[R] B) (hf : Function.Surjective f)
    (g : A →⋆ₐ[R] C) (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g) :
    (f.liftOfSurjective hf g hg).toNonUnitalStarAlgHom =
      f.toNonUnitalStarAlgHom.liftOfSurjective hf g.toNonUnitalStarAlgHom hg :=
  (rfl)

@[simp]
theorem liftOfSurjective_apply (f : A →⋆ₐ[R] B) (hf : Function.Surjective f)
    (g : A →⋆ₐ[R] C) (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g) (a : A) :
    f.liftOfSurjective hf g hg (f a) = g a :=
  f.toNonUnitalStarAlgHom.liftOfSurjective_apply hf g.toNonUnitalStarAlgHom hg a

@[simp]
theorem liftOfSurjective_comp (f : A →⋆ₐ[R] B) (hf : Function.Surjective f)
    (g : A →⋆ₐ[R] C) (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g) :
    (f.liftOfSurjective hf g hg).comp f = g :=
  ext <| f.liftOfSurjective_apply hf g hg

theorem eq_liftOfSurjective_iff {f : A →⋆ₐ[R] B} (hf : Function.Surjective f)
    {g : A →⋆ₐ[R] C} (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g) {h : B →⋆ₐ[R] C} :
    h = f.liftOfSurjective hf g hg ↔ h.comp f = g := by
  refine ⟨fun hh => hh ▸ f.liftOfSurjective_comp hf g hg, fun hh => ext fun b => ?_⟩
  obtain ⟨a, rfl⟩ := hf b
  exact (DFunLike.congr_fun hh a).trans (f.liftOfSurjective_apply hf g hg a).symm

theorem liftOfSurjective_injective {f : A →⋆ₐ[R] B} (hf : Function.Surjective f)
    {g : A →⋆ₐ[R] C} (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g)
    (hker : TwoSidedIdeal.ker g ≤ TwoSidedIdeal.ker f) :
    Function.Injective (f.liftOfSurjective hf g hg) :=
  f.toNonUnitalStarAlgHom.liftOfSurjective_injective (g := g.toNonUnitalStarAlgHom) hf hg hker

theorem liftOfSurjective_surjective {f : A →⋆ₐ[R] B} (hf : Function.Surjective f)
    {g : A →⋆ₐ[R] C} (hg : TwoSidedIdeal.ker f ≤ TwoSidedIdeal.ker g)
    (hg_surj : Function.Surjective g) :
    Function.Surjective (f.liftOfSurjective hf g hg) :=
  f.toNonUnitalStarAlgHom.liftOfSurjective_surjective (g := g.toNonUnitalStarAlgHom) hf hg hg_surj

end LiftOfSurjective

end StarAlgHom
