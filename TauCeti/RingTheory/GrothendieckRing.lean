/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup
public import Mathlib.Tactic.Abel

/-!
# The Grothendieck ring of a semiring

Mathlib's `Algebra.GrothendieckAddGroup M` is the group completion of an additive commutative
monoid `M`, realized as the localization of `M` at its top submonoid. When `M` carries a semiring
structure the completion carries a ring structure, uniquely determined by the requirement that
the canonical map `Algebra.GrothendieckAddGroup.of` be multiplicative, and it is commutative when
the semiring is. This file constructs that ring.

The multiplication is built from the universal property rather than from the underlying
quotient: multiplication by a fixed element of the semiring extends to an additive endomorphism
of the completion, and the assignment of that endomorphism is itself additive, so it extends
once more. No well-definedness computation on the localization relation is needed, and no
cancellativity hypothesis is used.

## Main definitions

* `Algebra.GrothendieckAddGroup.liftAddEquiv`: Mathlib's `lift` as an additive isomorphism.
* `Algebra.GrothendieckAddGroup.instRing` and `Algebra.GrothendieckAddGroup.instCommRing`: the
  ring structure, commutative when the semiring is.
* `Algebra.GrothendieckAddGroup.ofRingHom`: the canonical semiring map into the completion.
* `Algebra.GrothendieckAddGroup.liftRingHom`: the universal property, as an equivalence between
  semiring homomorphisms out of `S` into a ring and ring homomorphisms out of the completion.

## References

* [*Grothendieck group*, Wikipedia](https://en.wikipedia.org/wiki/Grothendieck_group)
-/

public section

namespace Algebra.GrothendieckAddGroup

variable {M : Type*} [AddCommMonoid M] {G : Type*} [AddCommGroup G]

/-! ### The universal property, in additive form -/

/-- Restricting the extension of `f` along `of` recovers `f`. -/
theorem lift_comp_of (f : M →+ G) : (lift f).comp (of : M →+ _) = f :=
  lift_symm_apply (lift f) ▸ lift.symm_apply_apply f

-- Not `@[simp]`: the simp normal form of `of a` is `AddLocalization.addMonoidOf ⊤ a`, because
-- `AddSubmonoid.LocalizationMap.toAddMonoidHom_apply` is a `simp` lemma and `of` is the
-- `AddMonoidHom` attached to that localization map. The same applies to the other characteristic
-- equations below, which are therefore stated for `rw` rather than for `simp`.
/-- The extension of `f` agrees with `f` on the image of the monoid. -/
theorem lift_apply_of (f : M →+ G) (a : M) : lift f (of a) = f a :=
  DFunLike.congr_fun (lift_comp_of f) a

/-- Two additive maps out of the Grothendieck group agree as soon as they agree on the image of
the monoid. -/
theorem addHom_ext {F₁ F₂ : GrothendieckAddGroup M →+ G}
    (h : ∀ a : M, F₁ (of a) = F₂ (of a)) : F₁ = F₂ :=
  lift.symm.injective (AddMonoidHom.ext h)

/-- Every element of the Grothendieck group is a difference of two elements of the monoid. -/
theorem exists_eq_sub_of (x : GrothendieckAddGroup M) : ∃ a b : M, x = of a - of b := by
  obtain ⟨⟨a, s⟩, h⟩ := (AddLocalization.addMonoidOf (⊤ : AddSubmonoid M)).surj x
  exact ⟨a, s, eq_sub_of_add_eq h⟩

/-- The universal property of the Grothendieck group, upgraded to an isomorphism of the additive
groups of homomorphisms. -/
noncomputable def liftAddEquiv : (M →+ G) ≃+ (GrothendieckAddGroup M →+ G) :=
  (AddEquiv.mk' lift.symm fun F₁ F₂ => AddMonoidHom.add_comp F₁ F₂ of).symm

@[simp]
theorem coe_liftAddEquiv : ⇑(liftAddEquiv : (M →+ G) ≃+ _) = lift := (rfl)

/-! ### The multiplication -/

section NonUnitalNonAssoc

variable {S : Type*} [NonUnitalNonAssocSemiring S]

/-- Multiplication on the Grothendieck ring of a semiring: the universal property extends
`fun a b => of (a * b)` first in `b`, then in `a`. -/
noncomputable instance instMul : Mul (GrothendieckAddGroup S) :=
  ⟨fun x y => lift (liftAddEquiv.toAddMonoidHom.comp (AddMonoidHom.mul.compr₂ of)) x y⟩

/-- The canonical map into the Grothendieck ring is multiplicative. -/
theorem of_mul_of (a b : S) : (of a : GrothendieckAddGroup S) * of b = of (a * b) :=
  -- By the definition of `instMul`, `of a * of b` is the double extension evaluated at `of a`
  -- and `of b`; `lift_apply_of` evaluates the outer and then the inner extension.
  (DFunLike.congr_fun (lift_apply_of _ a) (of b)).trans (lift_apply_of _ b)

/-- The Grothendieck group of a non-unital non-associative semiring is a non-unital
non-associative ring for the induced multiplication. -/
noncomputable instance instNonUnitalNonAssocRing :
    NonUnitalNonAssocRing (GrothendieckAddGroup S) :=
  -- The multiplication is, by definition, evaluation of this biadditive map.
  let mulHom : GrothendieckAddGroup S →+ GrothendieckAddGroup S →+ GrothendieckAddGroup S :=
    lift (liftAddEquiv.toAddMonoidHom.comp (AddMonoidHom.mul.compr₂ of))
  { left_distrib x := map_add (mulHom x)
    right_distrib x y := DFunLike.congr_fun (map_add mulHom x y)
    zero_mul := DFunLike.congr_fun (map_zero mulHom)
    mul_zero x := map_zero (mulHom x) }

end NonUnitalNonAssoc

section NonUnitalSemiring

variable {S : Type*} [NonUnitalSemiring S]

/-- The Grothendieck group of a non-unital semiring is a non-unital ring. -/
noncomputable instance instNonUnitalRing : NonUnitalRing (GrothendieckAddGroup S) where
  __ := (inferInstance : NonUnitalNonAssocRing (GrothendieckAddGroup S))
  mul_assoc x y z := by
    obtain ⟨a, b, rfl⟩ := exists_eq_sub_of x
    obtain ⟨c, d, rfl⟩ := exists_eq_sub_of y
    obtain ⟨e, f, rfl⟩ := exists_eq_sub_of z
    simp only [sub_mul, mul_sub, of_mul_of, mul_assoc]

end NonUnitalSemiring

section NonAssocSemiring

variable {S : Type*} [NonAssocSemiring S]

/-- The unit of the Grothendieck ring of a semiring. -/
noncomputable instance instOne : One (GrothendieckAddGroup S) := ⟨of 1⟩

/-- The unit of the Grothendieck ring is the image of the unit of the semiring. -/
theorem one_def : (1 : GrothendieckAddGroup S) = of 1 := (rfl)

/-- The Grothendieck group of a possibly nonassociative semiring is a possibly nonassociative
ring. -/
noncomputable instance instNonAssocRing : NonAssocRing (GrothendieckAddGroup S) where
  __ := (inferInstance : NonUnitalNonAssocRing (GrothendieckAddGroup S))
  one_mul x := by
    obtain ⟨a, b, rfl⟩ := exists_eq_sub_of x
    rw [one_def, mul_sub, of_mul_of, of_mul_of, one_mul, one_mul]
  mul_one x := by
    obtain ⟨a, b, rfl⟩ := exists_eq_sub_of x
    rw [one_def, sub_mul, of_mul_of, of_mul_of, mul_one, mul_one]

end NonAssocSemiring

section Semiring

variable {S : Type*} [Semiring S]

/-- **The Grothendieck ring**: the group completion of the additive monoid underlying a semiring
is a ring, with the multiplication induced by that of the semiring. -/
noncomputable instance instRing : Ring (GrothendieckAddGroup S) where
  __ := (inferInstance : NonUnitalRing (GrothendieckAddGroup S))
  __ := (inferInstance : NonAssocRing (GrothendieckAddGroup S))

end Semiring

section NonAssocSemiring

variable {S : Type*} [NonAssocSemiring S]

/-- The canonical map from a semiring into its Grothendieck ring. -/
noncomputable def ofRingHom : S →+* GrothendieckAddGroup S where
  __ := (of : S →+ GrothendieckAddGroup S)
  map_one' := (one_def).symm
  map_mul' a b := (of_mul_of a b).symm

@[simp]
theorem coe_ofRingHom : ⇑(ofRingHom : S →+* GrothendieckAddGroup S) = of := (rfl)

/-- The canonical ring map agrees with the canonical additive map on elements. -/
theorem ofRingHom_apply (a : S) : ofRingHom a = of a := (rfl)

/-! ### The universal property, in ring form -/

variable {R : Type*} [NonAssocRing R]

/-- Two ring homomorphisms out of the Grothendieck ring agree as soon as they agree on the image
of the semiring. -/
theorem ringHom_ext {F₁ F₂ : GrothendieckAddGroup S →+* R}
    (h : ∀ a : S, F₁ (of a) = F₂ (of a)) : F₁ = F₂ := by
  refine RingHom.ext fun x => ?_
  obtain ⟨a, b, rfl⟩ := exists_eq_sub_of x
  rw [map_sub, map_sub, h, h]

/-- **The universal property of the Grothendieck ring**: a semiring homomorphism from `S` to a
ring extends uniquely to the Grothendieck ring of `S`. -/
noncomputable def liftRingHom : (S →+* R) ≃ (GrothendieckAddGroup S →+* R) where
  toFun f :=
    { __ := lift f.toAddMonoidHom
      map_one' := by rw [one_def]; exact (lift_apply_of _ _).trans f.map_one
      map_mul' x y := by
        obtain ⟨a, b, rfl⟩ := exists_eq_sub_of x
        obtain ⟨c, d, rfl⟩ := exists_eq_sub_of y
        simp only [sub_mul, mul_sub, of_mul_of, AddMonoidHom.toFun_eq_coe, map_sub,
          lift_apply_of, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass, map_mul] }
  invFun F := F.comp ofRingHom
  left_inv f := RingHom.ext fun a => lift_apply_of f.toAddMonoidHom a
  right_inv F := ringHom_ext fun a => lift_apply_of (F.comp ofRingHom).toAddMonoidHom a

/-- The ring-homomorphism extension evaluates to the original semiring homomorphism on each
generator. -/
theorem liftRingHom_apply_of (f : S →+* R) (a : S) : liftRingHom f (of a) = f a :=
  lift_apply_of f.toAddMonoidHom a

/-- The inverse universal-property equivalence restricts a ring homomorphism along
`ofRingHom`. -/
@[simp]
theorem liftRingHom_symm_apply (F : GrothendieckAddGroup S →+* R) :
    liftRingHom.symm F = F.comp ofRingHom := (rfl)

end NonAssocSemiring

/-- The Grothendieck ring of a commutative semiring is commutative. -/
noncomputable instance instCommRing {S : Type*} [CommSemiring S] :
    CommRing (GrothendieckAddGroup S) where
  __ := (inferInstance : Ring (GrothendieckAddGroup S))
  mul_comm x y := by
    obtain ⟨a, b, rfl⟩ := exists_eq_sub_of x
    obtain ⟨c, d, rfl⟩ := exists_eq_sub_of y
    simp only [sub_mul, mul_sub, of_mul_of, mul_comm]
    abel

end Algebra.GrothendieckAddGroup
