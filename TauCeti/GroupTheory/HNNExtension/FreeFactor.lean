/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.Basic
public import Mathlib.GroupTheory.HNNExtension
public import TauCeti.Algebra.Group.Subgroup.Ker

/-!
# Conjugating a free factor into the other factor

Let `ι : Q →* G` be an injective homomorphism of groups. The HNN extension
`⟨G ∗ Q, t | t q t⁻¹ = ι q, q ∈ Q⟩` of the free product `G ∗ Q`, along the isomorphism from the
factor `Q` onto its copy `ι(Q)` in `G` (`MonoidHom.rangeEquivRange`), is the free product
`G ∗ ⟨z⟩` of `G` with an infinite cyclic group. The relations express every `q ∈ Q` through `G`
and `t`, as `q = t⁻¹ ι(q) t`, so the factor `Q` is redundant and the stable letter is free over
`G`. The isomorphism is the identity on `G` and sends `t` to `z⁻¹`, hence `q ∈ Q` to
`z ι(q) z⁻¹`.

## Main definitions

* `HNNExtension.equivCoprodFreeGroup hι`: the HNN extension of `G ∗ Q` along the isomorphism
  `inr q ↦ inl (ι q)` is isomorphic to `G ∗ FreeGroup Unit`.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer (1977), Chapter IV, §2
  (HNN extensions).
-/

public section

open Function Monoid.Coprod
open MonoidHom (ker_eq_ker_of_injective rangeEquivRange)

namespace HNNExtension

variable {G Q : Type*} [Group G] [Group Q] {ι : Q →* G} (hι : Injective ι)

/-- The homomorphism from the HNN extension of `G ∗ Q` along `inr q ↦ inl (ι q)` to `G ∗ ⟨z⟩`:
`g ↦ g`, `q ↦ z ι(q) z⁻¹` and `t ↦ z⁻¹`. -/
private noncomputable def toCoprod :
    HNNExtension (G ∗ Q) _ _ (rangeEquivRange inr (inl.comp ι)
      (ker_eq_ker_of_injective inr_injective (inl_injective.comp hι))) →* G ∗ FreeGroup Unit :=
  lift (Monoid.Coprod.lift inl
      ((MulAut.conj (inr (FreeGroup.of ()))).toMonoidHom.comp (inl.comp ι)))
    (inr (FreeGroup.of ()))⁻¹ fun a => by
      obtain ⟨q, rfl⟩ := (inr : Q →* G ∗ Q).rangeRestrict_surjective a
      simp [mul_assoc]

/-- The homomorphism from `G ∗ ⟨z⟩` to the HNN extension of `G ∗ Q` along `inr q ↦ inl (ι q)`:
`g ↦ g` and `z ↦ t⁻¹`. -/
private noncomputable def ofCoprod : G ∗ FreeGroup Unit →*
    HNNExtension (G ∗ Q) _ _ (rangeEquivRange inr (inl.comp ι)
      (ker_eq_ker_of_injective inr_injective (inl_injective.comp hι))) :=
  Monoid.Coprod.lift (of.comp inl) (FreeGroup.lift fun _ => t⁻¹)

/-- In the HNN extension of `G ∗ Q` along `inr q ↦ inl (ι q)`, the factor `Q` is the conjugate
`q = t⁻¹ ι(q) t` of its copy in `G`. -/
private theorem of_inr (q : Q) :
    (of (inr q) : HNNExtension (G ∗ Q) _ _ (rangeEquivRange inr (inl.comp ι)
      (ker_eq_ker_of_injective inr_injective (inl_injective.comp hι)))) =
      t⁻¹ * of (inl (ι q)) * t := by
  simpa using equiv_symm_eq_conj (φ := rangeEquivRange (inr : Q →* G ∗ Q) (inl.comp ι)
    (ker_eq_ker_of_injective inr_injective (inl_injective.comp hι)))
    (((inl : G →* G ∗ Q).comp ι).rangeRestrict q)

/-- **Conjugating a free factor into the other factor.** For an injective `ι : Q →* G`, the HNN
extension of `G ∗ Q` along the isomorphism `inr q ↦ inl (ι q)` from the factor `Q` onto its copy in
`G` is the free product of `G` with the infinite cyclic group `FreeGroup Unit` on `z`: `g ↦ g`,
`t ↦ z⁻¹`, and hence `q ↦ z ι(q) z⁻¹`. -/
noncomputable def equivCoprodFreeGroup :
    HNNExtension (G ∗ Q) _ _ (rangeEquivRange inr (inl.comp ι)
      (ker_eq_ker_of_injective inr_injective (inl_injective.comp hι))) ≃* G ∗ FreeGroup Unit :=
  MonoidHom.toMulEquiv (toCoprod hι) (ofCoprod hι)
    (hom_ext (Monoid.Coprod.hom_ext (by ext; simp [toCoprod, ofCoprod])
      (by ext; simp [toCoprod, ofCoprod, of_inr hι])) (by simp [toCoprod, ofCoprod]))
    (Monoid.Coprod.hom_ext (by ext; simp [toCoprod, ofCoprod])
      (FreeGroup.ext_hom _ _ fun _ => by simp [toCoprod, ofCoprod]))

/-- On the base group `G ∗ Q`, `equivCoprodFreeGroup` is the identity on `G` and conjugation of
`ι(q)` by `z` on `Q`. -/
@[simp]
theorem equivCoprodFreeGroup_comp_of :
    (MonoidHom.ofClass (equivCoprodFreeGroup hι)).comp of =
      Monoid.Coprod.lift inl
        ((MulAut.conj (inr (FreeGroup.of ()))).toMonoidHom.comp (inl.comp ι)) := by
  ext <;> simp [equivCoprodFreeGroup, toCoprod]

@[simp]
theorem equivCoprodFreeGroup_of_inl (g : G) :
    equivCoprodFreeGroup hι (of (inl g)) = inl g := by
  simp [equivCoprodFreeGroup, toCoprod]

@[simp]
theorem equivCoprodFreeGroup_of_inr (q : Q) :
    equivCoprodFreeGroup hι (of (inr q)) =
      inr (FreeGroup.of ()) * inl (ι q) * (inr (FreeGroup.of ()))⁻¹ := by
  simp [equivCoprodFreeGroup, toCoprod]

@[simp]
theorem equivCoprodFreeGroup_t : equivCoprodFreeGroup hι t = (inr (FreeGroup.of ()))⁻¹ := by
  simp [equivCoprodFreeGroup, toCoprod]

@[simp]
theorem equivCoprodFreeGroup_symm_inl (g : G) :
    (equivCoprodFreeGroup hι).symm (inl g) = of (inl g) := by
  simp [equivCoprodFreeGroup, ofCoprod]

/-- On the factor `G`, the inverse of `equivCoprodFreeGroup` is the inclusion of `G` into the base
group `G ∗ Q`. -/
@[simp]
theorem equivCoprodFreeGroup_symm_comp_inl :
    (MonoidHom.ofClass (equivCoprodFreeGroup hι).symm).comp inl = of.comp inl := by
  ext; simp

/-- On the infinite cyclic factor, the inverse of `equivCoprodFreeGroup` sends `z` to `t⁻¹`. -/
@[simp]
theorem equivCoprodFreeGroup_symm_comp_inr :
    (MonoidHom.ofClass (equivCoprodFreeGroup hι).symm).comp inr =
      FreeGroup.lift fun _ => t⁻¹ := by
  ext; simp [equivCoprodFreeGroup, ofCoprod]

@[simp]
theorem equivCoprodFreeGroup_symm_inr_of (x : Unit) :
    (equivCoprodFreeGroup hι).symm (inr (FreeGroup.of x)) = t⁻¹ := by
  simp [equivCoprodFreeGroup, ofCoprod]

end HNNExtension
