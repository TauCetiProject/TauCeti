/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CartanInvolution
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Basic

/-!
# Cartan involutions of stable closed subgroups

Let `θ` be an automorphism of a real affine group scheme `H`, and let `G ⊆ H` be a closed subgroup,
cut out by a Hopf ideal `I` of the coordinate Hopf algebra, which `θ` maps onto itself. Then `θ`
restricts to an automorphism `θ_G` of `G`, given on coordinates by the automorphism of `H ⧸ I`
induced by `θ` (`TauCeti.CommHopfAlgCat.quotientIsoOfComapEq`).

A complex point of `G` is twisted-real for `θ_G` exactly when, viewed as a complex point of `H`, it
is twisted-real for `θ`. So the twisted real points of `θ_G` are those twisted real points of `θ`
that vanish on `I`: a closed subset of the twisted real points of `θ`. Hence if `θ` is a Cartan
involution of `H`, then `θ_G` is a Cartan involution of `G`.

## Main results

* `TauCeti.quotientIsoOfComapEq_hom_comp_self`: over any base ring, the automorphism of `H ⧸ I`
  induced by an involution of `H` is an involution.
* `TauCeti.mem_twistedRealPoints_quotientIsoOfComapEq_iff`: a complex point of `G` is twisted-real
  for `θ_G` exactly when its composite with the quotient map is twisted-real for `θ`.
* `TauCeti.IsCartanInvolution.quotient`: a Cartan involution of `H` restricts to a Cartan
  involution of every closed subgroup that it maps onto itself.

## References

* J. S. Milne, *Introduction to Shimura varieties*, notes, version of 16 September 2017, §1,
  definition (9) and Example 1.17(b), p. 15.
-/

public section

open CategoryTheory

namespace TauCeti

universe v

section General

variable {R : Type*} [CommRing R] {H : _root_.CommHopfAlgCat.{v} R} {θ : H ≅ H}
  {I : HopfIdeal R H}

/-- The automorphism of `H ⧸ I` induced by `θ` sends the class of `x` to the class of `θ x`. -/
theorem quotientIsoOfComapEq_hom_mk
    (hI : I.comapOfSurjective θ.hom.hom (ConcreteCategory.bijective_of_isIso θ.hom).2 = I)
    (x : H) :
    (CommHopfAlgCat.quotientIsoOfComapEq θ I hI).hom.hom (Ideal.Quotient.mk I.toIdeal x) =
      Ideal.Quotient.mk I.toIdeal (θ.hom.hom x) := by
  have h := congr($(CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom θ I hI).hom x)
  simp only [_root_.CommHopfAlgCat.hom_comp, BialgHom.coe_comp, Function.comp_apply] at h
  rwa [CommHopfAlgCat.mkQuotient_apply, CommHopfAlgCat.mkQuotient_apply] at h

/-- The automorphism of `H ⧸ I` induced by an involution of `H` is an involution. -/
theorem quotientIsoOfComapEq_hom_comp_self (hθ : θ.hom ≫ θ.hom = 𝟙 H)
    (hI : I.comapOfSurjective θ.hom.hom (ConcreteCategory.bijective_of_isIso θ.hom).2 = I) :
    (CommHopfAlgCat.quotientIsoOfComapEq θ I hI).hom ≫
        (CommHopfAlgCat.quotientIsoOfComapEq θ I hI).hom =
      𝟙 (_root_.CommHopfAlgCat.quotient H I) := by
  ext : 1
  rw [← Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom, Category.assoc,
    CommHopfAlgCat.mkQuotient_comp_quotientIsoOfComapEq_hom, ← Category.assoc, hθ,
    Category.id_comp, Category.comp_id]

end General

variable {H : _root_.CommHopfAlgCat.{v} ℝ} {θ : H ≅ H} {I : HopfIdeal ℝ H}

/-- **Twisted real points of a stable closed subgroup.** A complex point `p` of the closed subgroup
cut out by a `θ`-stable Hopf ideal `I` is twisted-real for the restriction of `θ` exactly when,
viewed as the complex point `p ∘ (H → H ⧸ I)` of `H`, it is twisted-real for `θ`. -/
theorem mem_twistedRealPoints_quotientIsoOfComapEq_iff
    (hI : I.comapOfSurjective θ.hom.hom (ConcreteCategory.bijective_of_isIso θ.hom).2 = I)
    (p : H ⧸ I.toIdeal →ₐ[ℝ] ℂ) :
    p ∈ twistedRealPoints (CommHopfAlgCat.quotientIsoOfComapEq θ I hI) ↔
      p.comp (Ideal.Quotient.mkₐ ℝ I.toIdeal) ∈ twistedRealPoints θ := by
  rw [mem_twistedRealPoints_iff]
  simp only [mem_twistedRealPoints_iff, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  constructor
  · intro hp x
    rw [hp, quotientIsoOfComapEq_hom_mk]
  · intro hp y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [hp, quotientIsoOfComapEq_hom_mk]

/-- **A Cartan involution restricts to a Cartan involution of every stable closed subgroup.** If
`θ` is a Cartan involution of `H` and the closed subgroup `G` cut out by the Hopf ideal `I` is
mapped onto itself by `θ`, then the automorphism of `G` induced by `θ` is a Cartan involution: its
twisted real points are the twisted real points of `θ` lying in `G`, a closed subset of a compact
set. -/
theorem IsCartanInvolution.quotient (hθ : IsCartanInvolution θ)
    (hI : I.comapOfSurjective θ.hom.hom (ConcreteCategory.bijective_of_isIso θ.hom).2 = I) :
    IsCartanInvolution (CommHopfAlgCat.quotientIsoOfComapEq θ I hI) where
  hom_comp_self := quotientIsoOfComapEq_hom_comp_self hθ.hom_comp_self hI
  isCompact := by
    -- Read a function on `H` as a function on `H ⧸ I` through a section of the quotient map.
    let s := Function.surjInv (Ideal.Quotient.mk_surjective (I := I.toIdeal))
    have hs (y : H ⧸ I.toIdeal) : Ideal.Quotient.mk I.toIdeal (s y) = y :=
      Function.surjInv_eq _ y
    have hcont : Continuous fun (f : H → ℂ) (y : H ⧸ I.toIdeal) ↦ f (s y) :=
      continuous_pi fun y ↦ continuous_apply (s y)
    have hclosed : IsClosed {f : H → ℂ | ∀ x ∈ I.toIdeal, f x = 0} := by
      simp only [Set.ofPred_forall]
      exact isClosed_biInter fun x _ ↦ isClosed_eq (continuous_apply x) continuous_const
    convert (hθ.isCompact.inter_right hclosed).image hcont using 1
    ext g
    simp only [Set.mem_image, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨p, hp, rfl⟩
      refine ⟨p.comp (Ideal.Quotient.mkₐ ℝ I.toIdeal),
        ⟨⟨_, (mem_twistedRealPoints_quotientIsoOfComapEq_iff hI p).mp hp, rfl⟩, fun x hx ↦ ?_⟩,
        ?_⟩
      · simp [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
      · ext y
        simp [hs]
    · rintro ⟨_, ⟨⟨q, hq, rfl⟩, hvan⟩, rfl⟩
      let p : H ⧸ I.toIdeal →ₐ[ℝ] ℂ := Ideal.Quotient.liftₐ I.toIdeal q hvan
      have hpq : p.comp (Ideal.Quotient.mkₐ ℝ I.toIdeal) = q := by
        ext x
        exact Ideal.Quotient.lift_mk I.toIdeal (q : H →+* ℂ) hvan
      refine ⟨p, (mem_twistedRealPoints_quotientIsoOfComapEq_iff hI p).mpr (hpq ▸ hq), ?_⟩
      ext y
      change p y = q (s y)
      rw [← hpq, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, hs]

end TauCeti
