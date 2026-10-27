/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Dynamic.ClosedImmersion.Ideals
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Smooth
public import TauCeti.Algebra.AlgebraicGroup.Dynamic.Unipotent.Connected

/-!
# Dynamic unipotent subgroups of closed subgroups

Let `λ : 𝔾ₘ → G` be a cocharacter of an affine group `G = Spec H`, and let `Z ⊆ G` be a closed
subgroup, cut out by a Hopf ideal `I`, through which `λ` factors. In coordinates, `λ` kills `I` and
so descends to a cocharacter `λ_Z` of `Z` on `H ⧸ I`. The dynamic unipotent subgroup `U_Z(λ_Z)` of
`Z` is then the scheme-theoretic intersection `Z ∩ U_G(λ)`, cut out by `I ⊔ J` where `J` cuts out
`U_G(λ)`. This file records that identification as an isomorphism of coordinate Hopf algebras.

Properties of dynamic unipotent subgroups therefore pass to such intersections. If `Z` is smooth of
finite type over a Noetherian ring then `Z ∩ U_G(λ)` is smooth, whatever `G` is. Over a field,
`Z ∩ U_G(λ)` is geometrically connected, with no smoothness assumption on `Z` or `G`. A typical
`Z` is the centralizer of a subgroup of a torus containing the image of `λ`.

## Main declarations

* `BialgHom.comapOfSurjective_unipotentDefiningHopfIdeal_liftBialgHom`: the inverse image of
  `U_Z(λ_Z)` in `G` is `Z ∩ U_G(λ)`.
* `BialgHom.quotientSupUnipotentDefiningHopfIdealIso`: the corresponding isomorphism of
  coordinate Hopf algebras.
* `BialgHom.smoothCommHopfAlgProperty_quotient_sup_unipotentDefiningHopfIdeal`: `Z ∩ U_G(λ)` is
  smooth when `Z` is.
* `BialgHom.geometricallyConnectedCommHopfAlgProperty_quotient_sup_unipotentDefiningHopfIdeal`:
  over a field, `Z ∩ U_G(λ)` is geometrically connected.

## References

* B. Conrad, O. Gabber, G. Prasad, *Pseudo-reductive Groups*, §2.1.
* J. S. Milne, *Algebraic Groups* (2017), Chapter 13.
-/

public section

open CategoryTheory TauCeti

namespace BialgHom

universe u v

section CommRing

variable {R : Type u} [CommRing R] {H : CommHopfAlgCat.{v} R}

/-- **The dynamic unipotent subgroup of a closed subgroup `Z` through which `λ` factors is
`Z ∩ U_G(λ)`.** The inverse image in `G` of the dynamic unipotent subgroup of the descended
cocharacter of `Z = Spec (H ⧸ I)` is cut out by `I ⊔ J`, where `J` cuts out `U_G(λ)`. -/
theorem comapOfSurjective_unipotentDefiningHopfIdeal_liftBialgHom (I : HopfIdeal R H)
    (l : H →ₐc[R] LaurentPolynomial R) (hI : I.toIdeal ≤ RingHom.ker l.toAlgHom.toRingHom) :
    (Bialgebra.Quotient.liftBialgHom I.toIdeal l hI).unipotentDefiningHopfIdeal.comapOfSurjective
        (Bialgebra.Quotient.mkBialgHom I.toIdeal)
        (Bialgebra.Quotient.mkBialgHom_surjective I.toIdeal) =
      I ⊔ l.unipotentDefiningHopfIdeal := by
  rw [comapOfSurjective_unipotentDefiningHopfIdeal,
    Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom, HopfIdeal.kerOfSurjective_mkBialgHom,
    sup_comm]

/-- **`Z ∩ U_G(λ)` is the dynamic unipotent subgroup of `Z`**, as an isomorphism between the
coordinate Hopf algebra of `Z ∩ U_G(λ)` and that of the dynamic unipotent subgroup of the
cocharacter of `Z = Spec (H ⧸ I)` descended from `λ`. -/
noncomputable def quotientSupUnipotentDefiningHopfIdealIso (I : HopfIdeal R H)
    (l : H →ₐc[R] LaurentPolynomial R) (hI : I.toIdeal ≤ RingHom.ker l.toAlgHom.toRingHom) :
    CommHopfAlgCat.quotient H (I ⊔ l.unipotentDefiningHopfIdeal) ≅
      CommHopfAlgCat.quotient (CommHopfAlgCat.quotient H I)
        (Bialgebra.Quotient.liftBialgHom I.toIdeal l hI).unipotentDefiningHopfIdeal :=
  eqToIso (congrArg (CommHopfAlgCat.quotient H)
      (comapOfSurjective_unipotentDefiningHopfIdeal_liftBialgHom I l hI).symm) ≪≫
    CommHopfAlgCat.Hom.quotientIsoOfSurjective (CommHopfAlgCat.mkQuotient H I)
      (CommHopfAlgCat.mkQuotient_surjective H I) _

/-- The identification of `Z ∩ U_G(λ)` with the dynamic unipotent subgroup of `Z` is compatible
with the restriction maps from `G`: restricting to `Z ∩ U_G(λ)` is restricting to `Z` and then to
its dynamic unipotent subgroup. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_quotientSupUnipotentDefiningHopfIdealIso_hom (I : HopfIdeal R H)
    (l : H →ₐc[R] LaurentPolynomial R) (hI : I.toIdeal ≤ RingHom.ker l.toAlgHom.toRingHom) :
    CommHopfAlgCat.mkQuotient H (I ⊔ l.unipotentDefiningHopfIdeal) ≫
        (quotientSupUnipotentDefiningHopfIdealIso I l hI).hom =
      CommHopfAlgCat.mkQuotient H I ≫ CommHopfAlgCat.mkQuotient (CommHopfAlgCat.quotient H I)
        (Bialgebra.Quotient.liftBialgHom I.toIdeal l hI).unipotentDefiningHopfIdeal := by
  rw [quotientSupUnipotentDefiningHopfIdealIso, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
    CommHopfAlgCat.mkQuotient_comp_eqToHom
      (comapOfSurjective_unipotentDefiningHopfIdeal_liftBialgHom I l hI)]
  exact CommHopfAlgCat.Hom.mkQuotient_comp_quotientIsoOfSurjective_hom
    (CommHopfAlgCat.mkQuotient H I) (CommHopfAlgCat.mkQuotient_surjective H I)
    (Bialgebra.Quotient.liftBialgHom I.toIdeal l hI).unipotentDefiningHopfIdeal

/-- The inverse identification of the dynamic unipotent subgroup of `Z` with `Z ∩ U_G(λ)` is
compatible with the restriction maps from `G`. -/
@[reassoc (attr := simp)]
theorem mkQuotient_comp_mkQuotient_comp_quotientSupUnipotentDefiningHopfIdealIso_inv
    (I : HopfIdeal R H) (l : H →ₐc[R] LaurentPolynomial R)
    (hI : I.toIdeal ≤ RingHom.ker l.toAlgHom.toRingHom) :
    CommHopfAlgCat.mkQuotient H I ≫ CommHopfAlgCat.mkQuotient (CommHopfAlgCat.quotient H I)
        (Bialgebra.Quotient.liftBialgHom I.toIdeal l hI).unipotentDefiningHopfIdeal ≫
          (quotientSupUnipotentDefiningHopfIdealIso I l hI).inv =
      CommHopfAlgCat.mkQuotient H (I ⊔ l.unipotentDefiningHopfIdeal) := by
  rw [← Category.assoc, ← mkQuotient_comp_quotientSupUnipotentDefiningHopfIdealIso_hom,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- **`Z ∩ U_G(λ)` is smooth when `Z` is.** If `λ` factors through a closed subgroup `Z` which is
smooth of finite type over a Noetherian ring, then so is `Z ∩ U_G(λ)`. No smoothness of `G` is
needed. -/
theorem smoothCommHopfAlgProperty_quotient_sup_unipotentDefiningHopfIdeal [IsNoetherianRing R]
    [Algebra.FiniteType R H] {I : HopfIdeal R H} {l : H →ₐc[R] LaurentPolynomial R}
    (hI : I.toIdeal ≤ RingHom.ker l.toAlgHom.toRingHom)
    (hZ : smoothCommHopfAlgProperty R (CommHopfAlgCat.quotient H I)) :
    smoothCommHopfAlgProperty R (CommHopfAlgCat.quotient H (I ⊔ l.unipotentDefiningHopfIdeal)) := by
  have : Algebra.Smooth R (H ⧸ I.toIdeal) := (smoothCommHopfAlgProperty_iff _).mp hZ
  exact (smoothCommHopfAlgProperty R).prop_of_iso
    (quotientSupUnipotentDefiningHopfIdealIso I l hI).symm
    (smoothCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal
      (H := FiniteTypeCommHopfAlgCat.of R (H ⧸ I.toIdeal)) _)

end CommRing

/-- **`Z ∩ U_G(λ)` is geometrically connected.** Over a field, the intersection of the dynamic
unipotent subgroup of a finite-type affine group with a closed subgroup through which the
cocharacter factors is geometrically connected. No smoothness or reducedness is needed. -/
theorem geometricallyConnectedCommHopfAlgProperty_quotient_sup_unipotentDefiningHopfIdeal
    {k : Type u} [Field k] {H : CommHopfAlgCat.{u} k} [Algebra.FiniteType k H]
    {I : HopfIdeal k H} {l : H →ₐc[k] LaurentPolynomial k}
    (hI : I.toIdeal ≤ RingHom.ker l.toAlgHom.toRingHom) :
    geometricallyConnectedCommHopfAlgProperty k
      (CommHopfAlgCat.quotient H (I ⊔ l.unipotentDefiningHopfIdeal)) :=
  (geometricallyConnectedCommHopfAlgProperty k).prop_of_iso
    (quotientSupUnipotentDefiningHopfIdealIso I l hI).symm
    (Cocharacter.geometricallyConnectedCommHopfAlgProperty_quotient_unipotentDefiningHopfIdeal
      (H := H ⧸ I.toIdeal) _)

end BialgHom
