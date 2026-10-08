/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import TauCeti.Algebra.AlgebraicGroup.FiniteType.CommHopfAlgCat
public import TauCeti.Algebra.Bialgebra.Quotient
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic
public import TauCeti.Algebra.HopfAlgebra.HopfIdeal.Map

/-!
# Hopf-ideal quotients of commutative Hopf algebras

This file packages the quotient of a commutative Hopf algebra by a Hopf ideal as an object of
`CommHopfAlgCat`, with its quotient morphism, the induced morphisms out of it, its kernel, the
maps between quotients by nested Hopf ideals, and its transport along surjective ambient
morphisms; the quotient by the zero Hopf ideal is the original Hopf algebra. The Hopf algebra
structure and quotient bialgebra morphism are supplied by Mathlib's quotient instances and
morphisms.

The same quotient of a finite-type commutative Hopf algebra is again an object of
`FiniteTypeCommHopfAlgCat`: finite type descends along the surjective quotient algebra map.

## Main declarations

* `TauCeti.CommHopfAlgCat.quotient`: the quotient object in `CommHopfAlgCat`.
* `TauCeti.CommHopfAlgCat.mkQuotient_surjective`: the quotient morphism is surjective.
* `TauCeti.CommHopfAlgCat.mkQuotient_hom_ext`: morphisms out of a quotient are determined
  after precomposition with the quotient morphism.
* `TauCeti.FiniteTypeCommHopfAlgCat.quotient`: the quotient object in
  `FiniteTypeCommHopfAlgCat`.
* `TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient`: the quotient morphism.
* `TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_hom_ext`: morphisms out of a quotient are
  determined after precomposition with the quotient morphism.
* `TauCeti.FiniteTypeCommHopfAlgCat.mkQuotient_ker`: its kernel characterization.
* `TauCeti.CommHopfAlgCat.liftQuotient`, `TauCeti.CommHopfAlgCat.liftQuotient_unique`: the
  morphism out of a quotient induced by a morphism killing the Hopf ideal, and its uniqueness.
* `TauCeti.FiniteTypeCommHopfAlgCat.liftQuotient`: the induced morphism out of a quotient.
* `TauCeti.CommHopfAlgCat.toIdeal_le_ker_of_mkQuotient_comp`: a morphism factoring through
  the quotient by a Hopf ideal kills that ideal.
* `TauCeti.CommHopfAlgCat.quotientMapOfLe`: the morphism `H ⧸ I ⟶ H ⧸ J` induced by
  `I ≤ J`.
* `TauCeti.CommHopfAlgCat.quotientMapOfLe_surjective`: quotient-to-quotient coordinate maps are
  surjective.
* `TauCeti.CommHopfAlgCat.quotientMapOfLe_comp_liftQuotient_eq`: a quotient-to-quotient
  coordinate map followed by a lift through the larger ideal is identified by its
  precomposition with the quotient morphism.
* `TauCeti.FiniteTypeCommHopfAlgCat.quotientMapOfLe_surjective`: the finite-type form of
  quotient-to-quotient surjectivity.
* `TauCeti.CommHopfAlgCat.kerOfSurjective_quotientMapOfLe`: over a commutative ring, the
  Hopf ideal `J/I` is the surjective kernel of the induced quotient map.
* `TauCeti.CommHopfAlgCat.ker_quotientMapOfLe`: over a field, the Hopf ideal `J/I` is the
  kernel of the induced quotient map.
* `TauCeti.CommHopfAlgCat.quotientBotIso`: quotienting by the zero Hopf ideal does not
  change a commutative Hopf algebra.
* `TauCeti.CommHopfAlgCat.quotientIsoOfSurjective`: a surjective ambient morphism identifies
  the source quotient by an inverse-image Hopf ideal with the target quotient.
* `TauCeti.CommHopfAlgCat.quotientIsoOfIso`: the specialization to an ambient isomorphism.
* `TauCeti.CommHopfAlgCat.quotientKerOfSurjectiveIso`: the quotient by the kernel of a surjective
  morphism is its target.
* `TauCeti.CommHopfAlgCat.quotientIsoOfKerOfSurjectiveEq`: the quotient by a Hopf ideal equal to
  the kernel of a surjective morphism is its target.
* `TauCeti.CommHopfAlgCat.quotientIsoOfComapEq`: an ambient isomorphism pulling one Hopf ideal
  back to another induces an isomorphism of the quotients.
* `TauCeti.HopfIdeal.comapOfSurjective_eq_of_hom_le_of_inv_le`: two inverse containments under an
  ambient automorphism imply invariance of a Hopf ideal.
* `TauCeti.FiniteTypeCommHopfAlgCat.quotientIsoOfIso`: an ambient isomorphism induces an
  isomorphism between the corresponding finite-type Hopf-ideal quotients.
* `TauCeti.FiniteTypeCommHopfAlgCat.minimal_quotientProperty_comapOfIso`: a minimal Hopf ideal
  among those whose quotient has an isomorphism-closed property pulls back to a minimal one along
  an ambient isomorphism.
* `TauCeti.FiniteTypeCommHopfAlgCat.quotientBotIso`: quotienting by the zero Hopf ideal does
  not change a finite-type commutative Hopf algebra.

## References

The quotient Hopf algebra construction is Mathlib's
(`Mathlib.RingTheory.HopfAlgebra.Quotient`), applied through the instances of
`TauCeti.Algebra.HopfAlgebra.HopfIdeal.Basic`; see Sweedler, *Hopf Algebras*, Chapter 4, and
Waterhouse, *Introduction to Affine Group Schemes*, §16. The finite-type descent is Mathlib's
`Algebra.FiniteType.quotient`.
-/

public section

namespace TauCeti

universe u v

namespace CommHopfAlgCat

open CategoryTheory
open _root_.CommHopfAlgCat

variable {R : Type u} [CommRing R]

/-- The quotient of a commutative Hopf algebra by a Hopf ideal, as a bundled commutative
Hopf algebra. -/
noncomputable abbrev quotient (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    _root_.CommHopfAlgCat.{v} R :=
  _root_.CommHopfAlgCat.of R (H ⧸ I.toIdeal)

/-- The quotient morphism `H ⟶ H ⧸ I` in `CommHopfAlgCat`. -/
noncomputable abbrev mkQuotient (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    H ⟶ quotient H I :=
  _root_.CommHopfAlgCat.ofHom (Bialgebra.Quotient.mkBialgHom I.toIdeal)

/-- The quotient morphism has the expected underlying bialgebra morphism. -/
lemma hom_mkQuotient (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    (mkQuotient H I).hom = Bialgebra.Quotient.mkBialgHom I.toIdeal :=
  _root_.CommHopfAlgCat.hom_ofHom _

/-- The quotient morphism sends an element to its quotient class. -/
lemma mkQuotient_apply (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) (h : H) :
    (mkQuotient H I).hom h = Ideal.Quotient.mkₐ R I.toIdeal h := by
  rw [hom_mkQuotient, Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.mkₐ_eq_mk]

/-- The linear map underlying the quotient morphism is the ideal quotient map. -/
lemma mkQuotient_toLinearMap (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    (mkQuotient H I).hom.toLinearMap = (Ideal.Quotient.mkₐ R I.toIdeal).toLinearMap := by
  ext h
  exact mkQuotient_apply H I h

/-- The kernel of the quotient morphism is the Hopf ideal being quotiented by. -/
lemma mkQuotient_ker (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    RingHom.ker (mkQuotient H I).hom.toAlgHom.toRingHom = I.toIdeal := by
  rw [hom_mkQuotient]
  exact Ideal.Quotient.mkₐ_ker (R₁ := R) I.toIdeal

/-- An element maps to zero in the quotient exactly when it belongs to the Hopf ideal. -/
lemma mkQuotient_eq_zero_iff (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) (h : H) :
    (mkQuotient H I).hom h = 0 ↔ h ∈ I.toIdeal := by
  rw [mkQuotient_apply]
  exact Ideal.Quotient.eq_zero_iff_mem

/-- The quotient morphism is surjective. -/
lemma mkQuotient_surjective (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    Function.Surjective ⇑(mkQuotient H I).hom :=
  Ideal.Quotient.mkₐ_surjective R I.toIdeal

/-- A Hopf-algebra quotient morphism is an epimorphism. -/
instance mkQuotient_epi {H : _root_.CommHopfAlgCat.{v} R} {I : HopfIdeal R H} :
    Epi (mkQuotient H I) :=
  ConcreteCategory.epi_of_surjective _ (mkQuotient_surjective H I)

/-- Morphisms out of a Hopf-algebra quotient are determined by their composites with the
quotient morphism. -/
@[ext]
theorem mkQuotient_hom_ext {H X : _root_.CommHopfAlgCat.{v} R}
    {I : HopfIdeal R H} {f g : quotient H I ⟶ X}
    (h : mkQuotient H I ≫ f = mkQuotient H I ≫ g) : f = g :=
  (cancel_epi (mkQuotient H I)).mp h

variable {H K : _root_.CommHopfAlgCat.{v} R}

/-- A morphism of commutative Hopf algebras out of `H` which kills a Hopf ideal factors
through the quotient object. -/
noncomputable abbrev liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) : quotient H I ⟶ K :=
  _root_.CommHopfAlgCat.ofHom (Bialgebra.Quotient.liftBialgHom I.toIdeal f.hom hf)

/-- The quotient lift has the expected underlying bialgebra morphism. -/
lemma hom_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) :
    (liftQuotient I f hf).hom = Bialgebra.Quotient.liftBialgHom I.toIdeal f.hom hf :=
  _root_.CommHopfAlgCat.hom_ofHom _

/-- The quotient lift evaluates on quotient classes as the original morphism. -/
lemma liftQuotient_mk (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) (h : H) :
    (liftQuotient I f hf).hom (Ideal.Quotient.mkₐ R I.toIdeal h) =
      f.hom h :=
  Bialgebra.Quotient.liftBialgHom_mk I.toIdeal f.hom hf h

/-- The quotient lift composed with the quotient morphism is the original morphism. -/
@[simp]
lemma mkQuotient_comp_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) :
    mkQuotient H I ≫ liftQuotient I f hf = f := by
  ext h
  exact BialgHom.congr_fun
    (Bialgebra.Quotient.liftBialgHom_comp_mkBialgHom I.toIdeal f.hom hf) h

/-- A morphism out of the quotient object is determined by its precomposition with the
quotient morphism. -/
lemma liftQuotient_unique (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) (g : quotient H I ⟶ K)
    (hg : mkQuotient H I ≫ g = f) : g = liftQuotient I f hf := by
  apply mkQuotient_hom_ext
  rw [hg, mkQuotient_comp_liftQuotient]

/-- A surjective morphism remains surjective after factoring through a Hopf-ideal quotient. -/
theorem liftQuotient_surjective_of_surjective (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom)
    (hsurj : Function.Surjective f.hom) :
    Function.Surjective (liftQuotient I f hf).hom := by
  intro y
  obtain ⟨x, rfl⟩ := hsurj y
  exact ⟨Ideal.Quotient.mkₐ R I.toIdeal x, liftQuotient_mk I f hf x⟩

/-- Auxiliary quotient isomorphism when the source ideal is the kernel of the composite
with the target quotient morphism. -/
private noncomputable def quotientIsoOfSurjectiveAux (f : H ⟶ K)
    (hf : Function.Surjective f.hom) (I : HopfIdeal R K) (J : HopfIdeal R H)
    (hJ : J = HopfIdeal.kerOfSurjective
      ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f.hom)
      ((Ideal.Quotient.mkₐ_surjective R I.toIdeal).comp hf)) :
    quotient H J ≅ quotient K I :=
  _root_.CommHopfAlgCat.isoMk <| hJ.symm ▸
    HopfIdeal.kerLiftBialgEquiv
      ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f.hom)
      ((Ideal.Quotient.mkₐ_surjective R I.toIdeal).comp hf)

private lemma quotientIsoOfSurjectiveAux_hom_mk (f : H ⟶ K)
    (hf : Function.Surjective f.hom) (I : HopfIdeal R K) (J : HopfIdeal R H)
    (hJ : J = HopfIdeal.kerOfSurjective
      ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f.hom)
      ((Ideal.Quotient.mkₐ_surjective R I.toIdeal).comp hf)) (x : H) :
    (quotientIsoOfSurjectiveAux f hf I J hJ).hom.hom
        (Ideal.Quotient.mk J.toIdeal x) =
      Ideal.Quotient.mkₐ R I.toIdeal (f.hom x) := by
  subst J
  rw [quotientIsoOfSurjectiveAux]
  exact HopfIdeal.kerLiftBialgEquiv_apply
    ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f.hom)
    ((Ideal.Quotient.mkₐ_surjective R I.toIdeal).comp hf) _ |>.trans <|
      HopfIdeal.kerLiftBialgHom_mk
        ((Bialgebra.Quotient.mkBialgHom I.toIdeal).comp f.hom)
        ((Ideal.Quotient.mkₐ_surjective R I.toIdeal).comp hf) x

/-- A surjective morphism of commutative Hopf algebras identifies the quotient by the
inverse-image Hopf ideal with the corresponding quotient of the target. -/
noncomputable def quotientIsoOfSurjective (f : H ⟶ K) (hf : Function.Surjective f.hom)
    (I : HopfIdeal R K) : quotient H (I.comapOfSurjective f.hom hf) ≅ quotient K I :=
  quotientIsoOfSurjectiveAux f hf I (I.comapOfSurjective f.hom hf)
    (HopfIdeal.comapOfSurjective_eq_kerOfSurjective I f.hom hf)

/-- The forward quotient isomorphism induced by a surjective morphism commutes with the
quotient morphisms. -/
@[simp]
lemma mkQuotient_comp_quotientIsoOfSurjective_hom (f : H ⟶ K)
    (hf : Function.Surjective f.hom) (I : HopfIdeal R K) :
    mkQuotient H (I.comapOfSurjective f.hom hf) ≫ (quotientIsoOfSurjective f hf I).hom =
      f ≫ mkQuotient K I := by
  ext x
  rw [_root_.CommHopfAlgCat.comp_apply, _root_.CommHopfAlgCat.comp_apply,
    mkQuotient_apply, mkQuotient_apply, quotientIsoOfSurjective]
  exact quotientIsoOfSurjectiveAux_hom_mk f hf I _ _ x

/-- The forward quotient isomorphism induced by a surjective morphism evaluates on quotient
classes by applying the morphism before taking the target quotient. -/
@[simp]
lemma quotientIsoOfSurjective_hom_mk (f : H ⟶ K) (hf : Function.Surjective f.hom)
    (I : HopfIdeal R K) (x : H) :
    (quotientIsoOfSurjective f hf I).hom.hom
        (Ideal.Quotient.mk (I.comapOfSurjective f.hom hf).toIdeal x) =
      Ideal.Quotient.mkₐ R I.toIdeal (f.hom x) := by
  rw [quotientIsoOfSurjective]
  exact quotientIsoOfSurjectiveAux_hom_mk f hf I _ _ x

/-- Transporting the quotient object along an equality of Hopf ideals transports its quotient
morphism. This is the identity that lets an automorphism preserving a Hopf ideal be compared with
the isomorphism it induces on the quotient. -/
theorem mkQuotient_comp_eqToHom {I J : HopfIdeal R H} (hIJ : I = J) :
    mkQuotient H J ≫ eqToHom (congrArg (quotient H) hIJ.symm) = mkQuotient H I := by
  subst J
  rfl

/-- An isomorphism of commutative Hopf algebras induces an isomorphism from the quotient by
the inverse-image Hopf ideal to the corresponding quotient of the target. -/
noncomputable def quotientIsoOfIso (e : H ≅ K) (I : HopfIdeal R K) :
    quotient H (I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2) ≅
      quotient K I :=
  quotientIsoOfSurjective e.hom (ConcreteCategory.bijective_of_isIso e.hom).2 I

/-- The forward map of the quotient isomorphism commutes with the quotient morphisms. -/
@[simp]
lemma mkQuotient_comp_quotientIsoOfIso_hom (e : H ≅ K) (I : HopfIdeal R K) :
    mkQuotient H (I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2) ≫
        (quotientIsoOfIso e I).hom =
      e.hom ≫ mkQuotient K I :=
  mkQuotient_comp_quotientIsoOfSurjective_hom e.hom
    (ConcreteCategory.bijective_of_isIso e.hom).2 I

/-- The inverse map of the quotient isomorphism commutes with the quotient morphisms. -/
@[simp]
lemma mkQuotient_comp_quotientIsoOfIso_inv (e : H ≅ K) (I : HopfIdeal R K) :
    mkQuotient K I ≫ (quotientIsoOfIso e I).inv =
      e.inv ≫ mkQuotient H
        (I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  rw [← cancel_mono (quotientIsoOfIso e I).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id,
    mkQuotient_comp_quotientIsoOfIso_hom, Iso.inv_hom_id_assoc]

end CommHopfAlgCat

namespace HopfIdeal

open CategoryTheory

variable {R : Type u} [CommRing R]
variable {H : _root_.CommHopfAlgCat.{v} R}

/-- A Hopf ideal is invariant under an ambient automorphism if both the automorphism and its
inverse pull it into itself. -/
theorem comapOfSurjective_eq_of_hom_le_of_inv_le (e : H ≅ H) (I : HopfIdeal R H)
    (hhom : I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2 ≤ I)
    (hinv : I.comapOfSurjective e.inv.hom (ConcreteCategory.bijective_of_isIso e.inv).2 ≤ I) :
    I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2 = I := by
  apply le_antisymm hhom
  intro x hx
  rw [mem_comapOfSurjective]
  apply hinv
  rw [mem_comapOfSurjective]
  have hcancel := congrArg (fun f : H ⟶ H => f.hom x) e.hom_inv_id
  rw [_root_.CommHopfAlgCat.comp_apply] at hcancel
  simpa only [_root_.CommHopfAlgCat.id_apply] using hcancel.symm ▸ hx

end HopfIdeal

namespace CommHopfAlgCat

open CategoryTheory
open _root_.CommHopfAlgCat

variable {R : Type u} [CommRing R]
variable {H K : _root_.CommHopfAlgCat.{v} R}

/-- An isomorphism `e : H ≅ K` that pulls the Hopf ideal `I` of `K` back to the Hopf ideal `J`
of `H` induces an isomorphism of the quotients. For `K = H` and `J = I` this is the automorphism
of the quotient induced by an ideal-preserving automorphism. -/
noncomputable def quotientIsoOfComapEq (e : H ≅ K) (I : HopfIdeal R K) {J : HopfIdeal R H}
    (hI : I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2 = J) :
    quotient H J ≅ quotient K I :=
  eqToIso (congrArg (quotient H) hI.symm) ≪≫ quotientIsoOfIso e I

/-- The quotient isomorphism induced by an ideal-matching ambient isomorphism commutes with the
quotient morphisms. -/
@[simp]
lemma mkQuotient_comp_quotientIsoOfComapEq_hom (e : H ≅ K) (I : HopfIdeal R K)
    {J : HopfIdeal R H}
    (hI : I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2 = J) :
    mkQuotient H J ≫ (quotientIsoOfComapEq e I hI).hom = e.hom ≫ mkQuotient K I := by
  rw [quotientIsoOfComapEq, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
    mkQuotient_comp_eqToHom, mkQuotient_comp_quotientIsoOfIso_hom]
  exact hI

/-- The inverse of the quotient isomorphism induced by an ideal-matching ambient isomorphism
commutes with the quotient morphisms. -/
@[simp]
lemma mkQuotient_comp_quotientIsoOfComapEq_inv (e : H ≅ K) (I : HopfIdeal R K)
    {J : HopfIdeal R H}
    (hI : I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2 = J) :
    mkQuotient K I ≫ (quotientIsoOfComapEq e I hI).inv = e.inv ≫ mkQuotient H J := by
  rw [← cancel_mono (quotientIsoOfComapEq e I hI).hom]
  simp

/-- The forward quotient isomorphism induced by an ambient isomorphism evaluates on quotient
classes by applying the ambient isomorphism before taking the target quotient. -/
@[simp]
lemma quotientIsoOfIso_hom_mk (e : H ≅ K) (I : HopfIdeal R K) (x : H) :
    (quotientIsoOfIso e I).hom.hom
        (Ideal.Quotient.mk
          (I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2).toIdeal x) =
      Ideal.Quotient.mkₐ R I.toIdeal (e.hom.hom x) :=
  quotientIsoOfSurjective_hom_mk e.hom
    (ConcreteCategory.bijective_of_isIso e.hom).2 I x

/-- The inverse quotient isomorphism induced by an ambient isomorphism evaluates on quotient
classes by applying the inverse ambient isomorphism before taking the source quotient. -/
@[simp]
lemma quotientIsoOfIso_inv_mk (e : H ≅ K) (I : HopfIdeal R K) (y : K) :
    (quotientIsoOfIso e I).inv.hom (Ideal.Quotient.mk I.toIdeal y) =
      Ideal.Quotient.mkₐ R
        (I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2).toIdeal
        (e.inv.hom y) := by
  calc
    (quotientIsoOfIso e I).inv.hom (Ideal.Quotient.mkₐ R I.toIdeal y) =
        (mkQuotient K I ≫ (quotientIsoOfIso e I).inv).hom y := by
      rw [_root_.CommHopfAlgCat.comp_apply, mkQuotient_apply]
    _ = (e.inv ≫ mkQuotient H
        (I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2)).hom y := by
      rw [mkQuotient_comp_quotientIsoOfIso_inv]
    _ = Ideal.Quotient.mkₐ R
        (I.comapOfSurjective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom).2).toIdeal
        (e.inv.hom y) := by
      rw [_root_.CommHopfAlgCat.comp_apply, mkQuotient_apply]

/-- Quotienting a commutative Hopf algebra by the zero Hopf ideal gives an isomorphic object
of `CommHopfAlgCat`. -/
noncomputable def quotientBotIso (H : _root_.CommHopfAlgCat.{v} R) :
    quotient H (⊥ : HopfIdeal R H) ≅ H where
  hom := liftQuotient (⊥ : HopfIdeal R H) (𝟙 H) bot_le
  inv := mkQuotient H (⊥ : HopfIdeal R H)
  hom_inv_id := by
    apply _root_.CommHopfAlgCat.hom_ext
    ext q
    obtain ⟨h, rfl⟩ :=
      Ideal.Quotient.mkₐ_surjective R (⊥ : HopfIdeal R H).toIdeal q
    rw [_root_.CommHopfAlgCat.comp_apply,
      liftQuotient_mk (hf := bot_le), mkQuotient_apply]
    rfl
  inv_hom_id := mkQuotient_comp_liftQuotient
    (⊥ : HopfIdeal R H) (𝟙 H) bot_le

/-- The forward map of the quotient-by-zero isomorphism is the lift of the identity. -/
@[simp]
lemma quotientBotIso_hom (H : _root_.CommHopfAlgCat.{v} R) :
    (quotientBotIso H).hom =
      liftQuotient (⊥ : HopfIdeal R H) (𝟙 H) bot_le :=
  by rw [quotientBotIso]

/-- The inverse map of the quotient-by-zero isomorphism is the quotient morphism. -/
@[simp]
lemma quotientBotIso_inv (H : _root_.CommHopfAlgCat.{v} R) :
    (quotientBotIso H).inv = mkQuotient H (⊥ : HopfIdeal R H) :=
  by rw [quotientBotIso]

/-- A surjective morphism of commutative Hopf algebras identifies the quotient by its Hopf-ideal
kernel with its target. -/
noncomputable def quotientKerOfSurjectiveIso (f : H ⟶ K) (hf : Function.Surjective f.hom) :
    quotient H (HopfIdeal.kerOfSurjective f.hom hf) ≅ K :=
  _root_.CommHopfAlgCat.isoMk (HopfIdeal.kerLiftBialgEquiv f.hom hf)

/-- The kernel quotient isomorphism identifies the quotient morphism with the original
surjective morphism. -/
@[reassoc (attr := simp)]
lemma mkQuotient_comp_quotientKerOfSurjectiveIso_hom (f : H ⟶ K)
    (hf : Function.Surjective f.hom) :
    mkQuotient H (HopfIdeal.kerOfSurjective f.hom hf) ≫ (quotientKerOfSurjectiveIso f hf).hom =
      f := by
  ext x
  simp [quotientKerOfSurjectiveIso]

/-- The inverse of the kernel quotient isomorphism identifies the original surjective morphism
with the quotient morphism. -/
@[reassoc (attr := simp)]
lemma comp_quotientKerOfSurjectiveIso_inv (f : H ⟶ K) (hf : Function.Surjective f.hom) :
    f ≫ (quotientKerOfSurjectiveIso f hf).inv =
      mkQuotient H (HopfIdeal.kerOfSurjective f.hom hf) :=
  (Iso.comp_inv_eq _).mpr (mkQuotient_comp_quotientKerOfSurjectiveIso_hom f hf).symm

/-- A surjective morphism of commutative Hopf algebras identifies the quotient by any Hopf ideal
equal to its Hopf-ideal kernel with its target. -/
noncomputable def quotientIsoOfKerOfSurjectiveEq (f : H ⟶ K) (hf : Function.Surjective f.hom)
    {I : HopfIdeal R H} (hI : HopfIdeal.kerOfSurjective f.hom hf = I) : quotient H I ≅ K :=
  eqToIso (congrArg (quotient H) hI.symm) ≪≫ quotientKerOfSurjectiveIso f hf

/-- The identification of a quotient by the kernel of a surjective morphism with its target
identifies the quotient morphism with the original surjective morphism. -/
@[reassoc (attr := simp)]
lemma mkQuotient_comp_quotientIsoOfKerOfSurjectiveEq_hom (f : H ⟶ K)
    (hf : Function.Surjective f.hom) {I : HopfIdeal R H}
    (hI : HopfIdeal.kerOfSurjective f.hom hf = I) :
    mkQuotient H I ≫ (quotientIsoOfKerOfSurjectiveEq f hf hI).hom = f := by
  rw [quotientIsoOfKerOfSurjectiveEq, Iso.trans_hom, eqToIso.hom, ← Category.assoc,
    mkQuotient_comp_eqToHom hI]
  exact mkQuotient_comp_quotientKerOfSurjectiveIso_hom f hf

/-- The inverse identification of a quotient by the kernel of a surjective morphism with its
target identifies the original surjective morphism with the quotient morphism. -/
@[reassoc (attr := simp)]
lemma comp_quotientIsoOfKerOfSurjectiveEq_inv (f : H ⟶ K)
    (hf : Function.Surjective f.hom) {I : HopfIdeal R H}
    (hI : HopfIdeal.kerOfSurjective f.hom hf = I) :
    f ≫ (quotientIsoOfKerOfSurjectiveEq f hf hI).inv = mkQuotient H I :=
  (Iso.comp_inv_eq _).mpr (mkQuotient_comp_quotientIsoOfKerOfSurjectiveEq_hom f hf hI).symm

/-- If `I ≤ J`, then the quotient map by `J` kills every element of `I`. -/
lemma toIdeal_le_ker_mkQuotient_of_le
    (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    I.toIdeal ≤ RingHom.ker (mkQuotient H J).hom.toAlgHom.toRingHom := by
  rw [mkQuotient_ker]
  exact HopfIdeal.toIdeal_le_toIdeal.mpr hIJ

/-- A morphism out of `H` that factors through the quotient by `I` kills `I`. -/
lemma toIdeal_le_ker_of_mkQuotient_comp {I : HopfIdeal R H} {g : quotient H I ⟶ K}
    {f : H ⟶ K} (hg : mkQuotient H I ≫ g = f) :
    I.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom := by
  intro x hx
  have hx0 : (mkQuotient H I).hom x = 0 := (mkQuotient_eq_zero_iff H I x).mpr hx
  rw [RingHom.mem_ker, ← hg]
  -- The ring-hom coercion of a composite is definitionally the composite of the underlying
  -- maps; no lemma states this for the whole `hom.toAlgHom.toRingHom` coercion chain.
  change g.hom ((mkQuotient H I).hom x) = 0
  rw [hx0, map_zero]

/-- The coordinate morphism `H ⧸ I ⟶ H ⧸ J` induced by an inclusion `I ≤ J` of Hopf
ideals.

It is the unique morphism out of `H ⧸ I` whose composite with `H ⟶ H ⧸ I` is the quotient
map `H ⟶ H ⧸ J`. -/
noncomputable abbrev quotientMapOfLe (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) : quotient H I ⟶ quotient H J :=
  liftQuotient I (mkQuotient H J) (toIdeal_le_ker_mkQuotient_of_le H hIJ)

/-- The quotient-to-quotient morphism sends the class of `h` modulo `I` to its class
modulo `J`. -/
lemma quotientMapOfLe_mk (H : _root_.CommHopfAlgCat.{v} R) {I J : HopfIdeal R H}
    (hIJ : I ≤ J) (h : H) :
    (quotientMapOfLe H hIJ).hom (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R J.toIdeal h := by
  rw [quotientMapOfLe, liftQuotient_mk, mkQuotient_apply]

/-- A quotient-to-quotient coordinate morphism induced by an inclusion of Hopf ideals is
surjective. -/
theorem quotientMapOfLe_surjective (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    Function.Surjective (quotientMapOfLe H hIJ).hom :=
  liftQuotient_surjective_of_surjective I (mkQuotient H J)
    (toIdeal_le_ker_mkQuotient_of_le H hIJ) (mkQuotient_surjective H J)

/-- The surjective kernel Hopf ideal of the induced map `H ⧸ I ⟶ H ⧸ J` is the image
of `J` in `H ⧸ I`. -/
@[simp]
theorem kerOfSurjective_quotientMapOfLe (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    HopfIdeal.kerOfSurjective
        (Bialgebra.Quotient.liftBialgHom I.toIdeal
          (Bialgebra.Quotient.mkBialgHom J.toIdeal)
          (by simpa only [hom_mkQuotient] using
            toIdeal_le_ker_mkQuotient_of_le H hIJ))
        (quotientMapOfLe_surjective H hIJ) =
      J.map (Bialgebra.Quotient.mkBialgHom I.toIdeal) := by
  apply HopfIdeal.ext
  intro x
  obtain ⟨h, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [HopfIdeal.mem_kerOfSurjective, Bialgebra.Quotient.liftBialgHom_mk,
    Bialgebra.Quotient.mkBialgHom_apply, Ideal.Quotient.eq_zero_iff_mem, HopfIdeal.mem_toIdeal]
  conv_lhs => rw [← HopfIdeal.comapOfSurjective_map_mkBialgHom hIJ]
  rw [HopfIdeal.mem_comapOfSurjective, Bialgebra.Quotient.mkBialgHom_apply]

/-- Over a field, the kernel Hopf ideal of the induced map `H ⧸ I ⟶ H ⧸ J` is the
image of `J` in `H ⧸ I`. -/
@[simp]
theorem ker_quotientMapOfLe {k : Type u} [Field k]
    (H : _root_.CommHopfAlgCat.{v} k) {I J : HopfIdeal k H} (hIJ : I ≤ J) :
    HopfIdeal.ker
        (Bialgebra.Quotient.liftBialgHom I.toIdeal
          (Bialgebra.Quotient.mkBialgHom J.toIdeal)
          (by simpa only [hom_mkQuotient] using
            toIdeal_le_ker_mkQuotient_of_le H hIJ)) =
      J.map (Bialgebra.Quotient.mkBialgHom I.toIdeal) := by
  simpa only [HopfIdeal.kerOfSurjective_eq_ker] using
    kerOfSurjective_quotientMapOfLe H hIJ

/-- Composing the quotient map `H ⟶ H ⧸ I` with the quotient-to-quotient morphism for
`I ≤ J` gives the quotient map `H ⟶ H ⧸ J`. -/
@[reassoc]
lemma mkQuotient_comp_quotientMapOfLe (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    mkQuotient H I ≫ quotientMapOfLe H hIJ = mkQuotient H J :=
  mkQuotient_comp_liftQuotient I (mkQuotient H J)
    (toIdeal_le_ker_mkQuotient_of_le H hIJ)

/-- **A lift through the larger of two Hopf ideals is recognized by its precomposition with the
quotient morphism.** Composing `H ⧸ I ⟶ H ⧸ J` with the lift of `f : H ⟶ K` through `H ⧸ J` gives
the unique morphism `g : H ⧸ I ⟶ K` with `mkQuotient H I ≫ g = f`. -/
lemma quotientMapOfLe_comp_liftQuotient_eq (H : _root_.CommHopfAlgCat.{v} R)
    {K : _root_.CommHopfAlgCat.{v} R} {I J : HopfIdeal R H} (hIJ : I ≤ J) (f : H ⟶ K)
    (hf : J.toIdeal ≤ RingHom.ker f.hom.toAlgHom.toRingHom) (g : quotient H I ⟶ K)
    (hg : mkQuotient H I ≫ g = f) :
    quotientMapOfLe H hIJ ≫ liftQuotient J f hf = g := by
  apply mkQuotient_hom_ext
  rw [mkQuotient_comp_quotientMapOfLe_assoc, mkQuotient_comp_liftQuotient, hg]

/-- The quotient-to-quotient morphism for `I ≤ I` is the identity morphism. -/
@[simp]
lemma quotientMapOfLe_refl (H : _root_.CommHopfAlgCat.{v} R) (I : HopfIdeal R H) :
    quotientMapOfLe H (le_refl I) = 𝟙 (quotient H I) := by
  apply mkQuotient_hom_ext
  simp only [mkQuotient_comp_quotientMapOfLe, Category.comp_id]

/-- Quotient-to-quotient morphisms compose along inclusions of Hopf ideals. -/
@[simp]
lemma quotientMapOfLe_comp (H : _root_.CommHopfAlgCat.{v} R)
    {I J K : HopfIdeal R H} (hIJ : I ≤ J) (hJK : J ≤ K) :
    quotientMapOfLe H hIJ ≫ quotientMapOfLe H hJK =
      quotientMapOfLe H (hIJ.trans hJK) := by
  apply mkQuotient_hom_ext
  rw [mkQuotient_comp_quotientMapOfLe_assoc, mkQuotient_comp_quotientMapOfLe,
    mkQuotient_comp_quotientMapOfLe]

/-- The quotient-to-quotient morphism induced by an inclusion `I ≤ J` of Hopf ideals is
injective exactly when `I = J`. -/
theorem quotientMapOfLe_injective_iff (H : _root_.CommHopfAlgCat.{v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    Function.Injective (quotientMapOfLe H hIJ).hom ↔ I = J := by
  constructor
  · intro hinj
    refine le_antisymm hIJ fun x hx ↦ ?_
    rw [← HopfIdeal.mem_toIdeal, ← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk R]
    apply hinj
    rw [quotientMapOfLe_mk, map_zero, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem]
    exact HopfIdeal.mem_toIdeal.mpr hx
  · rintro rfl
    rw [quotientMapOfLe_refl]
    exact Function.injective_id

end CommHopfAlgCat

namespace FiniteTypeCommHopfAlgCat

open CategoryTheory

variable {R : Type u} [CommRing R]

/-- The quotient of a finite-type commutative Hopf algebra by a Hopf ideal, as a bundled
finite-type commutative Hopf algebra. -/
noncomputable abbrev quotient (H : FiniteTypeCommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    FiniteTypeCommHopfAlgCat.{u, v} R :=
  ⟨CommHopfAlgCat.quotient H.obj I, inferInstanceAs (Algebra.FiniteType R (H ⧸ I.toIdeal))⟩

/-- Quotienting a finite-type commutative Hopf algebra by the zero Hopf ideal gives an
isomorphic finite-type commutative Hopf algebra. -/
noncomputable def quotientBotIso (H : FiniteTypeCommHopfAlgCat.{u, v} R) :
    quotient H (⊥ : HopfIdeal R H) ≅ H :=
  ObjectProperty.isoMk _ (CommHopfAlgCat.quotientBotIso H.obj)

/-- The quotient morphism `H ⟶ H ⧸ I` in `FiniteTypeCommHopfAlgCat`. -/
noncomputable abbrev mkQuotient (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) : H ⟶ quotient H I :=
  ObjectProperty.homMk (CommHopfAlgCat.mkQuotient H.obj I)

/-- The finite-type quotient morphism forgets to the `CommHopfAlgCat` quotient morphism. -/
lemma forget₂_commHopfAlgCat_map_mkQuotient (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) :
    (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R) (_root_.CommHopfAlgCat.{v} R)).map
      (mkQuotient H I) = CommHopfAlgCat.mkQuotient H.obj I :=
  rfl

/-- Morphisms out of a finite-type Hopf-algebra quotient are determined by their composites
with the quotient morphism. -/
@[ext]
theorem mkQuotient_hom_ext {H X : FiniteTypeCommHopfAlgCat.{u, v} R}
    {I : HopfIdeal R H} {f g : quotient H I ⟶ X}
    (h : mkQuotient H I ≫ f = mkQuotient H I ≫ g) : f = g := by
  apply ObjectProperty.hom_ext
  apply CommHopfAlgCat.mkQuotient_hom_ext
  rw [← forget₂_commHopfAlgCat_map_mkQuotient]
  exact congrArg (fun q ↦ q.hom) h

/-- The inverse map of the finite-type quotient-by-zero isomorphism is the quotient morphism. -/
@[simp]
lemma quotientBotIso_inv (H : FiniteTypeCommHopfAlgCat.{u, v} R) :
    (quotientBotIso H).inv = mkQuotient H (⊥ : HopfIdeal R H) :=
  by
    rw [quotientBotIso]
    apply ObjectProperty.hom_ext
    exact CommHopfAlgCat.quotientBotIso_inv H.obj

/-- The kernel of the finite-type quotient morphism is the Hopf ideal being quotiented by. -/
lemma mkQuotient_ker (H : FiniteTypeCommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    RingHom.ker (toBialgHom (mkQuotient H I)).toAlgHom.toRingHom = I.toIdeal :=
  CommHopfAlgCat.mkQuotient_ker H.obj I

/-- An element maps to zero in the finite-type quotient exactly when it belongs to the Hopf
ideal. -/
lemma mkQuotient_eq_zero_iff (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    (I : HopfIdeal R H) (h : H) : toBialgHom (mkQuotient H I) h = 0 ↔ h ∈ I.toIdeal :=
  CommHopfAlgCat.mkQuotient_eq_zero_iff H.obj I h

variable {H K : FiniteTypeCommHopfAlgCat.{u, v} R}

/-- An isomorphism of finite-type commutative Hopf algebras induces an isomorphism from the
quotient by the inverse-image Hopf ideal to the corresponding quotient of the target. -/
noncomputable def quotientIsoOfIso (e : H ≅ K) (I : HopfIdeal R K) :
    quotient H
        (I.comapOfSurjective (toBialgHom e.hom) (ConcreteCategory.bijective_of_isIso e.hom).2) ≅
      quotient K I :=
  ObjectProperty.isoMk _ <|
    CommHopfAlgCat.quotientIsoOfIso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
        (_root_.CommHopfAlgCat.{v} R)).mapIso e) I

/-- If `I` is a minimal Hopf ideal of `K` among those whose quotient satisfies the
isomorphism-closed property `P`, then its inverse image along an isomorphism `e : H ≅ K` is a
minimal such Hopf ideal of `H`. -/
theorem minimal_quotientProperty_comapOfIso
    (P : ObjectProperty (FiniteTypeCommHopfAlgCat.{u, v} R)) [P.IsClosedUnderIsomorphisms]
    (I : HopfIdeal R K)
    (hI : Minimal (fun J : HopfIdeal R K ↦ P (quotient K J)) I) (e : H ≅ K) :
    Minimal (fun J : HopfIdeal R H ↦ P (quotient H J))
      (I.comapOfSurjective (toBialgHom e.hom)
        (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  let f := toBialgHom e.hom
  let hf := (ConcreteCategory.bijective_of_isIso e.hom).2
  let g := toBialgHom e.inv
  let hg := (ConcreteCategory.bijective_of_isIso e.inv).2
  refine ⟨P.prop_of_iso (quotientIsoOfIso e I).symm hI.prop, ?_⟩
  intro J hJ hJpulled
  let J' := J.comapOfSurjective g hg
  have hJ' : P (quotient K J') :=
    P.prop_of_iso (quotientIsoOfIso e.symm J).symm hJ
  have hJ'comap : J'.comapOfSurjective f hf = J :=
    HopfIdeal.comapOfSurjective_bialgEquiv_symm_apply J
      (_root_.CommHopfAlgCat.ofIso <|
        (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
          (_root_.CommHopfAlgCat.{v} R)).mapIso e)
  have hJ'I : J' ≤ I := by
    rw [← HopfIdeal.comapOfSurjective_le_comapOfSurjective_iff f hf, hJ'comap]
    exact hJpulled
  have hIJ' : I ≤ J' := hI.le_of_le hJ' hJ'I
  calc
    I.comapOfSurjective f hf ≤ J'.comapOfSurjective f hf :=
      HopfIdeal.comapOfSurjective_mono f hf hIJ'
    _ = J := hJ'comap

/-- Transporting a finite-type quotient object along an equality of Hopf ideals transports its
quotient morphism. -/
theorem mkQuotient_comp_eqToHom {I J : HopfIdeal R H} (hIJ : I = J) :
    mkQuotient H J ≫ eqToHom (congrArg (quotient H) hIJ.symm) = mkQuotient H I := by
  subst J
  rfl

/-- The forward finite-type quotient isomorphism commutes with the quotient morphisms. -/
@[simp]
lemma mkQuotient_comp_quotientIsoOfIso_hom (e : H ≅ K) (I : HopfIdeal R K) :
    mkQuotient H
          (I.comapOfSurjective (toBialgHom e.hom) (ConcreteCategory.bijective_of_isIso e.hom).2) ≫
        (quotientIsoOfIso e I).hom =
      e.hom ≫ mkQuotient K I := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.mkQuotient_comp_quotientIsoOfIso_hom
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
      (_root_.CommHopfAlgCat.{v} R)).mapIso e) I

/-- The inverse finite-type quotient isomorphism commutes with the quotient morphisms. -/
@[simp]
lemma mkQuotient_comp_quotientIsoOfIso_inv (e : H ≅ K) (I : HopfIdeal R K) :
    mkQuotient K I ≫ (quotientIsoOfIso e I).inv =
      e.inv ≫ mkQuotient H
        (I.comapOfSurjective (toBialgHom e.hom) (ConcreteCategory.bijective_of_isIso e.hom).2) := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.mkQuotient_comp_quotientIsoOfIso_inv
    ((forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
      (_root_.CommHopfAlgCat.{v} R)).mapIso e) I

/-- A morphism of finite-type commutative Hopf algebras out of `H` which kills a Hopf ideal
factors through the quotient object. -/
noncomputable abbrev liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) : quotient H I ⟶ K :=
  ObjectProperty.homMk (CommHopfAlgCat.liftQuotient I f.hom hf)

/-- The forward map of the finite-type quotient-by-zero isomorphism is the lift of the identity. -/
@[simp]
lemma quotientBotIso_hom (H : FiniteTypeCommHopfAlgCat.{u, v} R) :
    (quotientBotIso H).hom =
      liftQuotient (⊥ : HopfIdeal R H) (𝟙 H) bot_le :=
  by
    rw [quotientBotIso]
    apply ObjectProperty.hom_ext
    exact CommHopfAlgCat.quotientBotIso_hom H.obj

/-- The quotient lift composed with the quotient morphism is the original morphism. -/
@[simp]
lemma mkQuotient_comp_liftQuotient (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) :
    mkQuotient H I ≫ liftQuotient I f hf = f := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.mkQuotient_comp_liftQuotient I f.hom hf

/-- A morphism out of the quotient object is determined by its precomposition with the
quotient morphism. -/
lemma liftQuotient_unique (I : HopfIdeal R H) (f : H ⟶ K)
    (hf : I.toIdeal ≤ RingHom.ker (toBialgHom f).toAlgHom.toRingHom) (g : quotient H I ⟶ K)
    (hg : mkQuotient H I ≫ g = f) : g = liftQuotient I f hf := by
  apply mkQuotient_hom_ext
  rw [hg, mkQuotient_comp_liftQuotient]

/-- The finite-type coordinate morphism `H ⧸ I ⟶ H ⧸ J` induced by an inclusion `I ≤ J` of
Hopf ideals. -/
noncomputable abbrev quotientMapOfLe (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) : quotient H I ⟶ quotient H J :=
  ObjectProperty.homMk (CommHopfAlgCat.quotientMapOfLe H.obj hIJ)

/-- The finite-type quotient-to-quotient morphism sends the class of `h` modulo `I` to its
class modulo `J`. -/
lemma quotientMapOfLe_mk (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) (h : H) :
    (toBialgHom (quotientMapOfLe H hIJ)) (Ideal.Quotient.mkₐ R I.toIdeal h) =
      Ideal.Quotient.mkₐ R J.toIdeal h :=
  CommHopfAlgCat.quotientMapOfLe_mk H.obj hIJ h

/-- A finite-type quotient-to-quotient coordinate morphism induced by an inclusion of Hopf
ideals is surjective. -/
theorem quotientMapOfLe_surjective (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    Function.Surjective (toBialgHom (quotientMapOfLe H hIJ)) :=
  CommHopfAlgCat.quotientMapOfLe_surjective H.obj hIJ

/-- Composing the finite-type quotient map `H ⟶ H ⧸ I` with the quotient-to-quotient
morphism for `I ≤ J` gives the quotient map `H ⟶ H ⧸ J`. -/
@[reassoc (attr := simp)]
lemma mkQuotient_comp_quotientMapOfLe (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J : HopfIdeal R H} (hIJ : I ≤ J) :
    mkQuotient H I ≫ quotientMapOfLe H hIJ = mkQuotient H J := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe H.obj hIJ

/-- The finite-type quotient-to-quotient morphism for `I ≤ I` is the identity morphism. -/
@[simp]
lemma quotientMapOfLe_refl (H : FiniteTypeCommHopfAlgCat.{u, v} R) (I : HopfIdeal R H) :
    quotientMapOfLe H (le_refl I) = 𝟙 (quotient H I) := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.quotientMapOfLe_refl H.obj I

/-- Finite-type quotient-to-quotient morphisms compose along inclusions of Hopf ideals. -/
@[simp]
lemma quotientMapOfLe_comp (H : FiniteTypeCommHopfAlgCat.{u, v} R)
    {I J K : HopfIdeal R H} (hIJ : I ≤ J) (hJK : J ≤ K) :
    quotientMapOfLe H hIJ ≫ quotientMapOfLe H hJK =
      quotientMapOfLe H (hIJ.trans hJK) := by
  apply (forget₂ (FiniteTypeCommHopfAlgCat.{u, v} R)
    (_root_.CommHopfAlgCat.{v} R)).map_injective
  exact CommHopfAlgCat.quotientMapOfLe_comp H.obj hIJ hJK

end FiniteTypeCommHopfAlgCat

end TauCeti
