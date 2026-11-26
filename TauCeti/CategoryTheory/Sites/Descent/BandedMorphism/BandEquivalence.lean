/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Aut.Conjugation
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import TauCeti.CategoryTheory.Sites.Descent.Banding

/-!
# Band preservation along natural isomorphisms, modifications and inverse equivalences

Let `F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be pseudofunctors with `A`-bandings `bF`, `bG`. A functor
`P : F(U) ⥤ G(U)` between the fibres over `U` **carries the band** if it sends the band
automorphism of every coefficient `a ∈ A(U)` at every `x` to the band automorphism of `a` at `P x`
(`GerbeBandEquivalence.MapsBand`); a strong transformation is band-preserving exactly when all its
components carry the band (`GerbeBandEquivalence.bandPreserving_iff`).

Since band automorphisms are compatible with conjugation along isomorphisms, carrying the band is
invariant under natural isomorphism of fibre functors
(`GerbeBandEquivalence.fibreNatIso_map_band`). Hence a strong transformation with component
functors isomorphic to those of a band-preserving one is band-preserving
(`GerbeBandEquivalence.of_fibreNatIso`), and band preservation is invariant under invertible
modifications (`GerbeBandEquivalence.of_modificationIso`,
`GerbeBandEquivalence.modificationIso_iff`, evaluating at the components
`StrongTrans.isoApp`). The inverse of a fibre equivalence that carries the
band carries it back (`GerbeBandEquivalence.inverse_map_band`), the unit and counit of the
equivalence conjugate band automorphisms to band automorphisms
(`GerbeBandEquivalence.unit_band`, `GerbeBandEquivalence.counit_band`), and a strong
transformation `σ : G ⟶ F` whose components are isomorphic to the inverses of the components of a
band-preserving `η` with equivalence components is band-preserving
(`GerbeBandEquivalence.inverse_preserving`). Olsson, Lemma 31.3 shows that a band-preserving
morphism of `A`-gerbes is an equivalence; the statements here, which need no gerbe hypotheses,
give the band preservation of its inverse.

## Main declarations

In the namespace `CategoryTheory.Pseudofunctor.GerbeBandEquivalence`:

* `MapsBand`: a fibre functor carries the band; `bandPreserving_iff`.
* `fibreNatIso_map_band`, `of_fibreNatIso`, `of_modificationIso`, `modificationIso_iff`.
* `inverse_map_band`, `unit_band`, `counit_band`, `inverse_preserving`.

## References

* [Martin Olsson, *Stacks* (lecture notes, notes by A. Geraschenko et al.)](https://stacky.net/files/written/Stacks/Stacks.pdf),
  Definition 31.1 and Lemma 31.3
-/

public section

universe w v u v' u'

open CategoryTheory Opposite Bicategory
open scoped Pseudofunctor.StrongTrans

namespace CategoryTheory.Pseudofunctor.GerbeBandEquivalence

variable {C : Type u} [Category.{v} C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat.{w}}
  (bF : F.AbelianBanding J A) (bG : G.AbelianBanding J A)

/-- A functor `P : F(U) ⥤ G(U)` between the fibres over `U` **carries the band** if it sends the
band automorphism of every coefficient `a` at every `x` to the band automorphism of `a` at
`P x`. -/
def MapsBand (U : C) (P : F.obj (.mk (op U)) ⥤ G.obj (.mk (op U))) : Prop :=
  ∀ (x : F.obj (.mk (op U))) (a : Multiplicative (A.obj.obj (op U))),
    P.mapAut x (bF.mulEquiv U x a) = bG.mulEquiv U (P.obj x) a

variable {bF bG}

/-- Unfolding of `GerbeBandEquivalence.MapsBand`. -/
theorem mapsBand_iff {U : C} {P : F.obj (.mk (op U)) ⥤ G.obj (.mk (op U))} :
    MapsBand bF bG U P ↔ ∀ (x : F.obj (.mk (op U))) (a : Multiplicative (A.obj.obj (op U))),
      P.mapAut x (bF.mulEquiv U x a) = bG.mulEquiv U (P.obj x) a :=
  Iff.rfl

/-- A strong transformation is band-preserving exactly when every component functor carries the
band. -/
theorem bandPreserving_iff (η : F ⟶ G) :
    BandPreserving bF bG η ↔ ∀ U : C, MapsBand bF bG U (η.app (.mk (op U))).toFunctor :=
  ⟨fun h U ↦ h.mapAut_mulEquiv U, fun h ↦ ⟨h⟩⟩

/-- **Carrying the band is invariant under natural isomorphism**: if `P` carries the band and
`e : P ≅ Q`, then `Q` carries the band, through conjugation along the components of `e`. -/
theorem fibreNatIso_map_band {U : C} {P Q : F.obj (.mk (op U)) ⥤ G.obj (.mk (op U))} (e : P ≅ Q)
    (hP : MapsBand bF bG U P) : MapsBand bF bG U Q := fun x a ↦ by
  rw [Functor.mapAut_eq_autMulEquivOfIso_app e x, hP x a,
    AbelianBanding.autMulEquivOfIso_mulEquiv]

/-- **Band preservation along natural isomorphisms of components.** If `η` is band-preserving and
every component functor of `θ` is isomorphic to that of `η`, then `θ` is band-preserving. No
compatibility of the isomorphisms with restriction is needed. -/
theorem of_fibreNatIso {η θ : F ⟶ G} [hη : BandPreserving bF bG η]
    (e : ∀ U : C, (η.app (.mk (op U))).toFunctor ≅ (θ.app (.mk (op U))).toFunctor) :
    BandPreserving bF bG θ :=
  (bandPreserving_iff θ).2 fun U ↦
    fibreNatIso_map_band (e U) ((bandPreserving_iff η).1 hη U)

/-- **Band preservation is invariant under invertible modifications.** -/
theorem of_modificationIso {η θ : F ⟶ G} [BandPreserving bF bG η] (e : η ≅ θ) :
    BandPreserving bF bG θ :=
  of_fibreNatIso fun U ↦ Cat.Hom.toNatIso (StrongTrans.isoApp e (.mk (op U)))

/-- For an invertible modification `e : η ≅ θ`, `η` is band-preserving exactly when `θ` is. -/
theorem modificationIso_iff {η θ : F ⟶ G} (e : η ≅ θ) :
    BandPreserving bF bG η ↔ BandPreserving bF bG θ :=
  ⟨fun _ ↦ of_modificationIso e, fun _ ↦ of_modificationIso e.symm⟩

/-- **The inverse of a band-carrying equivalence carries the band back**: if an equivalence
`P : F(U) ⥤ G(U)` carries the band, its inverse sends the band automorphism of `a` at `y` to the
band automorphism of `a` at `P⁻¹ y`. -/
theorem inverse_map_band {U : C} {P : F.obj (.mk (op U)) ⥤ G.obj (.mk (op U))}
    [P.IsEquivalence] (hP : MapsBand bF bG U P) : MapsBand bG bF U P.inv := fun y a ↦ by
  -- `P` is faithful; apply it and compare `P (P⁻¹ b)` with `b` through the counit.
  refine Aut.ext (Iso.ext (P.map_injective ?_))
  have h₁ := congrArg (fun c : Aut _ ↦ c.asIso.hom) (hP (P.inv.obj y) a)
  have h₂ := bG.inv_comp_mulEquiv_hom_comp (P.asEquivalence.counitIso.app y).symm a
  simp only [Functor.mapAut_apply_asIso, Functor.mapIso_hom] at h₁ ⊢
  rw [h₁]
  refine Eq.trans ?_ h₂
  rw [Functor.fun_inv_map]
  simp

/-- **The unit conjugates the band**: conjugation along the unit `x ≅ P⁻¹ (P x)` of a fibre
equivalence sends the band automorphism of `a` at `x` to that at `P⁻¹ (P x)`. -/
theorem unit_band {U : C} (P : F.obj (.mk (op U)) ⥤ G.obj (.mk (op U))) [P.IsEquivalence]
    (x : F.obj (.mk (op U))) (a : Multiplicative (A.obj.obj (op U))) :
    Aut.autMulEquivOfIso (P.asEquivalence.unitIso.app x) (bF.mulEquiv U x a) =
      bF.mulEquiv U (P.inv.obj (P.obj x)) a :=
  bF.autMulEquivOfIso_mulEquiv _ a

/-- **The counit conjugates the band**: conjugation along the counit `P (P⁻¹ y) ≅ y` of a fibre
equivalence sends the band automorphism of `a` at `P (P⁻¹ y)` to that at `y`. -/
theorem counit_band {U : C} (P : F.obj (.mk (op U)) ⥤ G.obj (.mk (op U))) [P.IsEquivalence]
    (y : G.obj (.mk (op U))) (a : Multiplicative (A.obj.obj (op U))) :
    Aut.autMulEquivOfIso (P.asEquivalence.counitIso.app y) (bG.mulEquiv U (P.obj (P.inv.obj y)) a) =
      bG.mulEquiv U y a :=
  bG.autMulEquivOfIso_mulEquiv _ a

/-- **Inverse transformations preserve the band.** Let `η : F ⟶ G` be band-preserving with
equivalences as component functors, and `σ : G ⟶ F` a strong transformation whose component
functors are isomorphic to the inverses of those of `η`. Then `σ` is band-preserving. The
existence of `σ` and its coherence are hypotheses, not constructed here. -/
theorem inverse_preserving {η : F ⟶ G} [hη : BandPreserving bF bG η]
    [∀ U : C, (η.app (.mk (op U))).toFunctor.IsEquivalence] (σ : G ⟶ F)
    (e : ∀ U : C, (σ.app (.mk (op U))).toFunctor ≅ (η.app (.mk (op U))).toFunctor.inv) :
    BandPreserving bG bF σ :=
  (bandPreserving_iff σ).2 fun U ↦
    fibreNatIso_map_band (e U).symm (inverse_map_band ((bandPreserving_iff η).1 hη U))

end CategoryTheory.Pseudofunctor.GerbeBandEquivalence
