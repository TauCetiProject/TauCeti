/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.FunctorCategory
public import TauCeti.AlgebraicGeometry.ModularCurve.Ell

/-!
# Moduli problems over `Ell/B`

Following Katz and Mazur, a **moduli problem** over the category `Ell/B` of elliptic curves over
`B`-schemes is a contravariant functor `𝒫` from `Ell/B` to types: it assigns to an elliptic curve
`E` over a `B`-scheme `S` a type `𝒫(E/S)` of "level structures" on `E`, and to every cartesian
arrow `(E'/S') ⟶ (E/S)` a pull-back map `𝒫(E/S) ⟶ 𝒫(E'/S')`.

For an object `X = (E/S)` of `Ell/B`, the **fibre** `𝒫.fibre X` is the functor `T ↦ 𝒫(E_T/T)` on
schemes over `S`. The problem `𝒫` is **relatively representable** when every fibre is
representable by a scheme `𝒫_{E/S}` over `S`; `ModuliProblem.RelRepData` packages a choice of these
representing schemes. This is the notion all later constructions of moduli schemes are phrased in:
a relatively representable problem is *affine*, *finite*, *flat*, *étale*, … over `Ell/B` when
every representing morphism `𝒫_{E/S} ⟶ S` is (`RelRepData.HasProperty`).

Relative representability is a condition on each elliptic curve separately: unlike Mathlib's
`CategoryTheory.Functor.relativelyRepresentable`, whose representing objects lie in the source
category of a fixed functor, the representing objects here are schemes over the varying bases `S`.
Because every arrow of `Ell/B` is cartesian, these representing schemes are automatically
compatible with base change (`RelRepData.isPullback`), so any base-change-stable property of the
representing morphisms propagates along arrows of `Ell/B` (`RelRepData.rep_mem_of_hom`), and
`RelRepData.HasProperty` does not depend on the choice of representing schemes
(`RelRepData.hasProperty_congr`).

The trivial problem `[Γ(1)]` is the terminal presheaf `𝟙_`, relatively represented by the
identities of the bases (`RelRepData.tensorUnit`); every problem with exactly one level structure
on each object is isomorphic to it (`ModuliProblem.isoTensorUnitOfUnique`). The simultaneous
problem `(𝒫, 𝒬)` is the product presheaf `𝒫 ⊗ 𝒬`, relatively represented by the fibre products
`𝒫_{E/S} ×_S 𝒬_{E/S}` (`RelRepData.tensor`).

A moduli problem is **rigid** when no automorphism of an elliptic curve `E/S` other than the
identity fixes a level structure on `E/S` (`ModuliProblem.IsRigid`). Rigidity passes to every
problem with a morphism to a rigid one (`IsRigid.of_hom`), in particular to simultaneous problems,
and every problem representable by an object of `Ell/B` is rigid (`isRigid_of_representableBy`).

## Main definitions

* `TauCeti.AlgebraicGeometry.ModuliProblem B`: moduli problems over `Ell/B`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.fibre`: the functor `T ↦ 𝒫(E_T/T)` on schemes over the
  base of `E`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData`: relative-representability data.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.HasProperty`: a property of morphisms of
  schemes holds for every representing morphism.
* `TauCeti.AlgebraicGeometry.ModuliProblem.IsRigid`: rigidity.
* `TauCeti.AlgebraicGeometry.ModuliProblem.isoTensorUnitOfUnique`: a moduli problem with exactly
  one level structure on every object is the trivial problem `[Γ(1)]`.

## Main results

* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.isPullback`: for an arrow `(E'/S') ⟶ (E/S)`
  of `Ell/B`, `𝒫_{E'/S'}` is the base change of `𝒫_{E/S}` along `S' ⟶ S`.
* `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.tensor` and
  `TauCeti.AlgebraicGeometry.ModuliProblem.RelRepData.HasProperty.tensor`: the simultaneous
  problem of two relatively representable problems is relatively representable, and inherits every
  property stable under base change and composition.
* `TauCeti.AlgebraicGeometry.ModuliProblem.isRigid_of_representableBy`: a representable moduli
  problem is rigid.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Chapter 4, and Appendix A.4.1.
-/

public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Opposite AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry

/-- A **moduli problem** over `Ell/B`: a contravariant functor from the category `Ell/B` of
elliptic curves over `B`-schemes to types. Its values lie in `Type (u + 1)`, one universe above the
schemes, so that level structures may carry scheme-valued data such as subgroup schemes. -/
abbrev ModuliProblem (B : Scheme.{u}) := (EllObj B)ᵒᵖ ⥤ Type (u + 1)

namespace ModuliProblem

variable {B : Scheme.{u}} (P Q : ModuliProblem B) {X Y : EllObj B}

/-- The **fibre** of a moduli problem `𝒫` over an object `X = (E/S)` of `Ell/B`: the functor
`T ↦ 𝒫(E_T/T)` on schemes over `S`, where `E_T` is the base change of `E` along `T ⟶ S`. -/
@[expose, simps!]
noncomputable def fibre (X : EllObj B) : (Over X.base)ᵒᵖ ⥤ Type (u + 1) :=
  X.baseChangeFunctor.op ⋙ P

/-- **Base change of fibres along an arrow of `Ell/B`.** For an arrow `f : X ⟶ Y` of `Ell/B`
over `f.base : S' ⟶ S`, the fibre of `𝒫` over `X` is the fibre of `𝒫` over `Y` restricted to
schemes over `S'`, through `EllObj.baseChangeFunctorIso`. -/
noncomputable def fibreIso (f : X ⟶ Y) : P.fibre X ≅ (Over.map f.base).op ⋙ P.fibre Y :=
  Functor.isoWhiskerRight (NatIso.op (EllObj.baseChangeFunctorIso f)).symm P

@[simp]
theorem fibreIso_hom_app (f : X ⟶ Y) (T : (Over X.base)ᵒᵖ) :
    (P.fibreIso f).hom.app T = P.map ((EllObj.baseChangeFunctorIso f).inv.app T.unop).op :=
  (rfl)

/-- **A moduli problem with exactly one level structure on every object is trivial**: if `𝒫(E/S)`
has exactly one element for every object `(E/S)` of `Ell/B`, then `𝒫` is the trivial moduli
problem `[Γ(1)]`, the terminal presheaf `𝟙_`. -/
noncomputable def isoTensorUnitOfUnique [∀ X, Unique (P.obj X)] : P ≅ 𝟙_ (ModuliProblem B) where
  hom := toUnit _
  inv :=
    { app X := TypeCat.ofHom fun _ ↦ default
      naturality _ _ _ := by ext; exact Subsingleton.elim _ _ }
  hom_inv_id := by ext; exact Subsingleton.elim _ _
  inv_hom_id := toUnit_unique _ _

/-- **Relative-representability data** for a moduli problem `𝒫` (Katz–Mazur 4.2): for every
object `X = (E/S)` of `Ell/B`, a scheme `rep X = 𝒫_{E/S}` over `S` representing the fibre
`T ↦ 𝒫(E_T/T)`. -/
structure RelRepData where
  /-- The representing scheme `𝒫_{E/S}` over the base `S` of `X = (E/S)`. -/
  rep (X : EllObj B) : Over X.base
  /-- The scheme `rep X` represents the fibre of the problem over `X`. -/
  representableBy (X : EllObj B) : (P.fibre X).RepresentableBy (rep X)

namespace RelRepData

variable {P Q} (D : P.RelRepData)

/-- Along an arrow `f : X ⟶ Y` of `Ell/B`, the base change of the representing scheme over `Y`
along `f.base` represents the fibre of the problem over `X`. -/
noncomputable def representableByPullback (f : X ⟶ Y) :
    (P.fibre X).RepresentableBy ((Over.pullback f.base).obj (D.rep Y)) :=
  Functor.RepresentableBy.ofIso
    { homEquiv := ((Over.mapPullbackAdj f.base).homEquiv _ _).symm.trans
        (D.representableBy Y).homEquiv
      homEquiv_comp g h := by
        simp [Adjunction.homEquiv_naturality_left_symm, (D.representableBy Y).homEquiv_comp] }
    (P.fibreIso f).symm

/-- **Representing schemes commute with base change.** For an arrow `f : X ⟶ Y` of `Ell/B`, the
representing scheme over `X` is the base change of the representing scheme over `Y` along
`f.base`. -/
noncomputable def repIsoPullback (f : X ⟶ Y) : D.rep X ≅ (Over.pullback f.base).obj (D.rep Y) :=
  (D.representableBy X).uniqueUpToIso (D.representableByPullback f)

/-- **Representing schemes commute with base change**, as a pullback square: for an arrow
`f : (E'/S') ⟶ (E/S)` of `Ell/B`, the square formed by `𝒫_{E'/S'} ⟶ 𝒫_{E/S}`, the two representing
morphisms and `f.base : S' ⟶ S` is cartesian. -/
theorem isPullback (f : X ⟶ Y) :
    IsPullback ((D.repIsoPullback f).hom.left ≫ pullback.fst (D.rep Y).hom f.base)
      (D.rep X).hom (D.rep Y).hom f.base := by
  have h : (D.repIsoPullback f).hom.left ≫ pullback.snd (D.rep Y).hom f.base = (D.rep X).hom :=
    Over.w (D.repIsoPullback f).hom
  refine .of_iso_pullback ⟨?_⟩ ((Over.forget _).mapIso (D.repIsoPullback f)) rfl h
  rw [Category.assoc, pullback.condition, ← h, Category.assoc]

/-- A property of morphisms of schemes which is stable under base change propagates from the
representing morphism over `Y` to the representing morphism over `X`, along any arrow
`X ⟶ Y` of `Ell/B`. -/
theorem rep_mem_of_hom {W : MorphismProperty Scheme.{u}} [W.IsStableUnderBaseChange]
    (f : X ⟶ Y) (h : W (D.rep Y).hom) : W (D.rep X).hom :=
  W.of_isPullback (D.isPullback f) h

/-- A relatively representable moduli problem **has the property** `W` of morphisms of schemes
over `Ell/B` (for instance is affine, finite, flat or étale over `Ell/B`) when every representing
morphism `𝒫_{E/S} ⟶ S` has `W`. -/
def HasProperty (W : MorphismProperty Scheme.{u}) : Prop :=
  ∀ X : EllObj B, W (D.rep X).hom

/-- The defining condition of `RelRepData.HasProperty`: every representing morphism has `W`. -/
theorem hasProperty_iff {W : MorphismProperty Scheme.{u}} :
    D.HasProperty W ↔ ∀ X : EllObj B, W (D.rep X).hom :=
  Iff.rfl

/-- For a property `W` respecting isomorphisms, `HasProperty W` does not depend on the choice of
representing schemes. -/
theorem hasProperty_congr (D' : P.RelRepData) (W : MorphismProperty Scheme.{u}) [W.RespectsIso] :
    D.HasProperty W ↔ D'.HasProperty W := by
  refine forall_congr' fun X ↦ ?_
  let e := (D.representableBy X).uniqueUpToIso (D'.representableBy X)
  rw [← Over.w e.hom, W.cancel_left_of_respectsIso]

variable (B) in
/-- The trivial moduli problem `[Γ(1)]`, the terminal presheaf `𝟙_` on `Ell/B`, is relatively
representable: its fibre over `(E/S)` is represented by `S` itself. -/
noncomputable def tensorUnit : (𝟙_ (ModuliProblem B)).RelRepData where
  rep X := 𝟙_ (Over X.base)
  representableBy _ :=
    { homEquiv :=
        { toFun _ := PUnit.unit
          invFun _ := toUnit _
          left_inv _ := toUnit_unique _ _
          right_inv _ := rfl }
      homEquiv_comp _ _ := rfl }

@[simp]
theorem tensorUnit_rep (X : EllObj B) : (tensorUnit B).rep X = 𝟙_ (Over X.base) :=
  (rfl)

/-- The trivial moduli problem has every property of morphisms of schemes which holds for
identities. -/
theorem hasProperty_tensorUnit (W : MorphismProperty Scheme.{u}) [W.ContainsIdentities] :
    (tensorUnit B).HasProperty W :=
  fun X ↦ W.id_mem X.base

/-- **The simultaneous problem `(𝒫, 𝒬)`**, the product presheaf `𝒫 ⊗ 𝒬`, of two relatively
representable moduli problems is relatively representable: its fibre over `(E/S)` is represented
by the fibre product `𝒫_{E/S} ×_S 𝒬_{E/S}` of the two representing schemes. -/
noncomputable def tensor (D : P.RelRepData) (D' : Q.RelRepData) : (P ⊗ Q).RelRepData where
  rep X := D.rep X ⊗ D'.rep X
  representableBy X :=
    Functor.Monoidal.RepresentableBy.tensorObj (D.representableBy X) (D'.representableBy X)

@[simp]
theorem tensor_rep (D : P.RelRepData) (D' : Q.RelRepData) (X : EllObj B) :
    (D.tensor D').rep X = D.rep X ⊗ D'.rep X :=
  (rfl)

/-- The simultaneous problem of two relatively representable moduli problems with a property of
morphisms of schemes stable under base change and composition has that property. -/
theorem HasProperty.tensor {D : P.RelRepData} {D' : Q.RelRepData} {W : MorphismProperty Scheme.{u}}
    [W.IsStableUnderBaseChange] [W.IsStableUnderComposition] (h : D.HasProperty W)
    (h' : D'.HasProperty W) : (D.tensor D').HasProperty W :=
  fun X ↦ W.comp_mem _ _ (W.pullback_fst _ _ (h' X)) (h X)

end RelRepData

/-- A moduli problem `𝒫` is **rigid** when, for every elliptic curve `E/S`, the automorphism group
of `E/S` acts freely on `𝒫(E/S)`: an arrow `σ : X ⟶ X` of `Ell/B` over the identity of the base
(such an arrow is an automorphism, by `EllObj.isIso_iff_isIso_base`) which fixes some level
structure `α ∈ 𝒫(X)` is the identity. -/
def IsRigid : Prop :=
  ∀ ⦃X : EllObj B⦄ (σ : X ⟶ X), σ.base = 𝟙 X.base →
    ∀ α : P.obj (op X), P.map σ.op α = α → σ = 𝟙 X

/-- The defining condition of `IsRigid`: an arrow over the identity of the base fixing some level
structure is the identity. -/
theorem isRigid_iff : P.IsRigid ↔ ∀ ⦃X : EllObj B⦄ (σ : X ⟶ X), σ.base = 𝟙 X.base →
    ∀ α : P.obj (op X), P.map σ.op α = α → σ = 𝟙 X :=
  Iff.rfl

variable {P Q}

/-- A moduli problem with a morphism to a rigid moduli problem is rigid. -/
theorem IsRigid.of_hom (φ : P ⟶ Q) (hQ : Q.IsRigid) : P.IsRigid :=
  fun _ σ hσ α hα ↦ hQ σ hσ (φ.app _ α) (by rw [← NatTrans.naturality_apply, hα])

/-- The simultaneous problem `(𝒫, 𝒬)` is rigid when `𝒫` is. -/
theorem IsRigid.tensor_left (hP : P.IsRigid) : (P ⊗ Q).IsRigid :=
  hP.of_hom (fst P Q)

/-- The simultaneous problem `(𝒫, 𝒬)` is rigid when `𝒬` is. -/
theorem IsRigid.tensor_right (hQ : Q.IsRigid) : (P ⊗ Q).IsRigid :=
  hQ.of_hom (snd P Q)

/-- **A representable moduli problem is rigid** (Katz–Mazur A.4.1.2): if `𝒫` is represented by an
object `U` of `Ell/B`, in the sense that arrows `X ⟶ U` of `Ell/B` correspond naturally to
elements of `𝒫(X)`, then `𝒫` is rigid. -/
theorem isRigid_of_representableBy {U : EllObj B} (R : P.RepresentableBy U) : P.IsRigid := by
  intro X σ hσ α hα
  refine EllObj.hom_ext_of_comp (R.homEquiv.symm α) ?_ (hσ.trans (EllObj.id_base X).symm)
  rw [R.comp_homEquiv_symm, Category.id_comp]
  exact congrArg R.homEquiv.symm hα

end ModuliProblem

end TauCeti.AlgebraicGeometry
