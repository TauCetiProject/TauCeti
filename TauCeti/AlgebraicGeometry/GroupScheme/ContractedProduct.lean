/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.GroupScheme.Torsor
public import TauCeti.AlgebraicGeometry.Morphisms.Affine.BaseChange
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Over
public import TauCeti.CategoryTheory.Yoneda

/-!
# Contracted products of torsors under a group scheme

Let `G` be a group scheme over a scheme `S`, `P` a torsor under its sheaf of points `h_G` on the
big fppf site of `S`, and `X` a scheme over `S` with an action of `G`. The contracted product
`P ×^G X` of `P` with the sheaf of points of `X`
(`CategoryTheory.Sheaf.Torsor.contractedProduct`) is a sheaf which becomes isomorphic to the
sheaf of points of `X` over every scheme over which `P` has a section. When `X` is affine over
`S`, it is therefore represented by a scheme affine over `S`, by fppf descent of schemes affine
over the base and Zariski gluing
(`CategoryTheory.Sheaf.Torsor.exists_isAffineHom_nonempty_representableBy_of_iso`). This scheme
`P.contractedProductScheme X` is the twist of `X` by `P`: its base change to every scheme `T`
over which `P` has a section is isomorphic to the base change of `X`, so it is fppf-locally
isomorphic to `X`; for a global section of `P`, and in particular for the trivial torsor, it is
isomorphic to `X` itself. No hypothesis on `G` is needed. For a `G`-torsor `P` and a morphism
`p : S' ⟶ S`, the base change of `P ×^G X` is the contracted product of the base changes of `P`
and `X`, a torsor under the base change of `G` and a scheme with its action.

The same representability, applied to the torsor `Torsor.map φ P` obtained by extending the
structure group along a homomorphism `φ : G ⟶ H` of group schemes, gives for `H` affine over `S`
the `H`-torsor `TauCeti.GroupScheme.pushforwardTorsor φ P` whose torsor of points is
`Torsor.map φ P`, the contracted product `P ×^G H`
(`CategoryTheory.Sheaf.Torsor.contractedProductMulRightIso`). Its class in the torsor classes
of `H` is the image of the class of `P`.

## Main declarations

* `CategoryTheory.Sheaf.Torsor.exists_isAffineHom_nonempty_contractedProduct_representableBy`:
  for `X` affine over `S`, the contracted product `P ×^G X` is represented by a scheme affine
  over `S`.
* `CategoryTheory.Sheaf.Torsor.contractedProductScheme P X`: the scheme `P ×^G X` over `S`,
  affine over `S`, with its representation `contractedProductSchemeRepresentableBy`.
* `CategoryTheory.Sheaf.Torsor.pullbackContractedProductSchemeIsoOfSection`: over a scheme `T`
  over which `P` has a section, `(P ×^G X) ×_S T ≅ X ×_S T`.
* `CategoryTheory.Sheaf.Torsor.contractedProductSchemeIsoOfSection` and
  `CategoryTheory.Sheaf.Torsor.contractedProductSchemeTrivialIso`: a global section of `P` gives
  `P ×^G X ≅ X`, and `G ×^G X ≅ X`.
* `TauCeti.GroupScheme.pullbackContractedProductSchemeIso`: for a `G`-torsor `P` and
  `p : S' ⟶ S`, `(P ×^G X) ×_S S' ≅ (P ×_S S') ×^(G ×_S S') (X ×_S S')`.
* `TauCeti.GroupScheme.pushforwardTorsor φ P`: the `H`-torsor representing `Torsor.map φ P`,
  with `toTorsorPushforwardTorsorIso` and `mk_toTorsor_pushforwardTorsor`.

## References

* J. Giraud, *Cohomologie non abélienne*, Chapitre III, §1.3, for the contracted product.
* B. Poonen, *Rational points on varieties*, §5.12.5.2 and §6.5.6, for contracted products and
  twisting by torsors, and Theorem 6.5.10 (i) for the representability of torsors under an affine
  group scheme.
-/

public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry

universe w u

namespace CategoryTheory.Sheaf.Torsor

open GrothendieckTopology

variable {S : Scheme.{u}} {G : Grp (Over S)}
  (P : Torsor ((Scheme.fppfTopology.over S).uliftYonedaGrp.{w}.obj G)) (X : Over S) [ModObj G.X X]
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type (max u w))]
  [(Scheme.fppfTopology.over S).WEqualsLocallyBijective (Type (max u w))]

/-- **Contracted products with affine schemes are representable.** For a torsor `P` under the
sheaf of points of a group scheme `G` over `S` and a scheme `X` affine over `S` with an action of
`G`, the contracted product `P ×^G X` of `P` with the sheaf of points of `X` is represented by a
scheme affine over `S`: it is isomorphic to the sheaf of points of `X` over every scheme over
which `P` has a section. -/
theorem exists_isAffineHom_nonempty_contractedProduct_representableBy [IsAffineHom X.hom] :
    ∃ Y : Over S, IsAffineHom Y.hom ∧ Nonempty ((P.contractedProduct
      ((Scheme.fppfTopology.over S).uliftYonedaMulActionSheaf.{w} G X)).obj.RepresentableBy Y) :=
  P.exists_isAffineHom_nonempty_representableBy_of_iso _
    (uliftYonedaMulActionSheafRepresentableBy G X) fun _ σ ↦
      ⟨(P.contractedProductCompIsoOfSection _ _ (fun T' ↦ σ.val (op T'))
        fun _ _ f ↦ σ.property f.op).symm⟩

/-- For `X` affine over `S`, the contracted product `P ×^G X` is representable. -/
instance isRepresentable_contractedProduct [IsAffineHom X.hom] :
    (P.contractedProduct
      ((Scheme.fppfTopology.over S).uliftYonedaMulActionSheaf.{w} G X)).obj.IsRepresentable :=
  have ⟨_, _, ⟨e⟩⟩ := P.exists_isAffineHom_nonempty_contractedProduct_representableBy X
  e.isRepresentable

/-- The contracted product `P ×^G X` of a torsor `P` under the sheaf of points of `G` with a scheme
`X` affine over `S` with an action of `G`, as a scheme over `S`: the scheme representing the
contracted product of `P` with the sheaf of points of `X`. It is the twist of `X` by `P`, affine
over `S`, and fppf-locally isomorphic to `X` (`pullbackContractedProductSchemeIsoOfSection`).

Use `contractedProductSchemeRepresentableBy` for its points. -/
def contractedProductScheme [IsAffineHom X.hom] : Over S :=
  (P.contractedProduct ((Scheme.fppfTopology.over S).uliftYonedaMulActionSheaf.{w} G X)).obj.reprX

/-- The points of the scheme `P ×^G X` are the sections of the contracted product of `P` with the
sheaf of points of `X`. -/
def contractedProductSchemeRepresentableBy [IsAffineHom X.hom] :
    Functor.RepresentableBy
      (P.contractedProduct ((Scheme.fppfTopology.over S).uliftYonedaMulActionSheaf.{w} G X)).obj
      (P.contractedProductScheme X) :=
  Functor.representableBy _

/-- The contracted product `P ×^G X` of a torsor with a scheme affine over `S` is affine over
`S`. -/
instance isAffineHom_contractedProductScheme [IsAffineHom X.hom] :
    IsAffineHom (P.contractedProductScheme X).hom := by
  obtain ⟨Y, _, ⟨e⟩⟩ := P.exists_isAffineHom_nonempty_contractedProduct_representableBy X
  rw [← Over.w (e.uniqueUpToIso (P.contractedProductSchemeRepresentableBy X)).inv]
  infer_instance

variable [IsAffineHom X.hom]

/-- **The contracted product is fppf-locally isomorphic to `X`.** Over a scheme `T` over `S` over
which the torsor `P` has a section `ξ`, the base change of `P ×^G X` is isomorphic to the base
change of `X`: both represent the restriction of the contracted product to schemes over `T`,
identified with that of the sheaf of points of `X` by `x ↦ [ξ, x]`. Such schemes `T` cover `S`
for the fppf topology. -/
def pullbackContractedProductSchemeIsoOfSection {T : Over S} (ξ : P.sheaf.obj.obj (op T)) :
    (Over.pullback T.hom).obj (P.contractedProductScheme X) ≅ (Over.pullback T.hom).obj X :=
  ((Over.mapPullbackAdj T.hom).representableByComp
    (P.contractedProductSchemeRepresentableBy X)).uniqueUpToIso
      (((Over.mapPullbackAdj T.hom).representableByComp
        (uliftYonedaMulActionSheafRepresentableBy G X)).ofIso
          (P.contractedProductCompIsoOfSection _ (Over.map T.hom)
            (fun T' ↦ (Over.mapSection _ ξ).val (op T'))
            fun _ _ f ↦ (Over.mapSection _ ξ).property f.op))

/-- The isomorphism `pullbackContractedProductSchemeIsoOfSection ξ` sends a point `y` of the base
change of `X` to the point of `P ×^G X` corresponding to the class `[ξ, x]`, for `x` the point of
`X` adjoint to `y`. -/
@[simp]
lemma
    contractedProductSchemeRepresentableBy_homEquiv_pullbackContractedProductSchemeIsoOfSection_inv
    {T : Over S} (ξ : P.sheaf.obj.obj (op T)) {T' : Over T.left}
    (y : T' ⟶ (Over.pullback T.hom).obj X) :
    (P.contractedProductSchemeRepresentableBy X).homEquiv
        (((Over.mapPullbackAdj T.hom).homEquiv _ _).symm
          (y ≫ (P.pullbackContractedProductSchemeIsoOfSection X ξ).inv)) =
      contractedProductMk ((Over.mapSection _ ξ).val (op T'))
        ((uliftYonedaMulActionSheafSectionEquiv G X _).symm
          (((Over.mapPullbackAdj T.hom).homEquiv _ _).symm y)) := by
  rw [← Adjunction.representableByComp_homEquiv_apply, pullbackContractedProductSchemeIsoOfSection,
    Functor.RepresentableBy.homEquiv_comp_uniqueUpToIso_inv]
  exact (contractedProductCompIsoOfSection_hom_app_apply ..).trans (congrArg _
    ((Adjunction.representableByComp_homEquiv_apply ..).trans
      (uliftYonedaMulActionSheafRepresentableBy_homEquiv G X _)))

/-- A global section `s` of the torsor `P` identifies the contracted product `P ×^G X` with `X`:
both represent the contracted product of `P` with the sheaf of points of `X`, identified with the
sheaf of points of `X` by `x ↦ [s, x]` (`contractedProductIsoOfSection`). -/
def contractedProductSchemeIsoOfSection (s : P.sheaf.obj.sections) :
    P.contractedProductScheme X ≅ X :=
  (P.contractedProductSchemeRepresentableBy X).uniqueUpToIso
    ((uliftYonedaMulActionSheafRepresentableBy G X).ofIso
      ((sheafToPresheaf _ _).mapIso (P.contractedProductIsoOfSection _ s)))

/-- The isomorphism `contractedProductSchemeIsoOfSection s` sends a point `x : T ⟶ X` to the point
of `P ×^G X` corresponding to the class `[s, x]`. -/
@[simp]
lemma contractedProductSchemeRepresentableBy_homEquiv_comp_contractedProductSchemeIsoOfSection_inv
    (s : P.sheaf.obj.sections) {T : Over S} (x : T ⟶ X) :
    (P.contractedProductSchemeRepresentableBy X).homEquiv
        (x ≫ (P.contractedProductSchemeIsoOfSection X s).inv) =
      contractedProductMk (s.val (op T))
        ((uliftYonedaMulActionSheafSectionEquiv G X (op T)).symm x) := by
  rw [contractedProductSchemeIsoOfSection,
    Functor.RepresentableBy.homEquiv_comp_uniqueUpToIso_inv]
  exact (P.contractedProductIsoOfSection_hom_hom_app s _).trans
    (congrArg _ (uliftYonedaMulActionSheafRepresentableBy_homEquiv G X x))

variable (G) in
/-- **The contracted product with the trivial torsor.** The contracted product `G ×^G X` of the
trivial torsor, the sheaf of points of `G` acting on itself, with `X` is isomorphic to `X`, through
`[g, x] ↦ g⁻¹ • x` (`contractedProductTrivialIso`). -/
def contractedProductSchemeTrivialIso :
    (trivial ((Scheme.fppfTopology.over S).uliftYonedaGrp.{w}.obj G)).contractedProductScheme X ≅
      X :=
  (trivial _).contractedProductSchemeIsoOfSection X
    ⟨fun U ↦ (1 : ((Scheme.fppfTopology.over S).uliftYonedaGrp.{w}.obj G).obj.obj U),
      fun f ↦ map_one (((Scheme.fppfTopology.over S).uliftYonedaGrp.{w}.obj G).obj.map f).hom⟩

/-- The isomorphism `contractedProductSchemeTrivialIso` sends a point `x : T ⟶ X` to the point of
`G ×^G X` corresponding to the class `[1, x]`. -/
@[simp]
lemma
    contractedProductSchemeRepresentableBy_homEquiv_comp_contractedProductSchemeTrivialIso_inv
    {T : Over S} (x : T ⟶ X) :
    ((trivial _).contractedProductSchemeRepresentableBy X).homEquiv
        (x ≫ (contractedProductSchemeTrivialIso G X).inv) =
      contractedProductMk (P := trivial _)
        (1 : ((Scheme.fppfTopology.over S).uliftYonedaGrp.{w}.obj G).obj.obj (op T))
        ((uliftYonedaMulActionSheafSectionEquiv G X (op T)).symm x) := by
  exact contractedProductSchemeRepresentableBy_homEquiv_comp_contractedProductSchemeIsoOfSection_inv
    (G := G) (trivial _) X _ x

end CategoryTheory.Sheaf.Torsor

namespace TauCeti.GroupScheme

open GrothendieckTopology

section Pushforward

variable {S : Scheme.{u}} {G H : Grp (Over S)} [IsAffineHom H.X.hom] (φ : G ⟶ H)
  (P : Sheaf.Torsor ((Scheme.fppfTopology.over S).uliftYonedaGrp.{w}.obj G))
  [HasWeakSheafify (Scheme.fppfTopology.over S) (Type (max u w))]
  [(Scheme.fppfTopology.over S).WEqualsLocallyBijective (Type (max u w))]

/-- **Pushforward of torsors along a homomorphism of group schemes.** For a homomorphism
`φ : G ⟶ H` of group schemes over `S` with `H` affine over `S` and a torsor `P` under the sheaf of
points of `G`, the `H`-torsor whose torsor of points is the torsor `Torsor.map φ P` obtained by
extending the structure group along `φ`, which is the contracted product `P ×^G H` for the action
`g • h = h * φ(g)⁻¹` (`Sheaf.Torsor.contractedProductMulRightIso`). It is affine over `S`, as
every `H`-torsor is (`isAffineHom_of_isTorsor`).

Use `toTorsorPushforwardTorsorIso` to identify its torsor of points. -/
def pushforwardTorsor : ((Scheme.fppfTopology.over S).torsorProperty H).FullSubcategory :=
  ((Scheme.fppfTopology.over S).toTorsorFunctor.{w} H).objPreimage
    (P.map ((Scheme.fppfTopology.over S).uliftYonedaGrp.{w}.map φ))

/-- The torsor of points of `pushforwardTorsor φ P` is the torsor `Torsor.map φ P` obtained by
extending the structure group of `P` along `φ`. -/
def toTorsorPushforwardTorsorIso :
    ((Scheme.fppfTopology.over S).toTorsorFunctor.{w} H).obj (pushforwardTorsor φ P) ≅
      P.map ((Scheme.fppfTopology.over S).uliftYonedaGrp.{w}.map φ) :=
  Functor.objObjPreimageIso _ _

/-- The class of `pushforwardTorsor φ P` among the torsor classes of `H` is the image of the class
of `P` under the map induced by `φ`. -/
lemma mk_toTorsor_pushforwardTorsor :
    Sheaf.NonabelianH1.mk (pushforwardTorsor φ P).property.toTorsor =
      Sheaf.NonabelianH1.map ((Scheme.fppfTopology.over S).uliftYonedaGrp.{w}.map φ)
        (Sheaf.NonabelianH1.mk P) := by
  rw [Sheaf.NonabelianH1.map_mk]
  exact Sheaf.NonabelianH1.mk_eq_mk_iff.2 ⟨toTorsorPushforwardTorsorIso φ P⟩

end Pushforward

section BaseChange

open MonoidalCategory CartesianMonoidalCategory
open scoped MonObj Obj

variable {S S' : Scheme.{u}} (p : S' ⟶ S)

variable {G : Grp (Over S)} {P : Over S} [ModObj G.X P]
  (h : (Scheme.fppfTopology.over S).IsTorsor G P) (X : Over S) [ModObj G.X X]

/-- The torsor of points of the base change of the `G`-torsor `P`, a torsor under the sheaf of
points of the base change of `G`. -/
private abbrev baseChangeTorsor :
    Sheaf.Torsor ((Scheme.fppfTopology.over S').uliftYonedaGrp.{w}.obj
      ((Over.pullback p).mapGrp.obj G)) :=
  letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj P) :=
    (Over.pullback p).modObjObj G.X P
  (isTorsor_pullback_obj p h).toTorsor.{w}

/-- The sheaf of points of the base change of `X`, with the action of the sheaf of points of the
base change of `G`. -/
private abbrev baseChangeMulActionSheaf :
    Sheaf.MulActionSheaf ((Scheme.fppfTopology.over S').uliftYonedaGrp.{w}.obj
      ((Over.pullback p).mapGrp.obj G)) :=
  letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
    (Over.pullback p).modObjObj G.X X
  (Scheme.fppfTopology.over S').uliftYonedaMulActionSheaf.{w} _ ((Over.pullback p).obj X)

variable {X}

/-- The transpose of a point of the base change of `G` over `T`, a point of `G` over the scheme
`T` over `S`. -/
private def groupPoint (G : Grp (Over S)) (T : (Over S')ᵒᵖ)
    (g : ((Scheme.fppfTopology.over S').uliftYonedaGrp.{w}.obj
      ((Over.pullback p).mapGrp.obj G)).obj.obj T) :
    ((Scheme.fppfTopology.over S).uliftYonedaGrp.{w}.obj G).obj.obj ((Over.map p).op.obj T) :=
  (uliftYonedaGrpObjEquiv G _).symm (((Over.mapPullbackAdj p).homEquiv _ _).symm
    (uliftYonedaGrpObjEquiv _ T g))

/-- The transpose of a point of the base change of `X` over `T`, a point of `X` over the scheme
`T` over `S`. -/
private def mulActionPoint {T : (Over S')ᵒᵖ}
    (b : (baseChangeMulActionSheaf.{w} p (G := G) X).sheaf.obj.obj T) :
    ((Scheme.fppfTopology.over S).uliftYonedaMulActionSheaf.{w} G X).sheaf.obj.obj
      ((Over.map p).op.obj T) :=
  letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
    (Over.pullback p).modObjObj G.X X
  (uliftYonedaMulActionSheafSectionEquiv G X _).symm
    (((Over.mapPullbackAdj p).homEquiv _ _).symm
      (uliftYonedaMulActionSheafSectionEquiv _ _ T b))

private lemma mulActionPoint_map {T T' : (Over S')ᵒᵖ} (f : T ⟶ T')
    (b : (baseChangeMulActionSheaf.{w} p (G := G) X).sheaf.obj.obj T) :
    mulActionPoint p ((baseChangeMulActionSheaf.{w} p (G := G) X).sheaf.obj.map f b) =
      ((Scheme.fppfTopology.over S).uliftYonedaMulActionSheaf.{w} G X).sheaf.obj.map
        ((Over.map p).op.map f) (mulActionPoint p b) := by
  let : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
    (Over.pullback p).modObjObj G.X X
  apply (uliftYonedaMulActionSheafSectionEquiv G X _).injective
  rw [mulActionPoint, mulActionPoint, uliftYonedaMulActionSheafSectionEquiv_map,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (congrArg _ (uliftYonedaMulActionSheafSectionEquiv_map _ _ f b)).trans
    (Adjunction.homEquiv_naturality_left_symm ..)

private lemma mulActionPoint_smul {T : (Over S')ᵒᵖ}
    (g : ((Scheme.fppfTopology.over S').uliftYonedaGrp.{w}.obj
      ((Over.pullback p).mapGrp.obj G)).obj.obj T)
    (b : (baseChangeMulActionSheaf.{w} p (G := G) X).sheaf.obj.obj T) :
    mulActionPoint p (g • b) = groupPoint p G T g • mulActionPoint p b := by
  let : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
    (Over.pullback p).modObjObj G.X X
  apply (uliftYonedaMulActionSheafSectionEquiv G X _).injective
  rw [mulActionPoint, mulActionPoint, groupPoint, uliftYonedaMulActionSheafSectionEquiv_smul,
    Equiv.apply_symm_apply, MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact (congrArg _ (uliftYonedaMulActionSheafSectionEquiv_smul _ _ g b)).trans
    (Over.mapPullbackAdj_homEquiv_symm_smul p _ _)

/-- The transpose of a point of the base change of `P`, transported from `mulActionPoint` through
`IsTorsor.toTorsorMulActionSheafSectionEquiv`. This avoids unfolding either functor of points
across module boundaries. -/
private def torsorPoint {T : (Over S')ᵒᵖ} (a : (baseChangeTorsor.{w} p h).sheaf.obj.obj T) :
    (h.toTorsor.{w}).sheaf.obj.obj ((Over.map p).op.obj T) :=
  letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj P) :=
    (Over.pullback p).modObjObj G.X P
  (h.toTorsorMulActionSheafSectionEquiv _).symm
    (mulActionPoint p ((isTorsor_pullback_obj p h).toTorsorMulActionSheafSectionEquiv T a))

private lemma torsorPoint_map {T T' : (Over S')ᵒᵖ} (f : T ⟶ T')
    (a : (baseChangeTorsor.{w} p h).sheaf.obj.obj T) :
    torsorPoint p h ((baseChangeTorsor.{w} p h).sheaf.obj.map f a) =
      (h.toTorsor.{w}).sheaf.obj.map ((Over.map p).op.map f) (torsorPoint p h a) := by
  let : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj P) :=
    (Over.pullback p).modObjObj G.X P
  apply (h.toTorsorMulActionSheafSectionEquiv _).injective
  rw [torsorPoint, torsorPoint, Equiv.apply_symm_apply,
    IsTorsor.toTorsorMulActionSheafSectionEquiv_map,
    Equiv.apply_symm_apply, ← mulActionPoint_map]
  exact congrArg (mulActionPoint p) (IsTorsor.toTorsorMulActionSheafSectionEquiv_map _ f a)

private lemma torsorPoint_smul {T : (Over S')ᵒᵖ}
    (g : ((Scheme.fppfTopology.over S').uliftYonedaGrp.{w}.obj
      ((Over.pullback p).mapGrp.obj G)).obj.obj T)
    (a : (baseChangeTorsor.{w} p h).sheaf.obj.obj T) :
    torsorPoint p h (g • a) = groupPoint p G T g • torsorPoint p h a := by
  let : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj P) :=
    (Over.pullback p).modObjObj G.X P
  apply (h.toTorsorMulActionSheafSectionEquiv _).injective
  rw [torsorPoint, torsorPoint, Equiv.apply_symm_apply,
    IsTorsor.toTorsorMulActionSheafSectionEquiv_smul,
    Equiv.apply_symm_apply, ← mulActionPoint_smul]
  exact congrArg (mulActionPoint p) (IsTorsor.toTorsorMulActionSheafSectionEquiv_smul _ g a)

/-- The transpose of the section of the base change of `X` given by `b` is given by the adjoint
transpose of `b`. -/
private lemma mulActionPoint_symm {T : Over S'} (b : T ⟶ (Over.pullback p).obj X) :
    letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
      (Over.pullback p).modObjObj G.X X
    mulActionPoint p ((uliftYonedaMulActionSheafSectionEquiv _ _ (op T)).symm b) =
      (uliftYonedaMulActionSheafSectionEquiv G X _).symm
        (((Over.mapPullbackAdj p).homEquiv _ _).symm b) := by
  simp only [mulActionPoint, Equiv.apply_symm_apply, Functor.op_obj, unop_op]

/-- The transpose of the section of the base change of `P` given by `a` is given by the adjoint
transpose of `a`. -/
private lemma torsorPoint_symm {T : Over S'} (a : T ⟶ (Over.pullback p).obj P) :
    letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj P) :=
      (Over.pullback p).modObjObj G.X P
    torsorPoint p h (((isTorsor_pullback_obj p h).toTorsorSectionEquiv (op T)).symm a) =
      (h.toTorsorSectionEquiv _).symm (((Over.mapPullbackAdj p).homEquiv _ _).symm a) := by
  let : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj P) :=
    (Over.pullback p).modObjObj G.X P
  rw [torsorPoint, Equiv.symm_apply_eq]
  exact (congrArg (mulActionPoint p)
    (IsTorsor.toTorsorMulActionSheafSectionEquiv_toTorsorSectionEquiv_symm _ a)).trans
      ((mulActionPoint_symm p (G := G) (X := P) a).trans
        (IsTorsor.toTorsorMulActionSheafSectionEquiv_toTorsorSectionEquiv_symm h _).symm)

variable (X) [HasWeakSheafify (Scheme.fppfTopology.over S) (Type (max u w))]
  [(Scheme.fppfTopology.over S).WEqualsLocallyBijective (Type (max u w))]
  [HasWeakSheafify (Scheme.fppfTopology.over S') (Type (max u w))]
  [(Scheme.fppfTopology.over S').WEqualsLocallyBijective (Type (max u w))]

/-- The comparison from the contracted product of the base changes of `P` and `X` to the
restriction of the contracted product of `P` and `X` to schemes over `S'`: the class of points
`(p', x')` over `T` goes to the class of their transposes, points of `P` and `X` over the scheme
`T` over `S`. -/
private def baseChangeDesc :
    (baseChangeTorsor.{w} p h).contractedProduct (baseChangeMulActionSheaf.{w} p (G := G) X) ⟶
      (Scheme.fppfTopology.overMapPullback (Type (max u w)) p).obj
        ((h.toTorsor.{w}).contractedProduct
          ((Scheme.fppfTopology.over S).uliftYonedaMulActionSheaf.{w} G X)) :=
  Sheaf.Torsor.contractedProductDesc
    (ObjectProperty.homMk
      { app T := ↾fun a ↦ Sheaf.Torsor.contractedProductMk (torsorPoint p h a.1)
          (mulActionPoint p a.2)
        naturality T T' f := by
          ext ⟨a, b⟩
          exact (congrArg₂ Sheaf.Torsor.contractedProductMk (torsorPoint_map p h f a)
            (mulActionPoint_map p f b)).trans
              (Sheaf.Torsor.contractedProduct_map_contractedProductMk _ _ _).symm })
    fun T g a b ↦ (congrArg₂ Sheaf.Torsor.contractedProductMk (torsorPoint_smul p h g a)
      (mulActionPoint_smul p g b)).trans (Sheaf.Torsor.contractedProductMk_smul _ _ _)

omit [(Scheme.fppfTopology.over S).WEqualsLocallyBijective (Type (max u w))]
  [(Scheme.fppfTopology.over S').WEqualsLocallyBijective (Type (max u w))] in
/-- The comparison `baseChangeDesc` sends the class `[a, b]` to the class of the transposes. -/
private lemma baseChangeDesc_hom_app_contractedProductMk {T : (Over S')ᵒᵖ}
    (a : (baseChangeTorsor.{w} p h).sheaf.obj.obj T)
    (b : (baseChangeMulActionSheaf.{w} p (G := G) X).sheaf.obj.obj T) :
    (baseChangeDesc p h X).hom.app T (Sheaf.Torsor.contractedProductMk a b) =
      Sheaf.Torsor.contractedProductMk (torsorPoint p h a) (mulActionPoint p b) :=
  Sheaf.Torsor.contractedProductDesc_hom_app_contractedProductMk _ _ a b

/-- Over a scheme over which the base change of `P` has a section `a`, the comparison
`baseChangeDesc` is the bijection `x' ↦ [a, x'] ↦ [a₀, x₀]`, for `a₀` and `x₀` the transposes of
`a` and `x'`; so it is an isomorphism. -/
private instance isIso_baseChangeDesc : IsIso (baseChangeDesc p h X) :=
  Sheaf.Torsor.isIso_of_bijective_app (baseChangeTorsor.{w} p h) _ fun T ⟨a⟩ ↦ by
    let : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
      (Over.pullback p).modObjObj G.X X
    let e := (uliftYonedaMulActionSheafSectionEquiv.{w} (J := Scheme.fppfTopology.over S')
      ((Over.pullback p).mapGrp.obj G) ((Over.pullback p).obj X) (op T)).trans
      (((Over.mapPullbackAdj p).homEquiv _ _).symm.trans
        (uliftYonedaMulActionSheafSectionEquiv.{w} (J := Scheme.fppfTopology.over S) G X
          ((Over.map p).op.obj (op T))).symm)
    have hc : (baseChangeDesc p h X).hom.app (op T) ∘ Sheaf.Torsor.contractedProductObjEquiv a =
        Sheaf.Torsor.contractedProductObjEquiv (torsorPoint p h a) ∘ e :=
      funext fun b ↦ by
        simp only [Function.comp_apply, Sheaf.Torsor.contractedProductObjEquiv_apply]
        exact baseChangeDesc_hom_app_contractedProductMk p h X a b
    refine (Function.Bijective.of_comp_iff _
      (Sheaf.Torsor.contractedProductObjEquiv a).bijective).1 ?_
    rw [hc]
    exact (Equiv.bijective _).comp e.bijective

/-- **Base change of the contracted product.** For a `G`-torsor `P` over `S`, a scheme `X` affine
over `S` with an action of `G` and a morphism `p : S' ⟶ S`, the base change of `P ×^G X` to `S'`
is the contracted product of the base changes of `P` and `X`, a torsor under the base change of
`G` (`isTorsor_pullback_obj`) and a scheme with its action. Both represent sheaves on schemes over
`S'`, compared by sending the class of points `(p', x')` to the class of their transposes; this
comparison is bijective over every scheme over which the base change of `P` has a section. -/
def pullbackContractedProductSchemeIso [IsAffineHom X.hom] :
    letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj P) :=
      (Over.pullback p).modObjObj G.X P
    letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
      (Over.pullback p).modObjObj G.X X
    (Over.pullback p).obj ((h.toTorsor.{w}).contractedProductScheme X) ≅
      ((isTorsor_pullback_obj p h).toTorsor.{w}).contractedProductScheme
        ((Over.pullback p).obj X) :=
  letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
    (Over.pullback p).modObjObj G.X X
  ((Over.mapPullbackAdj p).representableByComp
    ((h.toTorsor.{w}).contractedProductSchemeRepresentableBy X)).uniqueUpToIso
      (((baseChangeTorsor.{w} p h).contractedProductSchemeRepresentableBy
        ((Over.pullback p).obj X)).ofIso
          ((sheafToPresheaf _ _).mapIso (asIso (baseChangeDesc p h X))))

/-- The inverse base-change comparison sends the class `[a, b]` of points of the base changes
to the class of their adjoint transposes, viewed as points over `S`. -/
@[simp]
lemma contractedProductSchemeRepresentableBy_homEquiv_pullbackContractedProductSchemeIso_inv
    [IsAffineHom X.hom] {T : Over S'}
    (a : T ⟶ (Over.pullback p).obj P) (b : T ⟶ (Over.pullback p).obj X) :
    letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj P) :=
      (Over.pullback p).modObjObj G.X P
    letI : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
      (Over.pullback p).modObjObj G.X X
    ((h.toTorsor.{w}).contractedProductSchemeRepresentableBy X).homEquiv
      (((Over.mapPullbackAdj p).homEquiv _ _).symm
        ((((isTorsor_pullback_obj p h).toTorsor.{w}).contractedProductSchemeRepresentableBy
          ((Over.pullback p).obj X)).homEquiv.symm
            (Sheaf.Torsor.contractedProductMk
              (((isTorsor_pullback_obj p h).toTorsorSectionEquiv (op T)).symm a)
              ((uliftYonedaMulActionSheafSectionEquiv _ _ (op T)).symm b)) ≫
          (pullbackContractedProductSchemeIso p h X).inv)) =
      Sheaf.Torsor.contractedProductMk
        ((h.toTorsorSectionEquiv _).symm (((Over.mapPullbackAdj p).homEquiv _ _).symm a))
        ((uliftYonedaMulActionSheafSectionEquiv G X _).symm
          (((Over.mapPullbackAdj p).homEquiv _ _).symm b)) := by
  let : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj P) :=
    (Over.pullback p).modObjObj G.X P
  let : ModObj ((Over.pullback p).mapGrp.obj G).X ((Over.pullback p).obj X) :=
    (Over.pullback p).modObjObj G.X X
  rw [← Adjunction.representableByComp_homEquiv_apply, pullbackContractedProductSchemeIso,
    Functor.RepresentableBy.homEquiv_comp_uniqueUpToIso_inv]
  refine (Functor.RepresentableBy.ofIso_homEquiv_apply ..).trans ?_
  rw [Equiv.apply_symm_apply]
  exact (baseChangeDesc_hom_app_contractedProductMk p h X _ _).trans
    (congrArg₂ Sheaf.Torsor.contractedProductMk (torsorPoint_symm p h a) (mulActionPoint_symm p b))

end BaseChange

end TauCeti.GroupScheme
