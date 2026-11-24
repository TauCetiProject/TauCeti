/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Sites.Canonical
public import TauCeti.CategoryTheory.Monoidal.Cartesian.Action
public import TauCeti.CategoryTheory.Sites.Canonical
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Map

/-!
# Torsors under a group object of a site

Let `(C, J)` be a site whose topology is subcanonical, where `C` is cartesian monoidal, and let `G`
be a group object of `C`, for instance a group scheme over a base scheme `S` in `Over S` with the
fppf topology. The functor of points `T ↦ (T ⟶ G)` is a sheaf of groups on `C`, the sheaf of
points `h_G`. This file compares the torsors of `C` itself with the torsors under `h_G` in the
sense of `CategoryTheory.Sheaf.Torsor`.

An object `X` of `C` with an action of `G` is a `G`-torsor for `J`, `J.IsTorsor G X`, when the
morphism `(g, x) ↦ (g • x, x)` from `G ⊗ X` to `X ⊗ X` is an isomorphism and `X` has sections
locally for `J`. Its functor of points is then a torsor under `h_G`, `IsTorsor.toTorsor`, and this
assignment is fully faithful: morphisms of torsors of sheaves are exactly the equivariant
morphisms in `C`. Consequently the classes in `NonabelianH1 h_G` detect isomorphism of torsors of
`C`, the class of `X` is the base point exactly when `X` has a global section, and an equivariant
morphism of torsors is an isomorphism in `C`.

The sheaf of points is taken with values in groups of a universe `max v w` for an arbitrary `w`,
so that its torsors can be sheafified in a large site such as the big fppf site of a scheme;
this is what the functoriality `NonabelianH1.map` along homomorphisms requires.

## Main declarations

* `CategoryTheory.GrothendieckTopology.uliftYonedaGrp`: the functor sending a group object to its
  sheaf of points.
* `CategoryTheory.GrothendieckTopology.IsTorsor`: a torsor of `C` under a group object.
* `CategoryTheory.GrothendieckTopology.IsTorsor.toTorsor`: its functor of points, a torsor under
  the sheaf of points.
* `CategoryTheory.GrothendieckTopology.IsTorsor.toTorsorSectionEquiv`: its sections are the
  morphisms into the torsor.
* `CategoryTheory.GrothendieckTopology.IsTorsor.toTorsorHomEquiv`: morphisms of these sheaf
  torsors are the equivariant morphisms.
* `CategoryTheory.GrothendieckTopology.IsTorsor.isIso_of_isModHom`: equivariant morphisms of
  torsors are isomorphisms.
* `CategoryTheory.GrothendieckTopology.IsTorsor.mk_toTorsor_eq_one_iff`: a torsor is trivial if
  and only if it has a global section.
* `CategoryTheory.GrothendieckTopology.IsTorsor.mk_toTorsor_eq_mk_toTorsor_iff`: two torsors have
  the same class if and only if there is an equivariant morphism between them.
* `CategoryTheory.GrothendieckTopology.IsTorsor.map_mk_toTorsor_eq_mk_toTorsor_iff`: the map on
  torsor classes induced by a homomorphism `φ` of group objects, computed by `φ`-equivariant
  morphisms.
* `CategoryTheory.GrothendieckTopology.isTorsor_self`: a group object is a torsor under itself,
  with the trivial class (`mk_toTorsor_isTorsor_self`); a torsor is equivariantly isomorphic to it
  if and only if it has a global section (`IsTorsor.exists_iso_isModHom_iff`).
* `CategoryTheory.GrothendieckTopology.subsingleton_nonabelianH1_of_isTerminal`: the trivial group
  object has a single torsor class.

## References

* [The Stacks project, Section 21.4 (03AG)](https://stacks.math.columbia.edu/tag/03AG).
* [The Stacks project, Definition 78.9.3 (04TY)](https://stacks.math.columbia.edu/tag/04TY).
* B. Poonen, *Rational points on varieties*, Section 5.12 and Section 6.5.
-/

public section

open CategoryTheory Opposite MonoidalCategory CartesianMonoidalCategory
open scoped MonObj

universe w v u

namespace CategoryTheory

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (J : GrothendieckTopology C) [J.Subcanonical]

/-- The presheaf of groups of points of a group object of a subcanonical site is a sheaf: its
underlying presheaf of sets is representable. -/
theorem isSheaf_yonedaGrp_obj_comp_uliftFunctor (G : Grp C) :
    Presheaf.IsSheaf J (yonedaGrp.obj G ⋙ GrpCat.uliftFunctor.{w, v}) :=
  Presheaf.isSheaf_of_isSheaf_comp J _ (forget GrpCat.{max v w})
    (J.uliftYoneda.{w}.obj G.X).property

/-- The sheaf of points of a group object `G` of a subcanonical site: the sheaf of groups
`T ↦ (T ⟶ G)`, lifted to the universe `max v w`.

Use `uliftYonedaGrpObjEquiv` to identify its sections with morphisms into `G`. -/
noncomputable def uliftYonedaGrp : Grp C ⥤ Sheaf J GrpCat.{max v w} :=
  ObjectProperty.lift _
    (yonedaGrp ⋙ (Functor.whiskeringRight _ _ _).obj GrpCat.uliftFunctor.{w, v})
    (isSheaf_yonedaGrp_obj_comp_uliftFunctor J)

variable {J}

/-- The group of sections of the sheaf of points of `G` over `T` is the group of morphisms
`T ⟶ G`. -/
noncomputable def uliftYonedaGrpObjEquiv (G : Grp C) (T : Cᵒᵖ) :
    (J.uliftYonedaGrp.{w}.obj G).obj.obj T ≃* (unop T ⟶ G.X) :=
  MulEquiv.ulift

/-- Restriction of sections of the sheaf of points is precomposition. -/
@[simp]
lemma uliftYonedaGrpObjEquiv_map (G : Grp C) {T T' : Cᵒᵖ} (f : T ⟶ T')
    (g : (J.uliftYonedaGrp.{w}.obj G).obj.obj T) :
    uliftYonedaGrpObjEquiv G T' ((J.uliftYonedaGrp.{w}.obj G).obj.map f g) =
      f.unop ≫ uliftYonedaGrpObjEquiv G T g :=
  (rfl)

/-- A homomorphism of group objects acts on sections of the sheaves of points by
postcomposition. -/
@[simp]
lemma uliftYonedaGrpObjEquiv_map_hom_app {G H : Grp C} (φ : G ⟶ H) (T : Cᵒᵖ)
    (g : (J.uliftYonedaGrp.{w}.obj G).obj.obj T) :
    uliftYonedaGrpObjEquiv H T ((J.uliftYonedaGrp.{w}.map φ).hom.app T g) =
      uliftYonedaGrpObjEquiv G T g ≫ φ.hom.hom :=
  (rfl)

/-- For the trivial group object, a terminal object of `C`, every torsor under its sheaf of points
is trivial: the torsor classes form a point. -/
lemma subsingleton_nonabelianH1_of_isTerminal {G : Grp C} (hG : Limits.IsTerminal G.X) :
    Subsingleton (Sheaf.NonabelianH1 (J.uliftYonedaGrp.{w}.obj G)) :=
  have (T : Cᵒᵖ) : Subsingleton ((J.uliftYonedaGrp.{w}.obj G).obj.obj T) :=
    ⟨fun _ _ ↦ (uliftYonedaGrpObjEquiv G T).injective (hG.hom_ext _ _)⟩
  inferInstance

variable (J) in
/-- An object `X` of `C` with an action of a group object `G` is a `G`-torsor for the topology
`J` if the morphism `(g, x) ↦ (g • x, x)` from `G ⊗ X` to `X ⊗ X` is an isomorphism and `X` has
sections locally for `J` (Stacks, Definition 78.9.3 (04TY)). -/
structure IsTorsor (G : Grp C) (X : C) [ModObj G.X X] : Prop where
  /-- The action is simply transitive on points with values in every object. -/
  isIso_leftSMul : IsIso (ModObj.leftSMul G.X X)
  /-- The objects over which `X` has a point cover the site. -/
  coversTop : J.CoversTop fun T : {T : C // Nonempty (T ⟶ X)} ↦ T.val

namespace IsTorsor

variable {G : Grp C} {X Y : C} [ModObj G.X X] [ModObj G.X Y]

omit [J.Subcanonical] in
/-- On a torsor, any point is carried to any other point by a unique point of `G`. -/
lemma existsUnique_smul_eq (h : J.IsTorsor G X) {T : C} (x y : T ⟶ X) :
    ∃! g : T ⟶ G.X, g • x = y :=
  (ModObj.isIso_leftSMul_iff (M := G.X) (X := X)).1 h.isIso_leftSMul T x y

/-- The functor of points of a torsor `X` under `G`, a torsor under the sheaf of points of `G`:
the sections over `T` are the morphisms `T ⟶ X`, on which `T ⟶ G` acts through the action of
`G` on `X`.

Use `toTorsorSectionEquiv` to identify its sections with morphisms into `X`, and
`toTorsorSectionEquiv_map` and `toTorsorSectionEquiv_smul` for restriction and the action. -/
noncomputable def toTorsor (h : J.IsTorsor G X) :
    Sheaf.Torsor (J.uliftYonedaGrp.{w}.obj G) where
  sheaf := J.uliftYoneda.{w}.obj X
  mulAction T :=
    { smul g x := ULift.up (uliftYonedaGrpObjEquiv G T g • (ULift.down (α := unop T ⟶ X) x))
      one_smul x := congrArg ULift.up (one_smul _ (ULift.down (α := unop T ⟶ X) x))
      mul_smul g g' x := congrArg ULift.up (mul_smul (uliftYonedaGrpObjEquiv G T g)
        (uliftYonedaGrpObjEquiv G T g') (ULift.down (α := unop T ⟶ X) x)) }
  map_smul T T' f g x :=
    congrArg ULift.up (ModObj.comp_smul f.unop _ (ULift.down (α := unop T ⟶ X) x))
  coversTop Z := J.superset_covering (by
    rintro T a ⟨⟨T', ⟨x⟩⟩, ⟨b⟩⟩
    exact ⟨⟨T', ⟨ULift.up x⟩⟩, ⟨b⟩⟩) (h.coversTop Z)
  bijective T := by
    refine ⟨fun ⟨g, x⟩ ⟨g', x'⟩ hgx ↦ ?_, fun ⟨y, x⟩ ↦ ?_⟩
    · obtain ⟨hg, rfl⟩ := Prod.ext_iff.1 hgx
      refine Prod.ext ((uliftYonedaGrpObjEquiv G T).injective ?_) rfl
      exact (h.existsUnique_smul_eq x.down _).unique rfl (congrArg ULift.down hg).symm
    · obtain ⟨g, hg, -⟩ := h.existsUnique_smul_eq x.down y.down
      exact ⟨((uliftYonedaGrpObjEquiv G T).symm g, x), Prod.ext (congrArg ULift.up
        (by rwa [MulEquiv.apply_symm_apply])) rfl⟩

variable (h : J.IsTorsor G X)

/-- The underlying sheaf of the torsor of points of `X` is the sheaf represented by `X`. -/
lemma toTorsor_sheaf : h.toTorsor.sheaf = J.uliftYoneda.{w}.obj X :=
  (rfl)

/-- The sections over `T` of the torsor of points of `X` are the morphisms `T ⟶ X`. -/
noncomputable def toTorsorSectionEquiv (T : Cᵒᵖ) :
    (toTorsor.{w} h).sheaf.obj.obj T ≃ (unop T ⟶ X) :=
  Equiv.ulift

/-- Restriction of sections of the torsor of points is precomposition. -/
@[simp]
lemma toTorsorSectionEquiv_map {T T' : Cᵒᵖ} (f : T ⟶ T') (x : (toTorsor.{w} h).sheaf.obj.obj T) :
    h.toTorsorSectionEquiv T' ((toTorsor.{w} h).sheaf.obj.map f x) =
      f.unop ≫ h.toTorsorSectionEquiv T x :=
  (rfl)

/-- A point `g : T ⟶ G` acts on a point `x : T ⟶ X` by the action of `G` on `X`. -/
@[simp]
lemma toTorsorSectionEquiv_smul {T : Cᵒᵖ} (g : (J.uliftYonedaGrp.{w}.obj G).obj.obj T)
    (x : (toTorsor.{w} h).sheaf.obj.obj T) :
    h.toTorsorSectionEquiv T (g • x) = uliftYonedaGrpObjEquiv G T g • h.toTorsorSectionEquiv T x :=
  (rfl)

variable (h' : J.IsTorsor G Y)

/-- Morphisms between the torsors of points of two torsors `X` and `Y` under `G` are the
`G`-equivariant morphisms `X ⟶ Y`. -/
noncomputable def toTorsorHomEquiv :
    (toTorsor.{w} h ⟶ h'.toTorsor) ≃ {f : X ⟶ Y // IsModHom G.X f} where
  toFun F := ⟨J.fullyFaithfulUliftYoneda.preimage F.hom, (TauCeti.isModHom_iff_map_smul _).2
    fun T g x ↦ (down_hom_app_up_eq_comp_preimage F.hom (g • x)).symm.trans <|
      (congrArg ULift.down
        (F.map_smul (op T) ((uliftYonedaGrpObjEquiv G (op T)).symm g) (ULift.up x))).trans
          (congrArg (g • ·) (down_hom_app_up_eq_comp_preimage F.hom x))⟩
  invFun f :=
    haveI := f.property
    ⟨J.uliftYoneda.map f.val, fun T g x ↦ congrArg ULift.up (IsModHom.map_smul f.val _ x.down)⟩
  left_inv F := by
    ext1
    exact J.fullyFaithfulUliftYoneda.map_preimage F.hom
  right_inv f := Subtype.ext (J.fullyFaithfulUliftYoneda.{w}.preimage_map f.val)

/-- The morphism of torsors of points coming from an equivariant morphism `f` acts on sections
by composition with `f`. -/
@[simp]
lemma toTorsorSectionEquiv_toTorsorHomEquiv_symm_apply (f : {f : X ⟶ Y // IsModHom G.X f})
    {T : Cᵒᵖ} (x : (toTorsor.{w} h).sheaf.obj.obj T) :
    h'.toTorsorSectionEquiv T (((toTorsorHomEquiv.{w} h h').symm f).hom.hom.app T x) =
      h.toTorsorSectionEquiv T x ≫ f.val :=
  (rfl)

/-- A morphism `F` of torsors of points acts on sections by composition with the equivariant
morphism `toTorsorHomEquiv h h' F` it comes from. -/
lemma toTorsorSectionEquiv_hom_app (F : toTorsor.{w} h ⟶ h'.toTorsor) {T : Cᵒᵖ}
    (x : (toTorsor.{w} h).sheaf.obj.obj T) :
    h'.toTorsorSectionEquiv T (F.hom.hom.app T x) =
      h.toTorsorSectionEquiv T x ≫ (toTorsorHomEquiv h h' F).val :=
  down_hom_app_up_eq_comp_preimage F.hom (h.toTorsorSectionEquiv T x)

/-- A `G`-equivariant morphism of torsors under `G` is an isomorphism. -/
lemma isIso_of_isModHom (h : J.IsTorsor G X) (h' : J.IsTorsor G Y) (f : X ⟶ Y)
    [IsModHom G.X f] : IsIso f := by
  have : IsIso (J.uliftYoneda.{0}.map f) :=
    Sheaf.Torsor.isIso_hom ((toTorsorHomEquiv.{0} h h').symm ⟨f, ‹_›⟩)
  exact isIso_of_fully_faithful J.uliftYoneda.{0} f

/-- Two torsors under `G` have the same class if and only if there is a `G`-equivariant
morphism between them, which is then an isomorphism by `isIso_of_isModHom`. -/
lemma mk_toTorsor_eq_mk_toTorsor_iff :
    Sheaf.NonabelianH1.mk (toTorsor.{w} h) = Sheaf.NonabelianH1.mk h'.toTorsor ↔
      ∃ f : X ⟶ Y, IsModHom G.X f := by
  rw [Sheaf.NonabelianH1.mk_eq_mk_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨_, (toTorsorHomEquiv h h' e.hom).property⟩,
    fun ⟨f, hf⟩ ↦ ⟨asIso ((toTorsorHomEquiv h h').symm ⟨f, hf⟩)⟩⟩

/-- A torsor under `G` has the trivial class if and only if it has a global section
(Stacks, Lemma 21.4.2 (03AI)). -/
lemma mk_toTorsor_eq_one_iff :
    Sheaf.NonabelianH1.mk (toTorsor.{w} h) = 1 ↔ Nonempty (𝟙_ C ⟶ X) :=
  (Sheaf.NonabelianH1.mk_eq_one_iff _).trans
    (J.nonempty_sections_uliftYoneda_obj_iff isTerminalTensorUnit)

section Functoriality

variable {H : Grp C} {Y : C} [ModObj H.X Y]
  [HasWeakSheafify J (Type (max v w))] [J.WEqualsLocallyBijective (Type (max v w))]

/-- Let `φ : G ⟶ H` be a homomorphism of group objects, `X` a torsor under `G` and `Y` a torsor
under `H`. The map induced by `φ` on torsor classes sends the class of `X` to the class of `Y`
if and only if there is a `φ`-equivariant morphism `X ⟶ Y`, that is, the class of the
contracted product `X ×^G H` is that of `Y` exactly when `Y` receives such a morphism. -/
lemma map_mk_toTorsor_eq_mk_toTorsor_iff (φ : G ⟶ H) (hY : J.IsTorsor H Y) :
    Sheaf.NonabelianH1.map (J.uliftYonedaGrp.{w}.map φ) (Sheaf.NonabelianH1.mk (toTorsor.{w} h)) =
        Sheaf.NonabelianH1.mk (toTorsor.{w} hY) ↔
      ∃ f : X ⟶ Y, ∀ (T : C) (g : T ⟶ G.X) (x : T ⟶ X),
        (g • x) ≫ f = (g ≫ φ.hom.hom) • (x ≫ f) := by
  rw [Sheaf.NonabelianH1.map_mk_eq_mk_iff]
  refine ⟨fun ⟨u, hu⟩ ↦ ⟨J.fullyFaithfulUliftYoneda.preimage u, fun T g x ↦ ?_⟩,
    fun ⟨f, hf⟩ ↦ ⟨J.uliftYoneda.map f, fun T g x ↦ congrArg ULift.up (hf _ _ _)⟩⟩
  exact (down_hom_app_up_eq_comp_preimage u (g • x)).symm.trans <| (congrArg ULift.down
    (hu (op T) ((uliftYonedaGrpObjEquiv G (op T)).symm g) (ULift.up x))).trans
      (congrArg ((g ≫ φ.hom.hom) • ·) (down_hom_app_up_eq_comp_preimage u x))

/-- A `φ`-equivariant morphism from a torsor `X` under `G` to a torsor `Y` under `H` identifies
the image of the class of `X` under the map induced by `φ` with the class of `Y`. -/
lemma map_mk_toTorsor_eq_mk_toTorsor (φ : G ⟶ H) (hY : J.IsTorsor H Y) (f : X ⟶ Y)
    (hf : ∀ (T : C) (g : T ⟶ G.X) (x : T ⟶ X), (g • x) ≫ f = (g ≫ φ.hom.hom) • (x ≫ f)) :
    Sheaf.NonabelianH1.map (J.uliftYonedaGrp.{w}.map φ) (Sheaf.NonabelianH1.mk (toTorsor.{w} h)) =
      Sheaf.NonabelianH1.mk (toTorsor.{w} hY) :=
  (map_mk_toTorsor_eq_mk_toTorsor_iff h φ hY).2 ⟨f, hf⟩

end Functoriality

end IsTorsor

section Self

attribute [local instance] ModObj.regular

omit [J.Subcanonical] in
variable (J) in
/-- A group object is a torsor under itself, acting by left multiplication. -/
lemma isTorsor_self (G : Grp C) : J.IsTorsor G G.X where
  isIso_leftSMul := (ModObj.isIso_leftSMul_iff (M := G.X) (X := G.X)).2 fun T x y ↦
    ⟨y * x⁻¹, by simp,
      fun g hg ↦ eq_mul_inv_of_mul_eq (by simpa [Hom.smul_def, ← Hom.mul_def] using hg)⟩
  coversTop Z :=
    J.superset_covering (fun T _ _ ↦ ⟨⟨T, ⟨toUnit T ≫ η⟩⟩, ⟨𝟙 T⟩⟩) (J.top_mem Z)

/-- The class of a group object acting on itself is the base point of the torsor classes. -/
@[simp]
lemma mk_toTorsor_isTorsor_self (G : Grp C) :
    Sheaf.NonabelianH1.mk (IsTorsor.toTorsor.{w} (J.isTorsor_self G)) = 1 :=
  (IsTorsor.mk_toTorsor_eq_one_iff _).2 ⟨η⟩

omit [J.Subcanonical] in
/-- A torsor `X` under `G` is isomorphic to `G` acting on itself by a `G`-equivariant
isomorphism if and only if `X` has a global section `x`; the isomorphism is then the orbit
morphism `g ↦ g • x`. This holds for every topology `J`. -/
lemma IsTorsor.exists_iso_isModHom_iff {G : Grp C} {X : C} [ModObj G.X X]
    (h : J.IsTorsor G X) :
    (∃ e : G.X ≅ X, IsModHom G.X e.hom) ↔ Nonempty (𝟙_ C ⟶ X) := by
  refine ⟨fun ⟨e, _⟩ ↦ ⟨η ≫ e.hom⟩, fun ⟨x⟩ ↦ ?_⟩
  have : IsIso (TauCeti.orbitMap G.X x) := by
    rw [isIso_iff_yoneda_map_bijective]
    refine fun T ↦ ⟨fun g g' hg ↦ ?_, fun y ↦ ?_⟩
    · simp only [TauCeti.comp_orbitMap] at hg
      exact (h.existsUnique_smul_eq (toUnit T ≫ x) _).unique hg rfl
    · obtain ⟨g, hg, -⟩ := h.existsUnique_smul_eq (toUnit T ≫ x) y
      exact ⟨g, by simpa using hg⟩
  exact ⟨asIso (TauCeti.orbitMap G.X x), ⟨TauCeti.mul_orbitMap G.X x⟩⟩

end Self

end GrothendieckTopology

end CategoryTheory
