/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.Topology.Sheaves.Stalks
public import TauCeti.Topology.Sheaves.Cohomology.Instances
public import TauCeti.Topology.Sheaves.LocallyConstant.Basic
import Mathlib.Topology.Sheaves.Sheafify

/-!
# The sheaf of locally constant functions valued in an abelian group

For a topological space `X` and an additive commutative group `A`, the locally constant `A`-valued
functions on open subsets of `X` form a sheaf of abelian groups
`TopCat.locallyConstantAddCommGrpSheaf X A : X.Sheaf AddCommGrpCat`. Over an open `U`, its group of
sections is `LocallyConstant U A`, with restriction given by `LocallyConstant.comapAddMonoidHom`.

This gives the concrete model of the constant sheaf `A_X` used in differential-geometric exact
sequences such as the smooth exponential sequence `0 ⟶ ℤ_M ⟶ C^∞_M(ℝ) ⟶ C^∞_M(S¹) ⟶ 0`:

* Its stalk at any point `x : X` is canonically `A` via evaluation at `x`
  (`TopCat.locallyConstantAddCommGrpStalkIso`).
* Sheafifying the constant presheaf `(Functor.const _).obj (AddCommGrpCat.of A)` along the
  inclusion of constant functions produces a canonical isomorphism with Mathlib's
  `CategoryTheory.constantSheaf` (`TopCat.constantSheafIsoLocallyConstantAddCommGrpSheaf`), natural
  in `A` (`TopCat.constantSheafNatIsoLocallyConstantAddCommGrpSheaf`), so
  `TopCat.locallyConstantAddCommGrpSheaf X A` satisfies `CategoryTheory.Sheaf.IsConstant` and has
  the same sheaf cohomology `Sheaf.H` as `constantSheaf`.
* Over a nonempty connected open `U`, evaluation at any basepoint identifies the sections over `U`
  with `A` (`TopCat.locallyConstantAddCommGrpSectionsAddEquiv`).
* For a ring `R`, forgetting multiplication sends `TopCat.locallyConstantRingCatSheaf X R` to
  `TopCat.locallyConstantAddCommGrpSheaf X R`.

## Main definitions

* `TopCat.locallyConstantAddCommGrpPresheaf X A`: the presheaf `U ↦ LocallyConstant U A` in
  `AddCommGrpCat`.
* `TopCat.locallyConstantAddCommGrpSheaf X A`: the sheaf of locally constant `A`-valued functions.
* `TopCat.locallyConstantAddCommGrpSheafFunctor X`: functoriality
  `AddCommGrpCat ⥤ X.Sheaf AddCommGrpCat`.
* `TopCat.locallyConstantAddCommGrpStalkIso`: stalk isomorphism `(A_X)_x ≅ A`.
* `TopCat.constantSheafNatIsoLocallyConstantAddCommGrpSheaf`: natural isomorphism between
  `constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat` and
  `locallyConstantAddCommGrpSheafFunctor X`.
-/

public noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u

namespace TopCat

variable (X : TopCat.{u}) (A : Type u) [AddCommGroup A]

/-- The presheaf of abelian groups of locally constant `A`-valued functions on `X`. -/
@[expose] def locallyConstantAddCommGrpPresheaf : X.Presheaf AddCommGrpCat.{u} where
  obj U := AddCommGrpCat.of (LocallyConstant U.unop A)
  map i := AddCommGrpCat.ofHom
    (LocallyConstant.comapAddMonoidHom ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩)

@[simp]
theorem locallyConstantAddCommGrpPresheaf_obj (U : (Opens X)ᵒᵖ) :
    (locallyConstantAddCommGrpPresheaf X A).obj U = AddCommGrpCat.of (LocallyConstant U.unop A) :=
  rfl

variable {X A} in
@[simp]
theorem locallyConstantAddCommGrpPresheaf_map_apply {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (f : LocallyConstant U.unop A) :
    dsimp% ((locallyConstantAddCommGrpPresheaf X A).map i f =
      f.comap ⟨Set.inclusion i.unop.le, continuous_inclusion i.unop.le⟩) :=
  rfl

/-- Locally constant functions valued in an abelian group satisfy the sheaf gluing condition. -/
theorem isSheaf_locallyConstantAddCommGrpPresheaf :
    (locallyConstantAddCommGrpPresheaf X A).IsSheaf := by
  refine (Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr fun ι U sf hsf ↦ ?_
  -- View each section `sf i` as `LocallyConstant (U i) A` so coercion to functions applies.
  change ∀ i, LocallyConstant (U i) A at sf
  have hmem (x : ↥(iSup U)) : ∃ i, x.1 ∈ U i := Opens.mem_iSup.mp x.2
  let g : ↥(iSup U) → A := fun x ↦ sf (hmem x).choose ⟨x, (hmem x).choose_spec⟩
  have hg (i : ι) (x : ↥(iSup U)) (hx : x.1 ∈ U i) : g x = sf i ⟨x, hx⟩ :=
    DFunLike.congr_fun (F := LocallyConstant ↥(U (hmem x).choose ⊓ U i) A)
      (hsf (hmem x).choose i) ⟨x, (hmem x).choose_spec, hx⟩
  have hj (i : ι) : Topology.IsOpenEmbedding
      (Set.inclusion (Opens.leSupr U i).le : U i → ↥(iSup U)) :=
    .inclusion _ ((U i).isOpen.preimage continuous_subtype_val)
  have hgc : IsLocallyConstant g := by
    refine (IsLocallyConstant.iff_eventually_eq g).mpr fun x ↦ ?_
    obtain ⟨i, hx⟩ := hmem x
    rw [← Set.inclusion_right (Opens.leSupr U i).le x hx, ← (hj i).map_nhds_eq,
      Filter.eventually_map]
    filter_upwards [(IsLocallyConstant.iff_eventually_eq _).mp (sf i).isLocallyConstant
      ⟨x, hx⟩] with z hz
    rw [hg i _ z.2, hg i _ hx]
    exact hz
  refine ⟨(⟨g, hgc⟩ : LocallyConstant ↥(iSup U) A), fun i ↦ ?_, fun t ht ↦ ?_⟩
  · exact LocallyConstant.ext fun x ↦ hg i ⟨x.1, (Opens.leSupr U i).le x.2⟩ x.2
  · refine LocallyConstant.ext fun x ↦ ?_
    obtain ⟨i, hx⟩ := hmem x
    exact (DFunLike.congr_fun (F := LocallyConstant (U i) A) (ht i) ⟨x, hx⟩).trans (hg i x hx).symm

/-- The sheaf `A_X` of locally constant `A`-valued functions on `X`, valued in `AddCommGrpCat`. -/
@[expose] def locallyConstantAddCommGrpSheaf : X.Sheaf AddCommGrpCat.{u} :=
  ⟨locallyConstantAddCommGrpPresheaf X A, isSheaf_locallyConstantAddCommGrpPresheaf X A⟩

@[simp]
theorem locallyConstantAddCommGrpSheaf_presheaf :
    (locallyConstantAddCommGrpSheaf X A).presheaf = locallyConstantAddCommGrpPresheaf X A :=
  (rfl)

theorem locallyConstantAddCommGrpSheaf_obj :
    (locallyConstantAddCommGrpSheaf X A).obj = locallyConstantAddCommGrpPresheaf X A :=
  (rfl)

section Functoriality

variable {A} {B C : Type u} [AddCommGroup B] [AddCommGroup C]

/-- Postcomposition of locally constant sections with an additive group homomorphism, as a morphism
of presheaves of abelian groups. -/
private def locallyConstantAddCommGrpPresheafMap (φ : A →+ B) :
    locallyConstantAddCommGrpPresheaf X A ⟶ locallyConstantAddCommGrpPresheaf X B where
  app _ := AddCommGrpCat.ofHom (LocallyConstant.mapAddMonoidHom φ)
  naturality {_ _} _ := by ext; rfl

/-- Postcomposition of locally constant sections with an additive group homomorphism, as a morphism
of sheaves of abelian groups. -/
def locallyConstantAddCommGrpSheafMap (φ : A →+ B) :
    locallyConstantAddCommGrpSheaf X A ⟶ locallyConstantAddCommGrpSheaf X B :=
  ObjectProperty.homMk (locallyConstantAddCommGrpPresheafMap X φ)

@[simp]
theorem locallyConstantAddCommGrpSheafMap_app_apply (φ : A →+ B) (U : (Opens X)ᵒᵖ)
    (f : LocallyConstant U.unop A) :
    (locallyConstantAddCommGrpSheafMap X φ).hom.app U f = f.map φ :=
  (rfl)

@[simp]
theorem locallyConstantAddCommGrpSheafMap_id :
    locallyConstantAddCommGrpSheafMap X (AddMonoidHom.id A) = 𝟙 _ := by
  ext
  rfl

@[simp]
theorem locallyConstantAddCommGrpSheafMap_comp (φ : A →+ B) (ψ : B →+ C) :
    locallyConstantAddCommGrpSheafMap X (ψ.comp φ) =
      locallyConstantAddCommGrpSheafMap X φ ≫ locallyConstantAddCommGrpSheafMap X ψ := by
  ext
  rfl

/-- Forming the sheaf of locally constant functions on `X`, as a functor
`AddCommGrpCat ⥤ X.Sheaf AddCommGrpCat`. -/
@[expose] def locallyConstantAddCommGrpSheafFunctor :
    AddCommGrpCat.{u} ⥤ X.Sheaf AddCommGrpCat.{u} where
  obj M := locallyConstantAddCommGrpSheaf X M
  map φ := locallyConstantAddCommGrpSheafMap X φ.hom
  map_id _ := locallyConstantAddCommGrpSheafMap_id X
  map_comp φ ψ := locallyConstantAddCommGrpSheafMap_comp X φ.hom ψ.hom

@[simp]
theorem locallyConstantAddCommGrpSheafFunctor_obj (M : AddCommGrpCat.{u}) :
    (locallyConstantAddCommGrpSheafFunctor X).obj M = locallyConstantAddCommGrpSheaf X M :=
  (rfl)

@[simp]
theorem locallyConstantAddCommGrpSheafFunctor_map {M N : AddCommGrpCat.{u}} (φ : M ⟶ N) :
    (locallyConstantAddCommGrpSheafFunctor X).map φ = locallyConstantAddCommGrpSheafMap X φ.hom :=
  (rfl)

end Functoriality

section RingForget

/-- Forgetting multiplication on the sheaf of locally constant `R`-valued functions produces the
abelian group sheaf of locally constant `R`-valued functions. -/
theorem sheafCompose_forget₂_locallyConstantRingCatSheaf (R : Type u) [Ring R] :
    (sheafCompose (Opens.grothendieckTopology X) (forget₂ RingCat.{u} AddCommGrpCat.{u})).obj
      (locallyConstantRingCatSheaf X R) = locallyConstantAddCommGrpSheaf X R :=
  (rfl)

end RingForget

section Stalks

variable {X A}

private def locallyConstantAddCommGrpStalkEval (x : X) :
    (locallyConstantAddCommGrpPresheaf X A).stalk x ⟶ AddCommGrpCat.of A :=
  colimit.desc ((OpenNhds.inclusion x).op ⋙ locallyConstantAddCommGrpPresheaf X A)
    { pt := AddCommGrpCat.of A
      ι :=
        { app := fun U ↦ AddCommGrpCat.ofHom (LocallyConstant.evalAddMonoidHom ⟨x, U.unop.2⟩)
          naturality := fun _ _ _ ↦ by ext; rfl } }

private theorem locallyConstantAddCommGrpStalkEval_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (f : LocallyConstant U A) :
    locallyConstantAddCommGrpStalkEval x
        ((locallyConstantAddCommGrpPresheaf X A).germ U x hx f) = f ⟨x, hx⟩ :=
  ConcreteCategory.congr_hom
    (colimit.ι_desc (F := (OpenNhds.inclusion x).op ⋙ locallyConstantAddCommGrpPresheaf X A)
      _ (op ⟨U, hx⟩)) f

/-- The germ of a locally constant `A`-valued function at `x` equals the germ of the global constant
function with value `f x`. -/
theorem germ_locallyConstantAddCommGrp_eq_const (x : X) (U : Opens X) (hx : x ∈ U)
    (f : LocallyConstant U A) :
    (locallyConstantAddCommGrpPresheaf X A).germ U x hx f =
      (locallyConstantAddCommGrpPresheaf X A).germ ⊤ x (by trivial)
        (LocallyConstant.const _ (f ⟨x, hx⟩)) := by
  obtain ⟨V, hV, hxV, hf⟩ := f.isLocallyConstant.exists_open ⟨x, hx⟩
  let W : Opens X := ⟨Subtype.val '' V, U.isOpen.isOpenMap_subtype_val _ hV⟩
  have hWU : W ≤ U := by rintro _ ⟨y, -, rfl⟩; exact y.2
  have hxW : x ∈ W := ⟨⟨x, hx⟩, hxV, rfl⟩
  have he : (locallyConstantAddCommGrpPresheaf X A).map (homOfLE hWU).op f =
      (locallyConstantAddCommGrpPresheaf X A).map (homOfLE (le_top : W ≤ ⊤)).op
        (LocallyConstant.const _ (f ⟨x, hx⟩)) :=
    LocallyConstant.ext fun ⟨_, z, hz, rfl⟩ ↦ hf z hz
  exact (Presheaf.germ_res_apply (locallyConstantAddCommGrpPresheaf X A)
    (homOfLE hWU) x hxW f).symm.trans
    ((congrArg ((locallyConstantAddCommGrpPresheaf X A).germ W x hxW) he).trans
      (Presheaf.germ_res_apply _ (homOfLE (le_top : W ≤ ⊤)) x hxW _))

/-- Evaluation at `x` identifies the stalk `(A_X)_x` of `locallyConstantAddCommGrpSheaf X A` with
`A`; its inverse takes `a : A` to the germ of the constant function `a`. -/
def locallyConstantAddCommGrpStalkIso (x : X) :
    (locallyConstantAddCommGrpPresheaf X A).stalk x ≅ AddCommGrpCat.of A where
  hom := locallyConstantAddCommGrpStalkEval x
  inv := AddCommGrpCat.ofHom
      (LocallyConstant.constAddMonoidHom : A →+ LocallyConstant (⊤ : Opens X) A) ≫
    (locallyConstantAddCommGrpPresheaf X A).germ ⊤ x (by trivial)
  hom_inv_id := by
    refine Presheaf.stalk_hom_ext _ fun U hx ↦ ?_
    ext f
    exact (congrArg (fun a : A ↦ (locallyConstantAddCommGrpPresheaf X A).germ ⊤ x
      (by trivial) (LocallyConstant.const _ a))
      (locallyConstantAddCommGrpStalkEval_germ x U hx f)).trans
        (germ_locallyConstantAddCommGrp_eq_const x U hx f).symm
  inv_hom_id := by
    ext a
    exact locallyConstantAddCommGrpStalkEval_germ x ⊤ (by trivial) (LocallyConstant.const _ a)

@[simp]
theorem locallyConstantAddCommGrpStalkIso_hom_germ (x : X) (U : Opens X) (hx : x ∈ U)
    (f : LocallyConstant U A) :
    dsimp% ((locallyConstantAddCommGrpStalkIso (A := A) x).hom
      ((locallyConstantAddCommGrpPresheaf X A).germ U x hx f) = f ⟨x, hx⟩) :=
  locallyConstantAddCommGrpStalkEval_germ x U hx f

@[simp]
theorem locallyConstantAddCommGrpStalkIso_inv_apply (x : X) (a : A) :
    (locallyConstantAddCommGrpStalkIso (A := A) x).inv a =
      (locallyConstantAddCommGrpPresheaf X A).germ ⊤ x (by trivial)
        (LocallyConstant.const _ a) :=
  (rfl)

/-- Two locally constant sections have the same germ at `x` if and only if their values at `x`
agree. -/
@[simp]
theorem germ_locallyConstantAddCommGrp_eq_iff (x : X) {U V : Opens X} (hxU : x ∈ U) (hxV : x ∈ V)
    (f : LocallyConstant U A) (g : LocallyConstant V A) :
    dsimp% ((locallyConstantAddCommGrpPresheaf X A).germ U x hxU f =
      (locallyConstantAddCommGrpPresheaf X A).germ V x hxV g) ↔ f ⟨x, hxU⟩ = g ⟨x, hxV⟩ := by
  constructor
  · intro h
    exact (locallyConstantAddCommGrpStalkIso_hom_germ x U hxU f).symm.trans
      ((congrArg (locallyConstantAddCommGrpStalkIso (A := A) x).hom h).trans
        (locallyConstantAddCommGrpStalkIso_hom_germ x V hxV g))
  · intro h
    exact (germ_locallyConstantAddCommGrp_eq_const x U hxU f).trans
      ((congrArg (fun a : A ↦ (locallyConstantAddCommGrpPresheaf X A).germ ⊤ x
        (by trivial) (LocallyConstant.const _ a)) h).trans
          (germ_locallyConstantAddCommGrp_eq_const x V hxV g).symm)

end Stalks

section ConstantSheafComparison

/-- Inclusion of constant `A`-valued sections into locally constant `A`-valued sections. -/
private def constToLocallyConstantAddCommGrpPresheaf (M : AddCommGrpCat.{u}) :
    (Functor.const (Opens X)ᵒᵖ).obj M ⟶ locallyConstantAddCommGrpPresheaf X M where
  app U := AddCommGrpCat.ofHom (LocallyConstant.constAddMonoidHom : M →+ LocallyConstant U.unop M)
  naturality _ _ _ := by ext; rfl

/-- Sheafified presheaf morphism from `sheafify` of the constant presheaf to
`locallyConstantAddCommGrpPresheaf`. -/
private def sheafifyConstToLocallyConstantAddCommGrpPresheaf (M : AddCommGrpCat.{u}) :
    CategoryTheory.sheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj M) ⟶
      locallyConstantAddCommGrpPresheaf X M :=
  CategoryTheory.sheafifyLift (Opens.grothendieckTopology X)
    (constToLocallyConstantAddCommGrpPresheaf X M)
    (isSheaf_locallyConstantAddCommGrpPresheaf X M)

/-- Sheafified morphism from `constantSheaf` to `locallyConstantAddCommGrpSheaf`. -/
private def constantSheafToLocallyConstantAddCommGrpSheaf (M : AddCommGrpCat.{u}) :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj M ⟶
      locallyConstantAddCommGrpSheaf X M :=
  ObjectProperty.homMk (sheafifyConstToLocallyConstantAddCommGrpPresheaf X M)

private lemma isIso_stalkFunctor_map_constToLocallyConstant (M : AddCommGrpCat.{u}) (x : X) :
    IsIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (constToLocallyConstantAddCommGrpPresheaf X M)) := by
  let P : X.Presheaf AddCommGrpCat.{u} := (Functor.const (Opens X)ᵒᵖ).obj M
  let α := constToLocallyConstantAddCommGrpPresheaf X M
  let eStalk :
      (Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj
        (locallyConstantAddCommGrpPresheaf X M) ≅ M :=
    locallyConstantAddCommGrpStalkIso (X := X) (A := M) x
  let gTop : M ⟶ (Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj P :=
    P.germ ⊤ x (by trivial)
  have hg_eq (U : Opens X) (hx : x ∈ U) (m : M) : P.germ U x hx m = gTop m :=
    P.germ_res_apply (homOfLE (le_top : U ≤ ⊤)) x hx m
  have hcomp : IsIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α ≫ eStalk.hom) := by
    refine ⟨⟨gTop, ?_, ?_⟩⟩
    · apply ConcreteCategory.ext_apply
      intro s
      obtain ⟨U, hxU, m, rfl⟩ := P.exists_germ_eq s
      have h1 : eStalk.hom (((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α)
          (P.germ U x hxU m)) = m := by
        have h2 : ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α) (P.germ U x hxU m) =
            (locallyConstantAddCommGrpPresheaf X M).germ U x hxU (α.app (op U) m) :=
          Presheaf.stalkFunctor_map_germ_apply U x hxU α m
        exact (congrArg eStalk.hom h2).trans
          (locallyConstantAddCommGrpStalkIso_hom_germ x U hxU (α.app (op U) m))
      exact (congrArg gTop h1).trans (hg_eq U hxU m).symm
    · apply ConcreteCategory.ext_apply
      intro m
      have h1 : ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α) (gTop m) =
          (locallyConstantAddCommGrpPresheaf X M).germ ⊤ x (by trivial) (α.app (op ⊤) m) :=
        Presheaf.stalkFunctor_map_germ_apply ⊤ x (by trivial) α m
      exact (congrArg eStalk.hom h1).trans
        (locallyConstantAddCommGrpStalkIso_hom_germ x ⊤ (by trivial) (α.app (op ⊤) m))
  exact IsIso.of_isIso_comp_right ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α) eStalk.hom

private instance isIso_constantSheafToLocallyConstantAddCommGrpSheaf (M : AddCommGrpCat.{u}) :
    IsIso (constantSheafToLocallyConstantAddCommGrpSheaf X M) := by
  have hstalk (x : X) :
      IsIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (constantSheafToLocallyConstantAddCommGrpSheaf X M).hom) := by
    have hfac :
        (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
              ((Functor.const (Opens X)ᵒᵖ).obj M)) ≫
          (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
            (sheafifyConstToLocallyConstantAddCommGrpPresheaf X M) =
        (Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
          (constToLocallyConstantAddCommGrpPresheaf X M) := by
      rw [← Functor.map_comp]
      exact congrArg ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map)
        (CategoryTheory.toSheafify_sheafifyLift (Opens.grothendieckTopology X)
          (constToLocallyConstantAddCommGrpPresheaf X M)
          (isSheaf_locallyConstantAddCommGrpPresheaf X M))
    have h₁ : IsIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          ((Functor.const (Opens X)ᵒᵖ).obj M))) :=
      Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
    have h₂ : IsIso ((Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
        (constToLocallyConstantAddCommGrpPresheaf X M)) :=
      isIso_stalkFunctor_map_constToLocallyConstant X M x
    exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _ h₁ h₂ hfac
  exact Presheaf.isIso_of_stalkFunctor_map_iso (constantSheafToLocallyConstantAddCommGrpSheaf X M)

private lemma sheafifyConstToLocallyConstant_naturality {M N : AddCommGrpCat.{u}} (φ : M ⟶ N) :
    CategoryTheory.sheafifyMap (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).map φ) ≫
        sheafifyConstToLocallyConstantAddCommGrpPresheaf X N =
      sheafifyConstToLocallyConstantAddCommGrpPresheaf X M ≫
        locallyConstantAddCommGrpPresheafMap X φ.hom := by
  apply CategoryTheory.sheafify_hom_ext _ _ _ (isSheaf_locallyConstantAddCommGrpPresheaf X N)
  dsimp only [sheafifyConstToLocallyConstantAddCommGrpPresheaf]
  rw [← CategoryTheory.toSheafify_naturality_assoc,
    CategoryTheory.toSheafify_sheafifyLift,
    ← Category.assoc, CategoryTheory.toSheafify_sheafifyLift]
  ext U m
  rfl

/-- Natural isomorphism between Mathlib's `CategoryTheory.constantSheaf` functor and the sheaf of
locally constant functions `locallyConstantAddCommGrpSheafFunctor X`. -/
def constantSheafNatIsoLocallyConstantAddCommGrpSheaf :
    constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≅
      locallyConstantAddCommGrpSheafFunctor X :=
  NatIso.ofComponents
    (fun M ↦ @asIso _ _ _ _ (constantSheafToLocallyConstantAddCommGrpSheaf X M)
      (isIso_constantSheafToLocallyConstantAddCommGrpSheaf X M))
    fun {_ _} φ ↦ ObjectProperty.hom_ext _ (sheafifyConstToLocallyConstant_naturality X φ)

/-- Canonical isomorphism between `(constantSheaf _ AddCommGrpCat).obj (AddCommGrpCat.of A)` and the
sheaf `locallyConstantAddCommGrpSheaf X A` of locally constant `A`-valued functions. -/
def constantSheafIsoLocallyConstantAddCommGrpSheaf :
    (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj (AddCommGrpCat.of A) ≅
      locallyConstantAddCommGrpSheaf X A :=
  (constantSheafNatIsoLocallyConstantAddCommGrpSheaf X).app (AddCommGrpCat.of A)

/-- The sheaf of locally constant `A`-valued functions is a constant sheaf in the sense of
`CategoryTheory.Sheaf.IsConstant`. -/
instance isConstant_locallyConstantAddCommGrpSheaf :
    CategoryTheory.Sheaf.IsConstant (Opens.grothendieckTopology X)
      (locallyConstantAddCommGrpSheaf X A) :=
  CategoryTheory.Sheaf.isConstant_of_iso (J := Opens.grothendieckTopology X)
    (constantSheafIsoLocallyConstantAddCommGrpSheaf X A).symm

/-- Sheaf cohomology of `locallyConstantAddCommGrpSheaf X A` agrees in every degree with the sheaf
cohomology of `(constantSheaf _ AddCommGrpCat).obj (AddCommGrpCat.of A)`. -/
def locallyConstantAddCommGrpSheafCohomologyAddEquiv (n : ℕ) :
    (locallyConstantAddCommGrpSheaf X A).H n ≃+
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of A)).H n where
  toFun := CategoryTheory.Sheaf.H.map (constantSheafIsoLocallyConstantAddCommGrpSheaf X A).inv n
  invFun := CategoryTheory.Sheaf.H.map (constantSheafIsoLocallyConstantAddCommGrpSheaf X A).hom n
  left_inv x := by
    rw [← CategoryTheory.Sheaf.H.map_comp_apply, Iso.inv_hom_id,
      CategoryTheory.Sheaf.H.map_id_apply]
  right_inv x := by
    rw [← CategoryTheory.Sheaf.H.map_comp_apply, Iso.hom_inv_id,
      CategoryTheory.Sheaf.H.map_id_apply]
  map_add' := map_add _

@[simp]
theorem locallyConstantAddCommGrpSheafCohomologyAddEquiv_apply (n : ℕ)
    (x : (locallyConstantAddCommGrpSheaf X A).H n) :
    locallyConstantAddCommGrpSheafCohomologyAddEquiv X A n x =
      CategoryTheory.Sheaf.H.map (constantSheafIsoLocallyConstantAddCommGrpSheaf X A).inv n x :=
  (rfl)

@[simp]
theorem locallyConstantAddCommGrpSheafCohomologyAddEquiv_symm_apply (n : ℕ)
    (x : ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of A)).H n) :
    (locallyConstantAddCommGrpSheafCohomologyAddEquiv X A n).symm x =
      CategoryTheory.Sheaf.H.map (constantSheafIsoLocallyConstantAddCommGrpSheaf X A).hom n x :=
  (rfl)

end ConstantSheafComparison

section Sections

/-- Over a preconnected open `U` containing a point `x`, evaluation at `x` identifies the sections
`LocallyConstant U A` of `locallyConstantAddCommGrpSheaf X A` over `U` with `A`. -/
def locallyConstantAddCommGrpSectionsAddEquiv {U : Opens X} [PreconnectedSpace U]
    {x : X} (hx : x ∈ U) :
    LocallyConstant U A ≃+ A where
  toFun f := f ⟨x, hx⟩
  invFun := LocallyConstant.const U
  left_inv f := (LocallyConstant.eq_const f ⟨x, hx⟩).symm
  right_inv _ := rfl
  map_add' _ _ := rfl

@[simp]
theorem locallyConstantAddCommGrpSectionsAddEquiv_apply {U : Opens X} [PreconnectedSpace U]
    {x : X} (hx : x ∈ U) (f : LocallyConstant U A) :
    locallyConstantAddCommGrpSectionsAddEquiv X A hx f = f ⟨x, hx⟩ :=
  (rfl)

@[simp]
theorem locallyConstantAddCommGrpSectionsAddEquiv_symm_apply {U : Opens X} [PreconnectedSpace U]
    {x : X} (hx : x ∈ U) (a : A) :
    (locallyConstantAddCommGrpSectionsAddEquiv X A hx).symm a = LocallyConstant.const U a :=
  (rfl)

end Sections

end TopCat
