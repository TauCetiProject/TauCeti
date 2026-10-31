/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Core
public import TauCeti.AlgebraicGeometry.Modules.Products
public import TauCeti.AlgebraicGeometry.VectorBundle.Determinant.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.OpenCover

/-!
# The determinant of a vector bundle of locally constant rank

The rank of a finite locally free sheaf `E` on a scheme `X` is only locally constant: on a
disconnected scheme it may differ between components. Its determinant `det E` is the invertible
sheaf which over each open set `X_n = {x | rank E x = n}` is the top exterior power `⋀ⁿ E`.

This file constructs it through the exterior power of an `𝒪_X`-module `M` in a locally constant
degree `r : X → ℕ` (`locallyConstantExteriorPower r`). The sets `r⁻¹{n}` form a cover of `X` by
pairwise disjoint open sets, and `⋀^r M` is the product over `n` of the pushforwards of the
restrictions of `⋀ⁿ M` to `r⁻¹{n}`: its sections over an open `V` are the families of sections of
the `⋀ⁿ M` over the sets `V ∩ r⁻¹{n}`. Over an open set on which `r` is constantly `n`, the other
factors have no nonzero sections, so `⋀^r M` restricts there to `⋀ⁿ M`
(`restrictLocallyConstantExteriorPowerIso`), and if `r` is constantly `n` then `⋀^r M ≅ ⋀ⁿ M`
(`locallyConstantExteriorPowerIso`).

For a finite locally free sheaf `E`, `⋀^r E` is again finite locally free, of rank
`(rank E x).choose (r x)` at `x`. Taking `r = rank E` gives an invertible sheaf, the determinant
`FiniteLocallyFreeSheaf.det E`. An isomorphism `E ≅ F` preserves the rank, so the determinant is a
functor `FiniteLocallyFreeSheaf.determinantCore X` on the core of the category of finite locally
free sheaves. On sheaves of constant rank `r` it agrees with the fixed-rank determinant
`FiniteLocallyFreeSheaf.determinant X r` (`FiniteLocallyFreeSheaf.detIsoDeterminant`).

## Main declarations

* `TauCeti.AlgebraicGeometry.locallyConstantExteriorPower r`: the exterior power `⋀^r` of
  `𝒪_X`-modules in a locally constant degree `r`;
* `TauCeti.AlgebraicGeometry.restrictLocallyConstantExteriorPowerIso` and
  `TauCeti.AlgebraicGeometry.locallyConstantExteriorPowerIso`: over an open set where `r` is
  constantly `n`, and if `r` is constantly `n`, `⋀^r` is the `n`-th exterior power;
* `FiniteLocallyFreeSheaf.locallyConstantExteriorPower X r` and
  `FiniteLocallyFreeSheaf.rank_locallyConstantExteriorPower_apply`: `⋀^r` of finite locally free
  sheaves, with rank `(rank E x).choose (r x)`;
* `FiniteLocallyFreeSheaf.det`: the determinant `⋀^{rank E} E` of a finite locally free sheaf, an
  invertible sheaf;
* `FiniteLocallyFreeSheaf.determinantCore X`: the determinant as a functor on the core of the
  category of finite locally free sheaves;
* `FiniteLocallyFreeSheaf.detIsoDeterminant`: in constant rank `r`, `det E` is the fixed-rank
  determinant `⋀ʳ E`.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 5.16
* F. Knudsen and D. Mumford, *The projectivity of the moduli space of stable curves I:
  Preliminaries on det and Div*, Math. Scand. 39 (1976), Chapter I
-/

public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry Scheme.Modules

noncomputable section

variable {X : Scheme.{u}}

/-- The open subset of `X` on which the locally constant function `r` takes the value `n`. -/
private def fiber (r : LocallyConstant X ℕ) (n : ℕ) : X.Opens :=
  ⟨r ⁻¹' {n}, r.isLocallyConstant.isOpen_fiber n⟩

/-- The `n`-th factor of `locallyConstantExteriorPower r`: the `n`-th exterior power, restricted
to the fiber `r⁻¹{n}` and pushed forward to `X`. -/
private abbrev summand (r : LocallyConstant X ℕ) (n : ℕ) : X.Modules ⥤ X.Modules :=
  SheafOfModules.exteriorPower X.sheaf n ⋙ restrictFunctor (fiber r n).ι ⋙
    pushforward (fiber r n).ι

/-- The exterior power `⋀^r M` of an `𝒪_X`-module `M` in a locally constant degree
`r : X → ℕ`: the `𝒪_X`-module whose restriction to each open set `r⁻¹{n}` is the `n`-th exterior
power of `M` there (`restrictLocallyConstantExteriorPowerIso`). It is the product over `n` of
the pushforwards of these restrictions, whose sections over an open `V` are the families of
sections of `⋀ⁿ M` over the sets `V ∩ r⁻¹{n}`. -/
def locallyConstantExteriorPower (r : LocallyConstant X ℕ) : X.Modules ⥤ X.Modules where
  obj M := ∏ᶜ fun n ↦ (summand r n).obj M
  map φ := Limits.Pi.map fun n ↦ (summand r n).map φ
  map_id M := by simp
  map_comp φ ψ := by simp [Limits.Pi.map_comp_map]

/-- Over an open `V` on which `r` is constantly `n`, the sections of `⋀^r M` are those of the
`n`-th factor. -/
private theorem bijective_π_app (r : LocallyConstant X ℕ) (M : X.Modules) {n : ℕ} {V : X.Opens}
    (hV : ∀ x ∈ V, r x = n) :
    Function.Bijective ((Pi.π (fun m ↦ (summand r m).obj M) n).app V) := by
  refine bijective_app_π_of_subsingleton _ n V fun m hm ↦ ?_
  -- The sections over `V` of the `m`-th factor are those of a module on `r⁻¹{m}` over the
  -- preimage of `V`, which is empty; they form a module over the zero ring `Γ(r⁻¹{m}, ∅)`.
  -- A point `x` of `r⁻¹{m}` satisfies `r x = m` by definition of the open set `fiber r m`.
  have h : (fiber r m).ι ⁻¹ᵁ V = ⊥ :=
    eq_bot_iff.2 fun x hx ↦ hm ((show r x.1 = m from x.2).symm.trans (hV x.1 hx))
  -- The sections of the pushforward over `V` are by definition those of the restriction over
  -- the preimage of `V`.
  have : Subsingleton
      Γ(Scheme.Modules.restrict ((SheafOfModules.exteriorPower X.sheaf m).obj M) (fiber r m).ι,
        (fiber r m).ι ⁻¹ᵁ V) :=
    h ▸ Module.subsingleton Γ((fiber r m).toScheme, ⊥) _
  exact this

/-- The projection of `⋀^r M` onto its `n`-th factor. -/
private def factorπ (r : LocallyConstant X ℕ) (n : ℕ) :
    locallyConstantExteriorPower r ⟶ summand r n where
  app M := Pi.π (fun m ↦ (summand r m).obj M) n
  naturality _ _ _ := by simp [locallyConstantExteriorPower]

/-- The map from `⋀ⁿ M` to the pushforward of its restriction to the fiber `r⁻¹{n}`. -/
private def factorι (r : LocallyConstant X ℕ) (n : ℕ) :
    SheafOfModules.exteriorPower X.sheaf n ⟶ summand r n where
  app _ := (restrictAdjunction (fiber r n).ι).unit.app _
  naturality _ _ _ := (restrictAdjunction (fiber r n).ι).unit.naturality _

private theorem isIso_factorπ_app_app (r : LocallyConstant X ℕ) (M : X.Modules) {n : ℕ}
    {V : X.Opens} (hV : ∀ x ∈ V, r x = n) :
    IsIso (Scheme.Modules.Hom.app ((factorπ r n).app M) V) :=
  (ConcreteCategory.isIso_iff_bijective _).2 (bijective_π_app r M hV)

/-- Over an open `V` on which `r` is constantly `n`, the sections of an `𝒪_X`-module `N` are
those of the pushforward of its restriction to `r⁻¹{n}`. -/
private theorem isIso_unit_app_app (r : LocallyConstant X ℕ) (N : X.Modules) {n : ℕ}
    {V : X.Opens} (hV : ∀ x ∈ V, r x = n) :
    IsIso (Scheme.Modules.Hom.app ((restrictAdjunction (fiber r n).ι).unit.app N) V) := by
  have h : (fiber r n).ι ''ᵁ ((fiber r n).ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 fun x hx ↦ hV x hx
  -- The component is the restriction of sections along `ι(ι⁻¹ V) ≤ V`, an equality here.
  have : homOfLE ((fiber r n).ι.image_preimage_le V) = eqToHom h := Subsingleton.elim _ _
  rw [restrictAdjunction_unit_app_app, this]
  exact Functor.map_isIso N.presheaf (eqToHom h).op

private theorem isIso_factorι_app_app (r : LocallyConstant X ℕ) (M : X.Modules) {n : ℕ}
    {V : X.Opens} (hV : ∀ x ∈ V, r x = n) :
    IsIso (Scheme.Modules.Hom.app ((factorι r n).app M) V) := by
  dsimp only [factorι]
  exact isIso_unit_app_app r _ hV

/-- A morphism of `𝒪_X`-modules restricts to an isomorphism over an open `U` if it is bijective
on sections over every open contained in `U`. -/
private theorem isIso_restrictFunctor_map {M N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (h : ∀ V ≤ U, IsIso (Scheme.Modules.Hom.app φ V)) : IsIso ((restrictFunctor U.ι).map φ) :=
  Hom.isIso_iff_isIso_app.2 fun W ↦ h _ (U.ι_image_le W)

/-- **Restriction of `⋀^r M` to an open where `r` is constant.** Over an open `U` on which the
locally constant function `r` takes the value `n`, the restriction of `⋀^r M` is the restriction
of the `n`-th exterior power `⋀ⁿ M`, naturally in `M`. -/
def restrictLocallyConstantExteriorPowerIso (r : LocallyConstant X ℕ) {n : ℕ} (U : X.Opens)
    (hU : ∀ x ∈ U, r x = n) :
    locallyConstantExteriorPower r ⋙ restrictFunctor U.ι ≅
      SheafOfModules.exteriorPower X.sheaf n ⋙ restrictFunctor U.ι :=
  have : ∀ M, IsIso ((Functor.whiskerRight (factorπ r n) (restrictFunctor U.ι)).app M) :=
    fun M ↦ isIso_restrictFunctor_map _ U fun _ hV ↦
      isIso_factorπ_app_app r M fun x hx ↦ hU x (hV hx)
  have : ∀ M, IsIso ((Functor.whiskerRight (factorι r n) (restrictFunctor U.ι)).app M) :=
    fun M ↦ isIso_restrictFunctor_map _ U fun _ hV ↦
      isIso_factorι_app_app r M fun x hx ↦ hU x (hV hx)
  have := NatIso.isIso_of_isIso_app (Functor.whiskerRight (factorπ r n) (restrictFunctor U.ι))
  have := NatIso.isIso_of_isIso_app (Functor.whiskerRight (factorι r n) (restrictFunctor U.ι))
  asIso (Functor.whiskerRight (factorπ r n) (restrictFunctor U.ι)) ≪≫
    (asIso (Functor.whiskerRight (factorι r n) (restrictFunctor U.ι))).symm

/-- **`⋀^r M` in constant degree.** If the locally constant function `r` is constantly `n`,
then `⋀^r M` is the `n`-th exterior power `⋀ⁿ M`, naturally in `M`. -/
def locallyConstantExteriorPowerIso (r : LocallyConstant X ℕ) {n : ℕ} (hr : ∀ x, r x = n) :
    locallyConstantExteriorPower r ≅ SheafOfModules.exteriorPower X.sheaf n :=
  have : ∀ M, IsIso ((factorπ r n).app M) := fun M ↦
    Hom.isIso_iff_isIso_app.2 fun _ ↦ isIso_factorπ_app_app r M fun x _ ↦ hr x
  have : ∀ M, IsIso ((factorι r n).app M) := fun M ↦
    Hom.isIso_iff_isIso_app.2 fun _ ↦ isIso_factorι_app_app r M fun x _ ↦ hr x
  have := NatIso.isIso_of_isIso_app (factorπ r n)
  have := NatIso.isIso_of_isIso_app (factorι r n)
  asIso (factorπ r n) ≪≫ (asIso (factorι r n)).symm

namespace FiniteLocallyFreeSheaf

/-- The pullback of `⋀^r E` to the open set `r⁻¹{n}` is the pullback of `⋀ⁿ E`. -/
private def pullbackFiberIso (r : LocallyConstant X ℕ) (n : ℕ) (M : X.Modules) :
    (Scheme.Modules.pullback (fiber r n).ι).obj ((locallyConstantExteriorPower r).obj M) ≅
      (Scheme.Modules.pullback (fiber r n).ι).obj
        ((SheafOfModules.exteriorPower X.sheaf n).obj M) :=
  ((restrictFunctorIsoPullback (fiber r n).ι).app _).symm ≪≫
    (restrictLocallyConstantExteriorPowerIso r (fiber r n) fun _ hx ↦ hx).app M ≪≫
    (restrictFunctorIsoPullback (fiber r n).ι).app _

/-- The exterior power `⋀^r E` of a finite locally free sheaf in a locally constant degree `r` is
finite locally free: over each open set `r⁻¹{n}` it is the finite locally free sheaf `⋀ⁿ E`. -/
theorem isFiniteLocallyFree_locallyConstantExteriorPower (r : LocallyConstant X ℕ)
    (E : FiniteLocallyFreeSheaf X) :
    Scheme.Modules.isFiniteLocallyFree X ((locallyConstantExteriorPower r).obj E.obj) := by
  have hU : IsOpenCover (fiber r) :=
    IsOpenCover.mk (top_unique fun x _ ↦ Opens.mem_iSup.mpr ⟨r x, rfl⟩)
  rw [isFiniteLocallyFree_iff_forall_pullback (X.openCoverOfIsOpenCover (fiber r) hU)]
  intro (n : ℕ)
  have h := ((pullback (fiber r n).ι).obj ((exteriorPower X n).obj E)).property
  rw [pullback_obj_obj, exteriorPower_obj_obj] at h
  exact (Scheme.Modules.isFiniteLocallyFree _).prop_of_iso (pullbackFiberIso r n E.obj).symm h

variable (X) in
/-- The exterior power `E ↦ ⋀^r E` of finite locally free sheaves in a locally constant degree
`r : X → ℕ`: over each open set `r⁻¹{n}` it is the `n`-th exterior power. -/
def locallyConstantExteriorPower (r : LocallyConstant X ℕ) :
    FiniteLocallyFreeSheaf X ⥤ FiniteLocallyFreeSheaf X :=
  (Scheme.Modules.isFiniteLocallyFree X).lift
    ((Scheme.Modules.isFiniteLocallyFree X).ι ⋙ AlgebraicGeometry.locallyConstantExteriorPower r)
    (isFiniteLocallyFree_locallyConstantExteriorPower r)

/-- The underlying sheaf of `⋀^r E` is `⋀^r` of the underlying `𝒪_X`-module of `E`. -/
@[simp]
lemma locallyConstantExteriorPower_obj_obj (r : LocallyConstant X ℕ)
    (E : FiniteLocallyFreeSheaf X) :
    ((locallyConstantExteriorPower X r).obj E).obj =
      (AlgebraicGeometry.locallyConstantExteriorPower r).obj E.obj :=
  (rfl)

/-- The exterior power `⋀^r` acts on morphisms of finite locally free sheaves through the
underlying morphisms of `𝒪_X`-modules. -/
@[simp]
lemma locallyConstantExteriorPower_map_hom (r : LocallyConstant X ℕ)
    {E F : FiniteLocallyFreeSheaf X} (φ : E ⟶ F) :
    ((locallyConstantExteriorPower X r).map φ).hom =
      eqToHom (locallyConstantExteriorPower_obj_obj r E) ≫
        (AlgebraicGeometry.locallyConstantExteriorPower r).map φ.hom ≫
          eqToHom (locallyConstantExteriorPower_obj_obj r F).symm := by
  -- Both `eqToHom`s are identities.
  exact ((Category.id_comp _).trans (Category.comp_id _)).symm

/-- The pullback of `⋀^r E` to the open set `r⁻¹{n}` is the pullback of `⋀ⁿ E`, as finite
locally free sheaves. -/
private def pullbackFiberIso' (r : LocallyConstant X ℕ) (n : ℕ) (E : FiniteLocallyFreeSheaf X) :
    ((pullback (fiber r n).ι).obj ((locallyConstantExteriorPower X r).obj E)).obj ≅
      ((pullback (fiber r n).ι).obj ((exteriorPower X n).obj E)).obj :=
  eqToIso (by rw [pullback_obj_obj, locallyConstantExteriorPower_obj_obj]) ≪≫
    pullbackFiberIso r n E.obj ≪≫ eqToIso (by rw [pullback_obj_obj, exteriorPower_obj_obj])

/-- The rank of `⋀^r E` at `x` is `(E.rank x).choose (r x)`. -/
@[simp]
theorem rank_locallyConstantExteriorPower_apply (r : LocallyConstant X ℕ)
    (E : FiniteLocallyFreeSheaf X) (x : X) :
    ((locallyConstantExteriorPower X r).obj E).rank x = (E.rank x).choose (r x) := by
  -- Compute the rank after pulling back to the open set `r⁻¹{r x}` containing `x`.
  let y : (fiber r (r x)).toScheme := ⟨x, rfl⟩
  calc ((locallyConstantExteriorPower X r).obj E).rank x
      = ((pullback (fiber r (r x)).ι).obj ((locallyConstantExteriorPower X r).obj E)).rank y :=
        by rw [rank_pullback_apply, Scheme.Opens.ι_apply]
    _ = ((pullback (fiber r (r x)).ι).obj ((exteriorPower X (r x)).obj E)).rank y := by
        rw [rank_eq_of_iso (pullbackFiberIso' r (r x) E)]
    _ = (E.rank x).choose (r x) :=
        by rw [rank_pullback_apply, Scheme.Opens.ι_apply, rank_exteriorPower_apply]

/-- The **determinant** `det E = ⋀^{rank E} E` of a finite locally free sheaf `E`: over each open
set where `E` has rank `n` it is the top exterior power `⋀ⁿ E`. It has rank `(rank E).choose
(rank E) = 1` everywhere, so it is an invertible sheaf. -/
def det (E : FiniteLocallyFreeSheaf X) : InvertibleSheaf X :=
  ⟨(AlgebraicGeometry.locallyConstantExteriorPower E.rank).obj E.obj,
    (isInvertible_iff_forall_rank_eq_one ((locallyConstantExteriorPower X E.rank).obj E)).2
      fun x ↦ by simp⟩

/-- The underlying sheaf of `det E` is `⋀^{rank E}` of the underlying `𝒪_X`-module of `E`. -/
@[simp]
lemma det_obj (E : FiniteLocallyFreeSheaf X) :
    (det E).obj = (AlgebraicGeometry.locallyConstantExteriorPower E.rank).obj E.obj :=
  (rfl)

/-- `⋀^r` of an identity, followed by the transport along `r = r`, is the identity. -/
private lemma locallyConstantExteriorPower_map_id_comp_eqToHom {r : LocallyConstant X ℕ}
    (h : r = r) (M : X.Modules) :
    (AlgebraicGeometry.locallyConstantExteriorPower r).map (𝟙 M) ≫
        eqToHom (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj M) h) =
      𝟙 _ := by
  simp

/-- `⋀^r` of a composite, followed by transport along `r = r''`, is the composite of the
transported maps along `r = r'` and `r' = r''`. -/
private lemma locallyConstantExteriorPower_map_comp_comp_eqToHom
    {r r' r'' : LocallyConstant X ℕ} (h : r = r') (h' : r' = r'') (h'' : r = r'')
    {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) :
    (AlgebraicGeometry.locallyConstantExteriorPower r).map (φ ≫ ψ) ≫
        eqToHom (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj P) h'') =
      ((AlgebraicGeometry.locallyConstantExteriorPower r).map φ ≫
          eqToHom (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj N) h)) ≫
        (AlgebraicGeometry.locallyConstantExteriorPower r').map ψ ≫
          eqToHom
            (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj P) h') := by
  subst h h'
  simp

variable (X) in
/-- The determinant is functorial on the core of the category of finite locally free sheaves:
an isomorphism `E ≅ F` preserves the rank and induces the isomorphism
`⋀^{rank E} E ≅ ⋀^{rank E} F = ⋀^{rank F} F` of determinants. -/
def determinantCore : Core (FiniteLocallyFreeSheaf X) ⥤ InvertibleSheaf X where
  obj E := det E.of
  map {E F} e := ObjectProperty.homMk <|
    (AlgebraicGeometry.locallyConstantExteriorPower E.of.rank).map e.iso.hom.hom ≫
      eqToHom (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj F.of.obj)
        (rank_eq_of_iso ((Scheme.Modules.isFiniteLocallyFree X).ι.mapIso e.iso)))
  map_id E := by
    ext1
    simp only [ObjectProperty.homMk_hom, coreCategory_id_iso, Iso.refl_hom,
      ObjectProperty.FullSubcategory.id_hom]
    exact locallyConstantExteriorPower_map_id_comp_eqToHom rfl _
  map_comp {E F G} e f := by
    ext1
    simp only [ObjectProperty.homMk_hom, coreCategory_comp_iso, Iso.trans_hom,
      ObjectProperty.FullSubcategory.comp_hom]
    exact locallyConstantExteriorPower_map_comp_comp_eqToHom
      (rank_eq_of_iso ((Scheme.Modules.isFiniteLocallyFree X).ι.mapIso e.iso))
      (rank_eq_of_iso ((Scheme.Modules.isFiniteLocallyFree X).ι.mapIso f.iso))
      (rank_eq_of_iso ((Scheme.Modules.isFiniteLocallyFree X).ι.mapIso (e ≫ f).iso)) _ _

/-- The determinant of an object of the core is `det` of the underlying finite locally free
sheaf. -/
@[simp]
lemma determinantCore_obj (E : Core (FiniteLocallyFreeSheaf X)) :
    (determinantCore X).obj E = det E.of :=
  (rfl)

/-- The determinant acts on an isomorphism `E ≅ F` through `⋀^{rank E}`, followed by the
identification `⋀^{rank E} F = ⋀^{rank F} F` given by `rank E = rank F`. -/
@[simp]
lemma determinantCore_map_hom {E F : Core (FiniteLocallyFreeSheaf X)} (e : E ⟶ F) :
    ((determinantCore X).map e).hom =
      eqToHom (by rw [determinantCore_obj, det_obj]) ≫
        (AlgebraicGeometry.locallyConstantExteriorPower E.of.rank).map e.iso.hom.hom ≫
        eqToHom (congrArg (fun r ↦ (AlgebraicGeometry.locallyConstantExteriorPower r).obj F.of.obj)
          (rank_eq_of_iso ((Scheme.Modules.isFiniteLocallyFree X).ι.mapIso e.iso))) ≫
        eqToHom (by rw [determinantCore_obj, det_obj]) :=
  -- The outer `eqToHom`s are identities; they only record `determinantCore_obj` and `det_obj`,
  -- which are not syntactic equalities outside this file.
  ((Category.id_comp _).trans (congrArg _ (Category.comp_id _))).symm

/-- On a sheaf `E` of constant rank `r`, the determinant `det E` is the fixed-rank determinant
`⋀ʳ E`. -/
def detIsoDeterminant {r : ℕ} (E : FixedRank X r) : det E.obj ≅ (determinant X r).obj E :=
  ObjectProperty.isoMk _ <| eqToIso (det_obj E.obj) ≪≫
    (AlgebraicGeometry.locallyConstantExteriorPowerIso E.obj.rank (FixedRank.rank_apply E)).app
      E.obj.obj ≪≫ eqToIso (determinant_obj_obj E).symm

/-- On underlying sheaves, `detIsoDeterminant` is `locallyConstantExteriorPowerIso`. -/
lemma detIsoDeterminant_hom_hom {r : ℕ} (E : FixedRank X r) :
    (detIsoDeterminant E).hom.hom =
      eqToHom (det_obj E.obj) ≫
        (AlgebraicGeometry.locallyConstantExteriorPowerIso E.obj.rank
          (FixedRank.rank_apply E)).hom.app E.obj.obj ≫
        eqToHom (determinant_obj_obj E).symm :=
  (rfl)

end FiniteLocallyFreeSheaf

end

end TauCeti.AlgebraicGeometry
