/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Pullback

/-!
# The base change map for higher direct images

Consider a commutative square of schemes

```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```

that is, `g' ≫ f = f' ≫ g`. This file constructs, for affine `Y`, the base change map

`Scheme.Hom.higherDirectImageBaseChange h q : g^* R^q f_* M ⟶ R^q f'_* g'^* M`,

natural in the sheaf of modules `M`, together with its adjoint
`Scheme.Hom.higherDirectImageBaseChangeAdj h q : R^q f_* M ⟶ g_* R^q f'_* g'^* M`. No
hypothesis on `f`, `g` or `M` is needed, and the square need not be cartesian.

`R^q f_* M` is the sheafification of the presheaf of modules `V ↦ H^q(f⁻¹ V, M)`
(`Scheme.Hom.higherDirectImagePresheafSheafificationIso`). Over an open `V` of `Y`, pullback on
cohomology along `g'` (`Scheme.Hom.cohomologyOnPullback`) is a map
`H^q(f⁻¹ V, M) ⟶ H^q(g'⁻¹ f⁻¹ V, g'^* M) = H^q(f'⁻¹ g⁻¹ V, g'^* M)`, compatible with restriction,
so these maps form a morphism from that presheaf to `g_* R^q f'_* g'^* M`
(`Scheme.Hom.higherDirectImageBaseChangeToPresheaf`). Sheafification and the adjunction
`g^* ⊣ g_*` turn it into the base change map.

The one point that uses the affineness of `Y` is linearity. The identification of
`V ↦ H^q(f⁻¹ V, M)` with cohomology is known to be compatible with the action of global functions
of `Y` (`Scheme.Hom.higherDirectImagePresheafToPresheafIso_hom_app_smul`), and so is pullback on
cohomology (`Scheme.Hom.cohomologyOnPullback_smul`). On an affine scheme, a map of abelian
presheaves into a sheaf of modules that is linear over global functions is linear over all
functions (`Scheme.Modules.app_smul_of_isAffine`), since a function on a basic open `D(s)` is a
global function divided by a power of `s`.

Over an affine open `V` of `Y` with `g⁻¹ V` affine, for quasi-compact quasi-separated `f` and `f'`
and quasi-coherent `M`, the sections of the adjoint base change map are pullback on cohomology,
under the identifications of sections of higher direct images with cohomology
(`Scheme.Hom.higherDirectImageBaseChangeAdj_app_sectionsAddEquiv`). At
`V = ⊤` this is the map `Scheme.Hom.cohomologyPullback` whose linear extension is the flat base
change map `TauCeti.AlgebraicGeometry.cohomologyBaseChange` over an affine base.

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.higherDirectImageBaseChange`: the base change map
  `g^* R^q f_* M ⟶ R^q f'_* g'^* M`, natural in `M`, for affine `Y`;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageBaseChangeAdj`: its adjoint
  `R^q f_* M ⟶ g_* R^q f'_* g'^* M`;
* `AlgebraicGeometry.Scheme.Hom.higherDirectImageBaseChangeAdj_app_app_presheafToSheaf` and
  `AlgebraicGeometry.Scheme.Hom.higherDirectImageBaseChangeAdj_app_sectionsAddEquiv`:
  its sections are pullback on cohomology;
* `AlgebraicGeometry.Scheme.Modules.app_smul_of_isAffine`: on an affine scheme, linearity over
  global functions implies linearity.

## References

* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH), flat base
  change, for which this is the comparison map.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry Scheme.Modules

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry.Scheme.Modules

section CohomologyPresheaf

variable {X Y : Scheme.{u}} (g : Y ⟶ X)

/-- Pullback on the cohomology of the opens of `X`, as a morphism from the cohomology presheaf
`U ↦ Hⁿ(U, M)` to the presheaf `U ↦ Hⁿ(g⁻¹ U, g^* M)`. -/
def cohomologyPresheafPullback (M : X.Modules) (n : ℕ) :
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).cohomologyPresheaf n ⟶
      (TopologicalSpace.Opens.map g.base).op ⋙
        ((SheafOfModules.toSheaf Y.ringCatSheaf).obj
          ((Scheme.Modules.pullback g).obj M)).cohomologyPresheaf n where
  app U := g.cohomologyOnPullback M n U.unop
  naturality U V i := by
    exact g.cohomologyOnRes_comp_cohomologyOnPullback M n (leOfHom i.unop)

/-- The components of `cohomologyPresheafPullback` are pullback on the cohomology of opens. -/
@[simp]
lemma cohomologyPresheafPullback_app (M : X.Modules) (n : ℕ) (U : X.Opensᵒᵖ) :
    (g.cohomologyPresheafPullback M n).app U = g.cohomologyOnPullback M n U.unop :=
  (rfl)

end CohomologyPresheaf

section Affine

variable {Y : Scheme.{u}} [IsAffine Y]

/-- **Linearity over an affine scheme.** On an affine scheme `Y`, a morphism of underlying
abelian presheaves from a presheaf of modules to a sheaf of modules is linear as soon as it is
linear over the restrictions of global functions: every function on a basic open is a global
function divided by a power of the defining function. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.app_smul_of_isAffine {P : Y.PresheafOfModules}
    {N : Y.Modules} (φ : P.presheaf ⟶ N.presheaf)
    (hφ : ∀ (U : Y.Opens) (r : Γ(Y, ⊤)) (x : P.obj (.op U)),
      φ.app (.op U) ((show Y.ringCatSheaf.obj.obj (.op U) from Y.presheaf.map U.leTop.op r) • x) =
        (show Γ(Y, U) from Y.presheaf.map U.leTop.op r) •
          (show Γ(N, U) from φ.app (.op U) x))
    (U : Y.Opens) (r : Y.ringCatSheaf.obj.obj (.op U)) (x : P.obj (.op U)) :
    φ.app (.op U) (r • x) = (show Γ(Y, U) from r) • (show Γ(N, U) from φ.app (.op U) x) := by
  refine TopCat.Presheaf.IsSheaf.section_ext N.isSheaf fun p hp ↦ ?_
  obtain ⟨s, hsU, hps⟩ := (isAffineOpen_top Y).exists_basicOpen_le ⟨p, hp⟩ trivial
  refine ⟨Y.basicOpen s, hsU, hps, ?_⟩
  -- Restrict to the basic open `D(s)`, where every function is `a / sⁿ` with `a` global.
  have key (r' : Y.ringCatSheaf.obj.obj (.op (Y.basicOpen s)))
      (x' : P.obj (.op (Y.basicOpen s))) :
      φ.app _ (r' • x') = (show Γ(Y, Y.basicOpen s) from r') •
        (show Γ(N, Y.basicOpen s) from φ.app _ x') := by
    obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers s)
      (show Γ(Y, Y.basicOpen s) from r')
    have hu : IsUnit (algebraMap Γ(Y, ⊤) Γ(Y, Y.basicOpen s) (s ^ n)) :=
      IsLocalization.map_units _ (⟨s ^ n, n, rfl⟩ : Submonoid.powers s)
    rw [← hu.smul_left_cancel]
    change Y.presheaf.map (Y.basicOpen s).leTop.op (s ^ n) • _ = _
    let u : Γ(Y, Y.basicOpen s) := Y.presheaf.map (Y.basicOpen s).leTop.op (s ^ n)
    let a' : Γ(Y, Y.basicOpen s) := Y.presheaf.map (Y.basicOpen s).leTop.op a
    have ha' : u * (show Γ(Y, Y.basicOpen s) from r') = a' := (mul_comm _ _).trans ha
    have h₁ : (show Y.ringCatSheaf.obj.obj (.op (Y.basicOpen s)) from u) • r' • x' =
        (show Y.ringCatSheaf.obj.obj (.op (Y.basicOpen s)) from a') • x' :=
      (mul_smul _ _ _).symm.trans (congrArg (· • x') ha')
    have h₂ : u • (show Γ(Y, Y.basicOpen s) from r') •
        (show Γ(N, Y.basicOpen s) from φ.app _ x') = a' • φ.app _ x' :=
      (mul_smul _ _ _).symm.trans (congrArg (· • _) ha')
    exact (hφ _ (s ^ n) (r' • x')).symm.trans ((congrArg (φ.app _) h₁).trans
      ((hφ _ a x').trans h₂.symm))
  have hr := P.map_smul (homOfLE hsU).op r x
  have hn := N.val.map_smul (homOfLE hsU).op r (φ.app _ x)
  have hnat := ConcreteCategory.congr_hom (φ.naturality (homOfLE hsU).op)
  exact (hnat (r • x)).symm.trans ((congrArg (φ.app _) hr).trans ((key _ _).trans
    ((congrArg _ (hnat x)).trans hn.symm)))

end Affine

section Naturality

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The identification of `V ↦ H^q(f⁻¹ V, M)` with cohomology is natural in `M`, on elements. -/
lemma higherDirectImagePresheafToPresheafIso_hom_app_map {M N : X.Modules} (φ : M ⟶ N)
    (q : ℕ) (V : Y.Opens) (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (f.higherDirectImagePresheafToPresheafIso N q).hom.app (op V)
        (((f.higherDirectImagePresheaf q).map φ).app (op V) x) =
      cohomologyOnMap φ q (f ⁻¹ᵁ V)
        ((f.higherDirectImagePresheafToPresheafIso M q).hom.app (op V) x) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (f.higherDirectImagePresheafToPresheafIso_naturality φ q) (op V)) x

/-- The inverse identification of cohomology with `V ↦ H^q(f⁻¹ V, M)` is natural in `M`, on
elements. -/
lemma higherDirectImagePresheafToPresheafIso_inv_app_cohomologyOnMap {M N : X.Modules}
    (φ : M ⟶ N) (q : ℕ) (V : Y.Opens) (x : cohomologyOn M q (f ⁻¹ᵁ V)) :
    (f.higherDirectImagePresheafToPresheafIso N q).inv.app (op V) (cohomologyOnMap φ q _ x) =
      ((f.higherDirectImagePresheaf q).map φ).app (op V)
        ((f.higherDirectImagePresheafToPresheafIso M q).inv.app (op V) x) := by
  apply (ConcreteCategory.bijective_of_isIso
    ((f.higherDirectImagePresheafToPresheafIso N q).hom.app (op V))).injective
  have h₁ := f.higherDirectImagePresheafToPresheafIso_hom_app_map φ q V
    ((f.higherDirectImagePresheafToPresheafIso M q).inv.app (op V) x)
  simp only [Iso.inv_hom_id_app_apply] at h₁ ⊢
  exact h₁.symm

end Naturality

section ToSheaf

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ)

/-- The map from the presheaf of modules `V ↦ H^q(f⁻¹ V, M)` to its sheafification `R^q f_* M`,
natural in `M`. -/
def higherDirectImagePresheafToSheaf :
    f.higherDirectImagePresheaf q ⟶ f.higherDirectImage q ⋙
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)) :=
  Functor.whiskerLeft (f.higherDirectImagePresheaf q)
      (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).unit ≫
    Functor.whiskerRight (f.higherDirectImagePresheafSheafificationIso q).hom
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj))

/-- Over an affine open `V`, the identification of `H^q(f⁻¹ V, M)` with the sections of
`R^q f_* M` sends a class to the section defined by the corresponding section of the presheaf
`V ↦ H^q(f⁻¹ V, M)`. -/
lemma higherDirectImageSectionsAddEquiv_eq_presheafToSheaf [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] {V : Y.Opens} (hV : IsAffineOpen V)
    (c : cohomologyOn M q (f ⁻¹ᵁ V)) :
    f.higherDirectImageSectionsAddEquiv M q hV c =
      ((f.higherDirectImagePresheafToSheaf q).app M).app (op V)
        ((f.higherDirectImagePresheafToPresheafIso M q).inv.app (op V) c) := by
  have e := f.higherDirectImageSectionsAddEquiv_higherDirectImagePresheafToPresheafIso_hom_app
    M q hV ((f.higherDirectImagePresheafToPresheafIso M q).inv.app (op V) c)
  simp only [Iso.inv_hom_id_app_apply] at e
  exact e.trans ((f.higherDirectImagePresheafSectionsLinearEquiv_apply M q hV _).trans rfl)

end ToSheaf

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

/-- For a commutative square `g' ≫ f = f' ≫ g`, taking preimages of opens of `Y` along the two
sides of the square agree. -/
def preimageSquareIso (h : g' ≫ f = f' ≫ g) :
    (TopologicalSpace.Opens.map f.base).op ⋙ (TopologicalSpace.Opens.map g'.base).op ≅
      (TopologicalSpace.Opens.map g.base).op ⋙ (TopologicalSpace.Opens.map f'.base).op :=
  NatIso.ofComponents (fun U ↦ eqToIso (congrArg op
    (congrArg (fun φ : X' ⟶ Y ↦ φ ⁻¹ᵁ U.unop) h))) (fun _ ↦ rfl)

variable (h : g' ≫ f = f' ≫ g) (q : ℕ)

/-- The base change map on the presheaves `V ↦ H^q(f⁻¹ V, M)` of a commutative square
`g' ≫ f = f' ≫ g`, as a morphism of abelian presheaves on `Y`: over an open `V` of `Y` it is the
pullback `H^q(f⁻¹ V, M) ⟶ H^q(g'⁻¹ f⁻¹ V, g'^* M) = H^q(f'⁻¹ g⁻¹ V, g'^* M)`. -/
def higherDirectImagePresheafBaseChangeToPresheaf (M : X.Modules) :
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj ((f.higherDirectImagePresheaf q).obj M) ⟶
      (TopologicalSpace.Opens.map g.base).op ⋙
        (PresheafOfModules.toPresheaf Y'.ringCatSheaf.obj).obj
          ((f'.higherDirectImagePresheaf q).obj ((Scheme.Modules.pullback g').obj M)) :=
  (f.higherDirectImagePresheafToPresheafIso M q).hom ≫
    Functor.whiskerLeft (TopologicalSpace.Opens.map f.base).op
      (g'.cohomologyPresheafPullback M q) ≫
    Functor.whiskerRight (preimageSquareIso h).hom
      (((SheafOfModules.toSheaf X'.ringCatSheaf).obj
        ((Scheme.Modules.pullback g').obj M)).cohomologyPresheaf q) ≫
    Functor.whiskerLeft (TopologicalSpace.Opens.map g.base).op
      (f'.higherDirectImagePresheafToPresheafIso _ q).inv

omit q in
include h in
/-- The two sides of a commutative square have the same preimages of opens. -/
lemma preimage_eq_of_comp_eq (V : Y.Opens) : f' ⁻¹ᵁ g ⁻¹ᵁ V = g' ⁻¹ᵁ f ⁻¹ᵁ V :=
  (congrArg (fun φ : X' ⟶ Y ↦ φ ⁻¹ᵁ V) h).symm

/-- The base change map on presheaves is, over an open `V` of `Y`, the pullback
`H^q(f⁻¹ V, M) ⟶ H^q(g'⁻¹ f⁻¹ V, g'^* M) = H^q(f'⁻¹ g⁻¹ V, g'^* M)` read through the
identifications of the presheaves `V ↦ H^q(f⁻¹ V, M)` with cohomology. -/
lemma higherDirectImagePresheafBaseChangeToPresheaf_app_apply (M : X.Modules) (V : Y.Opens)
    (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImagePresheafBaseChangeToPresheaf h q M).app (op V) x =
      (f'.higherDirectImagePresheafToPresheafIso _ q).inv.app (op (g ⁻¹ᵁ V))
        (cohomologyOnRes _ q (preimage_eq_of_comp_eq h V).le
          (g'.cohomologyOnPullback M q (f ⁻¹ᵁ V)
            ((f.higherDirectImagePresheafToPresheafIso M q).hom.app (op V) x))) :=
  (rfl)

/-- The base change map on presheaves is linear over the global functions of `Y`, acting on
`H^q(f'⁻¹ g⁻¹ V, g'^* M)` through `g`. -/
lemma higherDirectImagePresheafBaseChangeToPresheaf_app_smul (M : X.Modules) (V : Y.Opens)
    (r : Γ(Y, ⊤)) (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImagePresheafBaseChangeToPresheaf h q M).app (op V)
        ((show Y.ringCatSheaf.obj.obj (op V) from Y.presheaf.map V.leTop.op r) • x) =
      (show Y'.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V)) from
        Y'.presheaf.map (g ⁻¹ᵁ V).leTop.op (g.appTop r)) •
        (show ((f'.higherDirectImagePresheaf q).obj _).obj (op (g ⁻¹ᵁ V)) from
          (higherDirectImagePresheafBaseChangeToPresheaf h q M).app (op V) x) := by
  rw [higherDirectImagePresheafBaseChangeToPresheaf_app_apply,
    higherDirectImagePresheafBaseChangeToPresheaf_app_apply,
    higherDirectImagePresheafToPresheafIso_hom_app_smul, cohomologyOnPullback_smul,
    ← cohomologyOnResLinear_apply, LinearMap.map_smul, cohomologyOnResLinear_apply]
  have hr : g'.appTop (f.appTop r) = f'.appTop (g.appTop r) :=
    congrArg (fun φ : X' ⟶ Y ↦ φ.appTop r) h
  rw [hr]
  apply (ConcreteCategory.bijective_of_isIso
    ((f'.higherDirectImagePresheafToPresheafIso _ q).hom.app (op (g ⁻¹ᵁ V)))).injective
  rw [higherDirectImagePresheafToPresheafIso_hom_app_smul]
  simp only [Iso.inv_hom_id_app_apply]

/-- The base change map on presheaves is natural in the coefficient module. -/
lemma higherDirectImagePresheafBaseChangeToPresheaf_app_map {M N : X.Modules} (φ : M ⟶ N)
    (V : Y.Opens) (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImagePresheafBaseChangeToPresheaf h q N).app (op V)
        (((f.higherDirectImagePresheaf q).map φ).app (op V) x) =
      ((f'.higherDirectImagePresheaf q).map ((Scheme.Modules.pullback g').map φ)).app
        (op (g ⁻¹ᵁ V)) ((higherDirectImagePresheafBaseChangeToPresheaf h q M).app (op V) x) := by
  rw [higherDirectImagePresheafBaseChangeToPresheaf_app_apply,
    higherDirectImagePresheafBaseChangeToPresheaf_app_apply,
    higherDirectImagePresheafToPresheafIso_hom_app_map,
    ← higherDirectImagePresheafToPresheafIso_inv_app_cohomologyOnMap]
  refine congrArg _ ((congrArg _ (ConcreteCategory.congr_hom
    (g'.cohomologyOnMap_comp_cohomologyOnPullback φ q _) _)).trans ?_)
  exact (cohomologyOnMap_cohomologyOnRes _ q _ _).symm

/-- The base change map `H^q(f⁻¹ V, M) ⟶ Γ(g⁻¹ V, R^q f'_* g'^* M)` over the opens `V` of `Y`,
as a morphism of abelian presheaves on `Y` into the pushforward along `g`. -/
def higherDirectImageBaseChangeToPresheaf (M : X.Modules) :
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj ((f.higherDirectImagePresheaf q).obj M) ⟶
      ((Scheme.Modules.pushforward g).obj
        ((f'.higherDirectImage q).obj ((Scheme.Modules.pullback g').obj M))).presheaf :=
  higherDirectImagePresheafBaseChangeToPresheaf h q M ≫
    Functor.whiskerLeft (TopologicalSpace.Opens.map g.base).op
      ((PresheafOfModules.toPresheaf Y'.ringCatSheaf.obj).map
        ((f'.higherDirectImagePresheafToSheaf q).app _))

/-- The base change map into `g_* R^q f'_* g'^* M` is the base change map of presheaves followed
by sheafification. -/
lemma higherDirectImageBaseChangeToPresheaf_app_apply (M : X.Modules) (V : Y.Opens)
    (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImageBaseChangeToPresheaf h q M).app (op V) x =
      ((f'.higherDirectImagePresheafToSheaf q).app _).app (op (g ⁻¹ᵁ V))
        ((higherDirectImagePresheafBaseChangeToPresheaf h q M).app (op V) x) :=
  (rfl)

/-- The base change map into `g_* R^q f'_* g'^* M` is linear over the global functions of `Y`. -/
lemma higherDirectImageBaseChangeToPresheaf_app_smul (M : X.Modules) (V : Y.Opens)
    (r : Γ(Y, ⊤)) (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImageBaseChangeToPresheaf h q M).app (op V)
        ((show Y.ringCatSheaf.obj.obj (op V) from Y.presheaf.map V.leTop.op r) • x) =
      (show Γ(Y, V) from Y.presheaf.map V.leTop.op r) •
        (show Γ((Scheme.Modules.pushforward g).obj
          ((f'.higherDirectImage q).obj ((Scheme.Modules.pullback g').obj M)), V) from
          (higherDirectImageBaseChangeToPresheaf h q M).app (op V) x) := by
  have hg : g.app V (Y.presheaf.map V.leTop.op r) =
      Y'.presheaf.map (g ⁻¹ᵁ V).leTop.op (g.appTop r) :=
    ConcreteCategory.congr_hom (g.naturality V.leTop.op) r
  rw [higherDirectImageBaseChangeToPresheaf_app_apply,
    higherDirectImageBaseChangeToPresheaf_app_apply,
    higherDirectImagePresheafBaseChangeToPresheaf_app_smul]
  refine ((((f'.higherDirectImagePresheafToSheaf q).app _).app _).hom.map_smul _ _).trans ?_
  -- functions on `V` act on sections of `g_* N` over `V` through `g`
  rw [← hg]
  rfl

/-- The base change map into `g_* R^q f'_* g'^* M` is natural in `M`. -/
lemma higherDirectImageBaseChangeToPresheaf_app_map {M N : X.Modules} (φ : M ⟶ N)
    (V : Y.Opens) (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImageBaseChangeToPresheaf h q N).app (op V)
        (((f.higherDirectImagePresheaf q).map φ).app (op V) x) =
      ((f'.higherDirectImage q).map ((Scheme.Modules.pullback g').map φ)).app (g ⁻¹ᵁ V)
        ((higherDirectImageBaseChangeToPresheaf h q M).app (op V) x) := by
  rw [higherDirectImageBaseChangeToPresheaf_app_apply,
    higherDirectImageBaseChangeToPresheaf_app_apply,
    higherDirectImagePresheafBaseChangeToPresheaf_app_map]
  exact ConcreteCategory.congr_hom (congrArg (fun ψ ↦ ψ.app (op (g ⁻¹ᵁ V)))
    ((f'.higherDirectImagePresheafToSheaf q).naturality ((Scheme.Modules.pullback g').map φ))) _

variable [IsAffine Y]

/-- The base change map from the presheaf of modules `V ↦ H^q(f⁻¹ V, M)` to
`g_* R^q f'_* g'^* M`, as a morphism of presheaves of modules. It is linear over all functions
because the base `Y` is affine (`Scheme.Modules.app_smul_of_isAffine`). -/
def higherDirectImagePresheafBaseChange (M : X.Modules) :
    (f.higherDirectImagePresheaf q).obj M ⟶
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).obj
        ((Scheme.Modules.pushforward g).obj
          ((f'.higherDirectImage q).obj ((Scheme.Modules.pullback g').obj M))) :=
  PresheafOfModules.homMk (higherDirectImageBaseChangeToPresheaf h q M) fun U r x ↦
    Scheme.Modules.app_smul_of_isAffine (higherDirectImageBaseChangeToPresheaf h q M)
      (higherDirectImageBaseChangeToPresheaf_app_smul h q M) U.unop r x

/-- The base change map of presheaves of modules is natural in the coefficient module. -/
lemma higherDirectImagePresheafBaseChange_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (f.higherDirectImagePresheaf q).map φ ≫ higherDirectImagePresheafBaseChange h q N =
      higherDirectImagePresheafBaseChange h q M ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
          ((Scheme.Modules.pushforward g).map
            ((f'.higherDirectImage q).map ((Scheme.Modules.pullback g').map φ))) := by
  ext V x
  exact higherDirectImageBaseChangeToPresheaf_app_map h q φ V.unop x

/-- **The base change map, adjoint form.** For a commutative square `g' ≫ f = f' ≫ g` with
affine `Y`, the map `R^q f_* M ⟶ g_* R^q f'_* g'^* M`, natural in `M`. Over an open `V` of `Y`
it is the sheafification of the pullback `H^q(f⁻¹ V, M) ⟶ H^q(f'⁻¹ g⁻¹ V, g'^* M)`
(`higherDirectImagePresheafToSheaf_comp_higherDirectImageBaseChangeAdj`). -/
def higherDirectImageBaseChangeAdj :
    f.higherDirectImage q ⟶ Scheme.Modules.pullback g' ⋙ f'.higherDirectImage q ⋙
      Scheme.Modules.pushforward g where
  app M := ((f.higherDirectImagePresheafSheafificationIso q).app M).inv ≫
    ((PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).homEquiv _ _).symm
      (higherDirectImagePresheafBaseChange h q M)
  naturality M N φ := by
    let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
    have h₁ := (f.higherDirectImagePresheafSheafificationIso q).inv.naturality φ
    have h₂ := adj.homEquiv_naturality_left_symm ((f.higherDirectImagePresheaf q).map φ)
      (higherDirectImagePresheafBaseChange h q N)
    have h₃ := adj.homEquiv_naturality_right_symm (higherDirectImagePresheafBaseChange h q M)
      ((Scheme.Modules.pushforward g).map
        ((f'.higherDirectImage q).map ((Scheme.Modules.pullback g').map φ)))
    rw [higherDirectImagePresheafBaseChange_naturality] at h₂
    dsimp only [Functor.comp_obj, Functor.comp_map] at h₁ ⊢
    erw [reassoc_of% h₁, ← h₂, h₃]
    simp only [adj, Iso.app_inv]
    exact (Category.assoc _ _ _).symm

/-- The adjoint base change map restricts, on the presheaf `V ↦ H^q(f⁻¹ V, M)`, to the base change
map of presheaves: it is the sheafification of pullback on cohomology. -/
lemma higherDirectImagePresheafToSheaf_comp_higherDirectImageBaseChangeAdj (M : X.Modules) :
    (f.higherDirectImagePresheafToSheaf q).app M ≫
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
        ((higherDirectImageBaseChangeAdj h q).app M) =
      higherDirectImagePresheafBaseChange h q M := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  have e₁ : (f.higherDirectImagePresheafToSheaf q).app M = adj.unit.app _ ≫
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
        ((f.higherDirectImagePresheafSheafificationIso q).hom.app M) := rfl
  have e₂ : (f.higherDirectImagePresheafSheafificationIso q).hom.app M ≫
      (higherDirectImageBaseChangeAdj h q).app M =
        (adj.homEquiv _ _).symm (higherDirectImagePresheafBaseChange h q M) :=
    Iso.hom_inv_id_app_assoc _ _ _
  rw [e₁, Category.assoc]
  refine (congrArg (adj.unit.app _ ≫ ·) ((Functor.map_comp (SheafOfModules.forget _ ⋙
    PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)) _ _).symm.trans
      (congrArg _ e₂))).trans ?_
  exact (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- **The base change map.** For a commutative square `g' ≫ f = f' ≫ g` of schemes with affine
`Y`, the base change map `g^* R^q f_* M ⟶ R^q f'_* g'^* M` of higher direct images, natural in the
sheaf of modules `M`. It is adjoint to `higherDirectImageBaseChangeAdj`, whose sections are
pullback on cohomology. -/
def higherDirectImageBaseChange :
    f.higherDirectImage q ⋙ Scheme.Modules.pullback g ⟶
      Scheme.Modules.pullback g' ⋙ f'.higherDirectImage q :=
  Functor.whiskerRight (higherDirectImageBaseChangeAdj h q) (Scheme.Modules.pullback g) ≫
    Functor.whiskerLeft (Scheme.Modules.pullback g' ⋙ f'.higherDirectImage q)
      (Scheme.Modules.pullbackPushforwardAdjunction g).counit

/-- The base change map is adjoint to `higherDirectImageBaseChangeAdj`. -/
lemma higherDirectImageBaseChange_app (M : X.Modules) :
    (higherDirectImageBaseChange h q).app M =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
        ((higherDirectImageBaseChangeAdj h q).app M) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_counit _ _ _).symm

/-- The base change map is adjoint to `higherDirectImageBaseChangeAdj`. -/
lemma homEquiv_higherDirectImageBaseChange_app (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((higherDirectImageBaseChange h q).app M) =
      (higherDirectImageBaseChangeAdj h q).app M := by
  rw [higherDirectImageBaseChange_app]
  exact Equiv.apply_symm_apply _ _

/-- **Sections of the base change map.** Over an open `V` of `Y`, the adjoint base change map
sends the section of `R^q f_* M` defined by a class `c ∈ H^q(f⁻¹ V, M)` to the section of
`R^q f'_* g'^* M` over `g⁻¹ V` defined by the pullback of `c` to
`H^q(g'⁻¹ f⁻¹ V, g'^* M) = H^q(f'⁻¹ g⁻¹ V, g'^* M)`. -/
lemma higherDirectImageBaseChangeAdj_app_app_presheafToSheaf (M : X.Modules) (V : Y.Opens)
    (c : cohomologyOn M q (f ⁻¹ᵁ V)) :
    ((higherDirectImageBaseChangeAdj h q).app M).app V
        (((f.higherDirectImagePresheafToSheaf q).app M).app (op V)
          ((f.higherDirectImagePresheafToPresheafIso M q).inv.app (op V) c)) =
      ((f'.higherDirectImagePresheafToSheaf q).app _).app (op (g ⁻¹ᵁ V))
        ((f'.higherDirectImagePresheafToPresheafIso _ q).inv.app (op (g ⁻¹ᵁ V))
          (cohomologyOnRes _ q (preimage_eq_of_comp_eq h V).le
            (g'.cohomologyOnPullback M q (f ⁻¹ᵁ V) c))) := by
  have e := ConcreteCategory.congr_hom (congrArg (fun ψ ↦ ψ.app (op V))
    (higherDirectImagePresheafToSheaf_comp_higherDirectImageBaseChangeAdj h q M))
    ((f.higherDirectImagePresheafToPresheafIso M q).inv.app (op V) c)
  refine e.trans ?_
  change ((f'.higherDirectImagePresheafToSheaf q).app _).app (op (g ⁻¹ᵁ V))
    ((higherDirectImagePresheafBaseChangeToPresheaf h q M).app (op V) _) = _
  refine congrArg _ ((higherDirectImagePresheafBaseChangeToPresheaf_app_apply h q M V _).trans ?_)
  simp only [Iso.inv_hom_id_app_apply]

/-- **Compatibility with cohomology over affine opens.** For quasi-compact quasi-separated `f` and
`f'`, quasi-coherent `M`, an affine open `V` of `Y` and `g⁻¹ V` affine, the base change map on
sections over `V`, read through `Γ(V, R^q f_* M) = H^q(f⁻¹ V, M)` and
`Γ(g⁻¹ V, R^q f'_* g'^* M) = H^q(f'⁻¹ g⁻¹ V, g'^* M)`, is pullback on cohomology along `g'`. -/
theorem higherDirectImageBaseChangeAdj_app_sectionsAddEquiv
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (M : X.Modules) [M.IsQuasicoherent] {V : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (g ⁻¹ᵁ V)) (c : cohomologyOn M q (f ⁻¹ᵁ V)) :
    ((higherDirectImageBaseChangeAdj h q).app M).app V
        (f.higherDirectImageSectionsAddEquiv M q hV c) =
      f'.higherDirectImageSectionsAddEquiv _ q hV'
        (cohomologyOnRes _ q (preimage_eq_of_comp_eq h V).le
          (g'.cohomologyOnPullback M q (f ⁻¹ᵁ V) c)) := by
  rw [higherDirectImageSectionsAddEquiv_eq_presheafToSheaf,
    higherDirectImageSectionsAddEquiv_eq_presheafToSheaf]
  exact higherDirectImageBaseChangeAdj_app_app_presheafToSheaf h q M V c

end BaseChange

end AlgebraicGeometry.Scheme.Hom
