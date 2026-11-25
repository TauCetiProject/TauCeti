/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Quasicoherent
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic
public import TauCeti.AlgebraicGeometry.Cohomology.Pullback
public import TauCeti.AlgebraicGeometry.Scheme.Opens
import TauCeti.AlgebraicGeometry.Modules.AffineGlobalSections

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

`TauCeti.AlgebraicGeometry.higherDirectImageBaseChange h q : g^* R^q f_* M ⟶ R^q f'_* g'^* M`,

natural in the sheaf of modules `M`, together with its transpose under `g^* ⊣ g_*`

`TauCeti.AlgebraicGeometry.higherDirectImageBaseChangeTranspose h q :
  R^q f_* M ⟶ g_* R^q f'_* g'^* M`.

No hypothesis on `f`, `g` or `M` is needed, and the square need not be cartesian.

`R^q f_* M` is the sheafification of the presheaf of modules `V ↦ H^q(f⁻¹ V, M)`
(`Scheme.Hom.higherDirectImagePresheafSheafificationIso`). Over an open `V` of `Y`, pullback on
cohomology along `g'` (`Scheme.Hom.cohomologyOnPullback`) is a map
`H^q(f⁻¹ V, M) ⟶ H^q(g'⁻¹ f⁻¹ V, g'^* M) = H^q(f'⁻¹ g⁻¹ V, g'^* M)`, compatible with restriction,
so these maps form a morphism from that presheaf to `g_* R^q f'_* g'^* M`
(`TauCeti.AlgebraicGeometry.higherDirectImagePresheafBaseChangeToPresheaf`). Sheafification and the
adjunction `g^* ⊣ g_*` turn it into the base change map.

The one point that uses the affineness of `Y` is linearity. The identification of
`V ↦ H^q(f⁻¹ V, M)` with cohomology is known to be compatible with the action of global functions
of `Y` (`Scheme.Hom.higherDirectImagePresheafToPresheafIso_hom_app_smul`), and so is pullback on
cohomology (`Scheme.Hom.cohomologyOnPullback_smul`). On an affine scheme, a map of abelian
presheaves into a sheaf of modules that is linear over global functions is linear over all
functions (`Scheme.Modules.app_smul_of_isAffine`), since a function on a basic open `D(s)` is a
global function divided by a power of `s`.

Over an affine open `V` of `Y` with `g⁻¹ V` affine, for quasi-compact quasi-separated `f` and `f'`
and quasi-coherent `M`, the sections of the transposed base change map are pullback on cohomology,
under the identifications of sections of higher direct images with cohomology
(`TauCeti.AlgebraicGeometry.higherDirectImageBaseChangeTranspose_app_sectionsAddEquiv`). At
`V = ⊤` this is the map `Scheme.Hom.cohomologyPullback` whose linear extension is the flat base
change map `TauCeti.AlgebraicGeometry.cohomologyBaseChange` over an affine base. Similarly, on an
affine open `V'` of `Y'` lying over an affine open `V` of `Y`, the base change map itself sends
the pullback of the section defined by a class in `H^q(f⁻¹ V, M)` to the section defined by its
pullback to `H^q(f'⁻¹ V', g'^* M)`
(`higherDirectImageBaseChange_app_app_pullbackSectionsLE_sectionsAddEquiv`).

## Main declarations

* `TauCeti.AlgebraicGeometry.higherDirectImageBaseChange`: the base change map
  `g^* R^q f_* M ⟶ R^q f'_* g'^* M`, natural in `M`, for affine `Y`;
* `TauCeti.AlgebraicGeometry.higherDirectImageBaseChangeTranspose`: its transpose
  `R^q f_* M ⟶ g_* R^q f'_* g'^* M`;
* `TauCeti.AlgebraicGeometry.higherDirectImageBaseChangeTranspose_app_app_presheafToSheaf` and
  `TauCeti.AlgebraicGeometry.higherDirectImageBaseChangeTranspose_app_sectionsAddEquiv`:
  its sections are pullback on cohomology;
* `higherDirectImageBaseChange_app_app_pullbackSectionsLE_sectionsAddEquiv`:
  the same for the base change map itself, on pullbacks of sections to an affine open `V` of `Y'`
  lying over an affine open `U` of `Y`, with `g⁻¹ U` arbitrary.

## References

* [The Stacks Project, Lemma 30.5.2](https://stacks.math.columbia.edu/tag/02KH), flat base
  change, for which this is the comparison map.
-/

public section

open CategoryTheory Opposite AlgebraicGeometry Scheme.Modules

universe u

noncomputable section

namespace TauCeti.AlgebraicGeometry

open Scheme.Modules Scheme.Hom

section BaseChange

variable {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}

variable (h : g' ≫ f = f' ≫ g) (q : ℕ)

/-- The base change map on the presheaves `V ↦ H^q(f⁻¹ V, M)` of a commutative square
`g' ≫ f = f' ≫ g`, as a morphism of abelian presheaves on `Y`: over an open `V` of `Y` it is the
pullback `H^q(f⁻¹ V, M) ⟶ H^q(g'⁻¹ f⁻¹ V, g'^* M) = H^q(f'⁻¹ g⁻¹ V, g'^* M)`. -/
def higherDirectImagePresheafMapBaseChange (M : X.Modules) :
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

/-- The base change map on presheaves is, over an open `V` of `Y`, the pullback
`H^q(f⁻¹ V, M) ⟶ H^q(g'⁻¹ f⁻¹ V, g'^* M) = H^q(f'⁻¹ g⁻¹ V, g'^* M)` read through the
identifications of the presheaves `V ↦ H^q(f⁻¹ V, M)` with cohomology. -/
lemma higherDirectImagePresheafMapBaseChange_app_apply (M : X.Modules) (V : Y.Opens)
    (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImagePresheafMapBaseChange h q M).app (op V) x =
      (f'.higherDirectImagePresheafToPresheafIso _ q).inv.app (op (g ⁻¹ᵁ V))
        (cohomologyOnRes _ q (preimage_preimage_eq_of_comp_eq h V).le
          (g'.cohomologyOnPullback M q (f ⁻¹ᵁ V)
            ((f.higherDirectImagePresheafToPresheafIso M q).hom.app (op V) x))) := by
  dsimp only [higherDirectImagePresheafMapBaseChange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [cohomologyPresheafPullback_app]
  -- The component of `preimageSquareIso h` is an `eqToHom` between opens. Morphisms of opens are
  -- proofs of inclusions, so it is definitionally the `homOfLE` of the inclusion that defines
  -- `cohomologyOnRes`, and the cohomology presheaf maps along both agree by definition.
  rfl

/-- The base change map on presheaves is linear over the global functions of `Y`, acting on
`H^q(f'⁻¹ g⁻¹ V, g'^* M)` through `g`. -/
lemma higherDirectImagePresheafMapBaseChange_app_smul (M : X.Modules) (V : Y.Opens)
    (r : Γ(Y, ⊤)) (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImagePresheafMapBaseChange h q M).app (op V)
        ((show Y.ringCatSheaf.obj.obj (op V) from Y.presheaf.map V.leTop.op r) • x) =
      (show Y'.ringCatSheaf.obj.obj (op (g ⁻¹ᵁ V)) from
        Y'.presheaf.map (g ⁻¹ᵁ V).leTop.op (g.appTop r)) •
        (show ((f'.higherDirectImagePresheaf q).obj _).obj (op (g ⁻¹ᵁ V)) from
          (higherDirectImagePresheafMapBaseChange h q M).app (op V) x) := by
  rw [higherDirectImagePresheafMapBaseChange_app_apply,
    higherDirectImagePresheafMapBaseChange_app_apply,
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
lemma higherDirectImagePresheafMapBaseChange_app_map {M N : X.Modules} (φ : M ⟶ N)
    (V : Y.Opens) (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImagePresheafMapBaseChange h q N).app (op V)
        (((f.higherDirectImagePresheaf q).map φ).app (op V) x) =
      ((f'.higherDirectImagePresheaf q).map ((Scheme.Modules.pullback g').map φ)).app
        (op (g ⁻¹ᵁ V)) ((higherDirectImagePresheafMapBaseChange h q M).app (op V) x) := by
  rw [higherDirectImagePresheafMapBaseChange_app_apply,
    higherDirectImagePresheafMapBaseChange_app_apply,
    higherDirectImagePresheafToPresheafIso_hom_app_map,
    ← higherDirectImagePresheafToPresheafIso_inv_app_cohomologyOnMap]
  refine congrArg _ ((congrArg _ (ConcreteCategory.congr_hom
    (g'.cohomologyOnMap_comp_cohomologyOnPullback φ q _) _)).trans ?_)
  exact (cohomologyOnMap_cohomologyOnRes _ q _ _).symm

/-- The base change map `H^q(f⁻¹ V, M) ⟶ Γ(g⁻¹ V, R^q f'_* g'^* M)` over the opens `V` of `Y`,
as a morphism of abelian presheaves on `Y` into the pushforward along `g`. -/
def higherDirectImagePresheafBaseChangeToPresheaf (M : X.Modules) :
    (PresheafOfModules.toPresheaf Y.ringCatSheaf.obj).obj ((f.higherDirectImagePresheaf q).obj M) ⟶
      ((Scheme.Modules.pushforward g).obj
        ((f'.higherDirectImage q).obj ((Scheme.Modules.pullback g').obj M))).presheaf :=
  higherDirectImagePresheafMapBaseChange h q M ≫
    Functor.whiskerLeft (TopologicalSpace.Opens.map g.base).op
      ((PresheafOfModules.toPresheaf Y'.ringCatSheaf.obj).map
        ((f'.higherDirectImagePresheafToSheaf q).app _))

/-- The base change map into `g_* R^q f'_* g'^* M` is the base change map of presheaves followed
by sheafification. -/
lemma higherDirectImagePresheafBaseChangeToPresheaf_app_apply (M : X.Modules) (V : Y.Opens)
    (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImagePresheafBaseChangeToPresheaf h q M).app (op V) x =
      ((f'.higherDirectImagePresheafToSheaf q).app _).app (op (g ⁻¹ᵁ V))
        ((higherDirectImagePresheafMapBaseChange h q M).app (op V) x) :=
  (rfl)

/-- The base change map into `g_* R^q f'_* g'^* M` is linear over the global functions of `Y`. -/
lemma higherDirectImagePresheafBaseChangeToPresheaf_app_smul (M : X.Modules) (V : Y.Opens)
    (r : Γ(Y, ⊤)) (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImagePresheafBaseChangeToPresheaf h q M).app (op V)
        ((show Y.ringCatSheaf.obj.obj (op V) from Y.presheaf.map V.leTop.op r) • x) =
      (show Γ(Y, V) from Y.presheaf.map V.leTop.op r) •
        (show Γ((Scheme.Modules.pushforward g).obj
          ((f'.higherDirectImage q).obj ((Scheme.Modules.pullback g').obj M)), V) from
          (higherDirectImagePresheafBaseChangeToPresheaf h q M).app (op V) x) := by
  have hg : g.app V (Y.presheaf.map V.leTop.op r) =
      Y'.presheaf.map (g ⁻¹ᵁ V).leTop.op (g.appTop r) :=
    ConcreteCategory.congr_hom (g.naturality V.leTop.op) r
  rw [higherDirectImagePresheafBaseChangeToPresheaf_app_apply,
    higherDirectImagePresheafBaseChangeToPresheaf_app_apply,
    higherDirectImagePresheafMapBaseChange_app_smul]
  refine ((((f'.higherDirectImagePresheafToSheaf q).app _).app _).hom.map_smul _ _).trans ?_
  -- functions on `V` act on sections of `g_* N` over `V` through `g`
  rw [← hg]
  rfl

/-- The base change map into `g_* R^q f'_* g'^* M` is natural in `M`. -/
lemma higherDirectImagePresheafBaseChangeToPresheaf_app_map {M N : X.Modules} (φ : M ⟶ N)
    (V : Y.Opens) (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImagePresheafBaseChangeToPresheaf h q N).app (op V)
        (((f.higherDirectImagePresheaf q).map φ).app (op V) x) =
      ((f'.higherDirectImage q).map ((Scheme.Modules.pullback g').map φ)).app (g ⁻¹ᵁ V)
        ((higherDirectImagePresheafBaseChangeToPresheaf h q M).app (op V) x) := by
  rw [higherDirectImagePresheafBaseChangeToPresheaf_app_apply,
    higherDirectImagePresheafBaseChangeToPresheaf_app_apply,
    higherDirectImagePresheafMapBaseChange_app_map]
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
  PresheafOfModules.homMk (higherDirectImagePresheafBaseChangeToPresheaf h q M) fun U r x ↦
    Scheme.Modules.app_smul_of_isAffine (higherDirectImagePresheafBaseChangeToPresheaf h q M)
      (higherDirectImagePresheafBaseChangeToPresheaf_app_smul h q M) U.unop r x

/-- The base change map of presheaves of modules has the same underlying maps of sections as the
base change map of abelian presheaves `higherDirectImagePresheafBaseChangeToPresheaf`. -/
lemma higherDirectImagePresheafBaseChange_app_apply (M : X.Modules) (V : Y.Opens)
    (x : ((f.higherDirectImagePresheaf q).obj M).obj (op V)) :
    (higherDirectImagePresheafBaseChange h q M).app (op V) x =
      (higherDirectImagePresheafBaseChangeToPresheaf h q M).app (op V) x :=
  (rfl)

/-- The base change map of presheaves of modules is natural in the coefficient module. -/
lemma higherDirectImagePresheafBaseChange_naturality {M N : X.Modules} (φ : M ⟶ N) :
    (f.higherDirectImagePresheaf q).map φ ≫ higherDirectImagePresheafBaseChange h q N =
      higherDirectImagePresheafBaseChange h q M ≫
        (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
          ((Scheme.Modules.pushforward g).map
            ((f'.higherDirectImage q).map ((Scheme.Modules.pullback g').map φ))) := by
  ext V x
  exact higherDirectImagePresheafBaseChangeToPresheaf_app_map h q φ V.unop x

/-- **The base change map, transposed.** For a commutative square `g' ≫ f = f' ≫ g` with
affine `Y`, the map `R^q f_* M ⟶ g_* R^q f'_* g'^* M`, natural in `M`. Over an open `V` of `Y`
it is the sheafification of the pullback `H^q(f⁻¹ V, M) ⟶ H^q(f'⁻¹ g⁻¹ V, g'^* M)`
(`higherDirectImagePresheafToSheaf_comp_higherDirectImageBaseChangeTranspose`). -/
def higherDirectImageBaseChangeTranspose :
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
    simp only [Iso.app_inv, Functor.comp_map]
    -- Chain the three squares with `Eq.trans`: it identifies `Y.PresheafOfModules` with
    -- `PresheafOfModules Y.ringCatSheaf.obj` in the objects, which `rw` does not.
    exact ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) h₁).trans (Category.assoc _ _ _))).trans
      ((congrArg (_ ≫ ·) (h₂.symm.trans h₃)).trans (Category.assoc _ _ _).symm)

/-- The transposed base change map restricts, on the presheaf `V ↦ H^q(f⁻¹ V, M)`, to the base
change map of presheaves: it is the sheafification of pullback on cohomology. -/
lemma higherDirectImagePresheafToSheaf_comp_higherDirectImageBaseChangeTranspose (M : X.Modules) :
    (f.higherDirectImagePresheafToSheaf q).app M ≫
      (SheafOfModules.forget _ ⋙ PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).map
        ((higherDirectImageBaseChangeTranspose h q).app M) =
      higherDirectImagePresheafBaseChange h q M := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)
  have e₂ : (f.higherDirectImagePresheafSheafificationIso q).hom.app M ≫
      (higherDirectImageBaseChangeTranspose h q).app M =
        (adj.homEquiv _ _).symm (higherDirectImagePresheafBaseChange h q M) :=
    Iso.hom_inv_id_app_assoc _ _ _
  rw [higherDirectImagePresheafToSheaf_app, Category.assoc]
  refine (congrArg (adj.unit.app _ ≫ ·) ((Functor.map_comp (SheafOfModules.forget _ ⋙
    PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)) _ _).symm.trans
      (congrArg _ e₂))).trans ?_
  exact (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- **The base change map.** For a commutative square `g' ≫ f = f' ≫ g` of schemes with affine
`Y`, the base change map `g^* R^q f_* M ⟶ R^q f'_* g'^* M` of higher direct images, natural in the
sheaf of modules `M`. It is adjoint to `higherDirectImageBaseChangeTranspose`, whose sections are
pullback on cohomology. -/
def higherDirectImageBaseChange :
    f.higherDirectImage q ⋙ Scheme.Modules.pullback g ⟶
      Scheme.Modules.pullback g' ⋙ f'.higherDirectImage q :=
  Functor.whiskerRight (higherDirectImageBaseChangeTranspose h q) (Scheme.Modules.pullback g) ≫
    Functor.whiskerLeft (Scheme.Modules.pullback g' ⋙ f'.higherDirectImage q)
      (Scheme.Modules.pullbackPushforwardAdjunction g).counit

/-- The base change map is adjoint to `higherDirectImageBaseChangeTranspose`. -/
lemma higherDirectImageBaseChange_app (M : X.Modules) :
    (higherDirectImageBaseChange h q).app M =
      ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _).symm
        ((higherDirectImageBaseChangeTranspose h q).app M) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_counit _ _ _).symm

/-- The base change map is adjoint to `higherDirectImageBaseChangeTranspose`. -/
lemma homEquiv_higherDirectImageBaseChange_app (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
        ((higherDirectImageBaseChange h q).app M) =
      (higherDirectImageBaseChangeTranspose h q).app M := by
  rw [higherDirectImageBaseChange_app]
  exact Equiv.apply_symm_apply _ _

/-- **Sections of the base change map.** Over an open `V` of `Y`, the transposed base change map
sends the section of `R^q f_* M` defined by a class `c ∈ H^q(f⁻¹ V, M)` to the section of
`R^q f'_* g'^* M` over `g⁻¹ V` defined by the pullback of `c` to
`H^q(g'⁻¹ f⁻¹ V, g'^* M) = H^q(f'⁻¹ g⁻¹ V, g'^* M)`. -/
lemma higherDirectImageBaseChangeTranspose_app_app_presheafToSheaf (M : X.Modules) (V : Y.Opens)
    (c : cohomologyOn M q (f ⁻¹ᵁ V)) :
    ((higherDirectImageBaseChangeTranspose h q).app M).app V
        (((f.higherDirectImagePresheafToSheaf q).app M).app (op V)
          ((f.higherDirectImagePresheafToPresheafIso M q).inv.app (op V) c)) =
      ((f'.higherDirectImagePresheafToSheaf q).app _).app (op (g ⁻¹ᵁ V))
        ((f'.higherDirectImagePresheafToPresheafIso _ q).inv.app (op (g ⁻¹ᵁ V))
          (cohomologyOnRes _ q (preimage_preimage_eq_of_comp_eq h V).le
            (g'.cohomologyOnPullback M q (f ⁻¹ᵁ V) c))) := by
  have e := ConcreteCategory.congr_hom (congrArg (fun ψ ↦ ψ.app (op V))
    (higherDirectImagePresheafToSheaf_comp_higherDirectImageBaseChangeTranspose h q M))
    ((f.higherDirectImagePresheafToPresheafIso M q).inv.app (op V) c)
  refine e.trans (((higherDirectImagePresheafBaseChange_app_apply h q M V _).trans
    (higherDirectImagePresheafBaseChangeToPresheaf_app_apply h q M V _)).trans (congrArg _ ?_))
  refine ((higherDirectImagePresheafMapBaseChange_app_apply h q M V _).trans ?_)
  simp only [Iso.inv_hom_id_app_apply]

/-- **Compatibility with cohomology over affine opens.** For quasi-compact quasi-separated `f` and
`f'`, quasi-coherent `M`, an affine open `V` of `Y` and `g⁻¹ V` affine, the base change map on
sections over `V`, read through `Γ(V, R^q f_* M) = H^q(f⁻¹ V, M)` and
`Γ(g⁻¹ V, R^q f'_* g'^* M) = H^q(f'⁻¹ g⁻¹ V, g'^* M)`, is pullback on cohomology along `g'`. -/
theorem higherDirectImageBaseChangeTranspose_app_sectionsAddEquiv
    [QuasiCompact f] [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f']
    (M : X.Modules) [M.IsQuasicoherent] {V : Y.Opens} (hV : IsAffineOpen V)
    (hV' : IsAffineOpen (g ⁻¹ᵁ V)) (c : cohomologyOn M q (f ⁻¹ᵁ V)) :
    ((higherDirectImageBaseChangeTranspose h q).app M).app V
        (f.higherDirectImageSectionsAddEquiv M q hV c) =
      f'.higherDirectImageSectionsAddEquiv _ q hV'
        (cohomologyOnRes _ q (preimage_preimage_eq_of_comp_eq h V).le
          (g'.cohomologyOnPullback M q (f ⁻¹ᵁ V) c)) := by
  rw [higherDirectImageSectionsAddEquiv_eq_presheafToSheaf,
    higherDirectImageSectionsAddEquiv_eq_presheafToSheaf]
  exact higherDirectImageBaseChangeTranspose_app_app_presheafToSheaf h q M V c

/-- **Sections of the base change map on pulled-back sections.** For opens `U` of `Y` and
`V ≤ g⁻¹ U` of `Y'`, the base change map `g^* R^q f_* M ⟶ R^q f'_* g'^* M` sends the pullback to
`V` of a section `s` of `R^q f_* M` over `U` to the restriction to `V` of the image of `s` under
the transposed map `R^q f_* M ⟶ g_* R^q f'_* g'^* M`. -/
lemma higherDirectImageBaseChange_app_app_pullbackSectionsLE (M : X.Modules) (U : Y.Opens)
    (V : Y'.Opens) (hVU : V ≤ g ⁻¹ᵁ U) (s : Γ((f.higherDirectImage q).obj M, U)) :
    ((higherDirectImageBaseChange h q).app M).app V (g.pullbackSectionsLE _ U V hVU s) =
      ((f'.higherDirectImage q).obj ((Scheme.Modules.pullback g').obj M)).presheaf.map
        (homOfLE hVU).op (((higherDirectImageBaseChangeTranspose h q).app M).app U s) := by
  rw [pullbackSectionsLE_apply, ← homEquiv_higherDirectImageBaseChange_app,
    pullbackPushforwardAdjunction_homEquiv_app_apply]
  exact PresheafOfModules.naturality_apply ((higherDirectImageBaseChange h q).app M).val
    (homOfLE hVU).op _

/-- **Sections of the base change map over affine opens.** For quasi-compact quasi-separated `f`
and `f'`, quasi-coherent `M`, affine opens `U` of `Y` and `V ≤ g⁻¹ U` of `Y'`, the base change map
sends the pullback to `V` of the section of `R^q f_* M` over `U` defined by a class
`c ∈ H^q(f⁻¹ U, M)` to the section of `R^q f'_* g'^* M` over `V` defined by the restriction of the
pullback of `c` to `H^q(f'⁻¹ V, g'^* M)`. Unlike
`higherDirectImageBaseChangeTranspose_app_sectionsAddEquiv`, the inverse image `g⁻¹ U` need not be
affine. -/
theorem higherDirectImageBaseChange_app_app_pullbackSectionsLE_sectionsAddEquiv [QuasiCompact f]
    [QuasiSeparated f] [QuasiCompact f'] [QuasiSeparated f'] (M : X.Modules) [M.IsQuasicoherent]
    {U : Y.Opens} (hU : IsAffineOpen U) {V : Y'.Opens} (hV : IsAffineOpen V) (hVU : V ≤ g ⁻¹ᵁ U)
    (c : cohomologyOn M q (f ⁻¹ᵁ U)) :
    ((higherDirectImageBaseChange h q).app M).app V
        (g.pullbackSectionsLE _ U V hVU (f.higherDirectImageSectionsAddEquiv M q hU c)) =
      f'.higherDirectImageSectionsAddEquiv _ q hV
        (cohomologyOnRes _ q ((f'.preimage_mono hVU).trans (preimage_preimage_eq_of_comp_eq h U).le)
          (g'.cohomologyOnPullback M q (f ⁻¹ᵁ U) c)) := by
  rw [higherDirectImageBaseChange_app_app_pullbackSectionsLE,
    higherDirectImageSectionsAddEquiv_eq_presheafToSheaf,
    higherDirectImageBaseChangeTranspose_app_app_presheafToSheaf,
    higherDirectImageSectionsAddEquiv_eq_presheafToSheaf]
  -- Restriction from `g⁻¹ U` to `V` commutes with the passage from cohomology to sections of the
  -- sheafification.
  have h₁ := PresheafOfModules.naturality_apply
    ((f'.higherDirectImagePresheafToSheaf q).app ((Scheme.Modules.pullback g').obj M))
    (homOfLE hVU).op
  have h₂ := NatTrans.naturality_apply
    (f'.higherDirectImagePresheafToPresheafIso ((Scheme.Modules.pullback g').obj M) q).inv
    (homOfLE hVU).op
  rw [← cohomologyOnRes_comp _ q (f'.preimage_mono hVU) (preimage_preimage_eq_of_comp_eq h U).le,
    ConcreteCategory.comp_apply]
  exact ((congrArg _ (h₂ _)).trans (h₁ _)).symm

end BaseChange

end TauCeti.AlgebraicGeometry
