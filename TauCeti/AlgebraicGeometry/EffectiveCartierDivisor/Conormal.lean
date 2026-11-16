/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Pullback
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
public import TauCeti.AlgebraicGeometry.LineBundle.Endomorphisms

/-!
# The conormal sheaf of a section of a smooth relative curve

Let `s : S ⟶ X` be a morphism of schemes, with kernel ideal sheaf `s.ker`. Its **conormal sheaf**
`s.conormalSheaf` is the pullback `s^* s.ker.sheaf` on `S` (computing `I / I²` on affine opens when
`s` is a closed immersion). When `s` is a section of a separated morphism `π : X ⟶ S` that is smooth
of relative dimension one, `s.ker` is an effective Cartier divisor on `X`
(`Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension`), so `s.conormalSheaf` is
an invertible sheaf on `S` (`Scheme.Hom.isInvertible_conormalSheaf`).

Along a commutative square `s' ≫ g = f ≫ s` for which `s'.ker = s.ker.comap g` (in particular, any
cartesian square `IsPullback g π' π f` of separated morphisms carrying a section `s'` to a section
`s`), the ideal-sheaf comparison `pullbackSheafHom` induces a comparison morphism
`conormalPullbackHom : f^* s.conormalSheaf ⟶ s'.conormalSheaf`, which is an isomorphism whenever
`s.ker` and `s'.ker` are effective Cartier divisors (`isIso_conormalPullbackHom`). Consequently, a
global basis `ω : 𝟙_ S.Modules ≅ s.conormalSheaf` pulls back contravariantly along cartesian
pointed squares (`Scheme.Hom.conormalBasisPullback`), compatibly with identities, composition, and
rescaling by global units `Γ(S, 𝒪_S)ˣ` (`Scheme.Modules.unitSmulIso`).

For an elliptic curve over `S` with zero section `0 : S ⟶ E`, `0.conormalSheaf` is the Hodge line
bundle `ω_{E/S}` of invariant differentials (Katz–Mazur, 2.1.6), and global bases
`𝟙_ S.Modules ≅ 0.conormalSheaf` are its nowhere-vanishing invariant differentials.

## Main declarations

* `Scheme.IdealSheafData.pullbackSheafHom_id` and `Scheme.IdealSheafData.pullbackSheafHom_comp`:
  functoriality of the ideal-sheaf pullback comparison;
* `Scheme.Hom.conormalSheaf`: the conormal sheaf `s^* s.ker.sheaf` of `s : S ⟶ X`, invertible for a
  section of a separated smooth relative curve (`Scheme.Hom.isInvertible_conormalSheaf`);
* `Scheme.Hom.conormalPullbackHom`: the comparison `f^* s.conormalSheaf ⟶ s'.conormalSheaf`, with
  `conormalPullbackHom_id`, `conormalPullbackHom_comp`, and `isIso_conormalPullbackHom`;
* `Scheme.Hom.conormalBasisPullback`: contravariant pullback of bases
  `𝟙_ S.Modules ≅ s.conormalSheaf` along cartesian pointed squares of smooth relative curves.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.1.6.
* The Stacks Project, *Divisors*, Section *Regular immersions* (Tag 063M).
-/

public section

open CategoryTheory Limits MonoidalCategory

universe u

namespace AlgebraicGeometry

noncomputable section

namespace Scheme.IdealSheafData

variable {X Y Z : Scheme.{u}}

private lemma pullbackSheafHom_eqToHom_sheafι {I : Y.IdealSheafData} {J : X.IdealSheafData}
    {g : X ⟶ Y} (h : I.comap g = J) :
    (I.pullbackSheafHom g ≫ eqToHom (congrArg sheaf h)) ≫ J.sheafι =
      (Scheme.Modules.pullback g).map I.sheafι ≫ (Scheme.Modules.pullbackObjUnitIso g).hom := by
  subst h
  rw [eqToHom_refl, Category.comp_id, pullbackSheafHom_sheafι]

/-- Along the identity morphism, `pullbackSheafHom` is the identity comparison of module
pullback. -/
lemma pullbackSheafHom_id (I : X.IdealSheafData) :
    I.pullbackSheafHom (𝟙 X) ≫ eqToHom (congrArg sheaf I.comap_id) =
      (Scheme.Modules.pullbackId X).hom.app I.sheaf := by
  refine (cancel_mono I.sheafι).mp ?_
  exact (pullbackSheafHom_eqToHom_sheafι I.comap_id).trans <|
    (congrArg ((Scheme.Modules.pullback (𝟙 X)).map I.sheafι ≫ ·)
      (Scheme.Modules.pullbackObjUnitIso_id X)).trans <|
      (Scheme.Modules.pullbackId X).hom.naturality I.sheafι

/-- Along a composite `f ≫ g`, `pullbackSheafHom` factors through `f^* (I.pullbackSheafHom g)` and
`(I.comap g).pullbackSheafHom f`. -/
lemma pullbackSheafHom_comp (I : Z.IdealSheafData) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (Scheme.Modules.pullbackComp f g).inv.app I.sheaf ≫
        (Scheme.Modules.pullback f).map (I.pullbackSheafHom g) ≫
        (I.comap g).pullbackSheafHom f =
      I.pullbackSheafHom (f ≫ g) ≫ eqToHom (congrArg sheaf (I.comap_comp f g)) := by
  refine (cancel_mono ((I.comap g).comap f).sheafι).mp ?_
  have hstep1 : ((Scheme.Modules.pullback f).map (I.pullbackSheafHom g) ≫
      (I.comap g).pullbackSheafHom f) ≫ ((I.comap g).comap f).sheafι =
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map I.sheafι) ≫
        (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackObjUnitIso g).hom ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom :=
    (Category.assoc _ _ _).trans <|
      (congrArg (_ ≫ ·) ((I.comap g).pullbackSheafHom_sheafι f)).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) (((Scheme.Modules.pullback f).map_comp _ _).symm.trans
        (congrArg (Scheme.Modules.pullback f).map (I.pullbackSheafHom_sheafι g)))).trans <|
      (congrArg (· ≫ _) ((Scheme.Modules.pullback f).map_comp _ _)).trans
        (Category.assoc _ _ _)
  have hstep2 : (Scheme.Modules.pullbackComp f g).inv.app I.sheaf ≫
      ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullback g).map I.sheafι) ≫
        (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackObjUnitIso g).hom ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom) =
      (Scheme.Modules.pullback (f ≫ g)).map I.sheafι ≫
        (Scheme.Modules.pullbackObjUnitIso (f ≫ g)).hom :=
    (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ _) ((Scheme.Modules.pullbackComp f g).inv.naturality I.sheafι).symm).trans <|
      (Category.assoc _ _ _).trans <|
      congrArg (_ ≫ ·) (Scheme.Modules.pullbackObjUnitIso_comp f g)
  exact (Category.assoc _ _ _).trans <|
    (congrArg (_ ≫ ·) hstep1).trans <|
    hstep2.trans (pullbackSheafHom_eqToHom_sheafι (I.comap_comp f g)).symm

private lemma pullbackSheafHom_eqToHom_comp {X' X'' : Scheme.{u}} {I : X.IdealSheafData}
    {J : X'.IdealSheafData} {K : X''.IdealSheafData} {g : X' ⟶ X} {g' : X'' ⟶ X'}
    (hJ : J = I.comap g) (hK : K = J.comap g') (hK' : K = I.comap (g' ≫ g)) :
    (Scheme.Modules.pullback g').map
        (I.pullbackSheafHom g ≫ eqToHom (congrArg IdealSheafData.sheaf hJ.symm)) ≫
      (J.pullbackSheafHom g' ≫ eqToHom (congrArg IdealSheafData.sheaf hK.symm)) =
    (Scheme.Modules.pullbackComp g' g).hom.app I.sheaf ≫
      (I.pullbackSheafHom (g' ≫ g) ≫ eqToHom (congrArg IdealSheafData.sheaf hK'.symm)) := by
  subst hJ hK
  rw [← cancel_epi ((Scheme.Modules.pullbackComp g' g).inv.app I.sheaf), Iso.inv_hom_id_app_assoc,
    eqToHom_refl, Category.comp_id, eqToHom_refl, Category.comp_id]
  exact I.pullbackSheafHom_comp g' g

section PullbackComparison

variable {S X' S' X'' S'' : Scheme.{u}}

/-- Comparison morphism `f^* (p^* I) ⟶ p'^* I'` along a commutative square `p' ≫ g = f ≫ p`
satisfying `I' = I.comap g`. -/
def pullbackComparison (I : X.IdealSheafData) (I' : X'.IdealSheafData)
    {p : S ⟶ X} {p' : S' ⟶ X'} {f : S' ⟶ S} {g : X' ⟶ X}
    (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback p).obj I.sheaf) ⟶
      (Scheme.Modules.pullback p').obj I'.sheaf :=
  (Scheme.Modules.pullbackComp f p).hom.app I.sheaf ≫
    (Scheme.Modules.pullbackCongr h₀.symm).hom.app I.sheaf ≫
    (Scheme.Modules.pullbackComp p' g).inv.app I.sheaf ≫
    (Scheme.Modules.pullback p').map
      (I.pullbackSheafHom g ≫ eqToHom (congrArg sheaf hI.symm))

/-- When `I` and `I'` are effective Cartier divisors and `I' = I.comap g`, `pullbackComparison` is
an isomorphism. -/
theorem isIso_pullbackComparison (I : X.IdealSheafData) (I' : X'.IdealSheafData)
    {p : S ⟶ X} {p' : S' ⟶ X'} {f : S' ⟶ S} {g : X' ⟶ X}
    (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier) :
    IsIso (I.pullbackComparison I' h₀ hI) := by
  have : IsIso (I.pullbackSheafHom g) := I.isIso_pullbackSheafHom g hIC (hI ▸ hI'C)
  dsimp only [pullbackComparison]
  infer_instance

/-- Along the identity square, `pullbackComparison` is the identity comparison of pullback. -/
lemma pullbackComparison_id (I : X.IdealSheafData) (p : S ⟶ X)
    (h₀ : p ≫ 𝟙 X = 𝟙 S ≫ p := by simp) (hI : I = I.comap (𝟙 X) := I.comap_id.symm) :
    I.pullbackComparison I h₀ hI =
      (Scheme.Modules.pullbackId S).hom.app ((Scheme.Modules.pullback p).obj I.sheaf) := by
  refine (cancel_epi ((Scheme.Modules.pullbackComp (𝟙 S) p).inv.app I.sheaf)).mp ?_
  have hid : I.pullbackSheafHom (𝟙 X) ≫ eqToHom (congrArg sheaf hI.symm) =
      (Scheme.Modules.pullbackId X).hom.app I.sheaf := I.pullbackSheafHom_id
  simp only [pullbackComparison, hid, Iso.inv_hom_id_app_assoc,
    Scheme.Modules.pseudofunctor_left_unitality_app,
    Scheme.Modules.pseudofunctor_right_unitality_app]
  simp [Scheme.Modules.pullbackCongr]

/-- Along two stacked squares, `pullbackComparison` composes through `pullbackComp`. -/
lemma pullbackComparison_comp (I : X.IdealSheafData) (I' : X'.IdealSheafData)
    (I'' : X''.IdealSheafData) {p : S ⟶ X} {p' : S' ⟶ X'} {p'' : S'' ⟶ X''}
    {f : S' ⟶ S} {g : X' ⟶ X} {f' : S'' ⟶ S'} {g' : X'' ⟶ X'}
    (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (h₀' : p'' ≫ g' = f' ≫ p') (hI' : I'' = I'.comap g')
    (h₀'' : p'' ≫ g' ≫ g = (f' ≫ f) ≫ p) (hI'' : I'' = I.comap (g' ≫ g)) :
    (Scheme.Modules.pullbackComp f' f).inv.app ((Scheme.Modules.pullback p).obj I.sheaf) ≫
        (Scheme.Modules.pullback f').map (I.pullbackComparison I' h₀ hI) ≫
        I'.pullbackComparison I'' h₀' hI' =
      I.pullbackComparison I'' h₀'' hI'' := by
  set φ := I.pullbackSheafHom g ≫ eqToHom (congrArg sheaf hI.symm) with hφ
  set φ' := I'.pullbackSheafHom g' ≫ eqToHom (congrArg sheaf hI'.symm) with hφ'
  set φ'' := I.pullbackSheafHom (g' ≫ g) ≫ eqToHom (congrArg sheaf hI''.symm) with hφ''
  simp only [pullbackComparison, ← hφ, ← hφ', ← hφ'', Functor.map_comp, Category.assoc]
  rw [Scheme.Modules.pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app_assoc,
    Scheme.Modules.pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app_assoc,
    Scheme.Modules.pullbackComp_inv_app_comp_pullback_map_pullbackComp_inv_app_assoc]
  have h1 : (Scheme.Modules.pullbackComp f' p').inv.app
        ((Scheme.Modules.pullback g).obj I.sheaf) ≫
      (Scheme.Modules.pullback f').map ((Scheme.Modules.pullback p').map φ) ≫
      (Scheme.Modules.pullbackComp f' p').hom.app I'.sheaf =
      (Scheme.Modules.pullback (f' ≫ p')).map φ := by
    rw [← Functor.comp_map, ← (Scheme.Modules.pullbackComp f' p').inv.naturality_assoc,
      Iso.inv_hom_id_app, Category.comp_id]
  have h2 : (Scheme.Modules.pullback (f' ≫ p')).map φ ≫
      (Scheme.Modules.pullbackCongr h₀'.symm).hom.app I'.sheaf ≫
      (Scheme.Modules.pullbackComp p'' g').inv.app I'.sheaf =
      (Scheme.Modules.pullbackCongr h₀'.symm).hom.app
        ((Scheme.Modules.pullback g).obj I.sheaf) ≫
      (Scheme.Modules.pullbackComp p'' g').inv.app
        ((Scheme.Modules.pullback g).obj I.sheaf) ≫
      (Scheme.Modules.pullback p'').map ((Scheme.Modules.pullback g').map φ) := by
    rw [(Scheme.Modules.pullbackCongr h₀'.symm).hom.naturality_assoc]
    congr 1
    simpa only [Functor.comp_map] using (Scheme.Modules.pullbackComp p'' g').inv.naturality φ
  have h3 : (Scheme.Modules.pullback p'').map ((Scheme.Modules.pullback g').map φ) ≫
      (Scheme.Modules.pullback p'').map φ' =
      (Scheme.Modules.pullback p'').map
        ((Scheme.Modules.pullbackComp g' g).hom.app I.sheaf) ≫
      (Scheme.Modules.pullback p'').map φ'' := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (Scheme.Modules.pullback p'').map
      (pullbackSheafHom_eqToHom_comp hI hI' hI'')
  rw [reassoc_of% h1, reassoc_of% h2, h3,
    Scheme.Modules.pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app_assoc,
    Scheme.Modules.pullbackCongr_hom_app_comp_pullbackComp_hom_app_assoc,
    Iso.inv_hom_id_app_assoc]
  simp [Scheme.Modules.pullbackCongr]

private lemma pullbackComp_inv_map_sheafι {a : S' ⟶ S} {b : S ⟶ X} (I : X.IdealSheafData) :
    (Scheme.Modules.pullbackComp a b).inv.app I.sheaf ≫
        (Scheme.Modules.pullback a).map
          ((Scheme.Modules.pullback b).map I.sheafι ≫
            (Scheme.Modules.pullbackObjUnitIso b).hom) ≫
        (Scheme.Modules.pullbackObjUnitIso a).hom =
      (Scheme.Modules.pullback (a ≫ b)).map I.sheafι ≫
        (Scheme.Modules.pullbackObjUnitIso (a ≫ b)).hom :=
  (congrArg (_ ≫ ·) (congrArg (· ≫ _) ((Scheme.Modules.pullback a).map_comp _ _))).trans <|
    (congrArg (_ ≫ ·) (Category.assoc _ _ _)).trans <|
    (Category.assoc _ _ _).symm.trans <|
    (congrArg (· ≫ _) ((Scheme.Modules.pullbackComp a b).inv.naturality I.sheafι).symm).trans <|
    (Category.assoc _ _ _).trans <|
    congrArg (_ ≫ ·) (Scheme.Modules.pullbackObjUnitIso_comp a b)

private lemma pullbackCongr_hom_app_comp_map_sheafι {p₁ p₂ : S' ⟶ X} (hp : p₂ = p₁)
    (I : X.IdealSheafData) :
    (Scheme.Modules.pullbackCongr hp).hom.app I.sheaf ≫
        (Scheme.Modules.pullback p₁).map I.sheafι ≫
        (Scheme.Modules.pullbackObjUnitIso p₁).hom =
      (Scheme.Modules.pullback p₂).map I.sheafι ≫
        (Scheme.Modules.pullbackObjUnitIso p₂).hom := by
  subst hp
  simp [Scheme.Modules.pullbackCongr]

/-- Compatibility of `pullbackComparison` with the pulled-back ideal inclusion `p^* I ⟶ 𝒪_S`. -/
lemma pullbackComparison_comp_map_sheafι (I : X.IdealSheafData) (I' : X'.IdealSheafData)
    {p : S ⟶ X} {p' : S' ⟶ X'} {f : S' ⟶ S} {g : X' ⟶ X}
    (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g) :
    I.pullbackComparison I' h₀ hI ≫
        ((Scheme.Modules.pullback p').map I'.sheafι ≫
          (Scheme.Modules.pullbackObjUnitIso p').hom) =
      (Scheme.Modules.pullback f).map
          ((Scheme.Modules.pullback p).map I.sheafι ≫
            (Scheme.Modules.pullbackObjUnitIso p).hom) ≫
        (Scheme.Modules.pullbackObjUnitIso f).hom := by
  have h1 : (Scheme.Modules.pullback p').map
        (I.pullbackSheafHom g ≫ eqToHom (congrArg sheaf hI.symm)) ≫
      ((Scheme.Modules.pullback p').map I'.sheafι ≫
        (Scheme.Modules.pullbackObjUnitIso p').hom) =
      (Scheme.Modules.pullback p').map
          ((Scheme.Modules.pullback g).map I.sheafι ≫
            (Scheme.Modules.pullbackObjUnitIso g).hom) ≫
        (Scheme.Modules.pullbackObjUnitIso p').hom :=
    (Category.assoc _ _ _).symm.trans <|
      congrArg (· ≫ _) (((Scheme.Modules.pullback p').map_comp _ _).symm.trans
        (congrArg (Scheme.Modules.pullback p').map (pullbackSheafHom_eqToHom_sheafι hI.symm)))
  unfold pullbackComparison
  rw [Category.assoc, Category.assoc, Category.assoc, h1, pullbackComp_inv_map_sheafι,
    pullbackCongr_hom_app_comp_map_sheafι h₀.symm I,
    ← pullbackComp_inv_map_sheafι (a := f) (b := p), Iso.hom_inv_id_app_assoc]

/-- Contravariant pullback of a basis `ω : 𝟙_ S.Modules ≅ p^* I.sheaf` along a commutative square
`p' ≫ g = f ≫ p` of effective Cartier divisors satisfying `I' = I.comap g`. -/
def basisPullback (I : X.IdealSheafData) (I' : X'.IdealSheafData)
    {p : S ⟶ X} {p' : S' ⟶ X'} {f : S' ⟶ S} {g : X' ⟶ X}
    (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier)
    (ω : 𝟙_ S.Modules ≅ (Scheme.Modules.pullback p).obj I.sheaf) :
    𝟙_ S'.Modules ≅ (Scheme.Modules.pullback p').obj I'.sheaf :=
  have := I.isIso_pullbackComparison I' h₀ hI hIC hI'C
  (Scheme.Modules.pullbackObjUnitIso f).symm ≪≫ (Scheme.Modules.pullback f).mapIso ω ≪≫
    asIso (I.pullbackComparison I' h₀ hI)

lemma basisPullback_hom (I : X.IdealSheafData) (I' : X'.IdealSheafData)
    {p : S ⟶ X} {p' : S' ⟶ X'} {f : S' ⟶ S} {g : X' ⟶ X}
    (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier)
    (ω : 𝟙_ S.Modules ≅ (Scheme.Modules.pullback p).obj I.sheaf) :
    (I.basisPullback I' h₀ hI hIC hI'C ω).hom =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map ω.hom ≫
        I.pullbackComparison I' h₀ hI := by
  simp [basisPullback]

lemma basisPullback_congr (I : X.IdealSheafData) (I' : X'.IdealSheafData)
    {p : S ⟶ X} {p' : S' ⟶ X'} {f₁ f₂ : S' ⟶ S} {g₁ g₂ : X' ⟶ X}
    (hf : f₁ = f₂) (hg : g₁ = g₂)
    (h₀₁ : p' ≫ g₁ = f₁ ≫ p) (hI₁ : I' = I.comap g₁)
    (h₀₂ : p' ≫ g₂ = f₂ ≫ p) (hI₂ : I' = I.comap g₂)
    (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier)
    (ω : 𝟙_ S.Modules ≅ (Scheme.Modules.pullback p).obj I.sheaf) :
    I.basisPullback I' h₀₁ hI₁ hIC hI'C ω = I.basisPullback I' h₀₂ hI₂ hIC hI'C ω := by
  cases hf
  cases hg
  rfl

@[simp]
theorem basisPullback_id (I : X.IdealSheafData) {p : S ⟶ X}
    (h₀ : p ≫ 𝟙 X = 𝟙 S ≫ p := by simp) (hI : I = I.comap (𝟙 X) := I.comap_id.symm)
    (hIC : I.IsEffectiveCartier)
    (ω : 𝟙_ S.Modules ≅ (Scheme.Modules.pullback p).obj I.sheaf) :
    I.basisPullback I h₀ hI hIC hIC ω = ω := by
  ext1
  rw [basisPullback_hom, pullbackComparison_id,
    (Scheme.Modules.pullbackId S).hom.naturality, Functor.id_map,
    ← Scheme.Modules.pullbackObjUnitIso_id, Iso.inv_hom_id_assoc]

theorem basisPullback_comp (I : X.IdealSheafData) (I' : X'.IdealSheafData)
    (I'' : X''.IdealSheafData) {p : S ⟶ X} {p' : S' ⟶ X'} {p'' : S'' ⟶ X''}
    {f : S' ⟶ S} {g : X' ⟶ X} {f' : S'' ⟶ S'} {g' : X'' ⟶ X'}
    (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (h₀' : p'' ≫ g' = f' ≫ p') (hI' : I'' = I'.comap g')
    (h₀'' : p'' ≫ g' ≫ g = (f' ≫ f) ≫ p) (hI'' : I'' = I.comap (g' ≫ g))
    (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier)
    (hI''C : I''.IsEffectiveCartier)
    (ω : 𝟙_ S.Modules ≅ (Scheme.Modules.pullback p).obj I.sheaf) :
    I'.basisPullback I'' h₀' hI' hI'C hI''C (I.basisPullback I' h₀ hI hIC hI'C ω) =
      I.basisPullback I'' h₀'' hI'' hIC hI''C ω := by
  ext1
  simp only [basisPullback_hom, Functor.map_comp, Category.assoc]
  have hunit : (Scheme.Modules.pullbackObjUnitIso (f' ≫ f)).inv =
      (Scheme.Modules.pullbackObjUnitIso f').inv ≫
        (Scheme.Modules.pullback f').map (Scheme.Modules.pullbackObjUnitIso f).inv ≫
        (Scheme.Modules.pullbackComp f' f).hom.app (𝟙_ S.Modules) := by
    rw [← cancel_mono (Scheme.Modules.pullbackObjUnitIso (f' ≫ f)).hom, Iso.inv_hom_id,
      ← Scheme.Modules.pullbackObjUnitIso_comp f' f]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  have hnat : (Scheme.Modules.pullbackComp f' f).hom.app (𝟙_ S.Modules) ≫
      (Scheme.Modules.pullback (f' ≫ f)).map ω.hom ≫ I.pullbackComparison I'' h₀'' hI'' =
      (Scheme.Modules.pullback f').map ((Scheme.Modules.pullback f).map ω.hom) ≫
        (Scheme.Modules.pullbackComp f' f).hom.app ((Scheme.Modules.pullback p).obj I.sheaf) ≫
        I.pullbackComparison I'' h₀'' hI'' := by
    simpa only [Functor.comp_map] using
      ((Scheme.Modules.pullbackComp f' f).hom.naturality_assoc ω.hom
        (I.pullbackComparison I'' h₀'' hI'')).symm
  rw [hunit, Category.assoc, Category.assoc, hnat, ← I.pullbackComparison_comp I' I'' h₀ hI h₀' hI',
    Iso.hom_inv_id_app_assoc]

theorem basisPullback_unitSmulIso (I : X.IdealSheafData) (I' : X'.IdealSheafData)
    {p : S ⟶ X} {p' : S' ⟶ X'} {f : S' ⟶ S} {g : X' ⟶ X}
    (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier)
    (u : Γ(S, ⊤)ˣ) (ω : 𝟙_ S.Modules ≅ (Scheme.Modules.pullback p).obj I.sheaf) :
    I.basisPullback I' h₀ hI hIC hI'C (Scheme.Modules.unitSmulIso u ω) =
      Scheme.Modules.unitSmulIso (Units.map f.appTop.hom.toMonoidHom u)
        (I.basisPullback I' h₀ hI hIC hI'C ω) := by
  ext1
  have hu : ((Units.map f.appTop.hom.toMonoidHom u : Γ(S', ⊤)ˣ) : Γ(S', ⊤)) = f.appTop u := rfl
  have hsmul : (Scheme.Modules.pullbackObjUnitIso f).inv ≫
      Scheme.Modules.globalSectionsSmul ((Scheme.Modules.pullback f).obj (𝟙_ S.Modules))
        (f.appTop u) =
      Scheme.Modules.globalSectionsSmul (𝟙_ S'.Modules) (f.appTop u) ≫
        (Scheme.Modules.pullbackObjUnitIso f).inv :=
    (Scheme.Modules.globalSectionsSmul_naturality (Scheme.Modules.pullbackObjUnitIso f).inv _).symm
  simp only [basisPullback_hom, Scheme.Modules.unitSmulIso_hom, Functor.map_comp,
    Scheme.Modules.pullback_map_globalSectionsSmul, hu, Category.assoc, reassoc_of% hsmul]

end PullbackComparison

end Scheme.IdealSheafData

namespace Scheme.Hom

variable {X S X' S' X'' S'' : Scheme.{u}}

/-- The **conormal sheaf** of a morphism `s : S ⟶ X`: the pullback `s^* s.ker.sheaf` on `S` of its
kernel ideal sheaf. -/
abbrev conormalSheaf (s : S ⟶ X) : S.Modules :=
  (Scheme.Modules.pullback s).obj s.ker.sheaf

/-- The conormal sheaf of a section of a separated morphism that is smooth of relative dimension one
is invertible. -/
theorem isInvertible_conormalSheaf {π : X ⟶ S} (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    [IsSeparated π] [SmoothOfRelativeDimension 1 π] :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible S s.conormalSheaf := by
  have :=
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs).isEffectiveCartier
  have := this.isInvertible_sheaf
  exact TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_pullback s s.ker.sheaf

/-- For a cartesian square `IsPullback g π' π f` with `[IsSeparated π]` carrying a section `s'` of
`π'` to a section `s` of `π`, the ideal sheaf of `s'` is the inverse image of `s.ker` along `g`. -/
theorem ker_eq_comap_of_isPullback_section {π : X ⟶ S} {π' : X' ⟶ S'} {s : S ⟶ X} {s' : S' ⟶ X'}
    {f : S' ⟶ S} {g : X' ⟶ X} [IsSeparated π] (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S')
    (hg : IsPullback g π' π f) (h₀ : s' ≫ g = f ≫ s) : s'.ker = s.ker.comap g := by
  have := Scheme.Hom.isClosedImmersion_of_comp_eq_id s hs
  have hsq : IsPullback s' f g s :=
    IsPullback.of_right (by rw [hs', hs]; exact .of_horiz_isIso ⟨by simp⟩) h₀ hg.flip
  exact IdealSheafData.ker_eq_comap_of_isPullback s hsq

/-- The comparison morphism `f^* s.conormalSheaf ⟶ s'.conormalSheaf` induced by a commutative square
`s' ≫ g = f ≫ s` satisfying `s'.ker = s.ker.comap g`. -/
def conormalPullbackHom {s : S ⟶ X} {s' : S' ⟶ X'} {f : S' ⟶ S} {g : X' ⟶ X}
    (h₀ : s' ≫ g = f ≫ s) (hker : s'.ker = s.ker.comap g) :
    (Scheme.Modules.pullback f).obj s.conormalSheaf ⟶ s'.conormalSheaf :=
  s.ker.pullbackComparison s'.ker h₀ hker

/-- When `s.ker` and `s'.ker` are effective Cartier divisors and `s'.ker = s.ker.comap g`, the
conormal comparison `conormalPullbackHom` is an isomorphism. -/
theorem isIso_conormalPullbackHom {s : S ⟶ X} {s' : S' ⟶ X'} {f : S' ⟶ S} {g : X' ⟶ X}
    (h₀ : s' ≫ g = f ≫ s) (hker : s'.ker = s.ker.comap g)
    (hs : s.ker.IsEffectiveCartier) (hs' : s'.ker.IsEffectiveCartier) :
    IsIso (conormalPullbackHom h₀ hker) :=
  s.ker.isIso_pullbackComparison s'.ker h₀ hker hs hs'

/-- Along the identity square, `conormalPullbackHom` is the identity comparison of pullback. -/
lemma conormalPullbackHom_id (s : S ⟶ X) (h₀ : s ≫ 𝟙 X = 𝟙 S ≫ s := by simp)
    (hker : s.ker = s.ker.comap (𝟙 X) := s.ker.comap_id.symm) :
    conormalPullbackHom h₀ hker = (Scheme.Modules.pullbackId S).hom.app s.conormalSheaf :=
  s.ker.pullbackComparison_id s h₀ hker

/-- Along two stacked squares, `conormalPullbackHom` composes through `pullbackComp`. -/
lemma conormalPullbackHom_comp {s : S ⟶ X} {s' : S' ⟶ X'} {s'' : S'' ⟶ X''}
    {f : S' ⟶ S} {g : X' ⟶ X} {f' : S'' ⟶ S'} {g' : X'' ⟶ X'}
    (h₀ : s' ≫ g = f ≫ s) (hker : s'.ker = s.ker.comap g)
    (h₀' : s'' ≫ g' = f' ≫ s') (hker' : s''.ker = s'.ker.comap g')
    (h₀'' : s'' ≫ g' ≫ g = (f' ≫ f) ≫ s)
    (hker'' : s''.ker = s.ker.comap (g' ≫ g)) :
    (Scheme.Modules.pullbackComp f' f).inv.app s.conormalSheaf ≫
        (Scheme.Modules.pullback f').map (conormalPullbackHom h₀ hker) ≫
        conormalPullbackHom h₀' hker' =
      conormalPullbackHom h₀'' hker'' :=
  s.ker.pullbackComparison_comp s'.ker s''.ker h₀ hker h₀' hker' h₀'' hker''

/-- Contravariant pullback of a conormal basis `ω : 𝟙_ S.Modules ≅ s.conormalSheaf` along a
cartesian square `IsPullback g π' π f` carrying `s'` to `s`. -/
def conormalBasisPullback {π : X ⟶ S} {π' : X' ⟶ S'} {s : S ⟶ X} {s' : S' ⟶ X'}
    {f : S' ⟶ S} {g : X' ⟶ X}
    [IsSeparated π] [SmoothOfRelativeDimension 1 π]
    [IsSeparated π'] [SmoothOfRelativeDimension 1 π']
    (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S')
    (hg : IsPullback g π' π f) (h₀ : s' ≫ g = f ≫ s)
    (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) : 𝟙_ S'.Modules ≅ s'.conormalSheaf :=
  have heff :=
    Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs
  have heff' :=
    Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s' hs'
  s.ker.basisPullback s'.ker h₀ (ker_eq_comap_of_isPullback_section hs hs' hg h₀)
    heff.isEffectiveCartier heff'.isEffectiveCartier ω

lemma conormalBasisPullback_eq_basisPullback {π : X ⟶ S} {π' : X' ⟶ S'} {s : S ⟶ X} {s' : S' ⟶ X'}
    {f : S' ⟶ S} {g : X' ⟶ X}
    [IsSeparated π] [SmoothOfRelativeDimension 1 π]
    [IsSeparated π'] [SmoothOfRelativeDimension 1 π']
    (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S')
    (hg : IsPullback g π' π f) (h₀ : s' ≫ g = f ≫ s)
    (hIC : s.ker.IsEffectiveCartier) (hI'C : s'.ker.IsEffectiveCartier)
    (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullback hs hs' hg h₀ ω =
      s.ker.basisPullback s'.ker h₀ (ker_eq_comap_of_isPullback_section hs hs' hg h₀)
        hIC hI'C ω := by
  rfl

lemma conormalBasisPullback_congr {π : X ⟶ S} {π' : X' ⟶ S'} {s : S ⟶ X} {s' : S' ⟶ X'}
    {f₁ f₂ : S' ⟶ S} {g₁ g₂ : X' ⟶ X}
    [IsSeparated π] [SmoothOfRelativeDimension 1 π]
    [IsSeparated π'] [SmoothOfRelativeDimension 1 π']
    (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S')
    (hf : f₁ = f₂) (hg : g₁ = g₂)
    (hsq₁ : IsPullback g₁ π' π f₁) (h₀₁ : s' ≫ g₁ = f₁ ≫ s)
    (hsq₂ : IsPullback g₂ π' π f₂) (h₀₂ : s' ≫ g₂ = f₂ ≫ s)
    (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullback hs hs' hsq₁ h₀₁ ω = conormalBasisPullback hs hs' hsq₂ h₀₂ ω := by
  cases hf
  cases hg
  rfl

lemma conormalBasisPullback_hom {π : X ⟶ S} {π' : X' ⟶ S'} {s : S ⟶ X} {s' : S' ⟶ X'}
    {f : S' ⟶ S} {g : X' ⟶ X}
    [IsSeparated π] [SmoothOfRelativeDimension 1 π]
    [IsSeparated π'] [SmoothOfRelativeDimension 1 π']
    (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S')
    (hg : IsPullback g π' π f) (h₀ : s' ≫ g = f ≫ s) (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    (conormalBasisPullback hs hs' hg h₀ ω).hom =
      (Scheme.Modules.pullbackObjUnitIso f).inv ≫ (Scheme.Modules.pullback f).map ω.hom ≫
        conormalPullbackHom h₀ (ker_eq_comap_of_isPullback_section hs hs' hg h₀) :=
  s.ker.basisPullback_hom s'.ker h₀ (ker_eq_comap_of_isPullback_section hs hs' hg h₀)
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs).isEffectiveCartier
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s'
      hs').isEffectiveCartier ω

/-- Pulling back a conormal basis along the identity square recovers it. -/
@[simp]
theorem conormalBasisPullback_id {π : X ⟶ S} {s : S ⟶ X}
    [IsSeparated π] [SmoothOfRelativeDimension 1 π] (hs : s ≫ π = 𝟙 S)
    (hg : IsPullback (𝟙 X) π π (𝟙 S) := .of_horiz_isIso ⟨by simp⟩)
    (h₀ : s ≫ 𝟙 X = 𝟙 S ≫ s := by simp)
    (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullback hs hs hg h₀ ω = ω :=
  s.ker.basisPullback_id h₀ (ker_eq_comap_of_isPullback_section hs hs hg h₀)
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs).isEffectiveCartier
    ω

/-- Pulling back a conormal basis along two stacked cartesian squares agrees with pulling back
along the composite square. -/
theorem conormalBasisPullback_comp {π : X ⟶ S} {π' : X' ⟶ S'} {π'' : X'' ⟶ S''}
    {s : S ⟶ X} {s' : S' ⟶ X'} {s'' : S'' ⟶ X''}
    {f : S' ⟶ S} {g : X' ⟶ X} {f' : S'' ⟶ S'} {g' : X'' ⟶ X'}
    [IsSeparated π] [SmoothOfRelativeDimension 1 π]
    [IsSeparated π'] [SmoothOfRelativeDimension 1 π']
    [IsSeparated π''] [SmoothOfRelativeDimension 1 π'']
    (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S') (hs'' : s'' ≫ π'' = 𝟙 S'')
    (hg : IsPullback g π' π f) (h₀ : s' ≫ g = f ≫ s)
    (hg' : IsPullback g' π'' π' f') (h₀' : s'' ≫ g' = f' ≫ s')
    (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullback hs' hs'' hg' h₀' (conormalBasisPullback hs hs' hg h₀ ω) =
      conormalBasisPullback hs hs'' (hg'.paste_horiz hg)
        (by rw [reassoc_of% h₀', h₀, Category.assoc]) ω :=
  s.ker.basisPullback_comp s'.ker s''.ker h₀
    (ker_eq_comap_of_isPullback_section hs hs' hg h₀) h₀'
    (ker_eq_comap_of_isPullback_section hs' hs'' hg' h₀')
    (by rw [reassoc_of% h₀', h₀, Category.assoc])
    (ker_eq_comap_of_isPullback_section hs hs'' (hg'.paste_horiz hg)
      (by rw [reassoc_of% h₀', h₀, Category.assoc]))
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs).isEffectiveCartier
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s'
      hs').isEffectiveCartier
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s''
      hs'').isEffectiveCartier ω

/-- Pulling back a unit-rescaled conormal basis rescales the pulled-back basis by the pulled-back
unit. -/
theorem conormalBasisPullback_unitSmulIso {π : X ⟶ S} {π' : X' ⟶ S'} {s : S ⟶ X} {s' : S' ⟶ X'}
    {f : S' ⟶ S} {g : X' ⟶ X}
    [IsSeparated π] [SmoothOfRelativeDimension 1 π]
    [IsSeparated π'] [SmoothOfRelativeDimension 1 π']
    (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S')
    (hg : IsPullback g π' π f) (h₀ : s' ≫ g = f ≫ s)
    (u : Γ(S, ⊤)ˣ) (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullback hs hs' hg h₀ (Scheme.Modules.unitSmulIso u ω) =
      Scheme.Modules.unitSmulIso (Units.map f.appTop.hom.toMonoidHom u)
        (conormalBasisPullback hs hs' hg h₀ ω) :=
  s.ker.basisPullback_unitSmulIso s'.ker h₀ (ker_eq_comap_of_isPullback_section hs hs' hg h₀)
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs).isEffectiveCartier
    (Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s'
      hs').isEffectiveCartier u ω

end Scheme.Hom

end

end AlgebraicGeometry
