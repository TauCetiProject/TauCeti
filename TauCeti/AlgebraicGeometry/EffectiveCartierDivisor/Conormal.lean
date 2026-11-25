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

For `s : S ⟶ X`, `s.conormalSheaf` is `s^* s.ker.sheaf` on `S`, invertible when `s` is a section of
a separated morphism `π : X ⟶ S` smooth of relative dimension `1` (`isInvertible_conormalSheaf`;
for an elliptic curve, this is `ω_{E/S}`, Katz–Mazur 2.1.6). Along `s' ≫ g = f ≫ s` with
`s'.ker = s.ker.comap g`, `conormalPullbackHom : f^* s.conormalSheaf ⟶ s'.conormalSheaf` is an
isomorphism for effective Cartier divisors (`isIso_conormalPullbackHom`), inducing contravariant
pullbacks of bases along pointed cartesian squares (`conormalBasisPullback`) and pointed
isomorphisms over `S` (`conormalBasisPullbackOfIso`).

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Princeton Univ. Press, 1985,
  2.1.6.
* The Stacks Project, Tag 063M.
-/

public section

open CategoryTheory Limits MonoidalCategory

universe u

namespace AlgebraicGeometry

noncomputable section

namespace Scheme.IdealSheafData

variable {X S X' S' X'' S'' : Scheme.{u}} (I : X.IdealSheafData) (I' : X'.IdealSheafData)
  (I'' : X''.IdealSheafData) {p : S ⟶ X} {p' : S' ⟶ X'} {p'' : S'' ⟶ X''}
  {f : S' ⟶ S} {g : X' ⟶ X} {f' : S'' ⟶ S'} {g' : X'' ⟶ X'}

/-- Comparison `f^* (p^* I) ⟶ p'^* I'` along `p' ≫ g = f ≫ p` with `I' = I.comap g`. -/
def pullbackComparison (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g) :
    (Modules.pullback f).obj ((Modules.pullback p).obj I.sheaf) ⟶
      (Modules.pullback p').obj I'.sheaf :=
  (Modules.pullbackComp f p).hom.app I.sheaf ≫ (Modules.pullbackCongr h₀.symm).hom.app I.sheaf ≫
    (Modules.pullbackComp p' g).inv.app I.sheaf ≫
    (Modules.pullback p').map (I.pullbackSheafHom g ≫ eqToHom (congrArg sheaf hI.symm))

/-- `pullbackComparison` is an isomorphism for effective Cartier divisors. -/
theorem isIso_pullbackComparison (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier) :
    IsIso (I.pullbackComparison I' h₀ hI) := by
  have := I.isIso_pullbackSheafHom g hIC (hI ▸ hI'C)
  dsimp only [pullbackComparison]; infer_instance

/-- Along the identity square, `pullbackComparison` is `(Modules.pullbackId S).hom.app`. -/
lemma pullbackComparison_id (p : S ⟶ X) (h₀ : p ≫ 𝟙 X = 𝟙 S ≫ p := by simp)
    (hI : I = I.comap (𝟙 X) := I.comap_id.symm) :
    I.pullbackComparison I h₀ hI =
      (Modules.pullbackId S).hom.app ((Modules.pullback p).obj I.sheaf) := by
  refine (cancel_epi ((Modules.pullbackComp (𝟙 S) p).inv.app I.sheaf)).mp ?_
  have hid : I.pullbackSheafHom (𝟙 X) ≫ eqToHom (congrArg sheaf hI.symm) =
      (Modules.pullbackId X).hom.app I.sheaf := I.pullbackSheafHom_id
  simp only [pullbackComparison, hid, Iso.inv_hom_id_app_assoc,
    Modules.pseudofunctor_left_unitality_app, Modules.pseudofunctor_right_unitality_app]
  simp [Modules.pullbackCongr]

/-- Along two stacked squares, `pullbackComparison` composes through `pullbackComp`. -/
lemma pullbackComparison_comp (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (h₀' : p'' ≫ g' = f' ≫ p') (hI' : I'' = I'.comap g')
    (h₀'' : p'' ≫ g' ≫ g = (f' ≫ f) ≫ p) (hI'' : I'' = I.comap (g' ≫ g)) :
    (Modules.pullbackComp f' f).inv.app ((Modules.pullback p).obj I.sheaf) ≫
        (Modules.pullback f').map (I.pullbackComparison I' h₀ hI) ≫
        I'.pullbackComparison I'' h₀' hI' = I.pullbackComparison I'' h₀'' hI'' := by
  subst hI hI'
  set φ := I.pullbackSheafHom g; set φ' := (I.comap g).pullbackSheafHom g'
  set φ'' := I.pullbackSheafHom (g' ≫ g) ≫ eqToHom (congrArg sheaf hI''.symm)
  simp only [pullbackComparison, eqToHom_refl, Category.comp_id, Functor.map_comp, Category.assoc]
  rw [Modules.pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app_assoc,
    Modules.pullbackComp_inv_app_comp_pullback_map_pullbackCongr_hom_app_assoc,
    Modules.pullbackComp_inv_app_comp_pullback_map_pullbackComp_inv_app_assoc]
  have h1 : (Modules.pullbackComp f' p').inv.app _ ≫
      (Modules.pullback f').map ((Modules.pullback p').map φ) ≫
      (Modules.pullbackComp f' p').hom.app _ = (Modules.pullback (f' ≫ p')).map φ := by
    rw [← Functor.comp_map, ← (Modules.pullbackComp f' p').inv.naturality_assoc,
      Iso.inv_hom_id_app, Category.comp_id]
  have h2 : (Modules.pullback (f' ≫ p')).map φ ≫ (Modules.pullbackCongr h₀'.symm).hom.app _ ≫
      (Modules.pullbackComp p'' g').inv.app _ =
      (Modules.pullbackCongr h₀'.symm).hom.app _ ≫ (Modules.pullbackComp p'' g').inv.app _ ≫
      (Modules.pullback p'').map ((Modules.pullback g').map φ) := by
    rw [(Modules.pullbackCongr h₀'.symm).hom.naturality_assoc]; congr 1
    simpa only [Functor.comp_map] using (Modules.pullbackComp p'' g').inv.naturality φ
  have h3 : (Modules.pullback p'').map ((Modules.pullback g').map φ) ≫
      (Modules.pullback p'').map φ' =
      (Modules.pullback p'').map ((Modules.pullbackComp g' g).hom.app I.sheaf) ≫
      (Modules.pullback p'').map φ'' := by
    rw [← Functor.map_comp, ← Functor.map_comp]; congr 1
    exact (cancel_epi ((Modules.pullbackComp g' g).inv.app I.sheaf)).mp
      ((I.pullbackSheafHom_comp g' g).trans (Iso.inv_hom_id_app_assoc _ _ _).symm)
  rw [reassoc_of% h1, reassoc_of% h2, h3,
    Modules.pullbackComp_inv_app_comp_pullback_map_pullbackComp_hom_app_assoc,
    Modules.pullbackCongr_hom_app_comp_pullbackComp_hom_app_assoc, Iso.inv_hom_id_app_assoc]
  simp [Modules.pullbackCongr, φ'']

private lemma pullbackCongr_hom_app_comp_map_sheafι {p₁ p₂ : S' ⟶ X} (hp : p₂ = p₁) :
    (Modules.pullbackCongr hp).hom.app I.sheaf ≫ (Modules.pullback p₁).map I.sheafι ≫
      (Modules.pullbackObjUnitIso p₁).hom =
      (Modules.pullback p₂).map I.sheafι ≫ (Modules.pullbackObjUnitIso p₂).hom := by
  subst hp; simp [Modules.pullbackCongr]

/-- Compatibility of `pullbackComparison` with the pulled-back ideal inclusion `p^* I ⟶ 𝒪_S`. -/
lemma pullbackComparison_comp_map_sheafι (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g) :
    I.pullbackComparison I' h₀ hI ≫
        ((Modules.pullback p').map I'.sheafι ≫ (Modules.pullbackObjUnitIso p').hom) =
      (Modules.pullback f).map
        ((Modules.pullback p).map I.sheafι ≫ (Modules.pullbackObjUnitIso p).hom) ≫
        (Modules.pullbackObjUnitIso f).hom := by
  subst hI
  let ι : I.sheaf ⟶ 𝟙_ X.Modules := I.sheafι
  let ι' : (I.comap g).sheaf ⟶ 𝟙_ X'.Modules := (I.comap g).sheafι
  have hι : I.pullbackSheafHom g ≫ ι' =
      (Modules.pullback g).map ι ≫ (Modules.pullbackObjUnitIso g).hom := I.pullbackSheafHom_sheafι g
  change I.pullbackComparison (I.comap g) h₀ rfl ≫
      ((Modules.pullback p').map ι' ≫ (Modules.pullbackObjUnitIso p').hom) =
    (Modules.pullback f).map ((Modules.pullback p).map ι ≫ (Modules.pullbackObjUnitIso p).hom) ≫
      (Modules.pullbackObjUnitIso f).hom
  unfold pullbackComparison
  rw [eqToHom_refl, Category.comp_id, Category.assoc, Category.assoc, Category.assoc,
    ← Functor.map_comp_assoc, hι, I.pullbackComp_inv_map_sheafι p' g,
    I.pullbackCongr_hom_app_comp_map_sheafι h₀.symm, ← I.pullbackComp_inv_map_sheafι f p,
    Iso.hom_inv_id_app_assoc]

/-- Contravariant pullback of a basis `ω : 𝟙_ S.Modules ≅ p^* I.sheaf` along `p' ≫ g = f ≫ p`. -/
def basisPullback (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier)
    (ω : 𝟙_ S.Modules ≅ (Modules.pullback p).obj I.sheaf) :
    𝟙_ S'.Modules ≅ (Modules.pullback p').obj I'.sheaf :=
  have := I.isIso_pullbackComparison I' h₀ hI hIC hI'C
  (Modules.pullbackObjUnitIso f).symm ≪≫ (Modules.pullback f).mapIso ω ≪≫
    asIso (I.pullbackComparison I' h₀ hI)

/-- Forward morphism of `basisPullback`. -/
lemma basisPullback_hom (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier)
    (ω : 𝟙_ S.Modules ≅ (Modules.pullback p).obj I.sheaf) :
    (I.basisPullback I' h₀ hI hIC hI'C ω).hom =
      (Modules.pullbackObjUnitIso f).inv ≫ (Modules.pullback f).map ω.hom ≫
        I.pullbackComparison I' h₀ hI := by simp [basisPullback]

/-- `basisPullback` depends on the square only through `(f, g)`. -/
lemma basisPullback_congr {f₁ f₂ : S' ⟶ S} {g₁ g₂ : X' ⟶ X} (hf : f₁ = f₂) (hg : g₁ = g₂)
    (h₀₁ : p' ≫ g₁ = f₁ ≫ p) (hI₁ : I' = I.comap g₁) (h₀₂ : p' ≫ g₂ = f₂ ≫ p)
    (hI₂ : I' = I.comap g₂) (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier)
    (ω : 𝟙_ S.Modules ≅ (Modules.pullback p).obj I.sheaf) :
    I.basisPullback I' h₀₁ hI₁ hIC hI'C ω = I.basisPullback I' h₀₂ hI₂ hIC hI'C ω := by
  cases hf; cases hg; rfl

/-- Pulling back a basis along the identity square recovers it. -/
@[simp]
theorem basisPullback_id (h₀ : p ≫ 𝟙 X = 𝟙 S ≫ p := by simp)
    (hI : I = I.comap (𝟙 X) := I.comap_id.symm) (hIC : I.IsEffectiveCartier)
    (ω : 𝟙_ S.Modules ≅ (Modules.pullback p).obj I.sheaf) :
    I.basisPullback I h₀ hI hIC hIC ω = ω := by
  ext1
  rw [basisPullback_hom, pullbackComparison_id, (Modules.pullbackId S).hom.naturality,
    Functor.id_map, ← Modules.pullbackObjUnitIso_id, Iso.inv_hom_id_assoc]

/-- Contravariant functoriality of `basisPullback` along stacked squares. -/
theorem basisPullback_comp (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (h₀' : p'' ≫ g' = f' ≫ p') (hI' : I'' = I'.comap g')
    (h₀'' : p'' ≫ g' ≫ g = (f' ≫ f) ≫ p) (hI'' : I'' = I.comap (g' ≫ g))
    (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier) (hI''C : I''.IsEffectiveCartier)
    (ω : 𝟙_ S.Modules ≅ (Modules.pullback p).obj I.sheaf) :
    I'.basisPullback I'' h₀' hI' hI'C hI''C (I.basisPullback I' h₀ hI hIC hI'C ω) =
      I.basisPullback I'' h₀'' hI'' hIC hI''C ω := by
  ext1; simp only [basisPullback_hom, Functor.map_comp, Category.assoc]
  have hnat : (Modules.pullbackComp f' f).hom.app _ ≫ (Modules.pullback (f' ≫ f)).map ω.hom ≫
      I.pullbackComparison I'' h₀'' hI'' =
      (Modules.pullback f').map ((Modules.pullback f).map ω.hom) ≫
        (Modules.pullbackComp f' f).hom.app _ ≫ I.pullbackComparison I'' h₀'' hI'' := by
    simpa only [Functor.comp_map] using ((Modules.pullbackComp f' f).hom.naturality_assoc ω.hom
      (I.pullbackComparison I'' h₀'' hI'')).symm
  rw [← Modules.pullbackObjUnitIso_inv_comp_assoc f' f, hnat,
    ← I.pullbackComparison_comp I' I'' h₀ hI h₀' hI', Iso.hom_inv_id_app_assoc]

/-- Compatibility of `basisPullback` with `Modules.unitSmulIso`. -/
theorem basisPullback_unitSmulIso (h₀ : p' ≫ g = f ≫ p) (hI : I' = I.comap g)
    (hIC : I.IsEffectiveCartier) (hI'C : I'.IsEffectiveCartier)
    (u : Γ(S, ⊤)ˣ) (ω : 𝟙_ S.Modules ≅ (Modules.pullback p).obj I.sheaf) :
    I.basisPullback I' h₀ hI hIC hI'C (Modules.unitSmulIso u ω) =
      Modules.unitSmulIso (Units.map f.appTop.hom.toMonoidHom u)
        (I.basisPullback I' h₀ hI hIC hI'C ω) := by
  ext1
  have hu : ((Units.map f.appTop.hom.toMonoidHom u : Γ(S', ⊤)ˣ) : Γ(S', ⊤)) = f.appTop u := by
    simp [Units.coe_map]
  have hsmul :=
    (Modules.globalSectionsSmul_naturality (Modules.pullbackObjUnitIso f).inv (f.appTop u)).symm
  simp only [basisPullback_hom, Modules.unitSmulIso_hom, Functor.map_comp,
    Modules.pullback_map_globalSectionsSmul, hu, Category.assoc, reassoc_of% hsmul]

end Scheme.IdealSheafData

namespace Scheme.Hom

variable {X S X' S' X'' S'' : Scheme.{u}}

/-- The **conormal sheaf** `s^* s.ker.sheaf` on `S` of a morphism `s : S ⟶ X`. -/
abbrev conormalSheaf (s : S ⟶ X) : S.Modules := (Modules.pullback s).obj s.ker.sheaf

/-- The conormal sheaf of a section of a separated smooth relative curve is invertible. -/
theorem isInvertible_conormalSheaf {π : X ⟶ S} (s : S ⟶ X) (hs : s ≫ π = 𝟙 S)
    [IsSeparated π] [SmoothOfRelativeDimension 1 π] :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible S s.conormalSheaf := by
  have := (isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension s hs).isEffectiveCartier
  have := this.isInvertible_sheaf
  exact TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible_pullback s s.ker.sheaf

/-- For a cartesian square `IsPullback g π' π f` carrying a section `s'` to `s`,
`s'.ker = s.ker.comap g`. -/
theorem ker_eq_comap_of_isPullback_section {π : X ⟶ S} {π' : X' ⟶ S'} {s : S ⟶ X} {s' : S' ⟶ X'}
    {f : S' ⟶ S} {g : X' ⟶ X} [IsSeparated π] (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S')
    (hg : IsPullback g π' π f) (h₀ : s' ≫ g = f ≫ s) : s'.ker = s.ker.comap g := by
  have := isClosedImmersion_of_comp_eq_id s hs
  exact IdealSheafData.ker_eq_comap_of_isPullback s
    (IsPullback.of_right (by rw [hs', hs]; exact .of_horiz_isIso ⟨by simp⟩) h₀ hg.flip)

/-- Comparison `f^* s.conormalSheaf ⟶ s'.conormalSheaf` along `s' ≫ g = f ≫ s`. -/
def conormalPullbackHom {s : S ⟶ X} {s' : S' ⟶ X'} {f : S' ⟶ S} {g : X' ⟶ X}
    (h₀ : s' ≫ g = f ≫ s) (hker : s'.ker = s.ker.comap g) :
    (Modules.pullback f).obj s.conormalSheaf ⟶ s'.conormalSheaf :=
  s.ker.pullbackComparison s'.ker h₀ hker

/-- `conormalPullbackHom` is an isomorphism when `s.ker` and `s'.ker` are effective Cartier. -/
theorem isIso_conormalPullbackHom {s : S ⟶ X} {s' : S' ⟶ X'} {f : S' ⟶ S} {g : X' ⟶ X}
    (h₀ : s' ≫ g = f ≫ s) (hker : s'.ker = s.ker.comap g)
    (hs : s.ker.IsEffectiveCartier) (hs' : s'.ker.IsEffectiveCartier) :
    IsIso (conormalPullbackHom h₀ hker) :=
  s.ker.isIso_pullbackComparison s'.ker h₀ hker hs hs'

section BasisPullback

variable {π : X ⟶ S} {π' : X' ⟶ S'} {π'' : X'' ⟶ S''} {s : S ⟶ X} {s' : S' ⟶ X'} {s'' : S'' ⟶ X''}
  [IsSeparated π] [SmoothOfRelativeDimension 1 π] [IsSeparated π'] [SmoothOfRelativeDimension 1 π']
  [IsSeparated π''] [SmoothOfRelativeDimension 1 π'']

private lemma ker_cartier {Y T : Scheme.{u}} {q : Y ⟶ T} {t : T ⟶ Y}
    [IsSeparated q] [SmoothOfRelativeDimension 1 q] (ht : t ≫ q = 𝟙 T) :
    t.ker.IsEffectiveCartier :=
  (isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension t ht).isEffectiveCartier

section FixedSquare

variable {f : S' ⟶ S} {g : X' ⟶ X} (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S')
  (hg : IsPullback g π' π f) (h₀ : s' ≫ g = f ≫ s)

/-- Contravariant pullback of `ω : 𝟙_ S.Modules ≅ s.conormalSheaf` along a pointed cartesian
square. -/
def conormalBasisPullback (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) : 𝟙_ S'.Modules ≅ s'.conormalSheaf :=
  s.ker.basisPullback s'.ker h₀ (ker_eq_comap_of_isPullback_section hs hs' hg h₀)
    (ker_cartier hs) (ker_cartier hs') ω

/-- `conormalBasisPullback` as an instance of `IdealSheafData.basisPullback`. -/
lemma conormalBasisPullback_eq_basisPullback (hIC : s.ker.IsEffectiveCartier)
    (hI'C : s'.ker.IsEffectiveCartier) (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullback hs hs' hg h₀ ω =
      s.ker.basisPullback s'.ker h₀ (ker_eq_comap_of_isPullback_section hs hs' hg h₀) hIC hI'C ω :=
  by rfl

/-- Compatibility of `conormalBasisPullback` with `Modules.unitSmulIso`. -/
theorem conormalBasisPullback_unitSmulIso (u : Γ(S, ⊤)ˣ) (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullback hs hs' hg h₀ (Modules.unitSmulIso u ω) =
      Modules.unitSmulIso (Units.map f.appTop.hom.toMonoidHom u)
        (conormalBasisPullback hs hs' hg h₀ ω) :=
  s.ker.basisPullback_unitSmulIso s'.ker h₀ (ker_eq_comap_of_isPullback_section hs hs' hg h₀)
    (ker_cartier hs) (ker_cartier hs') u ω

end FixedSquare

/-- `conormalBasisPullback` depends on the square only through `(f, g)`. -/
lemma conormalBasisPullback_congr {f₁ f₂ : S' ⟶ S} {g₁ g₂ : X' ⟶ X}
    (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S') (hf : f₁ = f₂) (hg : g₁ = g₂)
    (hsq₁ : IsPullback g₁ π' π f₁) (h₀₁ : s' ≫ g₁ = f₁ ≫ s)
    (hsq₂ : IsPullback g₂ π' π f₂) (h₀₂ : s' ≫ g₂ = f₂ ≫ s)
    (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullback hs hs' hsq₁ h₀₁ ω = conormalBasisPullback hs hs' hsq₂ h₀₂ ω := by
  cases hf; cases hg; rfl

/-- Pulling back a conormal basis along the identity square recovers it. -/
@[simp]
theorem conormalBasisPullback_id (hs : s ≫ π = 𝟙 S)
    (hg : IsPullback (𝟙 X) π π (𝟙 S) := .of_horiz_isIso ⟨by simp⟩)
    (h₀ : s ≫ 𝟙 X = 𝟙 S ≫ s := by simp) (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullback hs hs hg h₀ ω = ω :=
  s.ker.basisPullback_id h₀ (ker_eq_comap_of_isPullback_section hs hs hg h₀) (ker_cartier hs) ω

/-- Contravariant functoriality of `conormalBasisPullback` along stacked squares. -/
theorem conormalBasisPullback_comp {f : S' ⟶ S} {g : X' ⟶ X} {f' : S'' ⟶ S'} {g' : X'' ⟶ X'}
    (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S') (hs'' : s'' ≫ π'' = 𝟙 S'')
    (hg : IsPullback g π' π f) (h₀ : s' ≫ g = f ≫ s)
    (hg' : IsPullback g' π'' π' f') (h₀' : s'' ≫ g' = f' ≫ s')
    (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullback hs' hs'' hg' h₀' (conormalBasisPullback hs hs' hg h₀ ω) =
      conormalBasisPullback hs hs'' (hg'.paste_horiz hg)
        (by rw [reassoc_of% h₀', h₀, Category.assoc]) ω :=
  s.ker.basisPullback_comp s'.ker s''.ker h₀ (ker_eq_comap_of_isPullback_section hs hs' hg h₀)
    h₀' (ker_eq_comap_of_isPullback_section hs' hs'' hg' h₀')
    (by rw [reassoc_of% h₀', h₀, Category.assoc])
    (ker_eq_comap_of_isPullback_section hs hs'' (hg'.paste_horiz hg)
      (by rw [reassoc_of% h₀', h₀, Category.assoc]))
    (ker_cartier hs) (ker_cartier hs') (ker_cartier hs'') ω

end BasisPullback

section IsoPullback

variable {π : X ⟶ S} {π' : X' ⟶ S} {π'' : X'' ⟶ S} {s : S ⟶ X} {s' : S ⟶ X'} {s'' : S ⟶ X''}
  [IsSeparated π] [SmoothOfRelativeDimension 1 π] [IsSeparated π'] [SmoothOfRelativeDimension 1 π']
  [IsSeparated π''] [SmoothOfRelativeDimension 1 π'']

section FixedIso

variable (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S) (e : X' ≅ X) (he : e.hom ≫ π = π')
  (he₀ : s' ≫ e.hom = s)

/-- Contravariant pullback of `ω` along a pointed isomorphism `e : X' ≅ X` over `S`. -/
def conormalBasisPullbackOfIso (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    𝟙_ S.Modules ≅ s'.conormalSheaf :=
  conormalBasisPullback hs hs' (f := 𝟙 S) (g := e.hom)
    (.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩) (by rw [he₀, Category.id_comp]) ω

/-- `conormalBasisPullbackOfIso` is `conormalBasisPullback` over `𝟙 S`. -/
theorem conormalBasisPullbackOfIso_def (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullbackOfIso hs hs' e he he₀ ω =
      conormalBasisPullback hs hs' (f := 𝟙 S) (g := e.hom)
        (.of_horiz_isIso ⟨by rw [he, Category.comp_id]⟩) (by rw [he₀, Category.id_comp]) ω := by rfl

/-- `conormalBasisPullbackOfIso` commutes with `unitSmulIso`. -/
theorem conormalBasisPullbackOfIso_unitSmulIso (u : Γ(S, ⊤)ˣ)
    (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullbackOfIso hs hs' e he he₀ (Modules.unitSmulIso u ω) =
      Modules.unitSmulIso u (conormalBasisPullbackOfIso hs hs' e he he₀ ω) := by
  rw [conormalBasisPullbackOfIso, conormalBasisPullback_unitSmulIso]
  exact congrArg (Modules.unitSmulIso · _) (Units.ext (by simp))

end FixedIso

/-- `conormalBasisPullbackOfIso` depends on `e` only through `e.hom`. -/
theorem conormalBasisPullbackOfIso_congr (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S)
    {e₁ e₂ : X' ≅ X} (he : e₁.hom = e₂.hom) (he₁ : e₁.hom ≫ π = π') (he₀₁ : s' ≫ e₁.hom = s)
    (he₂ : e₂.hom ≫ π = π') (he₀₂ : s' ≫ e₂.hom = s) (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullbackOfIso hs hs' e₁ he₁ he₀₁ ω =
      conormalBasisPullbackOfIso hs hs' e₂ he₂ he₀₂ ω :=
  conormalBasisPullback_congr hs hs' rfl he _ _ _ _ ω

/-- Pulling back a conormal basis along `Iso.refl X` recovers it. -/
@[simp]
theorem conormalBasisPullbackOfIso_refl (hs : s ≫ π = 𝟙 S)
    (he : (Iso.refl X).hom ≫ π = π := Category.id_comp π)
    (he₀ : s ≫ (Iso.refl X).hom = s := Category.comp_id s) (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullbackOfIso hs hs (Iso.refl X) he he₀ ω = ω :=
  conormalBasisPullback_id hs _ _ ω

/-- Pulling back successively along `e : X' ≅ X` and `e' : X'' ≅ X'` agrees with `e' ≪≫ e`. -/
theorem conormalBasisPullbackOfIso_trans (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S)
    (hs'' : s'' ≫ π'' = 𝟙 S) (e : X' ≅ X) (he : e.hom ≫ π = π') (he₀ : s' ≫ e.hom = s)
    (e' : X'' ≅ X') (he' : e'.hom ≫ π' = π'') (he₀' : s'' ≫ e'.hom = s')
    (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullbackOfIso hs' hs'' e' he' he₀' (conormalBasisPullbackOfIso hs hs' e he he₀ ω) =
      conormalBasisPullbackOfIso hs hs'' (e' ≪≫ e) (by rw [Iso.trans_hom, Category.assoc, he, he'])
        (by rw [Iso.trans_hom, reassoc_of% he₀', he₀]) ω :=
  (conormalBasisPullback_comp hs hs' hs'' _ _ _ _ ω).trans <|
    conormalBasisPullback_congr hs hs'' (Category.id_comp _) (Iso.trans_hom e' e).symm _ _ _ _ ω

/-- Pulling back along `e` and then `e.symm` recovers `ω`. -/
@[simp]
theorem conormalBasisPullbackOfIso_symm_apply (hs : s ≫ π = 𝟙 S) (hs' : s' ≫ π' = 𝟙 S)
    (e : X' ≅ X) (he : e.hom ≫ π = π') (he₀ : s' ≫ e.hom = s)
    (he_inv : e.inv ≫ π' = π := (Iso.inv_comp_eq e).mpr he.symm)
    (he₀_inv : s ≫ e.inv = s' := (Iso.comp_inv_eq e).mpr he₀.symm)
    (ω : 𝟙_ S.Modules ≅ s.conormalSheaf) :
    conormalBasisPullbackOfIso hs' hs e.symm he_inv he₀_inv
      (conormalBasisPullbackOfIso hs hs' e he he₀ ω) = ω := by
  rw [conormalBasisPullbackOfIso_trans, conormalBasisPullbackOfIso_congr hs hs (e₂ := Iso.refl X)
    (by simp) _ _ (Category.id_comp π) (Category.comp_id s), conormalBasisPullbackOfIso_refl]

end IsoPullback

end Scheme.Hom

end

end AlgebraicGeometry
