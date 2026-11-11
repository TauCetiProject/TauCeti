/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.TensorProduct
public import TauCeti.AlgebraicGeometry.Modules.Sections

/-!
# The graded map from a graded algebra to the direct images of its twisting sheaves

Let `A` be a graded algebra on a scheme `X` with quasi-coherent homogeneous components, and let
`p : Proj_X(A) ⟶ X` be its relative `Proj`. This file constructs, for `j : ℕ`, the morphism of
`𝒪_X`-modules

`Aⱼ ⟶ p_* 𝒪(j)`

(`CategoryTheory.CommMon.relativeProjToTwistingSheaf`), the degree-`j` component of the graded map
`A ⟶ ⨁_{n ≥ 0} p_* 𝒪(n)`. Over an affine open `U` of `X`, it sends a section `a ∈ Γ(Aⱼ, U)` to the
section of `𝒪(j)` over `p⁻¹ U` whose image in the chart `Proj (⨁ n, Γ(Aₙ, U))` is the fraction
`a / 1` (`AlgebraicGeometry.Proj.toTwistingSheaf`). These sections are compatible with restriction
between affine opens, because the transition maps of the twisting sheaves of the charts send `a / 1`
to the fraction of the restriction of `a`, and they are linear over `Γ(X, U)`, because functions
pulled back from `U` to the chart are the constants `r / 1`. As the affine opens of `X` are
cover-dense, they extend to a morphism of sheaves of modules on `X`. The components are
multiplicative: they carry the multiplication `Aᵢ ⊗ Aⱼ ⟶ Aᵢ₊ⱼ` to the multiplication of sections
of the twisting sheaves.

## Main definitions

* `CategoryTheory.CommMon.relativeProjToTwistingSheaf A h`: the morphism `Aⱼ ⟶ p_* 𝒪(n)` for
  `h : j = n`, characterized over affine opens by
  `CategoryTheory.CommMon.π_app_relativeProjToTwistingSheaf_app`.

## Main results

* `CategoryTheory.CommMon.relativeProjTwistingSheafMul_relativeProjToTwistingSheaf_app`: the
  components are compatible with the multiplications of `A` and of the twisting sheaves.

## References

* [The Stacks Project, Lemma 27.15.5](https://stacks.math.columbia.edu/tag/01NR)
* R. Hartshorne, *Algebraic Geometry*, Section II.7, before Proposition II.7.10.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite DirectSum

namespace TauCeti

open _root_.AlgebraicGeometry Scheme.AffineZariskiSite

universe u

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules)) [∀ n, (A.X n).IsQuasicoherent]

section Affine

variable {j : ℕ} {n : ℤ} (h : (j : ℤ) = n)

/-- A section of `Aⱼ` over `U`, as a homogeneous element of degree `j` of `⨁ n, Γ(Aₙ, U)`. -/
private def ofGrade (U : X.Opens) : Γ(A.X j, U) →+ A.gradedSectionsGrading U j :=
  ((DirectSum.lof Γ(X, U) ℕ (fun n ↦ Γ(A.X n, U)) j).codRestrict _
    (A.of_mem_gradedSectionsGrading j)).toAddMonoidHom

omit [∀ n, (A.X n).IsQuasicoherent] in
private theorem coe_ofGrade (U : X.Opens) (a : Γ(A.X j, U)) :
    (ofGrade A U a : ⨁ n, Γ(A.X n, U)) = DirectSum.of _ j a :=
  (rfl)

/-- The preimage of an affine open `U` under the structure morphism of the relative `Proj`, viewed
in the chart over `U`. -/
private abbrev chartPreimage (U : X.AffineZariskiSite) :
    (Proj (A.gradedSectionsGrading U.toOpens)).Opens :=
  colimit.ι A.relativeProjGluingData.functor U ⁻¹ᵁ (A.relativeProjToBase ⁻¹ᵁ U.toOpens)

/-- Over the preimage of an affine open `U`, the sections of `𝒪(n)` are the sections of the
twisting sheaf of the chart over `U`. -/
private def chartAddEquiv (n : ℤ) (U : X.AffineZariskiSite) :
    Γ(A.relativeProjTwistingSheaf n, A.relativeProjToBase ⁻¹ᵁ U.toOpens) ≃+
      Γ(Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n, chartPreimage A U) :=
  AddEquiv.ofBijective (((A.relativeProjTwistingSheafGlueData n).π U).app _).hom
    ((A.relativeProjTwistingSheafGlueData n).bijective_π_app
      (A.bijective_relativeProjTwistingSheafGlueData_map_app n)
      (A.relativeProjToBase_preimage U).le)

/-- The section of `𝒪(n)` over the preimage of an affine open `U` whose image in the chart over
`U` is `a / 1`. -/
private def affineHom (U : X.AffineZariskiSite) :
    Γ(A.X j, U.toOpens) →+ Γ(A.relativeProjTwistingSheaf n, A.relativeProjToBase ⁻¹ᵁ U.toOpens) :=
  (chartAddEquiv A n U).symm.toAddMonoidHom.comp
    ((Proj.toTwistingSheaf _ h (chartPreimage A U)).comp (ofGrade A U.toOpens))

private theorem chartAddEquiv_apply (U : X.AffineZariskiSite)
    (s : Γ(A.relativeProjTwistingSheaf n, A.relativeProjToBase ⁻¹ᵁ U.toOpens)) :
    chartAddEquiv A n U s = ((A.relativeProjTwistingSheafGlueData n).π U).app _ s :=
  (rfl)

private theorem chartAddEquiv_affineHom (U : X.AffineZariskiSite) (a : Γ(A.X j, U.toOpens)) :
    chartAddEquiv A n U (affineHom A h U a) =
      Proj.toTwistingSheaf _ h (chartPreimage A U) (ofGrade A U.toOpens a) :=
  (chartAddEquiv A n U).apply_symm_apply _

private theorem π_app_affineHom (U : X.AffineZariskiSite) (a : Γ(A.X j, U.toOpens)) :
    ((A.relativeProjTwistingSheafGlueData n).π U).app _ (affineHom A h U a) =
      Proj.toTwistingSheaf _ h (chartPreimage A U) (ofGrade A U.toOpens a) :=
  chartAddEquiv_affineHom A h U a

/-- The sections of `𝒪(n)` with chart image `a / 1` are compatible with restriction between
affine opens. -/
private theorem affineHom_naturality {U V : X.AffineZariskiSite} (i : V ⟶ U)
    (a : Γ(A.X j, U.toOpens)) :
    ((Scheme.Modules.pushforward A.relativeProjToBase).obj
        (A.relativeProjTwistingSheaf n)).presheaf.map ((toOpensFunctor X).map i).op
        (affineHom A h U a) =
      affineHom A h V ((A.X j).presheaf.map ((toOpensFunctor X).map i).op a) := by
  apply (chartAddEquiv A n V).injective
  refine Eq.trans ?_ (chartAddEquiv_affineHom A h V _).symm
  refine (chartAddEquiv_apply A V _).trans ?_
  refine ((A.relativeProjTwistingSheafGlueData n).transition_app_π_app i
    (A.relativeProjToBase ⁻¹ᵁ V.toOpens) _).symm.trans ?_
  have hle : A.relativeProjToBase ⁻¹ᵁ V.toOpens ≤ A.relativeProjToBase ⁻¹ᵁ U.toOpens :=
    Scheme.Hom.preimage_mono _ ((toOpensFunctor X).map i).le
  have h2 : ((A.relativeProjTwistingSheafGlueData n).π U).app _
        ((A.relativeProjTwistingSheaf n).presheaf.map (homOfLE hle).op (affineHom A h U a)) =
      (Proj.twistingSheaf (A.gradedSectionsGrading U.toOpens) n).presheaf.map
        (homOfLE (Scheme.Hom.preimage_mono _ hle)).op
        (((A.relativeProjTwistingSheafGlueData n).π U).app _ (affineHom A h U a)) :=
    NatTrans.naturality_apply ((A.relativeProjTwistingSheafGlueData n).π U).mapPresheaf
      (homOfLE hle).op (affineHom A h U a)
  have h4 : ((A.relativeProjTwistingSheafGlueData n).π U).app _
        ((A.relativeProjTwistingSheaf n).presheaf.map (homOfLE hle).op (affineHom A h U a)) =
      Proj.toTwistingSheaf _ h (colimit.ι A.relativeProjGluingData.functor U ⁻¹ᵁ
        (A.relativeProjToBase ⁻¹ᵁ V.toOpens)) (ofGrade A U.toOpens a) :=
    h2.trans (congrArg _ (π_app_affineHom A h U a))
  refine (congrArg (((A.relativeProjTwistingSheafGlueData n).transition i).app _) h4).trans ?_
  refine ((A.relativeProjTwistingSheafGlueData n).transition_app_apply i _ _).trans ?_
  refine (congrArg _ (Proj.twistingSheafMap_app_toTwistingSheaf
    (A.restrictGradedSectionsGradedHom ((toOpensFunctor X).map i))
    (A.irrelevant_le_map_restrictGradedSectionsGradedHom_toOpensFunctor i) _ h _)).trans ?_
  exact (Proj.res_toTwistingSheaf h _ _).trans (congrArg _ (Subtype.ext
    ((A.restrictGradedSectionsGradedHom_apply _ _).trans
      (A.restrictGradedSections_of ((toOpensFunctor X).map i) j a))))

/-- The sections of `𝒪(n)` with chart image `a / 1` are linear over the functions on `U`. -/
private theorem affineHom_smul (U : X.AffineZariskiSite) (r : Γ(X, U.toOpens))
    (a : Γ(A.X j, U.toOpens)) :
    affineHom A h U (r • a) = A.relativeProjToBase.app U.toOpens r • affineHom A h U a := by
  apply (chartAddEquiv A n U).injective
  refine (chartAddEquiv_affineHom A h U _).trans ?_
  refine Eq.trans ?_ (chartAddEquiv_apply A U _).symm
  refine Eq.trans ?_ (Scheme.Modules.Hom.app_smul ((A.relativeProjTwistingSheafGlueData n).π U)
    (A.relativeProjToBase.app U.toOpens r) (affineHom A h U a)).symm
  refine Eq.trans ?_ (congrArg _ (π_app_affineHom A h U a)).symm
  have hv (x : chartPreimage A U) :
      (((colimit.ι A.relativeProjGluingData.functor U ≫ A.relativeProjToBase).app U.toOpens
        r).1 x).val =
        Localization.mk (algebraMap Γ(X, U.toOpens) (⨁ n, Γ(A.X n, U.toOpens)) r) 1 := by
    rw [Scheme.Hom.app_eq_appLE]
    exact Proj.val_appLE_apply U.2 _ _ (A.relativeProjCover_f_relativeProjToBase U) le_rfl r x
  refine Proj.twistingSheaf.ext fun x ↦ (Proj.toTwistingSheaf_apply_apply ..).trans
    (Eq.trans ?_ (Proj.twistingSheaf.smul_apply
      ((colimit.ι A.relativeProjGluingData.functor U ≫ A.relativeProjToBase).app U.toOpens r) _
      x).symm)
  refine Eq.trans ?_ (congrArg (· * _) (hv x)).symm
  have hof : (ofGrade A U.toOpens (r • a) : ⨁ n, Γ(A.X n, U.toOpens)) =
      algebraMap _ _ r * DirectSum.of _ j a := by
    rw [coe_ofGrade, ← Algebra.smul_def, ← DirectSum.lof_eq_of Γ(X, U.toOpens),
      ← DirectSum.lof_eq_of Γ(X, U.toOpens), LinearMap.map_smul]
  exact (congrArg (Localization.mk · 1) hof).trans
    ((congrArg (Localization.mk _ ·) (one_mul 1).symm).trans (Localization.mk_mul ..).symm)

/-- The sections of `𝒪(n)` with chart image `a / 1`, as a morphism of abelian presheaves on the
affine opens of `X`. -/
private def affineNatTrans :
    (toOpensFunctor X).op ⋙ (A.X j).presheaf ⟶
      (toOpensFunctor X).op ⋙ ((Scheme.Modules.pushforward A.relativeProjToBase).obj
        (A.relativeProjTwistingSheaf n)).presheaf where
  app U := AddCommGrpCat.ofHom (affineHom A h U.unop)
  naturality _ _ i := AddCommGrpCat.hom_ext (AddMonoidHom.ext fun a ↦
    (affineHom_naturality A h i.unop a).symm)

end Affine

section Hom

variable {j : ℕ} {n : ℤ} (h : (j : ℤ) = n)

/-- The extension of `affineNatTrans` to all opens of `X`, using that the affine opens are
cover-dense and that `p_* 𝒪(n)` is a sheaf. -/
private def presheafHom :
    (A.X j).presheaf ⟶ ((Scheme.Modules.pushforward A.relativeProjToBase).obj
      (A.relativeProjTwistingSheaf n)).presheaf :=
  Functor.IsCoverDense.sheafHom (G := toOpensFunctor X) (K := Opens.grothendieckTopology X)
    (ℱ' := ⟨_, ((Scheme.Modules.pushforward A.relativeProjToBase).obj
      (A.relativeProjTwistingSheaf n)).isSheaf⟩) (affineNatTrans A h)

private theorem presheafHom_app_affine (U : X.AffineZariskiSite) (a : Γ(A.X j, U.toOpens)) :
    (presheafHom A h).app (op U.toOpens) a = affineHom A h U a :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (Functor.IsCoverDense.sheafHom_restrict_eq
    (K := Opens.grothendieckTopology X) (ℱ' := ⟨_, ((Scheme.Modules.pushforward
      A.relativeProjToBase).obj (A.relativeProjTwistingSheaf n)).isSheaf⟩)
    (affineNatTrans A h)) (op U)) a

private theorem presheafHom_smul (V : X.Opens) (r : Γ(X, V)) (a : Γ(A.X j, V)) :
    (presheafHom A h).app (op V) (r • a) = r • (presheafHom A h).app (op V) a := by
  refine Scheme.Modules.sections_ext_of_isAffineOpen fun U hU hUV ↦ ?_
  rw [← NatTrans.naturality_apply, Scheme.Modules.map_smul, Scheme.Modules.map_smul,
    ← NatTrans.naturality_apply]
  exact (presheafHom_app_affine A h ⟨U, hU⟩ _).trans
    ((affineHom_smul A h ⟨U, hU⟩ _ _).trans
      (congrArg _ (presheafHom_app_affine A h ⟨U, hU⟩ _).symm))

/-- **The graded map from `A` to the direct images of the twisting sheaves**: for `j = n`, the
morphism of `𝒪_X`-modules `Aⱼ ⟶ p_* 𝒪(n)` to the direct image of `𝒪(n)` along the structure
morphism `p` of the relative `Proj`. Over an affine open `U` of `X`, it sends `a ∈ Γ(Aⱼ, U)` to
the section of `𝒪(n)` over `p⁻¹ U` whose image in the chart `Proj (⨁ n, Γ(Aₙ, U))` is `a / 1`
(`CategoryTheory.CommMon.π_app_relativeProjToTwistingSheaf_app`). -/
@[stacks 01NR "the graded map"]
def _root_.CategoryTheory.CommMon.relativeProjToTwistingSheaf :
    A.X j ⟶ (Scheme.Modules.pushforward A.relativeProjToBase).obj (A.relativeProjTwistingSheaf n) :=
  ⟨PresheafOfModules.homMk (presheafHom A h) fun V r a ↦ presheafHom_smul A h V.unop r a⟩

/-- **The graded map is `a ↦ a / 1` on the charts**: over an affine open `U` of `X`, the image in
the chart `Proj (⨁ n, Γ(Aₙ, U))` of the section of `𝒪(n)` attached to `a ∈ Γ(Aⱼ, U)` is the
fraction `a / 1`. -/
-- Not a simp lemma: `Scheme.Modules.pushforward_obj_obj` already rewrites its left-hand side.
theorem _root_.CategoryTheory.CommMon.π_app_relativeProjToTwistingSheaf_app
    (U : X.AffineZariskiSite) (a : Γ(A.X j, U.toOpens)) :
    ((A.relativeProjTwistingSheafGlueData n).π U).app (A.relativeProjToBase ⁻¹ᵁ U.toOpens)
        ((A.relativeProjToTwistingSheaf h).app U.toOpens a) =
      Proj.toTwistingSheaf (A.gradedSectionsGrading U.toOpens) h
        (colimit.ι A.relativeProjGluingData.functor U ⁻¹ᵁ (A.relativeProjToBase ⁻¹ᵁ U.toOpens))
        ⟨DirectSum.of _ j a, A.of_mem_gradedSectionsGrading j a⟩ :=
  (congrArg (chartAddEquiv A n U) (presheafHom_app_affine A h U a)).trans
    (chartAddEquiv_affineHom A h U a)

end Hom

section Mul

variable {i j : ℕ} {m n : ℤ} (hi : (i : ℤ) = m) (hj : (j : ℤ) = n)

/-- Over an affine open, the graded map is multiplicative, as `a / 1` times `b / 1` is
`(a * b) / 1` in the charts. -/
private theorem relativeProjTwistingSheafMul_relativeProjToTwistingSheaf_app_affine
    (U : X.AffineZariskiSite) (a : Γ(A.X i, U.toOpens)) (b : Γ(A.X j, U.toOpens)) :
    A.relativeProjTwistingSheafMul (A.relativeProjToBase ⁻¹ᵁ U.toOpens) m n
        ((A.relativeProjToTwistingSheaf hi).app U.toOpens a)
        ((A.relativeProjToTwistingSheaf hj).app U.toOpens b) =
      (A.relativeProjToTwistingSheaf (by push_cast; omega : ((i + j : ℕ) : ℤ) = m + n)).app
        U.toOpens (GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.X n, U.toOpens)) a b) := by
  apply (chartAddEquiv A (m + n) U).injective
  refine (chartAddEquiv_apply A U _).trans ?_
  refine (CommMon.π_app_relativeProjTwistingSheafMul (A := A) (m := m) (n := n)
    (W := A.relativeProjToBase ⁻¹ᵁ U.toOpens) U _ _).trans ?_
  refine (congrArg₂ (fun s t ↦ Proj.twistingSheaf.mul (A.gradedSectionsGrading U.toOpens)
      (colimit.ι A.relativeProjGluingData.functor U ⁻¹ᵁ (A.relativeProjToBase ⁻¹ᵁ U.toOpens))
      m n s t)
    (CommMon.π_app_relativeProjToTwistingSheaf_app A hi U a)
    (CommMon.π_app_relativeProjToTwistingSheaf_app A hj U b)).trans ?_
  refine (Proj.mul_toTwistingSheaf hi hj _ _ _).trans ?_
  refine Eq.trans ?_ ((chartAddEquiv_apply A U _).trans
    (CommMon.π_app_relativeProjToTwistingSheaf_app A _ U _)).symm
  exact congrArg (Proj.toTwistingSheaf (A.gradedSectionsGrading U.toOpens)
    (by push_cast; omega : ((i + j : ℕ) : ℤ) = m + n)
    (colimit.ι A.relativeProjGluingData.functor U ⁻¹ᵁ (A.relativeProjToBase ⁻¹ᵁ U.toOpens)))
    (Subtype.ext (DirectSum.of_mul_of (A := fun n ↦ Γ(A.X n, U.toOpens)) a b))

/-- **The graded map is multiplicative**: the product of the sections of `𝒪(m)` and `𝒪(n)`
attached to `a ∈ Γ(Aᵢ, V)` and `b ∈ Γ(Aⱼ, V)` is the section of `𝒪(m + n)` attached to their
product in `Γ(Aᵢ₊ⱼ, V)`. -/
theorem _root_.CategoryTheory.CommMon.relativeProjTwistingSheafMul_relativeProjToTwistingSheaf_app
    (V : X.Opens) (a : Γ(A.X i, V)) (b : Γ(A.X j, V)) :
    A.relativeProjTwistingSheafMul (A.relativeProjToBase ⁻¹ᵁ V) m n
        ((A.relativeProjToTwistingSheaf hi).app V a) ((A.relativeProjToTwistingSheaf hj).app V b) =
      (A.relativeProjToTwistingSheaf (by push_cast; omega : ((i + j : ℕ) : ℤ) = m + n)).app V
        (GradedMonoid.GMul.mul (A := fun n ↦ Γ(A.X n, V)) a b) := by
  refine Scheme.Modules.sections_ext_of_isAffineOpen
    (M := (Scheme.Modules.pushforward A.relativeProjToBase).obj
      (A.relativeProjTwistingSheaf (m + n))) fun U hU hUV ↦ ?_
  have hres {k : ℕ} {l : ℤ} (hk : (k : ℤ) = l) (c : Γ(A.X k, V)) :
      (A.relativeProjTwistingSheaf l).presheaf.map
          (homOfLE (Scheme.Hom.preimage_mono A.relativeProjToBase hUV)).op
          ((A.relativeProjToTwistingSheaf hk).app V c) =
        (A.relativeProjToTwistingSheaf hk).app U ((A.X k).presheaf.map (homOfLE hUV).op c) :=
    (NatTrans.naturality_apply (A.relativeProjToTwistingSheaf hk).mapPresheaf
      (homOfLE hUV).op c).symm
  refine (CommMon.res_relativeProjTwistingSheafMul
    (homOfLE (Scheme.Hom.preimage_mono A.relativeProjToBase hUV)) _ _).trans ?_
  refine (congrArg₂ (fun s t ↦ A.relativeProjTwistingSheafMul (A.relativeProjToBase ⁻¹ᵁ U) m n s t)
    (hres hi a) (hres hj b)).trans ?_
  refine (relativeProjTwistingSheafMul_relativeProjToTwistingSheaf_app_affine A hi hj ⟨U, hU⟩
    _ _).trans (Eq.trans ?_ (hres _ _).symm)
  exact congrArg _ (A.map_gMul_sections (homOfLE hUV) a b).symm

end Mul

end TauCeti
