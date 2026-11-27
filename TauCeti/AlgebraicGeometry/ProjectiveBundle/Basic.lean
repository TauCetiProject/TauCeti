/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Sections
public import TauCeti.AlgebraicGeometry.Modules.Pushforward.Basic
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.GradedAlgebra.SymmetricAlgebra.Sections
public import TauCeti.AlgebraicGeometry.RelativeProj.TwistingSheaf.Pushforward
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.SymmetricAlgebra

/-!
# The projective bundle of a quasi-coherent module

For a quasi-coherent module `E` on a scheme `S`, the *projective bundle*

`P(E) = Proj_S (Sym E) ⟶ S`

is the relative `Proj` of the graded symmetric algebra of `E`. We use the quotient convention: a
point of `P(E)` with values in `T` over `f : T ⟶ S` is an invertible quotient of `f^* E`, and
`P(E)` carries the tautological quotient

`π^* E ⟶ 𝒪(1)`,

adjoint to the map `E ≅ Sym¹ E ⟶ π_* 𝒪(1)` sending a section `e` over an affine open `U` to the
fraction `e / 1` on the chart `Proj (Sym Γ(E, U))`.

Since `Sym E` is generated in degree one, every twisting sheaf `𝒪(m)`, `m ∈ ℤ`, of `P(E)` is
invertible, and the tautological quotient is an epimorphism: on the chart `D₊(e)` of a section
`e` of `E`, the image `e / 1` of the pullback of `e` generates `𝒪(1)`. No finiteness hypothesis on
`E` is needed.

## Main definitions

* `TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle S E`: the projective bundle `P(E)`.
* `TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle.projection S E`: the structure
  morphism `π : P(E) ⟶ S`.
* `TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle.twistingSheaf S E m`: the twisting
  sheaf `𝒪(m)` of `P(E)`, as an invertible sheaf.
* `TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle.universalQuotient S E`: the
  tautological quotient `π^* E ⟶ 𝒪(1)`.

* `TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle.affineOpenIso F hU`: the affine
  restriction as the projective spectrum of the symmetric algebra of the sections. It uses
  `TauCeti.AlgebraicGeometry.gradedSymmetricAlgebraSectionsEquiv` and
  `CategoryTheory.CommMon.isPullback_relativeProjCover_fromSpec`, composed using
  Mathlib's `CategoryTheory.Limits.IsPullback.isoOverPullback`.

## Main results

In the namespace `TauCeti.AlgebraicGeometry.ProjectiveBundles.projectiveBundle`:

* `affineOpenIso_inv_left_snd`: the map from the affine model into the projective bundle is the
  graded comparison followed by the relative `Proj` chart inclusion.
* `universalQuotient_app_pullbackSections`: the tautological quotient sends the pullback of a
  section `e` of `E` over an affine open `U` to the section of `𝒪(1)` that is `e / 1` on the chart
  over `U`.
* `epi_universalQuotient`: the tautological quotient is an epimorphism.

## References

* [The Stacks Project, Section 27.21, Projective bundles](https://stacks.math.columbia.edu/tag/01OA)
* A. Grothendieck and J. Dieudonné, *Éléments de géométrie algébrique II*, §4.1.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite DirectSum

namespace TauCeti.AlgebraicGeometry.ProjectiveBundles

open _root_.AlgebraicGeometry

universe u

variable (S : Scheme.{u}) (E : S.Modules) [E.IsQuasicoherent]

/-- The **projective bundle** `P(E) = Proj_S (Sym E)` of a quasi-coherent module `E` on `S`, in the
quotient convention: the relative `Proj` of the graded symmetric algebra of `E`. -/
@[expose, stacks 01OA]
def projectiveBundle : Scheme.{u} :=
  ((gradedSymmetricAlgebra S).obj ⟨E, inferInstance⟩).obj.relativeProj

namespace projectiveBundle

/-- The structure morphism `π : P(E) ⟶ S` of the projective bundle. It is exposed because the
statements about `universalQuotient` below are typed through `relativeProjToBase`; use
`projection_def` to rewrite it. -/
@[expose]
def projection : projectiveBundle S E ⟶ S :=
  ((gradedSymmetricAlgebra S).obj ⟨E, inferInstance⟩).obj.relativeProjToBase

/-- The structure morphism of `P(E)` is the structure morphism of the relative `Proj` of `Sym E`. -/
theorem projection_def :
    projection S E = ((gradedSymmetricAlgebra S).obj ⟨E, inferInstance⟩).obj.relativeProjToBase :=
  (rfl)

section Affine

variable {S : Scheme.{u}} (F : QuasicoherentSheaf S)
variable {U : S.Opens} (hU : IsAffineOpen U)

/-- The final change of structure map in the affine chart comparison. -/
private def affineOpenCoeffIso :
    Over.mk (Proj.toSpecCoeff (TauCeti.SymmetricAlgebra.homogeneousSubmodule Γ(S, U)
      ((Scheme.Modules.sectionsFunctor U).obj F.obj))) ≅
      Over.mk (TauCeti.SymmetricAlgebra.projToSpec Γ(S, U)
        ((Scheme.Modules.sectionsFunctor U).obj F.obj)) :=
  Over.isoMk (Iso.refl _) ((Category.id_comp _).trans
    (Proj.toSpecCoeff_homogeneousSubmodule Γ(S, U) _).symm)

/-- Over an affine open `U` of the base, the restriction of `P(E)` is isomorphic over
`Spec Γ(S, U)` to the projective spectrum of the symmetric algebra of the sections of `E` on `U`. -/
def affineOpenIso :
    Over.mk (pullback.fst hU.fromSpec (projection S F.obj)) ≅
      Over.mk (TauCeti.SymmetricAlgebra.projToSpec Γ(S, U)
        ((Scheme.Modules.sectionsFunctor U).obj F.obj)) :=
  let A := ((gradedSymmetricAlgebra S).obj F).obj
  let chartIso := Proj.mapIsoOverOfAlgEquiv _ _ (gradedSymmetricAlgebraSectionsEquiv F hU)
    (gradedSymmetricAlgebraSectionsEquiv_mem_grade_iff F hU)
  (A.isPullback_relativeProjCover_fromSpec ⟨U, hU⟩).isoOverPullback.symm ≪≫
    chartIso ≪≫ affineOpenCoeffIso (U := U) F

/-- The inverse affine comparison followed by the projection to the projective bundle is the
graded comparison on projective spectra followed by the relative `Proj` chart inclusion. -/
@[reassoc (attr := simp)]
theorem affineOpenIso_inv_left_snd :
    (affineOpenIso F hU).inv.left ≫ pullback.snd hU.fromSpec (projection S F.obj) =
      (Proj.mapIsoOverOfAlgEquiv _ _ (gradedSymmetricAlgebraSectionsEquiv F hU)
        (gradedSymmetricAlgebraSectionsEquiv_mem_grade_iff F hU)).inv.left ≫
        ((gradedSymmetricAlgebra S).obj F).obj.relativeProjCover.f ⟨U, hU⟩ := by
  let h := ((gradedSymmetricAlgebra S).obj F).obj.isPullback_relativeProjCover_fromSpec ⟨U, hU⟩
  let e := Proj.mapIsoOverOfAlgEquiv _ _ (gradedSymmetricAlgebraSectionsEquiv F hU)
    (gradedSymmetricAlgebraSectionsEquiv_mem_grade_iff F hU)
  have hCoeff : (affineOpenCoeffIso (U := U) F).inv.left = 𝟙 _ := by
    simp only [affineOpenCoeffIso, Over.isoMk_inv_left, Iso.refl_inv, Over.mk_left]
  have hInv : (h.isoOverPullback.symm ≪≫ e ≪≫ affineOpenCoeffIso (U := U) F).inv.left =
      e.inv.left ≫ h.isoOverPullback.hom.left := by
    simp only [Iso.trans_inv, Iso.symm_inv, Over.comp_left, hCoeff, Category.id_comp]
  unfold affineOpenIso
  calc
    _ = (e.inv.left ≫ h.isoOverPullback.hom.left) ≫ pullback.snd _ _ :=
      congrArg (· ≫ pullback.snd _ _) hInv
    _ = _ := by rw [Category.assoc, h.isoOverPullback_hom_left_comp_snd]

end Affine

/-- The **twisting sheaf** `𝒪(m)` of the projective bundle `P(E)`, for `m ∈ ℤ`. It is invertible
because `Sym E` is generated in degree one. It is exposed because the statements about
`universalQuotient` below are typed through `relativeProjTwistingSheaf`; use `twistingSheaf_obj` to
rewrite it. -/
@[expose]
def twistingSheaf (m : ℤ) : InvertibleSheaf (projectiveBundle S E) :=
  ⟨((gradedSymmetricAlgebra S).obj ⟨E, inferInstance⟩).obj.relativeProjTwistingSheaf m,
    isInvertible_relativeProjTwistingSheaf_gradedSymmetricAlgebra _ m⟩

/-- The underlying module of the twisting sheaf `𝒪(m)` of `P(E)` is the twisting sheaf of the
relative `Proj` of `Sym E`. -/
theorem twistingSheaf_obj (m : ℤ) :
    (twistingSheaf S E m).obj =
      ((gradedSymmetricAlgebra S).obj ⟨E, inferInstance⟩).obj.relativeProjTwistingSheaf m :=
  (rfl)

/-- The **tautological quotient** `π^* E ⟶ 𝒪(1)` of the projective bundle: the morphism adjoint to
the map `E ≅ Sym¹ E ⟶ π_* 𝒪(1)` that sends a section `e` of `E` over an affine open `U` to the
section of `𝒪(1)` that is `e / 1` on the chart `Proj (Sym Γ(E, U))` over `U`. -/
def universalQuotient :
    (Scheme.Modules.pullback (projection S E)).obj E ⟶ (twistingSheaf S E 1).obj :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (projection S E)).homEquiv _ _).symm
    ((gradedSymmetricAlgebraXOneIso ⟨E, inferInstance⟩).inv ≫
      ((gradedSymmetricAlgebra S).obj ⟨E, inferInstance⟩).obj.relativeProjToTwistingSheaf
        Nat.cast_one)

/-- The morphism `E ⟶ π_* 𝒪(1)` adjoint to the tautological quotient is the composite of
`E ≅ Sym¹ E` with the graded map `Sym¹ E ⟶ π_* 𝒪(1)`. -/
theorem homEquiv_universalQuotient :
    (Scheme.Modules.pullbackPushforwardAdjunction (projection S E)).homEquiv _ _
        (universalQuotient S E) =
      (gradedSymmetricAlgebraXOneIso ⟨E, inferInstance⟩).inv ≫
        ((gradedSymmetricAlgebra S).obj ⟨E, inferInstance⟩).obj.relativeProjToTwistingSheaf
          Nat.cast_one :=
  Equiv.apply_symm_apply _ _

/-- **The tautological quotient on pulled-back sections**: it sends the pullback of a section `e` of
`E` over an open `U` to the image of `e` under `E ≅ Sym¹ E ⟶ π_* 𝒪(1)`. Over an affine open `U`, the
latter is the section of `𝒪(1)` that is `e / 1` on the chart over `U`
(`CategoryTheory.CommMon.π_app_relativeProjToTwistingSheaf_app`). -/
theorem universalQuotient_app_pullbackSections (U : S.Opens) (e : Γ(E, U)) :
    (universalQuotient S E).app _ (Scheme.Hom.pullbackSections (projection S E) E U e) =
      (((gradedSymmetricAlgebra S).obj ⟨E, inferInstance⟩).obj.relativeProjToTwistingSheaf
        Nat.cast_one).app U ((gradedSymmetricAlgebraXOneIso ⟨E, inferInstance⟩).inv.app U e) := by
  have h := congr($(homEquiv_universalQuotient S E).app U e)
  rw [Adjunction.homEquiv_unit] at h
  rw [Scheme.Hom.pullbackSections_apply]
  exact h

/-- The graded symmetric algebra of `E`, for the proofs below. -/
private abbrev symAlg : CommMon (GradedObject ℕ S.Modules) :=
  ((gradedSymmetricAlgebra S).obj ⟨E, inferInstance⟩).obj

/-- On the chart over an affine open `U`, the tautological quotient sends the pullback of a section
`e` of `E` over `U` to the section `b / 1` of `𝒪(1)`, where `b` is the image of `e` in `Sym¹ E`. -/
private theorem π_app_universalQuotient_app_pullbackSectionsLE (U : S.AffineZariskiSite)
    (e : Γ(E, U.toOpens)) {W : (projectiveBundle S E).Opens}
    (hW : W ≤ projection S E ⁻¹ᵁ U.toOpens) :
    (((symAlg S E).relativeProjTwistingSheafGlueData 1).π U).app W
        ((universalQuotient S E).app W
          (Scheme.Hom.pullbackSectionsLE (projection S E) E U.toOpens W hW e)) =
      Proj.toTwistingSheaf ((symAlg S E).gradedSectionsGrading U.toOpens) Nat.cast_one
        (colimit.ι (symAlg S E).relativeProjGluingData.functor U ⁻¹ᵁ W)
        ⟨DirectSum.of _ 1 ((gradedSymmetricAlgebraXOneIso ⟨E, inferInstance⟩).inv.app U.toOpens e),
          (symAlg S E).of_mem_gradedSectionsGrading 1 _⟩ := by
  -- write the pullback to `W` as the restriction of the pullback to `π⁻¹ U`, and move the
  -- restriction past the tautological quotient
  rw [Scheme.Hom.pullbackSectionsLE_apply, Scheme.Modules.Hom.naturality_apply,
    universalQuotient_app_pullbackSections]
  -- `rw` cannot perform the remaining steps: the projection to the chart has source
  -- `relativeProjTwistingSheaf 1` and lies over `relativeProjToBase`, which are `𝒪(1)` and
  -- `projection S E` only up to unfolding, so its naturality and the chart formula `b / 1` are
  -- chained with `Eq.trans`
  refine (PresheafOfModules.naturality_apply
    (((symAlg S E).relativeProjTwistingSheafGlueData 1).π U).val (homOfLE hW).op _).trans ?_
  exact (congrArg (((Scheme.Modules.pushforward
      (colimit.ι (symAlg S E).relativeProjGluingData.functor U)).obj
        (((symAlg S E).relativeProjTwistingSheafGlueData 1).obj U)).val.map (homOfLE hW).op)
    (CommMon.π_app_relativeProjToTwistingSheaf_app _ Nat.cast_one U _)).trans
      (Proj.res_toTwistingSheaf _ _ _)

/-- **The image of a pulled-back section generates `𝒪(1)` on its chart.** Let `e` be a section of
`E` over an affine open `U` and `b` its image in `Sym¹ E`. On every open `W` inside the image of the
standard open `D₊(b)` of the chart over `U`, every section of `𝒪(1)` is a regular multiple of the
image of the pullback of `e` under the tautological quotient. -/
private theorem surjective_smul_universalQuotient_app_pullbackSectionsLE
    (U : S.AffineZariskiSite) (e : Γ(E, U.toOpens)) {W : (projectiveBundle S E).Opens}
    (hW : W ≤ colimit.ι (symAlg S E).relativeProjGluingData.functor U ''ᵁ Proj.basicOpen _
      (DirectSum.of _ 1 ((gradedSymmetricAlgebraXOneIso ⟨E, inferInstance⟩).inv.app U.toOpens e)))
    (hWU : W ≤ projection S E ⁻¹ᵁ U.toOpens) :
    Function.Surjective fun r : Γ(projectiveBundle S E, W) ↦
      r • (universalQuotient S E).app W (Scheme.Hom.pullbackSectionsLE _ E _ _ hWU e) := by
  -- the chart over `U`, typed as a morphism from `Proj (⨁ n, Γ(Symⁿ E, U))` to `P(E)`
  let ι : Proj ((symAlg S E).gradedSectionsGrading U.toOpens) ⟶ projectiveBundle S E :=
    colimit.ι (symAlg S E).relativeProjGluingData.functor U
  have : IsOpenImmersion ι := (symAlg S E).isOpenImmersion_colimit_ι_relativeProjGluingData U
  have hb := (symAlg S E).of_mem_gradedSectionsGrading 1
    ((gradedSymmetricAlgebraXOneIso ⟨E, inferInstance⟩).inv.app U.toOpens e)
  have hWA : W ≤ ι.opensRange := hW.trans (ι.image_le_opensRange _)
  have hWb : ι ⁻¹ᵁ W ≤ Proj.basicOpen _ _ :=
    (Scheme.Hom.preimage_mono _ hW).trans (ι.preimage_image_eq _).le
  have := ι.isIso_app W hWA
  -- on the chart, `r` times the image of the pullback of `e` is `r` times the generator `b / 1`;
  -- `r` acts on the sections of the pushforward along `ι` through `ι.app W r`
  have key (r : Γ(projectiveBundle S E, W)) :
      (((symAlg S E).relativeProjTwistingSheafGlueData 1).π U).app W
        (r • (universalQuotient S E).app W (Scheme.Hom.pullbackSectionsLE _ E _ _ hWU e)) =
      Proj.twistingSheaf.chartSectionsLinearEquiv 1 _ hb _ hWb (ι.app W r) := by
    -- `rw` does not see `r •` through the source of the projection to the chart or through the
    -- sections of the pushforward along `ι`, so these steps are chained with `Eq.trans`
    refine (Scheme.Modules.Hom.app_smul _ r _).trans ((pushforward_obj_smul ι _ r _).trans ?_)
    exact (congrArg (fun z : Γ(Proj.twistingSheaf _ 1, ι ⁻¹ᵁ W) ↦ ι.app W r • z)
      ((π_app_universalQuotient_app_pullbackSectionsLE S E U e hWU).trans
        (Proj.twistingSheaf.toTwistingSheaf_eq_chartGenerator_one _ hb _ hWb))).trans
          (Proj.twistingSheaf.chartSectionsLinearEquiv_apply 1 _ hb _ hWb _).symm
  -- the projection to the chart is bijective on sections over `W`
  refine (Function.Surjective.of_comp_iff' (((symAlg S E).relativeProjTwistingSheafGlueData
    1).bijective_π_app ((symAlg S E).bijective_relativeProjTwistingSheafGlueData_map_app 1) hWA)
      _).mp ?_
  intro t
  obtain ⟨r, hr⟩ := ((Proj.twistingSheaf.chartSectionsLinearEquiv 1 _ hb _ hWb).bijective.comp
    (ConcreteCategory.bijective_of_isIso (ι.app W))).2 t
  exact ⟨r, (key r).trans hr⟩

/-- **The tautological quotient `π^* E ⟶ 𝒪(1)` is an epimorphism.** Every point of `P(E)` lies on
the chart `D₊(b)` of a section `b` of `Sym¹ E ≅ E` over an affine open `U` of `S`, and there the
image `b / 1` of the pullback of `b` generates `𝒪(1)`. -/
instance epi_universalQuotient : Epi (universalQuotient S E) := by
  refine Scheme.Modules.Hom.epi_of_forall_exists_surjective_smul _ fun x ↦ ?_
  obtain ⟨U, y, rfl⟩ : ∃ U : S.AffineZariskiSite, ∃ y : Proj ((symAlg S E).gradedSectionsGrading
      U.toOpens), (symAlg S E).relativeProjCover.f U y = x :=
    (symAlg S E).relativeProjCover.exists_eq x
  -- `y` lies in the standard open `D₊(b)` of a section `b` of degree one
  obtain ⟨⟨_, hb⟩, hyb⟩ := TopologicalSpace.Opens.mem_iSup.mp
    ((Proj.iSup_basicOpen_eq_top_of_adjoin_eq_top _ (CommMon.isGeneratedInDegreeOne_iff.mp
      (isGeneratedInDegreeOne_gradedSymmetricAlgebra _) U.toOpens U.property)).ge (Set.mem_univ y))
  obtain ⟨b, rfl⟩ := DirectSum.mem_summand.mp hb
  -- `b` is the image of a section `e` of `E`
  let φ := (gradedSymmetricAlgebraXOneIso ⟨E, inferInstance⟩).inv
  have : IsIso (φ.app U.toOpens) := Scheme.Modules.Hom.isIso_iff_isIso_app.mp inferInstance _
  obtain ⟨e, rfl⟩ := (ConcreteCategory.bijective_of_isIso (φ.app U.toOpens)).2 b
  let ι := colimit.ι (symAlg S E).relativeProjGluingData.functor U
  have hV : ι ''ᵁ Proj.basicOpen _ (DirectSum.of _ 1 (φ.app U.toOpens e)) ≤
      projection S E ⁻¹ᵁ U.toOpens :=
    ((symAlg S E).relativeProjToBase_preimage U).symm ▸ ι.image_le_opensRange _
  refine ⟨ι ''ᵁ Proj.basicOpen _ (DirectSum.of _ 1 (φ.app U.toOpens e)), ⟨y, hyb, rfl⟩,
    Scheme.Hom.pullbackSectionsLE _ E _ _ hV e, fun W i t ↦ ?_⟩
  -- the restriction to `W` of the image of the pullback of `e` is the image of its pullback to `W`
  have hres : (twistingSheaf S E 1).obj.presheaf.map i.op ((universalQuotient S E).app _
      (Scheme.Hom.pullbackSectionsLE _ E _ _ hV e)) = (universalQuotient S E).app W
        (Scheme.Hom.pullbackSectionsLE _ E _ _ (i.le.trans hV) e) :=
    ((universalQuotient S E).naturality_apply i _).symm.trans
      (congrArg _ (Scheme.Hom.presheaf_map_pullbackSectionsLE _ E _ _ hV i e))
  obtain ⟨r, hr⟩ := surjective_smul_universalQuotient_app_pullbackSectionsLE S E U e i.le
    (i.le.trans hV) t
  exact ⟨r, (congrArg (r • ·) hres).trans hr⟩

end projectiveBundle

end TauCeti.AlgebraicGeometry.ProjectiveBundles
