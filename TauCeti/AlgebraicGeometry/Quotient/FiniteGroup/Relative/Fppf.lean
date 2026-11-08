/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Fppf
public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Relative.Basic
import TauCeti.CategoryTheory.Extensive

/-!
# Free relative invariant quotients by finite groups are fppf quotients

Let `A` be a quasi-coherent commutative `𝒪ₓ`-algebra on a scheme `X` and let a finite group `G`
act on `Spec_X(A)` by automorphisms over `X`, through `ρ : G →* Aut A`. Write
`Spec_X(A) ⟶ Spec_X(A)/G` for the relative invariant quotient projection of
`TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Relative.Basic`.

When the action is free, in the sense that over every affine open `U` of `X` and for every `g ≠ 1`
the sections `g • a - a` with `a` in `Γ(A.X, U)` generate the unit ideal, the projection is a finite
étale `G`-torsor and `Spec_X(A)/G` is the fppf quotient. Over each affine open `U` this is the
affine statement (`TauCeti.AffineInvariantQuotient.etale_projection`,
`TauCeti.AffineInvariantQuotient.isPullback_of_free`). Étaleness is local on the target. The torsor
square, which identifies `∐_g Spec_X(A)` with `Spec_X(A) ×_{Spec_X(A)/G} Spec_X(A)`, is local on
the source of the projection (`AlgebraicGeometry.Scheme.isPullback_of_openCover`): over the chart
`Spec Γ(A.X, U)`, finite coproducts are stable under base change
(`CategoryTheory.FinitaryPreExtensive.isPullback_sigmaMap_sigmaDesc_id`) and the chart of
`Spec_X(A)/G` over `U` has preimage the chart of `Spec_X(A)`
(`CategoryTheory.CommMon.isPullback_projection_relativeSpecπ`), so the square restricts to the
affine torsor square. The étale surjective projection generates an fppf covering sieve, and the
fppf quotient statement follows from the kernel pair by
`CategoryTheory.IsKernelPair.isColimitYonedaCofork`.

## Main results

* `CommMon.etale_invariantSubalgebraPresheaf_relativeSpecπ_of_free` and
  `CommMon.isFinite_invariantSubalgebraPresheaf_relativeSpecπ_of_free`: for a free action, the
  projection is finite étale.
* `CommMon.isPullback_invariantSubalgebraPresheaf_relativeSpecπ_of_free`: for a free action,
  `∐_g Spec_X(A)` is the kernel pair of the projection.
* `CommMon.isColimitInvariantQuotientFppfYonedaCofork`: for a free action, `Spec_X(A)/G` represents
  the fppf quotient sheaf of `Spec_X(A)` by `G`.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4 (free actions and
  fppf quotients).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace CategoryTheory.CommMon

universe u v

noncomputable section

variable {X : Scheme.{u}}

variable {A : CommMon X.Modules} {G : Type v} [Group G] [Finite G] [A.X.IsQuasicoherent]
  {ρ : G →* Aut A}

omit [Finite G] [A.X.IsQuasicoherent] in
/-- Over an affine open `U` of `X`, freeness of the action on the sections over `U`, in the form
used by the affine invariant quotient. -/
private lemma free_sectionsMulSemiringAction
    (hG : ∀ (U : X.affineOpens) (g : G), g ≠ 1 →
      Ideal.span (Set.range fun x : Γ(A.X, U) ↦ sectionsAlgHom (ρ g).asIso.hom U x - x) = ⊤)
    (U : X.AffineZariskiSite) :
    letI := sectionsMulSemiringAction ρ U.toOpens
    ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun x : Γ(A.X, U.toOpens) ↦ g • x - x) = ⊤ := by
  let := sectionsMulSemiringAction ρ U.toOpens
  intro g hg
  simpa only [sectionsMulSemiringAction_smul] using hG ⟨U.1, U.2⟩ g hg

variable
    (hG : ∀ (U : X.affineOpens) (g : G), g ≠ 1 →
      Ideal.span (Set.range fun x : Γ(A.X, U) ↦ sectionsAlgHom (ρ g).asIso.hom U x - x) = ⊤)
include hG

/-- For a free action, the quotient projection `Spec_X(A) ⟶ Spec_X(A)/G` is étale. -/
theorem etale_invariantSubalgebraPresheaf_relativeSpecπ_of_free :
    Etale (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
  have := HasRingHomProperty.instIsZariskiLocalAtTarget @Etale.{u} (Q := RingHom.Etale)
  refine ((invariantSubalgebraPresheaf ρ).relativeSpecπ_iff @Etale).mpr fun U ↦ ?_
  let := sectionsMulSemiringAction ρ U.toOpens
  have := TauCeti.AffineInvariantQuotient.etale_projection (free_sectionsMulSemiringAction hG U)
  rw [specMap_invariantSections]
  infer_instance

/-- For a free action, the quotient projection `Spec_X(A) ⟶ Spec_X(A)/G` is finite, with no
finiteness hypothesis on `Spec_X(A)` over `X`. -/
theorem isFinite_invariantSubalgebraPresheaf_relativeSpecπ_of_free :
    IsFinite (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
  have := etale_invariantSubalgebraPresheaf_relativeSpecπ_of_free hG
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩

open TauCeti.AffineInvariantQuotient in
/-- **The torsor square of a free relative quotient.** For a free action, the identity and the
action of `g` on the component of `g` exhibit `∐_g Spec_X(A)` as the kernel pair
`Spec_X(A) ×_{Spec_X(A)/G} Spec_X(A)` of the quotient projection. -/
theorem isPullback_invariantSubalgebraPresheaf_relativeSpecπ_of_free :
    IsPullback (Sigma.desc fun _ : G ↦ 𝟙 A.relativeSpec)
      (Sigma.desc fun g : G ↦ relativeSpecMap (ρ g).asIso.hom)
      (invariantSubalgebraPresheaf ρ).relativeSpecπ
      (invariantSubalgebraPresheaf ρ).relativeSpecπ := by
  refine Scheme.isPullback_of_openCover _ _ _ _ A.relativeSpecCover fun U ↦ ?_
  let := sectionsMulSemiringAction ρ U.toOpens
  -- Rebind the charts over `U` at their explicit sources, as in
  -- `SubalgebraPresheaf.relativeSpecπ_relativeSpecToBase`.
  let ι : Spec (CommRingCat.of Γ(A.X, U.toOpens)) ⟶ A.relativeSpec := A.relativeSpecCover.f U
  let ιQ : Spec (CommRingCat.of ((invariantSubalgebraPresheaf ρ).sections U.toOpens)) ⟶
      (invariantSubalgebraPresheaf ρ).relativeSpec :=
    (invariantSubalgebraPresheaf ρ).relativeSpecCover.f U
  let e := quotientIsoSpecInvariantSections ρ U.toOpens
  -- The base change of `∐_g Spec_X(A)` along the chart over `U` is `∐_g` of the chart.
  have hb : IsPullback (Limits.Sigma.map fun _ : G ↦ ι)
      (Sigma.desc fun _ : G ↦ 𝟙 (Spec (CommRingCat.of Γ(A.X, U.toOpens))))
      (Sigma.desc fun _ : G ↦ 𝟙 A.relativeSpec) ι :=
    FinitaryPreExtensive.isPullback_sigmaMap_sigmaDesc_id ι
  -- Over the chart, the square is the torsor square of the affine quotient, followed by the
  -- chart of the quotient projection.
  have hchart : IsPullback ι (projection Γ(A.X, U.toOpens) G)
      (invariantSubalgebraPresheaf ρ).relativeSpecπ (e.hom ≫ ιQ) :=
    ((isPullback_projection_relativeSpecπ (ρ := ρ) U).of_iso (Iso.refl _) e.symm (Iso.refl _)
      (Iso.refl _) (by simp [e]) (by cat_disch)
      (by rw [Iso.symm_hom, Iso.inv_hom_id_assoc]; exact Category.comp_id _) (by simp)).flip
  have hpaste :=
    (isPullback_of_free Γ(A.X, U.toOpens) G (free_sectionsMulSemiringAction hG U)).flip.paste_horiz
      hchart
  refine hpaste.flip.of_iso hb.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans hb.isoPullback_hom_snd.symm
  · -- The components of the pulled-back cover are the first projections, and `ι` is the chart
    -- over `U`.
    refine Sigma.hom_ext _ _ fun g ↦ ?_
    calc _ = specComap Γ(A.X, U.toOpens) G g ≫ ι := by simp
      _ = ι ≫ relativeSpecMap (ρ g).asIso.hom := specComap_relativeSpecCover_f U g
      _ = Sigma.ι _ g ≫ (hb.isoPullback.hom ≫ pullback.fst _ ι) ≫
          Sigma.desc fun g ↦ relativeSpecMap (ρ g).asIso.hom := by
        rw [hb.isoPullback_hom_fst]; simp
      _ = _ := by
        rw [Category.assoc]
        exact congrArg (fun f ↦ Sigma.ι _ g ≫ hb.isoPullback.hom ≫ f ≫ _)
          (PreZeroHypercover.pullback₁_f _ A.relativeSpecCover.toPreZeroHypercover U).symm
  · exact (Category.comp_id _).trans (((Category.assoc _ _ _).symm.trans
      (isPullback_projection_relativeSpecπ (ρ := ρ) U).w).trans (Category.id_comp _).symm)
  · simp

/-- **The fppf quotient of a free relative action.** For a free action, under the Yoneda embedding
into fppf sheaves, the quotient projection `Spec_X(A) ⟶ Spec_X(A)/G` is the coequalizer of the two
maps `∐_g Spec_X(A) ⇉ Spec_X(A)` given by the identity and by the action of `g` on the component
of `g`. Thus `Spec_X(A)/G` represents the fppf quotient sheaf of `Spec_X(A)` by `G`. -/
def isColimitInvariantQuotientFppfYonedaCofork :
    IsColimit (Cofork.ofπ
        (Scheme.fppfTopology.yoneda.map (invariantSubalgebraPresheaf ρ).relativeSpecπ)
        (by simp only [← Functor.map_comp,
          (isPullback_invariantSubalgebraPresheaf_relativeSpecπ_of_free hG).w]) :
      Cofork (Scheme.fppfTopology.yoneda.map (Sigma.desc fun _ : G ↦ 𝟙 A.relativeSpec))
        (Scheme.fppfTopology.yoneda.map
          (Sigma.desc fun g : G ↦ relativeSpecMap (ρ g).asIso.hom))) :=
  have := etale_invariantSubalgebraPresheaf_relativeSpecπ_of_free hG
  IsKernelPair.isColimitYonedaCofork Scheme.fppfTopology
    (isPullback_invariantSubalgebraPresheaf_relativeSpecπ_of_free hG)
    (Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage _))

end

end CategoryTheory.CommMon
