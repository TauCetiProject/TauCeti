/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Fppf
public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Glued.Basic
import TauCeti.CategoryTheory.Extensive

/-!
# Free quotients of schemes with an invariant affine cover are fppf quotients

Let a finite group `G` act on a scheme `X` by automorphisms, `σ : G →* Aut X`, such that the
invariant affine opens of `X` cover it, and write `X ⟶ X/G` for the glued quotient projection of
`TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Glued.Basic`.

Call the action free when `X` is covered by invariant affine opens `U` such that for every `g ≠ 1`
the sections `g • a - a` with `a` in `Γ(X, U)` generate the unit ideal; that is, no `g ≠ 1` has a
fixed point scheme-theoretically. For a free action, the projection `X ⟶ X/G` is a finite étale
`G`-torsor and `X/G` represents the fppf quotient sheaf of `X` by `G`. This is the constant-group
case of SGA 3, Exposé V, Théorème 4.1, for schemes with an invariant affine open cover, without
any separatedness hypothesis. A free action has an invariant affine cover; the statements still
take a proof `hσ` of `TauCeti.InvariantQuotient.HasInvariantAffineCover σ` to name the projection,
and by proof irrelevance every such proof names the same projection.

Over the chart `Spec Γ(X, U)ᴳ` of each invariant affine open `U` of the family, the projection is
the affine invariant quotient projection
(`TauCeti.InvariantQuotient.isPullback_projection_fromSpec`), so the statements reduce to the
affine ones (`TauCeti.AffineInvariantQuotient.etale_projection` and
`TauCeti.AffineInvariantQuotient.isPullback_specAction_of_free`). Étaleness is local on the target
(`TauCeti.InvariantQuotient.projection_of_forall_exists`). The torsor square, which identifies
`∐_g X` with `X ×_{X/G} X` through the identity and `σ g` on the component of `g`, is local on the
source of the projection (`AlgebraicGeometry.Scheme.isPullback_of_openCover`): over the chart
`Spec Γ(X, U) ⟶ X`, finite coproducts are stable under base change
(`CategoryTheory.FinitaryPreExtensive.isPullback_sigmaMap_sigmaDesc_id`), so the square restricts
to the affine torsor square. The étale surjective projection generates an fppf covering sieve, and
the fppf quotient statement follows from the kernel pair by
`CategoryTheory.IsKernelPair.isColimitYonedaCofork`.

## Main results

* `TauCeti.InvariantQuotient.etale_projection_of_free` and
  `TauCeti.InvariantQuotient.isFinite_projection_of_free`: for a free action, the projection is
  finite étale.
* `TauCeti.InvariantQuotient.isPullback_projection_of_free`: for a free action, `∐_g X` is the
  kernel pair of the projection.
* `TauCeti.InvariantQuotient.isColimitFppfYonedaCofork`: for a free action, `X/G` represents the
  fppf quotient sheaf of `X` by `G`.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §4, Théorème 4.1.
* D. Mumford, *Abelian Varieties*, §7, Theorem 1.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.InvariantQuotient

universe u v

variable {X : Scheme.{u}} {G : Type v} [Group G] [Finite G] {σ : G →* Aut X}
  (hσ : HasInvariantAffineCover σ)
  (hG : ∀ x : X, ∃ U : InvariantAffineOpens σ, x ∈ U.1 ∧
    letI := Scheme.sectionsMulSemiringAction σ U.2.2
    ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : Γ(X, U.1) ↦ g • a - a) = ⊤)

include hG

/-- The open cover of `X` by the spectra of the invariant affine opens over which the action is
free. -/
private noncomputable def freeCover : X.OpenCover :=
  Scheme.Cover.mkOfCovers {U : InvariantAffineOpens σ //
      letI := Scheme.sectionsMulSemiringAction σ U.2.2
      ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : Γ(X, U.1) ↦ g • a - a) = ⊤}
    (fun U ↦ Spec Γ(X, U.1.1)) (fun U ↦ U.1.2.1.fromSpec) fun x ↦ by
      obtain ⟨U, hxU, hU⟩ := hG x
      obtain ⟨p, rfl⟩ := U.2.1.range_fromSpec.ge hxU
      exact ⟨⟨U, hU⟩, p, rfl⟩

/-- For a free action, the quotient projection `X ⟶ X/G` is étale. -/
theorem etale_projection_of_free : Etale (projection σ hσ) := by
  have := HasRingHomProperty.instIsZariskiLocalAtTarget @Etale.{u} (Q := RingHom.Etale)
  refine projection_of_forall_exists hσ (P := @Etale) fun x ↦ ?_
  obtain ⟨U, hxU, hU⟩ := hG x
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  exact ⟨U, hxU, AffineInvariantQuotient.etale_projection hU⟩

/-- For a free action, the quotient projection `X ⟶ X/G` is finite. -/
theorem isFinite_projection_of_free : IsFinite (projection σ hσ) := by
  have := etale_projection_of_free hσ hG
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨inferInstance, inferInstance⟩

/-- **The torsor square of a free quotient.** For a free action, the identity and the automorphism
`σ g` on the component of `g` exhibit `∐_g X` as the kernel pair `X ×_{X/G} X` of the quotient
projection. -/
theorem isPullback_projection_of_free :
    IsPullback (Sigma.desc fun _ : G ↦ 𝟙 X) (Sigma.desc fun g : G ↦ (σ g).asIso.hom)
      (projection σ hσ) (projection σ hσ) := by
  refine Scheme.isPullback_of_openCover _ _ _ _ (freeCover hG) fun ⟨U, hU⟩ ↦ ?_
  let := Scheme.sectionsMulSemiringAction σ U.2.2
  -- The base change of `∐_g X` along the chart over `U` is `∐_g` of the chart.
  have hb : IsPullback (Limits.Sigma.map fun _ : G ↦ U.2.1.fromSpec)
      (Sigma.desc fun _ : G ↦ 𝟙 (Spec Γ(X, U.1))) (Sigma.desc fun _ : G ↦ 𝟙 X) U.2.1.fromSpec :=
    FinitaryPreExtensive.isPullback_sigmaMap_sigmaDesc_id U.2.1.fromSpec
  -- Over the chart, the square is the affine torsor square followed by the chart square of the
  -- quotient projection.
  have hpaste := (AffineInvariantQuotient.isPullback_specAction_of_free Γ(X, U.1) G
    hU).flip.paste_horiz (isPullback_projection_fromSpec hσ U).flip
  refine hpaste.flip.of_iso hb.isoPullback (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · exact (Category.comp_id _).trans hb.isoPullback_hom_snd.symm
  · -- The components of the pulled-back cover are the first projections.
    refine Sigma.hom_ext _ _ fun g ↦ ?_
    calc _ = (AffineInvariantQuotient.specAction Γ(X, U.1) G g).asIso.hom ≫ U.2.1.fromSpec := by
          simp
      _ = U.2.1.fromSpec ≫ (σ g).asIso.hom := specAction_fromSpec U.2.1 U.2.2 g
      _ = Sigma.ι _ g ≫ (hb.isoPullback.hom ≫ pullback.fst _ U.2.1.fromSpec) ≫
          Sigma.desc fun g ↦ (σ g).asIso.hom := by
        rw [hb.isoPullback_hom_fst]; simp
      _ = _ := by
        rw [Category.assoc]
        exact congrArg (fun f ↦ Sigma.ι _ g ≫ hb.isoPullback.hom ≫ f ≫ _)
          (PreZeroHypercover.pullback₁_f _ (freeCover hG).toPreZeroHypercover ⟨U, hU⟩).symm
  · exact (fromSpec_projection hσ U).symm.trans (Category.id_comp _).symm
  · simp

/-- **The fppf quotient of a free action.** For a free action, under the Yoneda embedding into fppf
sheaves, the quotient projection `X ⟶ X/G` is the coequalizer of the two maps `∐_g X ⇉ X` given by
the identity and by `σ g` on the component of `g`. Thus `X/G` represents the fppf quotient sheaf of
`X` by `G`. -/
noncomputable def isColimitFppfYonedaCofork :
    IsColimit (Cofork.ofπ (Scheme.fppfTopology.yoneda.map (projection σ hσ))
        (by simp only [← Functor.map_comp, (isPullback_projection_of_free hσ hG).w]) :
      Cofork (Scheme.fppfTopology.yoneda.map (Sigma.desc fun _ : G ↦ 𝟙 X))
        (Scheme.fppfTopology.yoneda.map (Sigma.desc fun g : G ↦ (σ g).asIso.hom))) :=
  have := etale_projection_of_free hσ hG
  IsKernelPair.isColimitYonedaCofork Scheme.fppfTopology (isPullback_projection_of_free hσ hG)
    (Precoverage.generate_mem_toGrothendieck (Scheme.Hom.singleton_mem_fppfPrecoverage _))

end TauCeti.InvariantQuotient
