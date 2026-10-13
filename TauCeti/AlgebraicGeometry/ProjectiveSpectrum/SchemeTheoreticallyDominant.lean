/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import TauCeti.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic

/-!
# Scheme-theoretically dense standard opens of `Proj`

For an `ℕ`-graded ring `A` and a homogeneous element `g` of positive degree that is a
nonzerodivisor of `A`, the standard open `D₊(g)` is scheme-theoretically dense in `Proj A`: the
open immersion `Proj.awayι 𝒜 g : Spec A_{(g)} ⟶ Proj A` is scheme-theoretically dominant.

On the standard chart `Spec A_{(f)}` of `Proj A`, the open `D₊(g)` is the spectrum of `A_{(fg)}`,
and the restriction `A_{(f)} → A_{(fg)}` is injective because `g` is a nonzerodivisor.

## Main results

* `AlgebraicGeometry.Proj.isSchemeTheoreticallyDominant_awayι`: for a homogeneous nonzerodivisor
  `g` of positive degree, the open immersion `Proj.awayι 𝒜 g` is scheme-theoretically dominant.

## References

* The Stacks Project, Tag 01RA (scheme theoretic closure and density), especially Lemma 29.7.5
  (Tag 01RE).

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/PoleFiltration.lean`, declarations
`spec_hom_ext_of_nonZeroDivisor` and `projModel_hom_ext_of_affine`. The first is the affine case:
by an equalizer argument, two morphisms from an affine scheme to a separated scheme that agree
after inverting a nonzerodivisor of its coordinate ring are equal. The second treats the projective
Weierstrass model only: on each standard chart `D₊(Xⱼ)` it presents `A_{(XⱼZ)}` as the localization
of `A_{(Xⱼ)}` at a nonzerodivisor and applies the first, so that two morphisms to a separated
scheme that agree on `D₊(Z)` are equal. Here the conclusion is Mathlib's
`AlgebraicGeometry.IsSchemeTheoreticallyDominant`, from which that extension statement follows by
`TauCeti.ext_of_isSchemeTheoreticallyDominant`. The statement for `Proj` of an arbitrary graded
ring, with the hypothesis that `g` is a nonzerodivisor of `A` rather than of each chart, is not in
the source.
-/

public section

open CategoryTheory Limits HomogeneousLocalization

namespace AlgebraicGeometry.Proj

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

-- A morphism to `Proj A` is scheme-theoretically dominant if its base change to each standard
-- affine chart `Spec A_{(f)}` is. The member of `Proj.affineOpenCover` at `⟨d, f⟩` is, by
-- definition, the chart `awayι 𝒜 f`, and base change to it is the second projection of the
-- pullback.
private theorem isSchemeTheoreticallyDominant_of_forall_pullbackSnd_awayι {X : Scheme}
    (φ : X ⟶ Proj 𝒜)
    (h : ∀ {d : ℕ} (hd : 0 < d) {f : A} (hf : f ∈ 𝒜 d),
      IsSchemeTheoreticallyDominant (pullback.snd φ (awayι 𝒜 f hf hd))) :
    IsSchemeTheoreticallyDominant φ :=
  .of_openCover (affineOpenCover 𝒜).openCover fun i ↦ h i.1.2 i.2.2

/-- For a homogeneous element `g` of positive degree that is a nonzerodivisor of the graded ring
`A`, the standard open `D₊(g)` is scheme-theoretically dense in `Proj A`: the open immersion
`Proj.awayι 𝒜 g : Spec A_{(g)} ⟶ Proj A` is scheme-theoretically dominant. -/
theorem isSchemeTheoreticallyDominant_awayι {g : A} {m : ℕ} (g_deg : g ∈ 𝒜 m) (hm : 0 < m)
    (hg : g ∈ nonZeroDivisors A) : IsSchemeTheoreticallyDominant (awayι 𝒜 g g_deg hm) := by
  refine isSchemeTheoreticallyDominant_of_forall_pullbackSnd_awayι 𝒜 _ fun {d} hd {f} hf ↦ ?_
  -- the restriction `A_{(f)} → A_{(gf)}` is injective
  have : IsSchemeTheoreticallyDominant
      (Spec.map (CommRingCat.ofHom (awayMap 𝒜 g_deg (mul_comm g f)))) := by
    rw [isSchemeTheoreticallyDominant_SpecMap_iff, CommRingCat.hom_ofHom]
    exact awayMap_injective g_deg (mul_comm g f) hg
  -- the base change of `awayι 𝒜 g` to the chart `Spec A_{(f)}` is `Spec` of that restriction, up
  -- to the isomorphism `pullbackAwayιIso`; an isomorphism is scheme-theoretically dominant, and so
  -- is a composition of two such morphisms
  rw [← pullbackAwayιIso_hom_SpecMap_awayMap_right 𝒜 g_deg hm hf hd rfl]
  infer_instance

end AlgebraicGeometry.Proj
