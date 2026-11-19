/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import TauCeti.AlgebraicGeometry.Quotient.FiniteGroup.Torsor
public import TauCeti.CategoryTheory.Sites.KernelPair

/-!
# The affine quotient by a free finite group represents the fppf quotient sheaf

Let a finite group `G` act on a commutative ring `A`, freely in the scheme-theoretic sense: for
every `g ≠ 1`, the elements `g • a - a` generate the unit ideal of `A`. Write `X = Spec A` and
`π : X ⟶ X/G = Spec Aᴳ` for the projection to the affine invariant quotient. This file shows that
`X/G` represents the fppf quotient sheaf of `X` by `G`.

The fppf quotient sheaf is the coequalizer, in fppf sheaves, of the action and the projection
`G × X ⇉ X`; for the constant group `G` the source is the disjoint union `∐_g X`, with the identity
and `specComap A G g` on the component of `g`. Under the Yoneda embedding into fppf sheaves,
`π` is this coequalizer (`TauCeti.AffineInvariantQuotient.isColimitFppfYonedaCofork`).
Consequently, a morphism from `X` to an fppf sheaf which is invariant under every
`specComap A G g` factors uniquely through `X/G`
(`TauCeti.AffineInvariantQuotient.existsUnique_fppfYoneda_comp_eq`).

The projection `π` is étale (`TauCeti.AffineInvariantQuotient.etale_projection`) and surjective,
so it is an fppf covering, and `∐_g X ⇉ X` is its kernel pair
(`TauCeti.AffineInvariantQuotient.isPullback_of_free`). The coequalizer statement is therefore the
general fact `CategoryTheory.IsKernelPair.isColimitYonedaCofork`. For the invariant form, an
fppf sheaf is separated for the cover of `∐_g X` by its components.

## Main definitions

* `TauCeti.AffineInvariantQuotient.isColimitFppfYonedaCofork`: `X/G` is the coequalizer of
  `∐_g X ⇉ X` in fppf sheaves.

## Main results

* `TauCeti.AffineInvariantQuotient.existsUnique_fppfYoneda_comp_eq`: a `G`-invariant morphism
  from `X` to an fppf sheaf factors uniquely through `X/G`.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé IV, §3, and Exposé V, §4.
-/

public section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace TauCeti.AffineInvariantQuotient

universe u v

variable (A : Type u) (G : Type v) [CommRing A] [Group G] [MulSemiringAction G A] [Finite G]

/-- **The fppf quotient of a free finite-group action.** If every `g ≠ 1` acts on `Spec A` with
empty scheme-theoretic fixed locus, then under the Yoneda embedding into fppf sheaves, the
projection `Spec A ⟶ Spec Aᴳ` is the coequalizer of the two maps `∐_g Spec A ⇉ Spec A` given by
the identity and by `specComap A G g` on the component of `g`. Thus `Spec Aᴳ` represents the fppf
quotient sheaf of `Spec A` by `G`. -/
noncomputable def isColimitFppfYonedaCofork
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤) :
    IsColimit (Cofork.ofπ (Scheme.fppfTopology.yoneda.map (projection A G))
        (by simp only [← Functor.map_comp, (isPullback_of_free A G hG).w]) :
      Cofork (Scheme.fppfTopology.yoneda.map (Sigma.desc fun _ : G ↦ 𝟙 (Spec (CommRingCat.of A))))
        (Scheme.fppfTopology.yoneda.map (Sigma.desc (specComap A G)))) :=
  have := etale_projection hG
  IsKernelPair.isColimitYonedaCofork Scheme.fppfTopology (isPullback_of_free A G hG)
    (Precoverage.generate_mem_toGrothendieck (projection A G).singleton_mem_fppfPrecoverage)

/-- **The universal property of the fppf quotient by a free finite-group action.** If every
`g ≠ 1` acts on `Spec A` with empty scheme-theoretic fixed locus, then every morphism from
`Spec A` to an fppf sheaf which is invariant under every `specComap A G g` factors uniquely
through the projection `Spec A ⟶ Spec Aᴳ`. -/
theorem existsUnique_fppfYoneda_comp_eq
    (hG : ∀ g : G, g ≠ 1 → Ideal.span (Set.range fun a : A ↦ g • a - a) = ⊤)
    {F : Sheaf Scheme.fppfTopology (Type u)}
    (f : Scheme.fppfTopology.yoneda.obj (Spec (CommRingCat.of A)) ⟶ F)
    (hf : ∀ g : G, Scheme.fppfTopology.yoneda.map (specComap A G g) ≫ f = f) :
    ∃! l : Scheme.fppfTopology.yoneda.obj (quotient A G) ⟶ F,
      Scheme.fppfTopology.yoneda.map (projection A G) ≫ l = f := by
  refine Cofork.IsColimit.existsUnique (isColimitFppfYonedaCofork A G hG) f ?_
  -- an fppf sheaf is separated for the cover of `∐_g Spec A` by its components
  have hsep : Presieve.IsSeparatedFor F.obj
      (Presieve.ofArrows _ (Sigma.ι fun _ : G ↦ Spec (CommRingCat.of A))) :=
    (((isSheaf_iff_isSheaf_of_type _ _).mp F.property).isSheafFor _
      (Precoverage.generate_mem_toGrothendieck
        (Scheme.zariskiPrecoverage_le_fppfPrecoverage _ (sigmaOpenCover _).mem₀))).isSeparatedFor
  apply Scheme.fppfTopology.yonedaEquiv.injective
  rw [← GrothendieckTopology.yonedaEquiv_naturality,
    ← GrothendieckTopology.yonedaEquiv_naturality]
  refine hsep.ext fun Z i ⟨g⟩ ↦ ?_
  -- restrict along the component of `g`, then use Yoneda naturality and invariance
  simp only [← Functor.map_comp_apply, ← op_comp, Sigma.ι_comp_desc, op_id,
    Functor.map_id_apply]
  rw [GrothendieckTopology.yonedaEquiv_naturality, hf]

end TauCeti.AffineInvariantQuotient
