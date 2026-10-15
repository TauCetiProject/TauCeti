/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.GroupCohomologyIso.Basic
import TauCeti.RepresentationTheory.Homological.GroupCohomology.Functoriality

/-!
# Coefficient maps in the explicit-to-algebraic cohomology comparison

For a discrete group, the comparison `explicitH2AddEquivGroupCohomology` commutes with
continuous equivariant coefficient maps. The coefficient modules need not be discrete, and
the representation may be over any commutative ring. The comparison therefore transfers an
algebraic isomorphism on second cohomology to the explicit continuous coefficient map.

This is useful for maps between compact extension kernels: an algebraic calculation of the
cohomology of a relation-module map can be used in the continuous extension-lifting criterion,
without replacing that map by an independently chosen isomorphism of cohomology groups.
The group and the additive coefficient coordinates may both be changed by the comparison.

## Main results

* `TauCeti.ContCohomology.explicitH2AddEquivGroupCohomology_explicitCoeff2`: the naturality square.
* `TauCeti.ContCohomology.explicitCoeff2_bijective_iff`: bijectivity is preserved and reflected.
* `TauCeti.ContCohomology.explicitCoeff2_bijective_of_isIso`: transfer an algebraic isomorphism.

The construction uses the cocycle dictionary in `GroupCohomologyIso/Basic.lean` and Mathlib's
`groupCohomology.H2π_comp_map`.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Chapter I, §2 and the proof of (7.4.1).
-/

public section

open CategoryTheory groupCohomology

namespace TauCeti.ContCohomology

universe u v v' w

variable {G : Type u} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  {M : Type v} {N : Type v'}
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M]
  [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [DistribMulAction G N] [ContinuousSMul G N]
  {k H : Type w} [CommRing k] [Group H] {B C : Rep k H}
  (φ : G ≃* H) (ψ : M ≃+ B) (χ : N ≃+ C)
  (hψ : ∀ g m, ψ (g • m) = B.ρ (φ g) (ψ m))
  (hχ : ∀ g n, χ (g • n) = C.ρ (φ g) (χ n))
  (f : M →+[G] N) (hf : Continuous f) (F : B ⟶ C)
  (hF : ∀ m, χ (f m) = F.hom (ψ m))

include hF

/-- The explicit-to-algebraic comparison in degree two commutes with a continuous coefficient
map, read in any compatible additive coordinates and over any coefficient ring. -/
theorem explicitH2AddEquivGroupCohomology_explicitCoeff2 (x : H2 G M) :
    explicitH2AddEquivGroupCohomology φ χ hχ (explicitCoeff2 G M f hf x) =
      groupCohomology.map (MonoidHom.id H) F 2
        (explicitH2AddEquivGroupCohomology φ ψ hψ x) := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    let c : cocycles₂ B := ⟨fun h ↦ ψ ((z : G × G → M) (φ.symm h.1, φ.symm h.2)), by
      refine (mem_cocycles₂_iff _).mpr fun a b d ↦ ?_
      have hz := (mem_Z2_iff.mp z.2).2 (φ.symm a) (φ.symm b) (φ.symm d)
      have ha := hψ (φ.symm a) ((z : G × G → M) (φ.symm b, φ.symm d))
      simpa only [map_mul, map_add, φ.apply_symm_apply, ha] using congrArg ψ hz⟩
    rw [explicitCoeff2_mk,
      explicitH2AddEquivGroupCohomology_mk φ ψ hψ z c (fun _ ↦ rfl)]
    have hmap := ConcreteCategory.congr_hom (H2π_comp_map (MonoidHom.id H) F) c
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at hmap
    rw [hmap]
    apply explicitH2AddEquivGroupCohomology_mk
    intro h
    rw [TauCeti.groupCohomology.mapCocycles₂_apply]
    -- Use the pointwise pullback equation as a term: rewriting under the coefficient
    -- equivalence would make a motive with the unreduced identity-action proof.
    have hcoef := cocyclesMap2_apply G M G N (ContinuousMonoidHom.id G) f hf
      (fun g m ↦ f.map_smul g m) z (φ.symm h.1) (φ.symm h.2)
    exact ((congrArg χ hcoef).trans (hF _)).symm

include hψ hχ hF

/-- An explicit continuous coefficient map is bijective on second cohomology exactly when the
same coefficient map in algebraic representation coordinates is bijective. -/
theorem explicitCoeff2_bijective_iff :
    Function.Bijective (explicitCoeff2 G M f hf) ↔
      Function.Bijective (groupCohomology.map (MonoidHom.id H) F 2) := by
  let eM := explicitH2AddEquivGroupCohomology φ ψ hψ
  let eN := explicitH2AddEquivGroupCohomology φ χ hχ
  have hcomp : eN ∘ explicitCoeff2 G M f hf =
      groupCohomology.map (MonoidHom.id H) F 2 ∘ eM :=
    funext (explicitH2AddEquivGroupCohomology_explicitCoeff2 φ ψ χ hψ hχ f hf F hF)
  rw [← Function.Bijective.of_comp_iff' eN.bijective, hcomp]
  exact Function.Bijective.of_comp_iff _ eM.bijective

/-- An algebraic coefficient map that is an isomorphism on second cohomology gives a bijective
explicit continuous coefficient map in compatible coordinates. -/
theorem explicitCoeff2_bijective_of_isIso
    [IsIso (groupCohomology.map (MonoidHom.id H) F 2)] :
    Function.Bijective (explicitCoeff2 G M f hf) :=
  (explicitCoeff2_bijective_iff φ ψ χ hψ hχ f hf F hF).mpr
    (ConcreteCategory.bijective_of_isIso _)

end TauCeti.ContCohomology
