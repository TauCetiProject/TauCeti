/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Character
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Inflation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.InvariantDual
import TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression

/-!
# Inflation from the maximal pro-`p` quotient

For a profinite group `G` and a prime `p`, pullback along the quotient map `G → G(p)` onto the
maximal pro-`p` quotient identifies degree-one continuous cohomology with trivial `𝔽_p`
coefficients, and is injective in degree two. These are the low-degree comparison results between
a profinite group and its maximal pro-`p` quotient.

Together these let the low-degree `𝔽_p`-cohomology of `G(p)` be studied through `G`: classes in
`H¹(G, 𝔽_p)` are exactly the inflations of classes in `H¹(G(p), 𝔽_p)`, and a class in
`H²(G(p), 𝔽_p)` vanishes as soon as its inflation to `G` does. In particular `H²(G(p), 𝔽_p)`
embeds in `H²(G, 𝔽_p)`, so bounds on the latter bound the former.

## Main results

* `TauCeti.explicitInfl2_proPKernel_injective`: explicit degree-two inflation from `G ⧸ R` to `G`,
  for `R` the pro-`p` kernel, is injective for trivial coefficients killed by `p`.
* `TauCeti.inflH1MaximalProP`: degree-one inflation from `G(p)` to `G` is a linear equivalence.
* `TauCeti.inflH2MaximalProP_injective`: degree-two inflation from `G(p)` to `G` is injective.
* `TauCeti.inflH2MaximalProP_surjective_of_map₂_cupFp_eq_top`: degree-two inflation from `G(p)`
  to `G` is surjective when `H²(G, 𝔽_p)` is spanned by cup products of degree-one classes.

## References

* J.-P. Serre, *Galois Cohomology*, Chapter I, §2.6 and §4.3.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, I §1.6.
-/

public section

namespace TauCeti

open CategoryTheory ContCohomology

universe u v

-- Several imported descriptions derive the additive group of `ZMod p`; the ring structure is the
-- one used by the trivial-coefficient representation and its linear cohomology.
attribute [local instance 2000] Ring.toAddCommGroup

section Explicit

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Explicit degree-two inflation from the maximal pro-`p` quotient is injective.** For the
pro-`p` kernel `R` and trivial discrete coefficients `M` killed by `p`, the explicit inflation
`H²(G ⧸ R, M ^ R) → H²(G, M)` is injective. -/
theorem explicitInfl2_proPKernel_injective {M : Type v} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
    (htriv : ∀ (g : G) (m : M), g • m = m) (hpM : ∀ m : M, p • m = 0) :
    Function.Injective (explicitInfl2 G M (proPKernel p G)) := by
  have := subsingleton_h1ConjInvariants_proPKernel htriv hpM
  exact explicitInfl2_injective_of_subsingleton G M (proPKernel p G)
    (isClosed_proPKernel (p := p) (G := G))

end Explicit

variable (p : ℕ) [Fact p.Prime] (G : Type u) [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Degree-one inflation from the maximal pro-`p` quotient.** Pullback along `G → G(p)`
identifies `H¹(G(p), 𝔽_p)` with `H¹(G, 𝔽_p)`. -/
noncomputable def inflH1MaximalProP :
    cohomFp p (maximalProPQuotient p G) 1 ≃ₗ[ZMod p] cohomFp p G 1 :=
  LinearEquiv.ofBijective
    (cohomFpMap p (ContinuousMonoidHom.quotientMk (proPKernel p G)) 1).hom.toLinearMap <| by
    -- Read through the identifications of `H¹` with continuous characters, the map is the
    -- pullback of characters along the quotient map, which the universal property makes bijective.
    have h : ⇑(cohomFpMap p (ContinuousMonoidHom.quotientMk (proPKernel p G)) 1).hom.toLinearMap =
        (cohomFpLinearEquivContinuousZModDual p G).symm ∘
          (ContinuousMonoidHom.quotientMk (proPKernel p G)).continuousZModDualMap (n := p) ∘
            cohomFpLinearEquivContinuousZModDual p (maximalProPQuotient p G) :=
      funext fun x ↦ (LinearEquiv.eq_symm_apply _).2
        (cohomFpLinearEquivContinuousZModDual_cohomFpMap p _ x)
    rw [h]
    exact (cohomFpLinearEquivContinuousZModDual p G).symm.bijective.comp
      (maximalProPQuotient.continuousZModDualMap_bijective.comp
        (cohomFpLinearEquivContinuousZModDual p (maximalProPQuotient p G)).bijective)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- The degree-one equivalence is the usual contravariant cohomology map along `G → G(p)`. -/
@[simp]
theorem inflH1MaximalProP_apply (x : cohomFp p (maximalProPQuotient p G) 1) :
    inflH1MaximalProP p G x =
      cohomFpMap p (ContinuousMonoidHom.quotientMk (proPKernel p G)) 1 x :=
  LinearEquiv.ofBijective_apply _ x

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- After identifying the quotient-invariants coefficient representation with trivial `𝔽_p`, the
degree-one equivalence is canonical inflation. -/
theorem inflH1MaximalProP_apply_eq_infl (x : cohomFp p (maximalProPQuotient p G) 1) :
    inflH1MaximalProP p G x =
      ContinuousCohomology.infl (proPKernel p G) (trivialFp p G) 1
        (ContinuousCohomology.coeffMap
          (trivialFpQuotientToInvariantsIso p G (proPKernel p G)).hom 1 x) := by
  rw [inflH1MaximalProP_apply, ← ConcreteCategory.comp_apply,
    coeffMap_trivialFpQuotientToInvariantsIso_hom_comp_infl]

/-- **Degree-two inflation from the maximal pro-`p` quotient is injective.** The inflation map
`H²(G(p), 𝔽_p) → H²(G, 𝔽_p)` is injective. -/
theorem inflH2MaximalProP_injective :
    Function.Injective (cohomFpMap p (ContinuousMonoidHom.quotientMk (proPKernel p G)) 2) := by
  -- Transport to the explicit models and apply `explicitInfl2_proPKernel_injective`.
  let R : Subgroup G := proPKernel p G
  -- The explicit models need actions on `ZMod p`; the trivial ones are installed for the proof.
  let := trivialZModAction p G
  let := trivialZModAction p (G ⧸ R)
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  have : ContinuousSMul (G ⧸ R) (ZMod p) := ⟨continuous_snd⟩
  have htrivG : ∀ (g : G) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  have htrivQ : ∀ (q : G ⧸ R) (m : ZMod p), q • m = m := fun _ _ ↦ rfl
  let eR := zmodEquivFixedPointsOfTrivialAction p G R htrivG
  have hequiv : ∀ (q : G ⧸ R) (m : ZMod p),
      eR ((ContinuousMulEquiv.refl (G ⧸ R)) q • m) = q • eR m := by
    intro q m
    simp only [ContinuousMulEquiv.coe_refl, id_eq, htrivQ]
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [coe_quotient_smul_fixedPoints_addSubgroup]
      apply Subtype.ext
      rw [coe_smul_fixedPoints_addSubgroup, htrivG]
  let eFix := explicitMap2Equiv (G ⧸ R) (ZMod p) (G ⧸ R) (FixedPoints.addSubgroup R (ZMod p))
    (ContinuousMulEquiv.refl (G ⧸ R)) eR continuous_of_discreteTopology
      continuous_of_discreteTopology hequiv
  intro x y hxy
  apply (cohomFpAddEquivH2 p (G ⧸ R) htrivQ).injective
  apply eFix.injective
  apply explicitInfl2_proPKernel_injective (p := p) htrivG
    fun m ↦ by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [← cohomFpAddEquivH2_cohomFpMap_quotientMk_eq_explicitInfl2 p G R htrivG htrivQ
      eR (zmodEquivFixedPointsOfTrivialAction_apply p G R htrivG) hequiv,
    ← cohomFpAddEquivH2_cohomFpMap_quotientMk_eq_explicitInfl2 p G R htrivG htrivQ eR
      (zmodEquivFixedPointsOfTrivialAction_apply p G R htrivG) hequiv,
    hxy]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- **Degree-two inflation from the maximal pro-`p` quotient is surjective when `H²(G, 𝔽_p)` is
spanned by cup products.** Every class `a ⌣ b` with `a, b ∈ H¹(G, 𝔽_p)` is inflated from `G(p)`,
since degree-one inflation is bijective and inflation commutes with the cup product. -/
theorem inflH2MaximalProP_surjective_of_map₂_cupFp_eq_top
    (h : Submodule.map₂ (cupFp p G) ⊤ ⊤ = ⊤) :
    Function.Surjective (cohomFpMap p (ContinuousMonoidHom.quotientMk (proPKernel p G)) 2) := by
  have hle : Submodule.map₂ (cupFp p G) ⊤ ⊤ ≤
      LinearMap.range
        (cohomFpMap p (ContinuousMonoidHom.quotientMk (proPKernel p G)) 2).hom.toLinearMap := by
    rw [Submodule.map₂_le]
    rintro a - b -
    obtain ⟨a, rfl⟩ := (inflH1MaximalProP p G).surjective a
    obtain ⟨b, rfl⟩ := (inflH1MaximalProP p G).surjective b
    rw [inflH1MaximalProP_apply, inflH1MaximalProP_apply, ← cupFp_map]
    exact LinearMap.mem_range_self _ _
  intro x
  exact hle (h ▸ Submodule.mem_top)

end TauCeti
