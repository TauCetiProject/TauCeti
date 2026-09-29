/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Character
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.InvariantDual
import TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression

/-!
# Inflation from the maximal pro-`p` quotient

For a profinite group `G` and a prime `p`, pullback along the quotient map `G → G(p)` onto the
maximal pro-`p` quotient identifies degree-one continuous cohomology with trivial `𝔽_p`
coefficients, and is injective in degree two. These are the low-degree comparison results between
a profinite group and its maximal pro-`p` quotient.

The degree-one statement follows from the universal property of the maximal pro-`p` quotient,
because `H¹(-, 𝔽_p)` is the continuous `𝔽_p`-dual. For degree two, the five-term sequence reduces
the kernel of inflation to the transgression from `H¹(R, 𝔽_p)^G`, where `R` is the pro-`p` kernel.
The relative elementary abelian quotient `R / Rᵖ[R,G]` is trivial, so this invariant group
vanishes and inflation is injective.

## Main results

* `TauCeti.explicitInfl2_proPKernel_injective`: explicit degree-two inflation from `G ⧸ R` to `G`,
  for `R` the pro-`p` kernel, is injective for trivial coefficients killed by `p`.
* `TauCeti.inflH1MaximalProP`: degree-one inflation from `G(p)` to `G` is a linear equivalence.
* `TauCeti.inflH2MaximalProP_injective`: degree-two inflation from `G(p)` to `G` is injective.

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
pro-`p` kernel `R` and trivial discrete coefficients `M` killed by `p`, the five-term sequence
identifies the kernel of `H²(G ⧸ R, M ^ R) → H²(G, M)` with the image of the transgression from
`H¹(R, M)^G`, which vanishes by `subsingleton_h1ConjInvariants_proPKernel`. -/
theorem explicitInfl2_proPKernel_injective {M : Type v} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
    (htriv : ∀ (g : G) (m : M), g • m = m) (hpM : ∀ m : M, p • m = 0) :
    Function.Injective (explicitInfl2 G M (proPKernel p G)) := by
  have := subsingleton_h1ConjInvariants_proPKernel htriv hpM
  rw [← AddMonoidHom.ker_eq_bot_iff, ← fiveTerm_exact_H2Q G M
    (proPKernel p G) (isClosed_proPKernel (p := p) (G := G)), AddMonoidHom.range_eq_bot_iff]
  exact AddMonoidHom.ext fun x ↦ by rw [Subsingleton.elim x 0, map_zero, AddMonoidHom.zero_apply]

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

omit [Fact p.Prime] in
/-- For a trivial action, `ZMod p` is its own subgroup of `N`-fixed points. -/
private noncomputable def zmodEquivFixedPointsOfTrivialAction
    {G : Type u} [Group G] [DistribMulAction G (ZMod p)] (N : Subgroup G)
    (htriv : ∀ (g : G) (m : ZMod p), g • m = m) :
    ZMod p ≃+ FixedPoints.addSubgroup N (ZMod p) where
  toFun m := ⟨m, (FixedPoints.mem_addSubgroup N (ZMod p) m).2 fun n ↦ htriv n m⟩
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **Degree-two inflation from the maximal pro-`p` quotient is injective.** The five-term sequence
identifies the kernel of `H²(G(p), 𝔽_p) → H²(G, 𝔽_p)` with the transgression range from
`H¹(R, 𝔽_p)^G`, which is zero because `R / Rᵖ[R,G]` is trivial for the pro-`p` kernel `R`. -/
theorem inflH2MaximalProP_injective :
    Function.Injective (cohomFpMap p (ContinuousMonoidHom.quotientMk (proPKernel p G)) 2) := by
  let R : Subgroup G := proPKernel p G
  -- The explicit models need actions on `ZMod p`; the trivial ones are installed for the proof.
  let := trivialZModAction p G
  let := trivialZModAction p (G ⧸ R)
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  have : ContinuousSMul (G ⧸ R) (ZMod p) := ⟨continuous_snd⟩
  have htrivG : ∀ (g : G) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  have htrivQ : ∀ (q : G ⧸ R) (m : ZMod p), q • m = m := fun _ _ ↦ rfl
  let eR := zmodEquivFixedPointsOfTrivialAction p R htrivG
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
  -- On the explicit models, the cohomology map is explicit inflation after identifying `ZMod p`
  -- with its `R`-fixed points.
  have hmap (x : cohomFp p (G ⧸ R) 2) :
      cohomFpAddEquivH2 p G htrivG
          (cohomFpMap p (ContinuousMonoidHom.quotientMk R) 2 x) =
        explicitInfl2 G (ZMod p) R (eFix (cohomFpAddEquivH2 p (G ⧸ R) htrivQ x)) := by
    rw [cohomFpAddEquivH2_cohomFpMap p (G ⧸ R) htrivQ htrivG]
    generalize cohomFpAddEquivH2 p (G ⧸ R) htrivQ x = y
    induction y using QuotientAddGroup.induction_on with
    | H c =>
      -- `explicitMap2_mk` is applied as a term to `eFix`: `explicitMap2Equiv` states the continuity
      -- of the coefficient map at the equivalence, which `rw` does not identify with its coercion.
      rw [explicitMap2_mk, explicitMap2Equiv_apply]
      -- `explicitMap2_mk` is applied as a term: `explicitMap2Equiv` states the continuity of the
      -- coefficient map at the equivalence, which `rw` does not identify with its coercion.
      refine Eq.trans ?_ (congrArg (explicitInfl2 G (ZMod p) R)
        (explicitMap2_mk (G ⧸ R) (ZMod p) (G ⧸ R) _ _ _ _ _ c)).symm
      rw [explicitInfl2_mk]
      -- Both cocycles read `c` at the images of the two arguments in `G ⧸ R`.
      refine congrArg _ (Subtype.ext (funext fun ⟨g, h⟩ ↦ ?_))
      rw [cocyclesMap2_apply, cocyclesMap2_apply]
      exact (congrArg Subtype.val (cocyclesMap2_apply (G ⧸ R) (ZMod p) (G ⧸ R) _
        (ContinuousMulEquiv.refl (G ⧸ R)) eR.toAddMonoidHom _ hequiv c _ _)).symm
  intro x y hxy
  apply (cohomFpAddEquivH2 p (G ⧸ R) htrivQ).injective
  apply eFix.injective
  apply explicitInfl2_proPKernel_injective (p := p) htrivG
    fun m ↦ by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  rw [← hmap, ← hmap, hxy]

end TauCeti
