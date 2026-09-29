/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ProP
public import TauCeti.RepresentationTheory.Homological.ContCohomology.TrivialFp.Character
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.InvariantDual
import TauCeti.RepresentationTheory.Homological.ContCohomology.Inflation.Comparison
import TauCeti.RepresentationTheory.Homological.ContCohomology.Transgression

/-!
# Inflation from the maximal pro-p quotient of an absolute Galois group

For a field `K` and a prime `p`, pullback along the quotient
`G_K → G_K(p)` identifies degree-one continuous cohomology with trivial `𝔽_p` coefficients.
In degree two the same inflation map is injective. These are the low-degree comparison results
between the absolute Galois group and its maximal pro-`p` quotient.

The degree-one statement follows from the universal property of the maximal pro-`p` quotient,
because `H¹(-, 𝔽_p)` is the continuous `𝔽_p`-dual. For degree two, the five-term sequence reduces
the kernel of inflation to the transgression from `H¹(R, 𝔽_p)^{G_K}`, where `R` is the pro-`p`
kernel. The relative elementary abelian quotient `R / Rᵖ[R,G_K]` is trivial, so this invariant
group vanishes and inflation is injective.

## Main results

* `TauCeti.inflH1AbsoluteGaloisProP`: degree-one inflation from `G_K(p)` to `G_K` is a linear
  equivalence.
* `TauCeti.inflH2AbsoluteGaloisProPMap`: degree-two inflation as a linear map.
* `TauCeti.inflH2AbsoluteGaloisProP_injective`: degree-two inflation is injective.

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

variable (p : ℕ) [Fact p.Prime] (K : Type u) [Field K]

/-- The canonical continuous quotient map from an absolute Galois group to its maximal pro-`p`
quotient. -/
noncomputable abbrev absoluteGaloisGroupProPQuotientMap :
    Field.absoluteGaloisGroup K →ₜ* absoluteGaloisGroupProP p K :=
  ⟨maximalProPQuotient.mk p (Field.absoluteGaloisGroup K),
    maximalProPQuotient.continuous_mk p (Field.absoluteGaloisGroup K)⟩

/-- **Degree-one inflation from the maximal pro-`p` quotient.** Pullback along
`G_K → G_K(p)` identifies `H¹(G_K(p), 𝔽_p)` with `H¹(G_K, 𝔽_p)`. -/
noncomputable def inflH1AbsoluteGaloisProP :
    cohomFp p (absoluteGaloisGroupProP p K) 1 ≃ₗ[ZMod p]
      cohomFp p (Field.absoluteGaloisGroup K) 1 := by
  refine LinearEquiv.ofBijective
    (cohomFpMap p (absoluteGaloisGroupProPQuotientMap p K) 1).hom.toLinearMap ?_
  have hdual := maximalProPQuotient.continuousZModDualMap_bijective
    (p := p) (G := Field.absoluteGaloisGroup K)
  constructor
  · intro x y hxy
    apply (cohomFpLinearEquivContinuousZModDual p (absoluteGaloisGroupProP p K)).injective
    apply hdual.1
    rw [← cohomFpLinearEquivContinuousZModDual_cohomFpMap p
      (absoluteGaloisGroupProPQuotientMap p K) x,
      ← cohomFpLinearEquivContinuousZModDual_cohomFpMap p
        (absoluteGaloisGroupProPQuotientMap p K) y]
    exact congrArg (cohomFpLinearEquivContinuousZModDual p
      (Field.absoluteGaloisGroup K)) hxy
  · intro y
    obtain ⟨χ, hχ⟩ := hdual.2
      (cohomFpLinearEquivContinuousZModDual p (Field.absoluteGaloisGroup K) y)
    refine ⟨(cohomFpLinearEquivContinuousZModDual p
      (absoluteGaloisGroupProP p K)).symm χ, ?_⟩
    apply (cohomFpLinearEquivContinuousZModDual p (Field.absoluteGaloisGroup K)).injective
    change cohomFpLinearEquivContinuousZModDual p (Field.absoluteGaloisGroup K)
      (cohomFpMap p (absoluteGaloisGroupProPQuotientMap p K) 1
        ((cohomFpLinearEquivContinuousZModDual p
          (absoluteGaloisGroupProP p K)).symm χ)) = _
    rw [cohomFpLinearEquivContinuousZModDual_cohomFpMap,
      LinearEquiv.apply_symm_apply, hχ]

/-- The degree-one equivalence is the usual contravariant cohomology map along `G_K → G_K(p)`. -/
@[simp]
theorem inflH1AbsoluteGaloisProP_apply
    (x : cohomFp p (absoluteGaloisGroupProP p K) 1) :
    inflH1AbsoluteGaloisProP p K x =
      cohomFpMap p (absoluteGaloisGroupProPQuotientMap p K) 1 x :=
  by
    unfold inflH1AbsoluteGaloisProP
    exact LinearEquiv.ofBijective_apply _ x

/-- After identifying the quotient-invariants coefficient representation with trivial `𝔽_p`, the
degree-one equivalence is canonical inflation. -/
theorem inflH1AbsoluteGaloisProP_apply_eq_infl
    (x : cohomFp p (absoluteGaloisGroupProP p K) 1) :
    inflH1AbsoluteGaloisProP p K x =
      ContinuousCohomology.infl
        (proPKernel p (Field.absoluteGaloisGroup K))
        (trivialFp p (Field.absoluteGaloisGroup K)) 1
        (ContinuousCohomology.coeffMap
          (trivialFpQuotientToInvariantsIso p (Field.absoluteGaloisGroup K)
            (proPKernel p (Field.absoluteGaloisGroup K))).hom 1 x) := by
  rw [inflH1AbsoluteGaloisProP_apply]
  change cohomFpMap p
      (ContinuousMonoidHom.quotientMk (proPKernel p (Field.absoluteGaloisGroup K))) 1 x = _
  rw [← ConcreteCategory.comp_apply,
    coeffMap_trivialFpQuotientToInvariantsIso_hom_comp_infl]

omit [Fact p.Prime] in
private theorem subsingleton_h1ConjInvariants_proPKernel
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] {M : Type v} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [T1Space M] [DistribMulAction G M] [ContinuousSMul G M]
    (htriv : ∀ (g : G) (m : M), g • m = m) (hpM : ∀ m : M, p • m = 0) :
    Subsingleton (H1ConjInvariants G M (proPKernel p G)) := by
  let R : Subgroup G := proPKernel p G
  let _ : R.Normal := by dsimp [R]; infer_instance
  have hR : IsClosed (R : Set G) := isClosed_proPKernel
  have hstep : pLowerCentralStep p R = R := by
    simpa only [R] using pLowerCentralStep_proPKernel (p := p) (G := G)
  have htop : (pLowerCentralStep p R).subgroupOf R = ⊤ := by
    ext r
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_top, iff_true]
    rw [hstep]
    exact r.2
  let e := H1ConjInvariantsEquivOfSmulEqSelf htriv p hR hpM
  constructor
  intro x y
  apply e.injective
  apply Additive.toMul.injective
  apply ContinuousMonoidHom.ext
  intro q
  have hq : q = 1 := by
    obtain ⟨r, rfl⟩ := QuotientGroup.mk_surjective q
    rw [QuotientGroup.eq_one_iff, htop]
    exact Subgroup.mem_top r
  rw [hq, map_one, map_one]

omit [Fact p.Prime] in
private theorem explicitInfl2_proPKernel_injective
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] {M : Type v} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DiscreteTopology M] [DistribMulAction G M] [ContinuousSMul G M]
    (htriv : ∀ (g : G) (m : M), g • m = m) (hpM : ∀ m : M, p • m = 0) :
    Function.Injective (explicitInfl2 G M (proPKernel p G)) := by
  let hsub : Subsingleton (H1ConjInvariants G M (proPKernel p G)) :=
    subsingleton_h1ConjInvariants_proPKernel p htriv hpM
  rw [← AddMonoidHom.ker_eq_bot_iff, ← fiveTerm_exact_H2Q G M
    (proPKernel p G) (isClosed_proPKernel (p := p) (G := G))]
  rw [AddMonoidHom.range_eq_bot_iff]
  apply AddMonoidHom.ext
  intro x
  have hx : x = 0 := @Subsingleton.elim _ hsub _ _
  rw [hx, map_zero, AddMonoidHom.zero_apply]

omit [Fact p.Prime] in
private noncomputable def zmodEquivFixedPointsOfTrivialAction
    {G : Type u} [Group G] [DistribMulAction G (ZMod p)] (N : Subgroup G)
    (htriv : ∀ (g : G) (m : ZMod p), g • m = m) :
    ZMod p ≃+ FixedPoints.addSubgroup N (ZMod p) where
  toFun m := ⟨m, (FixedPoints.mem_addSubgroup N (ZMod p) m).2 fun n ↦ htriv n m⟩
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **Degree-two inflation from the maximal pro-`p` quotient.** This is explicit inflation,
conjugated by the standard identifications of trivial-coefficient continuous cohomology with its
low-degree cocycle model and by the identification of trivial coefficients with kernel-fixed
points. -/
noncomputable def inflH2AbsoluteGaloisProPMap :
    cohomFp p (absoluteGaloisGroupProP p K) 2 →ₗ[ZMod p]
      cohomFp p (Field.absoluteGaloisGroup K) 2 := by
  let G := Field.absoluteGaloisGroup K
  let R : Subgroup G := proPKernel p G
  let Q := G ⧸ R
  letI := trivialZModAction p G
  have htrivG : ∀ (g : G) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  haveI : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  letI := trivialZModAction p Q
  have htrivQ : ∀ (q : Q) (m : ZMod p), q • m = m := fun _ _ ↦ rfl
  haveI : ContinuousSMul Q (ZMod p) := ⟨continuous_snd⟩
  let eR := zmodEquivFixedPointsOfTrivialAction p R htrivG
  have hequiv : ∀ (q : Q) (m : ZMod p),
      eR ((ContinuousMulEquiv.refl Q) q • m) = q • eR m := by
    intro q m
    simp only [ContinuousMulEquiv.coe_refl, id_eq, htrivQ]
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [coe_quotient_smul_fixedPoints_addSubgroup]
      apply Subtype.ext
      rw [coe_smul_fixedPoints_addSubgroup, htrivG]
  let eQ := cohomFpAddEquivH2 p Q htrivQ
  let eFix := explicitMap2Equiv Q (ZMod p) Q (FixedPoints.addSubgroup R (ZMod p))
    (ContinuousMulEquiv.refl Q) eR continuous_of_discreteTopology
      continuous_of_discreteTopology hequiv
  let eG := cohomFpAddEquivH2 p G htrivG
  exact (eG.symm.toAddMonoidHom.comp
    ((explicitInfl2 G (ZMod p) R).comp
      (eFix.toAddMonoidHom.comp eQ.toAddMonoidHom))).toZModLinearMap p

/-- Degree-two inflation from `G_K(p)` to `G_K` is injective. The five-term sequence identifies
its kernel with the transgression range from `H¹(R, 𝔽_p)^{G_K}`. That group is zero because
`R / Rᵖ[R,G_K]` is trivial for the maximal pro-`p` kernel `R`. -/
theorem inflH2AbsoluteGaloisProP_injective :
    Function.Injective (inflH2AbsoluteGaloisProPMap p K) := by
  let G := Field.absoluteGaloisGroup K
  let R : Subgroup G := proPKernel p G
  let Q := G ⧸ R
  let _ := trivialZModAction p G
  have htrivG : ∀ (g : G) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  let _ := trivialZModAction p Q
  have htrivQ : ∀ (q : Q) (m : ZMod p), q • m = m := fun _ _ ↦ rfl
  have : ContinuousSMul Q (ZMod p) := ⟨continuous_snd⟩
  let eR := zmodEquivFixedPointsOfTrivialAction p R htrivG
  have hequiv : ∀ (q : Q) (m : ZMod p),
      eR ((ContinuousMulEquiv.refl Q) q • m) = q • eR m := by
    intro q m
    simp only [ContinuousMulEquiv.coe_refl, id_eq, htrivQ]
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [coe_quotient_smul_fixedPoints_addSubgroup]
      apply Subtype.ext
      rw [coe_smul_fixedPoints_addSubgroup, htrivG]
  let eQ := cohomFpAddEquivH2 p Q htrivQ
  let eFix := explicitMap2Equiv Q (ZMod p) Q (FixedPoints.addSubgroup R (ZMod p))
    (ContinuousMulEquiv.refl Q) eR continuous_of_discreteTopology
      continuous_of_discreteTopology hequiv
  let eG := cohomFpAddEquivH2 p G htrivG
  intro x y hxy
  apply eQ.injective
  apply eFix.injective
  apply explicitInfl2_proPKernel_injective (p := p) (G := G) (M := ZMod p) htrivG
    (fun m ↦ by rw [nsmul_eq_mul, ZMod.natCast_self, zero_mul])
  apply eG.symm.injective
  change inflH2AbsoluteGaloisProPMap p K x = inflH2AbsoluteGaloisProPMap p K y at hxy
  change eG.symm (explicitInfl2 G (ZMod p) R (eFix (eQ x))) =
    eG.symm (explicitInfl2 G (ZMod p) R (eFix (eQ y))) at hxy
  exact hxy

end TauCeti
