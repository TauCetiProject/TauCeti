/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologyComparison
public import TauCeti.RepresentationTheory.Homological.ContCohomology.ContinuousCohomologyIso
public import TauCeti.RepresentationTheory.Homological.ContCohomology.HomologySequence

/-!
# The explicit and canonical connecting maps agree

A short exact sequence `0 → A → B → C → 0` of discrete modules over a compact group `G` has two
connecting maps in low degrees: the explicit ones
`TauCeti.ContCohomology.DiscreteShortExact.explicitDelta0 : H⁰(G, C) → H¹(G, A)` and
`explicitDelta1 : H¹(G, C) → H²(G, A)`, defined on inhomogeneous cochains, and the canonical
`TauCeti.ContCohomology.DiscreteShortExact.delta`, defined in every degree by the snake lemma on
Mathlib's homogeneous cochains. This file proves that the comparison isomorphisms
`explicitH0IsoContinuousCohomology`, `explicitH1IsoContinuousCohomology` and
`explicitH2IsoContinuousCohomology` carry the first to the second in degrees zero and one:

```text
H⁰(G, C) --explicitDelta0--> H¹(G, A)        H¹(G, C) --explicitDelta1--> H²(G, A)
    |                            |                |                            |
    ≅                            ≅                ≅                            ≅
    v                            v                v                            v
H⁰_cont(G, C) ----delta 0--> H¹_cont(G, A)   H¹_cont(G, C) ----delta 1--> H²_cont(G, A)
```

So a statement about the long exact sequence proved on explicit cocycles, such as the Kummer
description of the connecting map, is a statement about the canonical long exact sequence.

## Main results

* `TauCeti.ContCohomology.DiscreteShortExact.explicitIso_delta0`: the degree-zero square.
* `TauCeti.ContCohomology.DiscreteShortExact.explicitIso_delta1`: the degree-one square.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  (1.3.2) for the long exact sequence, and Ch. I, §2 for the comparison of inhomogeneous and
  homogeneous cochains.
-/

public section

open CategoryTheory

namespace TauCeti.ContCohomology.DiscreteShortExact

open _root_.ContinuousCohomology _root_.TauCeti.ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

variable [CompactSpace G]
  {A : Type u} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction G A]
  [ContinuousSMul G A]
  {B : Type u} [AddCommGroup B] [TopologicalSpace B] [DiscreteTopology B] [DistribMulAction G B]
  [ContinuousSMul G B]
  {C : Type u} [AddCommGroup C] [TopologicalSpace C] [DiscreteTopology C] [DistribMulAction G C]
  [ContinuousSMul G C]
  (S : DiscreteShortExact G A B C)

-- The two `simp` lemmas below state their left-hand sides through `dsimp% only`, as the transport
-- lemmas of `ComparisonDegreeTwo.lean` do: the carriers of the cohomology objects in the implicit
-- arguments of the applied morphism are beta-reduced by `simp` before it looks a term up, so the
-- plain form is never found.
/-- **The explicit and canonical connecting maps agree in degree zero.** Under the comparisons of
`H⁰` and `H¹` with Mathlib's continuous cohomology, the explicit connecting map
`explicitDelta0 : H⁰(G, C) → H¹(G, A)` is the canonical `delta 0`. -/
@[simp]
theorem explicitIso_delta0 (x : H0 G C) :
    (dsimp% only (S.delta 0).hom ((explicitH0IsoContinuousCohomology G C).hom x)) =
      (explicitH1IsoContinuousCohomology G A).hom
        ((discreteH1Equiv G A).symm (S.explicitDelta0 x)) := by
  -- A preimage `b` of `x` in `B`, and the cocycle `a` on `A` with `incl ∘ a = d⁰ b`.
  obtain ⟨b, hb⟩ := S.proj_surjective (x : C)
  obtain ⟨a, -, hab⟩ := S.exists_continuous_incl_comp_eq (continuous_d0_apply (M := B) b)
    (proj_d0_eq_zero (hb ▸ x.2))
  have ha : a ∈ Z1 G A := S.mem_Z1_of_incl_comp_eq_d0 fun g ↦ (hab g).trans (d0_apply b g)
  -- A canonical `0`-cocycle representing `x`: it is the homogeneous cochain `g ↦ g • x`.
  obtain ⟨z₃, hz₃⟩ := HomologicalComplex.homologyπ_surjective
    (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)) 0
    ((explicitH0IsoContinuousCohomology G C).hom x)
  have hz₃' : (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles 0 z₃ =
      cochainEquiv0 G C x := by
    rw [← (cochainEquiv0 G C).apply_symm_apply
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles 0 z₃)]
    congr 1
    rw [cochainEquiv0_symm_apply, ← coe_zeroIso_hom_π, hz₃,
      explicitH0IsoContinuousCohomology_hom_eq_degreeZeroClass]
    exact coe_zeroIso_hom_degreeZeroClass _ _
  -- The homogeneous form of `b` lifts it, and the homogeneous form of `a` lies over `d⁰ b`.
  have hx₂ : (S.continuousCochainsShortExact.g.f 0).hom (cochainEquiv0 G B b) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles 0 z₃ := by
    rw [hz₃', ← hb]
    have h := cochainEquiv0_naturality G B G C (ContinuousMonoidHom.id G) S.proj
      S.proj_equivariant b
    rw [cochainsMap_ofDiscreteModulePair_id] at h
    exact h
  have hx₁ : (S.continuousCochainsShortExact.f.f 1).hom
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles 1
        (cocycleEquiv1 G A ⟨a, ha⟩)) =
      (S.continuousCochainsShortExact.X₂.d 0 1).hom (cochainEquiv0 G B b) := by
    refine (congrArg (S.continuousCochainsShortExact.f.f 1).hom
      (iCycles_cocycleEquiv1 G A ⟨a, ha⟩)).trans ?_
    have h := cochainEquiv1_naturality G A G B (ContinuousMonoidHom.id G) S.incl
      S.incl_equivariant ⟨a, Z1_le_C1 G A ha⟩
    rw [cochainsMap_ofDiscreteModulePair_id] at h
    refine h.trans (Eq.trans ?_ (d_cochainEquiv0 G B b).symm)
    congr 2
    exact funext fun g ↦ (cochainsMap1_apply _ _ _ g).trans (hab g)
  calc (S.delta 0).hom ((explicitH0IsoContinuousCohomology G C).hom x)
      _ = (S.delta 0).hom (π (ofDiscreteModule ℤ G C) 0 z₃) := congrArg _ hz₃.symm
      _ = π (ofDiscreteModule ℤ G A) 1 (cocycleEquiv1 G A ⟨a, ha⟩) :=
        S.delta_apply 0 z₃ _ hx₂ _ hx₁
      _ = explicitH1AddEquivContinuousCohomology G A (⟨a, ha⟩ : Z1 G A) :=
        (explicitH1AddEquivContinuousCohomology_apply G A ⟨a, ha⟩).symm
      _ = _ := by
        rw [S.explicitDelta0_apply x hb ha fun g ↦ (hab g).trans (d0_apply b g),
          explicitH1IsoContinuousCohomology_hom_apply, AddEquiv.apply_symm_apply,
          QuotientAddGroup.mk'_apply]

/-- **The explicit and canonical connecting maps agree in degree one.** Under the comparisons of
`H¹` and `H²` with Mathlib's continuous cohomology, the explicit connecting map
`explicitDelta1 : H¹(G, C) → H²(G, A)` is the canonical `delta 1`. -/
@[simp]
theorem explicitIso_delta1 (x : DiscreteH1 G C) :
    (dsimp% only (S.delta 1).hom ((explicitH1IsoContinuousCohomology G C).hom x)) =
      (explicitH2IsoContinuousCohomology G A).hom
        ((discreteH2Equiv G A).symm (S.explicitDelta1 (discreteH1Equiv G C x))) := by
  -- A cocycle `f` representing `x`, a continuous lift `e` of `f` to `B`, and the cocycle `a` on
  -- `A` with `incl ∘ a = d¹ e`.
  obtain ⟨f, hf⟩ := QuotientAddGroup.mk_surjective (discreteH1Equiv G C x)
  obtain ⟨hfc, hfcoc⟩ := mem_Z1_iff.1 f.2
  obtain ⟨e, hec, he⟩ := exists_continuous_lift S.proj_surjective hfc
  obtain ⟨a, -, hae⟩ := S.exists_continuous_incl_comp_eq (continuous_d1_apply hec)
    (proj_d1_eq_zero he hfcoc)
  have hae' (g h : G) : S.incl (a (g, h)) = g • e h - e (g * h) + e g :=
    (hae (g, h)).trans (d1_apply e g h)
  have ha : a ∈ Z2 G A := S.mem_Z2_of_incl_comp_eq_d1 hec hae'
  have hec' : e ∈ C1 G B := mem_C1_iff.2 hec
  -- The homogeneous form of `e` lifts the canonical cocycle of `f`, and the homogeneous form of
  -- `a` lies over the differential of that lift.
  have hx₂ : (S.continuousCochainsShortExact.g.f 1).hom (cochainEquiv1 G B ⟨e, hec'⟩) =
      (TopRep.homogeneousCochains (ofDiscreteModule ℤ G C)).iCycles 1 (cocycleEquiv1 G C f) := by
    have h := cochainEquiv1_naturality G B G C (ContinuousMonoidHom.id G) S.proj
      S.proj_equivariant ⟨e, hec'⟩
    rw [cochainsMap_ofDiscreteModulePair_id] at h
    refine h.trans (Eq.trans ?_ (iCycles_cocycleEquiv1 G C f).symm)
    congr 2
    exact funext fun g ↦ (cochainsMap1_apply _ _ _ g).trans (he g)
  have hx₁ : (S.continuousCochainsShortExact.f.f 2).hom
      ((TopRep.homogeneousCochains (ofDiscreteModule ℤ G A)).iCycles 2
        (cocycleEquiv2 G A ⟨a, ha⟩)) =
      (S.continuousCochainsShortExact.X₂.d 1 2).hom (cochainEquiv1 G B ⟨e, hec'⟩) := by
    refine (congrArg (S.continuousCochainsShortExact.f.f 2).hom
      (iCycles_cocycleEquiv2 G A ⟨a, ha⟩)).trans ?_
    have h := cochainEquiv2_naturality G A G B (ContinuousMonoidHom.id G) S.incl
      S.incl_equivariant ⟨a, Z2_le_C2 G A ha⟩
    rw [cochainsMap_ofDiscreteModulePair_id] at h
    refine h.trans (Eq.trans ?_ (d_cochainEquiv1 G B ⟨e, hec'⟩).symm)
    congr 2
    exact funext fun p ↦ (cochainsMap2_apply _ _ _ p.1 p.2).trans (hae p)
  calc (S.delta 1).hom ((explicitH1IsoContinuousCohomology G C).hom x)
      _ = (S.delta 1).hom (π (ofDiscreteModule ℤ G C) 1 (cocycleEquiv1 G C f)) := by
        rw [explicitH1IsoContinuousCohomology_hom_apply, ← hf]
        exact congrArg _ (explicitH1AddEquivContinuousCohomology_apply G C f)
      _ = π (ofDiscreteModule ℤ G A) 2 (cocycleEquiv2 G A ⟨a, ha⟩) :=
        S.delta_apply 1 _ _ hx₂ _ hx₁
      _ = explicitH2AddEquivContinuousCohomology G A (⟨a, ha⟩ : Z2 G A) :=
        (explicitH2AddEquivContinuousCohomology_apply G A ⟨a, ha⟩).symm
      _ = _ := by
        have hδ := S.explicitDelta1_apply f hec he ha hae'
        rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.mk'_apply, hf] at hδ
        rw [hδ, explicitH2IsoContinuousCohomology_hom_apply, AddEquiv.apply_symm_apply]

end TauCeti.ContCohomology.DiscreteShortExact
