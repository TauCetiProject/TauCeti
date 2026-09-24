/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.CartanChart
public import TauCeti.Geometry.Lie.Exponential.ProductChart
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic

/-!
# The identity slice chart of a closed subgroup

For a closed subgroup of a finite-dimensional Lie group, the complementary exponential-product
map is a local chart at the identity.  The local Cartan membership criterion and the transverse
separation lemma identify the subgroup in this chart with the zero-complement slice.  This is the
chart-level boundary used by the translated subgroup atlas.

## Main results

* `TauCeti.Lie.exists_isSliceChart_of_isClosed_subgroup` packages the identity slice chart.

The theorem stops at the topological chart interface: it does not install a manifold or Lie-group
structure on the subgroup subtype.
-/

public section

noncomputable section

namespace TauCeti.Lie

open Filter Set
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- A closed subgroup is the zero-complement slice in a complementary exponential chart at `1`. -/
theorem exists_isSliceChart_of_isClosed_subgroup {K : Subgroup G}
    (hK : IsClosed (K : Set G)) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    ∃ (p q : _root_.Submodule ℝ (LeftInvariantDerivation I G))
      (Φ : OpenPartialHomeomorph G (p × q)),
      IsCompl p q ∧ (1 : G) ∈ Φ.source ∧
        IsSliceChart Φ ((univ : Set p) ×ˢ ({0} : Set q)) (K : Set G) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let p : _root_.Submodule ℝ (LeftInvariantDerivation I G) :=
    (lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  obtain ⟨q, hpq⟩ := _root_.Submodule.exists_isCompl p
  obtain ⟨ε, hε, hsep⟩ :=
    exists_pos_forall_norm_lt_lieExp_mem_iff_eq_zero_of_disjoint (I := I) hK q hpq.disjoint.symm
  let hf := Submodule.isLocalDiffeomorphAt_lieExpMulLieExp_zero_of_isCompl
    (I := I) (G := G) p q hpq
  let Φ₀ : OpenPartialHomeomorph G (p × q) := hf.localInverse.toOpenPartialHomeomorph
  let A : Set (p × q) := (Prod.snd : p × q → q) ⁻¹' Metric.ball (0 : q) ε
  let V : Set G := Φ₀.source ∩ Φ₀ ⁻¹' A
  have hV : IsOpen V := by
    have hA : IsOpen A := by
      exact Metric.isOpen_ball.preimage continuous_snd
    simpa only [V] using Φ₀.continuousOn.isOpen_inter_preimage Φ₀.open_source hA
  let Φ := Φ₀.restrOpen V hV
  have hzero : Φ₀ 1 = 0 := by
    have h := hf.localInverse_left_inv (x' := (0 : p × q)) hf.localInverse_mem_target
    change hf.localInverse.toPartialEquiv 1 = 0
    simpa only [Submodule.lieExpMulLieExp_zero] using h
  have h1 : (1 : G) ∈ Φ.source := by
    change 1 ∈ Φ₀.source ∩ V
    refine ⟨?_, ?_⟩
    · change 1 ∈ hf.localInverse.source
      simpa only [Submodule.lieExpMulLieExp_zero] using hf.localInverse_mem_source
    · change 1 ∈ Φ₀.source ∩ Φ₀ ⁻¹' A
      refine ⟨?_, ?_⟩
      · exact (by
          change 1 ∈ hf.localInverse.source
          simpa only [Submodule.lieExpMulLieExp_zero] using hf.localInverse_mem_source)
      · change Φ₀ 1 ∈ A
        rw [hzero]
        change (0 : q) ∈ Metric.ball (0 : q) ε
        exact Metric.mem_ball_self hε
  refine ⟨p, q, Φ, hpq, h1, ?_⟩
  change IsSliceChart (Φ₀.restrOpen V hV)
    ((univ : Set p) ×ˢ ({0} : Set q)) (K : Set G)
  apply isSliceChart_iff.2
  intro x hx
  rw [OpenPartialHomeomorph.restrOpen_source] at hx
  simp only [OpenPartialHomeomorph.coe_restrOpen]
  change x ∈ Φ₀.source ∩ V at hx
  let z : p × q := Φ₀ x
  have hxV : x ∈ V := hx.2
  change x ∈ Φ₀.source ∩ Φ₀ ⁻¹' A at hxV
  have hzA : z ∈ A := by
    change Φ₀ x ∈ A
    exact hxV.2
  have hzprod : lieExp (I := I) (z.1 : LeftInvariantDerivation I G) *
      lieExp (I := I) (z.2 : LeftInvariantDerivation I G) = x := by
    have hright := hf.localInverse_right_inv hx.1
    change Submodule.lieExpMulLieExp (I := I) (G := G) p q
        (hf.localInverse.toPartialEquiv x) = x at hright
    rw [Submodule.lieExpMulLieExp_apply] at hright
    have hz_eq : z = hf.localInverse.toPartialEquiv x := by
      change Φ₀ x = hf.localInverse.toPartialEquiv x
      change hf.localInverse.toOpenPartialHomeomorph x = hf.localInverse.toPartialEquiv x
      exact (congrFun (OpenPartialHomeomorph.coe_toPartialEquiv
        hf.localInverse.toOpenPartialHomeomorph) x).symm
    rw [hz_eq]
    exact hright
  have hz2norm : ‖(z.2 : LeftInvariantDerivation I G)‖ < ε := by
    have hzA' : z.2 ∈ Metric.ball (0 : q) ε := by
      simpa only [A, Set.mem_preimage] using hzA
    simpa only [Metric.mem_ball, dist_zero_right, Submodule.norm_coe] using hzA'
  have hz1K : lieExp (I := I) (z.1 : LeftInvariantDerivation I G) ∈ K :=
    lieExp_mem_of_mem_lieSubalgebraOfSubgroup hK z.1.property
  constructor
  · intro hxK
    have hz2K : lieExp (I := I) (z.2 : LeftInvariantDerivation I G) ∈ K := by
      have hm := K.mul_mem (K.inv_mem hz1K) hxK
      rw [← hzprod] at hm
      simpa using hm
    have hz20 : (z.2 : LeftInvariantDerivation I G) = 0 :=
      (hsep (z.2 : LeftInvariantDerivation I G) z.2.property hz2norm).mp hz2K
    change z.1 ∈ (univ : Set p) ∧ z.2 ∈ ({0} : Set q)
    exact ⟨mem_univ _, Set.mem_singleton_iff.mpr (Subtype.ext hz20)⟩
  · intro hz20
    have hz20' : z.2 = 0 := by
      change z ∈ (univ : Set p) ×ˢ ({0} : Set q) at hz20
      exact hz20.2
    have hzprod' := hzprod
    rw [hz20'] at hzprod'
    change lieExp (I := I) (z.1 : LeftInvariantDerivation I G) *
        lieExp (I := I) (0 : LeftInvariantDerivation I G) = x at hzprod'
    rw [lieExp_zero, mul_one] at hzprod'
    rw [← hzprod']
    exact hz1K

end TauCeti.Lie
