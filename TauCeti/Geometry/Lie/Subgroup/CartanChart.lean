/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Exponential.ProductChart
public import TauCeti.Geometry.Lie.Subgroup.LocalSeparation

/-!
# The local Cartan chart of a closed subgroup

For a closed subgroup `K` of a finite-dimensional Lie group, this file gives a neighborhood of
the identity on which membership in `K` is equivalent to being the exponential of an element of
`lieSubalgebraOfSubgroup K`.  This local characterization is the membership criterion used by
the embedded Lie-subgroup chart.

## Main result

* `TauCeti.Lie.exists_mem_nhds_one_iff_exists_lieExp_eq_of_mem_lieSubalgebraOfSubgroup_of_isClosed`:
  a closed subgroup is locally the exponential image of its Lie algebra.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
* H. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
-/

public section

noncomputable section

namespace TauCeti.Lie

open Filter
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- Near the identity, a closed subgroup is exactly the exponential image of its Lie algebra.
This is the local membership criterion for the embedded Lie-subgroup chart. -/
theorem exists_mem_nhds_one_iff_exists_lieExp_eq_of_mem_lieSubalgebraOfSubgroup_of_isClosed
    {K : Subgroup G}
    (hK : IsClosed (K : Set G)) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    ∃ U ∈ 𝓝 (1 : G), ∀ x : G, x ∈ U →
      (x ∈ K ↔ ∃ X : LeftInvariantDerivation I G,
        X ∈ lieSubalgebraOfSubgroup (I := I) K ∧ lieExp (I := I) X = x) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  -- Choose a linear complement and the corresponding transverse separation radius; the
  -- local product chart then supplies coordinates in the Lie algebra and its complement.
  let p : Submodule ℝ (LeftInvariantDerivation I G) :=
    (lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
  obtain ⟨ε, hε, hsep⟩ :=
    exists_pos_forall_norm_lt_lieExp_mem_iff_eq_zero_of_disjoint (I := I) hK q hpq.disjoint.symm
  let hf := Submodule.isLocalDiffeomorphAt_lieExpMulLieExp_zero_of_isCompl
    (I := I) (G := G) p q hpq
  let A : Set (p × q) := (Prod.snd : p × q → q) ⁻¹' Metric.ball (0 : q) ε
  have hA : A ∈ 𝓝 (0 : p × q) := by
    apply continuousAt_snd.preimage_mem_nhds
    simpa using Metric.ball_mem_nhds (0 : q) hε
  have hinv_one : (hf.localInverse (1 : G) : p × q) = 0 := by
    have h := hf.localInverse_left_inv (x' := (0 : p × q)) hf.localInverse_mem_target
    simpa only [Submodule.lieExpMulLieExp_zero] using h
  have hsource : (1 : G) ∈ hf.localInverse.source := by
    simpa only [Submodule.lieExpMulLieExp_zero] using hf.localInverse_mem_source
  -- Restrict the chart source to points whose complement coordinate lies in the separation ball.
  -- The source condition makes the local inverse identities available, while the preimage
  -- condition is transported to the identity by the inverse value at `1`.
  let U : Set G := hf.localInverse.source ∩ hf.localInverse ⁻¹' A
  have hU : U ∈ 𝓝 (1 : G) := by
    apply Filter.inter_mem (hf.localInverse_open_source.mem_nhds hsource)
    have hA' : A ∈ 𝓝 (hf.localInverse (Submodule.lieExpMulLieExp p q 0)) := by
      rw [Submodule.lieExpMulLieExp_zero, hinv_one]
      exact hA
    simpa only [Submodule.lieExpMulLieExp_zero] using
      hf.localInverse_contMDiffAt.continuousAt.preimage_mem_nhds hA'
  refine ⟨U, hU, ?_⟩
  intro x hxU
  constructor
  -- In the forward direction, subgroup cancellation puts the transverse exponential in `K`;
  -- local separation forces its coordinate to vanish, leaving only the Lie-subalgebra factor.
  · intro hxK
    let z : p × q := hf.localInverse x
    have hxsource : x ∈ hf.localInverse.source := hxU.1
    have hzA : z ∈ A := hxU.2
    have hzprod : lieExp (I := I) (z.1 : LeftInvariantDerivation I G) *
        lieExp (I := I) (z.2 : LeftInvariantDerivation I G) = x := by
      simpa only [z, Function.comp_apply, Submodule.lieExpMulLieExp_apply] using
        hf.localInverse_right_inv hxsource
    have hz2norm : ‖(z.2 : LeftInvariantDerivation I G)‖ < ε := by
      have hzA' : z.2 ∈ Metric.ball (0 : q) ε := by
        simpa only [A, Set.mem_preimage] using hzA
      simpa only [Metric.mem_ball, dist_zero_right, Submodule.norm_coe] using hzA'
    have hz1p : (z.1 : LeftInvariantDerivation I G) ∈
        (lieSubalgebraOfSubgroup (I := I) K).toSubmodule := by
      simpa only [p] using z.1.property
    have hz1K : lieExp (I := I) (z.1 : LeftInvariantDerivation I G) ∈ K :=
      lieExp_mem_of_mem_lieSubalgebraOfSubgroup hK
        ((LieSubalgebra.mem_toSubmodule (lieSubalgebraOfSubgroup (I := I) K)).mp hz1p)
    have hz2K : lieExp (I := I) (z.2 : LeftInvariantDerivation I G) ∈ K := by
      have hm := K.mul_mem (K.inv_mem hz1K) hxK
      rw [← hzprod] at hm
      simpa using hm
    have hz20 : (z.2 : LeftInvariantDerivation I G) = 0 :=
      (hsep (z.2 : LeftInvariantDerivation I G) z.2.property hz2norm).mp hz2K
    refine ⟨(z.1 : LeftInvariantDerivation I G),
      (LieSubalgebra.mem_toSubmodule (lieSubalgebraOfSubgroup (I := I) K)).mp hz1p, ?_⟩
    have hzprod' := hzprod
    rw [hz20, lieExp_zero, mul_one] at hzprod'
    exact hzprod'
  -- The reverse direction is the defining exponential-membership property of the Lie subalgebra.
  · rintro ⟨X, hX, rfl⟩
    exact lieExp_mem_of_mem_lieSubalgebraOfSubgroup hK hX

end TauCeti.Lie
