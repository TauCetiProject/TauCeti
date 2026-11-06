/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.CartanChart
public import TauCeti.Geometry.Manifold.LocallyFlat.Basic

/-!
# The identity slice chart of a closed subgroup

For a closed subgroup of a finite-dimensional Lie group, the complementary exponential-product
map is a local chart at the identity.  The local Cartan membership criterion and the transverse
separation lemma identify the subgroup in this chart with the zero-complement slice, whose
tangential factor is the Lie algebra that `TauCeti.Lie.lieSubalgebraOfSubgroup` assigns to the
subgroup.  Translating this identity chart gives the corresponding local models at other subgroup
points.

The complement, transverse separation radius, and local product chart are supplied by
`TauCeti.Lie.exists_complement_data_of_isClosed_subgroup`.

## Main results

* `TauCeti.Lie.exists_isSliceChart_of_isClosed_subgroup` packages the identity slice chart.

The resulting chart retains the smoothness of both directions of the local diffeomorphism. A
separate construction installs the induced manifold structure on the subgroup subtype.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition (2013), Theorem 20.12.
* H. Hilgert and K.-H. Neeb, *Structure and Geometry of Lie Groups* (2012), Section 9.1.
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

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- A chart whose inverse coordinates `(z₁, z₂)` satisfy `exp z₁ * exp z₂ = x` is a slice chart
for a subgroup `K` on any open subset of its source where the transverse coordinate `z₂` lies in
a ball on which `exp z₂ ∈ K` forces `z₂ = 0`, once `exp z₁ ∈ K` for all tangential `z₁`. -/
private theorem isSliceChart_restrOpen_of_lieExp_mul_lieExp [T2Space G] {K : Subgroup G}
    {p q : _root_.Submodule ℝ (LeftInvariantDerivation I G)}
    (hpK : ∀ z ∈ p, lieExp (I := I) z ∈ K) {ε : ℝ}
    (hsep : ∀ X ∈ q, ‖X‖ < ε → (lieExp (I := I) X ∈ K ↔ X = 0))
    (Φ₀ : OpenPartialHomeomorph G (p × q))
    (hprod : ∀ x ∈ Φ₀.source, lieExp (I := I) (Φ₀ x).1 * lieExp (I := I) (Φ₀ x).2 = x)
    {V : Set G} (hV : IsOpen V)
    (hε : ∀ x ∈ Φ₀.source ∩ V, ‖((Φ₀ x).2 : LeftInvariantDerivation I G)‖ < ε) :
    IsSliceChart (Φ₀.restrOpen V hV) ((univ : Set p) ×ˢ ({0} : Set q)) (K : Set G) := by
  refine isSliceChart_iff.2 fun x hx => ?_
  rw [OpenPartialHomeomorph.restrOpen_source] at hx
  simp only [OpenPartialHomeomorph.coe_restrOpen, Set.mem_prod, Set.mem_univ, true_and,
    Set.mem_singleton_iff, SetLike.mem_coe]
  have hz1K := hpK (Φ₀ x).1 (Φ₀ x).1.property
  refine ⟨fun hxK ↦ ?_, fun hz20 ↦ ?_⟩
  · -- Cancel the first exponential inside `K`; separation then forces the transverse term
    -- to vanish.
    have hz2K : lieExp (I := I) ((Φ₀ x).2 : LeftInvariantDerivation I G) ∈ K := by
      rw [eq_inv_mul_iff_mul_eq.2 (hprod x hx.1)]
      exact K.mul_mem (K.inv_mem hz1K) hxK
    exact Subtype.ext ((hsep _ (Φ₀ x).2.property (hε x hx)).mp hz2K)
  · -- A zero transverse coordinate reduces the product to an exponential from the subalgebra.
    have h := hprod x hx.1
    rw [hz20, Submodule.coe_zero, lieExp_zero, mul_one] at h
    exact h ▸ hz1K

/-- A closed subgroup is the zero-complement slice in a smooth complementary exponential chart
at `1`, the tangential factor of the chart being its Lie algebra. -/
theorem exists_isSliceChart_of_isClosed_subgroup {K : Subgroup G}
    (hK : IsClosed (K : Set G)) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    ∃ (q : _root_.Submodule ℝ (LeftInvariantDerivation I G))
      (Φ : OpenPartialHomeomorph G
        ((lieSubalgebraOfSubgroup (I := I) K).toSubmodule × q)),
      IsCompl (lieSubalgebraOfSubgroup (I := I) K).toSubmodule q ∧ (1 : G) ∈ Φ.source ∧
        IsSliceChart Φ
          ((univ : Set (lieSubalgebraOfSubgroup (I := I) K).toSubmodule) ×ˢ ({0} : Set q))
          (K : Set G) ∧
        ContMDiffOn I 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule × q) ∞ Φ Φ.source ∧
        ContMDiffOn 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule × q) I ∞ Φ.symm
          Φ.target := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  obtain ⟨q, ε, hpq, hε, hsep, hf⟩ :=
    exists_complement_data_of_isClosed_subgroup (I := I) hK
  let Φ₀ := hf.localInverse.toOpenPartialHomeomorph
  -- Shrink the inverse chart so that its transverse coordinate lies in the separation ball.
  let V : Set G := Φ₀.source ∩ Φ₀ ⁻¹' (Prod.snd ⁻¹' Metric.ball 0 ε)
  have hV : IsOpen V := Φ₀.continuousOn.isOpen_inter_preimage Φ₀.open_source
    (Metric.isOpen_ball.preimage continuous_snd)
  have h1 : (1 : G) ∈ Φ₀.source := by
    have h := hf.localInverse_mem_source
    rw [Submodule.lieExpMulLieExp_zero] at h
    exact h
  have hzero : Φ₀ 1 = 0 := by
    have h := hf.localInverse_left_inv (x' := 0) hf.localInverse_mem_target
    rw [Submodule.lieExpMulLieExp_zero] at h
    exact h
  refine ⟨q, Φ₀.restrOpen V hV, hpq, ⟨h1, h1, ?_⟩, ?_, ?_, ?_⟩
  · -- The inverse chart sends `1` to `0`, whose transverse coordinate lies in every positive ball.
    change Φ₀ 1 ∈ Prod.snd ⁻¹' Metric.ball 0 ε
    rw [hzero]
    exact Metric.mem_ball_self hε
  · refine isSliceChart_restrOpen_of_lieExp_mul_lieExp
      (fun z hz ↦ lieExp_mem_of_mem_lieSubalgebraOfSubgroup hK hz) hsep Φ₀ (fun x hx ↦ ?_) hV
      fun x hx ↦ ?_
    · have h := hf.localInverse_right_inv hx
      rw [Submodule.lieExpMulLieExp_apply] at h
      exact h
    · have h : (Φ₀ x).2 ∈ Metric.ball (0 : q) ε := hx.2.2
      simpa only [Metric.mem_ball, dist_zero_right, Submodule.norm_coe] using h
  · exact hf.contMDiffOn_localInverse.mono inter_subset_left
  · exact hf.localInverse.contMDiffOn_invFun.mono inter_subset_left

end TauCeti.Lie
