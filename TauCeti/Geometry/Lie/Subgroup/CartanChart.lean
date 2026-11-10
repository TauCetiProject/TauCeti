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

* The local characterization theorem below: a closed subgroup is locally the
  exponential image of its Lie algebra.
* `TauCeti.Lie.isOpen_subgroupOf_of_lieSubalgebraOfSubgroup_le`: a closed subgroup of a closed
  subgroup `K` whose Lie algebra contains that of `K` is open in `K`.

* `TauCeti.Lie.le_of_lieSubalgebraOfSubgroup_le`: a closed connected subgroup lies in any
  closed subgroup whose Lie algebra contains its own.

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

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- For a closed subgroup, there are a complementary submodule and positive radius such that small
transverse exponentials lie in the subgroup exactly at zero, while the complementary exponential
product is a local diffeomorphism at the identity. -/
theorem exists_complement_data_of_isClosed_subgroup {K : Subgroup G}
    (hK : IsClosed (K : Set G)) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    ∃ (q : Submodule ℝ (LeftInvariantDerivation I G)) (ε : ℝ),
      IsCompl ((lieSubalgebraOfSubgroup (I := I) K).toSubmodule) q ∧ 0 < ε ∧
        (∀ X ∈ q, ‖X‖ < ε →
          (lieExp (I := I) X ∈ K ↔ X = 0)) ∧
        IsLocalDiffeomorphAt 𝓘(ℝ, (lieSubalgebraOfSubgroup (I := I) K).toSubmodule × q) I ∞
          (Submodule.lieExpMulLieExp (lieSubalgebraOfSubgroup (I := I) K).toSubmodule q) 0 := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  let p : Submodule ℝ (LeftInvariantDerivation I G) :=
    (lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  obtain ⟨q, hpq⟩ := Submodule.exists_isCompl p
  obtain ⟨ε, hε, hsep⟩ :=
    exists_pos_forall_norm_lt_lieExp_mem_iff_eq_zero_of_disjoint (I := I) hK q hpq.disjoint.symm
  let hf := Submodule.isLocalDiffeomorphAt_lieExpMulLieExp_zero_of_isCompl
    (I := I) (G := G) p q hpq
  exact ⟨q, ε, hpq, hε, hsep, hf⟩

/-- If a product `exp X₁ * exp X₂` of a Lie-subalgebra exponential and a small transverse
exponential lies in the closed subgroup `K`, then `exp X₂` is trivial, so the product equals
`exp X₁`. -/
private theorem lieExp_eq_of_mul_mem [T2Space G] {K : Subgroup G} (hK : IsClosed (K : Set G))
    {q : Submodule ℝ (LeftInvariantDerivation I G)} {ε : ℝ}
    (hsep : ∀ X ∈ q, ‖X‖ < ε → (lieExp (I := I) X ∈ K ↔ X = 0))
    {X₁ X₂ : LeftInvariantDerivation I G} (hX₁ : X₁ ∈ lieSubalgebraOfSubgroup (I := I) K)
    (hX₂ : X₂ ∈ q) (hnorm : ‖X₂‖ < ε)
    (hmem : lieExp (I := I) X₁ * lieExp (I := I) X₂ ∈ K) :
    lieExp (I := I) X₁ * lieExp (I := I) X₂ = lieExp (I := I) X₁ := by
  have hz1K : lieExp (I := I) X₁ ∈ K := lieExp_mem_of_mem_lieSubalgebraOfSubgroup hK hX₁
  have hz2K : lieExp (I := I) X₂ ∈ K := by
    simpa using K.mul_mem (K.inv_mem hz1K) hmem
  rw [(hsep X₂ hX₂ hnorm).mp hz2K, lieExp_zero, mul_one]

/-- Near the identity, a closed subgroup is exactly the exponential image of its Lie algebra.
This is the local membership criterion for the embedded Lie-subgroup chart. -/
theorem exists_mem_nhds_one_iff_exists_mem_lieSubalgebraOfSubgroup_and_lieExp_eq_of_isClosed
    {K : Subgroup G}
    (hK : IsClosed (K : Set G)) :
    let _ : T2Space G := I.t2Space_of_lieGroup ∞
    ∃ U ∈ 𝓝 (1 : G), ∀ x : G, x ∈ U →
      (x ∈ K ↔ ∃ X : LeftInvariantDerivation I G,
        X ∈ lieSubalgebraOfSubgroup (I := I) K ∧ lieExp (I := I) X = x) := by
  let _ : T2Space G := I.t2Space_of_lieGroup ∞
  dsimp only
  let p : Submodule ℝ (LeftInvariantDerivation I G) :=
    (lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  obtain ⟨q, ε, _, hε, hsep, hf⟩ :=
    exists_complement_data_of_isClosed_subgroup (I := I) hK
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
      hf.contMDiffAt_localInverse.continuousAt.preimage_mem_nhds hA'
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
    have hz1p : (z.1 : LeftInvariantDerivation I G) ∈ lieSubalgebraOfSubgroup (I := I) K :=
      (LieSubalgebra.mem_toSubmodule (lieSubalgebraOfSubgroup (I := I) K)).mp
        (by simpa only [p] using z.1.property)
    exact ⟨_, hz1p, (lieExp_eq_of_mul_mem hK hsep hz1p z.2.property hz2norm
      (by rwa [hzprod])).symm.trans hzprod⟩
  -- The reverse direction is the defining exponential-membership property of the Lie subalgebra.
  · rintro ⟨X, hX, rfl⟩
    exact lieExp_mem_of_mem_lieSubalgebraOfSubgroup hK hX

/-- **A closed subgroup `T` whose Lie algebra contains that of a closed subgroup `K` is open in
`K`**: `T ∩ K` is an open subgroup of `K`. -/
theorem isOpen_subgroupOf_of_lieSubalgebraOfSubgroup_le [T2Space G] {T K : Subgroup G}
    (hT : IsClosed (T : Set G)) (hK : IsClosed (K : Set G))
    (h : lieSubalgebraOfSubgroup (I := I) K ≤ lieSubalgebraOfSubgroup (I := I) T) :
    IsOpen (T.subgroupOf K : Set K) := by
  -- Near the identity `K` is the exponential image of its Lie algebra, which lies in `Lie(T)`.
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  obtain ⟨U, hU, hUK⟩ :=
    exists_mem_nhds_one_iff_exists_mem_lieSubalgebraOfSubgroup_and_lieExp_eq_of_isClosed
      (I := I) hK
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  rw [nhds_subtype_eq_comap]
  refine ⟨U, hU, fun k hk => ?_⟩
  obtain ⟨X, hX, hXk⟩ := (hUK k hk).mp k.2
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, ← hXk]
  exact lieExp_mem_of_mem_lieSubalgebraOfSubgroup hT (h hX)

/-- A closed connected subgroup lies in any closed subgroup containing its Lie algebra. -/
theorem le_of_lieSubalgebraOfSubgroup_le [T2Space G] {K L : Subgroup G}
    (hK : IsClosed (K : Set G)) (hconn : IsPreconnected (K : Set G))
    (hL : IsClosed (L : Set G))
    (h : lieSubalgebraOfSubgroup (I := I) K ≤ lieSubalgebraOfSubgroup (I := I) L) :
    K ≤ L := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hconn
  have hopen := isOpen_subgroupOf_of_lieSubalgebraOfSubgroup_le hL hK h
  have huniv := IsClopen.eq_univ
    ⟨(L.subgroupOf K).isClosed_of_isOpen hopen, hopen⟩ ⟨1, (L.subgroupOf K).one_mem⟩
  intro k hk
  exact Subgroup.mem_subgroupOf.mp (Set.eq_univ_iff_forall.mp huniv (⟨k, hk⟩ : K))

end TauCeti.Lie
