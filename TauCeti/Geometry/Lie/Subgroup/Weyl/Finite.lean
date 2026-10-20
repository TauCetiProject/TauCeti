/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Subgroup.Torus
public import TauCeti.Algebra.Group.NormalizerQuotient.Basic
import TauCeti.Geometry.Lie.Exponential.CommutativeGroup
import TauCeti.Geometry.Lie.Subgroup.CartanChart
import TauCeti.Geometry.Lie.Subgroup.Differential
import TauCeti.Geometry.Lie.Adjoint.Representation.Basic
import TauCeti.Geometry.Lie.Adjoint.Exponential.Formula
import TauCeti.Topology.Algebra.Group.Subgroup
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# The Weyl group of a maximal torus is finite

For a maximal torus `T` of a compact finite-dimensional real Lie group `G`, the Weyl group
`N(T) / T` is finite. The proof has three steps.

* **The integral lattice spans.** The elements `X ∈ Lie(T)` with `lieExp X = 1` span `Lie(T)`:
  through the closed-subgroup theorem `T` is itself a compact commutative Lie group with Lie
  algebra `Lie(T)`, whose exponential kernel is a lattice of full rank.
* **The normalizer has the Lie algebra of the centralizer.** For `X` in the Lie algebra of the
  normalizer of a torus `T`, the operators `Ad (lieExp (s • X))` preserve the integral lattice of
  `Lie(T)`, which is discrete, and depend continuously on `s`; so they fix the lattice pointwise,
  hence fix `Lie(T)`, and the one-parameter subgroup of `X` centralizes `T`. For a maximal torus
  of a compact group the centralizer has the Lie algebra of `T`.
* **Openness.** A closed subgroup `T ≤ K` with `Lie(K) ≤ Lie(T)` is open in `K`, because near the
  identity `K` is the exponential image of its Lie algebra. So `T` is open in its normalizer,
  which is compact; the quotient of a compact group by an open subgroup is finite.

## Main results

* `TauCeti.Lie.IsTorus.span_setOf_lieExp_eq_one`: the integral lattice of a torus spans its Lie
  algebra.
* `TauCeti.Lie.IsTorus.lieSubalgebraOfSubgroup_normalizer`: the normalizer and the centralizer of
  a torus have the same Lie algebra.
* `TauCeti.Lie.IsMaximalTorus.lieSubalgebraOfSubgroup_normalizer`: the normalizer of a maximal
  torus of a compact Lie group has the Lie algebra of the torus.
* `TauCeti.Lie.IsMaximalTorus.finite_normalizerQuotient`: **the Weyl group of a maximal torus of a
  compact Lie group is finite.**

## References

* T. Bröcker and T. tom Dieck, *Representations of Compact Lie Groups*, Springer GTM 98 (1985),
  Chapter IV, § 1 (Maximal Tori).
* D. Bump, *Lie Groups*, 2nd ed., Springer GTM 225 (2013), Chapter 15 (Tori).
-/

public section

noncomputable section

namespace TauCeti.Lie

open Filter
open scoped ContDiff Manifold Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [FiniteDimensional ℝ E] [LieGroup I ∞ G] [T2Space G]

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- **The integral lattice of a torus spans its Lie algebra**: the elements `X ∈ Lie(T)` with
`lieExp X = 1` span `Lie(T)`. -/
theorem IsTorus.span_setOf_lieExp_eq_one {T : Subgroup G} (hT : IsTorus T) :
    Submodule.span ℝ {X | X ∈ lieSubalgebraOfSubgroup (I := I) T ∧ lieExp (I := I) X = 1} =
      (lieSubalgebraOfSubgroup (I := I) T).toSubmodule := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  let _ : FiniteDimensional ℝ (LeftInvariantDerivation I G) :=
    finiteDimensional_leftInvariantDerivation
      (ContMDiffMul.isInteriorPoint (I := I) (n := ∞) (by simp) (1 : G))
  refine le_antisymm (Submodule.span_le.mpr fun X hX => hX.1) ?_
  -- Through the closed-subgroup theorem, `T` is a compact commutative Lie group modelled on
  -- `Lie(T)`, and the differential of its inclusion identifies its Lie algebra with `Lie(T)`.
  obtain ⟨d⟩ :=
    nonempty_embeddedLieSubgroupData_lieSubalgebraOfSubgroup_of_isClosed (I := I) hT.isClosed
  let F := (lieSubalgebraOfSubgroup (I := I) T).toSubmodule
  let _ : ChartedSpace F T := d.chartedSpace
  let _ : LieGroup 𝓘(ℝ, F) ∞ T := d.lieGroup
  have _ : CompactSpace T := isCompact_iff_compactSpace.mp hT.isCompact
  have _ : IsMulCommutative T := hT.isMulCommutative
  have hrange := d.range_lieMapSubtypeVal_eq
  dsimp only at hrange
  conv_lhs => rw [← hrange]
  rw [LieHom.range_toSubmodule, ← Submodule.map_top,
    ← span_ker_lieExpAddMonoidHom_eq_top (I := 𝓘(ℝ, F)) (G := T), Submodule.map_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨Y, hY, rfl⟩
  refine ⟨d.lieMapSubtypeVal_mem_lieSubalgebraOfSubgroup Y, ?_⟩
  have hexp := map_lieExp d.subtypeVal Y
  dsimp only at hexp
  rw [SetLike.mem_coe, mem_ker_lieExpAddMonoidHom] at hY
  rw [hY, map_one] at hexp
  rw [LieHom.coe_toLinearMap, d.lieMapSubtypeVal_apply]
  exact hexp.symm

/-- For `X` in the Lie algebra of the normalizer of a torus `T`, each `Ad (lieExp (s • X))` fixes
the integral lattice of `Lie(T)`. -/
private theorem IsTorus.Ad_lieExp_smul_apply_eq_self_of_lieExp_eq_one {T : Subgroup G}
    (hT : IsTorus T) {X : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) (Subgroup.normalizer (T : Set G)))
    {Y : LeftInvariantDerivation I G} (hY : Y ∈ lieSubalgebraOfSubgroup (I := I) T)
    (hY1 : lieExp (I := I) Y = 1) (s : ℝ) :
    Ad (I := I) (lieExp (I := I) (s • X)) Y = Y := by
  -- `Ad (lieExp (s • X)) Y` stays in the integral lattice, which is discrete since `lieExp` is
  -- injective near `0`, and depends continuously on `s`; so it is locally constant in `s`.
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have := hT.isMulCommutative
  have hmemN := (mem_lieSubalgebraOfSubgroup (Subgroup.isClosed_normalizer hT.isClosed)).mp hX
  obtain ⟨V, hV, hVlog⟩ := (eventually_lieLog_lieExp (I := I) (G := G)).exists_mem
  have hdiscrete : ∀ Z ∈ V, lieExp (I := I) Z = 1 → Z = 0 := fun Z hZ hZ1 => by
    rw [← hVlog Z hZ, hZ1, lieLog_one]
  let f : ℝ → LeftInvariantDerivation I G := fun s => Ad (I := I) (lieExp (I := I) (s • X)) Y
  have hf : Continuous f :=
    (contMDiff_Ad_apply (I := I) (G := G)).continuous.comp
      (((contMDiff_lieExp (I := I) (G := G)).continuous.comp
        (continuous_id.smul continuous_const)).prodMk continuous_const)
  have hfT : ∀ s, f s ∈ lieSubalgebraOfSubgroup (I := I) T := fun s =>
    Ad_mem_lieSubalgebraOfSubgroup (hmemN s) hY
  have hf1 : ∀ s, lieExp (I := I) (f s) = 1 := fun s => by
    simp only [f, ← conj_lieExp, hY1, mul_one, mul_inv_cancel]
  have hloc : IsLocallyConstant f := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro s₀
    have hsub : Tendsto (fun s => f s - f s₀) (𝓝 s₀) (𝓝 0) := by
      simpa only [sub_self] using (hf.tendsto s₀).sub_const (f s₀)
    filter_upwards [hsub hV] with s hs
    refine sub_eq_zero.mp (hdiscrete _ hs ?_)
    rw [sub_eq_add_neg, lieExp_add_of_lie_eq_zero
        (lie_eq_zero_of_mem_lieSubalgebraOfSubgroup (hfT s) (neg_mem (hfT s₀))),
      lieExp_neg, hf1, hf1, inv_one, mul_one]
  have h0 : f 0 = Y := by simp only [f, zero_smul, lieExp_zero, Ad_one, LieEquiv.refl_apply]
  have hs := hloc.apply_eq_of_preconnectedSpace s 0
  rwa [h0] at hs

/-- For `X` in the Lie algebra of the normalizer of a torus `T`, each `Ad (lieExp (s • X))` fixes
`Lie(T)` pointwise. -/
private theorem IsTorus.Ad_lieExp_smul_apply_eq_self {T : Subgroup G} (hT : IsTorus T)
    {X : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) (Subgroup.normalizer (T : Set G)))
    {Y : LeftInvariantDerivation I G} (hY : Y ∈ lieSubalgebraOfSubgroup (I := I) T) (s : ℝ) :
    Ad (I := I) (lieExp (I := I) (s • X)) Y = Y := by
  -- The integral lattice, which `Ad (lieExp (s • X))` fixes, spans `Lie(T)`.
  rw [← SetLike.mem_coe, ← LieSubalgebra.coe_toSubmodule, ← hT.span_setOf_lieExp_eq_one,
    SetLike.mem_coe] at hY
  induction hY using Submodule.span_induction with
  | mem Z hZ => exact hT.Ad_lieExp_smul_apply_eq_self_of_lieExp_eq_one hX hZ.1 hZ.2 s
  | zero => exact map_zero _
  | add Z W _ _ hZ hW => rw [map_add, hZ, hW]
  | smul c Z _ hZ => rw [map_smul, hZ]

/-- A one-parameter subgroup in the normalizer of a torus `T` centralizes `T`. -/
private theorem IsTorus.lieExp_smul_mem_centralizer {T : Subgroup G} (hT : IsTorus T)
    {X : LeftInvariantDerivation I G}
    (hX : X ∈ lieSubalgebraOfSubgroup (I := I) (Subgroup.normalizer (T : Set G))) (s : ℝ) :
    lieExp (I := I) (s • X) ∈ Subgroup.centralizer (T : Set G) := by
  -- The adjoint action of `lieExp (s • X)` fixes `Lie(T)`, whose exponential image is `T`.
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rw [← hT.image_lieExp_lieSubalgebraOfSubgroup (I := I)] at ht
  obtain ⟨Y, hY, rfl⟩ := ht
  have hconj := conj_lieExp (I := I) (lieExp (I := I) (s • X)) Y
  dsimp only at hconj
  rw [hT.Ad_lieExp_smul_apply_eq_self hX hY s] at hconj
  exact (mul_inv_eq_iff_eq_mul.mp hconj).symm

/-- **The normalizer and the centralizer of a torus have the same Lie algebra.** -/
theorem IsTorus.lieSubalgebraOfSubgroup_normalizer {T : Subgroup G} (hT : IsTorus T) :
    lieSubalgebraOfSubgroup (I := I) (Subgroup.normalizer (T : Set G)) =
      lieSubalgebraOfSubgroup (I := I) (Subgroup.centralizer (T : Set G)) :=
  le_antisymm
    (fun _ hX => mem_lieSubalgebraOfSubgroup_of_forall
      (hT.lieExp_smul_mem_centralizer hX))
    (lieSubalgebraOfSubgroup_mono (Subgroup.centralizer_le_normalizer _))

variable [CompactSpace G]

/-- **The normalizer of a maximal torus of a compact Lie group has the Lie algebra of the
torus.** -/
theorem IsMaximalTorus.lieSubalgebraOfSubgroup_normalizer {T : Subgroup G}
    (hT : IsMaximalTorus T) :
    lieSubalgebraOfSubgroup (I := I) (Subgroup.normalizer (T : Set G)) =
      lieSubalgebraOfSubgroup (I := I) T := by
  rw [hT.isTorus.lieSubalgebraOfSubgroup_normalizer, hT.lieSubalgebraOfSubgroup_centralizer]

section Finite

variable (I)
include I

/-- **A maximal torus of a compact Lie group is open in its normalizer.** -/
theorem IsMaximalTorus.isOpen_subgroupOf_normalizer {T : Subgroup G} (hT : IsMaximalTorus T) :
    IsOpen (T.subgroupOf (Subgroup.normalizer (T : Set G)) :
      Set (Subgroup.normalizer (T : Set G))) :=
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  isOpen_subgroupOf_of_lieSubalgebraOfSubgroup_le (I := I) hT.isTorus.isClosed
    (Subgroup.isClosed_normalizer hT.isTorus.isClosed)
    (hT.lieSubalgebraOfSubgroup_normalizer (I := I)).le

/-- **The Weyl group of a maximal torus of a compact Lie group is finite.** -/
theorem IsMaximalTorus.finite_normalizerQuotient {T : Subgroup G} (hT : IsMaximalTorus T) :
    Finite T.normalizerQuotient := by
  let _ : IsTopologicalGroup G := topologicalGroup_of_lieGroup I ∞
  have _ : CompactSpace (Subgroup.normalizer (T : Set G)) :=
    isCompact_iff_compactSpace.mp (Subgroup.isClosed_normalizer hT.isTorus.isClosed).isCompact
  exact Subgroup.quotient_finite_of_isOpen _ (hT.isOpen_subgroupOf_normalizer I)

end Finite

end TauCeti.Lie
