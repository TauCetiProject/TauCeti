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
separation lemma identify the subgroup in this chart with the zero-complement slice.  Translating
this identity chart gives the corresponding local models at other subgroup points.

The complement, transverse separation radius, and local product chart are supplied by
`TauCeti.Lie.exists_complement_data_of_isClosed_subgroup`.

## Main results

* `TauCeti.Lie.exists_isSliceChart_of_isClosed_subgroup` packages the identity slice chart while
  retaining its smooth partial-diffeomorphism structure.

The theorem does not install a manifold or Lie-group structure on the subgroup subtype.

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

attribute [local instance] LieGroup.minSmoothnessThree
attribute [local instance] ContMDiffMul.boundarylessManifold

/-- A closed subgroup is the zero-complement slice in a complementary exponential chart at `1`. -/
theorem exists_isSliceChart_of_isClosed_subgroup {K : Subgroup G}
    (hK : IsClosed (K : Set G)) :
    let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
    ∃ (p q : _root_.Submodule ℝ (LeftInvariantDerivation I G))
      (Φ : PartialDiffeomorph I 𝓘(ℝ, p × q) G (p × q) ∞),
      IsCompl p q ∧ (1 : G) ∈ Φ.source ∧
        IsSliceChart Φ.toOpenPartialHomeomorph
          ((univ : Set p) ×ˢ ({0} : Set q)) (K : Set G) := by
  let _ : T2Space G := t2Space_of_lieGroup (I := I) (n := ∞)
  dsimp only
  let p : _root_.Submodule ℝ (LeftInvariantDerivation I G) :=
    (lieSubalgebraOfSubgroup (I := I) K).toSubmodule
  obtain ⟨q, ε, hpq, hε, hsep, hf⟩ :=
    exists_complement_data_of_isClosed_subgroup (I := I) hK
  let Φ₀ : OpenPartialHomeomorph G (p × q) := hf.localInverse.toOpenPartialHomeomorph
  -- Shrink the inverse chart so that its transverse coordinate lies in the separation ball.
  let A : Set (p × q) := (Prod.snd : p × q → q) ⁻¹' Metric.ball (0 : q) ε
  let V : Set G := Φ₀.source ∩ Φ₀ ⁻¹' A
  have hV : IsOpen V := by
    have hA : IsOpen A := by
      exact Metric.isOpen_ball.preimage continuous_snd
    simpa only [V] using Φ₀.continuousOn.isOpen_inter_preimage Φ₀.open_source hA
  let Ψ : PartialDiffeomorph I 𝓘(ℝ, p × q) G (p × q) ∞ :=
    { __ := Φ₀.restrOpen V hV
      contMDiffOn_toFun := hf.localInverse.contMDiffOn_toFun.mono inter_subset_left
      contMDiffOn_invFun := hf.localInverse.contMDiffOn_invFun.mono inter_subset_left }
  have hΦ₀_eq : Φ₀ = hf.localInverse.toOpenPartialHomeomorph := by
    -- `Φ₀` is this wrapper by definition; no chart data is changed here.
    rfl
  have hΦ₀_source_eq : Φ₀.source = hf.localInverse.source := by
    -- Read the source through the explicit partial-equivalence bridge supplied by Mathlib.
    change hf.localInverse.toOpenPartialHomeomorph.source = hf.localInverse.source
    exact congrArg PartialEquiv.source
      (PartialDiffeomorph.toOpenPartialHomeomorph_toPartialHomeomorph_toPartialEquiv
        hf.localInverse)
  let Φ := Φ₀.restrOpen V hV
  have hΦ₀_toPartialEquiv (x : G) : Φ₀ x = hf.localInverse.toPartialEquiv x := by
    rw [hΦ₀_eq]
    exact (congrFun (OpenPartialHomeomorph.coe_toPartialEquiv
      hf.localInverse.toOpenPartialHomeomorph) x).symm
  have hlocalInverse_toPartialEquiv (x : G) :
      hf.localInverse.toPartialEquiv x = hf.localInverse x := by
    rfl
  have hΦ₀_source : (1 : G) ∈ Φ₀.source := by
    rw [hΦ₀_source_eq]
    simpa only [Submodule.lieExpMulLieExp_zero] using hf.localInverse_mem_source
  have hzero : Φ₀ 1 = 0 := by
    have h := hf.localInverse_left_inv (x' := (0 : p × q)) hf.localInverse_mem_target
    rw [hΦ₀_toPartialEquiv]
    simpa only [Submodule.lieExpMulLieExp_zero] using h
  have h1 : (1 : G) ∈ Φ.source := by
    -- The inverse chart sends `1` to `0`, whose transverse coordinate lies in every positive ball.
    rw [OpenPartialHomeomorph.restrOpen_source]
    refine ⟨?_, ?_⟩
    · exact hΦ₀_source
    · change 1 ∈ Φ₀.source ∩ Φ₀ ⁻¹' A
      refine ⟨hΦ₀_source, ?_⟩
      change Φ₀ 1 ∈ A
      rw [hzero]
      exact Metric.mem_ball_self hε
  refine ⟨p, q, Ψ, hpq, ?_, ?_⟩
  · change (1 : G) ∈ Φ.source
    exact h1
  -- Unfold the local name `Φ`; the remaining chart equality uses the coercion fact above.
  · change IsSliceChart (Φ₀.restrOpen V hV)
      ((univ : Set p) ×ˢ ({0} : Set q)) (K : Set G)
    apply isSliceChart_iff.2
    intro x hx
    -- On the restricted source, write `x = exp z₁ · exp z₂` using the local inverse.
    rw [OpenPartialHomeomorph.restrOpen_source] at hx
    simp only [OpenPartialHomeomorph.coe_restrOpen]
    -- The remaining changes below unfold the local set aliases `V` and `A`.
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
      have hright' : Submodule.lieExpMulLieExp (I := I) (G := G) p q
          (hf.localInverse.toPartialEquiv x) = x := by
        rw [hlocalInverse_toPartialEquiv]
        exact hright
      rw [Submodule.lieExpMulLieExp_apply] at hright'
      have hz_eq : z = hf.localInverse.toPartialEquiv x := by
        exact hΦ₀_toPartialEquiv x
      rw [hz_eq]
      exact hright'
    have hz2norm : ‖(z.2 : LeftInvariantDerivation I G)‖ < ε := by
      have hzA' : z.2 ∈ Metric.ball (0 : q) ε := by
        simpa only [A, Set.mem_preimage] using hzA
      simpa only [Metric.mem_ball, dist_zero_right, Submodule.norm_coe] using hzA'
    have hz1K : lieExp (I := I) (z.1 : LeftInvariantDerivation I G) ∈ K :=
      lieExp_mem_of_mem_lieSubalgebraOfSubgroup hK z.1.property
    constructor
    · intro hxK
      -- Cancel the first exponential inside `K`; separation then forces the transverse term
      -- to vanish.
      have hz2K : lieExp (I := I) (z.2 : LeftInvariantDerivation I G) ∈ K := by
        have hm := K.mul_mem (K.inv_mem hz1K) hxK
        rw [← hzprod] at hm
        simpa using hm
      have hz20 : (z.2 : LeftInvariantDerivation I G) = 0 :=
        (hsep (z.2 : LeftInvariantDerivation I G) z.2.property hz2norm).mp hz2K
      exact Set.mem_prod.mpr
        ⟨Set.mem_univ _, Set.mem_singleton_iff.mpr (Subtype.ext hz20)⟩
    · intro hz20
      -- A zero transverse coordinate reduces the product to an exponential from the Lie
      -- subalgebra.
      have hz20' : z.2 = 0 := by
        exact Set.mem_singleton_iff.mp (Set.mem_prod.mp hz20).2
      have hzprod' := hzprod
      rw [hz20'] at hzprod'
      have hzprod'' : lieExp (I := I) (z.1 : LeftInvariantDerivation I G) = x := by
        simpa only [Submodule.coe_zero, lieExp_zero, mul_one] using hzprod'
      rw [← hzprod'']
      exact hz1K

end TauCeti.Lie
