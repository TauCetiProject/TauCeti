/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.AddCircle
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Extend
public import TauCeti.Geometry.Diffeomorphism.Diffeotopy.Disjoint

/-!
# Extending prescribed boundary-circle maps to the ambient manifold

A parametrized inward collar is a smooth open embedding of
`EuclideanHalfSpace 1 × AddCircle T`. An orientation-preserving circle map, presented by a
smooth degree-one lift with positive derivative, extends to a diffeomorphism of the ambient
manifold. The extension is the final map of an ambient diffeotopy which fixes every point
outside the compact collar of depth two at every time. Its final map is the prescribed product
map up to depth one. In particular the motion fixes an open neighborhood of any protected set
disjoint from that compact collar, and every time slice preserves ambient orientations.

`exists_diffeotopy_extend_boundaryCircle_of_lift` constructs this extension. It uses
`AddCircle.halfCylinderDiffeotopyOfLift` on the inward half-cylinder and
`Diffeotopy.exists_extend_of_isCompact` to extend by the identity.
`exists_diffeotopy_extend_boundaryCircles_of_lifts` treats finitely many disjoint labelled
collars simultaneously, retaining each prescribed circle parametrization on a smaller collar.
The collars are supplied as geometric data; no collar-existence theorem is assumed or proved.

## References

* M. W. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 8, §§1–2
  (extension of isotopies across collars).
* B. Farb and D. Margalit, *A Primer on Mapping Class Groups*, Section 2.1
  (degree-one lifts of orientation-preserving circle maps).
-/

public section

noncomputable section

open Set Topology
open scoped Manifold ContDiff

namespace TauCeti

variable {T : ℝ} [Fact (0 < T)] {n : ℕ∞}
  {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

/-- Extend a prescribed orientation-preserving circle map across a supplied inward collar by an
ambient diffeotopy. Its final map agrees with the product map through depth one, and the whole
motion has compact support within depth two. Disjoint protected marks or collars remain fixed. -/
theorem exists_diffeotopy_extend_boundaryCircle_of_lift
    {χ : EuclideanHalfSpace 1 × AddCircle T → M}
    (hχ : IsLocalDiffeomorph ((𝓡∂ 1).prod 𝓘(ℝ)) J n χ) (hχo : IsOpenEmbedding χ)
    {F : ℝ → ℝ} (hF : ContDiff ℝ n F) (hn : n ≠ 0)
    (hper : ∀ x, F (x + T) = F x + T) (hpos : ∀ x, 0 < deriv F x)
    {φ : AddCircle T → AddCircle T} (hφ : ∀ x : ℝ, φ x = F x) :
    ∃ (Φ : Diffeotopy J n M) (K : Set M), IsCompact K ∧
      K ⊆ χ '' ({r : EuclideanHalfSpace 1 | r.1 0 ≤ 2} ×ˢ univ) ∧
      (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      ∀ (r : EuclideanHalfSpace 1) (θ : AddCircle T), r.1 0 ≤ 1 →
        Φ.final (χ (r, θ)) = χ (r, φ θ) := by
  let Λ := AddCircle.halfCylinderDiffeotopyOfLift hF hn hper hpos
  -- In dimension one the depth coordinate is a closed embedding into the real line.
  let e : EuclideanSpace ℝ (Fin 1) ≃L[ℝ] ℝ :=
    (EuclideanSpace.equiv (Fin 1) ℝ).trans (ContinuousLinearEquiv.piUnique ℝ (fun _ : Fin 1 ↦ ℝ))
  have he : IsClosedEmbedding (fun r : EuclideanHalfSpace 1 ↦ r.1 0) :=
    e.toHomeomorph.isClosedEmbedding.comp
      (isClosed_le continuous_const (PiLp.continuous_apply 2 _ 0)).isClosedEmbedding_subtypeVal
  have hK : IsCompact {r : EuclideanHalfSpace 1 | r.1 0 ≤ 2} := by
    have heq : (fun r : EuclideanHalfSpace 1 ↦ r.1 0) ⁻¹' Icc (0 : ℝ) 2 =
        {r : EuclideanHalfSpace 1 | r.1 0 ≤ 2} := by
      ext r
      simp [r.2]
    rw [← heq]
    exact he.isCompact_preimage isCompact_Icc
  obtain ⟨Φ, hΦχ, hΦK⟩ := Λ.exists_extend_of_isCompact hχ hχo
    (hK.prod isCompact_univ) (fun t ⟨r, θ⟩ hr ↦
      AddCircle.halfCylinderDiffeotopyOfLift_apply_of_two_le hF hn hper hpos t
        (by simp only [mem_prod, mem_ofPred_eq, mem_univ, and_true] at hr; linarith) θ)
  refine ⟨Φ, _, (hK.prod isCompact_univ).image hχo.continuous, subset_rfl,
    hΦK, fun r θ hr ↦ ?_⟩
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective θ
  rw [Diffeotopy.final_apply, hΦχ, ← Diffeotopy.final_apply,
    AddCircle.halfCylinderDiffeotopyOfLift_final_apply_coe_of_le_one hF hn hper hpos hr, hφ]

/-- Prescribed orientation-preserving maps on finitely many disjoint labelled boundary collars
extend simultaneously. The ambient motion has compact support in the union of their depth-two
subcollars, and its final map agrees with each prescribed product map through depth one. -/
theorem exists_diffeotopy_extend_boundaryCircles_of_lifts {ι : Type*} [Finite ι]
    {χ : ι → EuclideanHalfSpace 1 × AddCircle T → M}
    (hχ : ∀ i, IsLocalDiffeomorph ((𝓡∂ 1).prod 𝓘(ℝ)) J n (χ i))
    (hχo : ∀ i, IsOpenEmbedding (χ i))
    (hdis : Pairwise fun i j ↦ Disjoint (range (χ i)) (range (χ j)))
    {F : ι → ℝ → ℝ} (hF : ∀ i, ContDiff ℝ n (F i)) (hn : n ≠ 0)
    (hper : ∀ i x, F i (x + T) = F i x + T) (hpos : ∀ i x, 0 < deriv (F i) x)
    {φ : ι → AddCircle T → AddCircle T} (hφ : ∀ i (x : ℝ), φ i x = F i x) :
    ∃ (Φ : Diffeotopy J n M) (K : Set M), IsCompact K ∧
      K ⊆ ⋃ i, χ i '' ({r : EuclideanHalfSpace 1 | r.1 0 ≤ 2} ×ˢ univ) ∧
      (∀ t, ∀ y ∉ K, Φ (t, y) = y) ∧
      ∀ i (r : EuclideanHalfSpace 1) (θ : AddCircle T), r.1 0 ≤ 1 →
        Φ.final (χ i (r, θ)) = χ i (r, φ i θ) := by
  let : Fintype ι := Fintype.ofFinite ι
  let W (i : ι) := χ i '' ({r : EuclideanHalfSpace 1 | r.1 0 ≤ 2} ×ˢ univ)
  have hW : (univ : Set ι).PairwiseDisjoint W := fun i _ j _ hij ↦
    (hdis hij).mono (image_subset_range _ _) (image_subset_range _ _)
  have ha (i : ι) (p : EuclideanHalfSpace 1 × AddCircle T) (hp : p.1.1 0 ≤ 1) :
      χ i p ∈ W i := ⟨p, ⟨by dsimp; linarith, mem_univ _⟩, rfl⟩
  have hb (i : ι) (p : EuclideanHalfSpace 1 × AddCircle T) (hp : p.1.1 0 ≤ 1) :
      χ i (p.1, φ i p.2) ∈ W i :=
    ⟨(p.1, φ i p.2), ⟨by dsimp; linarith, mem_univ _⟩, rfl⟩
  obtain ⟨Φ, K, hK, hKW, hΦK, hΦ⟩ :=
    exists_diffeotopy_final_comp_eqOn_of_pairwise_disjoint Finset.univ
      (by simpa only [Finset.coe_univ] using hW)
      (A := {p : EuclideanHalfSpace 1 × AddCircle T | p.1.1 0 ≤ 1})
      (a := fun i p ↦ χ i p) (b := fun i p ↦ χ i (p.1, φ i p.2))
      (fun i _ ↦ ha i) (fun i _ ↦ hb i) (fun i _ ↦ by
        obtain ⟨Φ, K, hK, hKW, hΦK, hΦ⟩ :=
          exists_diffeotopy_extend_boundaryCircle_of_lift (hχ i) (hχo i) (hF i) hn
            (hper i) (hpos i) (hφ i)
        exact ⟨Φ, K, hK, hKW, hΦK, fun p hp ↦ hΦ p.1 p.2 hp⟩)
  exact ⟨Φ, K, hK, by simpa only [Finset.mem_univ, iUnion_true] using hKW,
    hΦK, fun i r θ hr ↦ hΦ i (Finset.mem_univ _) hr⟩

end TauCeti
