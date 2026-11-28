/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.MomentMap.MorseBott
import TauCeti.Geometry.Manifold.Morse.Bott.Level

/-!
# Connected levels of the components of a moment map

Let a compact Lie group `G` act smoothly on a compact connected manifold `M`, preserving a
nondegenerate two-form `σ`, with moment map `μ : M → 𝔤*`. For `ξ ∈ 𝔤` the component
`μ^ξ = ⟨μ, ξ⟩` is a Morse–Bott function whose critical submanifolds are the fixed sets
`M^{T_ξ}_d` of the closure `T_ξ` of `{exp (t ξ)}`
(`IsMomentMap.exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank_of_compactSpace` in
the namespace `TauCeti.SmoothTwoForm`), and its Morse index and coindex at every critical point are
even (`TauCeti.SmoothTwoForm.IsMomentMap.even_manifoldMorseIndex`,
`TauCeti.SmoothTwoForm.IsMomentMap.even_manifoldMorseIndex_neg`), so never one. Hence every critical
point lies in a convexity chart of `μ^ξ`
(`TauCeti.SmoothEmbedding.IsNondegenerateCriticalSubmanifold.exists_isConvexChart`), and **every
level set of `μ^ξ` is connected**, critical levels included
(`TauCeti.SmoothTwoForm.IsMomentMap.isPreconnected_setOf_apply_eq`). This holds for irrational as
well as rational directions `ξ`, and neither closedness of `σ` nor equivariance of `μ` is used.
The same convexity charts show that a critical point at which `μ^ξ` has Morse index zero, a local
minimum by the Morse–Bott lemma, is a global minimum
(`TauCeti.SmoothTwoForm.IsMomentMap.isMinOn_of_manifoldMorseIndex_eq_zero`).

## Main results

* `TauCeti.SmoothTwoForm.IsMomentMap.isPreconnected_setOf_apply_eq`: the levels of the components
  of the moment map of a compact group action on a compact connected manifold are preconnected.
* `TauCeti.SmoothTwoForm.IsMomentMap.isMinOn_of_manifoldMorseIndex_eq_zero`: a critical point of
  Morse index zero of such a component, for instance one with positive semidefinite Hessian, is a
  global minimum.

## References

* M. F. Atiyah, *Convexity and commuting Hamiltonians*, Bull. London Math. Soc. 14 (1982), 1–15,
  § 2 (the levels of the components of a moment map are connected).
* V. Guillemin and S. Sternberg, *Convexity properties of the moment mapping*, Invent. Math. 67
  (1982), 491–513, § 3.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, § 27.1 and Homework 21.
-/

public section

open Filter Set Topology
open scoped ContDiff Manifold

namespace TauCeti.SmoothTwoForm.IsMomentMap

attribute [local instance] LieGroup.minSmoothness_of_isRCLikeNormedField
attribute [local instance] ContMDiffMul.boundarylessManifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G] [T2Space G]
  [IsTopologicalGroup G] [CompactSpace G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {M : Type*} [TopologicalSpace M] [ChartedSpace E' M] [IsManifold 𝓘(ℝ, E') ∞ M] [T2Space M]
  [CompactSpace M] [PreconnectedSpace M] [MulAction G M] [ContMDiffSMul I 𝓘(ℝ, E') ∞ G M]
  {σ : SmoothTwoForm 𝓘(ℝ, E') M} {μ : M → Module.Dual ℝ (GroupLieAlgebra I G)}

omit [PreconnectedSpace M] in
/-- At a critical point `x` of a moment map component `μ^ξ`, which lies on one of the Morse–Bott
critical submanifolds `M^{T_ξ}_d`, the component has a convexity chart, and a local minimum if its
Morse index at `x` is zero. -/
private theorem exists_isConvexChart_and_isLocalMin
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ (a : G) (x : M) (u v : TangentSpace 𝓘(ℝ, E') x),
      σ.eval₂ (a • x) (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x u)
        (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x v) = σ.eval₂ x u v)
    (ξ : GroupLieAlgebra I G) {x : M} (hx : x ∈ criticalPoints 𝓘(ℝ, E') fun y ↦ μ y ξ) :
    (∃ U, x ∈ U ∧ IsConvexChart (fun y ↦ μ y ξ) U) ∧
      (manifoldMorseIndex 𝓘(ℝ, E') (fun y ↦ μ y ξ) x = 0 → IsLocalMin (fun y ↦ μ y ξ) x) := by
  have hf : ContMDiff 𝓘(ℝ, E') 𝓘(ℝ) ∞ fun y ↦ μ y ξ := h.contMDiff ξ
  -- A critical point lies on one of the Morse–Bott critical submanifolds `M^{T_ξ}_d`.
  obtain ⟨d, hd⟩ := mem_iUnion.1 (h.criticalPoints_eq_iUnion_fixedPointsOfFinrank hσ ξ ▸ hx)
  -- The fixed tangent subspace at `x`, of dimension `d`, is a subspace of the model `E'`, which is
  -- the tangent space `T_x M` by definition.
  let L : Submodule ℝ E' := fixedTangentSubspace 𝓘(ℝ, E') (Lie.closedOneParameterSubgroup ξ) x
  obtain ⟨C, -, hemb, hcrit, -⟩ :=
    h.exists_isNondegenerateCriticalSubmanifold_fixedPointsOfFinrank_of_compactSpace hσ
      (L := L) (by exact (mem_fixedPointsOfFinrank.1 hd).2)
  -- The charted-space structure `C` on `M^{T_ξ}_d` (modelled on `L`) is only given by the
  -- existential above, so instance search cannot find it: install it as a local instance.
  let := C
  have hix : SmoothEmbedding.ofIsSmoothEmbedding _ hemb ⟨x, hd⟩ = x := by
    rw [SmoothEmbedding.coe_ofIsSmoothEmbedding]
  have hf3 : ∀ᶠ y in 𝓝 (SmoothEmbedding.ofIsSmoothEmbedding _ hemb ⟨x, hd⟩),
      ContMDiffAt 𝓘(ℝ, E') 𝓘(ℝ) 3 (fun y ↦ μ y ξ) y :=
    Eventually.of_forall fun y ↦ (hf y).of_le (by simp)
  refine ⟨?_, fun h0 ↦ ?_⟩
  · have := hcrit.exists_isConvexChart (s := ⟨x, hd⟩) (by simp) hf3
      (fun h1 ↦ Nat.not_even_one (h1 ▸ h.even_manifoldMorseIndex hσ hσG (by rw [hix]; exact hx)))
      (fun h1 ↦ Nat.not_even_one
        (h1 ▸ h.even_manifoldMorseIndex_neg hσ hσG (by rw [hix]; exact hx)))
    rwa [hix] at this
  · have := hcrit.isLocalMin_of_manifoldMorseIndex_eq_zero (s := ⟨x, hd⟩) (by simp) hf3
      (by rw [hix]; exact h0)
    rwa [hix] at this

/-- **The levels of a moment map component are connected.** Let a compact Lie group `G` act
smoothly on a compact connected boundaryless finite-dimensional manifold `M`, preserving a
nondegenerate two-form `σ`, with moment map `μ`. Then for every `ξ` in the Lie algebra of `G` and
every `c`, the level set `{x | ⟨μ x, ξ⟩ = c}` is preconnected, so connected when nonempty. -/
theorem isPreconnected_setOf_apply_eq
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ (a : G) (x : M) (u v : TangentSpace 𝓘(ℝ, E') x),
      σ.eval₂ (a • x) (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x u)
        (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x v) = σ.eval₂ x u v)
    (ξ : GroupLieAlgebra I G) (c : ℝ) :
    IsPreconnected {x | μ x ξ = c} :=
  isPreconnected_preimage_singleton_of_forall_mem_criticalPoints_exists_isConvexChart
    ((h.contMDiff ξ).of_le (by simp))
    (fun _ hx ↦ (h.exists_isConvexChart_and_isLocalMin hσ hσG ξ hx).1) c

/-- **A critical point of index zero of a moment map component is a global minimum.** Let a compact
Lie group `G` act smoothly on a compact connected boundaryless finite-dimensional manifold `M`,
preserving a nondegenerate two-form `σ`, with moment map `μ`. If `x` is a critical point of a
component `μ^ξ` at which its Morse index is zero, for instance one at which its Hessian is positive
semidefinite, then `μ^ξ` attains its minimum at `x`. -/
theorem isMinOn_of_manifoldMorseIndex_eq_zero
    (h : σ.IsMomentMap (InfinitesimalAction.fundamental I G 𝓘(ℝ, E') M) μ)
    (hσ : σ.IsNondegenerate)
    (hσG : ∀ (a : G) (x : M) (u v : TangentSpace 𝓘(ℝ, E') x),
      σ.eval₂ (a • x) (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x u)
        (mfderiv 𝓘(ℝ, E') 𝓘(ℝ, E') (a • ·) x v) = σ.eval₂ x u v)
    {ξ : GroupLieAlgebra I G} {x : M} (hx : x ∈ criticalPoints 𝓘(ℝ, E') fun y ↦ μ y ξ)
    (h0 : manifoldMorseIndex 𝓘(ℝ, E') (fun y ↦ μ y ξ) x = 0) :
    IsMinOn (fun y ↦ μ y ξ) univ x :=
  isMinOn_of_isLocalMin_of_forall_mem_criticalPoints_exists_isConvexChart
    ((h.contMDiff ξ).of_le (by simp))
    (fun _ hy ↦ (h.exists_isConvexChart_and_isLocalMin hσ hσG ξ hy).1)
    ((h.exists_isConvexChart_and_isLocalMin hσ hσG ξ hx).2 h0)

end TauCeti.SmoothTwoForm.IsMomentMap
