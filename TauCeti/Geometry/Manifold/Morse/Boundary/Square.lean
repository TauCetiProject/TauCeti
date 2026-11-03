/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Basic

/-!
# The square of the mod-two Morse boundary on a compact manifold counts broken trajectories

Let `f` be a Morse function on a compact boundaryless manifold and `X` an adapted pseudo-gradient
satisfying the Morse–Smale condition. For critical points `p` and `r` whose Morse indices differ by
two, a *broken trajectory* from `p` to `r` is a pair of trajectories, from `p` to a critical point
`q` of the intermediate index and from `q` to `r`. Representing each component by its point on the
middle level between its ends, the broken trajectories form the set
`TauCeti.IsAdaptedPseudoGradient.morseBrokenTrajectorySet` of triples `(q, z₁, z₂)`.

This set is finite, and the `r`-coefficient of `∂ (∂ p)` is its cardinality modulo two.
Consequently `∂ ∘ ∂ = 0` holds exactly when every set of broken index-two trajectories has even
cardinality. This is the algebraic half of `∂² = 0`. The geometric half, that broken trajectories
are the boundary points of a compact one-dimensional manifold of trajectories and therefore come in
pairs, needs the compactification and gluing of index-two trajectory spaces and is not proved here.

This is the manifold form of `TauCeti.Analysis.Calculus.Morse.Boundary.Square`.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseBrokenTrajectorySet`: the broken index-two trajectories from `p` to `r`.
* `IsMorseSmale.finite_morseBrokenTrajectorySet`: there are finitely many.
* `IsMorseSmale.morseBoundary_morseBoundary_single_apply`: the coefficients of `∂ (∂ p)` count
  broken trajectories modulo two.
* `IsMorseSmale.morseBoundary_comp_morseBoundary_eq_zero_iff`: `∂ ∘ ∂ = 0` exactly when every set
  of broken trajectories has even cardinality.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex): the proof that `∂ ∘ ∂ = 0` counts the coefficient of `r` in
  `∂ (∂ p)` as the number of broken trajectories from `p` to `r`.
-/

public section

open Set
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [CompactSpace M] [T2Space M]
  {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

namespace IsAdaptedPseudoGradient

variable (hX : IsAdaptedPseudoGradient f X)

/-- The broken index-two trajectories from `p` to `r`: triples `(q, z₁, z₂)` of a critical point
`q` whose Morse index lies one below that of `p` and one above that of `r`, a point `z₁` on the
middle-level slice of trajectories from `p` to `q`, and a point `z₂` on the middle-level slice of
trajectories from `q` to `r`. -/
def morseBrokenTrajectorySet (p r : M) : Set (criticalPoints 𝓘(ℝ, E) f × M × M) :=
  {x | manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x.1 + 1 ∧
    manifoldMorseIndex 𝓘(ℝ, E) f x.1 = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
    x.2.1 ∈ hX.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ hX.morseTrajectorySlice x.1 r}

/-- Membership in the set of broken index-two trajectories. -/
@[simp]
theorem mem_morseBrokenTrajectorySet {p r : M} {x : criticalPoints 𝓘(ℝ, E) f × M × M} :
    x ∈ hX.morseBrokenTrajectorySet p r ↔
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f x.1 + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f x.1 = manifoldMorseIndex 𝓘(ℝ, E) f r + 1 ∧
          x.2.1 ∈ hX.morseTrajectorySlice p x.1 ∧ x.2.2 ∈ hX.morseTrajectorySlice x.1 r :=
  Iff.rfl

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

include h hf in
/-- **Finitely many broken trajectories.** Under the Morse–Smale condition, there are finitely
many broken index-two trajectories between two critical points. -/
theorem finite_morseBrokenTrajectorySet (p r : criticalPoints 𝓘(ℝ, E) f) :
    (hX.morseBrokenTrajectorySet p r).Finite := by
  have := hf.finite_criticalPoints.to_subtype
  have hcrit := fun a : criticalPoints 𝓘(ℝ, E) f ↦ mem_criticalPoints_iff_mfderiv_eq_zero.1 a.2
  -- Sort the broken trajectories by their intermediate critical point `q`.
  refine ((toFinite {q : criticalPoints 𝓘(ℝ, E) f |
      manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
        manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1}).biUnion
    fun q hq ↦ ((h.finite_morseTrajectorySlice hf (hcrit p) (hcrit q) hq.1).prod
      (h.finite_morseTrajectorySlice hf (hcrit q) (hcrit r) hq.2)).image (Prod.mk q)).subset
    fun x hx ↦ mem_biUnion ⟨hx.1, hx.2.1⟩ ⟨x.2, ⟨hx.2.2.1, hx.2.2.2⟩, rfl⟩

/-- **`∂ ∘ ∂` counts broken trajectories.** The `r`-coefficient of the boundary of the boundary
of a critical point `p` is the number of broken index-two trajectories from `p` to `r`, modulo
two. -/
theorem morseBoundary_morseBoundary_single_apply (p r : criticalPoints 𝓘(ℝ, E) f) :
    h.morseBoundary hf (h.morseBoundary hf (Finsupp.single p 1)) r =
      ((hX.morseBrokenTrajectorySet p r).ncard : ZMod 2) := by
  classical
  have := hf.finite_criticalPoints.to_subtype
  have := Fintype.ofFinite (criticalPoints 𝓘(ℝ, E) f)
  have hfin := h.finite_morseBrokenTrajectorySet hf p r
  -- Sort the broken trajectories by their intermediate critical point `q`.
  rw [morseBoundary_apply, Finsupp.sum_fintype _ _ fun _ ↦ zero_mul _,
    ncard_eq_toFinset_card _ hfin,
    Finset.card_eq_sum_card_fiberwise fun x _ ↦ Finset.mem_univ x.1, Nat.cast_sum]
  refine Finset.sum_congr rfl fun q _ ↦ ?_
  -- The fiber over `q` is a copy of the pairs of trajectories through `q`.
  rw [morseBoundary_single_apply, one_mul, ← ncard_coe_finset, Finset.coe_filter,
    ← ncard_preimage_of_injective_subset_range (Prod.mk_right_injective q) ?_]
  swap
  · rintro ⟨_, z⟩ ⟨-, rfl⟩
    exact ⟨z, rfl⟩
  by_cases hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 ∧
      manifoldMorseIndex 𝓘(ℝ, E) f q = manifoldMorseIndex 𝓘(ℝ, E) f r + 1
  · rw [h.morseBoundaryCoeff_eq_ncard hf hind.1, h.morseBoundaryCoeff_eq_ncard hf hind.2,
      ← Nat.cast_mul, ← ncard_prod]
    congr 2
    ext
    simp [hind]
  · rcases not_and_or.mp hind with hpq | hqr
    · simp [hpq]
    · simp [hqr]

/-- **`∂² = 0` reduces to counting broken trajectories.** The mod-two Morse boundary squares to
zero exactly when, between any two critical points, the number of broken index-two trajectories
is even. -/
theorem morseBoundary_comp_morseBoundary_eq_zero_iff :
    h.morseBoundary hf ∘ₗ h.morseBoundary hf = 0 ↔
      ∀ p r : criticalPoints 𝓘(ℝ, E) f, Even (hX.morseBrokenTrajectorySet p r).ncard := by
  simp_rw [← ZMod.natCast_eq_zero_iff_even, ← h.morseBoundary_morseBoundary_single_apply hf]
  constructor
  · intro h0 p r
    simpa using DFunLike.congr_fun (LinearMap.congr_fun h0 (Finsupp.single p 1)) r
  · intro h0
    refine Finsupp.lhom_ext fun p a ↦ Finsupp.ext fun r ↦ ?_
    -- Over `ZMod 2`, the boundary of `a • p` is `a` times the boundary of `p`.
    rw [LinearMap.comp_apply, ← Finsupp.smul_single_one, map_smul, map_smul]
    simp [h0]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
