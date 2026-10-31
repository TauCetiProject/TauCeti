/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.CriticalPoints
public import TauCeti.Geometry.Manifold.Morse.Stable.Breaking
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import TauCeti.Geometry.Manifold.Morse.Stable.LevelSlice

/-!
# The mod-two Morse boundary on a compact manifold

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a pseudo-gradient field
adapted to `f` satisfying the Morse–Smale condition. The mod-two Morse chains are the finitely
supported `ZMod 2`-valued functions on the critical points of `f`. The coefficient of `q` in the
boundary of `p` counts, modulo two, the trajectories of `X` from `p` to `q` when
`ind p = ind q + 1`, and is zero otherwise.

A trajectory from `p` to `q` is represented by its unique point on the level `(f p + f q) / 2`
halfway between the critical values. When the indices differ by one, these points form a finite
set (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.finite_morseTrajectorySlice`). This combines
the finiteness of the index-one level slices strictly between the critical values with the
observation that the slice is empty unless `f q < f p`. The boundary is the linear extension of
the resulting counts. Showing that it squares to zero needs the compactification and gluing of
index-two trajectory spaces, and is not asserted here; see
`TauCeti.Geometry.Manifold.Morse.Boundary.Square` for its reduction to counting broken
trajectories.

This is the manifold form of `TauCeti.Analysis.Calculus.Morse.Boundary.Basic`, which treats the
negative-gradient flow of a function with compact sublevels on a vector space. On a compact
manifold, the critical points of a Morse function are finite in number, so no sublevel
hypothesis is needed.

## Main declarations

In the namespace `TauCeti.IsAdaptedPseudoGradient`:

* `morseTrajectorySlice`: the points of the trajectories from `p` to `q` on the middle level.
* `IsMorseSmale.finite_morseTrajectorySlice`: for consecutive indices it is finite.
* `IsMorseSmale.morseBoundaryCoeff`: the coefficient of `q` in the boundary of `p`.
* `IsMorseSmale.morseBoundary`: the mod-two Morse boundary, an endomorphism of the free
  `ZMod 2`-module on the critical points.
* `IsMorseSmale.morseBoundary_single_apply`: the boundary of a critical point has the trajectory
  counts as coefficients.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the Morse complex).
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

/-- The points on the level `(f p + f q) / 2` of the trajectories of an adapted pseudo-gradient
from `p` to `q`. For distinct critical points `p` and `q`, every trajectory from `p` to `q`
crosses this level exactly once, so the set stands for the unparametrized trajectories. -/
noncomputable def morseTrajectorySlice (p q : M) : Set M :=
  hX.flow.unstableSet p ∩ hX.flow.stableSet q ∩ {z | f z = (f p + f q) / 2}

/-- Membership in the middle-level trajectory slice. -/
@[simp]
theorem mem_morseTrajectorySlice {p q z : M} :
    z ∈ hX.morseTrajectorySlice p q ↔
      z ∈ hX.flow.unstableSet p ∧ z ∈ hX.flow.stableSet q ∧ f z = (f p + f q) / 2 := by
  simp only [morseTrajectorySlice, mem_inter_iff, mem_ofPred_eq, and_assoc]

/-- The middle-level slice of trajectories between distinct points is empty unless the value of
`f` drops strictly from the source to the target. -/
theorem value_lt_of_mem_morseTrajectorySlice (hf : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f) {p q z : M}
    (hpq : p ≠ q) (hz : z ∈ hX.morseTrajectorySlice p q) : f q < f p := by
  rw [mem_morseTrajectorySlice] at hz
  have h := hX.mem_Ioo_of_mem_unstableSet_inter_stableSet hf hpq ⟨hz.1, hz.2.1⟩
  exact h.1.trans h.2

omit hX in
/-- **Finitely many trajectories between critical points of consecutive index.** Under the
Morse–Smale condition, if `ind p = ind q + 1`, then the middle-level slice of trajectories from
`p` to `q` is finite. -/
theorem IsMorseSmale.finite_morseTrajectorySlice {hX : IsAdaptedPseudoGradient f X}
    (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f) {p q : M}
    (hp : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f p = 0) (hq : mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f q = 0)
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    (hX.morseTrajectorySlice p q).Finite := by
  by_cases hqp : f q < f p
  · rw [morseTrajectorySlice]
    exact h.finite_unstableSet_inter_stableSet_inter_level hf hp hq hind
      ⟨by linarith, by linarith⟩
  · have hpq : p ≠ q := by
      rintro rfl
      omega
    exact finite_empty.subset fun z hz ↦
      hqp (hX.value_lt_of_mem_morseTrajectorySlice (hf.contMDiff.mdifferentiable (by simp)) hpq hz)

namespace IsMorseSmale

variable {hX : IsAdaptedPseudoGradient f X} (h : hX.IsMorseSmale) (hf : IsMorse 𝓘(ℝ, E) f)

/-- The coefficient of the critical point `q` in the mod-two Morse boundary of the critical point
`p`: the number of trajectories from `p` to `q` modulo two when `ind p = ind q + 1`, and `0`
otherwise. The finiteness of the trajectory slice enters the definition, so no infinite slice is
silently counted as zero. -/
noncomputable def morseBoundaryCoeff (p q : criticalPoints 𝓘(ℝ, E) f) : ZMod 2 :=
  if hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 then
    (h.finite_morseTrajectorySlice hf (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2) hind).toFinset.card
  else 0

/-- For critical points of consecutive index, the boundary coefficient is the number of
trajectories, read on the middle level, modulo two. -/
theorem morseBoundaryCoeff_eq_ncard {p q : criticalPoints 𝓘(ℝ, E) f}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    h.morseBoundaryCoeff hf p q = ((hX.morseTrajectorySlice p q).ncard : ZMod 2) := by
  rw [morseBoundaryCoeff, dite_eq_left hind, ncard_eq_toFinset_card _
    (h.finite_morseTrajectorySlice hf (mem_criticalPoints_iff_mfderiv_eq_zero.1 p.2)
      (mem_criticalPoints_iff_mfderiv_eq_zero.1 q.2) hind)]

/-- The boundary coefficient vanishes between critical points whose indices do not differ by
one. -/
@[simp]
theorem morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one {p q : criticalPoints 𝓘(ℝ, E) f}
    (hind : manifoldMorseIndex 𝓘(ℝ, E) f p ≠ manifoldMorseIndex 𝓘(ℝ, E) f q + 1) :
    h.morseBoundaryCoeff hf p q = 0 := by
  rw [morseBoundaryCoeff, dite_eq_right hind]

/-- A nonzero boundary coefficient joins critical points whose indices differ by one. -/
theorem morseIndex_eq_add_one_of_morseBoundaryCoeff_ne_zero {p q : criticalPoints 𝓘(ℝ, E) f}
    (hpq : h.morseBoundaryCoeff hf p q ≠ 0) :
    manifoldMorseIndex 𝓘(ℝ, E) f p = manifoldMorseIndex 𝓘(ℝ, E) f q + 1 := by
  by_contra hind
  exact hpq (h.morseBoundaryCoeff_eq_zero_of_morseIndex_ne_add_one hf hind)

/-- A nonzero boundary coefficient joins critical points with strictly decreasing critical
value. -/
theorem value_lt_of_morseBoundaryCoeff_ne_zero {p q : criticalPoints 𝓘(ℝ, E) f}
    (hpq : h.morseBoundaryCoeff hf p q ≠ 0) : f q < f p := by
  have hind := h.morseIndex_eq_add_one_of_morseBoundaryCoeff_ne_zero hf hpq
  rw [h.morseBoundaryCoeff_eq_ncard hf hind] at hpq
  obtain ⟨z, hz⟩ := nonempty_of_ncard_ne_zero fun h0 ↦ hpq (by rw [h0, Nat.cast_zero])
  have hne : (p : M) ≠ q := fun he ↦ by
    rw [he] at hind
    omega
  exact hX.value_lt_of_mem_morseTrajectorySlice (hf.contMDiff.mdifferentiable (by simp)) hne hz

/-- The boundary coefficient vanishes unless the critical value drops. -/
theorem morseBoundaryCoeff_eq_zero_of_value_le {p q : criticalPoints 𝓘(ℝ, E) f}
    (hpq : f p ≤ f q) : h.morseBoundaryCoeff hf p q = 0 := by
  by_contra hne
  exact (h.value_lt_of_morseBoundaryCoeff_ne_zero hf hne).not_ge hpq

/-- **The mod-two Morse boundary.** The `ZMod 2`-linear endomorphism of the free module on the
critical points of `f` sending a critical point `p` to the sum of the critical points `q` with
`ind q = ind p - 1`, each weighted by the number of trajectories from `p` to `q` modulo two. -/
noncomputable def morseBoundary :
    (criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) →ₗ[ZMod 2] (criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2) :=
  haveI := hf.finite_criticalPoints.to_subtype
  Finsupp.linearCombination (ZMod 2) fun p ↦
    Finsupp.ofSupportFinite (h.morseBoundaryCoeff hf p) (toFinite _)

/-- The coefficient of `q` in the Morse boundary of a chain `c` is the sum over the critical
points `p` of `c p` times the boundary coefficient `morseBoundaryCoeff`: the number of
trajectories from `p` to `q` modulo two when `ind p = ind q + 1`, and zero otherwise. -/
theorem morseBoundary_apply (c : criticalPoints 𝓘(ℝ, E) f →₀ ZMod 2)
    (q : criticalPoints 𝓘(ℝ, E) f) :
    h.morseBoundary hf c q = c.sum fun p a ↦ a * h.morseBoundaryCoeff hf p q := by
  simp [morseBoundary, Finsupp.linearCombination_apply, Finsupp.ofSupportFinite_coe]

/-- The coefficient of `q` in the Morse boundary of `a • p` is `a` times the boundary
coefficient `morseBoundaryCoeff`: the number of trajectories from `p` to `q` modulo two when
`ind p = ind q + 1`, and zero otherwise. -/
@[simp]
theorem morseBoundary_single_apply (p q : criticalPoints 𝓘(ℝ, E) f) (a : ZMod 2) :
    h.morseBoundary hf (Finsupp.single p a) q = a * h.morseBoundaryCoeff hf p q := by
  rw [morseBoundary_apply, Finsupp.sum_single_index (zero_mul _)]

end IsMorseSmale

end IsAdaptedPseudoGradient

end TauCeti
