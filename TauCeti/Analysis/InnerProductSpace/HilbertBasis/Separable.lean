/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Basic.Denumerable
import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic
import TauCeti.Analysis.Normed.Lp.Basic

/-!
# Separable Hilbert spaces and `ℕ`-indexed Hilbert bases

This file characterizes separable Hilbert spaces via the countability of their Hilbert bases and
identifies every complete separable infinite-dimensional Hilbert carrier (including countably
infinite Hilbert direct sums) with `ℓ²(ℕ, 𝕜)`, supplying the `ℓ²(ℕ)` carrier identifications used
for separable C⋆-algebra representations.

* `Orthonormal.dist_eq_sqrt_two` and `Orthonormal.countable`: distinct vectors in an orthonormal
  family lie at pairwise distance `√2`, so in a separable inner product space every orthonormal
  family is countable.
* `HilbertBasis.separableSpace_iff`: for a Hilbert basis `b : HilbertBasis ι 𝕜 E`, `E` is separable
  iff `ι` is countable.
* `TauCeti.nonempty_hilbertBasis_nat` and `TauCeti.nonempty_hilbertBasis_nat_iff`: combining Zorn's
  existence of a Hilbert basis (`exists_hilbertBasis`), the dimension characterization
  `HilbertBasis.infinite_iff`, and reindexing (`HilbertBasis.reindex`) along
  `nonempty_equiv_of_countable`, an inner product space admits a `ℕ`-indexed Hilbert basis iff it is
  complete, separable, and infinite-dimensional.
* `TauCeti.nonempty_linearIsometryEquiv_lp_nat` and
  `TauCeti.nonempty_linearIsometryEquiv_lp_of_infinite`: every complete separable
  infinite-dimensional Hilbert space—and in particular, via `lp.not_finiteDimensional`, every
  countably infinite Hilbert direct sum `lp F 2` of nontrivial separable Hilbert spaces—is linearly
  isometrically equivalent to `ℓ²(ℕ, 𝕜)`.

## References

* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Springer GTM 96, 1990, §I.4.
-/

public section

open TopologicalSpace
open scoped InnerProductSpace lp

section Orthonormal

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Distinct vectors in an orthonormal family lie at distance `√2`. -/
theorem Orthonormal.dist_eq_sqrt_two {v : ι → E} (hv : Orthonormal 𝕜 v) {i j : ι} (hij : i ≠ j) :
    dist (v i) (v j) = Real.sqrt 2 := by
  have hsq : ‖v i - v j‖ ^ 2 = 2 := by
    rw [@norm_sub_sq 𝕜, hv.norm_eq_one i, hv.norm_eq_one j, hv.inner_eq_zero hij, map_zero]
    norm_num
  rw [dist_eq_norm, ← Real.sqrt_sq (norm_nonneg _), hsq]

/-- In a separable inner product space, every orthonormal family is countable. -/
theorem Orthonormal.countable [SeparableSpace E] {v : ι → E} (hv : Orthonormal 𝕜 v) :
    Countable ι := by
  have hr : 0 < Real.sqrt 2 / 2 := by positivity
  exact Pairwise.countable_of_isOpen_disjoint (s := fun i ↦ Metric.ball (v i) (Real.sqrt 2 / 2))
    (fun i j hij ↦ Metric.ball_disjoint_ball (by rw [add_halves, hv.dist_eq_sqrt_two hij]))
    (fun _ ↦ Metric.isOpen_ball) (fun i ↦ ⟨v i, Metric.mem_ball_self hr⟩)

end Orthonormal

namespace HilbertBasis

variable {ι 𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A Hilbert basis of a separable space has a countable index type. -/
theorem countable [SeparableSpace E] (b : HilbertBasis ι 𝕜 E) : Countable ι :=
  b.orthonormal.countable

/-- A space admitting a countable Hilbert basis is separable. -/
theorem separableSpace [Countable ι] (b : HilbertBasis ι 𝕜 E) : SeparableSpace E := by
  have : SeparableSpace (lp (fun _ : ι ↦ 𝕜) 2) := lp.separableSpace (by simp)
  exact b.repr.symm.surjective.denseRange.separableSpace b.repr.symm.continuous

/-- For a space with a Hilbert basis `b : HilbertBasis ι 𝕜 E`, separability of `E` is equivalent
to countability of `ι`. -/
theorem separableSpace_iff (b : HilbertBasis ι 𝕜 E) : SeparableSpace E ↔ Countable ι :=
  ⟨fun _ ↦ b.countable, fun _ ↦ b.separableSpace⟩

end HilbertBasis

namespace TauCeti

variable (𝕜 E : Type*) [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- Every complete separable infinite-dimensional Hilbert space admits a Hilbert basis indexed by
`ℕ`. -/
theorem nonempty_hilbertBasis_nat [CompleteSpace E] [SeparableSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) : Nonempty (HilbertBasis ℕ 𝕜 E) := by
  obtain ⟨s, b, -⟩ := exists_hilbertBasis 𝕜 E
  have : Countable s := b.countable
  have : Infinite s := b.infinite_iff.2 hE
  obtain ⟨e⟩ := nonempty_equiv_of_countable (α := s) (β := ℕ)
  exact ⟨b.reindex e⟩

/-- An inner product space over `ℝ` or `ℂ` admits a `ℕ`-indexed Hilbert basis if and only if it is
complete, separable, and infinite-dimensional. -/
theorem nonempty_hilbertBasis_nat_iff :
    Nonempty (HilbertBasis ℕ 𝕜 E) ↔
      CompleteSpace E ∧ SeparableSpace E ∧ ¬ FiniteDimensional 𝕜 E := by
  refine ⟨fun ⟨b⟩ ↦ ⟨b.completeSpace, b.separableSpace, b.infinite_iff.1 inferInstance⟩, ?_⟩
  rintro ⟨_, _, hE⟩
  exact nonempty_hilbertBasis_nat 𝕜 E hE

/-- Every complete separable infinite-dimensional Hilbert space is linearly isometrically
equivalent to `ℓ²(ℕ, 𝕜)`. -/
theorem nonempty_linearIsometryEquiv_lp_nat [CompleteSpace E] [SeparableSpace E]
    (hE : ¬ FiniteDimensional 𝕜 E) : Nonempty (E ≃ₗᵢ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) :=
  let ⟨b⟩ := nonempty_hilbertBasis_nat 𝕜 E hE
  ⟨b.repr⟩

/-- The Hilbert direct sum `lp F 2` of a countably infinite family of nontrivial separable Hilbert
spaces is linearly isometrically equivalent to `ℓ²(ℕ, 𝕜)`. -/
theorem nonempty_linearIsometryEquiv_lp_of_infinite {ι : Type*} [Countable ι] [Infinite ι]
    (F : ι → Type*) [∀ i, NormedAddCommGroup (F i)] [∀ i, InnerProductSpace 𝕜 (F i)]
    [∀ i, CompleteSpace (F i)] [∀ i, SeparableSpace (F i)] [∀ i, Nontrivial (F i)] :
    Nonempty (lp F 2 ≃ₗᵢ[𝕜] lp (fun _ : ℕ ↦ 𝕜) 2) := by
  have : SeparableSpace (lp F 2) := lp.separableSpace (by simp)
  exact nonempty_linearIsometryEquiv_lp_nat 𝕜 (lp F 2) lp.not_finiteDimensional

end TauCeti
