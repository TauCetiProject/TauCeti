/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Adjoint
public import TauCeti.Analysis.Fredholm.Zero
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Dimension

/-!
# Fredholm operators and Hilbert dimension

A Fredholm operator between Hilbert spaces changes the space only by finite-dimensional pieces: it
maps the orthogonal complement of its finite-dimensional kernel isomorphically onto its closed
range, whose orthogonal complement is finite-dimensional. Since the Hilbert dimension
(`TauCeti.hilbertDim`) is invariant under continuous linear equivalences and additive on
orthogonal decompositions, an infinite-dimensional Hilbert space has the same Hilbert dimension as
every Hilbert space it maps to by a Fredholm operator.

This determines exactly when Fredholm operators `E →L[𝕜] F` exist. If both spaces are
finite-dimensional, every operator is Fredholm. If exactly one is, there is none
(`ContinuousLinearMap.IsFredholm.finiteDimensional_iff`). If both are infinite-dimensional, a
Fredholm operator exists if and only if `E` and `F` have the same Hilbert dimension, in which case
a unitary equivalence is one. The Hamel rank is not the right invariant here: `ℓ²(ℕ, ℂ)` and
`ℓ²(ℝ, ℂ)` both have Hamel rank the continuum, but Hilbert dimensions `ℵ₀` and the continuum, so
there is no Fredholm operator between them.

## Main results

* `ContinuousLinearMap.lift_hilbertDim_range_add_hilbertDim_ker`: rank–nullity for Hilbert
  dimension; an operator with closed range satisfies
  `hilbertDim (range T) + hilbertDim (ker T) = hilbertDim E`.
* `ContinuousLinearMap.IsFredholm.lift_hilbertDim_eq`: a Fredholm operator out of an
  infinite-dimensional Hilbert space joins spaces of the same Hilbert dimension.
* `ContinuousLinearMap.nonempty_isFredholm_iff`: the Fredholm locus
  `{T : E →L[𝕜] F // T.IsFredholm}` is nonempty if and only if both spaces are finite-dimensional
  or they have the same Hilbert dimension.

## References

* D. S. Freed, *The Atiyah–Singer index theorem*, Bull. Amer. Math. Soc. **58** (2021), 517–566,
  arXiv:2107.03557, §3.
* J. B. Conway, *A Course in Functional Analysis*, 2nd ed., Chapter I, §§4–5.
-/

public section

open Cardinal TauCeti
open scoped lp

universe u v

namespace ContinuousLinearMap

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **Rank–nullity for Hilbert dimension.** For an operator `T : E →L[𝕜] F` between Hilbert spaces
with closed (equivalently, complete) range, the Hilbert dimensions of its range and kernel add up
to that of `E`. -/
theorem lift_hilbertDim_range_add_hilbertDim_ker (T : E →L[𝕜] F)
    [CompleteSpace (LinearMap.range (T : E →ₗ[𝕜] F))] :
    lift.{u} (hilbertDim 𝕜 (LinearMap.range (T : E →ₗ[𝕜] F))) +
        lift.{v} (hilbertDim 𝕜 (LinearMap.ker (T : E →ₗ[𝕜] F))) =
      lift.{v} (hilbertDim 𝕜 E) := by
  have hT : IsClosed (LinearMap.range (T : E →ₗ[𝕜] F) : Set F) :=
    (completeSpace_coe_iff_isComplete.1 ‹_›).isClosed
  rw [← (T.orthogonalKerEquivRange hT).lift_hilbertDim_eq, ← lift_add, add_comm,
    Submodule.hilbertDim_add_hilbertDim_orthogonal]

/-- A Fredholm operator out of an infinite-dimensional Hilbert space `E` joins spaces of the same
Hilbert dimension. -/
theorem IsFredholm.lift_hilbertDim_eq {T : E →L[𝕜] F} (hT : T.IsFredholm)
    (hE : ¬ FiniteDimensional 𝕜 E) :
    lift.{v} (hilbertDim 𝕜 E) = lift.{u} (hilbertDim 𝕜 F) := by
  set R := LinearMap.range (T : E →ₗ[𝕜] F)
  have : CompleteSpace R := hT.isClosed_range.completeSpace_coe
  have := hT.finite_ker
  have : FiniteDimensional 𝕜 Rᗮ :=
    Module.Finite.iff_fg.2 (hT.finite_coker.fg_of_isCompl R.isCompl_orthogonal)
  have hdomain := T.lift_hilbertDim_range_add_hilbertDim_ker
  have hcodomain := R.hilbertDim_add_hilbertDim_orthogonal
  rw [hilbertDim_eq_finrank (E := LinearMap.ker (T : E →ₗ[𝕜] F)), lift_natCast] at hdomain
  rw [hilbertDim_eq_finrank (E := Rᗮ)] at hcodomain
  -- The range has infinite Hilbert dimension, since adding a finite cardinal to it gives that of
  -- the infinite-dimensional space `E`.
  have hR : ℵ₀ ≤ lift.{u} (hilbertDim 𝕜 R) := by
    by_contra! h
    have hE' : ℵ₀ ≤ lift.{v} (hilbertDim 𝕜 E) :=
      aleph0_le_lift.2 (aleph0_le_hilbertDim_iff.2 hE)
    exact (hdomain ▸ hE').not_gt (add_lt_aleph0 h natCast_lt_aleph0)
  rw [← hdomain, ← hcodomain, lift_add, lift_natCast, add_nat_eq _ hR, add_nat_eq _ hR]

/-- **Nonemptiness of the Fredholm locus.** Between Hilbert spaces `E` and `F` over `𝕜`, a Fredholm
operator `E →L[𝕜] F` exists if and only if both spaces are finite-dimensional or they have the same
Hilbert dimension. -/
theorem nonempty_isFredholm_iff :
    Nonempty {T : E →L[𝕜] F // T.IsFredholm} ↔
      FiniteDimensional 𝕜 E ∧ FiniteDimensional 𝕜 F ∨
        lift.{v} (hilbertDim 𝕜 E) = lift.{u} (hilbertDim 𝕜 F) := by
  refine ⟨fun ⟨T, hT⟩ ↦ ?_, ?_⟩
  · by_cases hE : FiniteDimensional 𝕜 E
    · exact .inl ⟨hE, hT.finiteDimensional_iff.1 hE⟩
    · exact .inr (hT.lift_hilbertDim_eq hE)
  · rintro (⟨hE, hF⟩ | h)
    · exact instNonemptyIsFredholmOfFiniteDimensional
    · obtain ⟨e⟩ := nonempty_linearIsometryEquiv_iff_lift_hilbertDim_eq.2 h
      exact ⟨⟨e.toContinuousLinearEquiv, e.toContinuousLinearEquiv.isFredholm⟩⟩

/-- `ℓ²(ℕ, ℂ)` and `ℓ²(ℝ, ℂ)` have the same Hamel rank, but there is no Fredholm operator between
them, since their Hilbert dimensions `ℵ₀` and `𝔠` differ. -/
example : IsEmpty {T : ℓ²(ℕ, ℂ) →L[ℂ] ℓ²(ℝ, ℂ) // T.IsFredholm} := by
  rw [← not_nonempty_iff, nonempty_isFredholm_iff]
  rintro (⟨h, -⟩ | h)
  · exact aleph0_le_hilbertDim_iff.1 (by simp) h
  · simp [Cardinal.mk_real, Cardinal.aleph0_lt_continuum.ne] at h

end ContinuousLinearMap
