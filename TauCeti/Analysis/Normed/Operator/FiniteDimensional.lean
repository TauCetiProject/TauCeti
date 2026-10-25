/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Bounded operators on a finite-dimensional space

A bounded operator on a finite-dimensional normed space is just a linear map, so its spectrum is
the finite set of eigenvalues. This holds over every field of scalars acting compatibly, for
instance over `ℝ` for an operator on a complex space.

Bounded operators out of a finite-dimensional space are determined by the images of a basis,
with operator norm controlled by the norms of those images. Hence such operators into `E` are
approximated in operator norm by operators factoring through any operator `g : F →L[𝕜] E` of
dense range.

## Main results

* `ContinuousLinearMap.finite_spectrum`: a bounded operator on a finite-dimensional normed space
  has finite spectrum, also over subfields of the scalars such as `ℝ ⊆ ℂ`.
* `ContinuousLinearMap.denseRange_comp`: on operators out of a finite-dimensional space,
  postcomposition with an operator of dense range has dense range.
-/

public section

namespace ContinuousLinearMap

variable {𝕜 V : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [NormedAddCommGroup V] [NormedSpace 𝕜 V] [FiniteDimensional 𝕜 V]

/-- A bounded operator on a finite-dimensional normed space has finite spectrum over any field
`S` of scalars acting compatibly, for instance over `ℝ` for an operator on a complex space. -/
theorem finite_spectrum (S : Type*) [Field S] [Algebra S 𝕜] [Algebra S (V →L[𝕜] V)]
    [IsScalarTower S 𝕜 (V →L[𝕜] V)] (T : V →L[𝕜] V) : (spectrum S T).Finite := by
  have := FiniteDimensional.complete 𝕜 V
  rw [← spectrum.preimage_algebraMap 𝕜, spectrum_eq]
  exact (Module.End.finite_spectrum _).preimage (algebraMap S 𝕜).injective.injOn

/-- On continuous linear maps out of a finite-dimensional space, postcomposition with a
continuous linear map of dense range has dense range: each `T : V →L[𝕜] E` is approximated in
operator norm by maps `g.comp U` with `U : V →L[𝕜] F`. -/
theorem denseRange_comp {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup F] [NormedSpace 𝕜 F] {g : F →L[𝕜] E} (hg : DenseRange g) :
    DenseRange (g.comp : (V →L[𝕜] F) → V →L[𝕜] E) := by
  rw [Metric.denseRange_iff]
  intro T r hr
  -- Approximate the images of a basis of `V` by points of the range of `g`.
  let v := Module.finBasis 𝕜 V
  obtain ⟨C, hC, hv⟩ := v.exists_opNorm_le (F := E)
  have hrC : 0 < r / (2 * C) := by positivity
  choose y hy using fun i ↦ Metric.denseRange_iff.1 hg (T (v i)) _ hrC
  refine ⟨v.constrL y, ?_⟩
  rw [dist_eq_norm]
  calc ‖T - g.comp (v.constrL y)‖ ≤ C * (r / (2 * C)) :=
        hv hrC.le fun i ↦ by
          simpa [Module.Basis.constrL_basis, ← dist_eq_norm] using (hy i).le
    _ = r / 2 := by field_simp
    _ < r := half_lt_self hr

end ContinuousLinearMap
