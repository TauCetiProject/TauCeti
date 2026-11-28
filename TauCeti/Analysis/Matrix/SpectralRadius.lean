/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Matrix.Normed
import TauCeti.Analysis.Normed.Algebra.GelfandRadius

/-!
# Spectral radius and convergence of matrix powers

Powers of a square complex matrix converge entrywise to zero exactly when its spectral radius
is strictly less than one. The criterion includes the empty matrix. For a real matrix the
criterion uses the spectral radius of its complexification, since nonreal eigenvalues also
affect convergence. These results give the spectral test for convergence of stationary
iterations from every starting vector and for every constant term.

The complex criterion uses Mathlib's Gelfand formula
(`spectrum.spectralRadius_eq_gelfandRadius`) with the row-sum operator norm.

## References

* Yousef Saad, *Iterative Methods for Sparse Linear Systems*, second edition, SIAM, 2003,
  Theorem 1.10, p. 20.
-/

public section

open Filter Topology
open scoped ENNReal

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

open scoped Matrix.Norms.Operator in
/-- A complex square matrix has powers tending to zero exactly when its spectral radius is
strictly less than one. Convergence is in the entrywise topology. -/
theorem tendsto_pow_atTop_nhds_zero_iff_spectralRadius_lt_one (G : Matrix ι ι ℂ) :
    Tendsto (fun k : ℕ ↦ G ^ k) atTop (𝓝 0) ↔ spectralRadius ℂ G < 1 := by
  rw [spectrum.spectralRadius_eq_gelfandRadius, ENNReal.ofReal_lt_one]
  exact TauCeti.isTopologicallyNilpotent_iff_gelfandRadius_lt_one G

/-- A real square matrix has powers tending to zero exactly when the spectral radius of its
entrywise complexification is strictly less than one. -/
theorem tendsto_pow_atTop_nhds_zero_iff_spectralRadius_map_lt_one (G : Matrix ι ι ℝ) :
    Tendsto (fun k : ℕ ↦ G ^ k) atTop (𝓝 0) ↔
      spectralRadius ℂ (G.map Complex.ofRealHom) < 1 := by
  let f : Matrix ι ι ℝ →+* Matrix ι ι ℂ := Complex.ofRealHom.mapMatrix
  have hf : IsInducing f := Complex.isometry_ofReal.isEmbedding.isInducing.matrix_map
  rw [hf.tendsto_nhds_iff, ← tendsto_pow_atTop_nhds_zero_iff_spectralRadius_lt_one]
  simp only [Function.comp_def, map_pow, map_zero, f, RingHom.mapMatrix_apply]

end Matrix
