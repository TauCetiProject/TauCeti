/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import TauCeti.Analysis.Convex.FiniteMean

/-!
# The empirical second-moment matrix

For a finite sample `v : ι → n → 𝕜` of vectors over `ℝ` or `ℂ`, the uncentered empirical
second-moment matrix is

`M̂ = r⁻¹ ∑ᵢ vᵢ vᵢᴴ`, with entries `M̂ₖₗ = r⁻¹ ∑ᵢ vᵢₖ conj (vᵢₗ)`,

where `r = card ι`. It is the mean (`TauCeti.finiteMean`) of the rank-one matrices `vᵢ vᵢᴴ`,
so it is Hermitian and positive semidefinite. Evaluated on random samples it is the natural
estimator of a population second-moment matrix `E[V Vᴴ]`; each of its entries is a sample mean of
products of coordinates, which is what makes the second-moment bounds for sample means apply to it
entry by entry.

## Main declarations

* `TauCeti.sampleSecondMoment`: the empirical second-moment matrix of a finite sample.
* `TauCeti.sampleSecondMoment_apply`: its entries are sample means of coordinate products.
* `TauCeti.isHermitian_sampleSecondMoment`, `TauCeti.posSemidef_sampleSecondMoment`: it is
  Hermitian, and positive semidefinite in finite dimension.

## References

* R. Vershynin, *High-Dimensional Probability* (2018), §4.7: the sample covariance matrix.
-/

public section

open Matrix
open scoped ComplexOrder

namespace TauCeti

variable {𝕜 ι n : Type*} [RCLike 𝕜] [Fintype ι]

/-- The uncentered empirical second-moment matrix `r⁻¹ ∑ᵢ vᵢ vᵢᴴ` of a finite sample
`v : ι → n → 𝕜`, where `r = card ι`: the mean of the rank-one matrices `vᵢ vᵢᴴ`. The empty sample
has second-moment matrix `0`. -/
noncomputable def sampleSecondMoment (v : ι → n → 𝕜) : Matrix n n 𝕜 :=
  finiteMean 𝕜 fun i ↦ vecMulVec (v i) (star (v i))

theorem sampleSecondMoment_def (v : ι → n → 𝕜) :
    sampleSecondMoment v = finiteMean 𝕜 fun i ↦ vecMulVec (v i) (star (v i)) :=
  (rfl)

/-- The `(k, l)` entry of the empirical second-moment matrix is the sample mean of the products
`vᵢₖ conj (vᵢₗ)`. -/
@[simp]
theorem sampleSecondMoment_apply (v : ι → n → 𝕜) (k l : n) :
    sampleSecondMoment v k l = finiteMean 𝕜 fun i ↦ v i k * star (v i l) := by
  simp [sampleSecondMoment_def, finiteMean_eq_inv_smul_sum, Matrix.sum_apply, vecMulVec_apply]

/-- The empirical second-moment matrix is Hermitian. -/
theorem isHermitian_sampleSecondMoment (v : ι → n → 𝕜) : (sampleSecondMoment v).IsHermitian :=
  IsHermitian.ext fun k l ↦ by
    simp [finiteMean_eq_inv_smul_sum, star_sum, mul_comm]

/-- The empirical second-moment matrix is positive semidefinite. -/
theorem posSemidef_sampleSecondMoment [Finite n] (v : ι → n → 𝕜) :
    (sampleSecondMoment v).PosSemidef := by
  have := Fintype.ofFinite n
  rw [sampleSecondMoment_def, finiteMean_eq_inv_smul_sum]
  exact (posSemidef_sum _ fun i _ ↦ posSemidef_vecMulVec_self_star (v i)).smul (by positivity)

end TauCeti
