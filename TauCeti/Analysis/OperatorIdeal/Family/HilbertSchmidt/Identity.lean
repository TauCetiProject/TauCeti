/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.OperatorIdeal.Family.HilbertSchmidt

/-!
# The identity operator and the Hilbert–Schmidt ideal

The Hilbert–Schmidt energy of the identity of a Hilbert space `E` in a Hilbert basis indexed by
`ι` is `∑' i, ‖bᵢ‖ₑ² = #ι`. Hence the identity is Hilbert–Schmidt exactly when the basis is finite:
on a Hilbert space with an infinite (for instance `ℕ`-indexed) Hilbert basis it has no
representative in the Hilbert–Schmidt ideal, while on an `n`-dimensional space it does, with
Hilbert–Schmidt norm `√n`. Since the real-valued Hilbert–Schmidt norm is `0` at infinite energy,
non-membership is stated for the ideal rather than read off from the norm.

## Main declarations

* `ContinuousLinearMap.hilbertSchmidtEnergy_id`: `E_b(id) = #ι`.
* `TauCeti.OperatorIdealFamily.id_mem_finiteSubmodule_hilbertSchmidt_iff`: the identity lies in
  the Hilbert–Schmidt ideal iff some (equivalently every) Hilbert basis is finite.
* `TauCeti.OperatorIdealFamily.id_notMem_finiteSubmodule_hilbertSchmidt`: no Hilbert–Schmidt
  identity in the presence of an infinite Hilbert basis.
* `TauCeti.OperatorIdealFamily.id_mem_finiteSubmodule_hilbertSchmidt`,
  `ContinuousLinearMap.hilbertSchmidtNorm_id`: in finite dimension the identity is
  Hilbert–Schmidt with norm `√(finrank 𝕜 E)`.

## References

* G. Teschl, *Mathematical Methods in Quantum Mechanics*, 2nd ed., AMS, 2014, §6.3.
-/

public section

open scoped ENNReal

universe v

namespace ContinuousLinearMap

variable {𝕜 E ι : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- The Hilbert–Schmidt energy of the identity is the cardinality of the Hilbert basis. -/
@[simp]
theorem hilbertSchmidtEnergy_id (b : HilbertBasis ι 𝕜 E) :
    (ContinuousLinearMap.id 𝕜 E).hilbertSchmidtEnergy b = ENat.card ι := by
  have h1 (i : ι) : ‖b i‖ₑ = 1 := by rw [← ofReal_norm, b.orthonormal.1 i, ENNReal.ofReal_one]
  simp [hilbertSchmidtEnergy_def, h1]

/-- In finite dimension the identity has Hilbert–Schmidt norm `√(finrank 𝕜 E)`. (Completeness is
automatic in finite dimension, `FiniteDimensional.complete`, but is not an instance.) -/
@[simp]
theorem hilbertSchmidtNorm_id [FiniteDimensional 𝕜 E] [CompleteSpace E] :
    (ContinuousLinearMap.id 𝕜 E).hilbertSchmidtNorm = √(Module.finrank 𝕜 E) := by
  rw [hilbertSchmidtNorm_eq_sqrt _ (stdOrthonormalBasis 𝕜 E).toHilbertBasis,
    hilbertSchmidtEnergy_id]
  simp

end ContinuousLinearMap

namespace TauCeti.OperatorIdealFamily

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [CompleteSpace E]

/-- The identity lies in the Hilbert–Schmidt ideal exactly when the Hilbert basis `b` is
finite. -/
theorem id_mem_finiteSubmodule_hilbertSchmidt_iff {ι : Type*} (b : HilbertBasis ι 𝕜 E) :
    ContinuousLinearMap.id 𝕜 E ∈ ((hilbertSchmidt 𝕜).operatorGauge E E).finiteSubmodule ↔
      Finite ι := by
  rw [mem_finiteSubmodule_hilbertSchmidt_iff _ b, ContinuousLinearMap.hilbertSchmidtEnergy_id,
    ne_eq, ENat.toENNReal_eq_top, ENat.card_eq_top, not_infinite_iff_finite]

/-- **The identity is not Hilbert–Schmidt** on a Hilbert space with an infinite Hilbert basis, for
instance an `ℕ`-indexed one. -/
theorem id_notMem_finiteSubmodule_hilbertSchmidt {ι : Type*} [Infinite ι]
    (b : HilbertBasis ι 𝕜 E) :
    ContinuousLinearMap.id 𝕜 E ∉ ((hilbertSchmidt 𝕜).operatorGauge E E).finiteSubmodule := by
  rw [id_mem_finiteSubmodule_hilbertSchmidt_iff b, not_finite_iff_infinite]
  infer_instance

/-- In finite dimension the identity is Hilbert–Schmidt; its Hilbert–Schmidt norm is
`ContinuousLinearMap.hilbertSchmidtNorm_id`. -/
theorem id_mem_finiteSubmodule_hilbertSchmidt [FiniteDimensional 𝕜 E] :
    ContinuousLinearMap.id 𝕜 E ∈ ((hilbertSchmidt 𝕜).operatorGauge E E).finiteSubmodule :=
  (id_mem_finiteSubmodule_hilbertSchmidt_iff (stdOrthonormalBasis 𝕜 E).toHilbertBasis).2
    inferInstance

end TauCeti.OperatorIdealFamily
