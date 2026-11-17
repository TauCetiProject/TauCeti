/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Discriminant

/-!
# Discriminants of trace-dual bases

Let `E / F` be a finite separable extension of fields and `b` a finite `F`-basis of `E`.
Because the trace pairing is nondegenerate, `b` admits a trace-dual basis `b.traceDual`
satisfying `Tr_{E/F}(b_i · b*_j) = δ_{ij}`. Expanding each `b_i` in the dual basis shows
that the trace matrices of `b` and `b.traceDual` are inverses of one another, and taking
determinants shows that their discriminants multiply to `1`.

## Main results

* `Module.Basis.traceMatrix_mul_traceMatrix_traceDual`:
  `Algebra.traceMatrix F b * Algebra.traceMatrix F b.traceDual = 1`.
* `Module.Basis.discr_mul_discr_traceDual`:
  `Algebra.discr F b * Algebra.discr F b.traceDual = 1`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section 3.3–3.5 (complementary bases and discriminants).
* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2.
-/

public section

namespace Module.Basis

variable {F E ι : Type*} [Field F] [Field E] [Algebra F E]
  [FiniteDimensional F E] [Algebra.IsSeparable F E] [Fintype ι] [DecidableEq ι]

/-- **The trace matrices of a basis and its trace-dual basis are inverses**:
`traceMatrix F b * traceMatrix F b.traceDual = 1`. -/
theorem traceMatrix_mul_traceMatrix_traceDual (b : Module.Basis ι F E) :
    Algebra.traceMatrix F b * Algebra.traceMatrix F b.traceDual = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hsum : ∑ l, Algebra.traceMatrix F b i l * Algebra.traceMatrix F b.traceDual l j =
      Algebra.trace F E ((∑ l, b.traceDual.repr (b i) l • b.traceDual l) * b.traceDual j) := by
    rw [Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [Algebra.traceMatrix_apply, b.traceDual_repr_apply, Algebra.traceForm_apply,
      smul_mul_assoc, LinearMap.map_smul, smul_eq_mul]
  rw [hsum, b.traceDual.sum_repr, b.trace_mul_traceDual]

/-- **The discriminants of a basis and its trace-dual basis multiply to `1`**:
`discr F b * discr F b.traceDual = 1`. -/
theorem discr_mul_discr_traceDual (b : Module.Basis ι F E) :
    Algebra.discr F b * Algebra.discr F b.traceDual = 1 := by
  rw [Algebra.discr_def, Algebra.discr_def, ← Matrix.det_mul,
    b.traceMatrix_mul_traceMatrix_traceDual, Matrix.det_one]

end Module.Basis

end
