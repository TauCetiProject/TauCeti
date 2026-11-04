/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import TauCeti.Algebra.BrauerAlgebra.Basic
public import TauCeti.RingTheory.Semisimple.Trace.Form

/-!
# The discriminant of the Brauer algebra

In the diagram basis the structure constants of the Brauer algebra `B_k(δ)` are powers of the loop
value `δ`: two diagrams multiply to `δ ^ c` times their stack, where `c` is the number of closed
loops left in the middle. So the trace of left multiplication by a product of two diagrams is an
integer polynomial in `δ`, namely

`tr(L_{D D'}) = δ ^ c(D, D') · ∑_{E, (D ∘ D') ∘ E = E} δ ^ c(D ∘ D', E)`,

and the Gram determinant of the regular trace form in the diagram basis, the **discriminant**
`TauCeti.BrauerAlgebra.discr k` of the Brauer algebra on `k` strands, is a single integer
polynomial whose value at `δ` is the discriminant of `B_k(δ)`, over every commutative ring
(`TauCeti.BrauerAlgebra.aeval_discr`).

By the trace-form criterion for semisimplicity, `B_k(δ)` is semisimple over a field wherever the
discriminant does not vanish at `δ`, and over a field of characteristic zero exactly there
(`TauCeti.BrauerAlgebra.isSemisimpleRing_iff_aeval_discr_ne_zero`). This is how the
semisimplicity of the Brauer algebra at a generic loop value is reduced to the nonvanishing of one
polynomial, that is, to its semisimplicity at a single loop value.

## Main definitions

* `TauCeti.BrauerAlgebra.discr`: the discriminant of the Brauer algebra on `k` strands, an integer
  polynomial in the loop value.

## Main results

* `TauCeti.BrauerAlgebra.trace_mulLeft_of_mul_of`: the trace of left multiplication by the product
  of two diagrams.
* `TauCeti.BrauerAlgebra.aeval_discr`: the value of the discriminant at `δ` is the Gram
  determinant of the regular trace form of `B_k(δ)` in the diagram basis.
* `TauCeti.BrauerAlgebra.isSemisimpleRing_of_aeval_discr_ne_zero`: over a field, `B_k(δ)` is
  semisimple when the discriminant does not vanish at `δ`.
* `TauCeti.BrauerAlgebra.isSemisimpleRing_iff_aeval_discr_ne_zero`: over a field of
  characteristic zero, `B_k(δ)` is semisimple exactly when the discriminant does not vanish at `δ`.

## References

* R. Brauer, *On algebras which are connected with the semisimple continuous groups*, Annals of
  Mathematics 38 (1937), 857-872.
* H. Wenzl, *On the structure of Brauer's centralizer algebras*, Annals of Mathematics 128 (1988),
  173-193.
-/

public section

open LinearMap Polynomial

namespace TauCeti

namespace BrauerAlgebra

/-- The trace of left multiplication by the product of the diagrams `D` and `D'`, as an integer
polynomial in the loop value. -/
private noncomputable def traceMulPoly {k : ℕ} (D D' : BrauerDiagram k) : ℤ[X] :=
  X ^ middleLoopCount D D' * ∑ E : BrauerDiagram k,
    if composeDiagram (composeDiagram D D') E = E then
      X ^ middleLoopCount (composeDiagram D D') E else 0

variable (k : ℕ) in
/-- **The discriminant of the Brauer algebra** on `k` strands: the Gram determinant of the regular
trace form `(x, y) ↦ tr(L_{xy})` in the diagram basis, as an integer polynomial in the loop value.
Its value at `δ` is the discriminant of `B_k(δ)` (`TauCeti.BrauerAlgebra.aeval_discr`). -/
noncomputable def discr : ℤ[X] :=
  (Matrix.of fun D D' : BrauerDiagram k => traceMulPoly D D').det

variable {k : ℕ}

/-- **The trace of left multiplication by a product of two diagrams** in the Brauer algebra: it is
`δ ^ c(D, D')` times the sum of `δ ^ c(D ∘ D', E)` over the diagrams `E` fixed by stacking `D ∘ D'`
on top. -/
theorem trace_mulLeft_of_mul_of {R : Type*} [CommSemiring R] {δ : R} (D D' : BrauerDiagram k) :
    trace R (BrauerAlgebra R δ k) (mulLeft R (of D * of D')) =
      δ ^ middleLoopCount D D' * ∑ E : BrauerDiagram k,
        if composeDiagram (composeDiagram D D') E = E then
          δ ^ middleLoopCount (composeDiagram D D') E else 0 := by
  classical
  rw [trace_eq_matrix_trace R (basis R δ k), Matrix.trace, Finset.mul_sum]
  refine Finset.sum_congr rfl fun E _ => ?_
  simp only [Matrix.diag_apply, toMatrix_apply, basis_apply, mulLeft_apply, basis_repr, of_mul_of,
    smul_mul_assoc, smul_smul, coeff_smul, coeff_of, Finsupp.smul_apply, Finsupp.single_apply,
    smul_eq_mul]
  split_ifs <;> simp [mul_comm]

/-- **The value of the discriminant at `δ`** is the Gram determinant of the regular trace form of
the Brauer algebra `B_k(δ)` in the diagram basis. -/
theorem aeval_discr {R : Type*} [CommRing R] (δ : R) :
    aeval δ (discr k) = (BilinForm.toMatrix (basis R δ k)
      (Algebra.regularTraceForm R (BrauerAlgebra R δ k))).det := by
  rw [discr, AlgHom.map_det]
  congr 1
  ext D D'
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, BilinForm.toMatrix_apply,
    Algebra.regularTraceForm_apply, basis_apply]
  have hL : Algebra.lmul R (BrauerAlgebra R δ k) (of D * of D') = mulLeft R (of D * of D') :=
    LinearMap.ext fun x => by
      rw [Algebra.coe_lmul_eq_mul, mul_apply', mulLeft_apply]
  rw [hL, trace_mulLeft_of_mul_of]
  simp [traceMulPoly, apply_ite]

/-- **The Brauer algebra is semisimple where the discriminant does not vanish.** Over every field,
if the discriminant of the Brauer algebra on `k` strands does not vanish at `δ`, then `B_k(δ)` is
semisimple. -/
theorem isSemisimpleRing_of_aeval_discr_ne_zero {K : Type*} [Field K] {δ : K}
    (h : aeval δ (discr k) ≠ 0) : IsSemisimpleRing (BrauerAlgebra K δ k) := by
  classical
  refine isSemisimpleRing_of_nondegenerate_regularTraceForm
    ((BilinForm.nondegenerate_iff_det_ne_zero (basis K δ k)).mpr ?_)
  rwa [← aeval_discr]

/-- **The semisimplicity locus of the Brauer algebra**: over a field of characteristic zero, the
Brauer algebra `B_k(δ)` is semisimple exactly when the discriminant does not vanish at `δ`. -/
theorem isSemisimpleRing_iff_aeval_discr_ne_zero {K : Type*} [Field K] [CharZero K] {δ : K} :
    IsSemisimpleRing (BrauerAlgebra K δ k) ↔ aeval δ (discr k) ≠ 0 := by
  classical
  rw [isSemisimpleRing_iff_nondegenerate_regularTraceForm (K := K),
    BilinForm.nondegenerate_iff_det_ne_zero (basis K δ k), aeval_discr]

end BrauerAlgebra

end TauCeti
