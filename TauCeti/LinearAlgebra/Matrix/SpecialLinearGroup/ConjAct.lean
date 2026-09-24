/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# The conjugation action of the special linear group on matrices

The special linear group `SL(n, R)` acts on the square matrices `Matrix n n R` by conjugation,
`g • M = g M g⁻¹`. As for any conjugation action, it is recorded as an action of the type synonym
`ConjAct (SL(n, R))`, so that it does not clash with the action of `SL(n, R)` on column vectors
or with the scalar action of `R`. Mathlib provides the conjugation action `ConjAct.unitsScalar`
of the units `Mˣ` of a monoid on `M`, which covers `GL(n, R)` acting on `Matrix n n R`, but not
the action of `SL(n, R)`, whose orbits are the `SL(n, R)`-conjugacy classes of matrices.

Conjugation preserves the trace, the determinant and, since `adjugate g = g⁻¹` for `g ∈ SL(n, R)`,
commutes with taking adjugates.

## Main definitions

* `Matrix.SpecialLinearGroup.instMulActionConjAct`: the conjugation action `g • M = g M g⁻¹` of
  `ConjAct (SpecialLinearGroup n R)` on `Matrix n n R`, with scalar multiplication
  `Matrix.SpecialLinearGroup.instSMulConjAct`.
* `Matrix.SpecialLinearGroup.traceDetFiber n t d`: the `n × n` matrices of trace `t` and
  determinant `d` (`Matrix.SpecialLinearGroup.mem_traceDetFiber`), as a sub-action, whose orbits
  are the `SL(n, R)`-conjugacy classes of such matrices.

## Main results

* `Matrix.SpecialLinearGroup.conjAct_smul_def`: `g • M = g M g⁻¹`.
* `Matrix.SpecialLinearGroup.trace_conjAct_smul` and
  `Matrix.SpecialLinearGroup.det_conjAct_smul`: conjugation preserves the trace and the
  determinant.
* `Matrix.SpecialLinearGroup.adjugate_conjAct_smul`: conjugation commutes with the adjugate.
* `Matrix.SpecialLinearGroup.adjugate_mem_traceDetFiber`: for `2 × 2` matrices, the adjugate has
  the same trace and determinant.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §1, equation (2): the sum
  over the `SL(2, ℤ)`-conjugacy classes of integer matrices of fixed trace and determinant, whose
  orbits this action describes.
-/

public section

open ConjAct

namespace Matrix.SpecialLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- `SL(n, R)` acts on `Matrix n n R` by conjugation, `g • M = g M g⁻¹`, through the type synonym
`ConjAct`, in the manner of Mathlib's `ConjAct.unitsScalar`. -/
instance instSMulConjAct : SMul (ConjAct (SpecialLinearGroup n R)) (Matrix n n R) where
  smul g M := ((ofConjAct g : SpecialLinearGroup n R) : Matrix n n R) * M *
    ((ofConjAct g)⁻¹ : SpecialLinearGroup n R)

/-- The conjugation action of `SL(n, R)` on matrices is `g • M = g M g⁻¹`. -/
theorem conjAct_smul_def (g : ConjAct (SpecialLinearGroup n R)) (M : Matrix n n R) :
    g • M = ((ofConjAct g : SpecialLinearGroup n R) : Matrix n n R) * M *
      ((ofConjAct g)⁻¹ : SpecialLinearGroup n R) :=
  rfl

/-- Conjugation `g • M = g M g⁻¹` is an action of `SL(n, R)` on `Matrix n n R`. -/
instance instMulActionConjAct : MulAction (ConjAct (SpecialLinearGroup n R)) (Matrix n n R) where
  one_smul M := by simp [conjAct_smul_def]
  mul_smul g h M := by simp [conjAct_smul_def, Matrix.mul_assoc]

/-- Conjugation by `SL(n, R)` preserves the trace. -/
@[simp]
theorem trace_conjAct_smul (g : ConjAct (SpecialLinearGroup n R)) (M : Matrix n n R) :
    trace (g • M) = trace M := by
  simp [conjAct_smul_def, trace_mul_cycle, adjugate_mul]

/-- Conjugation by `SL(n, R)` preserves the determinant. -/
@[simp]
theorem det_conjAct_smul (g : ConjAct (SpecialLinearGroup n R)) (M : Matrix n n R) :
    det (g • M) = det M := by
  simp [conjAct_smul_def, det_adjugate]

/-- Conjugation by `SL(n, R)` commutes with the adjugate:
`adjugate (g M g⁻¹) = g (adjugate M) g⁻¹`. -/
@[simp]
theorem adjugate_conjAct_smul (g : ConjAct (SpecialLinearGroup n R)) (M : Matrix n n R) :
    adjugate (g • M) = g • adjugate M := by
  -- `adjugate g = g⁻¹` and `adjugate g⁻¹ = g` for `g ∈ SL(n, R)`
  simp [conjAct_smul_def, adjugate_mul_distrib, Matrix.mul_assoc, ← SpecialLinearGroup.coe_inv]

variable (n) in
/-- The matrices of trace `t` and determinant `d`, as a sub-action of the conjugation action of
`SL(n, R)`: its orbits are the `SL(n, R)`-conjugacy classes of such matrices. -/
@[expose]
def traceDetFiber (t d : R) : SubMulAction (ConjAct (SpecialLinearGroup n R)) (Matrix n n R) where
  carrier := {M | M.trace = t ∧ M.det = d}
  smul_mem' g M hM := ⟨(trace_conjAct_smul g M).trans hM.1, (det_conjAct_smul g M).trans hM.2⟩

/-- A matrix lies in `traceDetFiber n t d` exactly when its trace is `t` and its determinant `d`. -/
@[simp]
theorem mem_traceDetFiber {t d : R} {M : Matrix n n R} :
    M ∈ traceDetFiber n t d ↔ M.trace = t ∧ M.det = d :=
  Iff.rfl

/-- The adjugate of a `2 × 2` matrix `M` has the trace and the determinant of `M`: it lies in
`traceDetFiber (Fin 2) t d` whenever `M` does. -/
theorem adjugate_mem_traceDetFiber {t d : R} {M : Matrix (Fin 2) (Fin 2) R}
    (hM : M ∈ traceDetFiber (Fin 2) t d) : adjugate M ∈ traceDetFiber (Fin 2) t d := by
  obtain ⟨rfl, rfl⟩ := hM
  exact ⟨by simp [adjugate_fin_two, trace_fin_two, add_comm], by simp [det_adjugate]⟩

end Matrix.SpecialLinearGroup
