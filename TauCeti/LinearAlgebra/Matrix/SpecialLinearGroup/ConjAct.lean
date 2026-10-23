/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
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

Conjugation by `SL(n, R)` is conjugation by its image in `GL(n, R)`, so `SL(n, R)`-conjugates are
`GL(n, R)`-conjugates. Conversely, a conjugate `g X g⁻¹` by `g ∈ GL(n, R)` is also a conjugate by
`SL(n, R)` exactly when the determinant of `g` can be corrected inside the centralizer of `X`: some
invertible matrix commuting with `X` has the same determinant as `g`.

## Main definitions

* `ConjAct.specialLinearGroupMulAction`: the conjugation action `g • M = g M g⁻¹` of
  `ConjAct (SpecialLinearGroup n R)` on `Matrix n n R`, with scalar multiplication
  `ConjAct.specialLinearGroupScalar`.
* `TauCeti.traceDetFiber n t d`: the `n × n` matrices of trace `t` and determinant `d`
  (`TauCeti.mem_traceDetFiber`), as a sub-action, whose orbits are the `SL(n, R)`-conjugacy
  classes of such matrices.

## Main results

* `ConjAct.specialLinearGroup_smul_def`: `g • M = g M g⁻¹`.
* `ConjAct.trace_specialLinearGroup_smul` and `ConjAct.det_specialLinearGroup_smul`: conjugation
  preserves the trace and the determinant.
* `Matrix.SpecialLinearGroup.trace_mul_mul_inv`: the product form `trace (P k P⁻¹) = trace k` of
  trace invariance, for `P k : SL(n, R)`.
* `ConjAct.adjugate_specialLinearGroup_smul`: conjugation commutes with the adjugate.
* `ConjAct.toConjAct_toGL_smul`: conjugating by `s ∈ SL(n, R)` is conjugating by its image in
  `GL(n, R)`.
* `Matrix.GeneralLinearGroup.toConjAct_smul_mem_orbit_specialLinearGroup_iff`: a
  `GL(n, R)`-conjugate is an `SL(n, R)`-conjugate exactly when the determinant of the conjugator
  is the determinant of an invertible matrix in the centralizer.
* `Matrix.GeneralLinearGroup.orbit_conjAct_specialLinearGroup_subset`: an `SL(n, R)`-conjugate is
  a `GL(n, R)`-conjugate.
* `TauCeti.adjugate_mem_traceDetFiber`: for `2 × 2` matrices, the adjugate has the same trace and
  determinant.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler–Selberg trace formula*,
  J. Reine Angew. Math. **762** (2020), 105–122, arXiv:1711.00327, §1, equation (2): the sum
  over the `SL(2, ℤ)`-conjugacy classes of integer matrices of fixed trace and determinant, whose
  orbits this action describes.
-/

public section

open Matrix

namespace ConjAct

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- `SL(n, R)` acts on `Matrix n n R` by conjugation, `g • M = g M g⁻¹`, through the type synonym
`ConjAct`, in the manner of Mathlib's `ConjAct.unitsScalar`. -/
instance specialLinearGroupScalar : SMul (ConjAct (SpecialLinearGroup n R)) (Matrix n n R) where
  smul g M := ((ofConjAct g : SpecialLinearGroup n R) : Matrix n n R) * M *
    ((ofConjAct g)⁻¹ : SpecialLinearGroup n R)

/-- The conjugation action of `SL(n, R)` on matrices is `g • M = g M g⁻¹`. -/
theorem specialLinearGroup_smul_def (g : ConjAct (SpecialLinearGroup n R)) (M : Matrix n n R) :
    g • M = ((ofConjAct g : SpecialLinearGroup n R) : Matrix n n R) * M *
      ((ofConjAct g)⁻¹ : SpecialLinearGroup n R) :=
  rfl

/-- Conjugation `g • M = g M g⁻¹` is an action of `SL(n, R)` on `Matrix n n R`. -/
instance specialLinearGroupMulAction :
    MulAction (ConjAct (SpecialLinearGroup n R)) (Matrix n n R) where
  one_smul M := by simp [specialLinearGroup_smul_def]
  mul_smul g h M := by simp [specialLinearGroup_smul_def, Matrix.mul_assoc]

/-- Conjugation by `SL(n, R)` preserves the trace. -/
@[simp]
theorem trace_specialLinearGroup_smul (g : ConjAct (SpecialLinearGroup n R)) (M : Matrix n n R) :
    trace (g • M) = trace M := by
  simp [specialLinearGroup_smul_def, trace_mul_cycle, adjugate_mul]

/-- Conjugation by `SL(n, R)` preserves the determinant. -/
@[simp]
theorem det_specialLinearGroup_smul (g : ConjAct (SpecialLinearGroup n R)) (M : Matrix n n R) :
    det (g • M) = det M := by
  simp [specialLinearGroup_smul_def, det_adjugate]

/-- Conjugation by `SL(n, R)` commutes with the adjugate:
`adjugate (g M g⁻¹) = g (adjugate M) g⁻¹`. -/
@[simp]
theorem adjugate_specialLinearGroup_smul (g : ConjAct (SpecialLinearGroup n R))
    (M : Matrix n n R) : adjugate (g • M) = g • adjugate M := by
  -- `adjugate g = g⁻¹` and `adjugate g⁻¹ = g` for `g ∈ SL(n, R)`
  simp [specialLinearGroup_smul_def, adjugate_mul_distrib, Matrix.mul_assoc,
    ← SpecialLinearGroup.coe_inv]

/-- Conjugating a matrix by the image of `s ∈ SL(n, R)` in `GL(n, R)` is conjugating it by `s`. -/
@[simp]
theorem toConjAct_toGL_smul (s : SpecialLinearGroup n R) (M : Matrix n n R) :
    toConjAct (SpecialLinearGroup.toGL s) • M = toConjAct s • M := by
  simp [units_smul_def, specialLinearGroup_smul_def, ← map_inv]

end ConjAct

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- **Determinant correction of conjugators.** Over a commutative ring `R`, the conjugate
`g X g⁻¹` of a matrix `X` by `g ∈ GL(n, R)` is also a conjugate of `X` by `SL(n, R)` exactly when
some invertible matrix commuting with `X` has the determinant of `g`. -/
theorem toConjAct_smul_mem_orbit_specialLinearGroup_iff {g : GL n R} {X : Matrix n n R} :
    ConjAct.toConjAct g • X ∈ MulAction.orbit (ConjAct (SpecialLinearGroup n R)) X ↔
      ∃ c : GL n R, Commute (c : Matrix n n R) X ∧ det c = det g := by
  -- An invertible matrix fixes `X` under conjugation exactly when it commutes with `X`.
  have hfix (c : GL n R) : ConjAct.toConjAct c • X = X ↔ Commute (c : Matrix n n R) X := by
    rw [ConjAct.units_smul_def, ConjAct.ofConjAct_toConjAct, Units.mul_inv_eq_iff_eq_mul]
    exact (commute_iff_eq _ _).symm
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨s, rfl⟩ := ConjAct.toConjAct.surjective s
    refine ⟨(SpecialLinearGroup.toGL s)⁻¹ * g, (hfix _).mp ?_, by simp⟩
    rw [ConjAct.toConjAct_mul, mul_smul, ← hs, ← ConjAct.toConjAct_toGL_smul,
      ConjAct.toConjAct_inv, inv_smul_smul]
  · rintro ⟨c, hc, hdet⟩
    obtain ⟨s, hs⟩ : g * c⁻¹ ∈ (SpecialLinearGroup.toGL (n := n) (R := R)).range := by
      rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker, map_mul, map_inv, hdet,
        mul_inv_cancel]
    refine ⟨ConjAct.toConjAct s, ?_⟩
    rw [← ConjAct.toConjAct_toGL_smul, hs, ConjAct.toConjAct_mul, mul_smul, ConjAct.toConjAct_inv,
      inv_smul_eq_iff.mpr ((hfix c).mpr hc).symm]

/-- An `SL(n, R)`-conjugate of a matrix is a `GL(n, R)`-conjugate. -/
theorem orbit_conjAct_specialLinearGroup_subset (X : Matrix n n R) :
    MulAction.orbit (ConjAct (SpecialLinearGroup n R)) X ⊆
      MulAction.orbit (ConjAct (GL n R)) X := by
  rintro _ ⟨s, rfl⟩
  exact ⟨ConjAct.toConjAct (SpecialLinearGroup.toGL (ConjAct.ofConjAct s)), by simp⟩

end Matrix.GeneralLinearGroup

namespace Matrix.SpecialLinearGroup

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

/-- Conjugation in `SL(n, R)` preserves the trace: `trace (P k P⁻¹) = trace k`. This is the
product form of `ConjAct.trace_specialLinearGroup_smul`. -/
theorem trace_mul_mul_inv (P k : SpecialLinearGroup n R) :
    ((P * k * P⁻¹ : SpecialLinearGroup n R) : Matrix n n R).trace = (k : Matrix n n R).trace := by
  simpa only [ConjAct.specialLinearGroup_smul_def, ConjAct.ofConjAct_toConjAct, coe_mul] using
    ConjAct.trace_specialLinearGroup_smul (ConjAct.toConjAct P) (k : Matrix n n R)

end Matrix.SpecialLinearGroup

namespace TauCeti

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R]

variable (n) in
/-- The matrices of trace `t` and determinant `d`, as a sub-action of the conjugation action of
`SL(n, R)`: its orbits are the `SL(n, R)`-conjugacy classes of such matrices. -/
def traceDetFiber (t d : R) : SubMulAction (ConjAct (SpecialLinearGroup n R)) (Matrix n n R) where
  carrier := {M | M.trace = t ∧ M.det = d}
  smul_mem' g M hM := ⟨(ConjAct.trace_specialLinearGroup_smul g M).trans hM.1,
    (ConjAct.det_specialLinearGroup_smul g M).trans hM.2⟩

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

end TauCeti
