/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Algebra.Defs
public import TauCeti.RingTheory.GradedAlgebra.Opposite

/-!
# Opposites of differential graded algebras

The opposite of a differential graded algebra uses the Koszul-signed multiplication

`op a * op b = (-1) ^ (|a| * |b|) • op (b * a)`.

With this multiplication, the unchanged differential `d (op a) = op (d a)` again obeys the
graded Leibniz rule.  The ordinary multiplicative opposite does not: reversing the two factors
without the Koszul sign puts the Leibniz sign on the wrong term.

## Main definitions

* `GradedOpposite.differential`: the differential induced on the graded opposite.

## Main results

* `GradedOpposite.differential_op` and `GradedOpposite.differential_unop`: normalization of the
  differential through the two directions of the underlying linear equivalence.
* `IsDGAlgebra.gradedOpposite`: the Koszul-signed opposite of a differential graded algebra is a
  differential graded algebra.

The convention follows B. Keller, *Deriving DG categories*, Section 1, and B. Keller,
*Introduction to A-infinity algebras and modules*, Section 3.1.
-/

public section

open scoped DirectSum

namespace TauCeti

universe uR uA

namespace GradedOpposite

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  (G : InternalGrading R A)

/-- The differential on the graded opposite, unchanged on underlying elements. -/
noncomputable def differential (d : A →ₗ[R] A) :
    GradedOpposite G →ₗ[R] GradedOpposite G :=
  (opLinearEquiv G).conj d

/-- The opposite differential acts by the original differential on underlying elements. -/
@[simp]
theorem differential_op (d : A →ₗ[R] A) (a : A) :
    differential G d (op G a) = op G (d a) := by
  rw [differential, LinearEquiv.conj_apply_apply]
  simp

/-- Returning the opposite differential to the original algebra gives the original
differential. -/
@[simp]
theorem differential_unop (d : A →ₗ[R] A) (a : GradedOpposite G) :
    unop G (differential G d a) = d (unop G a) := by
  have h := differential_op G d (unop G a)
  rw [op_unop G a] at h
  exact (congrArg (unop G) h).trans (unop_op G _)

variable [GradedAlgebra G.piece] {d : A →ₗ[R] A}

private theorem differential_leibniz_of_mem (h : IsDGAlgebra G.piece d)
    {p q : ℤ} {a b : A} (ha : a ∈ G.piece p) (hb : b ∈ G.piece q) :
    differential G d (op G a * op G b) =
      differential G d (op G a) * op G b +
        p.negOnePow • (op G a * differential G d (op G b)) := by
  rw [op_mul G ha hb]
  simp only [Units.smul_def, map_zsmul]
  rw [differential_op, h.leibniz hb a, op_add]
  rw [Units.smul_def, op_zsmul]
  rw [
    differential_op, differential_op, op_mul G (h.map_mem ha) hb,
    op_mul G ha (h.map_mem hb)]
  simp only [Units.smul_def]
  simp only [smul_add, smul_smul, add_comm]
  have hfirstUnits :
      (p * q).negOnePow * q.negOnePow = ((p + 1) * q).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    ring
  have hsecondUnits :
      (p * q).negOnePow = p.negOnePow * (p * (q + 1)).negOnePow := by
    rw [← Int.negOnePow_add]
    apply (Int.negOnePow_eq_iff _ _).2
    use -p
    ring
  have hfirst := congrArg Units.val hfirstUnits
  have hsecond := congrArg Units.val hsecondUnits
  simp only [Units.val_mul] at hfirst hsecond
  rw [hfirst, hsecond]

end GradedOpposite

namespace IsDGAlgebra

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {G : InternalGrading R A} [GradedAlgebra G.piece] {d : A →ₗ[R] A}

/-- The Koszul-signed graded opposite of a differential graded algebra, with the same differential
on underlying elements. -/
theorem gradedOpposite (h : IsDGAlgebra G.piece d) :
    IsDGAlgebra (GradedOpposite.grading G).piece (GradedOpposite.differential G d) where
  map_mem := by
    intro p x hx
    rw [← GradedOpposite.op_unop G x, GradedOpposite.differential_op,
      GradedOpposite.op_mem_piece_iff]
    exact h.map_mem ((GradedOpposite.mem_piece_iff G p x).1 hx)
  sq_zero := by
    intro x
    rw [← GradedOpposite.op_unop G x, GradedOpposite.differential_op,
      GradedOpposite.differential_op, h.sq_zero, GradedOpposite.op_zero]
  leibniz := by
    intro p x hx y
    classical
    conv_lhs => rw [← DirectSum.sum_support_decompose (GradedOpposite.grading G).piece y,
      Finset.mul_sum, map_sum]
    conv_rhs =>
      rw [← DirectSum.sum_support_decompose (GradedOpposite.grading G).piece y,
        Finset.mul_sum, map_sum, Finset.mul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun q _ ↦ ?_
    rw [← GradedOpposite.op_unop G x,
      ← GradedOpposite.op_unop G (DirectSum.decompose (GradedOpposite.grading G).piece y q)]
    exact GradedOpposite.differential_leibniz_of_mem G h
      ((GradedOpposite.mem_piece_iff G p x).1 hx)
      ((GradedOpposite.mem_piece_iff G q _).1 (SetLike.coe_mem _))

end IsDGAlgebra

end TauCeti
