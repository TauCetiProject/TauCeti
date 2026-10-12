/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.MonoidAlgebra.NotReduced
public import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Étaleness of finite commutative group algebras

A finite commutative group algebra is étale when the group order is invertible in the
base ring. Over a field this condition is also necessary: torsion of prime order equal
to the characteristic produces a nonzero nilpotent. Applied to character groups, this
detects the infinitesimal structure of finite diagonalizable groups.

## References

* J. S. Milne, *Algebraic Groups* (2017), §12, diagonalizable groups.

The converse uses `TauCeti.not_isReduced_monoidAlgebra` and Mathlib's Cauchy theorem.
-/

public section

open MonoidAlgebra

namespace TauCeti.MonoidAlgebra

variable (R G : Type*) [CommRing R] [CommGroup G] [Finite G]

omit [Finite G] in
/-- A commutative group algebra is formally unramified if its group order is
invertible in the base ring. -/
theorem formallyUnramified_of_isUnit_card (h : IsUnit (Nat.card G : R)) :
    Algebra.FormallyUnramified R (MonoidAlgebra R G) := by
  constructor
  suffices (⊤ : Submodule (MonoidAlgebra R G)
      (KaehlerDifferential R (MonoidAlgebra R G))) ≤ ⊥ from
    (subsingleton_iff_forall_eq 0).mpr fun x => this trivial
  rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  let D := KaehlerDifferential.D R (MonoidAlgebra R G)
  have hsingle (g : G) : D (single g 1) = 0 := by
    have hp : (single g (1 : R)) ^ Nat.card G = 1 := by
      simp [single_pow, ← one_def]
    have hd := D.leibniz_pow (a := single g 1) (Nat.card G)
    rw [hp, D.map_one_eq_zero, ← Nat.cast_smul_eq_nsmul R] at hd
    have hu : IsUnit ((single g (1 : R)) ^ (Nat.card G - 1)) :=
      ((Group.isUnit g).map (MonoidAlgebra.of R G)).pow _
    exact hu.smul_eq_zero.mp (h.smul_eq_zero.mp hd.symm)
  have hzero (y : MonoidAlgebra R G) : D y = 0 := by
    induction y using MonoidAlgebra.induction_linear with
    | zero => exact D.map_zero
    | add x y hx hy => exact (D.map_add x y).trans (by rw [hx, hy, add_zero])
    | single g r =>
      simpa only [smul_single, smul_eq_mul, mul_one] using
        (D.map_smul r (single g 1)).trans (by rw [hsingle, smul_zero])
  exact hzero x

/-- A finite commutative group algebra is étale if its group order is invertible in
the base ring. This includes arbitrary, possibly non-Noetherian, base rings. -/
theorem etale_of_isUnit_card (h : IsUnit (Nat.card G : R)) :
    Algebra.Etale R (MonoidAlgebra R G) := by
  let := formallyUnramified_of_isUnit_card R G h
  let := Module.finitePresentation_of_projective R (MonoidAlgebra R G)
  exact Algebra.Etale.of_formallyUnramified_of_flat

/-- Over a field, a finite commutative group algebra is étale exactly when its group
order is invertible, equivalently when the characteristic does not divide that order. -/
theorem etale_iff_isUnit_card (k : Type*) [Field k] :
    Algebra.Etale k (MonoidAlgebra k G) ↔ IsUnit (Nat.card G : k) := by
  refine ⟨fun he => ?_, etale_of_isUnit_card k G⟩
  let := he
  by_contra h
  exact not_isReduced_monoidAlgebra_of_not_isUnit_card k G h
    (Algebra.FormallyUnramified.isReduced_of_field k _)

end TauCeti.MonoidAlgebra
