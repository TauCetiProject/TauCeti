/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Basic
public import Mathlib.Algebra.Star.Module

/-!
# The analytic adjoint on Temperley–Lieb algebras

For a self-adjoint loop parameter in a commutative star semiring, the Temperley–Lieb algebra
has an involution fixing the generators, reversing products and conjugating coefficients.
Over the complex numbers this is the analytic adjoint for a real loop parameter, rather than
the coefficient-linear reflection. It supplies the star algebra in which positivity of the
closure trace can be formulated; no positivity is asserted here.

The instance requires `Fact (IsSelfAdjoint δ)`. The universal property `map_star_iff` says
that an algebra map preserves the adjoint exactly when its generator images are self-adjoint.
The adjoint is unique, commutes with the strand inclusions and preserves the augmentation.
Conversely, even on two strands, a conjugate-linear product reversal fixing the generator
forces the loop parameter to be self-adjoint.

The conjugate-opposite construction follows `TauCeti.InfiniteTypeAHeckeAlgebra.conjugateReverse`
in `TauCeti.Algebra.TypeAHeckeAlgebra.Star`: twist the target scalar action by `starRingEnd`,
then apply the presentation's universal property. No Hecke algebra results are imported.

## References

* D. Penneys, *Unitary Quantum Symmetries Lite*, Chapter 4, Sections 4.1–4.3.
-/

public section

namespace TauCeti.TemperleyLieb

open MulOpposite

variable {R : Type*} [CommSemiring R] [StarRing R] {δ : R} {n : ℕ}

section Construction

variable [hδ : Fact (IsSelfAdjoint δ)]

/-- Conjugate-linear word reversal, viewed as a ring map into the opposite algebra. -/
private def conjugateReverse : TemperleyLieb R δ n →+* (TemperleyLieb R δ n)ᵐᵒᵖ := by
  letI : Algebra R (TemperleyLieb R δ n)ᵐᵒᵖ := Algebra.compHom _ (starRingEnd R)
  exact (lift (fun i ↦ op (e δ i))
    (fun i ↦ unop_injective <| by
      simp only [unop_mul, unop_op, Algebra.smul_def,
        Algebra.compHom_algebraMap_apply, starRingEnd_apply, MulOpposite.algebraMap_apply,
        hδ.out.star_eq]
      rw [e_mul_self, Algebra.smul_def, Algebra.commutes])
    (fun {_ _} h ↦ unop_injective <| by simpa [mul_assoc] using e_mul_e_mul_e (δ := δ) h)
    (fun {_ _} h ↦ unop_injective <| (commute_e (δ := δ) h).eq.symm)).toRingHom

private theorem conjugateReverse_e (i : Fin (n - 1)) :
    conjugateReverse (e δ i) = op (e δ i) := by
  simp [conjugateReverse]

private theorem conjugateReverse_algebraMap (r : R) :
    conjugateReverse (algebraMap R (TemperleyLieb R δ n) r) =
      op (algebraMap R _ (star r)) := by
  simp [conjugateReverse, Algebra.compHom_algebraMap_apply, starRingEnd_apply]

private theorem conjugateReverse_involutive (x : TemperleyLieb R δ n) :
    unop (conjugateReverse (unop (conjugateReverse x))) = x := by
  induction x using TemperleyLieb.induction with
  | e i => simp [conjugateReverse_e]
  | algebraMap r => simp [conjugateReverse_algebraMap]
  | add x y hx hy => simp [map_add, hx, hy]
  | mul x y hx hy => simp [map_mul, hx, hy]

/-- The analytic adjoint fixes generators and conjugates scalars at a self-adjoint loop
parameter. In particular, real loop parameters give complex star algebras. -/
@[no_expose]
instance instStarRing : StarRing (TemperleyLieb R δ n) where
  star x := unop (conjugateReverse x)
  star_involutive := conjugateReverse_involutive
  star_mul x y := by simp [map_mul]
  star_add x y := by simp [map_add]

/-- Each Temperley–Lieb generator is self-adjoint. -/
@[simp]
theorem star_e (i : Fin (n - 1)) : star (e δ i) = e δ i :=
  congrArg unop (conjugateReverse_e i)

private theorem star_algebraMap (r : R) :
    star (algebraMap R (TemperleyLieb R δ n) r) = algebraMap R _ (star r) :=
  congrArg unop (conjugateReverse_algebraMap r)

/-- The analytic adjoint conjugates coefficients. -/
instance instStarModule : StarModule R (TemperleyLieb R δ n) where
  star_smul r x := by simp [Algebra.smul_def, star_mul, star_algebraMap, Algebra.commutes]

/-- A conjugate-linear unital product reversal fixing the generators is the analytic adjoint.
Involutivity need not be assumed for uniqueness. -/
theorem eq_star (f : TemperleyLieb R δ n →ₗ⋆[R] TemperleyLieb R δ n)
    (hone : f 1 = 1) (hmul : ∀ x y, f (x * y) = f y * f x)
    (he : ∀ i, f (e δ i) = e δ i) (x : TemperleyLieb R δ n) : f x = star x := by
  induction x using TemperleyLieb.induction with
  | e i => simp [he]
  | algebraMap r =>
    simp [Algebra.algebraMap_eq_smul_one, hone, starRingEnd_apply]
  | add x y hx hy => simp [hx, hy]
  | mul x y hx hy => simp [hmul, hx, hy]

section UniversalProperty

variable {A : Type*} [Semiring A] [StarRing A] [Algebra R A] [StarModule R A]

/-- An algebra map preserves the analytic adjoint exactly when all generator images are
self-adjoint. -/
theorem map_star_iff {F : TemperleyLieb R δ n →ₐ[R] A} :
    (∀ x, F (star x) = star (F x)) ↔ ∀ i, IsSelfAdjoint (F (e δ i)) := by
  constructor
  · intro h i
    simpa only [IsSelfAdjoint, star_e] using (h (e δ i)).symm
  · intro h x
    induction x using TemperleyLieb.induction with
    | e i => simp only [star_e, (h i).star_eq]
    | algebraMap r => simp [← algebraMap_star_comm]
    | add x y hx hy => simp only [star_add, map_add, hx, hy]
    | mul x y hx hy => simp only [star_mul, map_mul, hx, hy]

end UniversalProperty

/-- Adding a straight last strand commutes with the analytic adjoint. -/
@[simp]
theorem strandIncl_star (x : TemperleyLieb R δ (n + 1)) :
    strandIncl (star x) = star (strandIncl x) :=
  map_star_iff.mpr (fun i ↦ by simp [IsSelfAdjoint]) x

/-- The augmentation preserves the analytic adjoint. On zero and one strands, where the
augmentation is an equivalence with the coefficient semiring, the adjoint is scalar star. -/
@[simp]
theorem aug_star (x : TemperleyLieb R δ n) : aug (star x) = star (aug x) :=
  map_star_iff.mpr (fun i ↦ by simp [IsSelfAdjoint]) x

end Construction

/-- Already on two strands, a conjugate-linear product reversal fixing the generator forces
the loop parameter to be self-adjoint. Thus non-real complex parameters admit no analytic
adjoint with self-adjoint generators. -/
theorem isSelfAdjoint_loop_of_reverse
    (f : TemperleyLieb R δ 2 →ₗ⋆[R] TemperleyLieb R δ 2)
    (hmul : ∀ x y, f (x * y) = f y * f x) (he : f (e δ 0) = e δ 0) :
    IsSelfAdjoint δ := by
  have h := hmul (e δ 0) (e δ 0)
  rw [e_mul_self, f.map_smulₛₗ, he, e_mul_self] at h
  have hentry := congrArg (fun x ↦ twoStrandRep δ x 1 0) h
  simpa [IsSelfAdjoint, starRingEnd_apply] using hentry

end TauCeti.TemperleyLieb
