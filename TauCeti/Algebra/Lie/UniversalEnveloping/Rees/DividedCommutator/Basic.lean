/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.AssociatedGraded
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Basic

/-!
# The divided commutator of the PBW Rees algebra

Let `L` be a Lie algebra over a commutative ring `R`, with no freeness, finite-rank, or
characteristic-zero hypothesis. Because commutators in `UniversalEnvelopingAlgebra R L` drop PBW
filtration degree by at least one (`mul_sub_mul_mem_pbwFiltrationPrevious`), the commutator
`a * b - b * a` of any two elements of `reesAlgebra R L` has vanishing constant term and `n + 1`-st
coefficient in `pbwFiltration R L n`. Dividing by the central parameter `reesParameter R L` inside
`U(L)[X]` therefore produces a unique `R[X]`-bilinear **divided commutator**
`reesDividedCommutator R L : reesAlgebra R L →ₗ[R[X]] reesAlgebra R L →ₗ[R[X]] reesAlgebra R L`
obeying

`reesParameter R L * reesDividedCommutator R L a b = a * b - b * a`.

Because multiplication by `reesParameter R L` is central and injective
(`coeffSubalgebra.commute_X`, `coeffSubalgebra.X_mul_injective`), the generator formula,
alternation, skew-symmetry, left and right Leibniz rules, `reesParameter`-linearity, commutation
criterion, and the **Jacobi identity** hold already in `reesAlgebra R L`: the Jacobi identity
cancels `reesParameter R L` twice from the associative Jacobi identity for commutators.

## Main definitions

* `TauCeti.UniversalEnvelopingAlgebra.reesDividedCommutator`: the `R[X]`-bilinear divided
  commutator `(ab - ba)/t` on `reesAlgebra R L`, requiring no freeness hypothesis on `L`.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.commutator_coeff_mem_pbwFiltrationPrevious`: coefficients of a
  Rees commutator drop PBW filtration degree by one.
* `TauCeti.UniversalEnvelopingAlgebra.reesParameter_mul_reesDividedCommutator`: defining equation of
  the divided commutator.
* `TauCeti.UniversalEnvelopingAlgebra.reesDividedCommutator_eq_zero_iff`: vanishing characterizes
  commutation in `reesAlgebra R L`.
* `TauCeti.UniversalEnvelopingAlgebra.reesDividedCommutator_jacobi`: exact Jacobi identity of the
  divided commutator.

## References

* J. Dixmier, *Enveloping Algebras*, Graduate Studies in Mathematics 11, AMS (1996), §2.3, for
  filtered enveloping algebras and their Rees algebras.
-/

public section

open Polynomial

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v

section DividedCommutator

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

local notation "U" => _root_.UniversalEnvelopingAlgebra R L

/-- Every coefficient of a commutator in `reesAlgebra R L` lies one step lower in the PBW
filtration. -/
theorem commutator_coeff_mem_pbwFiltrationPrevious (a b : reesAlgebra R L) (n : ℕ) :
    ((a * b - b * a : reesAlgebra R L) : U[X]).coeff n ∈ pbwFiltrationPrevious R L n := by
  rw [Subalgebra.coe_sub, Subalgebra.coe_mul, Subalgebra.coe_mul, coeff_sub, coeff_mul, coeff_mul,
    ← Finset.Nat.sum_antidiagonal_swap (n := n)
      (f := fun x ↦ (b : U[X]).coeff x.1 * (a : U[X]).coeff x.2),
    ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun x hx ↦ ?_
  rw [← Finset.mem_antidiagonal.mp hx]
  exact mul_sub_mul_mem_pbwFiltrationPrevious R L
    (mem_coeffSubalgebra_iff.mp a.property x.1) (mem_coeffSubalgebra_iff.mp b.property x.2)

private theorem mul_reesParameter_injective :
    Function.Injective (LinearMap.mul R[X] (reesAlgebra R L) (reesParameter R L)) :=
  fun _ _ h ↦ reesParameter_mul_injective R L (by simpa only [LinearMap.mul_apply'] using h)

private theorem commutator_mem_range_mul_reesParameter (a b : reesAlgebra R L) :
    a * b - b * a ∈ LinearMap.range (LinearMap.mul R[X] (reesAlgebra R L) (reesParameter R L)) := by
  simp only [LinearMap.mem_range, LinearMap.mul_apply']
  refine (coeffSubalgebra.exists_X_mul_eq_iff (pbwFiltration R L) (one_mem_pbwFiltration R L 1)
    (a * b - b * a)).mpr ⟨?_, fun n ↦ ?_⟩
  · have hmem := commutator_coeff_mem_pbwFiltrationPrevious R L a b 0
    rwa [pbwFiltrationPrevious_zero, Submodule.mem_bot] at hmem
  · rw [← pbwFiltrationPrevious_succ]
    exact commutator_coeff_mem_pbwFiltrationPrevious R L a b (n + 1)

/-- The **divided commutator** on the PBW Rees algebra, sending `(a, b)` to the unique element `c`
satisfying `reesParameter R L * c = a * b - b * a`, bundled as an `R[X]`-bilinear map. Requires no
freeness hypothesis on `L`. -/
noncomputable def reesDividedCommutator :
    reesAlgebra R L →ₗ[R[X]] reesAlgebra R L →ₗ[R[X]] reesAlgebra R L :=
  -- Cache `AddCommGroup (reesAlgebra R L)` locally so `HSub` on the nested `R[X]`-bilinear
  -- map synthesizes (`reesAlgebra R L` is a `Subalgebra R U[X]` with a separate `Algebra R[X]`).
  letI : AddCommGroup (reesAlgebra R L) := inferInstance
  LinearMap.codRestrict₂
    (LinearMap.mul R[X] (reesAlgebra R L) - (LinearMap.mul R[X] (reesAlgebra R L)).flip)
    (LinearMap.mul R[X] (reesAlgebra R L) (reesParameter R L))
    (mul_reesParameter_injective R L)
    fun a b ↦ by
      simpa only [LinearMap.sub_apply, LinearMap.flip_apply, LinearMap.mul_apply'] using
        commutator_mem_range_mul_reesParameter R L a b

/-- **Defining relation of the divided commutator.** -/
@[simp]
theorem reesParameter_mul_reesDividedCommutator (a b : reesAlgebra R L) :
    reesParameter R L * reesDividedCommutator R L a b = a * b - b * a := by
  -- Same local `AddCommGroup` cache so `LinearMap.sub_apply` synthesizes on the nested map.
  let _ : AddCommGroup (reesAlgebra R L) := inferInstance
  rw [← LinearMap.mul_apply' (R := R[X]) (reesParameter R L), reesDividedCommutator,
    LinearMap.codRestrict₂_apply]
  simp only [LinearMap.sub_apply, LinearMap.flip_apply, LinearMap.mul_apply']

@[simp]
theorem coe_reesDividedCommutator (a b : reesAlgebra R L) :
    (reesDividedCommutator R L a b : U[X]) =
      ((a * b - b * a : reesAlgebra R L) : U[X]).divX := by
  ext n
  have hc := congrArg (fun z : reesAlgebra R L ↦ (z : U[X]).coeff (n + 1))
    (reesParameter_mul_reesDividedCommutator R L a b)
  rw [Subalgebra.coe_mul, coeffSubalgebra.coe_X, Polynomial.coeff_X_mul] at hc
  simpa only [Polynomial.coeff_divX] using hc

@[simp]
theorem reesDividedCommutator_mul_reesParameter (a b : reesAlgebra R L) :
    reesDividedCommutator R L a b * reesParameter R L = a * b - b * a := by
  rw [← (commute_reesParameter R L _).eq, reesParameter_mul_reesDividedCommutator]

@[simp]
theorem evalOne_reesDividedCommutator (a b : reesAlgebra R L) :
    coeffSubalgebra.evalOne (pbwFiltration R L) (reesDividedCommutator R L a b) =
      coeffSubalgebra.evalOne (pbwFiltration R L) a *
          coeffSubalgebra.evalOne (pbwFiltration R L) b -
        coeffSubalgebra.evalOne (pbwFiltration R L) b *
          coeffSubalgebra.evalOne (pbwFiltration R L) a := by
  have h := congrArg (coeffSubalgebra.evalOne (pbwFiltration R L))
    (reesParameter_mul_reesDividedCommutator R L a b)
  simpa only [map_mul, coeffSubalgebra.evalOne_X, one_mul, map_sub] using h

/-- `reesDividedCommutator R L a b` is the unique solution `c` to `a * b - b * a = t * c`. -/
theorem reesDividedCommutator_eq_iff {a b c : reesAlgebra R L} :
    reesDividedCommutator R L a b = c ↔ a * b - b * a = reesParameter R L * c := by
  refine ⟨fun h ↦ by rw [← h, reesParameter_mul_reesDividedCommutator], fun h ↦ ?_⟩
  exact (reesParameter_mul_right_inj R L).mp (by rw [reesParameter_mul_reesDividedCommutator, h])

/-- The divided commutator of two Rees elements vanishes if and only if they commute. -/
theorem reesDividedCommutator_eq_zero_iff {a b : reesAlgebra R L} :
    reesDividedCommutator R L a b = 0 ↔ Commute a b := by
  rw [reesDividedCommutator_eq_iff, mul_zero, sub_eq_zero, Commute, SemiconjBy]

@[simp]
theorem reesDividedCommutator_reesGenerator (x y : L) :
    reesDividedCommutator R L (reesGenerator R L x) (reesGenerator R L y) =
      reesGenerator R L ⁅x, y⁆ :=
  reesDividedCommutator_eq_iff R L |>.mpr (reesGenerator_mul_sub_mul R L x y)

@[simp]
theorem reesDividedCommutator_self (a : reesAlgebra R L) :
    reesDividedCommutator R L a a = 0 :=
  reesDividedCommutator_eq_iff R L |>.mpr (by simp)

theorem reesDividedCommutator_swap (a b : reesAlgebra R L) :
    reesDividedCommutator R L a b = -(reesDividedCommutator R L b a) :=
  eq_neg_iff_add_eq_zero.mpr <| (reesParameter_mul_right_inj R L).mp <| by
    rw [mul_add, reesParameter_mul_reesDividedCommutator, reesParameter_mul_reesDividedCommutator,
      mul_zero, sub_add_sub_cancel, sub_self]

theorem reesDividedCommutator_eq_zero_of_commute {a b : reesAlgebra R L} (h : Commute a b) :
    reesDividedCommutator R L a b = 0 :=
  (reesDividedCommutator_eq_zero_iff R L).mpr h

@[simp]
theorem reesDividedCommutator_reesParameter_left (a : reesAlgebra R L) :
    reesDividedCommutator R L (reesParameter R L) a = 0 :=
  reesDividedCommutator_eq_zero_of_commute R L (commute_reesParameter R L a)

@[simp]
theorem reesDividedCommutator_reesParameter_right (a : reesAlgebra R L) :
    reesDividedCommutator R L a (reesParameter R L) = 0 :=
  reesDividedCommutator_eq_zero_of_commute R L (commute_reesParameter R L a).symm

@[simp]
theorem reesDividedCommutator_algebraMap_left (r : R) (a : reesAlgebra R L) :
    reesDividedCommutator R L (algebraMap R (reesAlgebra R L) r) a = 0 :=
  reesDividedCommutator_eq_zero_of_commute R L (Algebra.commutes r a)

@[simp]
theorem reesDividedCommutator_algebraMap_right (a : reesAlgebra R L) (r : R) :
    reesDividedCommutator R L a (algebraMap R (reesAlgebra R L) r) = 0 :=
  reesDividedCommutator_eq_zero_of_commute R L (Algebra.commutes r a).symm

@[simp]
theorem reesDividedCommutator_algebraMap_polynomial_left (q : R[X]) (a : reesAlgebra R L) :
    reesDividedCommutator R L (algebraMap R[X] (reesAlgebra R L) q) a = 0 :=
  reesDividedCommutator_eq_zero_of_commute R L (Algebra.commutes q a)

@[simp]
theorem reesDividedCommutator_algebraMap_polynomial_right (a : reesAlgebra R L) (q : R[X]) :
    reesDividedCommutator R L a (algebraMap R[X] (reesAlgebra R L) q) = 0 :=
  reesDividedCommutator_eq_zero_of_commute R L (Algebra.commutes q a).symm

@[simp]
theorem reesDividedCommutator_one_left (a : reesAlgebra R L) :
    reesDividedCommutator R L 1 a = 0 := by
  simpa using reesDividedCommutator_algebraMap_left R L 1 a

@[simp]
theorem reesDividedCommutator_one_right (a : reesAlgebra R L) :
    reesDividedCommutator R L a 1 = 0 := by
  simpa using reesDividedCommutator_algebraMap_right R L a 1

@[simp]
theorem reesDividedCommutator_natCast_left (n : ℕ) (a : reesAlgebra R L) :
    reesDividedCommutator R L (n : reesAlgebra R L) a = 0 := by
  simpa using reesDividedCommutator_algebraMap_left R L (n : R) a

@[simp]
theorem reesDividedCommutator_natCast_right (a : reesAlgebra R L) (n : ℕ) :
    reesDividedCommutator R L a (n : reesAlgebra R L) = 0 := by
  simpa using reesDividedCommutator_algebraMap_right R L a (n : R)

@[simp]
theorem reesDividedCommutator_ofNat_left (n : ℕ) [n.AtLeastTwo] (a : reesAlgebra R L) :
    reesDividedCommutator R L (ofNat(n) : reesAlgebra R L) a = 0 :=
  reesDividedCommutator_natCast_left R L n a

@[simp]
theorem reesDividedCommutator_ofNat_right (a : reesAlgebra R L) (n : ℕ) [n.AtLeastTwo] :
    reesDividedCommutator R L a (ofNat(n) : reesAlgebra R L) = 0 :=
  reesDividedCommutator_natCast_right R L a n

private theorem reesParameter_mul_mul_reesDividedCommutator (x y z : reesAlgebra R L) :
    reesParameter R L * (x * reesDividedCommutator R L y z) = x * (y * z - z * y) := by
  rw [(commute_reesParameter R L x).left_comm, reesParameter_mul_reesDividedCommutator]

private theorem reesParameter_mul_reesDividedCommutator_mul (x y z : reesAlgebra R L) :
    reesParameter R L * (reesDividedCommutator R L y z * x) = (y * z - z * y) * x := by
  rw [← mul_assoc, reesParameter_mul_reesDividedCommutator]

/-- **Right Leibniz rule** for `reesDividedCommutator` in `reesAlgebra R L`. -/
theorem reesDividedCommutator_mul_right (a b c : reesAlgebra R L) :
    reesDividedCommutator R L a (b * c) =
      b * reesDividedCommutator R L a c + reesDividedCommutator R L a b * c :=
  (reesParameter_mul_right_inj R L).mp <| by
    rw [reesParameter_mul_reesDividedCommutator, mul_add,
      reesParameter_mul_mul_reesDividedCommutator, reesParameter_mul_reesDividedCommutator_mul]
    simp only [mul_sub, sub_mul, mul_assoc]
    abel

/-- **Left Leibniz rule** for `reesDividedCommutator` in `reesAlgebra R L`. -/
theorem reesDividedCommutator_mul_left (a b c : reesAlgebra R L) :
    reesDividedCommutator R L (a * b) c =
      a * reesDividedCommutator R L b c + reesDividedCommutator R L a c * b :=
  (reesParameter_mul_right_inj R L).mp <| by
    rw [reesParameter_mul_reesDividedCommutator, mul_add,
      reesParameter_mul_mul_reesDividedCommutator, reesParameter_mul_reesDividedCommutator_mul]
    simp only [mul_sub, sub_mul, mul_assoc]
    abel

@[simp]
theorem reesDividedCommutator_reesParameter_mul_left (a b : reesAlgebra R L) :
    reesDividedCommutator R L (reesParameter R L * a) b =
      reesParameter R L * reesDividedCommutator R L a b := by
  rw [reesDividedCommutator_mul_left, reesDividedCommutator_reesParameter_left, zero_mul, add_zero]

@[simp]
theorem reesDividedCommutator_reesParameter_mul_right (a b : reesAlgebra R L) :
    reesDividedCommutator R L a (reesParameter R L * b) =
      reesParameter R L * reesDividedCommutator R L a b := by
  rw [reesDividedCommutator_mul_right, reesDividedCommutator_reesParameter_right, zero_mul,
    add_zero]

/-- **Exact Jacobi identity** for `reesDividedCommutator` in `reesAlgebra R L`. -/
theorem reesDividedCommutator_jacobi (a b c : reesAlgebra R L) :
    reesDividedCommutator R L (reesDividedCommutator R L a b) c +
      reesDividedCommutator R L (reesDividedCommutator R L b c) a +
      reesDividedCommutator R L (reesDividedCommutator R L c a) b = 0 := by
  let : LieRing (reesAlgebra R L) := LieRing.ofAssociativeRing
  rw [← reesParameter_mul_right_inj R L, ← reesParameter_mul_right_inj R L]
  simp only [mul_zero, mul_add, reesParameter_mul_reesDividedCommutator, mul_sub]
  simp only [reesParameter_mul_mul_reesDividedCommutator,
    reesParameter_mul_reesDividedCommutator_mul, ← Ring.lie_def]
  rw [← lie_skew ⁅a, b⁆ c, ← lie_skew ⁅b, c⁆ a, ← lie_skew ⁅c, a⁆ b,
    ← neg_add, ← neg_add, neg_eq_zero, add_rotate, lie_jacobi]

end DividedCommutator

end TauCeti.UniversalEnvelopingAlgebra
