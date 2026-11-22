/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Abelian
public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Functoriality
import Mathlib.Tactic.NoncommRing

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
alternation, skew-symmetry, left and right Leibniz rules, `reesParameter`-linearity, naturality
along Lie homomorphisms, commutation criterion, and the **Jacobi identity** hold already in
`reesAlgebra R L`: the Jacobi identity cancels `reesParameter R L` twice from the associative
Jacobi identity for commutators.

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
* `TauCeti.UniversalEnvelopingAlgebra.reesMap_reesDividedCommutator`: naturality under Lie
  homomorphisms.

## References

* J. Dixmier, *Enveloping Algebras*, Graduate Studies in Mathematics 11, AMS (1996), §2.3, for
  filtered enveloping algebras and their Rees algebras.
-/

public section

open Polynomial

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

section DividedCommutator

variable (R : Type u) (L : Type v) [CommRing R] [LieRing L] [LieAlgebra R L]

attribute [local instance 100] LieRing.ofAssociativeRing

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

private noncomputable def reesDividedCommutatorAux (a b : reesAlgebra R L) : reesAlgebra R L :=
  coeffSubalgebra.divX (pbwFiltration R L) (a * b - b * a) fun n ↦ by
    rw [← pbwFiltrationPrevious_succ]
    exact commutator_coeff_mem_pbwFiltrationPrevious R L a b (n + 1)

private theorem reesParameter_mul_reesDividedCommutatorAux (a b : reesAlgebra R L) :
    reesParameter R L * reesDividedCommutatorAux R L a b = a * b - b * a :=
  coeffSubalgebra.X_mul_divX (pbwFiltration R L) (one_mem_pbwFiltration R L 1) (a * b - b * a)
    (by
      have hmem := commutator_coeff_mem_pbwFiltrationPrevious R L a b 0
      rwa [pbwFiltrationPrevious_zero, Submodule.mem_bot] at hmem)
    (fun n ↦ by
      rw [← pbwFiltrationPrevious_succ]
      exact commutator_coeff_mem_pbwFiltrationPrevious R L a b (n + 1))

private theorem reesParameter_mul_cancel {x y : reesAlgebra R L}
    (h : reesParameter R L * x = reesParameter R L * y) : x = y :=
  coeffSubalgebra.X_mul_injective (pbwFiltration R L) (one_mem_pbwFiltration R L 1) h

private theorem commute_reesParameter (a : reesAlgebra R L) :
    Commute (reesParameter R L) a :=
  coeffSubalgebra.commute_X (pbwFiltration R L) (one_mem_pbwFiltration R L 1) a

/-- The **divided commutator** on the PBW Rees algebra, sending `(a, b)` to the unique element `c`
satisfying `reesParameter R L * c = a * b - b * a`, bundled as an `R[X]`-bilinear map. Requires no
freeness hypothesis on `L`. -/
noncomputable def reesDividedCommutator :
    reesAlgebra R L →ₗ[R[X]] reesAlgebra R L →ₗ[R[X]] reesAlgebra R L :=
  LinearMap.mk₂ R[X] (reesDividedCommutatorAux R L)
    (fun a₁ a₂ b ↦ reesParameter_mul_cancel R L <| by
      rw [mul_add, reesParameter_mul_reesDividedCommutatorAux,
        reesParameter_mul_reesDividedCommutatorAux, reesParameter_mul_reesDividedCommutatorAux]
      noncomm_ring)
    (fun q a b ↦ reesParameter_mul_cancel R L <| by
      rw [mul_smul_comm, reesParameter_mul_reesDividedCommutatorAux,
        reesParameter_mul_reesDividedCommutatorAux, smul_mul_assoc, mul_smul_comm, smul_sub])
    (fun a b₁ b₂ ↦ reesParameter_mul_cancel R L <| by
      rw [mul_add, reesParameter_mul_reesDividedCommutatorAux,
        reesParameter_mul_reesDividedCommutatorAux, reesParameter_mul_reesDividedCommutatorAux]
      noncomm_ring)
    (fun q a b ↦ reesParameter_mul_cancel R L <| by
      rw [mul_smul_comm, reesParameter_mul_reesDividedCommutatorAux,
        reesParameter_mul_reesDividedCommutatorAux, mul_smul_comm, smul_mul_assoc, smul_sub])

@[simp]
theorem coe_reesDividedCommutator (a b : reesAlgebra R L) :
    (reesDividedCommutator R L a b : U[X]) =
      ((a * b - b * a : reesAlgebra R L) : U[X]).divX :=
  coeffSubalgebra.coe_divX (a * b - b * a) _

/-- **Defining relation of the divided commutator.** -/
@[simp]
theorem reesParameter_mul_reesDividedCommutator (a b : reesAlgebra R L) :
    reesParameter R L * reesDividedCommutator R L a b = a * b - b * a :=
  reesParameter_mul_reesDividedCommutatorAux R L a b

@[simp]
theorem reesDividedCommutator_mul_reesParameter (a b : reesAlgebra R L) :
    reesDividedCommutator R L a b * reesParameter R L = a * b - b * a := by
  rw [← (commute_reesParameter R L _).eq, reesParameter_mul_reesDividedCommutator]

/-- `reesDividedCommutator R L a b` is the unique solution `c` to `a * b - b * a = t * c`. -/
theorem reesDividedCommutator_eq_iff {a b c : reesAlgebra R L} :
    reesDividedCommutator R L a b = c ↔ a * b - b * a = reesParameter R L * c := by
  refine ⟨fun h ↦ by rw [← h, reesParameter_mul_reesDividedCommutator], fun h ↦ ?_⟩
  exact reesParameter_mul_cancel R L (by rw [reesParameter_mul_reesDividedCommutator, h])

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
  eq_neg_iff_add_eq_zero.mpr <| reesParameter_mul_cancel R L <| by
    rw [mul_add, reesParameter_mul_reesDividedCommutator, reesParameter_mul_reesDividedCommutator,
      mul_zero, sub_add_sub_cancel, sub_self]

theorem reesDividedCommutator_of_commute {a b : reesAlgebra R L} (h : Commute a b) :
    reesDividedCommutator R L a b = 0 :=
  (reesDividedCommutator_eq_zero_iff R L).mpr h

@[simp]
theorem reesDividedCommutator_reesParameter_left (a : reesAlgebra R L) :
    reesDividedCommutator R L (reesParameter R L) a = 0 :=
  reesDividedCommutator_of_commute R L (commute_reesParameter R L a)

@[simp]
theorem reesDividedCommutator_reesParameter_right (a : reesAlgebra R L) :
    reesDividedCommutator R L a (reesParameter R L) = 0 :=
  reesDividedCommutator_of_commute R L (commute_reesParameter R L a).symm

@[simp]
theorem reesDividedCommutator_algebraMap_left (r : R) (a : reesAlgebra R L) :
    reesDividedCommutator R L (algebraMap R (reesAlgebra R L) r) a = 0 :=
  reesDividedCommutator_of_commute R L (Algebra.commutes r a)

@[simp]
theorem reesDividedCommutator_algebraMap_right (a : reesAlgebra R L) (r : R) :
    reesDividedCommutator R L a (algebraMap R (reesAlgebra R L) r) = 0 :=
  reesDividedCommutator_of_commute R L (Algebra.commutes r a).symm

@[simp]
theorem reesDividedCommutator_one_left (a : reesAlgebra R L) :
    reesDividedCommutator R L 1 a = 0 := by
  simpa using reesDividedCommutator_algebraMap_left R L 1 a

@[simp]
theorem reesDividedCommutator_one_right (a : reesAlgebra R L) :
    reesDividedCommutator R L a 1 = 0 := by
  simpa using reesDividedCommutator_algebraMap_right R L a 1

/-- **Right Leibniz rule** for `reesDividedCommutator` in `reesAlgebra R L`. -/
theorem reesDividedCommutator_mul_right (a b c : reesAlgebra R L) :
    reesDividedCommutator R L a (b * c) =
      b * reesDividedCommutator R L a c + reesDividedCommutator R L a b * c :=
  reesParameter_mul_cancel R L <| by
    rw [reesParameter_mul_reesDividedCommutator, mul_add,
      (commute_reesParameter R L b).left_comm, reesParameter_mul_reesDividedCommutator,
      ← mul_assoc (reesParameter R L), reesParameter_mul_reesDividedCommutator]
    simp only [mul_sub, sub_mul, mul_assoc]
    abel

/-- **Left Leibniz rule** for `reesDividedCommutator` in `reesAlgebra R L`. -/
theorem reesDividedCommutator_mul_left (a b c : reesAlgebra R L) :
    reesDividedCommutator R L (a * b) c =
      a * reesDividedCommutator R L b c + reesDividedCommutator R L a c * b :=
  reesParameter_mul_cancel R L <| by
    rw [reesParameter_mul_reesDividedCommutator, mul_add,
      (commute_reesParameter R L a).left_comm, reesParameter_mul_reesDividedCommutator,
      ← mul_assoc (reesParameter R L), reesParameter_mul_reesDividedCommutator]
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

/-- **Exact Jacobi identity** for `reesDividedCommutator` in `reesAlgebra R L`, proved by
cancelling `reesParameter R L` twice from the associative Jacobi identity. -/
theorem reesDividedCommutator_jacobi (a b c : reesAlgebra R L) :
    reesDividedCommutator R L (reesDividedCommutator R L a b) c +
      reesDividedCommutator R L (reesDividedCommutator R L b c) a +
      reesDividedCommutator R L (reesDividedCommutator R L c a) b = 0 := by
  apply reesParameter_mul_cancel R L
  apply reesParameter_mul_cancel R L
  simp only [mul_zero, mul_add, reesParameter_mul_reesDividedCommutator, mul_sub]
  rw [← mul_assoc (reesParameter R L), reesParameter_mul_reesDividedCommutator,
    (commute_reesParameter R L c).left_comm, reesParameter_mul_reesDividedCommutator,
    ← mul_assoc (reesParameter R L), reesParameter_mul_reesDividedCommutator,
    (commute_reesParameter R L a).left_comm, reesParameter_mul_reesDividedCommutator,
    ← mul_assoc (reesParameter R L), reesParameter_mul_reesDividedCommutator,
    (commute_reesParameter R L b).left_comm, reesParameter_mul_reesDividedCommutator]
  noncomm_ring [neg_neg]

/-- Naturality of `reesDividedCommutator` along a Lie algebra homomorphism. -/
@[simp]
theorem reesMap_reesDividedCommutator {M : Type w} [LieRing M] [LieAlgebra R M]
    (f : L →ₗ⁅R⁆ M) (a b : reesAlgebra R L) :
    reesMap R f (reesDividedCommutator R L a b) =
      reesDividedCommutator R M (reesMap R f a) (reesMap R f b) :=
  ((reesDividedCommutator_eq_iff R M).mpr <| by
    calc
      reesMap R f a * reesMap R f b - reesMap R f b * reesMap R f a
        = reesMap R f (a * b - b * a) := by simp
      _ = reesMap R f (reesParameter R L * reesDividedCommutator R L a b) := by
          rw [← reesParameter_mul_reesDividedCommutator]
      _ = reesParameter R M * reesMap R f (reesDividedCommutator R L a b) := by
          rw [map_mul, reesMap_reesParameter]).symm

/-- Over an abelian Lie algebra, `reesAlgebra R L` is commutative (`Abelian.instCommRing`), so its
divided commutator vanishes identically. -/
@[simp]
theorem reesDividedCommutator_eq_zero [IsLieAbelian L] (a b : reesAlgebra R L) :
    reesDividedCommutator R L a b = 0 :=
  reesDividedCommutator_of_commute R L (mul_comm a b)

end DividedCommutator

end TauCeti.UniversalEnvelopingAlgebra
