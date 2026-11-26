/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Norm

/-!
# The norm of a divisor along an extension of function fields

Let `F' / k'` be an extension of the field extension `F / k` with `F'` algebraic over `F`. The
**norm** of a divisor of `F' / k'` is the divisor of `F / k` obtained by sending each place `P'`
to `f(P' ∣ P) · P`, where `P = P'.restrict k F` is the place below `P'` and `f(P' ∣ P)` is the
relative degree, and extending additively:

`N(∑ n_{P'} P') = ∑ n_{P'} f(P' ∣ P) P`.

It is the pushforward of divisors along the covering of curves defined by `F ⊆ F'`, with the
residue degree weights that make it compatible with the field norm `N_{F'/F}`. For a finite
extension of an algebraic function field the norm of the divisor of a function is the divisor of
its norm, `N(div x) = div (N_{F'/F} x)`; this is the order-of-a-norm formula
`TauCeti.Place.ord_norm_of_isFunctionField` read coefficientwise. Together with the conorm
(`TauCeti.Divisor.conorm`), which pulls divisors back, it is the device that reduces statements
about divisors of a function field, such as Weil reciprocity, to the rational function field.

## Main definitions

* `TauCeti.Divisor.norm`: the norm homomorphism `N : Divisor k' F' →+ Divisor k F`.

## Main results

* `TauCeti.Divisor.norm_ofPoint`: the norm of a place is `f(P' ∣ P) · P`.
* `TauCeti.Divisor.norm_eq_sum_support`: `N(D) = ∑_{P' ∈ supp D} D(P') f(P' ∣ P) · P`.
* `TauCeti.Divisor.coeff_norm`: the coefficient of `N(D)` at `P` is `∑_{P' ∣ P} f(P' ∣ P) D(P')`.
* `TauCeti.Divisor.support_norm_subset`, `TauCeti.Divisor.norm_nonneg` and
  `TauCeti.Divisor.norm_mono`: `N(D)` is supported below the support of `D`, and `N` preserves
  effectivity and the order on divisors.
* `TauCeti.Divisor.norm_principal`: `N(div x) = div (N_{F'/F} x)` for a finite extension of an
  algebraic function field, with no separability hypothesis.
* `TauCeti.Divisor.degree_norm`: `deg N(D) = [k' : k] · deg D`.
* `TauCeti.Divisor.norm_conorm` and `TauCeti.Divisor.norm_conorm_of_isSeparable`:
  `N(Con D) = [F' : F] · D`.

## References

* W. Fulton, *Intersection Theory*, 2nd ed., Springer, 1998, Proposition 1.4 (proper pushforward
  of principal divisors).
-/

public section

namespace TauCeti

open AlgebraicGeometry

namespace Divisor

universe u u' v v'

variable {k : Type u} {k' : Type u'} {F : Type v} {F' : Type v'}
variable [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k' F'] [Algebra F F'] [Algebra k F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

variable (k F)

section Algebraic

variable [Algebra.IsIntegral F F']

/-- **The norm of a divisor** along an algebraic extension of function fields: the homomorphism
`Divisor k' F' →+ Divisor k F` sending a place `P'` to `f(P' ∣ P) · P`, where `P` is the place
below `P'`. The coefficient of `N(D)` at a place `P` is `∑_{P' ∣ P} f(P' ∣ P) D(P')`; see
`TauCeti.Divisor.coeff_norm`. -/
noncomputable def norm : Divisor k' F' →+ Divisor k F :=
  Finsupp.liftAddHom fun P' ↦
    zmultiplesHom (Divisor k F)
      ((Place.relativeDegree k F P' : ℤ) • WeilDivisor.ofPoint (P'.restrict k F))

/-- The norm of a place is `f(P' ∣ P) · P`, for the place `P` below `P'`. -/
@[simp]
theorem norm_ofPoint (P' : Place k' F') :
    norm k F (WeilDivisor.ofPoint P') =
      (Place.relativeDegree k F P' : ℤ) • WeilDivisor.ofPoint (P'.restrict k F) := by
  rw [← one_smul ℤ (WeilDivisor.ofPoint P'), ← WeilDivisor.single_eq_zsmul_ofPoint, norm,
    Finsupp.liftAddHom_apply_single, zmultiplesHom_apply, one_zsmul]

/-- **The coefficients of a norm**: the coefficient of `N(D)` at a place `P` is
`∑_{P' ∣ P} f(P' ∣ P) D(P')`, the sum running over the finite set `s` of places above `P`. -/
theorem coeff_norm (D : Divisor k' F') (P : Place k F) {s : Finset (Place k' F')}
    (hs : ∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) :
    (norm k F D).coeff P = ∑ P' ∈ s, (Place.relativeDegree k F P' : ℤ) * D.coeff P' := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE =>
    simp only [map_add, WeilDivisor.coeff_add, hD, hE, mul_add, Finset.sum_add_distrib]
  | single P' n =>
    rw [WeilDivisor.single_eq_zsmul_ofPoint, map_zsmul, norm_ofPoint]
    simp_rw [WeilDivisor.coeff_zsmul]
    by_cases h : P'.restrict k F = P
    · rw [Finset.sum_eq_single P' (fun Q _ hQ ↦ by simp [WeilDivisor.coeff_ofPoint_of_ne hQ])
        (fun hP' ↦ absurd ((hs P').mpr h) hP'), h]
      simp only [WeilDivisor.coeff_ofPoint_self]
      ring
    · rw [WeilDivisor.coeff_ofPoint_of_ne (Ne.symm h), Finset.sum_eq_zero fun Q hQ ↦ ?_]
      · simp
      rw [WeilDivisor.coeff_ofPoint_of_ne fun hQP ↦ h (by rw [← hQP]; exact (hs Q).mp hQ)]
      simp

/-- The norm of a divisor as a sum over its support:
`N(D) = ∑_{P' ∈ supp D} D(P') f(P' ∣ P) · P`, for `P` the place below `P'`. -/
theorem norm_eq_sum_support (D : Divisor k' F') :
    norm k F D = ∑ P' ∈ D.support,
      (D.coeff P' * Place.relativeDegree k F P') • WeilDivisor.ofPoint (P'.restrict k F) := by
  rw [norm, Finsupp.liftAddHom_apply]
  refine Finset.sum_congr rfl fun P' _ ↦ ?_
  dsimp only
  rw [zmultiplesHom_apply, mul_smul]
  -- `D.coeff P'` is by definition the value `D P'` of the underlying finsupp.
  rfl

/-- The norm of a divisor is supported below its support: a place `P` with nonzero coefficient
in `N(D)` lies under a place `P'` with nonzero coefficient in `D`. -/
theorem support_norm_subset (D : Divisor k' F') :
    ((norm k F D).support : Set (Place k F)) ⊆
      (fun P' : Place k' F' ↦ P'.restrict k F) '' D.support := by
  classical
  intro P hP
  rw [Finset.mem_coe, norm_eq_sum_support] at hP
  obtain ⟨P', hP', hPP'⟩ := Finset.mem_biUnion.1 (Finsupp.support_finsetSum hP)
  have hPP'' := Finsupp.support_smul hPP'
  rw [WeilDivisor.support_ofPoint, Finset.mem_singleton] at hPP''
  exact ⟨P', hP', hPP''.symm⟩

/-- The norm of an effective divisor is effective. -/
theorem norm_nonneg {D : Divisor k' F'} (hD : 0 ≤ D) : 0 ≤ norm k F D := by
  rw [norm_eq_sum_support]
  exact Finset.sum_nonneg fun P' _ ↦ zsmul_nonneg (WeilDivisor.ofPoint_nonneg _)
    (mul_nonneg (WeilDivisor.coeff_nonneg hD P') (by positivity))

/-- The norm of divisors is monotone. -/
theorem norm_mono : Monotone (norm k F : Divisor k' F' → Divisor k F) := fun D E h ↦ by
  simpa only [map_sub, sub_nonneg] using norm_nonneg k F (sub_nonneg.2 h)

/-- **The degree of a norm**: `deg N(D) = [k' : k] · deg D`. On a place this is
`f(P' ∣ P) · deg P = [k' : k] · deg P'`, the comparison of the degrees of a place and of the place
below it. -/
theorem degree_norm (D : Divisor k' F') :
    degree (norm k F D) = Module.finrank k k' * degree D := by
  induction D using Finsupp.induction_linear with
  | zero => simp
  | add D E hD hE => simp only [map_add, hD, hE, mul_add]
  | single P' n =>
    rw [WeilDivisor.single_eq_zsmul_ofPoint, map_zsmul, norm_ofPoint, degree_zsmul, degree_zsmul,
      degree_zsmul, degree_ofPoint, degree_ofPoint]
    have := congrArg (Nat.cast : ℕ → ℤ)
      (Place.finrank_mul_degree_eq_relativeDegree_mul_degree_restrict k F P')
    push_cast at this
    linear_combination -n * this

end Algebraic

variable [FiniteDimensional F F'] [Algebra.IsIntegral k k']

/-- **The norm of a principal divisor** (Fulton, Proposition 1.4(b)): for a finite extension
`F' / F` of an algebraic function field `F / k`, the norm of the divisor of `x ∈ F'ˣ` is the divisor
of its norm, `N(div x) = div (N_{F'/F} x)`. No separability hypothesis is needed. -/
theorem norm_principal (hF : IsFunctionField k F) (hF' : IsFunctionField k' F') (x : F'ˣ) :
    norm k F (principal hF' x) = principal hF (Units.map (Algebra.norm F : F' →* F) x) := by
  refine WeilDivisor.ext fun P ↦ ?_
  have hfin := Place.finite_setOf_restrict_eq (k' := k') (F' := F') k F P
  rw [coeff_norm k F _ P (s := hfin.toFinset) fun _ ↦ Set.Finite.mem_toFinset _, coeff_principal,
    Units.coe_map, Place.ord_norm_of_isFunctionField hF P (s := hfin.toFinset)
      fun _ ↦ Set.Finite.mem_toFinset _]
  simp

omit [Algebra.IsIntegral k k'] in
/-- The norm of a conorm is `[F' : F] · D` wherever the fundamental identity holds. -/
private theorem norm_conorm_of_fundamental_identity
    (h : ∀ (P : Place k F) {s : Finset (Place k' F')},
      (∀ P' : Place k' F', P' ∈ s ↔ P'.restrict k F = P) →
        ∑ P' ∈ s, Place.ramificationIdx F P' * Place.relativeDegree k F P' =
          Module.finrank F F')
    (D : Divisor k F) : norm k F (conorm k' F' D) = (Module.finrank F F' : ℤ) • D := by
  refine WeilDivisor.ext fun P ↦ ?_
  have hfin := Place.finite_setOf_restrict_eq (k' := k') (F' := F') k F P
  have hs : ∀ P' : Place k' F', P' ∈ hfin.toFinset ↔ P'.restrict k F = P :=
    fun _ ↦ Set.Finite.mem_toFinset _
  rw [coeff_norm k F _ P hs, WeilDivisor.coeff_zsmul, ← h P hs, Nat.cast_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun P' hP' ↦ ?_
  rw [coeff_conorm, (hs P').mp hP']
  push_cast
  ring

/-- **The norm of a conorm** for a separable extension: `N(Con D) = [F' : F] · D`, by the
fundamental identity `∑_{P' ∣ P} e(P' ∣ P) f(P' ∣ P) = [F' : F]`. When `F / k` is an algebraic
function field no separability is needed; that is `TauCeti.Divisor.norm_conorm`. -/
theorem norm_conorm_of_isSeparable [Algebra.IsSeparable F F'] (D : Divisor k F) :
    norm k F (conorm k' F' D) = (Module.finrank F F' : ℤ) • D :=
  norm_conorm_of_fundamental_identity k F
    (fun P _ hs ↦ Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isSeparable k F P hs) D

/-- **The norm of a conorm**: for a finite extension `F' / F` of an algebraic function field
`F / k`, `N(Con D) = [F' : F] · D`, by the fundamental identity
`∑_{P' ∣ P} e(P' ∣ P) f(P' ∣ P) = [F' : F]`. No separability hypothesis is needed. -/
theorem norm_conorm (hF : IsFunctionField k F) (D : Divisor k F) :
    norm k F (conorm k' F' D) = (Module.finrank F F' : ℤ) • D :=
  norm_conorm_of_fundamental_identity k F (fun P _ hs ↦
    Place.sum_ramificationIdx_mul_relativeDegree_eq_finrank_of_isFunctionField k F hF P hs) D

end Divisor

end TauCeti
