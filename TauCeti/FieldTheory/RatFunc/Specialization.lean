/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
public import TauCeti.FieldTheory.RatFunc.NumDenom

/-!
# Specializing the parameter of polynomials over `K(T)`

Hilbert's irreducibility theorem compares a polynomial `p(T, Y)` with coefficients in the rational
function field `K(T)` with its specializations `p(t, Y) ∈ K[Y]` at parameters `t ∈ K`. This file
sets up that specialization map over an arbitrary field `K`, keeping track of where it behaves
like a ring map and where it preserves the degree in `Y`.

Mathlib's evaluation `RatFunc.eval (RingHom.id K) t f = num(f)(t) / denom(f)(t)` uses the reduced
numerator and denominator and is total: at a pole it returns `0`. It is therefore not a ring map on
`K(T)` (at `t = 0`, `T · T⁻¹ = 1` has value `1` while the product of the values is `0`). It is a
ring map on the subring `Rₜ` of functions regular at `t`, the valuation ring of the finite place
`T = t`, and the specialization of polynomials respects sums and products of polynomials whose
coefficients lie in `Rₜ`.

The degree in `Y` is preserved as soon as the leading coefficient has a nonzero value at `t`. The
*guard* `D(p) · num(lc(p))`, the product of the reduced denominators of the coefficients times the
numerator of the leading coefficient, is a nonzero polynomial in `T` for `p ≠ 0`, and away from its
roots every coefficient is regular and the degree is preserved. So the bad parameters of any
polynomial form a finite set, and over an infinite field a finite family of polynomials has a
common good parameter outside any given finite set. None of this says anything about
irreducibility of the specializations: `Y² − T` is regular of degree two at every `t`, while
`Y² − 4` is reducible.

## Main definitions

* `TauCeti.RationalSpecialization.regularSubring t`: the subring `Rₜ` of `K(T)` of functions
  regular at `t`, the valuation ring of `TauCeti.Place.adicOfIrreducible` at `T - t`.
* `TauCeti.RationalSpecialization.regularEval t`: evaluation at `t` as a ring map `Rₜ →+* K`.
* `TauCeti.RationalSpecialization.specialize t p`: the coefficientwise specialization
  `p(T, Y) ↦ p(t, Y)` of `p ∈ K(T)[Y]`, a total function `K(T)[Y] → K[Y]`.
* `TauCeti.RationalSpecialization.denomProduct p`: the product `D(p)` of the reduced denominators
  of the nonzero coefficients of `p`.
* `TauCeti.RationalSpecialization.specializationGuard p`: the polynomial `D(p) · num(lc(p))`.

## Main results

* `TauCeti.RationalSpecialization.mem_regularSubring_iff`: `f ∈ Rₜ` exactly when the reduced
  denominator of `f` does not vanish at `t`.
* `TauCeti.RationalSpecialization.algebraMap_regularEval`: `regularEval t` is the residue map of
  the place `T = t`.
* `TauCeti.RationalSpecialization.coeff_specialize`,
  `TauCeti.RationalSpecialization.specialize_map_subtype`,
  `TauCeti.RationalSpecialization.specialize_add` and
  `TauCeti.RationalSpecialization.specialize_mul`: specialization is coefficientwise evaluation,
  and it is additive and multiplicative on polynomials with coefficients regular at `t`.
* `TauCeti.RationalSpecialization.eval_denomProduct_ne_zero_iff`: `D(p)(t) ≠ 0` exactly when
  every coefficient of `p` is regular at `t`.
* `TauCeti.RationalSpecialization.natDegree_specialize_of_eval_specializationGuard_ne_zero` and
  `TauCeti.RationalSpecialization.finite_setOf_exists_eval_denom_coeff_eq_zero_or_natDegree_ne`:
  away from the finitely many roots of the guard, specialization has regular coefficients and
  preserves the degree.
* `TauCeti.RationalSpecialization.exists_notMem_forall_eval_denom_coeff_ne_zero_and_natDegree_eq`:
  over an infinite field, a finite family of polynomials has a common such parameter
  outside a prescribed finite set.

## References

* P. Dèbes, *Arithmétique des revêtements de la droite*, §§5.2.1–5.2.2.
-/

public section

noncomputable section

open Polynomial

namespace TauCeti.RationalSpecialization

variable {K : Type*} [Field K]

/-! ### Rational functions regular at a point -/

/-- The subring `Rₜ` of rational functions regular at `t`: the valuation ring of the finite place
of `K(T)` at the irreducible polynomial `T - t`. By `mem_regularSubring_iff`, it consists of the
`f` whose reduced denominator does not vanish at `t`. -/
def regularSubring (t : K) : Subring (RatFunc K) :=
  (Place.adicOfIrreducible (irreducible_X_sub_C t)).integers.toSubring

/-- `Rₜ` is the valuation ring of the place `T = t` of `K(T)`. -/
theorem mem_regularSubring_iff_mem_integers {t : K} {f : RatFunc K} :
    f ∈ regularSubring t ↔ f ∈ (Place.adicOfIrreducible (irreducible_X_sub_C t)).integers :=
  Iff.rfl

/-- **Membership by reduced denominator.** A rational function is regular at `t` exactly when its
reduced denominator does not vanish at `t`. The test uses Mathlib's reduced denominator, so common
factors cancel first: `(T² - 1) / (T - 1) = T + 1` is regular at `1`. -/
@[simp]
theorem mem_regularSubring_iff {t : K} {f : RatFunc K} :
    f ∈ regularSubring t ↔ f.denom.eval t ≠ 0 := by
  rw [mem_regularSubring_iff_mem_integers, Place.mem_integers_iff,
    Place.valuation_adicOfIrreducible, Place.valuation_ofIrreducible_le_one_iff, dvd_iff_isRoot,
    IsRoot.def]

/-- Polynomials are regular at every point. -/
theorem algebraMap_mem_regularSubring (t : K) (q : K[X]) :
    algebraMap K[X] (RatFunc K) q ∈ regularSubring t := by
  simp [RatFunc.denom_algebraMap]

/-- A subring of `K(T)` consists of functions regular at `t` exactly when the reduced denominator
of each of its elements does not vanish at `t`. -/
theorem le_regularSubring_iff {t : K} {A : Subring (RatFunc K)} :
    A ≤ regularSubring t ↔ ∀ f ∈ A, f.denom.eval t ≠ 0 := by
  simp [IsConcreteLE.le_iff]

/-- A polynomial over `K(T)` has coefficients in `Rₜ` exactly when the reduced denominator of each
of its coefficients does not vanish at `t`. -/
theorem mem_lifts_subtype_regularSubring_iff {t : K} {p : (RatFunc K)[X]} :
    p ∈ lifts (regularSubring t).subtype ↔ ∀ n, (p.coeff n).denom.eval t ≠ 0 := by
  simp [lifts_iff_coeff_lifts]

/-! ### Evaluation on the regular subring -/

/-- Evaluation at `t` as a ring map on the functions regular at `t`. It is the restriction of
Mathlib's total evaluation `RatFunc.eval (RingHom.id K) t`, which is not a ring map on all of
`K(T)`. -/
def regularEval (t : K) : regularSubring t →+* K where
  toFun f := RatFunc.eval (RingHom.id K) t f
  map_one' := RatFunc.eval_one _ _
  map_mul' f g :=
    RatFunc.eval_mul _ _ (mem_regularSubring_iff.mp f.property)
      (mem_regularSubring_iff.mp g.property)
  map_zero' := RatFunc.eval_zero _ _
  map_add' f g :=
    RatFunc.eval_add _ _ (mem_regularSubring_iff.mp f.property)
      (mem_regularSubring_iff.mp g.property)

@[simp]
theorem regularEval_apply (t : K) (f : regularSubring t) :
    regularEval t f = RatFunc.eval (RingHom.id K) t f :=
  (rfl)

/-- On a polynomial, evaluation on the regular subring is polynomial evaluation. -/
theorem regularEval_algebraMap (t : K) (q : K[X]) :
    regularEval t ⟨algebraMap K[X] (RatFunc K) q, algebraMap_mem_regularSubring t q⟩ =
      q.eval t := by
  simp

/-- Evaluation at `t` takes every value: the constant `a` has value `a`. -/
theorem regularEval_surjective (t : K) : Function.Surjective (regularEval t) := fun a ↦
  ⟨⟨algebraMap K[X] (RatFunc K) (C a), algebraMap_mem_regularSubring t _⟩, by simp⟩

/-- **Evaluation is the residue map.** Under the identification of `K` with the residue field of
the place `T = t` of `K(T)`, the value at `t` of a function regular at `t` is its residue. -/
theorem algebraMap_regularEval (t : K) (f : regularSubring t) :
    algebraMap K (Place.adicOfIrreducible (irreducible_X_sub_C t)).ResidueField (regularEval t f) =
      IsLocalRing.residue (Place.adicOfIrreducible (irreducible_X_sub_C t)).integers
        ⟨f, mem_regularSubring_iff_mem_integers.mp f.property⟩ := by
  -- In the valuation ring, `f · denom(f) = num(f)`; take residues of both sides.
  have hmul : (⟨f, mem_regularSubring_iff_mem_integers.mp f.property⟩ :
        (Place.adicOfIrreducible (irreducible_X_sub_C t)).integers) *
      ⟨algebraMap K[X] (RatFunc K) (f : RatFunc K).denom,
        mem_regularSubring_iff_mem_integers.mp (algebraMap_mem_regularSubring t _)⟩ =
      ⟨algebraMap K[X] (RatFunc K) (f : RatFunc K).num,
        mem_regularSubring_iff_mem_integers.mp (algebraMap_mem_regularSubring t _)⟩ :=
    Subtype.ext <| (eq_div_iff (by simpa using RatFunc.denom_ne_zero (f : RatFunc K))).mp
      (RatFunc.num_div_denom (f : RatFunc K)).symm
  have hres :=
    congrArg (IsLocalRing.residue (Place.adicOfIrreducible (irreducible_X_sub_C t)).integers) hmul
  rw [map_mul, Place.residue_algebraMap_adicOfIrreducible_X_sub_C,
    Place.residue_algebraMap_adicOfIrreducible_X_sub_C] at hres
  rw [regularEval_apply, RatFunc.eval_id_eq_div, map_div₀, ← hres,
    mul_div_cancel_right₀ _ ((_root_.map_ne_zero _).mpr (mem_regularSubring_iff.mp f.property))]

/-! ### Specialization of polynomials -/

/-- The **specialization** `p(T, Y) ↦ p(t, Y)` of a polynomial `p ∈ K(T)[Y]` at `t ∈ K`: each
coefficient is evaluated at `t` by Mathlib's total evaluation `RatFunc.eval`. It is defined even
when a coefficient has a pole at `t`, where that coefficient is sent to `0`; it is additive and
multiplicative only on polynomials whose coefficients are regular at `t` (`specialize_add`,
`specialize_mul`). -/
def specialize (t : K) (p : (RatFunc K)[X]) : K[X] :=
  p.sum fun n c ↦ monomial n (RatFunc.eval (RingHom.id K) t c)

/-- **Coefficients after specialization.** The coefficient of `Yⁿ` in `p(t, Y)` is the value at
`t` of the coefficient of `Yⁿ` in `p`, also when that coefficient has a pole at `t`. -/
@[simp]
theorem coeff_specialize (t : K) (p : (RatFunc K)[X]) (n : ℕ) :
    (specialize t p).coeff n = RatFunc.eval (RingHom.id K) t (p.coeff n) := by
  rw [specialize, coeff_sum, Polynomial.sum_def]
  simp_rw [coeff_monomial_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, RatFunc.eval_zero]

@[simp]
theorem specialize_monomial (t : K) (n : ℕ) (f : RatFunc K) :
    specialize t (monomial n f) = monomial n (RatFunc.eval (RingHom.id K) t f) := by
  ext m
  rw [coeff_specialize, coeff_monomial_apply, coeff_monomial_apply]
  split_ifs <;> simp

@[simp]
theorem specialize_C (t : K) (f : RatFunc K) :
    specialize t (C f) = C (RatFunc.eval (RingHom.id K) t f) := by
  simpa using specialize_monomial t 0 f

@[simp]
theorem specialize_zero (t : K) : specialize t (0 : (RatFunc K)[X]) = 0 := by
  simpa using specialize_C t 0

@[simp]
theorem specialize_one (t : K) : specialize t (1 : (RatFunc K)[X]) = 1 := by
  simpa using specialize_C t 1

/-- The outer variable `Y` is not specialized. -/
@[simp]
theorem specialize_X (t : K) : specialize t (X : (RatFunc K)[X]) = X := by
  rw [← monomial_one_one_eq_X, specialize_monomial, RatFunc.eval_one, monomial_one_one_eq_X]

/-- Specializing a polynomial with polynomial coefficients evaluates each coefficient at `t`. -/
@[simp]
theorem specialize_map_algebraMap (t : K) (p : K[X][X]) :
    specialize t (p.map (algebraMap K[X] (RatFunc K))) = p.map (evalRingHom t) := by
  ext n
  simp

/-- **Compatibility with polynomial coefficient maps.** On polynomials with coefficients regular
at `t`, specialization is the coefficient map along the ring map `regularEval t`. -/
@[simp]
theorem specialize_map_subtype (t : K) (q : (regularSubring t)[X]) :
    specialize t (q.map (regularSubring t).subtype) = q.map (regularEval t) := by
  ext n
  simp

/-- **Specialization preserves addition** of polynomials whose coefficients are regular at `t`.
The hypotheses cannot be dropped: at `t = 0`, `C T⁻¹ + C (1 - T⁻¹) = 1` specializes to `1`, while
both summands specialize to `0`. -/
theorem specialize_add {t : K} {p q : (RatFunc K)[X]}
    (hp : ∀ n, (p.coeff n).denom.eval t ≠ 0) (hq : ∀ n, (q.coeff n).denom.eval t ≠ 0) :
    specialize t (p + q) = specialize t p + specialize t q := by
  obtain ⟨p, rfl⟩ := (mem_lifts _).mp (mem_lifts_subtype_regularSubring_iff.mpr hp)
  obtain ⟨q, rfl⟩ := (mem_lifts _).mp (mem_lifts_subtype_regularSubring_iff.mpr hq)
  simp only [← Polynomial.map_add, specialize_map_subtype]

/-- **Specialization preserves multiplication** of polynomials whose coefficients are regular at
`t`. The hypotheses cannot be dropped: at `t = 0`, `C T * C T⁻¹ = 1` specializes to `1`, while
`C T` and `C T⁻¹` both specialize to `0`. -/
theorem specialize_mul {t : K} {p q : (RatFunc K)[X]}
    (hp : ∀ n, (p.coeff n).denom.eval t ≠ 0) (hq : ∀ n, (q.coeff n).denom.eval t ≠ 0) :
    specialize t (p * q) = specialize t p * specialize t q := by
  obtain ⟨p, rfl⟩ := (mem_lifts _).mp (mem_lifts_subtype_regularSubring_iff.mpr hp)
  obtain ⟨q, rfl⟩ := (mem_lifts _).mp (mem_lifts_subtype_regularSubring_iff.mpr hq)
  simp only [← Polynomial.map_mul, specialize_map_subtype]

/-! ### Denominators and the specialization guard -/

/-- The **denominator product** `D(p)` of `p ∈ K(T)[Y]`: the product of the reduced denominators of
its nonzero coefficients. It is a product with repetitions, not a least common denominator:
`D(T⁻¹ Y + T⁻¹) = T²`. -/
def denomProduct (p : (RatFunc K)[X]) : K[X] :=
  ∏ n ∈ p.support, (p.coeff n).denom

theorem denomProduct_def (p : (RatFunc K)[X]) :
    denomProduct p = ∏ n ∈ p.support, (p.coeff n).denom :=
  (rfl)

@[simp]
theorem denomProduct_zero : denomProduct (0 : (RatFunc K)[X]) = 1 := by
  simp [denomProduct_def]

@[simp]
theorem denomProduct_C (f : RatFunc K) : denomProduct (C f) = f.denom := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp [RatFunc.denom_zero]
  · simp [denomProduct_def, support_C hf]

/-- A polynomial with polynomial coefficients has denominator product `1`. -/
@[simp]
theorem denomProduct_map_algebraMap (p : K[X][X]) :
    denomProduct (p.map (algebraMap K[X] (RatFunc K))) = 1 :=
  Finset.prod_eq_one fun _ _ ↦ by simp [RatFunc.denom_algebraMap]

theorem monic_denomProduct (p : (RatFunc K)[X]) : (denomProduct p).Monic :=
  monic_prod_of_monic _ _ fun _ _ ↦ RatFunc.monic_denom _

/-- The denominator product is a nonzero polynomial, although it may vanish at some `t`. -/
theorem denomProduct_ne_zero (p : (RatFunc K)[X]) : denomProduct p ≠ 0 :=
  (monic_denomProduct p).ne_zero

/-- **The exact coefficient-regularity locus.** The denominator product of `p` does not vanish at
`t` exactly when every coefficient of `p` is regular at `t`. -/
theorem eval_denomProduct_ne_zero_iff {t : K} {p : (RatFunc K)[X]} :
    (denomProduct p).eval t ≠ 0 ↔ ∀ n, (p.coeff n).denom.eval t ≠ 0 := by
  rw [denomProduct_def, eval_prod, Finset.prod_ne_zero_iff]
  refine ⟨fun h n ↦ ?_, fun h n _ ↦ h n⟩
  by_cases hn : n ∈ p.support
  · exact h n hn
  · rw [notMem_support_iff.mp hn, RatFunc.denom_zero, eval_one]
    exact one_ne_zero

/-- **Degree preservation by the leading coefficient.** If the leading coefficient of `p` has a
nonzero value at `t`, specialization at `t` preserves the degree. No hypothesis on the other
coefficients is needed. -/
theorem natDegree_specialize_of_eval_leadingCoeff_ne_zero {t : K} {p : (RatFunc K)[X]}
    (h : RatFunc.eval (RingHom.id K) t p.leadingCoeff ≠ 0) :
    (specialize t p).natDegree = p.natDegree := by
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rwa [coeff_specialize])
  rw [natDegree_le_iff_coeff_eq_zero]
  intro n hn
  rw [coeff_specialize, coeff_eq_zero_of_natDegree_lt hn, RatFunc.eval_zero]

/-- The **specialization guard** `D(p) · num(lc(p))` of `p ∈ K(T)[Y]`. Away from its roots every
coefficient of `p` is regular and specialization preserves the degree
(`eval_denom_coeff_ne_zero_of_eval_specializationGuard_ne_zero`,
`natDegree_specialize_of_eval_specializationGuard_ne_zero`). -/
def specializationGuard (p : (RatFunc K)[X]) : K[X] :=
  denomProduct p * p.leadingCoeff.num

theorem specializationGuard_def (p : (RatFunc K)[X]) :
    specializationGuard p = denomProduct p * p.leadingCoeff.num :=
  (rfl)

@[simp]
theorem specializationGuard_eq_zero_iff {p : (RatFunc K)[X]} :
    specializationGuard p = 0 ↔ p = 0 := by
  simp [specializationGuard_def, denomProduct_ne_zero, RatFunc.num_eq_zero_iff]

theorem specializationGuard_ne_zero {p : (RatFunc K)[X]} (hp : p ≠ 0) :
    specializationGuard p ≠ 0 :=
  specializationGuard_eq_zero_iff.not.mpr hp

/-- Away from the roots of the guard, every coefficient is regular. -/
theorem eval_denom_coeff_ne_zero_of_eval_specializationGuard_ne_zero {t : K}
    {p : (RatFunc K)[X]} (h : (specializationGuard p).eval t ≠ 0) (n : ℕ) :
    (p.coeff n).denom.eval t ≠ 0 := by
  rw [specializationGuard_def, eval_mul] at h
  exact eval_denomProduct_ne_zero_iff.mp (left_ne_zero_of_mul h) n

/-- **The specialization guard.** Away from the roots of the guard, specialization preserves the
degree. -/
theorem natDegree_specialize_of_eval_specializationGuard_ne_zero {t : K}
    {p : (RatFunc K)[X]} (h : (specializationGuard p).eval t ≠ 0) :
    (specialize t p).natDegree = p.natDegree := by
  apply natDegree_specialize_of_eval_leadingCoeff_ne_zero
  have hden := eval_denom_coeff_ne_zero_of_eval_specializationGuard_ne_zero h p.natDegree
  rw [specializationGuard_def, eval_mul] at h
  rw [RatFunc.eval_id_eq_div]
  exact div_ne_zero (right_ne_zero_of_mul h) hden

/-- **Finiteness of bad specialization parameters.** For every `p ∈ K(T)[Y]`, the parameters
`t` at which some coefficient of `p` has a pole, or specialization changes the degree, form a
finite set: for `p ≠ 0` they are roots of the guard, and for `p = 0` there are none. This holds over
every field and does not assert that a good parameter exists. -/
theorem finite_setOf_exists_eval_denom_coeff_eq_zero_or_natDegree_ne (p : (RatFunc K)[X]) :
    {t : K | (∃ n, (p.coeff n).denom.eval t = 0) ∨
      (specialize t p).natDegree ≠ p.natDegree}.Finite := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [RatFunc.denom_zero]
  refine (finite_setOfPred_isRoot (specializationGuard_ne_zero hp)).subset fun t ht ↦ ?_
  by_contra h
  rcases ht with ⟨n, hn⟩ | ht
  · exact eval_denom_coeff_ne_zero_of_eval_specializationGuard_ne_zero h n hn
  · exact ht (natDegree_specialize_of_eval_specializationGuard_ne_zero h)

/-- **Simultaneous avoidance for a finite family.** Over an infinite field, for a finite family of
polynomials in `K(T)[Y]` and a finite set `A ⊆ K`, some parameter `t ∉ A` makes every
coefficient of every member regular at `t` and preserves every degree. Nothing is claimed about
irreducibility of the specializations. -/
theorem exists_notMem_forall_eval_denom_coeff_ne_zero_and_natDegree_eq [Infinite K]
    (s : Finset (RatFunc K)[X]) {A : Set K} (hA : A.Finite) :
    ∃ t ∉ A, ∀ p ∈ s, (∀ n, (p.coeff n).denom.eval t ≠ 0) ∧
      (specialize t p).natDegree = p.natDegree := by
  obtain ⟨t, ht⟩ := (hA.union (s.finite_toSet.biUnion fun p _ ↦
    finite_setOf_exists_eval_denom_coeff_eq_zero_or_natDegree_ne p)).exists_notMem
  simp only [Set.mem_union, Set.mem_iUnion, Set.mem_ofPred_eq, Finset.mem_coe, not_or,
    not_exists] at ht
  refine ⟨t, ht.1, fun p hp ↦ ⟨fun n ↦ (ht.2 p hp).1 n, ?_⟩⟩
  simpa using (ht.2 p hp).2

end TauCeti.RationalSpecialization
