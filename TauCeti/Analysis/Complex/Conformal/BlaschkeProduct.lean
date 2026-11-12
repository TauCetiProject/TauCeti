/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import TauCeti.Analysis.Complex.Conformal.Moebius

/-!
# Boundary-compatible Blaschke factors and finite Blaschke products

For a parameter `a` in the closed unit disc, the **Blaschke factor** is
`b_a(z) = (z - a) / (1 - conj a * z)` when `‖a‖ < 1` and the constant `-a` when `‖a‖ = 1`.
The boundary formula is the removable extension of the same rational expression: for
`‖a‖ = 1` and `z ≠ a` one has `(z - a) / (1 - conj a * z) = -a`, whereas Lean's totalized
division would assign the value `0` at `z = a`.  Every such factor is analytic on a
neighbourhood of the closed unit disc and has modulus one on the unit circle; an interior factor
maps the open disc into itself and vanishes in the closed unit disc exactly at `a`, while a
boundary factor is a unimodular constant.

A **finite Blaschke product** is `B(z) = ∏ i, b_(a i)(z) ^ n i` for a finite family of
parameters `a i` in the closed unit disc with multiplicities `n i`.  It is analytic near the
closed unit disc, has modulus one on the unit circle, maps the open disc into the closed disc, and
maps it into the open disc exactly when some interior parameter has positive multiplicity.

These products are the boundary-compatible zero-removal factors used in Nevanlinna's quotient
representation of a function holomorphic near the closed disc: on the open disc, the interior
factor is the existing disc automorphism `TauCeti.unitDiscMoebius` and the reciprocal of
Mathlib's canonical factor `Complex.canonicalFactor 1 a`.

## Main definitions

* `TauCeti.blaschkeFactor a`: the boundary-compatible Blaschke factor with parameter `a`.
* `TauCeti.blaschkeProduct a n`: the finite Blaschke product with parameters `a` and
  multiplicities `n`.

## Main results

* `TauCeti.blaschkeFactor_eq_div`: for `‖a‖ ≤ 1`, the factor agrees with the rational
  expression wherever its denominator is nonzero.
* `TauCeti.coe_unitDiscMoebius_eq_blaschkeFactor` and
  `TauCeti.blaschkeFactor_eq_inv_canonicalFactor`: comparison with the native disc automorphism
  and with Mathlib's canonical factor.
* `TauCeti.norm_blaschkeProduct_eq_one`: finite Blaschke products are unimodular on the unit
  circle.
* `TauCeti.norm_blaschkeProduct_lt_one_iff`: on the open disc, a finite Blaschke product has
  modulus less than one exactly when some interior parameter has positive multiplicity.
* `TauCeti.blaschkeProduct_eq_zero_iff`: the zeros of a finite Blaschke product in the closed
  disc are its interior parameters of positive multiplicity.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), proof of Lemma 2.3.1.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

/-! ### Blaschke factors -/

/-- The boundary-compatible Blaschke factor with parameter `a`: it is
`z ↦ (z - a) / (1 - conj a * z)` when `‖a‖ < 1` and the constant `-a` otherwise.  For `‖a‖ = 1`
this constant is the removable extension of the same rational expression
(see `TauCeti.blaschkeFactor_eq_div`).  Parameters of norm greater than one are not intended. -/
noncomputable def blaschkeFactor (a z : ℂ) : ℂ :=
  if ‖a‖ < 1 then (z - a) / (1 - conj a * z) else -a

variable {a z : ℂ}

/-- An interior Blaschke factor is given by the rational expression. -/
lemma blaschkeFactor_of_norm_lt_one (ha : ‖a‖ < 1) (z : ℂ) :
    blaschkeFactor a z = (z - a) / (1 - conj a * z) :=
  ite_eq_left ha

/-- A Blaschke factor whose parameter has norm at least one is the constant `-a`. -/
lemma blaschkeFactor_of_one_le_norm (ha : 1 ≤ ‖a‖) (z : ℂ) : blaschkeFactor a z = -a :=
  ite_eq_right ha.not_gt

/-- A boundary Blaschke factor is the constant `-a`. -/
lemma blaschkeFactor_of_norm_eq_one (ha : ‖a‖ = 1) (z : ℂ) : blaschkeFactor a z = -a :=
  blaschkeFactor_of_one_le_norm ha.ge z

/-- The Blaschke factor with parameter zero is the identity. -/
@[simp]
lemma blaschkeFactor_zero (z : ℂ) : blaschkeFactor 0 z = z := by
  simp [blaschkeFactor_of_norm_lt_one (a := 0) (by simp)]

/-- For a parameter in the closed unit disc, the Blaschke factor agrees with the rational
expression `(z - a) / (1 - conj a * z)` wherever its denominator is nonzero.  For `‖a‖ = 1`
this says that the constant `-a` is the removable extension of that expression. -/
lemma blaschkeFactor_eq_div (ha : ‖a‖ ≤ 1) (hz : 1 - conj a * z ≠ 0) :
    blaschkeFactor a z = (z - a) / (1 - conj a * z) := by
  rcases ha.lt_or_eq with ha | ha
  · exact blaschkeFactor_of_norm_lt_one ha z
  · have h : a * conj a = 1 := by simp [Complex.mul_conj', ha]
    rw [blaschkeFactor_of_norm_eq_one ha, eq_div_iff hz]
    linear_combination z * h

/-- On the open unit disc, the Blaschke factor with an interior parameter is the native disc
automorphism `TauCeti.unitDiscMoebius`. -/
lemma coe_unitDiscMoebius_eq_blaschkeFactor (a z : Complex.UnitDisc) :
    (unitDiscMoebius a z : ℂ) = blaschkeFactor a z := by
  rw [coe_unitDiscMoebius, blaschkeFactor_of_norm_lt_one a.norm_lt_one]

/-- For an interior parameter, the Blaschke factor is the reciprocal of Mathlib's canonical
factor `Complex.canonicalFactor 1 a`. -/
lemma blaschkeFactor_eq_inv_canonicalFactor (ha : ‖a‖ < 1) :
    blaschkeFactor a = (canonicalFactor 1 a)⁻¹ := by
  ext z
  simp [blaschkeFactor_of_norm_lt_one ha, canonicalFactor_apply]

/-- A boundary Blaschke factor has modulus one everywhere. -/
lemma norm_blaschkeFactor_of_norm_eq_one (ha : ‖a‖ = 1) (z : ℂ) : ‖blaschkeFactor a z‖ = 1 := by
  rw [blaschkeFactor_of_norm_eq_one ha, norm_neg, ha]

/-- A Blaschke factor with parameter in the closed unit disc has modulus one on the unit
circle. -/
lemma norm_blaschkeFactor_eq_one (ha : ‖a‖ ≤ 1) (hz : ‖z‖ = 1) : ‖blaschkeFactor a z‖ = 1 := by
  rcases ha.lt_or_eq with ha | ha
  · rw [blaschkeFactor_eq_inv_canonicalFactor ha, Pi.inv_apply, norm_inv,
      norm_canonicalFactor_eval_circle_eq_one (by simpa using ha) (by simpa using hz), inv_one]
  · exact norm_blaschkeFactor_of_norm_eq_one ha z

/-- A Blaschke factor with an interior parameter maps the open unit disc into itself. -/
lemma norm_blaschkeFactor_lt_one (ha : ‖a‖ < 1) (hz : ‖z‖ < 1) : ‖blaschkeFactor a z‖ < 1 := by
  rw [blaschkeFactor_of_norm_lt_one ha, ← mem_ball_zero_iff]
  exact mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha (mem_ball_zero_iff.2 hz)

/-- A Blaschke factor with parameter in the closed unit disc maps the closed unit disc into
itself. -/
lemma norm_blaschkeFactor_le_one (ha : ‖a‖ ≤ 1) (hz : ‖z‖ ≤ 1) : ‖blaschkeFactor a z‖ ≤ 1 := by
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hz.lt_or_eq with hz | hz
    · exact (norm_blaschkeFactor_lt_one ha' hz).le
    · exact (norm_blaschkeFactor_eq_one ha hz).le
  · exact (norm_blaschkeFactor_of_norm_eq_one ha' z).le

/-- In the closed unit disc, a Blaschke factor vanishes exactly at an interior parameter. -/
lemma blaschkeFactor_eq_zero_iff (hz : ‖z‖ ≤ 1) : blaschkeFactor a z = 0 ↔ ‖a‖ < 1 ∧ z = a := by
  by_cases ha : ‖a‖ < 1
  · rw [blaschkeFactor_of_norm_lt_one ha,
      div_eq_zero_iff, or_iff_left (one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one hz ha),
      sub_eq_zero, and_iff_right ha]
  · have ha0 : a ≠ 0 := by rintro rfl; simp at ha
    simp [blaschkeFactor_of_one_le_norm (not_lt.1 ha), ha, ha0]

/-- A Blaschke factor is analytic on a neighbourhood of the closed unit disc. -/
lemma analyticOnNhd_blaschkeFactor (a : ℂ) :
    AnalyticOnNhd ℂ (blaschkeFactor a) (closedBall 0 1) := by
  intro z hz
  by_cases ha : ‖a‖ < 1
  · have hden := one_sub_conj_mul_ne_zero_of_norm_le_one_of_norm_lt_one
      (mem_closedBall_zero_iff.1 hz) ha
    rw [show blaschkeFactor a = fun z => (z - a) / (1 - conj a * z) from
      funext (blaschkeFactor_of_norm_lt_one ha)]
    fun_prop (disch := exact hden)
  · rw [show blaschkeFactor a = fun _ => -a from
      funext (blaschkeFactor_of_one_le_norm (not_lt.1 ha))]
    exact analyticAt_const

/-! ### Finite Blaschke products -/

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The finite Blaschke product `z ↦ ∏ i, blaschkeFactor (a i) z ^ n i` with parameters `a i` and
multiplicities `n i`. -/
noncomputable def blaschkeProduct (a : ι → ℂ) (n : ι → ℕ) (z : ℂ) : ℂ :=
  ∏ i, blaschkeFactor (a i) z ^ n i

/-- The defining formula of a finite Blaschke product. -/
lemma blaschkeProduct_apply (a : ι → ℂ) (n : ι → ℕ) (z : ℂ) :
    blaschkeProduct a n z = ∏ i, blaschkeFactor (a i) z ^ n i :=
  (rfl)

/-- The finite Blaschke product of an empty family is `1`. -/
@[simp]
lemma blaschkeProduct_of_isEmpty [IsEmpty ι] (a : ι → ℂ) (n : ι → ℕ) :
    blaschkeProduct a n = 1 := by
  ext z
  simp [blaschkeProduct_apply]

/-- The finite Blaschke product of a disjoint union of two families is the product of their
finite Blaschke products. -/
lemma blaschkeProduct_sumElim (a : ι → ℂ) (n : ι → ℕ) (b : κ → ℂ) (m : κ → ℕ) :
    blaschkeProduct (Sum.elim a b) (Sum.elim n m) = blaschkeProduct a n * blaschkeProduct b m := by
  ext z
  simp [blaschkeProduct_apply, Fintype.prod_sum_type]

/-- The finite Blaschke product of two concatenated `Fin`-indexed families is the product of their
finite Blaschke products. -/
lemma blaschkeProduct_finAppend {k l : ℕ} (a : Fin k → ℂ) (n : Fin k → ℕ) (b : Fin l → ℂ)
    (m : Fin l → ℕ) :
    blaschkeProduct (Fin.append a b) (Fin.append n m) =
      blaschkeProduct a n * blaschkeProduct b m := by
  ext z
  simp [blaschkeProduct_apply, Fin.prod_univ_add]

/-- A finite Blaschke product is analytic on a neighbourhood of the closed unit disc. -/
lemma analyticOnNhd_blaschkeProduct (a : ι → ℂ) (n : ι → ℕ) :
    AnalyticOnNhd ℂ (blaschkeProduct a n) (closedBall 0 1) := by
  rw [funext (blaschkeProduct_apply a n)]
  exact Finset.analyticOnNhd_fun_prod _ fun i _ => (analyticOnNhd_blaschkeFactor (a i)).pow (n i)

variable {a : ι → ℂ} {n : ι → ℕ}

/-- A finite Blaschke product with parameters in the closed unit disc has modulus one on the unit
circle. -/
lemma norm_blaschkeProduct_eq_one (ha : ∀ i, ‖a i‖ ≤ 1) (hz : ‖z‖ = 1) :
    ‖blaschkeProduct a n z‖ = 1 := by
  simp [blaschkeProduct_apply, norm_blaschkeFactor_eq_one (ha _) hz]

/-- A finite Blaschke product whose parameters all lie on the unit circle has modulus one
everywhere. -/
lemma norm_blaschkeProduct_of_forall_norm_eq_one (ha : ∀ i, ‖a i‖ = 1) (z : ℂ) :
    ‖blaschkeProduct a n z‖ = 1 := by
  simp [blaschkeProduct_apply, norm_blaschkeFactor_of_norm_eq_one (ha _)]

/-- A finite Blaschke product with parameters in the closed unit disc maps the closed unit disc
into itself. -/
lemma norm_blaschkeProduct_le_one (ha : ∀ i, ‖a i‖ ≤ 1) (hz : ‖z‖ ≤ 1) :
    ‖blaschkeProduct a n z‖ ≤ 1 := by
  rw [blaschkeProduct_apply, norm_prod]
  exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun i _ => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_blaschkeFactor_le_one (ha i) hz)

/-- On the open unit disc, a finite Blaschke product with parameters in the closed unit disc has
modulus less than one exactly when some interior parameter has positive multiplicity; otherwise
it has modulus one there. -/
lemma norm_blaschkeProduct_lt_one_iff (ha : ∀ i, ‖a i‖ ≤ 1) (hz : ‖z‖ < 1) :
    ‖blaschkeProduct a n z‖ < 1 ↔ ∃ i, ‖a i‖ < 1 ∧ n i ≠ 0 := by
  constructor
  · intro h
    by_contra! hne
    refine h.ne ?_
    rw [blaschkeProduct_apply, norm_prod]
    refine Finset.prod_eq_one fun i _ => ?_
    rcases (ha i).lt_or_eq with hai | hai
    · simp [hne i hai]
    · rw [norm_pow, norm_blaschkeFactor_of_norm_eq_one hai, one_pow]
  · rintro ⟨i, hai, hni⟩
    classical
    rw [blaschkeProduct_apply, norm_prod, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
    refine (mul_le_of_le_one_right (norm_nonneg _) ?_).trans_lt ?_
    · exact Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) fun j _ => by
        rw [norm_pow]
        exact pow_le_one₀ (norm_nonneg _) (norm_blaschkeFactor_le_one (ha j) hz.le)
    · rw [norm_pow]
      exact pow_lt_one₀ (norm_nonneg _) (norm_blaschkeFactor_lt_one hai hz) hni

/-- In the closed unit disc, a finite Blaschke product vanishes exactly at its interior parameters
of positive multiplicity. -/
lemma blaschkeProduct_eq_zero_iff (hz : ‖z‖ ≤ 1) :
    blaschkeProduct a n z = 0 ↔ ∃ i, n i ≠ 0 ∧ ‖a i‖ < 1 ∧ z = a i := by
  simp [blaschkeProduct_apply, Finset.prod_eq_zero_iff, pow_eq_zero_iff',
    blaschkeFactor_eq_zero_iff hz, and_comm]

end TauCeti
