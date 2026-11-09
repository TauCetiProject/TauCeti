/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.PowerSeries
public import TauCeti.Probability.FreeProbability.Cumulant.Free
public import TauCeti.RingTheory.PowerSeries.SubstInv
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The moment series and the free cumulant series of one variable

Let `φ : A → R` be a function on a monoid (in free probability, a linear functional on an
algebra) and let `a ∈ A`. The *moment series* and the *free cumulant series* of `a` are the formal
power series

`M(z) = ∑_{n ≥ 0} φ (a ^ n) z ^ n` and `C(z) = 1 + ∑_{n ≥ 1} κ_n(a, …, a) z ^ n = 1 + z R(z)`,

where `R(z) = ∑_{n ≥ 0} κ_{n+1}(a, …, a) z ^ n` is the formal *R-series* of `a`, the formal
counterpart of Voiculescu's R-transform. For a normalised `φ`, `φ 1 = 1`, they satisfy the
functional equations

`M(z) = C(z M(z))` and `M(z) = 1 + z M(z) R(z M(z))`,

proved coefficientwise from the moment–cumulant formula, by the recurrence of noncrossing
partitions by the part containing the first position. Conversely `C` is the only power series
with `C(z M(z)) = M(z)`, and it is computed from `M` as `C = M ∘ (z M)⁻¹`, using Mathlib's
compositional inverse `PowerSeries.substInvOfIsUnit` of `z M(z)`, whose linear coefficient is
`φ 1 = 1`. These are formal identities: nothing is said about convergence or about the analytic
R-transform of a measure.

The R-series behaves additively: it is additive on elements of freely independent subalgebras,
adding a scalar `c` to `a` adds the constant `c` to it, and rescaling `a` by `c` rescales `M` and
`C` by `c`, so that `R_{c a}(z) = c R_a(c z)`. For normalised functionals, the free cumulant series
and the moment series determine each other.

## Main definitions

* `TauCeti.momentSeries φ a` — the moment series `M(z) = ∑_{n ≥ 0} φ (a ^ n) z ^ n`.
* `TauCeti.freeCumulantSeries φ a` — the free cumulant series `C(z) = 1 + ∑_{n ≥ 1} κ_n z ^ n`.
* `TauCeti.rSeries φ a` — the R-series `R(z) = ∑_{n ≥ 0} κ_{n+1} z ^ n`, with
  `TauCeti.freeCumulantSeries_eq_one_add_X_mul_rSeries` stating `C(z) = 1 + z R(z)`.

## Main results

* `TauCeti.apply_pow_eq_sum_prod_coeff_freeCumulantSeries` — the moment–cumulant formula for a
  single variable, `φ (a ^ n) = ∑_{π ∈ NC(n)} ∏_{B ∈ π} κ_{|B|}(a, …, a)`.
* `TauCeti.freeCumulantSeries_subst_X_mul_momentSeries` — the functional equation
  `C(z M(z)) = M(z)`, and `TauCeti.momentSeries_eq_one_add_X_mul_momentSeries_mul_rSeries_subst`
  — its R-series form `M(z) = 1 + z M(z) R(z M(z))`.
* `TauCeti.eq_freeCumulantSeries_of_subst_eq` and
  `TauCeti.freeCumulantSeries_eq_subst_substInvOfIsUnit` — the free cumulant series is the only
  solution of `C(z M(z)) = M(z)`, namely `C = M ∘ (z M)⁻¹`.
* `TauCeti.freeCumulantSeries_congr` — equal moment series give equal free cumulant series, and
  `TauCeti.freeCumulantSeries_eq_iff_momentSeries_eq` — conversely for normalised functionals.
* `TauCeti.IsFreelyIndependent.rSeries_sum` and `TauCeti.IsFreelyIndependent.rSeries_add` — the
  R-series is additive on elements of freely independent subalgebras, with the element versions
  `TauCeti.IsFreelyIndependentElements.rSeries_sum` and
  `TauCeti.IsFreelyIndependentElements.rSeries_add`.
* `TauCeti.rSeries_add_algebraMap`, `TauCeti.momentSeries_smul`,
  `TauCeti.freeCumulantSeries_smul` and `TauCeti.rSeries_smul` — shifts and dilations.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 16 (the
  functional relation between the moment series and the cumulant series of one variable) and
  Lecture 12 (the R-transform and its additivity on free variables, Theorem 12.7).
* D. Voiculescu, *Addition of certain noncommuting random variables*, J. Funct. Anal. 66 (1986),
  323–346.
-/

public section

open Finset PowerSeries

namespace TauCeti

variable {R A : Type*}

section MomentSeries

variable [Semiring R] [Monoid A] (φ : A → R) (a : A)

/-- The *moment series* `M(z) = ∑_{n ≥ 0} φ (a ^ n) z ^ n` of `a` with respect to `φ`. Its
constant coefficient is `φ 1`, which is `1` for a normalised `φ`. -/
def momentSeries : R⟦X⟧ :=
  PowerSeries.mk fun n => φ (a ^ n)

/-- The coefficients of the moment series are the moments. -/
@[simp]
theorem coeff_momentSeries (n : ℕ) : coeff n (momentSeries φ a) = φ (a ^ n) := by
  rw [momentSeries, coeff_mk]

/-- The constant coefficient of the moment series is `φ 1`. -/
@[simp]
theorem constantCoeff_momentSeries : constantCoeff (momentSeries φ a) = φ 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_momentSeries, pow_zero]

end MomentSeries

/-- Rescaling `a` by `c` rescales its moment series: `M_{c a}(z) = M_a(c z)`. -/
theorem momentSeries_smul [CommSemiring R] [Semiring A] [Algebra R A] (φ : A →ₗ[R] R) (c : R)
    (a : A) : momentSeries φ (c • a) = rescale c (momentSeries φ a) := by
  ext n
  rw [coeff_momentSeries, coeff_rescale, coeff_momentSeries, smul_pow, map_smul, smul_eq_mul]

variable [CommRing R]

section Monoid

variable [Monoid A] (φ : A → R) (a : A)

/-- The *free cumulant series* `C(z) = 1 + ∑_{n ≥ 1} κ_n(a, …, a) z ^ n` of `a` with respect to
`φ`, whose `n`-th coefficient is the free cumulant of the constant word of length `n`. -/
def freeCumulantSeries : R⟦X⟧ :=
  PowerSeries.mk fun n => freeCumulant φ (fun _ : Fin n => a) univ

/-- The `n`-th coefficient of the free cumulant series is the free cumulant `κ_n(a, …, a)`. -/
@[simp]
theorem coeff_freeCumulantSeries (n : ℕ) :
    coeff n (freeCumulantSeries φ a) = freeCumulant φ (fun _ : Fin n => a) univ := by
  rw [freeCumulantSeries, coeff_mk]

/-- The free cumulant of a constant word along any finite set `s` of positions in a linear order
is the coefficient of the free cumulant series at `#s`. -/
theorem freeCumulant_const_eq_coeff_freeCumulantSeries {α : Type*} [LinearOrder α]
    (s : Finset α) : freeCumulant φ (fun _ => a) s = coeff #s (freeCumulantSeries φ a) := by
  have h := freeCumulant_comp_of_strictMonoOn (s := univ) φ
    ((s.orderEmbOfFin rfl).strictMono.strictMonoOn _) fun _ => a
  simp only [image_orderEmbOfFin_univ, Function.comp_def] at h
  rw [coeff_freeCumulantSeries, ← h]

/-- The constant coefficient of the free cumulant series is `1`. -/
@[simp]
theorem constantCoeff_freeCumulantSeries : constantCoeff (freeCumulantSeries φ a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_freeCumulantSeries, univ_eq_empty,
    freeCumulant_empty]

/-- The linear coefficient of the free cumulant series is the mean `κ₁(a) = φ a`. -/
theorem coeff_one_freeCumulantSeries : coeff 1 (freeCumulantSeries φ a) = φ a := by
  rw [coeff_freeCumulantSeries, univ_unique, freeCumulant_singleton]

/-- The quadratic coefficient of the free cumulant series is the variance
`κ₂(a, a) = φ (a ^ 2) - φ a ^ 2`. -/
theorem coeff_two_freeCumulantSeries :
    coeff 2 (freeCumulantSeries φ a) = φ (a ^ 2) - φ a ^ 2 := by
  rw [coeff_freeCumulantSeries, univ_fin2, freeCumulant_pair φ _ Fin.zero_lt_one, sq, sq]

/-- The *R-series* `R(z) = ∑_{n ≥ 0} κ_{n+1}(a, …, a) z ^ n` of `a` with respect to `φ`, the
formal R-transform, so that `C(z) = 1 + z R(z)`. -/
def rSeries : R⟦X⟧ :=
  PowerSeries.mk fun n => freeCumulant φ (fun _ : Fin (n + 1) => a) univ

/-- The `n`-th coefficient of the R-series is the free cumulant `κ_{n+1}(a, …, a)`. -/
@[simp]
theorem coeff_rSeries (n : ℕ) :
    coeff n (rSeries φ a) = freeCumulant φ (fun _ : Fin (n + 1) => a) univ := by
  rw [rSeries, coeff_mk]

/-- The constant coefficient of the R-series is the mean `φ a`. -/
@[simp]
theorem constantCoeff_rSeries : constantCoeff (rSeries φ a) = φ a := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rSeries, Nat.zero_add, univ_unique,
    freeCumulant_singleton]

/-- The free cumulant series is `C(z) = 1 + z R(z)`. -/
theorem freeCumulantSeries_eq_one_add_X_mul_rSeries :
    freeCumulantSeries φ a = 1 + X * rSeries φ a := by
  ext (_ | n)
  · simp
  · simp [coeff_succ_X_mul]

/-- The coefficient of the free cumulant series at `n + 1` is the coefficient of the R-series at
`n`. -/
theorem coeff_succ_freeCumulantSeries (n : ℕ) :
    coeff (n + 1) (freeCumulantSeries φ a) = coeff n (rSeries φ a) := by
  rw [coeff_freeCumulantSeries, coeff_rSeries]

/-- The free cumulant series depends only on the moment series: if `φ (a ^ n) = ψ (b ^ n)` for
every `n`, then `a` and `b` have the same free cumulants. No normalisation is needed. -/
theorem freeCumulantSeries_congr {B : Type*} [Monoid B] {ψ : B → R} {b : B}
    (h : momentSeries φ a = momentSeries ψ b) :
    freeCumulantSeries φ a = freeCumulantSeries ψ b := by
  ext n
  simp_rw [coeff_freeCumulantSeries, freeCumulant_eq_sum_mu_mul_partitionMoment,
    partitionMoment_const, ← coeff_momentSeries, h]

/-- The R-series depends only on the moment series. No normalisation is needed. -/
theorem rSeries_congr {B : Type*} [Monoid B] {ψ : B → R} {b : B}
    (h : momentSeries φ a = momentSeries ψ b) : rSeries φ a = rSeries ψ b := by
  ext n
  rw [← coeff_succ_freeCumulantSeries, ← coeff_succ_freeCumulantSeries,
    freeCumulantSeries_congr φ a h]

variable {φ}

/-- *The moment–cumulant formula for a single variable*: for a normalised `φ`, the moment
`φ (a ^ #s)` is the sum over the noncrossing partitions `π` of a finite set `s` of positions of the
products `∏_{B ∈ π} κ_{|B|}(a, …, a)` of the coefficients of the free cumulant series. -/
theorem apply_pow_eq_sum_prod_coeff_freeCumulantSeries (hφ : φ 1 = 1) {α : Type*}
    [LinearOrder α] (s : Finset α) :
    φ (a ^ #s) =
      ∑ π : NoncrossingPartition s, ∏ B ∈ π.1.parts, coeff #B (freeCumulantSeries φ a) := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [card_empty, pow_zero, hφ, Fintype.sum_unique,
      Finpartition.parts_eq_empty_iff.2 rfl, prod_empty]
  simp_rw [← freeCumulant_const_eq_coeff_freeCumulantSeries]
  rw [← apply_prod_eq_sum_prod_freeCumulant φ (fun _ => a) hs]
  simp

/-- *The moment–cumulant functional equation*: for a normalised `φ`, the moment series and the
free cumulant series of `a` satisfy `C(z M(z)) = M(z)`. -/
theorem freeCumulantSeries_subst_X_mul_momentSeries (hφ : φ 1 = 1) :
    (freeCumulantSeries φ a).subst (X * momentSeries φ a) = momentSeries φ a :=
  NoncrossingPartition.subst_eq_of_forall_sum_prod_coeff_eq (α := ℕ)
    (constantCoeff_freeCumulantSeries φ a) fun s => by
      rw [coeff_momentSeries, apply_pow_eq_sum_prod_coeff_freeCumulantSeries a hφ]

/-- *The functional equation of the R-series*: for a normalised `φ`,
`M(z) = 1 + z M(z) R(z M(z))`. -/
theorem momentSeries_eq_one_add_X_mul_momentSeries_mul_rSeries_subst (hφ : φ 1 = 1) :
    momentSeries φ a =
      1 + X * momentSeries φ a * (rSeries φ a).subst (X * momentSeries φ a) := by
  have hM : HasSubst (X * momentSeries φ a) :=
    .of_constantCoeff_zero' (by simp)
  conv_lhs => rw [← freeCumulantSeries_subst_X_mul_momentSeries a hφ,
    freeCumulantSeries_eq_one_add_X_mul_rSeries]
  rw [subst_add hM, subst_mul hM, subst_one, subst_X hM]

/-- For a normalised `φ`, the linear coefficient of `z M(z)` is the unit `φ 1 = 1`, so that
`z M(z)` has a compositional inverse. -/
theorem isUnit_coeff_one_X_mul_momentSeries (hφ : φ 1 = 1) :
    IsUnit (coeff 1 (X * momentSeries φ a)) := by
  rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, constantCoeff_momentSeries, hφ]
  exact isUnit_one

/-- *Uniqueness of the free cumulant series*: for a normalised `φ`, every power series `C` with
`C(z M(z)) = M(z)` is the free cumulant series. -/
theorem eq_freeCumulantSeries_of_subst_eq (hφ : φ 1 = 1) {C : R⟦X⟧}
    (h : C.subst (X * momentSeries φ a) = momentSeries φ a) : C = freeCumulantSeries φ a := by
  have h0 : constantCoeff (X * momentSeries φ a) = 0 := by simp
  have hu := isUnit_coeff_one_X_mul_momentSeries a hφ
  rw [eq_subst_substInvOfIsUnit_of_subst_eq h0 hu h,
    ← eq_subst_substInvOfIsUnit_of_subst_eq h0 hu
      (freeCumulantSeries_subst_X_mul_momentSeries a hφ)]

/-- For a normalised `φ`, the free cumulant series is the moment series composed with the
compositional inverse of `z M(z)`: `C = M ∘ (z M)⁻¹`. -/
theorem freeCumulantSeries_eq_subst_substInvOfIsUnit (hφ : φ 1 = 1) :
    freeCumulantSeries φ a = (momentSeries φ a).subst
      ((X * momentSeries φ a).substInvOfIsUnit (isUnit_coeff_one_X_mul_momentSeries a hφ)) :=
  eq_subst_substInvOfIsUnit_of_subst_eq (by simp) _
    (freeCumulantSeries_subst_X_mul_momentSeries a hφ)

/-- For normalised functionals, two elements have the same moment series exactly when they have the
same free cumulant series. -/
theorem freeCumulantSeries_eq_iff_momentSeries_eq (hφ : φ 1 = 1) {B : Type*} [Monoid B]
    {ψ : B → R} {b : B} (hψ : ψ 1 = 1) :
    freeCumulantSeries φ a = freeCumulantSeries ψ b ↔ momentSeries φ a = momentSeries ψ b := by
  refine ⟨fun h => ?_, freeCumulantSeries_congr φ a⟩
  -- Both moments are the noncrossing-partition sums of the common free cumulants.
  ext n
  have ha := apply_pow_eq_sum_prod_coeff_freeCumulantSeries a hφ (univ : Finset (Fin n))
  have hb := apply_pow_eq_sum_prod_coeff_freeCumulantSeries b hψ (univ : Finset (Fin n))
  rw [card_univ, Fintype.card_fin] at ha hb
  rw [coeff_momentSeries, coeff_momentSeries, ha, hb, h]

end Monoid

section Algebra

variable [Semiring A] [Algebra R A] {φ : A →ₗ[R] R}

/-- Rescaling `a` by `c` rescales its free cumulant series: `C_{c a}(z) = C_a(c z)`, since
`κ_n` is multilinear. -/
theorem freeCumulantSeries_smul (φ : A →ₗ[R] R) (c : R) (a : A) :
    freeCumulantSeries φ (c • a) = rescale c (freeCumulantSeries φ a) := by
  ext n
  have h := (freeCumulantMultilinear (α := Fin n) φ).map_smul_univ (fun _ => c) fun _ => a
  rw [freeCumulantMultilinear_apply, freeCumulantMultilinear_apply, prod_const, card_univ,
    Fintype.card_fin, smul_eq_mul] at h
  rw [coeff_freeCumulantSeries, coeff_rescale, coeff_freeCumulantSeries, h]

/-- For a normalised `φ`, adding the scalar `c` to `a` adds the constant `c` to its R-series:
`R_{a + c}(z) = R_a(z) + c`. Only the mean `κ₁` changes. -/
theorem rSeries_add_algebraMap (hφ : φ 1 = 1) (a : A) (c : R) :
    rSeries φ (a + algebraMap R A c) = rSeries φ a + PowerSeries.C c := by
  ext (_ | n)
  · simp [Algebra.algebraMap_eq_smul_one, hφ]
  · rw [coeff_rSeries, map_add, coeff_rSeries, coeff_succ_C, add_zero]
    exact freeCumulant_add_algebraMap φ (fun _ => a) hφ (fun _ => c)
      (by rw [card_univ, Fintype.card_fin]; omega)

/-- Rescaling `a` by `c` transforms its R-series by `R_{c a}(z) = c R_a(c z)`. -/
theorem rSeries_smul (φ : A →ₗ[R] R) (c : R) (a : A) :
    rSeries φ (c • a) = c • rescale c (rSeries φ a) := by
  ext n
  simp [pow_succ', mul_assoc]

/-- The R-series of `0` vanishes. -/
@[simp]
theorem rSeries_zero : rSeries φ (0 : A) = 0 := by
  ext n
  rw [coeff_rSeries, ← freeCumulantMultilinear_apply,
    (freeCumulantMultilinear φ).map_coord_zero 0 rfl, map_zero]

/-- For a normalised `φ`, the R-series of the scalar `c • 1` is the constant `c`: its only nonzero
free cumulant is its mean. -/
@[simp]
theorem rSeries_algebraMap (hφ : φ 1 = 1) (c : R) :
    rSeries φ (algebraMap R A c) = PowerSeries.C c := by
  simpa using rSeries_add_algebraMap hφ 0 c

/-- *The R-series is additive on free families*: if each `a k` lies in the subalgebra `B k`, with
`B` freely independent for a normalised `φ`, then `R_{∑ k ∈ T, a k} = ∑ k ∈ T, R_{a k}`. -/
theorem IsFreelyIndependent.rSeries_sum {ι : Type*} {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {T : Finset ι} {a : ι → A}
    (ha : ∀ k ∈ T, a k ∈ B k) :
    rSeries φ (∑ k ∈ T, a k) = ∑ k ∈ T, rSeries φ (a k) := by
  ext n
  rw [coeff_rSeries, map_sum, h.freeCumulant_sum hφ (fun k hk _ _ => ha k hk) univ_nonempty]
  simp

/-- *The R-series is additive on two free subalgebras*: if `a ∈ B i` and `b ∈ B j` for `i ≠ j`,
with `B` freely independent for a normalised `φ`, then `R_{a + b} = R_a + R_b`. -/
theorem IsFreelyIndependent.rSeries_add {ι : Type*} {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ B i) (hb : b ∈ B j) :
    rSeries φ (a + b) = rSeries φ a + rSeries φ b := by
  ext n
  rw [coeff_rSeries, map_add, h.freeCumulant_add hφ hij (fun _ _ => ha) (fun _ _ => hb)
    univ_nonempty, coeff_rSeries, coeff_rSeries]

/-- *The R-series is additive on free elements*: if the elements `c k` are freely independent
for a normalised `φ`, then `R_{∑ k ∈ T, c k} = ∑ k ∈ T, R_{c k}`. -/
theorem IsFreelyIndependentElements.rSeries_sum {ι : Type*} {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) (T : Finset ι) :
    rSeries φ (∑ k ∈ T, c k) = ∑ k ∈ T, rSeries φ (c k) :=
  (isFreelyIndependentElements_iff.mp h).rSeries_sum hφ fun k _ =>
    Algebra.self_mem_adjoin_singleton R (c k)

/-- *The R-series is additive on two free elements*: if `c i` and `c j`, for `i ≠ j`, belong to a
freely independent family for a normalised `φ`, then `R_{c i + c j} = R_{c i} + R_{c j}`. -/
theorem IsFreelyIndependentElements.rSeries_add {ι : Type*} {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) :
    rSeries φ (c i + c j) = rSeries φ (c i) + rSeries φ (c j) :=
  (isFreelyIndependentElements_iff.mp h).rSeries_add hφ hij (Algebra.self_mem_adjoin_singleton R _)
    (Algebra.self_mem_adjoin_singleton R _)

end Algebra

end TauCeti
