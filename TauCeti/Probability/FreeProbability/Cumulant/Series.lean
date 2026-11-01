/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.PowerSeries
public import TauCeti.Probability.FreeProbability.Cumulant.Free
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The moment series, the free cumulant series and the R-transform

Let `φ : A → R` be a function on a monoid `A` with values in a commutative ring (in free
probability, a normalised linear functional on an algebra, used through its coercion to a
function), and let `a : A`. This file attaches to
`a` three formal power series:

* the *moment series* `M(z) = ∑_{n ≥ 0} φ (a ^ n) z^n`, so `M(z) = 1 + ∑_{n ≥ 1} m_n z^n` when
  `φ 1 = 1`;
* the *free cumulant series* `C(z) = 1 + ∑_{n ≥ 1} κ_n z^n`, where `κ_n = κ_n(a, …, a)` is the
  `n`-th free cumulant of `a`;
* the *R-transform* `R(z) = ∑_{n ≥ 1} κ_n z^(n - 1)`, so that `C(z) = 1 + z R(z)`.

For a normalised `φ` the moment–cumulant formula of noncrossing partitions becomes the functional
equation

`M(z) = C(z M(z)) = 1 + z M(z) R(z M(z))`,

an identity of formal power series proved coefficient by coefficient from the decomposition of a
noncrossing partition by its part through the first position. Since `z M(z)` has linear
coefficient `φ 1 = 1`, it has a compositional inverse, and the functional equation determines the
cumulant series from the moment series: `C = M ∘ (z M)^⟨-1⟩`. These are formal identities; no
convergence or analytic inverse is asserted.

Free cumulants are additive on free elements, so the R-transform linearises free additive
convolution at the formal level: `R_{a + b} = R_a + R_b` for free `a` and `b`.

## Main definitions

* `TauCeti.momentSeries φ a` — the moment series `M(z) = ∑_{n ≥ 0} φ (a ^ n) z^n`.
* `TauCeti.freeCumulantSeries φ a` — the free cumulant series `C(z) = 1 + ∑_{n ≥ 1} κ_n z^n`.
* `TauCeti.rTransform φ a` — the R-transform `R(z) = ∑_{n ≥ 1} κ_n z^(n - 1)`.

## Main results

* `TauCeti.freeCumulantSeries_eq_one_add_X_mul_rTransform` — `C(z) = 1 + z R(z)`.
* `TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries` — the free cumulant of the constant
  word `(a, …, a)` along any finite set `s` of positions is the coefficient of `C` at `|s|`.
* `TauCeti.freeCumulantSeries_subst_X_mul_momentSeries` — the functional equation
  `M(z) = C(z M(z))` for normalised `φ`.
* `TauCeti.momentSeries_eq_one_add_X_mul_momentSeries_mul_subst_rTransform` — its R-transform
  form `M(z) = 1 + z M(z) R(z M(z))`.
* `TauCeti.freeCumulantSeries_eq_subst_substInvOfIsUnit` — `C = M ∘ (z M)^⟨-1⟩`, and more
  generally `TauCeti.freeCumulantSeries_eq_subst_of_subst_eq_X` — `C = M ∘ Q` for every right
  compositional inverse `Q` of `z M(z)`.
* `TauCeti.eq_freeCumulantSeries_of_subst_eq` — the cumulant series is the only series `C'` with
  `M(z) = C'(z M(z))`.
* `TauCeti.IsFreelyIndependentElements.rTransform_sum` and
  `TauCeti.IsFreelyIndependentElements.rTransform_add` — the R-transform is additive on free
  elements.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 16 (the
  functional relation between the moment series and the cumulant series) and Lecture 12 (the
  R-transform and its additivity on free variables).
* D. Voiculescu, *Addition of certain noncommuting random variables*, J. Funct. Anal. 66 (1986),
  323–346.
-/

public section

open Finset PowerSeries

namespace TauCeti

variable {R A : Type*}

section Moment

variable [Semiring R] [Monoid A] (φ : A → R) (a : A)

/-- The *moment series* `M(z) = ∑_{n ≥ 0} φ (a ^ n) z^n` of `a`. -/
noncomputable def momentSeries : R⟦X⟧ :=
  mk fun n => φ (a ^ n)

@[simp]
theorem coeff_momentSeries (n : ℕ) : coeff n (momentSeries φ a) = φ (a ^ n) := by
  rw [momentSeries, coeff_mk]

@[simp]
theorem constantCoeff_momentSeries : constantCoeff (momentSeries φ a) = φ 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_momentSeries, pow_zero]

/-- The series `z M(z)` has constant coefficient `0`. -/
theorem constantCoeff_X_mul_momentSeries : constantCoeff (X * momentSeries φ a) = 0 := by
  rw [map_mul, constantCoeff_X, zero_mul]

/-- The linear coefficient of `z M(z)` is `φ 1`. -/
theorem coeff_one_X_mul_momentSeries : coeff 1 (X * momentSeries φ a) = φ 1 := by
  rw [coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply, constantCoeff_momentSeries]

/-- For a normalised `φ`, the linear coefficient of `z M(z)` is a unit, so `z M(z)` has a
compositional inverse `PowerSeries.substInvOfIsUnit`. -/
theorem isUnit_coeff_one_X_mul_momentSeries (hφ : φ 1 = 1) :
    IsUnit (coeff 1 (X * momentSeries φ a)) := by
  rw [coeff_one_X_mul_momentSeries, hφ]
  exact isUnit_one

end Moment

section Cumulant

variable [CommRing R] [Monoid A] (φ : A → R) (a : A)

/-- The series `z M(z)` can be substituted into formal power series. -/
theorem hasSubst_X_mul_momentSeries : HasSubst (X * momentSeries φ a) :=
  HasSubst.of_constantCoeff_zero' (constantCoeff_X_mul_momentSeries φ a)

/-- The *free cumulant series* `C(z) = 1 + ∑_{n ≥ 1} κ_n z^n` of `a`, where `κ_n` is the `n`-th
free cumulant `κ_n(a, …, a)`. Its constant coefficient is the free cumulant of the empty word,
which is `1`. -/
noncomputable def freeCumulantSeries : R⟦X⟧ :=
  mk fun n => freeCumulant φ (fun _ : Fin n => a) univ

/-- The formal *R-transform* `R(z) = ∑_{n ≥ 1} κ_n z^(n - 1)` of `a` in free probability: its
coefficient at `n` is the `(n + 1)`-st free cumulant `κ_{n+1}(a, …, a)`. -/
noncomputable def rTransform : R⟦X⟧ :=
  mk fun n => freeCumulant φ (fun _ : Fin (n + 1) => a) univ

@[simp]
theorem coeff_freeCumulantSeries (n : ℕ) :
    coeff n (freeCumulantSeries φ a) = freeCumulant φ (fun _ : Fin n => a) univ := by
  rw [freeCumulantSeries, coeff_mk]

@[simp]
theorem coeff_rTransform (n : ℕ) :
    coeff n (rTransform φ a) = freeCumulant φ (fun _ : Fin (n + 1) => a) univ := by
  rw [rTransform, coeff_mk]

@[simp]
theorem constantCoeff_freeCumulantSeries : constantCoeff (freeCumulantSeries φ a) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_freeCumulantSeries, univ_eq_empty,
    freeCumulant_empty]

/-- The linear coefficient of the free cumulant series is the mean `κ₁ = φ a`. -/
theorem coeff_one_freeCumulantSeries : coeff 1 (freeCumulantSeries φ a) = φ a := by
  rw [coeff_freeCumulantSeries, univ_unique, freeCumulant_singleton]

/-- The constant coefficient of the R-transform is the mean `κ₁ = φ a`. -/
@[simp]
theorem constantCoeff_rTransform : constantCoeff (rTransform φ a) = φ a := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rTransform, zero_add, univ_unique,
    freeCumulant_singleton]

/-- The free cumulant series is `C(z) = 1 + z R(z)`. -/
theorem freeCumulantSeries_eq_one_add_X_mul_rTransform :
    freeCumulantSeries φ a = 1 + X * rTransform φ a := by
  ext (_ | n)
  · simp
  · simp [coeff_succ_X_mul, coeff_one]

/-- The free cumulant of the constant word `(a, …, a)` along a finite set `s` of positions is the
`|s|`-th free cumulant `κ_{|s|}(a, …, a)`, the coefficient of the free cumulant series at
`|s|`. -/
theorem freeCumulant_const_eq_coeff_freeCumulantSeries {α : Type*} [LinearOrder α]
    (s : Finset α) : freeCumulant φ (fun _ => a) s = coeff #s (freeCumulantSeries φ a) := by
  have h := freeCumulant_comp_of_strictMonoOn φ
    ((s.orderEmbOfFin rfl).strictMono.strictMonoOn (univ : Finset (Fin #s))) fun _ => a
  rw [image_orderEmbOfFin_univ] at h
  rw [coeff_freeCumulantSeries, ← h, Function.comp_def]

/-- *The moment–cumulant functional equation*: for a normalised `φ`, the moment series and the
free cumulant series of `a` satisfy `M(z) = C(z M(z))`. -/
theorem freeCumulantSeries_subst_X_mul_momentSeries (hφ : φ 1 = 1) :
    (freeCumulantSeries φ a).subst (X * momentSeries φ a) = momentSeries φ a := by
  refine (NoncrossingPartition.subst_X_mul_eq_iff (α := ℕ)
    (constantCoeff_freeCumulantSeries φ a)).2 fun s => ?_
  simp_rw [← freeCumulant_const_eq_coeff_freeCumulantSeries, coeff_momentSeries]
  obtain rfl | hs := s.eq_empty_or_nonempty
  · -- The empty partition has weight `1 = φ 1`.
    rw [card_empty, pow_zero, hφ, Fintype.sum_unique,
      Finpartition.parts_eq_empty_iff.2 rfl, prod_empty]
  · -- The moment–cumulant formula for the constant word `(a, …, a)` along `s`.
    rw [← apply_prod_eq_sum_prod_freeCumulant φ (fun _ => a) hs, List.map_const',
      List.prod_replicate, length_sort]

/-- *The moment–cumulant functional equation in terms of the R-transform*: for a normalised `φ`,
`M(z) = 1 + z M(z) R(z M(z))`. -/
theorem momentSeries_eq_one_add_X_mul_momentSeries_mul_subst_rTransform (hφ : φ 1 = 1) :
    momentSeries φ a =
      1 + X * momentSeries φ a * (rTransform φ a).subst (X * momentSeries φ a) := by
  have hP := hasSubst_X_mul_momentSeries φ a
  conv_lhs => rw [← freeCumulantSeries_subst_X_mul_momentSeries φ a hφ,
    freeCumulantSeries_eq_one_add_X_mul_rTransform]
  rw [subst_add hP, subst_mul hP, subst_X hP, subst_one hP]

/-- For a normalised `φ`, the free cumulant series is determined by the moment series through
compositional inversion: `C = M ∘ Q` for every right compositional inverse `Q` of `z M(z)`. See
`TauCeti.freeCumulantSeries_eq_subst_substInvOfIsUnit` for `Q = PowerSeries.substInvOfIsUnit`. -/
theorem freeCumulantSeries_eq_subst_of_subst_eq_X (hφ : φ 1 = 1) {Q : R⟦X⟧} (hQ : HasSubst Q)
    (h : (X * momentSeries φ a).subst Q = X) :
    freeCumulantSeries φ a = (momentSeries φ a).subst Q := by
  conv_rhs => rw [← freeCumulantSeries_subst_X_mul_momentSeries φ a hφ]
  rw [subst_comp_subst_apply (hasSubst_X_mul_momentSeries φ a) hQ, h, X_subst]

/-- For a normalised `φ`, the free cumulant series is the moment series composed with the
compositional inverse of `z M(z)`: `C = M ∘ (z M)^⟨-1⟩`. -/
theorem freeCumulantSeries_eq_subst_substInvOfIsUnit (hφ : φ 1 = 1) :
    freeCumulantSeries φ a = (momentSeries φ a).subst
      ((X * momentSeries φ a).substInvOfIsUnit (isUnit_coeff_one_X_mul_momentSeries φ a hφ)) :=
  freeCumulantSeries_eq_subst_of_subst_eq_X φ a hφ (HasSubst.substInvOfIsUnit _ _)
    (subst_substInvOfIsUnit_right _ (constantCoeff_X_mul_momentSeries φ a) _)

/-- For a normalised `φ`, the free cumulant series is the only series `C'` with
`M(z) = C'(z M(z))`. -/
theorem eq_freeCumulantSeries_of_subst_eq (hφ : φ 1 = 1) {C' : R⟦X⟧}
    (h : C'.subst (X * momentSeries φ a) = momentSeries φ a) : C' = freeCumulantSeries φ a := by
  have h1 := isUnit_coeff_one_X_mul_momentSeries φ a hφ
  have hQ := HasSubst.substInvOfIsUnit _ h1
  have hPQ := subst_substInvOfIsUnit_right _ (constantCoeff_X_mul_momentSeries φ a) h1
  rw [freeCumulantSeries_eq_subst_substInvOfIsUnit φ a hφ]
  generalize (X * momentSeries φ a).substInvOfIsUnit h1 = Q at hQ hPQ ⊢
  rw [← h, subst_comp_subst_apply (hasSubst_X_mul_momentSeries φ a) hQ, hPQ, X_subst]

end Cumulant

section Free

variable {ι : Type*} [CommRing R] [Semiring A] [Algebra R A] {φ : A →ₗ[R] R} {c : ι → A}

/-- *The R-transform linearises free additive convolution*: for a normalised `φ` and freely
independent elements `c k`, the R-transform of a finite sum `∑_{k ∈ T} c k` is the sum of the
R-transforms. -/
theorem IsFreelyIndependentElements.rTransform_sum (h : IsFreelyIndependentElements φ c)
    (hφ : φ 1 = 1) (T : Finset ι) :
    rTransform φ (∑ k ∈ T, c k) = ∑ k ∈ T, rTransform φ (c k) := by
  ext n
  rw [coeff_rTransform, map_sum, h.freeCumulant_sum hφ T univ_nonempty]
  simp_rw [coeff_rTransform]

/-- *The R-transform linearises free additive convolution*: for a normalised `φ` and freely
independent elements `c i` and `c j` with `i ≠ j`, `R_{c i + c j} = R_{c i} + R_{c j}`. -/
theorem IsFreelyIndependentElements.rTransform_add (h : IsFreelyIndependentElements φ c)
    (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) :
    rTransform φ (c i + c j) = rTransform φ (c i) + rTransform φ (c j) := by
  ext n
  rw [coeff_rTransform, map_add, h.freeCumulant_add hφ hij univ_nonempty, coeff_rTransform,
    coeff_rTransform]

end Free

end TauCeti
