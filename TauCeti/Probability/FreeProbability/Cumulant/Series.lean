/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.PowerSeries
public import TauCeti.Probability.FreeProbability.Cumulant.Free

/-!
# The moment series, the free cumulant series and the R-series of one variable

Let `φ : A → R` be a functional on a monoid `A` with values in a commutative ring, and let `x ∈ A`.
This file packages the moments and free cumulants of `x` into formal power series:

* the *moment series* `M(z) = ∑_{n ≥ 0} φ (x ^ n) z ^ n`, whose constant coefficient is `φ 1`;
* the *free cumulant series* `C(z) = 1 + ∑_{n ≥ 1} κ_n(x, …, x) z ^ n`;
* the *R-series* `R(z) = ∑_{n ≥ 0} κ_{n+1}(x, …, x) z ^ n`, so that `C(z) = 1 + z R(z)`.

For a normalised functional, `φ 1 = 1`, the moment–cumulant formula over noncrossing partitions is
equivalent to the functional equation

`M(z) = C(z M(z)) = 1 + z M(z) R(z M(z))`,

proved coefficient by coefficient from the recurrence by the part containing the first position.
Since `z M(z)` has constant coefficient `0` and linear coefficient `φ 1 = 1`, it has a
compositional inverse, and the functional equation determines `C` from `M`: the free cumulant series
is `M` composed with that inverse, and it is the only series `C'` with `M(z) = C'(z M(z))`.

The R-series linearises free independence: for free elements `a`, `b` of a normalised functional,
`R_{a+b} = R_a + R_b`, because free cumulants are additive on free families. Under the affine maps
`x ↦ c • x` and `x ↦ x + c • 1` the R-series transforms by `R_{c • x}(z) = c R_x(c z)` and
`R_{x + c • 1} = R_x + c`. These are the formal, coefficientwise forms of the R-transform of
Voiculescu; no convergence or analytic inversion is asserted.

## Main definitions

* `TauCeti.momentSeries φ x` — the moment series `M(z)`.
* `TauCeti.freeCumulantSeries φ x` — the free cumulant series `C(z)`.
* `TauCeti.rSeries φ x` — the R-series `R(z)`.

## Main results

* `TauCeti.freeCumulantSeries_subst_X_mul_momentSeries` — `C(z M(z)) = M(z)` for a normalised `φ`.
* `TauCeti.momentSeries_eq_one_add_X_mul_momentSeries_mul_subst_rSeries` —
  `M(z) = 1 + z M(z) R(z M(z))`.
* `TauCeti.freeCumulantSeries_eq_subst_of_subst_eq_X` and
  `TauCeti.eq_freeCumulantSeries_of_subst_eq` — `C` is `M` composed with the compositional inverse
  of `z M(z)`, and it is the unique solution of the functional equation.
* `TauCeti.freeCumulantSeries_eq_iff_momentSeries_eq` — two normalised functionals give elements
  the same moment series exactly when they give them the same free cumulant series.
* `TauCeti.IsFreelyIndependent.rSeries_sum` and `TauCeti.IsFreelyIndependent.rSeries_add` — the
  R-series is additive on elements of freely independent subalgebras, with the element versions
  `TauCeti.IsFreelyIndependentElements.rSeries_sum` and
  `TauCeti.IsFreelyIndependentElements.rSeries_add`.
* `TauCeti.rSeries_smul` and `TauCeti.rSeries_add_algebraMap` — the R-series under dilations and
  translations by scalars.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 16 for the
  functional equation and Lecture 12 for the additivity of the R-transform.
* D. V. Voiculescu, *Addition of certain non-commuting random variables*, J. Funct. Anal. 66
  (1986), 323–346.
-/

public section

open Finset PowerSeries

namespace TauCeti

variable {R A A' : Type*}

section Moment

variable [Semiring R] [Monoid A]

/-- The *moment series* `M(z) = ∑_{n ≥ 0} φ (x ^ n) z ^ n` of an element `x` for a functional `φ`.
Its constant coefficient is `φ 1`, which is `1` for a normalised functional. -/
def momentSeries (φ : A → R) (x : A) : R⟦X⟧ :=
  mk fun n => φ (x ^ n)

/-- The coefficients of the moment series are the moments. -/
@[simp]
theorem coeff_momentSeries (φ : A → R) (x : A) (n : ℕ) :
    coeff n (momentSeries φ x) = φ (x ^ n) := by
  rw [momentSeries, coeff_mk]

/-- The constant coefficient of the moment series is `φ 1`. -/
@[simp]
theorem constantCoeff_momentSeries (φ : A → R) (x : A) :
    constantCoeff (momentSeries φ x) = φ 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_momentSeries, pow_zero]

end Moment

section Cumulant

variable [CommRing R] [Monoid A] [Monoid A'] (φ : A → R) (x : A)

/-- The *free cumulant series* `C(z) = 1 + ∑_{n ≥ 1} κ_n(x, …, x) z ^ n` of an element `x` for a
functional `φ`, whose coefficient at `n ≥ 1` is the free cumulant of the constant word of length
`n` with letter `x`. -/
def freeCumulantSeries : R⟦X⟧ :=
  mk fun n => freeCumulant φ (fun _ => x) (univ : Finset (Fin n))

/-- The coefficients of the free cumulant series are the free cumulants of constant words. -/
@[simp]
theorem coeff_freeCumulantSeries (n : ℕ) :
    coeff n (freeCumulantSeries φ x) = freeCumulant φ (fun _ => x) (univ : Finset (Fin n)) := by
  rw [freeCumulantSeries, coeff_mk]

/-- The free cumulant of the constant word with letter `x` along any finite set `s` of positions is
the coefficient of the free cumulant series at `#s`. -/
theorem freeCumulant_const_eq_coeff_freeCumulantSeries {α : Type*} [LinearOrder α]
    (s : Finset α) :
    freeCumulant φ (fun _ => x) s = coeff #s (freeCumulantSeries φ x) := by
  -- Relabel `s` increasingly by `Fin #s`.
  have h := freeCumulant_comp_of_strictMonoOn φ (s := (univ : Finset (Fin #s)))
    ((s.orderEmbOfFin rfl).strictMono.strictMonoOn _) fun _ => x
  rw [s.image_orderEmbOfFin_univ rfl] at h
  simpa [Function.comp_def] using h.symm

/-- The constant coefficient of the free cumulant series is `1`. -/
@[simp]
theorem constantCoeff_freeCumulantSeries : constantCoeff (freeCumulantSeries φ x) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_freeCumulantSeries, univ_eq_empty,
    freeCumulant_empty]

/-- The linear coefficient of the free cumulant series is the mean `φ x`. -/
theorem coeff_one_freeCumulantSeries : coeff 1 (freeCumulantSeries φ x) = φ x := by
  rw [coeff_freeCumulantSeries, univ_unique, freeCumulant_singleton]

/-- The quadratic coefficient of the free cumulant series is the variance `φ (x ^ 2) - φ x ^ 2`. -/
theorem coeff_two_freeCumulantSeries :
    coeff 2 (freeCumulantSeries φ x) = φ (x ^ 2) - φ x ^ 2 := by
  rw [coeff_freeCumulantSeries, freeCumulant_const_of_card_eq_two φ x (card_fin 2)]

/-- The *R-series* `R(z) = ∑_{n ≥ 0} κ_{n+1}(x, …, x) z ^ n` of an element `x` for a functional
`φ`: the free cumulant series with its constant term removed and divided by `z`. -/
def rSeries : R⟦X⟧ :=
  mk fun n => freeCumulant φ (fun _ => x) (univ : Finset (Fin (n + 1)))

/-- The coefficients of the R-series are the free cumulants of nonempty constant words. -/
@[simp]
theorem coeff_rSeries (n : ℕ) :
    coeff n (rSeries φ x) = freeCumulant φ (fun _ => x) (univ : Finset (Fin (n + 1))) := by
  rw [rSeries, coeff_mk]

/-- The coefficient of the free cumulant series at `n + 1` is the coefficient of the R-series at
`n`. -/
theorem coeff_succ_freeCumulantSeries (n : ℕ) :
    coeff (n + 1) (freeCumulantSeries φ x) = coeff n (rSeries φ x) := by
  rw [coeff_freeCumulantSeries, coeff_rSeries]

/-- The constant coefficient of the R-series is the mean `φ x`. -/
@[simp]
theorem constantCoeff_rSeries : constantCoeff (rSeries φ x) = φ x := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_succ_freeCumulantSeries, zero_add,
    coeff_one_freeCumulantSeries]

/-- The free cumulant series is `C(z) = 1 + z R(z)`. -/
theorem freeCumulantSeries_eq_one_add_X_mul_rSeries :
    freeCumulantSeries φ x = 1 + X * rSeries φ x := by
  ext (_ | n)
  · simp
  · simp [coeff_succ_X_mul]

variable {φ}

/-- *The moment–cumulant functional equation.* For a normalised functional, the moment series and
the free cumulant series satisfy `C(z M(z)) = M(z)`. -/
theorem freeCumulantSeries_subst_X_mul_momentSeries (hφ : φ 1 = 1) :
    (freeCumulantSeries φ x).subst (X * momentSeries φ x) = momentSeries φ x := by
  refine NoncrossingPartition.subst_X_mul_eq_of_forall_sum_prod_coeff_eq_coeff (α := ℕ)
    (constantCoeff_freeCumulantSeries φ x) fun s => ?_
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [Fintype.sum_unique, Finpartition.parts_eq_empty_iff.2 rfl, prod_empty, card_empty,
      coeff_momentSeries, pow_zero, hφ]
  -- This is the moment–cumulant formula for the constant word with letter `x` along `s`.
  rw [coeff_momentSeries, ← length_sort (· ≤ ·) (s := s), ← List.prod_replicate,
    ← List.map_const', apply_prod_eq_sum_prod_freeCumulant φ _ hs]
  simp_rw [freeCumulant_const_eq_coeff_freeCumulantSeries φ x]

/-- *The functional equation of the R-series.* For a normalised functional,
`M(z) = 1 + z M(z) R(z M(z))`. -/
theorem momentSeries_eq_one_add_X_mul_momentSeries_mul_subst_rSeries (hφ : φ 1 = 1) :
    momentSeries φ x =
      1 + X * momentSeries φ x * (rSeries φ x).subst (X * momentSeries φ x) := by
  have h := freeCumulantSeries_subst_X_mul_momentSeries x hφ
  rwa [freeCumulantSeries_eq_one_add_X_mul_rSeries,
    ← coe_substAlgHom (HasSubst.X'.mul_left (g := momentSeries φ x)), map_add, map_mul, map_one,
    substAlgHom_X, coe_substAlgHom, eq_comm] at h

/-- For a normalised functional, the free cumulant series is the moment series composed with any
right compositional inverse `Q` of `z M(z)`: if `(z M(z))(Q(w)) = w` then `C(w) = M(Q(w))`. -/
theorem freeCumulantSeries_eq_subst_of_subst_eq_X (hφ : φ 1 = 1) {Q : R⟦X⟧} (hQ : HasSubst Q)
    (hQM : (X * momentSeries φ x).subst Q = X) :
    freeCumulantSeries φ x = (momentSeries φ x).subst Q := by
  rw [← freeCumulantSeries_subst_X_mul_momentSeries x hφ,
    subst_comp_subst_apply HasSubst.X'.mul_left hQ, hQM, X_subst]

/-- For a normalised functional, the free cumulant series is the only series `C'` satisfying the
functional equation `C'(z M(z)) = M(z)`. -/
theorem eq_freeCumulantSeries_of_subst_eq (hφ : φ 1 = 1) {C' : R⟦X⟧}
    (hC' : C'.subst (X * momentSeries φ x) = momentSeries φ x) :
    C' = freeCumulantSeries φ x := by
  -- Compose both sides of the functional equation with the inverse of `z M(z)`.
  have h0 : constantCoeff (X * momentSeries φ x) = 0 := by simp
  have h1 : IsUnit (coeff 1 (X * momentSeries φ x)) := by simp [coeff_succ_X_mul, hφ]
  have key (D : R⟦X⟧) : PowerSeries.subst ((X * momentSeries φ x).substInvOfIsUnit h1)
      (D.subst (X * momentSeries φ x)) = D := by
    rw [subst_comp_subst_apply HasSubst.X'.mul_left (HasSubst.substInvOfIsUnit _ h1),
      subst_substInvOfIsUnit_right _ h0 h1, X_subst]
  rw [← key C', ← key (freeCumulantSeries φ x), hC',
    freeCumulantSeries_subst_X_mul_momentSeries x hφ]

/-- The free cumulant series depends only on the moment series. No normalisation is needed: the
free cumulants of constant words are Möbius combinations of products of moments. -/
theorem freeCumulantSeries_eq_of_momentSeries_eq {ψ : A' → R} {y : A'}
    (h : momentSeries φ x = momentSeries ψ y) :
    freeCumulantSeries φ x = freeCumulantSeries ψ y := by
  ext n
  simp only [coeff_freeCumulantSeries, freeCumulant_eq_sum_mu_mul_partitionMoment,
    partitionMoment_const, ← coeff_momentSeries, h]

/-- For normalised functionals, two elements have the same moment series exactly when they have the
same free cumulant series. -/
theorem freeCumulantSeries_eq_iff_momentSeries_eq (hφ : φ 1 = 1) {ψ : A' → R} {y : A'}
    (hψ : ψ 1 = 1) :
    freeCumulantSeries φ x = freeCumulantSeries ψ y ↔ momentSeries φ x = momentSeries ψ y := by
  refine ⟨fun h => ?_, freeCumulantSeries_eq_of_momentSeries_eq x⟩
  -- Both moment series are the noncrossing-partition sums of the common cumulant series.
  ext n
  have hx := NoncrossingPartition.sum_prod_coeff_eq_coeff_of_subst_eq
    (constantCoeff_freeCumulantSeries φ x) (freeCumulantSeries_subst_X_mul_momentSeries x hφ)
    (univ : Finset (Fin n))
  have hy := NoncrossingPartition.sum_prod_coeff_eq_coeff_of_subst_eq
    (constantCoeff_freeCumulantSeries ψ y) (freeCumulantSeries_subst_X_mul_momentSeries y hψ)
    (univ : Finset (Fin n))
  rw [card_fin] at hx hy
  rw [← hx, ← hy, h]

/-- The R-series depends only on the moment series. -/
theorem rSeries_eq_of_momentSeries_eq {ψ : A' → R} {y : A'}
    (h : momentSeries φ x = momentSeries ψ y) : rSeries φ x = rSeries ψ y := by
  ext n
  rw [← coeff_succ_freeCumulantSeries, ← coeff_succ_freeCumulantSeries,
    freeCumulantSeries_eq_of_momentSeries_eq x h]

end Cumulant

section Linear

variable [CommRing R] [Semiring A] [Algebra R A] {φ : A →ₗ[R] R}

/-- *The R-series is additive on free families*: if each `x k` lies in the subalgebra `B k`, with
`B` freely independent for a normalised `φ`, then `R_{∑ k ∈ T, x k} = ∑ k ∈ T, R_{x k}`. -/
theorem IsFreelyIndependent.rSeries_sum {ι : Type*} {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {T : Finset ι} {x : ι → A}
    (hx : ∀ k ∈ T, x k ∈ B k) :
    rSeries φ (∑ k ∈ T, x k) = ∑ k ∈ T, rSeries φ (x k) := by
  ext n
  rw [coeff_rSeries, map_sum, h.freeCumulant_sum hφ (fun k hk _ _ => hx k hk) univ_nonempty]
  simp

/-- *The R-series is additive on two free subalgebras*: if `x ∈ B i` and `y ∈ B j` for `i ≠ j`,
with `B` freely independent for a normalised `φ`, then `R_{x + y} = R_x + R_y`. -/
theorem IsFreelyIndependent.rSeries_add {ι : Type*} {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {x y : A}
    (hx : x ∈ B i) (hy : y ∈ B j) :
    rSeries φ (x + y) = rSeries φ x + rSeries φ y := by
  ext n
  rw [coeff_rSeries, map_add, h.freeCumulant_add hφ hij (fun _ _ => hx) (fun _ _ => hy)
    univ_nonempty, coeff_rSeries, coeff_rSeries]

/-- *The R-series is additive on free elements*: if the elements `c k` are freely independent for
a normalised `φ`, then `R_{∑ k ∈ T, c k} = ∑ k ∈ T, R_{c k}`. -/
theorem IsFreelyIndependentElements.rSeries_sum {ι : Type*} {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) (T : Finset ι) :
    rSeries φ (∑ k ∈ T, c k) = ∑ k ∈ T, rSeries φ (c k) :=
  (isFreelyIndependentElements_iff.1 h).rSeries_sum hφ fun k _ =>
    Algebra.self_mem_adjoin_singleton R (c k)

/-- *The R-series is additive on two free elements*: if `c i` and `c j`, for `i ≠ j`, belong to a
freely independent family for a normalised `φ`, then `R_{c i + c j} = R_{c i} + R_{c j}`. -/
theorem IsFreelyIndependentElements.rSeries_add {ι : Type*} {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) :
    rSeries φ (c i + c j) = rSeries φ (c i) + rSeries φ (c j) :=
  (isFreelyIndependentElements_iff.1 h).rSeries_add hφ hij
    (Algebra.self_mem_adjoin_singleton R (c i)) (Algebra.self_mem_adjoin_singleton R (c j))

variable (φ) (x : A)

/-- The moment series of `c • x` is the moment series of `x` rescaled by `c`. -/
theorem momentSeries_smul (c : R) : momentSeries φ (c • x) = rescale c (momentSeries φ x) := by
  ext n
  rw [coeff_momentSeries, coeff_rescale, coeff_momentSeries, smul_pow, map_smul, smul_eq_mul]

/-- The free cumulant series of `c • x` is the free cumulant series of `x` rescaled by `c`:
`κ_n(c • x, …, c • x) = c ^ n κ_n(x, …, x)`. -/
theorem freeCumulantSeries_smul (c : R) :
    freeCumulantSeries φ (c • x) = rescale c (freeCumulantSeries φ x) := by
  ext n
  rw [coeff_freeCumulantSeries, coeff_rescale, coeff_freeCumulantSeries,
    ← freeCumulantMultilinear_apply, ← freeCumulantMultilinear_apply,
    (freeCumulantMultilinear φ).map_smul_univ (fun _ => c) fun _ => x, prod_const, card_fin,
    smul_eq_mul]

/-- The R-series of `c • x` is `R_{c • x}(z) = c R_x(c z)`. -/
theorem rSeries_smul (c : R) : rSeries φ (c • x) = c • rescale c (rSeries φ x) := by
  ext n
  rw [← coeff_succ_freeCumulantSeries, freeCumulantSeries_smul, coeff_rescale,
    coeff_succ_freeCumulantSeries, coeff_smul, coeff_rescale, pow_succ', smul_eq_mul, mul_assoc]

variable {φ}

/-- For a normalised `φ`, translating by a scalar adds that scalar to the R-series,
`R_{x + c • 1} = R_x + c`: the mean moves by `c` and the free cumulants of order at least two do
not change. -/
theorem rSeries_add_algebraMap (hφ : φ 1 = 1) (c : R) :
    rSeries φ (x + algebraMap R A c) = rSeries φ x + PowerSeries.C c := by
  ext (_ | n)
  · simp [hφ, Algebra.algebraMap_eq_smul_one]
  · rw [coeff_rSeries, freeCumulant_add_algebraMap φ (fun _ => x) hφ (fun _ => c) (by simp),
      map_add, coeff_rSeries, coeff_succ_C, add_zero]

/-- The R-series of `0` vanishes. -/
@[simp]
theorem rSeries_zero : rSeries φ (0 : A) = 0 := by
  ext n
  rw [coeff_rSeries, ← freeCumulantMultilinear_apply,
    (freeCumulantMultilinear φ).map_coord_zero 0 rfl, map_zero]

/-- For a normalised `φ`, the R-series of the scalar `c • 1` is the constant `c`: its only nonzero
free cumulant is its mean. -/
theorem rSeries_algebraMap (hφ : φ 1 = 1) (c : R) :
    rSeries φ (algebraMap R A c) = PowerSeries.C c := by
  simpa using rSeries_add_algebraMap (φ := φ) 0 hφ c

end Linear

end TauCeti
