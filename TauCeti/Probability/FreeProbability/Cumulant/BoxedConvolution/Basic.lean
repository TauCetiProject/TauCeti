/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.NoncrossingPartition.BoxedConvolution
public import TauCeti.Probability.FreeProbability.Cumulant.Kreweras
public import TauCeti.Probability.FreeProbability.Cumulant.Series

/-!
# Boxed convolution of moment and free cumulant series

The boxed convolution `PowerSeries.boxedConvolution` of two formal power series sums, over the
noncrossing partitions `π` of `n` positions, the products of the coefficients of the first series
at the part sizes of `π` and of the second series at the part sizes of its Kreweras complement
`K(π)`. This file identifies the moment and free cumulant series of one variable, for a normalised
functional `φ`, through boxed convolutions:

* the moment series is the boxed convolution of the free cumulant series with the zeta series
  `∑_{n ≥ 0} zⁿ`, which is the moment–cumulant formula `φ (aⁿ) = ∑_{π ∈ NC(n)} κ_π(a)`;
* the free cumulant series is the boxed convolution of the moment series with the Möbius series
  `∑_{n ≥ 0} (-1)^(n-1) C_(n-1) zⁿ`, which is the inverse formula
  `κ_n(a) = ∑_{π ∈ NC(n)} μ(π, 1_n) φ_π(a)` with `μ(π, 1_n) = ∏_{B ∈ K(π)} (-1)^(|B|-1) C_(|B|-1)`;
* for elements `a` and `b` of two different members of a free family of subalgebras, the free
  cumulant series of `a b` is the boxed convolution of the free cumulant series of `a` and `b`,
  and the moment series of `a b` is the boxed convolution of the free cumulant series of `a` with
  the moment series of `b`. These are the one-variable forms of the formulas
  `κ_n(ab, …, ab) = ∑_{π ∈ NC(n)} κ_π(a) κ_{K(π)}(b)` and
  `φ ((ab)ⁿ) = ∑_{π ∈ NC(n)} κ_π(a) φ_{K(π)}(b)`.

No traciality is needed.

## Main results

* `TauCeti.boxedConvolution_freeCumulantSeries_mk_one` — `M_a = C_a ⊠ ζ`.
* `TauCeti.boxedConvolution_momentSeries_mobius` — `C_a = M_a ⊠ μ`.
* `TauCeti.IsFreelyIndependent.freeCumulantSeries_mul` — `C_{ab} = C_a ⊠ C_b` for `a`, `b` in two
  different members of a free family of subalgebras, and
  `TauCeti.IsFreelyIndependentElements.freeCumulantSeries_mul` for free elements.
* `TauCeti.IsFreelyIndependent.momentSeries_mul` — `M_{ab} = C_a ⊠ M_b`, and
  `TauCeti.IsFreelyIndependentElements.momentSeries_mul` for free elements.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Theorem 14.4 and
  Lecture 17 (boxed convolution and the multiplication of free elements).
-/

public section

open Finset PowerSeries

namespace TauCeti

variable {R A : Type*} [CommRing R]

section Monoid

variable [Monoid A] {φ : A → R} (a : A)

/-- *Moments from free cumulants by boxed convolution*: for a normalised `φ`, the moment series
of `a` is the boxed convolution of its free cumulant series with the zeta series
`∑_{n ≥ 0} zⁿ`. -/
theorem boxedConvolution_freeCumulantSeries_mk_one (hφ : φ 1 = 1) :
    (freeCumulantSeries φ a).boxedConvolution (mk 1) = momentSeries φ a :=
  boxedConvolution_mk_one_eq_of_subst_eq (constantCoeff_freeCumulantSeries φ a)
    (freeCumulantSeries_subst_X_mul_momentSeries a hφ)

/-- *Free cumulants from moments by boxed convolution*: for a normalised `φ`, the free cumulant
series of `a` is the boxed convolution of its moment series with the Möbius series
`∑_{n ≥ 0} (-1)^(n-1) C_(n-1) zⁿ`, where `C_k` is the `k`-th Catalan number. -/
theorem boxedConvolution_momentSeries_mobius (hφ : φ 1 = 1) :
    (momentSeries φ a).boxedConvolution (mk fun n => (-1) ^ (n - 1) * (catalan (n - 1) : R)) =
      freeCumulantSeries φ a := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hφ]
  rw [coeff_boxedConvolution hn, coeff_freeCumulantSeries,
    freeCumulant_eq_sum_mu_mul_partitionMoment]
  refine sum_congr rfl fun π _ => ?_
  rw [NoncrossingPartition.mu_top_eq_prod_kreweras, partitionMoment_const, mul_comm]
  simp

end Monoid

section Algebra

variable [Semiring A] [Algebra R A] {φ : A →ₗ[R] R} {ι : Type*}

/-- *Free cumulants of a product of free elements*: if `a ∈ B i` and `b ∈ B j` for `i ≠ j`, with
`B` freely independent for a normalised `φ`, then the free cumulant series of `a b` is the boxed
convolution of the free cumulant series of `a` and of `b`. -/
theorem IsFreelyIndependent.freeCumulantSeries_mul {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ B i) (hb : b ∈ B j) :
    freeCumulantSeries φ (a * b) =
      (freeCumulantSeries φ a).boxedConvolution (freeCumulantSeries φ b) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [coeff_boxedConvolution hn, coeff_freeCumulantSeries,
    h.freeCumulant_mul_eq_sum_partitionCumulant_mul_partitionCumulant hφ hij
      (a := fun _ => a) (b := fun _ => b) (fun _ _ => ha) (fun _ _ => hb)]
  simp only [partitionCumulant_eq_prod_freeCumulant, freeCumulant_const_eq_coeff_freeCumulantSeries]

/-- *Moments of a product of free elements*: if `a ∈ B i` and `b ∈ B j` for `i ≠ j`, with `B`
freely independent for a normalised `φ`, then the moment series of `a b` is the boxed convolution
of the free cumulant series of `a` with the moment series of `b`. -/
theorem IsFreelyIndependent.momentSeries_mul {B : ι → Subalgebra R A}
    (h : IsFreelyIndependent φ B) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ B i) (hb : b ∈ B j) :
    momentSeries φ (a * b) = (freeCumulantSeries φ a).boxedConvolution (momentSeries φ b) := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hφ]
  have key := h.apply_prod_ofFn_mul_eq_sum_partitionCumulant_mul_partitionMoment hφ hij
    (a := fun _ : Fin n => a) (b := fun _ => b) (fun _ => ha) (fun _ => hb)
  rw [List.ofFn_const, List.prod_replicate] at key
  rw [coeff_boxedConvolution hn, coeff_momentSeries, key]
  simp only [partitionCumulant_eq_prod_freeCumulant, freeCumulant_const_eq_coeff_freeCumulantSeries,
    partitionMoment_const, coeff_momentSeries]

/-- *Free cumulants of a product of free elements*: if `c i` and `c j`, for `i ≠ j`, belong to a
freely independent family for a normalised `φ`, then the free cumulant series of `c i * c j` is
the boxed convolution of the free cumulant series of `c i` and of `c j`. -/
theorem IsFreelyIndependentElements.freeCumulantSeries_mul {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) :
    freeCumulantSeries φ (c i * c j) =
      (freeCumulantSeries φ (c i)).boxedConvolution (freeCumulantSeries φ (c j)) :=
  (isFreelyIndependentElements_iff.mp h).freeCumulantSeries_mul hφ hij
    (Algebra.self_mem_adjoin_singleton R _) (Algebra.self_mem_adjoin_singleton R _)

/-- *Moments of a product of free elements*: if `c i` and `c j`, for `i ≠ j`, belong to a freely
independent family for a normalised `φ`, then the moment series of `c i * c j` is the boxed
convolution of the free cumulant series of `c i` with the moment series of `c j`. -/
theorem IsFreelyIndependentElements.momentSeries_mul {c : ι → A}
    (h : IsFreelyIndependentElements φ c) (hφ : φ 1 = 1) {i j : ι} (hij : i ≠ j) :
    momentSeries φ (c i * c j) =
      (freeCumulantSeries φ (c i)).boxedConvolution (momentSeries φ (c j)) :=
  (isFreelyIndependentElements_iff.mp h).momentSeries_mul hφ hij
    (Algebra.self_mem_adjoin_singleton R _) (Algebra.self_mem_adjoin_singleton R _)

end Algebra

end TauCeti
