/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.BoxLargeDeviation
public import TauCeti.NumberTheory.Height.House
public import TauCeti.NumberTheory.NumberField.SiegelsLemma
public import TauCeti.RingTheory.IntegralClosure.IsIntegral.Basic
public import TauCeti.RingTheory.MvPolynomial.Box
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex

/-!
# Roth's auxiliary polynomial

Let `α` be an algebraic number of degree `d`, let `b ≥ 1` be an integer with `b α` integral, and
let `ε ≥ 0`. If the number `n` of variables satisfies `2 d ≤ exp (ε² n / 2)`, then for all
positive integers `r₁, …, rₙ` there is a nonzero `P ∈ ℤ[X₁, …, Xₙ]` with `deg_{Xᵢ} P ≤ rᵢ`,
whose index at the diagonal point `(α, …, α)` with weights `r` is at least `(n / 2) (1 - ε)`,
and whose coefficients are bounded in absolute value by `C ^ (r₁ + ⋯ + rₙ)`, where
`C = 12 b max(1, ⌈α⌉)` and `⌈α⌉` is the house of `α`.

This is the auxiliary polynomial in the proof of Roth's theorem. It vanishes to high index at
`(α, …, α)`; evaluated at a tuple of very good rational approximations of `α`, a suitable Hasse
derivative of it is a nonzero rational number which is too small to have the denominator forced
by the coefficients, unless the approximations have bounded height.

The coefficients of `P` are the `∏ᵢ (rᵢ + 1)` unknowns. Index at least `(n / 2) (1 - ε)` means
that the jets `∂^d P (α, …, α)` vanish for every `d` in the box `∏ᵢ {0, …, rᵢ}` with
`∑ᵢ dᵢ / rᵢ < (n / 2) (1 - ε)`; the other jets vanish because of the degree bounds. After
multiplication by `b ^ (r₁ + ⋯ + rₙ)` these are linear equations with coefficients in the ring
of integers of `ℚ(α)`. By `TauCeti.card_filter_sum_div_le_mul_one_sub_le` there are at most
`∏ᵢ (rᵢ + 1) exp (-ε² n / 2)` of them, so `d` times their number is at most half the number of
unknowns, and Siegel's lemma `NumberField.exists_ne_zero_int_vec_abs_le_of_house_le` gives a
small nonzero integer solution.

## Main results

* `TauCeti.exists_roth_auxiliary_polynomial`: Roth's auxiliary polynomial, for an element `α`
  of any field of characteristic zero.

## Implementation notes

Pottmeyer assumes `0 < ε < 1` and `exp (ε² n / 4) ≥ 2 d`. The counting estimate used here has
the exponent `ε² n / 2`, so the weaker hypothesis `exp (ε² n / 2) ≥ 2 d` suffices, and no upper
bound on `ε` is needed.

## References

* L. Pottmeyer, [*Diophantine Approximation*](https://esaga.uni-due.de/f/lukas.pottmeyer/DioApp.pdf)
  (2022), §2.6, Theorem 2.6.5.
* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 3, Theorem 3.20 (Siegel's
  lemma), and ch. 6, Lemma 6.10 (Thue's one-variable auxiliary polynomials, whose reduction to
  `ℚ(α)` is followed here).
-/

public section

open Finset Module NumberField MvPolynomial Real

open scoped ENNReal

namespace TauCeti

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- Counting the equations: if `2 D ≤ exp (ε² n / 2)`, then `2 D` times the number of points `d`
of the box `∏ᵢ {0, …, rᵢ}` with `∑ᵢ dᵢ / rᵢ ≤ (n / 2) (1 - ε)` is at most the number
`∏ᵢ (rᵢ + 1)` of all points of the box. -/
private theorem two_mul_mul_card_filter_le [DecidableEq ι] {r : ι → ℕ} (hr : ∀ i, r i ≠ 0)
    {ε : ℝ} (hε : 0 ≤ ε) {D : ℝ} (hD : 0 ≤ D) (hDε : 2 * D ≤ exp (ε ^ 2 * Fintype.card ι / 2)) :
    2 * (D * #{d ∈ Fintype.piFinset fun i ↦ range (r i + 1) |
        ∑ i, (d i : ℝ) / r i ≤ Fintype.card ι / 2 * (1 - ε)}) ≤ ∏ i, ((r i : ℝ) + 1) := by
  have hcount := card_filter_sum_div_le_mul_one_sub_le hr hε
  calc 2 * (D * #{d ∈ Fintype.piFinset fun i ↦ range (r i + 1) |
        ∑ i, (d i : ℝ) / r i ≤ Fintype.card ι / 2 * (1 - ε)})
      ≤ 2 * D * ((∏ i, ((r i : ℝ) + 1)) * exp (-(ε ^ 2 * Fintype.card ι / 2))) := by
        rw [← mul_assoc]
        gcongr
    _ = (∏ i, ((r i : ℝ) + 1)) * (2 * D / exp (ε ^ 2 * Fintype.card ι / 2)) := by
        rw [exp_neg]
        ring
    _ ≤ ∏ i, ((r i : ℝ) + 1) := by
        refine mul_le_of_le_one_right (by positivity) ?_
        rwa [div_le_one (exp_pos _)]

/-- The bound of Siegel's lemma for the linear system of Roth's auxiliary polynomial: if
`2 D ≤ N ≤ 2 ^ R` and `R ≥ 1`, then `(3 N (2 b H) ^ R) ^ (D / (N - D)) ≤ (12 b H) ^ R`. -/
private theorem rpow_div_sub_le {N R b : ℕ} {D H : ℝ} (hb : 0 < b) (hH : 1 ≤ H) (hN : 0 < N)
    (hDN : 2 * D ≤ N) (hNR : N ≤ 2 ^ R) (hR : 1 ≤ R) :
    (3 * N * (2 * b * H) ^ R : ℝ) ^ (D / (N - D)) ≤ (12 * b * H) ^ R := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hA : (1 : ℝ) ≤ (2 * b * H) ^ R :=
    one_le_pow₀ (by nlinarith [show (1 : ℝ) ≤ b by exact_mod_cast hb])
  have h1 : (1 : ℝ) ≤ 3 * N * (2 * b * H) ^ R := by nlinarith
  have he : D / (N - D) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  calc (3 * N * (2 * b * H) ^ R : ℝ) ^ (D / (N - D))
      ≤ (3 * N * (2 * b * H) ^ R) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le h1 he
    _ = 3 * N * (2 * b * H) ^ R := rpow_one _
    _ ≤ 3 ^ R * 2 ^ R * (2 * b * H) ^ R := by
        gcongr
        · exact le_self_pow₀ (by norm_num) (by omega)
        · exact_mod_cast hNR
    _ = (12 * b * H) ^ R := by rw [← mul_pow, ← mul_pow]; ring_nf

/-- Roth's auxiliary polynomial over a number field `K`, in which `α` lies. -/
private theorem exists_roth_auxiliary_polynomial_of_numberField [NumberField K] (α : K) {b : ℕ}
    (hb : 0 < b) (hbα : IsIntegral ℤ ((b : K) * α)) {ε : ℝ} (hε : 0 ≤ ε)
    (hn : 2 * (finrank ℚ K : ℝ) ≤ exp (ε ^ 2 * Fintype.card ι / 2)) {r : ι → ℕ}
    (hr : ∀ i, r i ≠ 0) :
    ∃ P : MvPolynomial ι ℤ, P ≠ 0 ∧ (∀ i, P.degreeOf i ≤ r i) ∧
      ENNReal.ofReal (Fintype.card ι / 2 * (1 - ε)) ≤
        weightedIndex r (fun _ ↦ α) (P.map (Int.castRingHom K)) ∧
      ∀ m, |(P.coeff m : ℝ)| ≤ (12 * b * max 1 (NumberField.house α)) ^ ∑ i, r i := by
  -- Set up the linear system over `𝓞 K`, count its equations, solve it with Siegel's lemma,
  -- and read off the polynomial from the solution.
  classical
  set R := ∑ i, r i
  set t : ℝ := Fintype.card ι / 2 * (1 - ε)
  -- The unknowns are indexed by the box `∀ i, Fin (r i + 1)`, the equations by its points `d`
  -- with `∑ᵢ dᵢ / rᵢ ≤ t`.
  set box : Finset (ι → ℕ) := Fintype.piFinset fun i ↦ range (r i + 1)
  set rows : Finset (ι → ℕ) := {d ∈ box | ∑ i, (d i : ℝ) / r i ≤ t}
  have hbox {μ : ι → ℕ} : μ ∈ box ↔ ∀ i, μ i ≤ r i := by
    simp [box]
  have hle (μ : ∀ i, Fin (r i + 1)) (j : ι) : (μ j : ℕ) ≤ r j := Nat.lt_succ_iff.mp (μ j).isLt
  -- The equation for `d`, multiplied by `b ^ R`, has coefficient `e d μ` at the unknown
  -- coefficient of `X ^ μ`.
  let e : rows → (∀ i, Fin (r i + 1)) → K := fun d μ ↦
    hasseDerivRow r (fun _ ↦ α) (Finsupp.equivFunOnFinite.symm d.1) μ * (b : K) ^ R
  have he_eq (d : rows) (μ : ∀ i, Fin (r i + 1)) : e d μ =
      ((∏ j, (μ j : ℕ).choose (d.1 j) : ℕ) : K) *
        ((b : K) ^ R * α ^ ∑ j, ((μ j : ℕ) - d.1 j)) := by
    simp only [e, hasseDerivRow_def, prod_mul_distrib, prod_pow_eq_pow_sum, Nat.cast_prod,
      Finsupp.coe_equivFunOnFinite_symm]
    ring
  have hdeg (d : rows) (μ : ∀ i, Fin (r i + 1)) : ∑ j, ((μ j : ℕ) - d.1 j) ≤ R :=
    sum_le_sum fun j _ ↦ (Nat.sub_le _ _).trans (hle μ j)
  have hchoose (d : rows) (μ : ∀ i, Fin (r i + 1)) : ∏ j, (μ j : ℕ).choose (d.1 j) ≤ 2 ^ R :=
    calc ∏ j, (μ j : ℕ).choose (d.1 j) ≤ ∏ j, 2 ^ (μ j : ℕ) :=
          prod_le_prod fun j _ ↦ Nat.choose_le_two_pow _ _
      _ = 2 ^ ∑ j, (μ j : ℕ) := prod_pow_eq_pow_sum _ _ _
      _ ≤ 2 ^ R := Nat.pow_le_pow_right two_pos (sum_le_sum fun j _ ↦ hle μ j)
  have he (d : rows) (μ : ∀ i, Fin (r i + 1)) : IsIntegral ℤ (e d μ) := by
    rw [he_eq]
    exact (isIntegral_natCast _).mul (isIntegral_natCast_pow_mul_pow hbα (hdeg d μ))
  let a : Matrix rows (∀ i, Fin (r i + 1)) (𝓞 K) := fun d μ ↦ (⟨e d μ, he d μ⟩ : 𝓞 K)
  have hH : 1 ≤ max 1 (NumberField.house α) := le_max_left _ _
  have hA : 1 ≤ (2 * b * max 1 (NumberField.house α) : ℝ) ^ R :=
    one_le_pow₀ (by nlinarith [show (1 : ℝ) ≤ b by exact_mod_cast hb])
  -- The entry `a d μ` coerces to `e d μ` by `RingOfIntegers.map_mk`, which holds by `rfl`.
  have hae (d μ) : (a d μ : K) = e d μ := rfl
  have ha (d μ) : NumberField.house (a d μ : K) ≤ (2 * b * max 1 (NumberField.house α)) ^ R := by
    rw [hae, he_eq]
    exact house_natCast_mul_pow_mul_pow_le α (hchoose d μ) (hdeg d μ)
  have hcardbox : Fintype.card (∀ i, Fin (r i + 1)) = #box := by
    rw [card_piFinset_range]
    simp
  have hN : (Fintype.card (∀ i, Fin (r i + 1)) : ℝ) = ∏ i, ((r i : ℝ) + 1) := by
    rw [hcardbox]
    exact_mod_cast card_piFinset_range r
  have hM : 2 * (finrank ℚ K * Fintype.card rows : ℝ) ≤ Fintype.card (∀ i, Fin (r i + 1)) := by
    rw [hN, Fintype.card_coe]
    exact two_mul_mul_card_filter_le hr hε (Nat.cast_nonneg _) hn
  have hN₀ : 0 < Fintype.card (∀ i, Fin (r i + 1)) := Fintype.card_pos
  have hcard : finrank ℚ K * Fintype.card rows < Fintype.card (∀ i, Fin (r i + 1)) := by
    have : (finrank ℚ K * Fintype.card rows : ℝ) < Fintype.card (∀ i, Fin (r i + 1)) := by
      nlinarith [show (0 : ℝ) < Fintype.card (∀ i, Fin (r i + 1)) by exact_mod_cast hN₀]
    exact_mod_cast this
  obtain ⟨x, hx0, hax, hxle⟩ := exists_ne_zero_int_vec_abs_le_of_house_le a hA hcard ha
  have hR : 1 ≤ R := by
    have hι : Fintype.card ι ≠ 0 := by
      intro hι
      rw [hι] at hn
      norm_num at hn
      linarith [show (1 : ℝ) ≤ finrank ℚ K by exact_mod_cast finrank_pos]
    obtain ⟨i⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero hι)
    exact (Nat.one_le_iff_ne_zero.mpr (hr i)).trans (single_le_sum (by simp) (mem_univ i))
  have hNR : Fintype.card (∀ i, Fin (r i + 1)) ≤ 2 ^ R := by
    rw [hcardbox]
    exact card_piFinset_range_le_two_pow r
  -- The polynomial with coefficient vector `x`.
  set P : MvPolynomial ι ℤ := ofBox r x
  have hPdeg (i : ι) : P.degreeOf i ≤ r i := degreeOf_ofBox_le x i
  have hP0 : P ≠ 0 := fun h ↦ hx0 (ofBox_injective (h.trans (map_zero _).symm))
  refine ⟨P, hP0, hPdeg, ?_, fun m ↦ ?_⟩
  · -- A jet of order `d ≤ r` and weight `< t` is, up to the factor `b ^ R`, the equation `d`.
    refine ofReal_le_weightedIndex_of_eval_hasseDeriv_eq_zero
      (fun i ↦ MvPolynomial.degreeOf_le_iff.mpr fun m hm ↦
        MvPolynomial.degreeOf_le_iff.mp (hPdeg i) m (support_map_subset _ _ hm))
      fun d hdr hdt ↦ ?_
    have hdrow : ⇑d ∈ rows := mem_filter.mpr ⟨hbox.mpr hdr, hdt.le⟩
    -- `(a d μ : K)` is `e d μ` by `hae`.
    have hrow : ∑ μ, e ⟨d, hdrow⟩ μ * (x μ : K) = 0 :=
      sum_mul_intCast_eq_zero_of_mulVec_eq_zero hax ⟨d, hdrow⟩
    have hb' : (b : K) ^ R ≠ 0 := pow_ne_zero _ (by exact_mod_cast hb.ne')
    refine (mul_eq_zero.mp ?_).resolve_left hb'
    rw [← hrow, hasseDeriv_map, eval_map, ← algebraMap_int_eq, ← aeval_def,
      aeval_hasseDeriv_ofBox, mul_sum]
    refine sum_congr rfl fun μ _ ↦ ?_
    simp only [e, Finsupp.equivFunOnFinite_symm_coe, eq_intCast]
    ring
  · by_cases hm : ∀ j, m j ≤ r j
    · obtain ⟨μ, rfl⟩ := exists_boxMonomial_eq hm
      rw [coeff_ofBox]
      exact (hxle _).trans (rpow_div_sub_le hb hH hN₀ (by linarith) hNR hR)
    · rw [coeff_ofBox_of_not_le x hm]
      simp

/-- **Roth's auxiliary polynomial** (Pottmeyer, Theorem 2.6.5). Let `α` be an algebraic number
of degree `d` in a field of characteristic zero, and let `b ≥ 1` be an integer such that `b α` is
integral over `ℤ`. Let `ε ≥ 0` and let `ι` be a finite set of `n` variables with
`2 d ≤ exp (ε² n / 2)`. For all positive integers `rᵢ`, `i ∈ ι`, there is a nonzero
`P ∈ ℤ[Xᵢ : i ∈ ι]` with `deg_{Xᵢ} P ≤ rᵢ`, whose index at `(α, …, α)` with weights `r` is at
least `(n / 2) (1 - ε)`, and whose coefficients have absolute value at most
`(12 b max(1, ⌈α⌉)) ^ (∑ᵢ rᵢ)`, where `⌈α⌉` is the house of `α`. -/
theorem exists_roth_auxiliary_polynomial {F : Type*} [Field F] [CharZero F] {α : F} {b : ℕ}
    (hb : 0 < b) (hbα : IsIntegral ℤ ((b : F) * α)) {ε : ℝ} (hε : 0 ≤ ε)
    (hn : 2 * ((minpoly ℚ α).natDegree : ℝ) ≤ exp (ε ^ 2 * Fintype.card ι / 2)) {r : ι → ℕ}
    (hr : ∀ i, r i ≠ 0) :
    ∃ P : MvPolynomial ι ℤ, P ≠ 0 ∧ (∀ i, P.degreeOf i ≤ r i) ∧
      ENNReal.ofReal (Fintype.card ι / 2 * (1 - ε)) ≤
        weightedIndex r (fun _ ↦ α) (P.map (Int.castRingHom F)) ∧
      ∀ m, |(P.coeff m : ℝ)| ≤ (12 * b * max 1 (house α)) ^ ∑ i, r i := by
  -- Work in the number field `K = ℚ(α)`, of degree `d`.
  obtain ⟨K, _, α', hα', hdK, hbα', hhouse⟩ :=
    exists_numberField_of_isIntegral_natCast_mul hb.ne' hbα
  rw [← hdK] at hn
  obtain ⟨P, hP0, hPdeg, hPind, hPcoeff⟩ :=
    exists_roth_auxiliary_polynomial_of_numberField α' hb hbα' hε hn hr
  refine ⟨P, hP0, hPdeg, ?_, by rwa [hhouse] at hPcoeff⟩
  -- Transport the index from `K` to `F`; both integer casts into `F` agree.
  rw [← weightedIndex_map (algebraMap K F) (algebraMap K F).injective, MvPolynomial.map_map,
    RingHom.ext_int ((algebraMap K F).comp (Int.castRingHom K)) (Int.castRingHom F)] at hPind
  simpa only [hα'] using hPind

end TauCeti
