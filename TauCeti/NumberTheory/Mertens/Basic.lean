/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.PrimeCounting
public import TauCeti.NumberTheory.LFunctions.Mertens
import TauCeti.Analysis.Asymptotics.Lemmas
import TauCeti.NumberTheory.NumberField.DedekindZeta
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Mertens's second and third theorems over the rationals

Specializing the number-field Mertens theorems of `TauCeti.NumberTheory.LFunctions.Mertens` to
`ℚ` and transporting prime ideals of `𝓞 ℚ` to rational primes via
`Rat.HeightOneSpectrum.primesEquiv` yields the classical rational Mertens estimates on
`Nat.primesLE ⌊x⌋₊`:

* **Meissel–Mertens constant** (`TauCeti.meisselMertensConstant`): the constant
  `M = lim_{x → ∞} (∑_{p ≤ x} 1 / p - log log x)`, with closed form
  `M = γ + ∑_p (log (1 - 1 / p) + 1 / p) < γ`.
* **Mertens's second theorem**: `∑_{p ≤ x} 1 / p = log log x + M + O(1 / log x)`, uniformly bounded
  by `C / log x` on `1 < x`.
* **Logarithmic Euler product**: `∑_{p ≤ x} -log (1 - 1 / p) = log log x + γ + O(1 / log x)`,
  uniformly bounded by `C / log x` on `1 < x`.
* **Mertens's third theorem**: `∏_{p ≤ x} (1 - 1 / p)⁻¹ = e^γ log x + O(1)` (uniformly on `1 ≤ x`),
  together with the asymptotic limits `∏_{p ≤ x} (1 - 1 / p)⁻¹ / log x → e^γ` and
  `∏_{p ≤ x} (1 - 1 / p) * log x → e^(-γ)`.
* **Two-sided Euler-product comparison with finite prime deletion**: for any finite set
  `S : Finset ℕ`, there exist positive constants `c₁, c₂ > 0` such that for all `x ≥ 2`,
  `c₁ / log x ≤ ∏_{p ≤ x, p ∉ S} (1 - 1 / p) ≤ c₂ / log x`, and reciprocally
  `c₁ * log x ≤ ∏_{p ≤ x, p ∉ S} (1 - 1 / p)⁻¹ ≤ c₂ * log x`.

## Main definitions and results

* `TauCeti.meisselMertensConstant` and `TauCeti.LFunctions.mertensConstant_rat`: the
  Meissel–Mertens constant `M` as the rational specialization `mertensConstant ℚ`.
* `TauCeti.meisselMertensConstant_eq`: `M = γ + ∑_p (log (1 - 1 / p) + 1 / p)`.
* `TauCeti.meisselMertensConstant_lt_eulerMascheroniConstant`: `M < γ`.
* `TauCeti.isBigO_sum_primesLE_inv_sub_log_log_sub`,
  `TauCeti.tendsto_sum_primesLE_inv_sub_log_log`, and
  `TauCeti.exists_abs_sum_primesLE_inv_sub_log_log_sub_le`: Mertens's second theorem.
* `TauCeti.isBigO_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub`,
  `TauCeti.tendsto_sum_primesLE_neg_log_one_sub_inv_sub_log_log`, and
  `TauCeti.exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le`: logarithmic Euler
  product over primes up to `x`.
* `TauCeti.isBigO_prod_primesLE_one_sub_inv_inv_sub_exp_eulerMascheroniConstant_mul_log`,
  `TauCeti.exists_abs_prod_primesLE_one_sub_inv_inv_sub_exp_eulerMascheroniConstant_mul_log_le`,
  `TauCeti.tendsto_prod_primesLE_one_sub_inv_inv_div_log`, and
  `TauCeti.tendsto_prod_primesLE_one_sub_inv_mul_log`: Mertens's third theorem.
* `TauCeti.exists_pos_mul_inv_log_le_prod_primesLE_one_sub_inv_le`,
  `TauCeti.exists_pos_mul_inv_log_le_prod_primesLE_filter_notMem_one_sub_inv_le`, and
  `TauCeti.exists_pos_mul_log_le_prod_primesLE_filter_notMem_one_sub_inv_inv_le`: two-sided
  Euler-product comparison on `2 ≤ x`.

## References

* F. Mertens, *Ein Beitrag zur analytischen Zahlentheorie*, J. Reine Angew. Math. 78 (1874),
  46–62.
* G. H. Hardy and E. M. Wright, *An Introduction to the Theory of Numbers*, 6th ed., §§22.7–22.8,
  Theorems 428 and 429.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, 3rd ed., Chapter I.1,
  Theorems 1.8 and 1.12.
-/

public section

open Asymptotics Filter IsDedekindDomain NumberField
open scoped NumberField Topology

namespace TauCeti

/-! ### Transport between `HeightOneSpectrum (𝓞 ℚ)` and rational primes -/

/-- On `𝓞 ℚ`, a height-one prime ideal is uniquely determined by its absolute norm. -/
theorem absNorm_asIdeal_rat_injective :
    Function.Injective fun v : HeightOneSpectrum (𝓞 ℚ) ↦ Ideal.absNorm v.asIdeal := by
  intro v w h
  dsimp only at h
  rw [Rat.HeightOneSpectrum.absNorm_asIdeal, Rat.HeightOneSpectrum.absNorm_asIdeal] at h
  exact Rat.HeightOneSpectrum.primesEquiv.injective (Subtype.ext h)

/-- The norms of the height-one primes of `𝓞 ℚ` bounded by `x` are the rational primes `p ≤ ⌊x⌋₊`.
For `x < 2` both sides are empty. -/
theorem image_absNorm_primesLE_rat (x : ℝ) :
    (primesLE ℚ x).image (fun v ↦ Ideal.absNorm v.asIdeal) = Nat.primesLE ⌊x⌋₊ := by
  ext p
  simp only [Finset.mem_image, mem_normLE, Nat.mem_primesLE]
  constructor
  · rintro ⟨v, hvx, rfl⟩
    exact ⟨Nat.le_floor hvx,
      (Rat.HeightOneSpectrum.absNorm_asIdeal v).symm ▸ Rat.HeightOneSpectrum.prime_natGenerator v⟩
  · rintro ⟨hpx, hp⟩
    obtain ⟨v, rfl⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq hp
    exact ⟨v, (Nat.le_floor_iff' hp.ne_zero).mp hpx, rfl⟩

/-- A product over `primesLE ℚ x` depending only on the absolute norm equals the corresponding
product over `Nat.primesLE ⌊x⌋₊`. -/
@[to_additive /-- A sum over `primesLE ℚ x` depending only on the absolute norm equals the
corresponding sum over `Nat.primesLE ⌊x⌋₊`. -/]
theorem prod_primesLE_rat_eq_prod_primesLE {M : Type*} [CommMonoid M] (f : ℕ → M) (x : ℝ) :
    (∏ v ∈ primesLE ℚ x, f (Ideal.absNorm v.asIdeal)) = ∏ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  rw [← image_absNorm_primesLE_rat,
    Finset.prod_image fun _ _ _ _ h ↦ absNorm_asIdeal_rat_injective h]

/-- The prime summatory function over `ℚ` of a function of the ideal norm is the finite sum over
rational primes `p ≤ ⌊x⌋₊`. -/
theorem primeSummatory_rat_eq_sum_primesLE (f : ℕ → ℝ) (x : ℝ) :
    primeSummatory ℚ (fun v ↦ f (Ideal.absNorm v.asIdeal)) x = ∑ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  rw [primeSummatory_apply, sum_primesLE_rat_eq_sum_primesLE]

/-- A `finprod` over `HeightOneSpectrum (𝓞 ℚ)` truncated at norm `x` equals the finite product over
`Nat.primesLE ⌊x⌋₊`. -/
theorem finprod_heightOneSpectrum_rat_ite_absNorm_le_eq_prod_primesLE {M : Type*} [CommMonoid M]
    (f : ℕ → M) (x : ℝ) :
    (∏ᶠ v : HeightOneSpectrum (𝓞 ℚ),
        if (Ideal.absNorm v.asIdeal : ℝ) ≤ x then f (Ideal.absNorm v.asIdeal) else 1) =
      ∏ p ∈ Nat.primesLE ⌊x⌋₊, f p := by
  rw [finprod_eq_prod_of_mulSupport_subset (s := primesLE ℚ x),
    ← prod_primesLE_rat_eq_prod_primesLE]
  · exact Finset.prod_congr rfl fun v hv ↦
      ite_eq_left ((mem_normLE fun w : HeightOneSpectrum (𝓞 ℚ) ↦ Ideal.absNorm w.asIdeal).mp hv)
  · intro v hv
    rw [Finset.mem_coe, mem_normLE]
    by_contra hvx
    exact hv (ite_eq_right hvx)

/-! ### Uniform `C / log x` passage on `(1, ∞)` -/

/-- **Uniform `C / log x` bound on `(1, ∞)` from an eventual `O(1 / log x)` Mertens estimate.**
On a bounded interval `(1, B]`, the step function `g ⌊x⌋₊` takes at most `B + 1` values while
`|log (log x)| * log x` stays bounded near `1⁺` because `|log u| ≤ u + u⁻¹` for `u > 0`. -/
theorem exists_abs_comp_natFloor_sub_log_log_sub_le {g : ℕ → ℝ} {A : ℝ}
    (hO : (fun x : ℝ ↦ g ⌊x⌋₊ - Real.log (Real.log x) - A) =O[atTop] fun x ↦ (Real.log x)⁻¹) :
    ∃ C, 0 ≤ C ∧ ∀ x, 1 < x → |g ⌊x⌋₊ - Real.log (Real.log x) - A| ≤ C / Real.log x := by
  obtain ⟨c₀, hc₀, hbound⟩ := hO.exists_nonneg
  obtain ⟨b, hb⟩ := eventually_atTop.mp hbound.bound
  set B : ℕ := max 2 ⌈b⌉₊
  have hbB : b ≤ B := (Nat.le_ceil b).trans (by exact_mod_cast le_max_right 2 ⌈b⌉₊)
  set M : ℝ := ∑ k ∈ Finset.Icc 0 B, |g k|
  have hM0 : 0 ≤ M := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
  set C₁ : ℝ := (M + |A|) * Real.log B + (Real.log B ^ 2 + 1)
  refine ⟨max c₀ C₁, hc₀.trans (le_max_left _ _), fun x hx1 ↦ ?_⟩
  have hx0 : 0 < x := zero_lt_one.trans hx1
  have hu : 0 < Real.log x := Real.log_pos hx1
  rcases le_or_gt (B : ℝ) x with hBx | hxB
  · have h := hb x (hbB.trans hBx)
    rw [Real.norm_eq_abs, Real.norm_of_nonneg (inv_nonneg.mpr hu.le), ← div_eq_mul_inv] at h
    exact h.trans (div_le_div_of_nonneg_right (le_max_left _ _) hu.le)
  · have hfloor : ⌊x⌋₊ ∈ Finset.Icc 0 B :=
      Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.floor_le_of_le hxB.le⟩
    have hgM : |g ⌊x⌋₊| ≤ M :=
      Finset.single_le_sum (f := fun k ↦ |g k|) (fun _ _ ↦ abs_nonneg _) hfloor
    have huB : Real.log x ≤ Real.log B := Real.log_le_log hx0 hxB.le
    have hlogu : |Real.log (Real.log x)| ≤ Real.log x + (Real.log x)⁻¹ := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · have hinv := Real.log_le_sub_one_of_pos (inv_pos.mpr hu)
        rw [Real.log_inv] at hinv
        linarith
      · linarith [Real.log_le_sub_one_of_pos hu, inv_pos.mpr hu]
    have htri : |g ⌊x⌋₊ - Real.log (Real.log x) - A| ≤
        (|g ⌊x⌋₊| + |A|) + |Real.log (Real.log x)| := by
      linarith [abs_sub (g ⌊x⌋₊ - Real.log (Real.log x)) A,
        abs_sub (g ⌊x⌋₊) (Real.log (Real.log x))]
    rw [le_div_iff₀ hu]
    calc |g ⌊x⌋₊ - Real.log (Real.log x) - A| * Real.log x
        ≤ ((|g ⌊x⌋₊| + |A|) + (Real.log x + (Real.log x)⁻¹)) * Real.log x :=
          mul_le_mul_of_nonneg_right (htri.trans (add_le_add le_rfl hlogu)) hu.le
      _ = (|g ⌊x⌋₊| + |A|) * Real.log x + (Real.log x ^ 2 + (Real.log x)⁻¹ * Real.log x) := by
          ring
      _ = (|g ⌊x⌋₊| + |A|) * Real.log x + (Real.log x ^ 2 + 1) := by
          rw [inv_mul_cancel₀ hu.ne']
      _ ≤ (M + |A|) * Real.log B + (Real.log B ^ 2 + 1) := add_le_add
          (mul_le_mul (add_le_add hgM le_rfl) huB hu.le (add_nonneg hM0 (abs_nonneg A)))
          (add_le_add (pow_le_pow_left₀ hu.le huB 2) le_rfl)
      _ ≤ max c₀ C₁ := le_max_right _ _

/-! ### The Meissel–Mertens constant and Mertens's second theorem -/

/-- **The Meissel–Mertens constant** `M = lim_{x → ∞} (∑_{p ≤ x} 1 / p - log log x)`, defined as
the rational specialization `TauCeti.LFunctions.mertensConstant ℚ`. -/
noncomputable def meisselMertensConstant : ℝ :=
  LFunctions.mertensConstant ℚ

/-- Over `ℚ`, `TauCeti.LFunctions.mertensConstant` specializes to
`TauCeti.meisselMertensConstant`. -/
@[simp]
theorem LFunctions.mertensConstant_rat :
    LFunctions.mertensConstant ℚ = meisselMertensConstant := by
  rfl

/-- The prime series `∑_p (log (1 - 1 / p) + 1 / p)` is summable. -/
theorem summable_log_one_sub_inv_add_inv_primes :
    Summable fun p : Nat.Primes ↦ Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹ := by
  rw [← (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).summable_iff]
  refine (LFunctions.summable_log_one_sub_inv_absNorm_add_inv_absNorm ℚ).congr fun v ↦ ?_
  simp only [Function.comp_apply, Rat.HeightOneSpectrum.absNorm_asIdeal]
  rfl

/-- **Closed form of the Meissel–Mertens constant** (Mertens, 1874; Hardy & Wright, Theorem 428):
`M = γ + ∑_p (log (1 - 1 / p) + 1 / p)`, where `γ` is the Euler–Mascheroni constant. -/
theorem meisselMertensConstant_eq :
    meisselMertensConstant = Real.eulerMascheroniConstant +
      ∑' p : Nat.Primes, (Real.log (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹) := by
  rw [← LFunctions.mertensConstant_rat, LFunctions.mertensConstant_eq,
    dedekindZeta_residue_rat, Real.log_one, add_zero,
    ← (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).tsum_eq]
  congr 1
  refine tsum_congr fun v ↦ ?_
  rw [Rat.HeightOneSpectrum.absNorm_asIdeal]
  rfl

/-- The Meissel–Mertens constant is strictly smaller than the Euler–Mascheroni constant `γ`. -/
theorem meisselMertensConstant_lt_eulerMascheroniConstant :
    meisselMertensConstant < Real.eulerMascheroniConstant := by
  simpa using LFunctions.mertensConstant_lt_eulerMascheroniConstant_add_log_dedekindZeta_residue ℚ

/-- **Mertens's second theorem** (Mertens, 1874; Tenenbaum, Theorem I.1.8):
`∑_{p ≤ x} 1 / p = log log x + M + O(1 / log x)` as `x → ∞`, where `M` is
`TauCeti.meisselMertensConstant`. -/
theorem isBigO_sum_primesLE_inv_sub_log_log_sub :
    (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) -
      Real.log (Real.log x) - meisselMertensConstant) =O[atTop] fun x ↦ (Real.log x)⁻¹ := by
  refine (LFunctions.isBigO_primeSummatory_inv_absNorm_sub_log_log_sub_mertensConstant
    ℚ).congr_left fun x ↦ ?_
  rw [primeSummatory_rat_eq_sum_primesLE (fun p : ℕ ↦ (p : ℝ)⁻¹) x, LFunctions.mertensConstant_rat]

/-- **Mertens's second theorem, limit form**: `∑_{p ≤ x} 1 / p - log log x` tends to
`TauCeti.meisselMertensConstant` as `x → ∞`. -/
theorem tendsto_sum_primesLE_inv_sub_log_log :
    Tendsto (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) - Real.log (Real.log x))
      atTop (𝓝 meisselMertensConstant) := by
  rw [← LFunctions.mertensConstant_rat]
  refine (LFunctions.tendsto_primeSummatory_inv_absNorm_sub_log_log ℚ).congr fun x ↦ ?_
  rw [primeSummatory_rat_eq_sum_primesLE (fun p : ℕ ↦ (p : ℝ)⁻¹) x]

/-- **Mertens's second theorem, uniform form on `(1, ∞)`**: there exists `C ≥ 0` such that
`|(∑_{p ≤ x} 1 / p) - log log x - M| ≤ C / log x` for all `x > 1`. -/
theorem exists_abs_sum_primesLE_inv_sub_log_log_sub_le :
    ∃ C, 0 ≤ C ∧ ∀ x, 1 < x →
      |(∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹) - Real.log (Real.log x) -
        meisselMertensConstant| ≤ C / Real.log x :=
  exists_abs_comp_natFloor_sub_log_log_sub_le
    (g := fun n ↦ ∑ p ∈ Nat.primesLE n, (p : ℝ)⁻¹) isBigO_sum_primesLE_inv_sub_log_log_sub

/-! ### Logarithmic Euler product and Mertens's third theorem -/

/-- **Logarithmic form of Mertens's third theorem**:
`∑_{p ≤ x} -log (1 - 1 / p) = log log x + γ + O(1 / log x)` as `x → ∞`. -/
theorem isBigO_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub :
    (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
      Real.log (Real.log x) - Real.eulerMascheroniConstant) =O[atTop]
      fun x ↦ (Real.log x)⁻¹ := by
  have h := LFunctions.isBigO_primeSummatory_neg_log_one_sub_inv_absNorm_sub_log_log_sub ℚ
  rw [dedekindZeta_residue_rat, Real.log_one, add_zero] at h
  exact h.congr_left fun x ↦ by
    rw [primeSummatory_rat_eq_sum_primesLE (fun p : ℕ ↦ -Real.log (1 - (p : ℝ)⁻¹)) x]

/-- **Logarithmic form of Mertens's third theorem, limit form**:
`∑_{p ≤ x} -log (1 - 1 / p) - log log x` tends to `γ` as `x → ∞`. -/
theorem tendsto_sum_primesLE_neg_log_one_sub_inv_sub_log_log :
    Tendsto (fun x : ℝ ↦ (∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) -
      Real.log (Real.log x)) atTop (𝓝 Real.eulerMascheroniConstant) := by
  have h := LFunctions.tendsto_primeSummatory_neg_log_one_sub_inv_absNorm_sub_log_log ℚ
  rw [dedekindZeta_residue_rat, Real.log_one, add_zero] at h
  exact h.congr fun x ↦ by
    rw [primeSummatory_rat_eq_sum_primesLE (fun p : ℕ ↦ -Real.log (1 - (p : ℝ)⁻¹)) x]

/-- **Logarithmic form of Mertens's third theorem, uniform on `(1, ∞)`**: there exists `C ≥ 0`
such that `|(∑_{p ≤ x} -log (1 - 1 / p)) - log log x - γ| ≤ C / log x` for all `x > 1`. -/
theorem exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le :
    ∃ C, 0 ≤ C ∧ ∀ x, 1 < x →
      |(∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) - Real.log (Real.log x) -
        Real.eulerMascheroniConstant| ≤ C / Real.log x :=
  exists_abs_comp_natFloor_sub_log_log_sub_le
    (g := fun n ↦ ∑ p ∈ Nat.primesLE n, -Real.log (1 - (p : ℝ)⁻¹))
    isBigO_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub

/-- **Mertens's third theorem with additive `O(1)` error** (Mertens, 1874; Tenenbaum,
Theorem I.1.12): `∏_{p ≤ x} (1 - 1 / p)⁻¹ = e^γ log x + O(1)` as `x → ∞`. -/
theorem isBigO_prod_primesLE_one_sub_inv_inv_sub_exp_eulerMascheroniConstant_mul_log :
    (fun x : ℝ ↦ (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) -
      Real.exp Real.eulerMascheroniConstant * Real.log x) =O[atTop] fun _ ↦ (1 : ℝ) := by
  have h := LFunctions.isBigO_prod_one_sub_inv_absNorm_sub_mul_log ℚ
  rw [dedekindZeta_residue_rat, mul_one] at h
  exact h.congr_left fun x ↦ by
    rw [finprod_heightOneSpectrum_rat_ite_absNorm_le_eq_prod_primesLE
      (fun p : ℕ ↦ (1 - (p : ℝ)⁻¹)⁻¹) x]

/-- **Mertens's third theorem, uniform on `[1, ∞)`**: there exists `C ≥ 0` such that
`|(∏_{p ≤ x} (1 - 1 / p)⁻¹) - e^γ log x| ≤ C` for all `x ≥ 1`. -/
theorem exists_abs_prod_primesLE_one_sub_inv_inv_sub_exp_eulerMascheroniConstant_mul_log_le :
    ∃ C, 0 ≤ C ∧ ∀ x, 1 ≤ x →
      |(∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) -
        Real.exp Real.eulerMascheroniConstant * Real.log x| ≤ C := by
  set P : ℝ → ℝ := fun x ↦ ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹
  have hfac (p : ℕ) (hp : p.Prime) : 1 ≤ (1 - (p : ℝ)⁻¹)⁻¹ :=
    (one_le_inv₀ (sub_pos.mpr (inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)))).mpr
      (sub_le_self _ (by positivity))
  have hP0 (x : ℝ) : 0 ≤ P x :=
    Finset.prod_nonneg fun p hp ↦ zero_le_one.trans (hfac p (Nat.prime_of_mem_primesLE hp))
  have hPmono : Monotone P := fun x y hxy ↦ Finset.prod_le_prod_of_subset_of_one_le₀
    (Nat.primesLE_mono (Nat.floor_mono hxy))
    (fun p hp ↦ zero_le_one.trans (hfac p (Nat.prime_of_mem_primesLE hp)))
    fun p hp _ ↦ hfac p (Nat.prime_of_mem_primesLE hp)
  have hO := IsBigO.isBigO_principal_Ici
    isBigO_prod_primesLE_one_sub_inv_inv_sub_exp_eulerMascheroniConstant_mul_log
    (a := 1) zero_lt_one (fun _ _ ↦ by simp) fun Y ↦
        ⟨P (max 1 Y) + Real.exp Real.eulerMascheroniConstant * Real.log (max 1 Y), fun x hx ↦ by
          have hxY : x ≤ max 1 Y := hx.2.trans (le_max_right 1 Y)
          have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx.1
          have hlogY : Real.log x ≤ Real.log (max 1 Y) :=
            Real.log_le_log (zero_lt_one.trans_le hx.1) hxY
          rw [Real.norm_eq_abs, abs_le]
          constructor <;> nlinarith [hPmono hxY, hP0 x, hP0 (max 1 Y),
            Real.exp_pos Real.eulerMascheroniConstant]⟩
  obtain ⟨C, hC0, hC⟩ := hO.exists_nonneg
  refine ⟨C, hC0, fun x hx ↦ ?_⟩
  have h := isBigOWith_principal.mp hC x hx
  rwa [Real.norm_eq_abs, norm_one, mul_one] at h

/-- **Mertens's third theorem, ratio form** (Hardy & Wright, Theorem 429):
`(∏_{p ≤ x} (1 - 1 / p)⁻¹) / log x → e^γ` as `x → ∞`. -/
theorem tendsto_prod_primesLE_one_sub_inv_inv_div_log :
    Tendsto (fun x : ℝ ↦ (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)⁻¹) / Real.log x)
      atTop (𝓝 (Real.exp Real.eulerMascheroniConstant)) := by
  have h := (LFunctions.tendsto_prod_one_sub_inv_absNorm_div_log ℚ).const_mul
    (Real.exp Real.eulerMascheroniConstant)
  rw [dedekindZeta_residue_rat, mul_one] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hlog : Real.log x ≠ 0 := (Real.log_pos hx).ne'
  have hexp : Real.exp Real.eulerMascheroniConstant ≠ 0 := (Real.exp_pos _).ne'
  rw [finprod_heightOneSpectrum_rat_ite_absNorm_le_eq_prod_primesLE
    (fun p : ℕ ↦ (1 - (p : ℝ)⁻¹)⁻¹) x]
  field_simp

/-- **Mertens's third theorem, sieve product form**:
`(∏_{p ≤ x} (1 - 1 / p)) * log x → e^(-γ)` as `x → ∞`. -/
theorem tendsto_prod_primesLE_one_sub_inv_mul_log :
    Tendsto (fun x : ℝ ↦ (∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹)) * Real.log x)
      atTop (𝓝 (Real.exp (-Real.eulerMascheroniConstant))) := by
  rw [Real.exp_neg]
  refine (tendsto_prod_primesLE_one_sub_inv_inv_div_log.inv₀
    (Real.exp_pos _).ne').congr fun x ↦ ?_
  rw [inv_div, div_eq_inv_mul, ← Finset.prod_inv_distrib]
  simp_rw [inv_inv]

/-! ### Two-sided Euler-product comparison on `[2, ∞)` -/

/-- **Two-sided Mertens comparison for `∏_{p ≤ x} (1 - 1 / p)` on `2 ≤ x`.** There exist positive
constants `c₁, c₂ > 0` such that `c₁ / log x ≤ ∏_{p ≤ x} (1 - 1 / p) ≤ c₂ / log x` for all
`x ≥ 2`. -/
theorem exists_pos_mul_inv_log_le_prod_primesLE_one_sub_inv_le :
    ∃ c₁ > 0, ∃ c₂ > 0, ∀ x, 2 ≤ x →
      c₁ / Real.log x ≤ ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) ∧
        ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) ≤ c₂ / Real.log x := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_sum_primesLE_neg_log_one_sub_inv_sub_log_log_sub_le
  set B : ℝ := C / Real.log 2
  refine ⟨Real.exp (-Real.eulerMascheroniConstant - B), Real.exp_pos _,
    Real.exp (-Real.eulerMascheroniConstant + B), Real.exp_pos _, fun x hx2 ↦ ?_⟩
  have hx1 : 1 < x := one_lt_two.trans_le hx2
  have hlogx : 0 < Real.log x := Real.log_pos hx1
  have herr : |(∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) - Real.log (Real.log x) -
      Real.eulerMascheroniConstant| ≤ B :=
    (hC x hx1).trans
      (div_le_div_of_nonneg_left hC0 (Real.log_pos one_lt_two) (Real.log_le_log zero_lt_two hx2))
  have hexp_prod : ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) =
      Real.exp (-∑ p ∈ Nat.primesLE ⌊x⌋₊, -Real.log (1 - (p : ℝ)⁻¹)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    have hp1 : (1 : ℝ) < p := mod_cast (Nat.prime_of_mem_primesLE hp).one_lt
    rw [neg_neg, Real.exp_log (sub_pos.mpr (inv_lt_one_of_one_lt₀ hp1))]
  constructor
  · rw [div_eq_mul_inv, ← Real.exp_log hlogx, ← Real.exp_neg, ← Real.exp_add, hexp_prod]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp herr).2])
  · rw [div_eq_mul_inv, ← Real.exp_log hlogx, ← Real.exp_neg, ← Real.exp_add, hexp_prod]
    exact Real.exp_le_exp.mpr (by linarith [(abs_le.mp herr).1])

/-- **Two-sided Mertens comparison with finite prime deletion.** For every finite set
`S : Finset ℕ`, there exist positive constants `c₁, c₂ > 0` such that
`c₁ / log x ≤ ∏_{p ≤ x, p ∉ S} (1 - 1 / p) ≤ c₂ / log x` for all `x ≥ 2`. Elements of `S` need
not be prime; this directly controls sieve Euler products with primes dividing a modulus omitted. -/
theorem exists_pos_mul_inv_log_le_prod_primesLE_filter_notMem_one_sub_inv_le (S : Finset ℕ) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∀ x, 2 ≤ x →
      c₁ / Real.log x ≤ ∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∉ S, (1 - (p : ℝ)⁻¹) ∧
        ∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∉ S, (1 - (p : ℝ)⁻¹) ≤ c₂ / Real.log x := by
  obtain ⟨c₁, hc₁, c₂, hc₂, hfull⟩ := exists_pos_mul_inv_log_le_prod_primesLE_one_sub_inv_le
  set D : ℝ := ∏ p ∈ S with p.Prime, (1 - (p : ℝ)⁻¹)⁻¹
  have hfac_pos (p : ℕ) (hp : p.Prime) : 0 < 1 - (p : ℝ)⁻¹ :=
    sub_pos.mpr (inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt))
  have hfac_inv_ge (p : ℕ) (hp : p.Prime) : 1 ≤ (1 - (p : ℝ)⁻¹)⁻¹ :=
    (one_le_inv₀ (hfac_pos p hp)).mpr (sub_le_self _ (by positivity))
  have hD1 : 1 ≤ D := Finset.one_le_prod₀ fun p hp ↦ hfac_inv_ge p (Finset.mem_filter.mp hp).2
  refine ⟨c₁, hc₁, D * c₂, mul_pos (zero_lt_one.trans_le hD1) hc₂, fun x hx2 ↦ ?_⟩
  obtain ⟨hlo, hhi⟩ := hfull x hx2
  have hsplit := Finset.prod_filter_mul_prod_filter_not (Nat.primesLE ⌊x⌋₊) (· ∈ S)
    fun p ↦ 1 - (p : ℝ)⁻¹
  constructor
  · refine hlo.trans ?_
    rw [← hsplit]
    exact mul_le_of_le_one_left
      (Finset.prod_nonneg fun p hp ↦ (hfac_pos p (Nat.prime_of_mem_primesLE
        (Finset.mem_filter.mp hp).1)).le)
      (Finset.prod_le_one₀ (fun p hp ↦ (hfac_pos p (Nat.prime_of_mem_primesLE
        (Finset.mem_filter.mp hp).1)).le) fun _ _ ↦ sub_le_self _ (by positivity))
  · have hdel : ∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∈ S, (1 - (p : ℝ)⁻¹)⁻¹ ≤ D :=
      Finset.prod_le_prod_of_subset_of_one_le₀
        (fun p hp ↦ Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hp).2,
          Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1⟩)
        (fun p hp ↦ zero_le_one.trans
          (hfac_inv_ge p (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)))
        fun p hp _ ↦ hfac_inv_ge p (Finset.mem_filter.mp hp).2
    have hprod_in_pos : 0 < ∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∈ S, (1 - (p : ℝ)⁻¹) :=
      Finset.prod_pos fun p hp ↦ hfac_pos p
        (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)
    have hfilt_eq : ∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∉ S, (1 - (p : ℝ)⁻¹) =
        (∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∈ S, (1 - (p : ℝ)⁻¹)⁻¹) *
          ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) := by
      rw [Finset.prod_inv_distrib, ← hsplit, inv_mul_cancel_left₀ hprod_in_pos.ne']
    have hfull_nonneg : 0 ≤ ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) :=
      Finset.prod_nonneg fun p hp ↦ (hfac_pos p (Nat.prime_of_mem_primesLE hp)).le
    calc ∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∉ S, (1 - (p : ℝ)⁻¹)
        ≤ D * ∏ p ∈ Nat.primesLE ⌊x⌋₊, (1 - (p : ℝ)⁻¹) := by
          rw [hfilt_eq]
          exact mul_le_mul_of_nonneg_right hdel hfull_nonneg
      _ ≤ D * (c₂ / Real.log x) := mul_le_mul_of_nonneg_left hhi (zero_le_one.trans hD1)
      _ = D * c₂ / Real.log x := (mul_div_assoc _ _ _).symm

/-- **Two-sided Mertens comparison for the reciprocal Euler product with finite deletion.** For
every `S : Finset ℕ`, there exist `c₁, c₂ > 0` such that
`c₁ * log x ≤ ∏_{p ≤ x, p ∉ S} (1 - 1 / p)⁻¹ ≤ c₂ * log x` for all `x ≥ 2`. -/
theorem exists_pos_mul_log_le_prod_primesLE_filter_notMem_one_sub_inv_inv_le (S : Finset ℕ) :
    ∃ c₁ > 0, ∃ c₂ > 0, ∀ x, 2 ≤ x →
      c₁ * Real.log x ≤ ∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∉ S, (1 - (p : ℝ)⁻¹)⁻¹ ∧
        ∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∉ S, (1 - (p : ℝ)⁻¹)⁻¹ ≤ c₂ * Real.log x := by
  obtain ⟨c₁, hc₁, c₂, hc₂, h⟩ :=
    exists_pos_mul_inv_log_le_prod_primesLE_filter_notMem_one_sub_inv_le S
  refine ⟨c₂⁻¹, inv_pos.mpr hc₂, c₁⁻¹, inv_pos.mpr hc₁, fun x hx2 ↦ ?_⟩
  obtain ⟨hlo, hhi⟩ := h x hx2
  have hlogx : 0 < Real.log x := Real.log_pos (one_lt_two.trans_le hx2)
  have hprod_pos : 0 < ∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∉ S, (1 - (p : ℝ)⁻¹) :=
    (div_pos hc₁ hlogx).trans_le hlo
  rw [Finset.prod_inv_distrib]
  constructor
  · calc c₂⁻¹ * Real.log x = (c₂ / Real.log x)⁻¹ := by rw [inv_div, div_eq_inv_mul]
      _ ≤ (∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∉ S, (1 - (p : ℝ)⁻¹))⁻¹ := inv_anti₀ hprod_pos hhi
  · calc (∏ p ∈ Nat.primesLE ⌊x⌋₊ with p ∉ S, (1 - (p : ℝ)⁻¹))⁻¹
        ≤ (c₁ / Real.log x)⁻¹ := inv_anti₀ (div_pos hc₁ hlogx) hlo
      _ = c₁⁻¹ * Real.log x := by rw [inv_div, div_eq_inv_mul]

end TauCeti
