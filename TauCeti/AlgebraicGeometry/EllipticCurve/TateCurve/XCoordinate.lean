/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Theta.Product
public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Uniformization
import TauCeti.Analysis.Normed.Module.InfiniteSum
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.Data.Int.MulPred
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# The fibres of the first Tate coordinate

Let `K` be a complete non-archimedean field and `q ∈ Kˣ` with `‖q‖ < 1`. Multiplied by the
square of the theta function `θ` of the Tate curve, the first Tate coordinate becomes an entire
Laurent series: `θ(u)² (X(u) + 2 s₁(q))` is a convergent Laurent series on all of `Kˣ ∖ q^ℤ`,
whose coefficients satisfy the degree-two quasi-periodicity recurrence
`a(n + 2) = qⁿ a(n)` (`TauCeti.exists_hasSum_tateTheta_sq_mul_tateUniformizationX`). So do the
coefficients of `θ(a u) θ(a⁻¹ u)` for every unit `a`
(`TauCeti.exists_hasSum_tateTheta_mul_tateTheta`), and of `θ(u)²`. The space of solutions of
this recurrence has dimension two (`TauCeti.finrank_tateThetaCoefficients`), which gives the
classical identity

`θ(a u) θ(a⁻¹ u) = α θ(u)² (X(u) - X(a))`,  `α ≠ 0`,

for `a ∉ q^ℤ` (`TauCeti.exists_tateTheta_mul_tateTheta_eq`). The zeros of `θ` are the powers
of `q`, so `X(u) = X(a)` exactly when `u ∈ a q^ℤ ∪ a⁻¹ q^ℤ`
(`TauCeti.tateUniformizationX_eq_tateUniformizationX_iff`). For the uniformisation map
`Kˣ / q^ℤ → E_q(K)` this says that two parameters with the same image are equal or mutually
inverse, and in the second case the common image is a point of order at most two
(`TauCeti.tateUniformization_eq_tateUniformization_iff`).

The argument works at the level of Laurent coefficients, so it needs no uniqueness theorem for
Laurent expansions of analytic functions, and it applies for every complete non-archimedean
absolute value, discrete or not, in every characteristic. The Laurent expansion of `X` on the
fundamental annulus `‖q‖ < ‖u‖ ≤ 1` includes the unit circle, where the expansion of
`u / (1 - u)²` diverges; the expansion is made there for `(1 - u)² X(u)` instead.

## Main results

* `TauCeti.exists_hasSum_tateTheta_sq_mul_tateUniformizationX`: the Laurent coefficients of
  `θ(u)² (X(u) + 2 s₁(q))` are quasi-periodic of degree two.
* `TauCeti.exists_tateTheta_mul_tateTheta_eq`: `θ(a u) θ(a⁻¹ u) = α θ(u)² (X(u) - X(a))`.
* `TauCeti.tateUniformizationX_eq_tateUniformizationX_iff`: the fibres of `X` are the cosets
  `a^{±1} q^ℤ`.
* `TauCeti.tateUniformization_eq_tateUniformization_iff`: the fibres of the uniformisation map.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
* P. Roquette, *Analytic theory of elliptic functions over local fields*, Hamburger
  Mathematische Einzelschriften (N.F.) 1, Vandenhoeck & Ruprecht (1970).
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, §V.3.
-/

public section

open Filter Topology

namespace TauCeti

variable {K : Type*} [NormedField K]

/-! ### The coefficients of `θ²` -/

section Theta

private theorem hasSum_tateThetaCoeff_one [CompleteSpace K] (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSum (tateThetaCoeff q) 0 := by
  simpa [← tateThetaCoeff_def] using hasSum_tateTheta q 1 hq

private theorem tateThetaCoeff_one_sub (q : Kˣ) (n : ℤ) :
    tateThetaCoeff q (1 - n) = -tateThetaCoeff q n := by
  rw [tateThetaCoeff_def, tateThetaCoeff_def, Int.one_sub_mul_one_sub_sub_one_ediv_two,
    sub_eq_add_neg, zpow_add₀ (neg_ne_zero.mpr one_ne_zero), zpow_one, zpow_neg, ← inv_zpow,
    inv_neg_one]
  ring

private theorem norm_tateThetaCoeff_le_one (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℤ) :
    ‖tateThetaCoeff q n‖ ≤ 1 := by
  rw [tateThetaCoeff_def, norm_mul, norm_zpow, norm_neg, norm_one, one_zpow, one_mul, norm_zpow]
  refine zpow_le_one₀ (norm_pos_iff.mpr q.ne_zero) hq.le (Int.ediv_nonneg ?_ (by norm_num))
  rcases le_or_gt n 0 with h | h <;> nlinarith

/-- The coefficients of `θ²` satisfy `t(-n) = qⁿ t(n)`, reflecting `θ(u⁻¹)² = u⁻² θ(u)²`. -/
private theorem tateThetaProductCoeff_one_neg (q : Kˣ) (n : ℤ) :
    tateThetaProductCoeff q 1 (-n) = (q : K) ^ n * tateThetaProductCoeff q 1 n := by
  rw [← tateThetaProductCoeff_add_two, tateThetaProductCoeff_def, tateThetaProductCoeff_def,
    ← (Equiv.subLeft (1 : ℤ)).tsum_eq (f := fun m ↦ tateThetaCoeff q m * ((1 : Kˣ) : K) ^ m *
      (tateThetaCoeff q (n + 2 - m) * ((1⁻¹ : Kˣ) : K) ^ (n + 2 - m)))]
  congr 1 with m
  simp only [Equiv.subLeft_apply, Units.val_one, one_zpow, inv_one, mul_one]
  rw [show n + 2 - (1 - m) = 1 - (-n - m) by ring, tateThetaCoeff_one_sub,
    tateThetaCoeff_one_sub]
  ring

private theorem tateThetaProductCoeff_one_eq (q : Kˣ) (n : ℤ) :
    tateThetaProductCoeff q 1 n = ∑' m, tateThetaCoeff q m * tateThetaCoeff q (n - m) := by
  simp [tateThetaProductCoeff_def]

variable [CompleteSpace K]

private theorem hasSum_tateThetaProductCoeff_one (q u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSum (fun n ↦ tateThetaProductCoeff q 1 n * (u : K) ^ n) (tateTheta q u ^ 2) := by
  simpa [sq] using hasSum_tateThetaProductCoeff q 1 u hq

private theorem hasSum_tateThetaProductCoeff_one_one (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSum (tateThetaProductCoeff q 1) 0 := by
  simpa using hasSum_tateThetaProductCoeff_one q 1 hq

variable [IsUltrametricDist K]

/-- The first moment `∑ n t(n)` of the coefficients of `θ²` vanishes: it is twice the product
of the first moment of the coefficients of `θ` with `θ(1) = 0`. -/
private theorem hasSum_intCast_mul_tateThetaProductCoeff_one (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSum (fun n : ℤ ↦ (n : K) * tateThetaProductCoeff q 1 n) 0 := by
  have hθ := hasSum_tateThetaCoeff_one q hq
  have hsum (c : ℤ → K) (hc : ∀ m, ‖c m‖ ≤ 1) :
      Summable (fun m ↦ c m * tateThetaCoeff q m) :=
    summable_mul_of_norm_le_one hθ.summable hc
  have hc (n m : ℤ) (k : ℤ) : ‖(k : K) * tateThetaCoeff q (n - m)‖ ≤ 1 := by
    rw [norm_mul]
    calc ‖(k : K)‖ * ‖tateThetaCoeff q (n - m)‖ ≤ 1 * 1 :=
          mul_le_mul (IsUltrametricDist.norm_intCast_le_one K k)
            (norm_tateThetaCoeff_le_one q hq _) (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have hdθ : HasSum (fun n : ℤ ↦ ((n : K) * tateThetaCoeff q n) * (1 : K) ^ n)
      (∑' n : ℤ, (n : K) * tateThetaCoeff q n) := by
    simpa [mul_comm] using (hsum (fun n ↦ (n : K)) fun n ↦
      IsUltrametricDist.norm_intCast_le_one K n).hasSum
  have h := hasSum_laurent_mul one_ne_zero hdθ (by simpa using hθ)
  simp only [mul_zero, one_zpow, mul_one] at h
  convert h.mul_left 2 using 1
  · funext n
    have h₁ := hsum (fun m ↦ (m : K) * tateThetaCoeff q (n - m)) (fun m ↦ hc n m m)
    have h₂ := hsum (fun m ↦ ((n - m : ℤ) : K) * tateThetaCoeff q (n - m)) (fun m ↦ hc n m _)
    have hswap : ∑' m : ℤ, ((n - m : ℤ) : K) * tateThetaCoeff q (n - m) * tateThetaCoeff q m =
        ∑' m : ℤ, (m : K) * tateThetaCoeff q (n - m) * tateThetaCoeff q m := by
      rw [← (Equiv.subLeft n).tsum_eq]
      congr 1 with m
      simp only [Equiv.subLeft_apply, sub_sub_cancel]
      ring
    rw [tateThetaProductCoeff_one_eq, ← tsum_mul_left]
    calc ∑' m : ℤ, (n : K) * (tateThetaCoeff q m * tateThetaCoeff q (n - m))
        = ∑' m : ℤ, ((m : K) * tateThetaCoeff q (n - m) * tateThetaCoeff q m +
            ((n - m : ℤ) : K) * tateThetaCoeff q (n - m) * tateThetaCoeff q m) := by
          congr 1 with m
          push_cast
          ring
      _ = 2 * ∑' m : ℤ, (m : K) * tateThetaCoeff q m * tateThetaCoeff q (n - m) := by
          rw [h₁.tsum_add h₂, hswap, ← two_mul]
          congr 2 with m
          ring
  · ring

end Theta

/-! ### The Laurent coefficients of `θ² (X + 2 s₁)` -/

section XCoeff

/-- The Laurent coefficient `k / (1 - qᵏ)` of `X + 2 s₁` on the annulus `‖q‖ < ‖u‖ < 1`. -/
private noncomputable def xCoeff (q : Kˣ) (k : ℤ) : K := k / (1 - (q : K) ^ k)

/-- The Laurent coefficients of `X(u) + 2 s₁(q) - u / (1 - u)²` on the annulus
`‖q‖ < ‖u‖ < ‖q‖⁻¹`. -/
private noncomputable def yCoeff (q : Kˣ) (k : ℤ) : K :=
  xCoeff q k - if 0 < k then (k : K) else 0

/-- The second difference `x(k) - 2 x(k - 1) + x(k - 2)` of the Laurent coefficients of
`X + 2 s₁`, which are the Laurent coefficients of `(1 - u)² (X(u) + 2 s₁)`. -/
private noncomputable def x2Coeff (q : Kˣ) (k : ℤ) : K :=
  xCoeff q k - 2 * xCoeff q (k - 1) + xCoeff q (k - 2)

private theorem x2Coeff_eq (q : Kˣ) (k : ℤ) :
    x2Coeff q k = yCoeff q k - 2 * yCoeff q (k - 1) + yCoeff q (k - 2) +
      if k = 1 then 1 else 0 := by
  rcases (by omega : k ≤ 0 ∨ k = 1 ∨ k = 2 ∨ 3 ≤ k) with h | rfl | rfl | h
  · have h₁ : ¬ 0 < k := by omega
    have h₂ : ¬ 0 < k - 1 := by omega
    have h₃ : ¬ 0 < k - 2 := by omega
    have h₄ : k ≠ 1 := by omega
    simp only [x2Coeff, yCoeff, h₁, h₂, h₃, h₄, ↓reduceIte]
    ring
  · simp only [x2Coeff, yCoeff]
    norm_num
    ring
  · simp only [x2Coeff, yCoeff]
    norm_num
    ring
  · have h₁ : 0 < k := by omega
    have h₂ : 0 < k - 1 := by omega
    have h₃ : 0 < k - 2 := by omega
    have h₄ : k ≠ 1 := by omega
    simp only [x2Coeff, yCoeff, h₁, h₂, h₃, h₄, ↓reduceIte]
    push_cast
    ring

variable [IsUltrametricDist K]

private theorem norm_xCoeff_le_one {q : Kˣ} (hq : ‖(q : K)‖ < 1) (k : ℤ) : ‖xCoeff q k‖ ≤ 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [xCoeff]
  rw [xCoeff, norm_div]
  exact div_le_one_of_le₀ ((IsUltrametricDist.norm_intCast_le_one K k).trans
    (one_le_norm_one_sub_of_norm_ne_one (norm_zpow_ne_one hq hk))) (norm_nonneg _)

variable [CompleteSpace K]

/-- The coefficients of `θ² (X + 2 s₁)`: the Cauchy product of `k / (1 - qᵏ)` with the
coefficients of `θ²`. -/
private noncomputable def tateXCoeff (q : Kˣ) (n : ℤ) : K :=
  ∑' k, xCoeff q k * tateThetaProductCoeff q 1 (n - k)

private theorem hasSum_xCoeff_mul (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℤ) :
    HasSum (fun k ↦ xCoeff q k * tateThetaProductCoeff q 1 (n - k)) (tateXCoeff q n) := by
  refine (summable_mul_of_norm_le_one ?_ (norm_xCoeff_le_one hq)).hasSum
  exact ((Equiv.subLeft n).summable_iff.mpr (hasSum_tateThetaProductCoeff_one_one q hq).summable)

/-- `∑ₖ k q⁻ᵏ t(n - k) = 0`, by the reflection `t(-j) = qʲ t(j)` and the vanishing of the
zeroth and first moments of `t`. -/
private theorem hasSum_intCast_mul_zpow_neg_mul (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℤ) :
    HasSum (fun k : ℤ ↦ (k : K) * (q : K) ^ (-k) * tateThetaProductCoeff q 1 (n - k)) 0 := by
  rw [← (Equiv.subLeft n).hasSum_iff, ← (Equiv.neg ℤ).hasSum_iff]
  have h := (((hasSum_tateThetaProductCoeff_one_one q hq).mul_left (n : K)).add
    (hasSum_intCast_mul_tateThetaProductCoeff_one q hq)).mul_left ((q : K) ^ (-n))
  simp only [mul_zero, add_zero] at h
  convert h using 1
  funext j
  simp only [Function.comp_apply, Equiv.neg_apply, Equiv.subLeft_apply, sub_neg_eq_add,
    show n - (n + j) = -j by ring, tateThetaProductCoeff_one_neg, zpow_add₀ q.ne_zero, zpow_neg]
  push_cast
  field_simp

private theorem tateXCoeff_add_two (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℤ) :
    tateXCoeff q (n + 2) = (q : K) ^ n * tateXCoeff q n := by
  have h := ((hasSum_xCoeff_mul q hq n).add (hasSum_intCast_mul_zpow_neg_mul q hq n)).mul_left
    ((q : K) ^ n)
  rw [add_zero] at h
  refine (hasSum_xCoeff_mul q hq (n + 2)).unique (h.congr_fun fun k ↦ ?_)
  rw [show n + 2 - k = n - k + 2 by ring, tateThetaProductCoeff_add_two]
  rcases eq_or_ne k 0 with rfl | hk
  · simp [xCoeff]
  have h₁ := one_sub_zpow_ne_zero hq hk
  simp only [xCoeff, zpow_sub₀ q.ne_zero, zpow_neg]
  field_simp
  ring

private theorem tateXCoeff_mem (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    tateXCoeff q ∈ tateThetaCoefficients q 1 2 := by
  rw [mem_tateThetaCoefficients_iff]
  intro n
  simp [tateXCoeff_add_two q hq]

end XCoeff

/-! ### The Laurent expansion of `θ(u)² (X(u) + 2 s₁)` -/

section Expansion

variable [IsUltrametricDist K] [CompleteSpace K]

private theorem hasSum_yCoeff (q u : Kˣ) (hq : ‖(q : K)‖ < 1) (hu₁ : ‖(q : K) * u‖ < 1)
    (hu₂ : ‖(q : K) * (u : K)⁻¹‖ < 1) :
    HasSum (fun k ↦ yCoeff q k * (u : K) ^ k)
      (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K) - u / (1 - u) ^ 2) := by
  have hne (k : ℕ) : 1 - (q : K) ^ (k + 1) ≠ 0 := by
    simpa only [zpow_natCast] using one_sub_zpow_ne_zero hq (k := ((k + 1 : ℕ) : ℤ)) (by omega)
  have hnat : HasSum (fun n : ℕ ↦ yCoeff q n * (u : K) ^ (n : ℤ))
      (∑' n : ℕ, (q : K) ^ (n + 1) * u / (1 - (q : K) ^ (n + 1) * u) ^ 2) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, yCoeff, xCoeff,
      Int.cast_zero, zero_div, lt_self_iff_false, ↓reduceIte, sub_zero, zero_mul]
    convert hasSum_lambert hq hu₁ using 2 with k
    have hk : (0 : ℤ) < ((k + 1 : ℕ) : ℤ) := by omega
    simp only [hk, ↓reduceIte, zpow_natCast, Int.cast_natCast]
    field_simp [hne k]
    ring
  have hneg : HasSum (fun n : ℕ ↦ yCoeff q (-(n + 1)) * (u : K) ^ (-((n : ℤ) + 1)))
      (∑' n : ℕ, (q : K) ^ (n + 1) * (u : K)⁻¹ / (1 - (q : K) ^ (n + 1) * (u : K)⁻¹) ^ 2) := by
    convert hasSum_lambert hq hu₂ using 2 with k
    have hk : ¬ (0 : ℤ) < -((k : ℤ) + 1) := by omega
    simp only [yCoeff, xCoeff, hk, ↓reduceIte, sub_zero]
    rw [show -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_neg,
      zpow_natCast, zpow_natCast, inv_pow]
    have hx : (q : K) ^ (k + 1) ≠ 0 := pow_ne_zero _ q.ne_zero
    have h₁ := hne k
    generalize (q : K) ^ (k + 1) = x at hx h₁ ⊢
    have h₂ : 1 - x⁻¹ = -(1 - x) / x := by field_simp; ring
    rw [h₂]
    push_cast
    field_simp
  have h := HasSum.of_nat_of_neg_add_one (f := fun k : ℤ ↦ yCoeff q k * (u : K) ^ k) hnat hneg
  rw [tateUniformizationX_eq_tsum_nat q hq u]
  convert h using 1
  ring

private theorem hasSum_x2Coeff (q u : Kˣ) (hq : ‖(q : K)‖ < 1) (hu₁ : ‖(q : K) * u‖ < 1)
    (hu₂ : ‖(q : K) * (u : K)⁻¹‖ < 1) (hu : (u : K) ≠ 1) :
    HasSum (fun k ↦ x2Coeff q k * (u : K) ^ k)
      ((1 - u) ^ 2 * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K))) := by
  have hY := hasSum_yCoeff q u hq hu₁ hu₂
  have hδ : HasSum (fun k : ℤ ↦ (if k = 1 then (1 : K) else 0) * (u : K) ^ k) u := by
    convert hasSum_ite_eq (1 : ℤ) (u : K) using 1
    funext k
    split_ifs with h <;> simp [h]
  have h := ((hY.sub ((hasSum_laurent_shift u.ne_zero 1 hY).mul_left 2)).add
    (hasSum_laurent_shift u.ne_zero 2 hY)).add hδ
  simp only [zpow_one, zpow_two] at h
  convert h using 1
  · funext k
    rw [x2Coeff_eq]
    ring
  · have h₁ : 1 - (u : K) ≠ 0 := sub_ne_zero.mpr hu.symm
    field_simp
    ring

/-- The second difference of the coefficients of `θ² (X + 2 s₁)` is the Cauchy product of the
second difference of the coefficients of `X + 2 s₁` with the coefficients of `θ²`. -/
private theorem tsum_x2Coeff_mul (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℤ) :
    ∑' k, x2Coeff q k * tateThetaProductCoeff q 1 (n - k) =
      tateXCoeff q n - 2 * tateXCoeff q (n - 1) + tateXCoeff q (n - 2) := by
  have hshift (j : ℤ) : HasSum (fun k ↦ xCoeff q (k - j) * tateThetaProductCoeff q 1 (n - k))
      (tateXCoeff q (n - j)) := by
    rw [← (Equiv.addRight j).hasSum_iff]
    convert hasSum_xCoeff_mul q hq (n - j) using 2 with k
    simp only [Function.comp_apply, Equiv.coe_addRight, add_sub_cancel_right]
    ring_nf
  have h := ((hshift 0).sub ((hshift 1).mul_left 2)).add (hshift 2)
  simp only [sub_zero] at h
  refine (h.congr_fun fun k ↦ ?_).tsum_eq
  simp only [x2Coeff]
  ring

/-- The Laurent expansion of `θ(u)² (X(u) + 2 s₁)` on the fundamental annulus. -/
private theorem hasSum_tateXCoeff_of_norm (q u : Kˣ) (hu₁ : ‖(q : K)‖ < ‖(u : K)‖)
    (hu₂ : ‖(u : K)‖ ≤ 1) (hu : (u : K) ≠ 1) :
    HasSum (fun n ↦ tateXCoeff q n * (u : K) ^ n)
      (tateTheta q u ^ 2 * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K))) := by
  have hq : ‖(q : K)‖ < 1 := hu₁.trans_le hu₂
  have hu₀ : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  have hqu : ‖(q : K) * u‖ < 1 := by
    rw [norm_mul]
    calc ‖(q : K)‖ * ‖(u : K)‖ ≤ ‖(q : K)‖ * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  have hqu' : ‖(q : K) * (u : K)⁻¹‖ < 1 := by
    rwa [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one hu₀]
  have hA : HasSum (fun n ↦ tateXCoeff q n * (u : K) ^ n)
      (∑' n, tateXCoeff q n * (u : K) ^ n) := by
    have h := summable_tateThetaCoefficients q 1 hq two_pos ⟨_, tateXCoeff_mem q hq⟩ u
    simp only [Units.val_zpow_eq_zpow_val] at h
    exact h.hasSum
  have hΔ := (hA.sub ((hasSum_laurent_shift u.ne_zero 1 hA).mul_left 2)).add
    (hasSum_laurent_shift u.ne_zero 2 hA)
  have hC := hasSum_laurent_mul u.ne_zero (hasSum_x2Coeff q u hq hqu hqu' hu)
    (hasSum_tateThetaProductCoeff_one q u hq)
  simp only [tsum_x2Coeff_mul q hq] at hC
  simp only [zpow_one, zpow_two] at hΔ
  have heq := hC.unique (hΔ.congr_fun fun n ↦ by ring)
  have h₁ : (1 - (u : K)) ^ 2 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hu.symm)
  convert hA using 1
  apply mul_left_cancel₀ h₁
  linear_combination heq

/-- The Laurent series with coefficients in `tateThetaCoefficients q 1 2` transforms like
`θ(u)² (X(u) + 2 s₁)` under `u ↦ q u`. -/
private theorem hasSum_tateXCoeff_iff_mul (q u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSum (fun n ↦ tateXCoeff q n * (u : K) ^ n)
        (tateTheta q u ^ 2 * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K))) ↔
      HasSum (fun n ↦ tateXCoeff q n * ((q * u : Kˣ) : K) ^ n)
        (tateTheta q (q * u) ^ 2 *
          (tateUniformizationX q (q * u) + 2 * divisorSumAt 1 (q : K))) := by
  let a : tateThetaCoefficients q 1 2 := ⟨_, tateXCoeff_mem q hq⟩
  have hstep {s : K} (h : HasSum (fun n ↦ tateXCoeff q n * (u : K) ^ n) s) :
      HasSum (fun n ↦ tateXCoeff q n * ((q * u : Kˣ) : K) ^ n) ((u : K) ^ (-2 : ℤ) * s) := by
    have h' := hasSum_tateThetaCoefficients_mul q 1 2 a u
      (by simpa only [Units.val_zpow_eq_zpow_val] using h)
    simpa [a, Units.val_zpow_eq_zpow_val] using h'
  have hvalue : tateTheta q (q * u) ^ 2 *
      (tateUniformizationX q (q * u) + 2 * divisorSumAt 1 (q : K)) =
      (u : K) ^ (-2 : ℤ) * (tateTheta q u ^ 2 *
        (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K))) := by
    rw [tateTheta_self_mul, tateUniformizationX_self_mul, zpow_neg, zpow_two]
    field_simp
  rw [hvalue]
  refine ⟨hstep, fun h ↦ ?_⟩
  have hs := summable_tateThetaCoefficients q 1 hq two_pos a u
  simp only [a, Units.val_zpow_eq_zpow_val] at hs
  convert hs.hasSum using 1
  have := (hstep hs.hasSum).unique h
  have hu2 : (u : K) ^ (-2 : ℤ) ≠ 0 := zpow_ne_zero _ u.ne_zero
  exact (mul_left_cancel₀ hu2 this).symm

private theorem hasSum_tateXCoeff (q : Kˣ) (hq : ‖(q : K)‖ < 1) {u : Kˣ}
    (hu : u ∉ Subgroup.zpowers q) :
    HasSum (fun n ↦ tateXCoeff q n * (u : K) ^ n)
      (tateTheta q u ^ 2 * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K))) := by
  have hzpow (k : ℤ) (v : Kˣ) :
      HasSum (fun n ↦ tateXCoeff q n * (v : K) ^ n)
          (tateTheta q v ^ 2 * (tateUniformizationX q v + 2 * divisorSumAt 1 (q : K))) ↔
        HasSum (fun n ↦ tateXCoeff q n * ((q ^ k * v : Kˣ) : K) ^ n)
          (tateTheta q (q ^ k * v) ^ 2 *
            (tateUniformizationX q (q ^ k * v) + 2 * divisorSumAt 1 (q : K))) := by
    induction k using Int.induction_on with
    | zero => simp
    | succ k ih =>
      rw [ih, hasSum_tateXCoeff_iff_mul q (q ^ (k : ℤ) * v) hq,
        show q * (q ^ (k : ℤ) * v) = q ^ ((k : ℤ) + 1) * v by group]
    | pred k ih =>
      rw [ih, hasSum_tateXCoeff_iff_mul q (q ^ (-(k : ℤ) - 1) * v) hq,
        show q * (q ^ (-(k : ℤ) - 1) * v) = q ^ (-(k : ℤ)) * v by group]
  obtain ⟨k, ⟨hk₁, hk₂⟩, -⟩ := existsUnique_norm_zpow_mul_mem_Ioc q u hq
  have hk : ((q ^ k * u : Kˣ) : K) ≠ 1 := by
    intro h
    refine hu ⟨-k, ?_⟩
    rw [Units.val_eq_one] at h
    dsimp only
    rw [zpow_neg, inv_eq_of_mul_eq_one_right h]
  exact (hzpow k u).mpr (hasSum_tateXCoeff_of_norm q _ hk₁ hk₂ hk)

end Expansion

/-! ### The fibres of the first Tate coordinate -/

section Fibre

variable [IsUltrametricDist K] [CompleteSpace K]

/-- **The Laurent expansion of `θ(u)² (X(u) + 2 s₁(q))`.** Its coefficients are quasi-periodic
of degree two, and the Laurent series converges to `θ(u)² (X(u) + 2 s₁(q))` at every unit
`u ∉ q^ℤ`. -/
theorem exists_hasSum_tateTheta_sq_mul_tateUniformizationX (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    ∃ a ∈ tateThetaCoefficients q 1 2, ∀ u : Kˣ, u ∉ Subgroup.zpowers q →
      HasSum (fun n ↦ a n * (u : K) ^ n)
        (tateTheta q u ^ 2 * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K))) :=
  ⟨_, tateXCoeff_mem q hq, fun _ hu ↦ hasSum_tateXCoeff q hq hu⟩

/-- On the unit circle `‖X(u) + 2 s₁(q)‖ = ‖1 - u‖⁻²`: the term `u / (1 - u)²` dominates. -/
private theorem norm_tateUniformizationX_add (q u : Kˣ) (hq : ‖(q : K)‖ < 1)
    (hu : ‖(u : K)‖ = 1) (hu₁ : (u : K) ≠ 1) :
    ‖tateUniformizationX q u + 2 * divisorSumAt 1 (q : K)‖ = (‖1 - (u : K)‖ ^ 2)⁻¹ := by
  have hterm (w : K) (hw : ‖w‖ = 1) (n : ℕ) :
      ‖(q : K) ^ (n + 1) * w / (1 - (q : K) ^ (n + 1) * w) ^ 2‖ ≤ ‖(q : K)‖ := by
    have hz : ‖(q : K) ^ (n + 1) * w‖ = ‖(q : K)‖ ^ (n + 1) := by
      rw [norm_mul, norm_pow, hw, mul_one]
    have hz₁ : ‖(q : K) ^ (n + 1) * w‖ < 1 := by
      rw [hz]
      exact pow_lt_one₀ (norm_nonneg _) hq (Nat.succ_ne_zero n)
    rw [norm_div, norm_pow, norm_one_sub_of_norm_lt_one hz₁, one_pow, div_one, hz]
    exact pow_le_of_le_one (norm_nonneg _) hq.le (Nat.succ_ne_zero n)
  have hS : ‖(∑' n : ℕ, (q : K) ^ (n + 1) * u / (1 - (q : K) ^ (n + 1) * u) ^ 2) +
      ∑' n : ℕ, (q : K) ^ (n + 1) * (u : K)⁻¹ / (1 - (q : K) ^ (n + 1) * (u : K)⁻¹) ^ 2‖ < 1 := by
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt ?_ ?_)
    · exact (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _)
        (hterm _ hu)).trans_lt hq
    · exact (IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (norm_nonneg _)
        (hterm _ (by rw [norm_inv, hu, inv_one]))).trans_lt hq
  have h₁ : ‖1 - (u : K)‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans ?_
    simp [hu]
  have h₀ : 0 < ‖1 - (u : K)‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hu₁.symm)
  have hmain : ‖(u : K) / (1 - u) ^ 2‖ = (‖1 - (u : K)‖ ^ 2)⁻¹ := by
    rw [norm_div, norm_pow, hu, one_div]
  have hge : 1 ≤ (‖1 - (u : K)‖ ^ 2)⁻¹ :=
    (one_le_inv₀ (by positivity)).mpr (pow_le_one₀ h₀.le h₁)
  rw [tateUniformizationX_eq_tsum_nat q hq u, sub_add_cancel, add_assoc,
    IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hmain]; exact (hS.trans_le hge).ne'),
    hmain, max_eq_left (hS.trans_le hge).le]

/-- The first Tate coordinate is not constant off `q^ℤ`: on the unit circle its norm detects
`‖1 - u‖`. -/
private theorem exists_tateUniformizationX_ne (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    ∃ u v : Kˣ, u ∉ Subgroup.zpowers q ∧ v ∉ Subgroup.zpowers q ∧
      tateUniformizationX q u ≠ tateUniformizationX q v := by
  have hq₀ : 0 < ‖(q : K)‖ := norm_pos_iff.mpr q.ne_zero
  have hmk (n : ℕ) (hn : n ≠ 0) : ∃ u : Kˣ, u ∉ Subgroup.zpowers q ∧ ‖(u : K)‖ = 1 ∧
      (u : K) ≠ 1 ∧ ‖1 - (u : K)‖ = ‖(q : K)‖ ^ n := by
    have hz : ‖(q : K) ^ n‖ < 1 := by
      rw [norm_pow]
      exact pow_lt_one₀ hq₀.le hq hn
    have hnorm : ‖1 + (q : K) ^ n‖ = 1 := by
      rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hz.ne'),
        norm_one, max_eq_left hz.le]
    have hne : 1 + (q : K) ^ n ≠ 0 := by
      intro h
      rw [h, norm_zero] at hnorm
      exact zero_ne_one hnorm
    have hne₁ : 1 + (q : K) ^ n ≠ 1 := by simp [q.ne_zero]
    refine ⟨Units.mk0 _ hne, notMem_zpowers_of_norm_eq_one hq (by simpa using hnorm)
      (fun h ↦ hne₁ (by simpa using congrArg Units.val h)), by simpa using hnorm,
      by simp [q.ne_zero], by simp [norm_pow]⟩
  obtain ⟨u, hu, hu₁, hu₂, hnu⟩ := hmk 1 one_ne_zero
  obtain ⟨v, hv, hv₁, hv₂, hnv⟩ := hmk 2 two_ne_zero
  refine ⟨u, v, hu, hv, fun h ↦ ?_⟩
  have h' := congrArg (fun x ↦ ‖x + 2 * divisorSumAt 1 (q : K)‖) h
  simp only [norm_tateUniformizationX_add q u hq hu₁ hu₂,
    norm_tateUniformizationX_add q v hq hv₁ hv₂, hnu, hnv, inv_inj, ← pow_mul] at h'
  exact (pow_lt_pow_right_of_lt_one₀ hq₀ hq (by norm_num : 1 * 2 < 2 * 2)).ne h'.symm

/-- **The theta-function form of the first Tate coordinate.** For `a ∉ q^ℤ` there is a
nonzero constant `α` with `θ(a u) θ(a⁻¹ u) = α θ(u)² (X(u) - X(a))` for every `u ∉ q^ℤ`. -/
theorem exists_tateTheta_mul_tateTheta_eq (q : Kˣ) (hq : ‖(q : K)‖ < 1) {a : Kˣ}
    (ha : a ∉ Subgroup.zpowers q) :
    ∃ α : K, α ≠ 0 ∧ ∀ u : Kˣ, u ∉ Subgroup.zpowers q →
      tateTheta q (a * u) * tateTheta q (a⁻¹ * u) =
        α * tateTheta q u ^ 2 * (tateUniformizationX q u - tateUniformizationX q a) := by
  have hθ {v : Kˣ} (hv : v ∉ Subgroup.zpowers q) : tateTheta q v ≠ 0 :=
    fun h ↦ hv ((tateTheta_eq_zero_iff q v hq).mp h)
  obtain ⟨u₀, v₀, hu₀, hv₀, hne⟩ := exists_tateUniformizationX_ne q hq
  let T : tateThetaCoefficients q 1 2 := ⟨_, tateThetaProductCoeff_mem q 1⟩
  let A : tateThetaCoefficients q 1 2 := ⟨_, tateXCoeff_mem q hq⟩
  let P : tateThetaCoefficients q 1 2 := ⟨_, tateThetaProductCoeff_mem q a⟩
  -- `θ²` and `θ² (X + 2 s₁)` span the two-dimensional coefficient space.
  have hT : T ≠ 0 := by
    intro h
    have h' := hasSum_tateThetaProductCoeff_one q u₀ hq
    simp only [show tateThetaProductCoeff q 1 = 0 from congrArg Subtype.val h, Pi.zero_apply,
      zero_mul] at h'
    exact hθ hu₀ (pow_eq_zero_iff two_ne_zero |>.mp (hasSum_zero.unique h').symm)
  have hind : LinearIndependent K ![T, A] := by
    refine (LinearIndependent.pair_iff' hT).mpr fun c hc ↦ hne ?_
    have hcoef (n : ℤ) : tateXCoeff q n = c * tateThetaProductCoeff q 1 n :=
      (congrFun (congrArg Subtype.val hc) n).symm
    have hconst {u : Kˣ} (hu : u ∉ Subgroup.zpowers q) :
        tateUniformizationX q u + 2 * divisorSumAt 1 (q : K) = c := by
      have h₁ := hasSum_tateXCoeff q hq hu
      simp only [hcoef, mul_assoc] at h₁
      have h₂ := h₁.unique ((hasSum_tateThetaProductCoeff_one q u hq).mul_left c)
      exact mul_left_cancel₀ (pow_ne_zero 2 (hθ hu)) (by linear_combination h₂)
    linear_combination hconst hu₀ - hconst hv₀
  have hspan := hind.span_eq_top_of_card_eq_finrank (by simp)
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hspan ▸ Submodule.mem_top :
    P ∈ Submodule.span K (Set.range ![T, A]))
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at hc
  have hcoef (n : ℤ) : tateThetaProductCoeff q a n =
      c 0 * tateThetaProductCoeff q 1 n + c 1 * tateXCoeff q n :=
    (congrFun (congrArg Subtype.val hc) n).symm
  have hid {u : Kˣ} (hu : u ∉ Subgroup.zpowers q) :
      tateTheta q (a * u) * tateTheta q (a⁻¹ * u) = c 0 * tateTheta q u ^ 2 +
        c 1 * (tateTheta q u ^ 2 * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K))) := by
    have h := hasSum_tateThetaProductCoeff q a u hq
    simp only [hcoef, add_mul, mul_assoc] at h
    exact h.unique (((hasSum_tateThetaProductCoeff_one q u hq).mul_left (c 0)).add
      ((hasSum_tateXCoeff q hq hu).mul_left (c 1)))
  -- At `u = a` the left side vanishes, which determines `c 0`.
  have hc₀ : c 0 = -(c 1 * (tateUniformizationX q a + 2 * divisorSumAt 1 (q : K))) := by
    have h := hid ha
    rw [inv_mul_cancel, tateTheta_one, mul_zero] at h
    have h' := mul_left_cancel₀ (pow_ne_zero 2 (hθ ha)) (a := tateTheta q a ^ 2)
      (b := c 0 + c 1 * (tateUniformizationX q a + 2 * divisorSumAt 1 (q : K))) (c := 0)
      (by linear_combination -h)
    linear_combination h'
  refine ⟨c 1, fun h₁ ↦ ?_, fun u hu ↦ ?_⟩
  · -- Otherwise `θ(a u) θ(a⁻¹ u)` would vanish identically, in particular at `u = 1`.
    rw [h₁, zero_mul, neg_zero] at hc₀
    have h := hasSum_tateThetaProductCoeff q a 1 hq
    simp only [hcoef, hc₀, h₁, zero_mul, add_zero, mul_one, tateTheta_inv] at h
    rcases mul_eq_zero.mp (hasSum_zero.unique h).symm with h' | h'
    · exact hθ ha h'
    rcases mul_eq_zero.mp h' with h' | h'
    · exact inv_ne_zero a.ne_zero (neg_eq_zero.mp h')
    · exact hθ ha h'
  · rw [hid hu, hc₀]
    ring

/-- **The fibres of the first Tate coordinate.** For units `u, a ∉ q^ℤ`, `X(u) = X(a)` exactly
when `u` lies in `a q^ℤ` or in `a⁻¹ q^ℤ`. -/
theorem tateUniformizationX_eq_tateUniformizationX_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {u a : Kˣ} (hu : u ∉ Subgroup.zpowers q) (ha : a ∉ Subgroup.zpowers q) :
    tateUniformizationX q u = tateUniformizationX q a ↔
      a * u ∈ Subgroup.zpowers q ∨ a⁻¹ * u ∈ Subgroup.zpowers q := by
  obtain ⟨α, hα, h⟩ := exists_tateTheta_mul_tateTheta_eq q hq ha
  have hθ : tateTheta q u ≠ 0 := fun h ↦ hu ((tateTheta_eq_zero_iff q u hq).mp h)
  rw [← tateTheta_eq_zero_iff q _ hq, ← tateTheta_eq_zero_iff q _ hq, ← mul_eq_zero, h u hu]
  simp [hα, hθ, sub_eq_zero]

/-- **The fibres of the Tate uniformisation map.** Two parameters in `Kˣ / q^ℤ` have the same
image on the Tate curve exactly when they are equal, or mutually inverse with a common image of
order at most two. -/
theorem tateUniformization_eq_tateUniformization_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    (x y : Kˣ ⧸ Subgroup.zpowers q) :
    tateUniformization q hq x = tateUniformization q hq y ↔
      x = y ∨ x = y⁻¹ ∧ -tateUniformization q hq y = tateUniformization q hq y := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · by_cases hx : x = 1
    · subst hx
      left
      exact ((tateUniformization_eq_zero_iff q hq y).mp (h ▸ tateUniformization_one q hq)).symm
    by_cases hy : y = 1
    · subst hy
      left
      exact (tateUniformization_eq_zero_iff q hq x).mp (h.trans (tateUniformization_one q hq))
    induction x using QuotientGroup.induction_on with | H u => ?_
    induction y using QuotientGroup.induction_on with | H v => ?_
    have hu : u ∉ Subgroup.zpowers q := fun h ↦ hx ((QuotientGroup.eq_one_iff u).mpr h)
    have hv : v ∉ Subgroup.zpowers q := fun h ↦ hy ((QuotientGroup.eq_one_iff v).mpr h)
    have hX : tateUniformizationX q u = tateUniformizationX q v := by
      have h' := h
      rw [tateUniformization_mk_of_notMem_zpowers q u hq hu,
        tateUniformization_mk_of_notMem_zpowers q v hq hv] at h'
      simp only [WeierstrassCurve.Affine.Point.mk, WeierstrassCurve.Affine.Point.some.injEq] at h'
      exact h'.1
    rcases (tateUniformizationX_eq_tateUniformizationX_iff q hq hu hv).mp hX with h' | h'
    · right
      have hinv : (u : Kˣ ⧸ Subgroup.zpowers q) = (v : Kˣ ⧸ Subgroup.zpowers q)⁻¹ := by
        rw [← QuotientGroup.mk_inv, QuotientGroup.eq, ← mul_inv]
        exact inv_mem (by rwa [mul_comm])
      refine ⟨hinv, ?_⟩
      rw [← tateUniformization_inv, ← hinv, h]
    · left
      rw [QuotientGroup.eq]
      simpa [mul_comm] using inv_mem h'
  · rintro (rfl | ⟨rfl, h⟩)
    · rfl
    · rwa [tateUniformization_inv]

end Fibre


end TauCeti

end
