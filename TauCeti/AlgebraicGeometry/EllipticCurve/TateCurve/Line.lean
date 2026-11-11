/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.XCoordinate
import TauCeti.AlgebraicGeometry.EllipticCurve.TateCurve.Strata
import TauCeti.Analysis.Normed.Field.ZPowers
import TauCeti.Analysis.Normed.Group.Ultra
import TauCeti.Analysis.Normed.Module.InfiniteSum
import TauCeti.Analysis.Normed.Ring.Ultra
import TauCeti.Analysis.SpecificLimits.Normed
import TauCeti.Data.Int.MulPred
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Lines through three points of the Tate curve

Let `K` be a complete non-archimedean field and `q ∈ Kˣ` with `‖q‖ < 1`. Multiplied by the cube
of the theta function `θ` of the Tate curve, the second Tate coordinate becomes an entire
Laurent series: `θ(u)³ (Y(u) - s₁(q))` is a convergent Laurent series on all of `Kˣ ∖ q^ℤ`, whose
coefficients satisfy the degree-three quasi-periodicity recurrence `a(n + 3) = -qⁿ a(n)`
(`TauCeti.exists_hasSum_tateTheta_pow_three_mul_tateUniformizationY`). So do the coefficients of
`θ(u)³`, of `θ(u)³ (X(u) + 2 s₁(q))`, and of `θ(a⁻¹ u) θ(b⁻¹ u) θ(a b u)` for all units `a, b`.
The first three are linearly independent, because `X` and `Y` have poles of orders two and
three at `u = 1`, so they span the three-dimensional space of solutions. This gives the classical
identity

`θ(a⁻¹ u) θ(b⁻¹ u) θ(a b u) = θ(u)³ (α + β X(u) + γ Y(u))`,  `γ ≠ 0`,

for `a, b, a b ∉ q^ℤ` (`TauCeti.exists_tateTheta_mul_tateTheta_mul_tateTheta_eq`). Since the
zeros of `θ` are the powers of `q`, the line `α + β x + γ y = 0` meets the image of `Kˣ ∖ q^ℤ`
under the Tate coordinates exactly in the images of `a q^ℤ`, `b q^ℤ` and `(a b)⁻¹ q^ℤ`
(`TauCeti.exists_tateUniformizationY_eq_iff`). These are the three points whose sum in the group
law of the Tate curve is zero.

As for the first coordinate, the argument works at the level of Laurent coefficients, with no
uniqueness theorem for Laurent expansions, and it applies to every complete non-archimedean
absolute value, discrete or not, in every characteristic. The coefficients of `Y - s₁` are
`(k (k - 1) / 2) / (1 - qᵏ)`, and the halved product `k (k - 1) / 2` is an integer, so no
division by `2` takes place in `K`. The expansion on the unit circle is made for
`(1 - u)³ (Y(u) - s₁(q))`.

## Main results

* `TauCeti.exists_hasSum_tateTheta_pow_three_mul_tateUniformizationY`: the Laurent coefficients
  of `θ(u)³ (Y(u) - s₁(q))` are quasi-periodic of degree three.
* `TauCeti.exists_tateTheta_mul_tateTheta_mul_tateTheta_eq`:
  `θ(a⁻¹ u) θ(b⁻¹ u) θ(a b u) = θ(u)³ (α + β X(u) + γ Y(u))` with `γ ≠ 0`.
* `TauCeti.exists_tateUniformizationY_eq_iff`: the line through the images of `a`, `b` and
  `(a b)⁻¹` meets the image of `Kˣ ∖ q^ℤ` only there.
* `TauCeti.exists_tateQuotientCoordinates_snd_eq_iff`: the same on `Kˣ / q^ℤ`, for classes `x`,
  `y` and `(x y)⁻¹`.

## References

* J. Tate, *A review of non-Archimedean elliptic functions*, in *Elliptic curves, modular forms,
  & Fermat's last theorem* (Hong Kong, 1993), International Press (1995), 162–184.
* P. Roquette, *Analytic theory of elliptic functions over local fields*, Hamburger
  Mathematische Einzelschriften (N.F.) 1, Vandenhoeck & Ruprecht (1970).
* J. H. Silverman, *Advanced Topics in the Arithmetic of Elliptic Curves*, GTM 151, §V.3.
-/

public section

namespace TauCeti

variable {K : Type*} [NormedField K]

/-! ### The Laurent coefficients of `θ³` -/

section Cube

/-- The Laurent coefficients of `θ(a u) θ(b u) θ(c u)`. -/
private noncomputable def tripleCoeff (q a b c : Kˣ) (n : ℤ) : K :=
  ∑' m, tateThetaCoeff q m * (a : K) ^ m * ∑' k, tateThetaCoeff q k * (b : K) ^ k *
    (tateThetaCoeff q (n - m - k) * (c : K) ^ (n - m - k))

private theorem tripleCoeff_mem (q a b c : Kˣ) :
    tripleCoeff q a b c ∈ tateThetaCoefficients q (-a * (-b * -c)) 3 :=
  tsum_mul_sub_mem_tateThetaCoefficients (tateThetaCoeff_mul_zpow_mem q a)
    (tsum_mul_sub_mem_tateThetaCoefficients (tateThetaCoeff_mul_zpow_mem q b)
      (tateThetaCoeff_mul_zpow_mem q c))

/-- The Laurent coefficients `s` of `θ³` satisfy `s(n + 3) = -qⁿ s(n)`. -/
private theorem tripleCoeff_one_mem (q : Kˣ) :
    tripleCoeff q 1 1 1 ∈ tateThetaCoefficients q (-1) 3 := by
  have h := tripleCoeff_mem q 1 1 1
  rwa [show (-1 : Kˣ) * (-1 * -1) = -1 by simp] at h

private theorem tripleCoeff_one_add_three (q : Kˣ) (n : ℤ) :
    tripleCoeff q 1 1 1 (n + 3) = -(q : K) ^ n * tripleCoeff q 1 1 1 n := by
  simpa using (mem_tateThetaCoefficients_iff _ _ _ _).mp (tripleCoeff_one_mem q) n

private theorem tripleCoeff_one_eq (q : Kˣ) : tripleCoeff q 1 1 1 = fun n ↦
    ∑' m, tateThetaCoeff q m * ∑' k, tateThetaCoeff q k * tateThetaCoeff q (n - m - k) := by
  funext n
  simp [tripleCoeff]

variable [CompleteSpace K] [IsUltrametricDist K]

private theorem hasSum_tripleCoeff (q a b c u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSum (fun n ↦ tripleCoeff q a b c n * (u : K) ^ n)
      (tateTheta q (a * u) * tateTheta q (b * u) * tateTheta q (c * u)) := by
  have h := hasSum_laurent_mul u.ne_zero (hasSum_tateThetaCoeff_mul_zpow q a u hq)
    (hasSum_laurent_mul u.ne_zero (hasSum_tateThetaCoeff_mul_zpow q b u hq)
      (hasSum_tateThetaCoeff_mul_zpow q c u hq))
  rw [mul_assoc]
  exact h

private theorem hasSum_tripleCoeff_one (q u : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSum (fun n ↦ tripleCoeff q 1 1 1 n * (u : K) ^ n) (tateTheta q u ^ 3) := by
  convert hasSum_tripleCoeff q 1 1 1 u hq using 1
  simp only [one_mul]
  ring

/-- `θ³` vanishes to order three at `u = 1`: the moments `∑ s(n)`, `∑ n s(n)` and
`∑ (n (n - 1) / 2) s(n)` of its Laurent coefficients vanish. -/
private theorem tripleCoeff_one_moments (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    HasSum (tripleCoeff q 1 1 1) 0 ∧
      HasSum (fun n : ℤ ↦ (n : K) * tripleCoeff q 1 1 1 n) 0 ∧
      HasSum (fun n : ℤ ↦ ((n * (n - 1) / 2 : ℤ) : K) * tripleCoeff q 1 1 1 n) 0 := by
  have h₀ := hasSum_tateThetaCoeff_one q hq
  have h₁ := (summable_mul_of_norm_le_one h₀.summable
    fun n : ℤ ↦ IsUltrametricDist.norm_intCast_le_one K n).hasSum
  have h₂ := (summable_mul_of_norm_le_one h₀.summable
    fun n : ℤ ↦ IsUltrametricDist.norm_intCast_le_one K (n * (n - 1) / 2)).hasSum
  -- The coefficients of `θ²` have vanishing zeroth and first moments.
  have s₀ := h₀.tsum_mul_sub h₀
  have s₁ := h₀.intCast_mul_tsum_mul_sub h₁ h₀ h₁
  have s₂ := h₀.intCast_mul_sub_one_ediv_two_mul_tsum_mul_sub h₁ h₂ h₀ h₁ h₂
  simp only [mul_zero, zero_mul, add_zero, zero_add] at s₀ s₁ s₂
  rw [tripleCoeff_one_eq]
  refine ⟨?_, ?_, ?_⟩
  · simpa using h₀.tsum_mul_sub s₀
  · simpa using h₀.intCast_mul_tsum_mul_sub h₁ s₀ s₁
  · simpa using h₀.intCast_mul_sub_one_ediv_two_mul_tsum_mul_sub h₁ h₂ s₀ s₁ s₂

end Cube

/-! ### The Laurent coefficients of `θ³ (Y - s₁)` -/

section YCoeff

/-- The Laurent coefficient `(k (k - 1) / 2) / (1 - qᵏ)` of `Y - s₁` on the annulus
`‖q‖ < ‖u‖ < 1`. -/
private noncomputable def yCoeff (q : Kˣ) (k : ℤ) : K :=
  ((k * (k - 1) / 2 : ℤ) : K) / (1 - (q : K) ^ k)

/-- The Laurent coefficients of `u² / (1 - u)³` on the open unit disc. -/
private def nodeCoeff (k : ℤ) : ℤ := if 0 < k then k * (k - 1) / 2 else 0

/-- The Laurent coefficients of `Y(u) - s₁(q) - u² / (1 - u)³` on the annulus
`‖q‖ < ‖u‖ < ‖q‖⁻¹`. -/
private noncomputable def yTildeCoeff (q : Kˣ) (k : ℤ) : K := yCoeff q k - nodeCoeff k

/-- The third difference of the Laurent coefficients of `Y - s₁`, which are the Laurent
coefficients of `(1 - u)³ (Y(u) - s₁)`. -/
private noncomputable def y3Coeff (q : Kˣ) (k : ℤ) : K :=
  yCoeff q k - 3 * yCoeff q (k - 1) + 3 * yCoeff q (k - 2) - yCoeff q (k - 3)

/-- The third difference of the coefficients of `u² / (1 - u)³` is the coefficient sequence
of `u²`. -/
private theorem nodeCoeff_third_difference (k : ℤ) :
    nodeCoeff k - 3 * nodeCoeff (k - 1) + 3 * nodeCoeff (k - 2) - nodeCoeff (k - 3) =
      if k = 2 then 1 else 0 := by
  have h := Int.two_mul_mul_sub_one_ediv_two
  rcases (by omega : k ≤ 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with hk | rfl | rfl | rfl | hk
  · simp only [nodeCoeff, show ¬ 0 < k by omega, show ¬ 0 < k - 1 by omega,
      show ¬ 0 < k - 2 by omega, show ¬ 0 < k - 3 by omega, show k ≠ 2 by omega, ↓reduceIte]
    norm_num
  · rfl
  · rfl
  · rfl
  · simp only [nodeCoeff, show 0 < k by omega, show 0 < k - 1 by omega, show 0 < k - 2 by omega,
      show 0 < k - 3 by omega, show k ≠ 2 by omega, ↓reduceIte]
    linarith [h k, h (k - 1), h (k - 2), h (k - 3)]

private theorem y3Coeff_eq (q : Kˣ) (k : ℤ) :
    y3Coeff q k = yTildeCoeff q k - 3 * yTildeCoeff q (k - 1) + 3 * yTildeCoeff q (k - 2) -
      yTildeCoeff q (k - 3) + if k = 2 then 1 else 0 := by
  have h := congrArg (fun z : ℤ ↦ (z : K)) (nodeCoeff_third_difference k)
  push_cast at h
  rw [y3Coeff, yTildeCoeff, yTildeCoeff, yTildeCoeff, yTildeCoeff, ← h]
  ring

variable [IsUltrametricDist K]

private theorem norm_yCoeff_le_one {q : Kˣ} (hq : ‖(q : K)‖ < 1) (k : ℤ) :
    ‖yCoeff q k‖ ≤ 1 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [yCoeff]
  rw [yCoeff, norm_div]
  exact div_le_one_of_le₀ ((IsUltrametricDist.norm_intCast_le_one K _).trans
    (one_le_norm_one_sub_of_norm_ne_one (norm_zpow_ne_one hq hk))) (norm_nonneg _)

variable [CompleteSpace K]

/-- The expansion of `Y(u) - s₁(q) - u² / (1 - u)³` on the annulus `‖q‖ < ‖u‖ < ‖q‖⁻¹`. -/
private theorem hasSum_yTildeCoeff (q u : Kˣ) (hq : ‖(q : K)‖ < 1) (hu₁ : ‖(q : K) * u‖ < 1)
    (hu₂ : ‖(q : K) * (u : K)⁻¹‖ < 1) :
    HasSum (fun k ↦ yTildeCoeff q k * (u : K) ^ k)
      (tateUniformizationY q u - divisorSumAt 1 (q : K) - (u : K) ^ 2 / (1 - u) ^ 3) := by
  -- The indices `k ≥ 1` give a Lambert series in `q u` and the indices `k ≤ 0` one in `q u⁻¹`;
  -- `Y(u) - s₁ - u² / (1 - u)³` is the sum of the two by `tateUniformizationY_eq_tsum_nat`.
  have hne (k : ℕ) : 1 - (q : K) ^ (k + 1) ≠ 0 := by
    simpa only [zpow_natCast] using one_sub_zpow_ne_zero hq (k := ((k + 1 : ℕ) : ℤ)) (by omega)
  -- For `k ≥ 1`, `yCoeff q k = (k choose 2) / (1 - qᵏ)` and `nodeCoeff k = k choose 2`.
  have hnat : HasSum (fun n : ℕ ↦ yTildeCoeff q n * (u : K) ^ (n : ℤ))
      (∑' n : ℕ, ((q : K) ^ (n + 1) * u) ^ 2 / (1 - (q : K) ^ (n + 1) * u) ^ 3) := by
    rw [← hasSum_nat_add_iff' 1]
    convert hasSum_lambert_sq_div_pow_three hq hu₁ using 1
    · funext k
      have hT := (Int.natCast_choose_two (k + 1)).symm
      push_cast at hT
      simp only [yTildeCoeff, yCoeff, nodeCoeff, show (0 : ℤ) < ((k + 1 : ℕ) : ℤ) by omega,
        ↓reduceIte, zpow_natCast]
      push_cast
      rw [hT]
      push_cast
      field_simp [hne k]
      ring
    · simp [yTildeCoeff, yCoeff, nodeCoeff]
  -- For `k = -(n + 1)`, `nodeCoeff k = 0` and `yCoeff q k = -(n + 2 choose 2) qᵐ / (1 - qᵐ)`
  -- with `m = n + 1`.
  have hneg' : HasSum (fun n : ℕ ↦ yTildeCoeff q (-(n + 1)) * (u : K) ^ (-((n : ℤ) + 1)))
      (∑' n : ℕ, -((q : K) ^ (n + 1) * (u : K)⁻¹) /
        (1 - (q : K) ^ (n + 1) * (u : K)⁻¹) ^ 3) := by
    convert (hasSum_lambert_div_pow_three hq hu₂).neg using 1
    swap
    · rw [← tsum_neg]
      simp only [neg_div]
    funext k
    have hT : (-((k : ℤ) + 1)) * (-((k : ℤ) + 1) - 1) / 2 = (((k + 2).choose 2 : ℕ) : ℤ) := by
      rw [Int.natCast_choose_two, ← Int.one_sub_mul_one_sub_sub_one_ediv_two]
      push_cast
      ring_nf
    simp only [yTildeCoeff, yCoeff, nodeCoeff, show ¬ (0 : ℤ) < -((k : ℤ) + 1) by omega,
      ↓reduceIte, Int.cast_zero, sub_zero, hT, Int.cast_natCast]
    rw [show -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_neg,
      zpow_natCast, zpow_natCast, inv_pow]
    have hx : (q : K) ^ (k + 1) ≠ 0 := pow_ne_zero _ q.ne_zero
    have h₁ := hne k
    generalize (q : K) ^ (k + 1) = x at hx h₁ ⊢
    have h₂ : 1 - x⁻¹ = -(1 - x) / x := by field_simp; ring
    rw [h₂]
    field_simp
  -- Glue the two halves of the Laurent series.
  have h := HasSum.of_nat_of_neg_add_one (f := fun k : ℤ ↦ yTildeCoeff q k * (u : K) ^ k)
    hnat hneg'
  rw [tateUniformizationY_eq_tsum_nat q hq u]
  convert h using 1
  ring

/-- The expansion of `(1 - u)³ (Y(u) - s₁(q))` on `‖q‖ < ‖u‖ < ‖q‖⁻¹`, which includes the unit
circle. -/
private theorem hasSum_y3Coeff (q u : Kˣ) (hq : ‖(q : K)‖ < 1) (hu₁ : ‖(q : K) * u‖ < 1)
    (hu₂ : ‖(q : K) * (u : K)⁻¹‖ < 1) (hu : (u : K) ≠ 1) :
    HasSum (fun k ↦ y3Coeff q k * (u : K) ^ k)
      ((1 - u) ^ 3 * (tateUniformizationY q u - divisorSumAt 1 (q : K))) := by
  have hY := hasSum_yTildeCoeff q u hq hu₁ hu₂
  have hδ : HasSum (fun k : ℤ ↦ (if k = 2 then (1 : K) else 0) * (u : K) ^ k) ((u : K) ^ 2) := by
    convert hasSum_ite_eq (2 : ℤ) ((u : K) ^ 2) using 1
    funext k
    split_ifs with h <;> simp [h]
  have h := ((((hY.sub ((hasSum_laurent_shift u.ne_zero 1 hY).mul_left 3)).add
    ((hasSum_laurent_shift u.ne_zero 2 hY).mul_left 3)).sub
    (hasSum_laurent_shift u.ne_zero 3 hY)).add hδ)
  convert h using 1
  · funext k
    rw [y3Coeff_eq]
    ring
  · have h₁ : 1 - (u : K) ≠ 0 := sub_ne_zero.mpr hu.symm
    simp only [zpow_ofNat]
    field_simp
    ring

/-- The coefficients of `θ³ (Y - s₁)`: the Cauchy product of `(k (k - 1) / 2) / (1 - qᵏ)` with
the coefficients of `θ³`. -/
private noncomputable def tateYCoeff (q : Kˣ) (n : ℤ) : K :=
  ∑' k, yCoeff q k * tripleCoeff q 1 1 1 (n - k)

private theorem hasSum_yCoeff_mul (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℤ) :
    HasSum (fun k ↦ yCoeff q k * tripleCoeff q 1 1 1 (n - k)) (tateYCoeff q n) := by
  refine (summable_mul_of_norm_le_one ?_ (norm_yCoeff_le_one hq)).hasSum
  exact (Equiv.subLeft n).summable_iff.mpr (tripleCoeff_one_moments q hq).1.summable

/-- `∑ₖ (k (k - 1) / 2) q⁻ᵏ s(n - k) = 0` for the coefficients `s` of `θ³`, by the recurrence of
`s` and the vanishing of its first three moments. -/
private theorem hasSum_ediv_two_mul_zpow_neg_mul (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℤ) :
    HasSum (fun k : ℤ ↦
      ((k * (k - 1) / 2 : ℤ) : K) * (q : K) ^ (-k) * tripleCoeff q 1 1 1 (n - k)) 0 := by
  obtain ⟨h₀, h₁, h₂⟩ := tripleCoeff_one_moments q hq
  have h := (((h₀.mul_left (((n + 3) * (n + 3 - 1) / 2 : ℤ) : K)).add h₂).add
    (h₁.mul_left (1 - ((n + 3 : ℤ) : K)))).mul_left (-(q : K) ^ (-n))
  simp only [mul_zero, add_zero] at h
  rw [← (Equiv.subLeft (n + 3)).hasSum_iff]
  refine h.congr_fun fun j ↦ ?_
  -- `T(n + 3 - j) = T(n + 3) + T(j) + j - (n + 3) j` for `T(m) = m (m - 1) / 2`.
  have hT : (n + 3 - j) * (n + 3 - j - 1) / 2 =
      (n + 3) * (n + 3 - 1) / 2 + j * (j - 1) / 2 + j - (n + 3) * j := by
    have h := Int.two_mul_mul_sub_one_ediv_two
    linarith [h (n + 3 - j), h (n + 3), h j]
  have hs := tripleCoeff_one_add_three q (j - 3)
  rw [sub_add_cancel] at hs
  simp only [Function.comp_apply, Equiv.subLeft_apply, hT,
    show n - (n + 3 - j) = j - 3 by ring, hs]
  rw [show -(n + 3 - j) = -n + (j - 3) by ring, zpow_add₀ q.ne_zero]
  push_cast
  ring

private theorem tateYCoeff_add_three (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℤ) :
    tateYCoeff q (n + 3) = -(q : K) ^ n * tateYCoeff q n := by
  have h := ((hasSum_yCoeff_mul q hq n).add (hasSum_ediv_two_mul_zpow_neg_mul q hq n)).mul_left
    (-(q : K) ^ n)
  rw [add_zero] at h
  refine (hasSum_yCoeff_mul q hq (n + 3)).unique (h.congr_fun fun k ↦ ?_)
  rw [show n + 3 - k = n - k + 3 by ring, tripleCoeff_one_add_three]
  rcases eq_or_ne k 0 with rfl | hk
  · simp [yCoeff]
  have h₁ := one_sub_zpow_ne_zero hq hk
  simp only [yCoeff, zpow_sub₀ q.ne_zero, zpow_neg]
  field_simp
  ring

private theorem tateYCoeff_mem (q : Kˣ) (hq : ‖(q : K)‖ < 1) :
    tateYCoeff q ∈ tateThetaCoefficients q (-1) 3 := by
  rw [mem_tateThetaCoefficients_iff]
  intro n
  simp [tateYCoeff_add_three q hq]

/-- The third difference of the coefficients of `θ³ (Y - s₁)` is the Cauchy product of the third
difference of the coefficients of `Y - s₁` with the coefficients of `θ³`. -/
private theorem tsum_y3Coeff_mul (q : Kˣ) (hq : ‖(q : K)‖ < 1) (n : ℤ) :
    ∑' k, y3Coeff q k * tripleCoeff q 1 1 1 (n - k) =
      tateYCoeff q n - 3 * tateYCoeff q (n - 1) + 3 * tateYCoeff q (n - 2) -
        tateYCoeff q (n - 3) := by
  have hshift (j : ℤ) : HasSum (fun k ↦ yCoeff q (k - j) * tripleCoeff q 1 1 1 (n - k))
      (tateYCoeff q (n - j)) := by
    rw [← (Equiv.addRight j).hasSum_iff]
    convert hasSum_yCoeff_mul q hq (n - j) using 2 with k
    simp only [Function.comp_apply, Equiv.coe_addRight, add_sub_cancel_right]
    ring_nf
  have h := (((hshift 0).sub ((hshift 1).mul_left 3)).add ((hshift 2).mul_left 3)).sub (hshift 3)
  simp only [sub_zero] at h
  refine (h.congr_fun fun k ↦ ?_).tsum_eq
  simp only [y3Coeff]
  ring

/-- The Laurent expansion of `θ(u)³ (Y(u) - s₁)` on the fundamental annulus. -/
private theorem hasSum_tateYCoeff_of_norm (q u : Kˣ) (hu₁ : ‖(q : K)‖ < ‖(u : K)‖)
    (hu₂ : ‖(u : K)‖ ≤ 1) (hu : (u : K) ≠ 1) :
    HasSum (fun n ↦ tateYCoeff q n * (u : K) ^ n)
      (tateTheta q u ^ 3 * (tateUniformizationY q u - divisorSumAt 1 (q : K))) := by
  have hq : ‖(q : K)‖ < 1 := hu₁.trans_le hu₂
  have hu₀ : 0 < ‖(u : K)‖ := norm_pos_iff.mpr u.ne_zero
  have hqu : ‖(q : K) * u‖ < 1 := by
    rw [norm_mul]
    calc ‖(q : K)‖ * ‖(u : K)‖ ≤ ‖(q : K)‖ * 1 := by gcongr
      _ < 1 := by rwa [mul_one]
  have hqu' : ‖(q : K) * (u : K)⁻¹‖ < 1 := by
    rwa [norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_one hu₀]
  have hA : HasSum (fun n ↦ tateYCoeff q n * (u : K) ^ n)
      (∑' n, tateYCoeff q n * (u : K) ^ n) := by
    have h := summable_tateThetaCoefficients q (-1) hq three_pos ⟨_, tateYCoeff_mem q hq⟩ u
    simp only [Units.val_zpow_eq_zpow_val] at h
    exact h.hasSum
  have hΔ := ((hA.sub ((hasSum_laurent_shift u.ne_zero 1 hA).mul_left 3)).add
    ((hasSum_laurent_shift u.ne_zero 2 hA).mul_left 3)).sub
    (hasSum_laurent_shift u.ne_zero 3 hA)
  have hC := hasSum_laurent_mul u.ne_zero (hasSum_y3Coeff q u hq hqu hqu' hu)
    (hasSum_tripleCoeff_one q u hq)
  simp only [tsum_y3Coeff_mul q hq] at hC
  simp only [zpow_ofNat] at hΔ
  have heq := hC.unique (hΔ.congr_fun fun n ↦ by ring)
  have h₁ : (1 - (u : K)) ^ 3 ≠ 0 := pow_ne_zero _ (sub_ne_zero.mpr hu.symm)
  convert hA using 1
  apply mul_left_cancel₀ h₁
  linear_combination heq

private theorem hasSum_tateYCoeff (q : Kˣ) (hq : ‖(q : K)‖ < 1) {u : Kˣ}
    (hu : u ∉ Subgroup.zpowers q) :
    HasSum (fun n ↦ tateYCoeff q n * (u : K) ^ n)
      (tateTheta q u ^ 3 * (tateUniformizationY q u - divisorSumAt 1 (q : K))) := by
  refine hasSum_tateThetaCoefficients_of_forall_norm q (-1) hq three_pos ⟨_, tateYCoeff_mem q hq⟩
    (f := fun u ↦ tateTheta q u ^ 3 * (tateUniformizationY q u - divisorSumAt 1 (q : K)))
    (fun v ↦ ?_) (fun v hv₁ hv₂ hv ↦ hasSum_tateYCoeff_of_norm q v hv₁ hv₂ ?_) hu
  · rw [inv_neg, inv_one, Units.val_mul, Units.val_neg, Units.val_one,
      Units.val_zpow_eq_zpow_val]
    simp only [tateTheta_self_mul, tateUniformizationY_self_mul, Nat.cast_ofNat, zpow_neg]
    field_simp
  · exact fun h ↦ hv (Units.val_eq_one.mp h)

/-- **The Laurent expansion of `θ(u)³ (Y(u) - s₁(q))`.** Its coefficients are quasi-periodic
of degree three, and the Laurent series converges to `θ(u)³ (Y(u) - s₁(q))` at every unit
`u ∉ q^ℤ`. -/
theorem exists_hasSum_tateTheta_pow_three_mul_tateUniformizationY (q : Kˣ)
    (hq : ‖(q : K)‖ < 1) :
    ∃ a ∈ tateThetaCoefficients q (-1) 3, ∀ u : Kˣ, u ∉ Subgroup.zpowers q →
      HasSum (fun n ↦ a n * (u : K) ^ n)
        (tateTheta q u ^ 3 * (tateUniformizationY q u - divisorSumAt 1 (q : K))) :=
  ⟨_, tateYCoeff_mem q hq, fun _ hu ↦ hasSum_tateYCoeff q hq hu⟩

end YCoeff

/-! ### Lines through three points -/

section Line

variable [IsUltrametricDist K] [CompleteSpace K]

/-- Near `u = 1` on the unit circle the Tate coordinates have poles of orders two and three:
for every `ε > 0` there are `u ∉ q^ℤ` and `0 < r < min ε 1` with `‖X(u) + 2 s₁‖ r² = 1` and
`‖Y(u) - s₁‖ r³ = 1`. -/
private theorem exists_norm_tateUniformization_mul_eq_one (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ u : Kˣ, u ∉ Subgroup.zpowers q ∧ ∃ r : ℝ, 0 < r ∧ r < ε ∧ r < 1 ∧
      ‖tateUniformizationX q u + 2 * divisorSumAt 1 (q : K)‖ * r ^ 2 = 1 ∧
      ‖tateUniformizationY q u - divisorSumAt 1 (q : K)‖ * r ^ 3 = 1 := by
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one (lt_min hε one_pos) hq
  set z : K := (q : K) ^ m with hz
  have hz₀ : z ≠ 0 := pow_ne_zero _ q.ne_zero
  have hzr : 0 < ‖z‖ := norm_pos_iff.mpr hz₀
  have hz₁ : ‖z‖ < 1 := by rw [hz, norm_pow]; exact hm.trans_le (min_le_right _ _)
  have hnorm : ‖1 + z‖ = 1 := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hz₁.ne'),
      norm_one, max_eq_left hz₁.le]
  have hne : 1 + z ≠ 0 := norm_ne_zero_iff.mp (by rw [hnorm]; exact one_ne_zero)
  set u : Kˣ := Units.mk0 (1 + z) hne
  have hu : (u : K) = 1 + z := rfl
  have hu₁ : (u : K) ≠ 1 := by rw [hu]; simpa using hz₀
  have hun : ‖(u : K)‖ = 1 := by rw [hu, hnorm]
  have hd : ‖1 - (u : K)‖ = ‖z‖ := by rw [hu, show 1 - (1 + z) = -z by ring, norm_neg]
  have hs : ‖divisorSumAt 1 (q : K)‖ < 1 := (norm_divisorSumAt_le 1 hq).trans_lt hq
  have h2s : ‖2 * divisorSumAt 1 (q : K)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (by exact_mod_cast IsUltrametricDist.norm_natCast_le_one K 2)).trans_lt hs
  have hpow (k : ℕ) (hk : k ≠ 0) : 1 < (‖z‖ ^ k)⁻¹ :=
    (one_lt_inv₀ (pow_pos hzr k)).mpr (pow_lt_one₀ hzr.le hz₁ hk)
  refine ⟨u, notMem_zpowers_of_norm_eq_one hq hun (fun h ↦ hu₁ (by rw [h, Units.val_one])),
    ‖z‖, hzr, hm.trans_le' (by rw [hz, norm_pow]) |>.trans_le (min_le_left _ _), hz₁, ?_, ?_⟩
  · have hX := norm_tateUniformizationX_of_norm_one_sub_lt_one q u hq hu₁ (by rwa [hd])
    rw [hd] at hX
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm
      (by rw [hX]; exact (h2s.trans (hpow 2 two_ne_zero)).ne'), hX,
      max_eq_left (h2s.trans (hpow 2 two_ne_zero)).le, inv_mul_cancel₀ (pow_pos hzr 2).ne']
  · have hmain : ‖(u : K) ^ 2 / (1 - u) ^ 3‖ = (‖z‖ ^ 3)⁻¹ := by
      rw [norm_div, norm_pow, norm_pow, hun, hd, one_pow, one_div]
    have hY := norm_tateUniformizationY_sub_le_of_norm_eq_one q u hq hun
    have hlt : ‖tateUniformizationY q u - divisorSumAt 1 (q : K) - (u : K) ^ 2 / (1 - u) ^ 3‖ <
        ‖(u : K) ^ 2 / (1 - u) ^ 3‖ := by
      rw [sub_right_comm]
      refine ((IsUltrametricDist.norm_sub_le_max _ _).trans_lt (max_lt (hY.trans_lt hq) hs)).trans
        ?_
      rw [hmain]
      exact hpow 3 three_ne_zero
    rw [← IsUltrametricDist.norm_eq_of_norm_sub_lt_left (by rwa [norm_sub_rev]), hmain,
      inv_mul_cancel₀ (pow_pos hzr 3).ne']

/-- The pole-order argument: a coefficient `δ` with `‖δ‖ ≤ a rᵏ + b r` at every point `u ∉ q^ℤ`
and radius `0 < r < 1` as in `exists_norm_tateUniformization_mul_eq_one` vanishes, since `r` can
be taken arbitrarily small. -/
private theorem eq_zero_of_norm_le_pow_add_mul (q : Kˣ) (hq : ‖(q : K)‖ < 1) {δ : K} {a b : ℝ}
    {k : ℕ} (hk : k ≠ 0) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : ∀ u : Kˣ, u ∉ Subgroup.zpowers q → ∀ r : ℝ, 0 < r → r < 1 →
      ‖tateUniformizationX q u + 2 * divisorSumAt 1 (q : K)‖ * r ^ 2 = 1 →
      ‖tateUniformizationY q u - divisorSumAt 1 (q : K)‖ * r ^ 3 = 1 → ‖δ‖ ≤ a * r ^ k + b * r) :
    δ = 0 := by
  by_contra hδ
  obtain ⟨u, hu, r, hr₀, hrε, hr₁, hX, hY⟩ := exists_norm_tateUniformization_mul_eq_one q hq
    (div_pos (norm_pos_iff.mpr hδ) (by positivity : 0 < a + b + 1))
  rw [lt_div_iff₀ (by positivity)] at hrε
  have hrk : a * r ^ k ≤ a * r := mul_le_mul_of_nonneg_left (pow_le_of_le_one hr₀.le hr₁.le hk) ha
  linarith [h u hu r hr₀ hr₁ hX hY]

/-- The functions `1`, `X + 2 s₁` and `Y - s₁` are linearly independent on `Kˣ ∖ q^ℤ`. -/
private theorem eq_zero_of_forall_add_mul_add_mul_eq_zero (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {α β γ : K} (h : ∀ u : Kˣ, u ∉ Subgroup.zpowers q →
      α + β * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K)) +
        γ * (tateUniformizationY q u - divisorSumAt 1 (q : K)) = 0) :
    α = 0 ∧ β = 0 ∧ γ = 0 := by
  -- `Y - s₁` has a pole of order three, `X + 2 s₁` one of order two.
  have hγ : γ = 0 := eq_zero_of_norm_le_pow_add_mul q hq three_ne_zero (norm_nonneg α)
      (norm_nonneg β) fun u hu r hr₀ _ hX hY ↦ by
    have key : ‖γ * (tateUniformizationY q u - divisorSumAt 1 (q : K))‖ ≤
        ‖α‖ + ‖β‖ * ‖tateUniformizationX q u + 2 * divisorSumAt 1 (q : K)‖ := by
      rw [show γ * (tateUniformizationY q u - divisorSumAt 1 (q : K)) =
        -(α + β * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K))) by
        linear_combination h u hu, norm_neg, ← norm_mul]
      exact norm_add_le _ _
    rw [norm_mul] at key
    have := mul_le_mul_of_nonneg_right key (pow_pos hr₀ 3).le
    rwa [mul_assoc, hY, mul_one, add_mul, mul_assoc, show ‖tateUniformizationX q u +
      2 * divisorSumAt 1 (q : K)‖ * r ^ 3 = ‖tateUniformizationX q u +
      2 * divisorSumAt 1 (q : K)‖ * r ^ 2 * r by ring, hX, one_mul] at this
  subst hγ
  have hβ : β = 0 := eq_zero_of_norm_le_pow_add_mul q hq two_ne_zero (norm_nonneg α) le_rfl
      fun u hu r _ _ hX _ ↦ by
    have key : ‖β * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K))‖ = ‖α‖ := by
      rw [show β * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K)) = -α by
        linear_combination h u hu, norm_neg]
    rw [norm_mul] at key
    have := congrArg (· * r ^ 2) key
    rw [mul_assoc, hX, mul_one] at this
    linarith
  subst hβ
  obtain ⟨u, hu, -⟩ := exists_norm_tateUniformization_mul_eq_one q hq one_pos
  exact ⟨by simpa using h u hu, rfl, rfl⟩

/-- Laurent series converging to `θ³`, `θ³ (X + 2 s₁)` and `θ³ (Y - s₁)` off `q^ℤ` have linearly
independent coefficient sequences. -/
private theorem linearIndependent_of_hasSum (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {s x y : tateThetaCoefficients q (-1) 3}
    (hs : ∀ u : Kˣ, u ∉ Subgroup.zpowers q →
      HasSum (fun n ↦ s.val n * (u : K) ^ n) (tateTheta q u ^ 3))
    (hx : ∀ u : Kˣ, u ∉ Subgroup.zpowers q → HasSum (fun n ↦ x.val n * (u : K) ^ n)
      (tateTheta q u ^ 3 * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K))))
    (hy : ∀ u : Kˣ, u ∉ Subgroup.zpowers q → HasSum (fun n ↦ y.val n * (u : K) ^ n)
      (tateTheta q u ^ 3 * (tateUniformizationY q u - divisorSumAt 1 (q : K)))) :
    LinearIndependent K ![s, x, y] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hcoef (n : ℤ) : g 0 * s.val n + g 1 * x.val n + g 2 * y.val n = 0 := by
    simpa [Fin.sum_univ_three] using congrFun (congrArg Subtype.val hg) n
  obtain ⟨h₀, h₁, h₂⟩ := eq_zero_of_forall_add_mul_add_mul_eq_zero q hq (α := g 0) (β := g 1)
      (γ := g 2) fun u hu ↦ by
    have h := (((hs u hu).mul_left (g 0)).add ((hx u hu).mul_left (g 1))).add
      ((hy u hu).mul_left (g 2))
    simp only [← mul_assoc, ← add_mul, hcoef, zero_mul] at h
    have hθ : tateTheta q u ^ 3 ≠ 0 :=
      pow_ne_zero 3 (tateTheta_ne_zero q hq hu)
    refine (mul_eq_zero.mp ?_).resolve_left hθ
    linear_combination -(hasSum_zero.unique h)
  intro i
  fin_cases i
  exacts [h₀, h₁, h₂]

/-- **The degree-three coefficient space.** Every solution `a` of the recurrence
`a(n + 3) = -qⁿ a(n)` is the coefficient sequence of `θ(u)³ (α + β (X(u) + 2 s₁) + γ (Y(u) - s₁))`
off `q^ℤ`, and if `γ = 0` its Laurent series vanishes at `u = 1`. -/
private theorem exists_hasSum_tateTheta_pow_three_mul (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {a : ℤ → K} (ha : a ∈ tateThetaCoefficients q (-1) 3) :
    ∃ α β γ : K, (∀ u : Kˣ, u ∉ Subgroup.zpowers q → HasSum (fun n ↦ a n * (u : K) ^ n)
      (tateTheta q u ^ 3 * (α + β * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K)) +
        γ * (tateUniformizationY q u - divisorSumAt 1 (q : K))))) ∧ (γ = 0 → HasSum a 0) := by
  -- The coefficients of `θ³ (X + 2 s₁)`, the Cauchy product of those of `θ` and `θ² (X + 2 s₁)`.
  obtain ⟨A, hA, hAsum⟩ := exists_hasSum_tateTheta_sq_mul_tateUniformizationX q hq
  have hTA := tsum_mul_sub_mem_tateThetaCoefficients (tateThetaCoeff_mem q) hA
  rw [show (-1 : Kˣ) * 1 = -1 by simp] at hTA
  have hTAsum (u : Kˣ) (hu : u ∉ Subgroup.zpowers q) :
      HasSum (fun n ↦ (∑' m, tateThetaCoeff q m * A (n - m)) * (u : K) ^ n)
        (tateTheta q u ^ 3 * (tateUniformizationX q u + 2 * divisorSumAt 1 (q : K))) := by
    convert hasSum_laurent_mul u.ne_zero (hasSum_tateThetaCoeff q u hq) (hAsum u hu) using 1
    ring
  -- Its Laurent series vanishes at `u = 1`, as `θ(1) = 0`.
  have hTA₁ : HasSum (fun n ↦ ∑' m, tateThetaCoeff q m * A (n - m)) 0 := by
    have hA₁ := summable_tateThetaCoefficients q 1 hq two_pos ⟨A, hA⟩ 1
    simp only [one_zpow, Units.val_one, mul_one] at hA₁
    simpa using (hasSum_tateThetaCoeff_one q hq).tsum_mul_sub hA₁.hasSum
  let S : tateThetaCoefficients q (-1) 3 := ⟨_, tripleCoeff_one_mem q⟩
  let T : tateThetaCoefficients q (-1) 3 := ⟨_, hTA⟩
  let U : tateThetaCoefficients q (-1) 3 := ⟨_, tateYCoeff_mem q hq⟩
  have hspan := (linearIndependent_of_hasSum q hq (s := S) (x := T) (y := U)
    (fun u _ ↦ hasSum_tripleCoeff_one q u hq) hTAsum
    (fun u hu ↦ hasSum_tateYCoeff q hq hu)).span_eq_top_of_card_eq_finrank
    (by simp [finrank_tateThetaCoefficients])
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).mp (hspan ▸ Submodule.mem_top :
    (⟨a, ha⟩ : tateThetaCoefficients q (-1) 3) ∈ Submodule.span K (Set.range ![S, T, U]))
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hc
  have hcoef (n : ℤ) : a n = c 0 * tripleCoeff q 1 1 1 n +
      c 1 * ∑' m, tateThetaCoeff q m * A (n - m) + c 2 * tateYCoeff q n := by
    have := congrFun (congrArg Subtype.val hc) n
    simp only [Submodule.coe_add, Submodule.coe_smul, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, S, T, U] at this
    exact this.symm
  refine ⟨c 0, c 1, c 2, fun u hu ↦ ?_, fun h₂ ↦ ?_⟩
  · convert (((hasSum_tripleCoeff_one q u hq).mul_left (c 0)).add
      ((hTAsum u hu).mul_left (c 1))).add ((hasSum_tateYCoeff q hq hu).mul_left (c 2)) using 1
    · funext n
      rw [hcoef]
      ring
    · ring
  · convert ((tripleCoeff_one_moments q hq).1.mul_left (c 0)).add (hTA₁.mul_left (c 1)) using 1
    · funext n
      rw [hcoef, h₂]
      ring
    · ring

/-- **Three translated theta functions and a line.** For units `a, b` with `a, b, a b ∉ q^ℤ`
there are `α, β, γ ∈ K` with `γ ≠ 0` such that
`θ(a⁻¹ u) θ(b⁻¹ u) θ(a b u) = θ(u)³ (α + β X(u) + γ Y(u))` for every `u ∉ q^ℤ`. -/
theorem exists_tateTheta_mul_tateTheta_mul_tateTheta_eq (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {a b : Kˣ} (ha : a ∉ Subgroup.zpowers q) (hb : b ∉ Subgroup.zpowers q)
    (hab : a * b ∉ Subgroup.zpowers q) :
    ∃ α β γ : K, γ ≠ 0 ∧ ∀ u : Kˣ, u ∉ Subgroup.zpowers q →
      tateTheta q (a⁻¹ * u) * tateTheta q (b⁻¹ * u) * tateTheta q (a * b * u) =
        tateTheta q u ^ 3 * (α + β * tateUniformizationX q u + γ * tateUniformizationY q u) := by
  -- The coefficients of `θ(a⁻¹ u) θ(b⁻¹ u) θ(a b u)` lie in the degree-three space.
  have hF := tripleCoeff_mem q a⁻¹ b⁻¹ (a * b)
  rw [show -a⁻¹ * (-b⁻¹ * -(a * b)) = -1 by
    ext; simp only [Units.val_mul, Units.val_neg, Units.val_inv_eq_inv_val, Units.val_one]
    field_simp] at hF
  obtain ⟨α, β, γ, hid, h₀⟩ := exists_hasSum_tateTheta_pow_three_mul q hq hF
  refine ⟨α + 2 * β * divisorSumAt 1 (q : K) - γ * divisorSumAt 1 (q : K), β, γ,
    fun hγ ↦ ?_, fun u hu ↦ ?_⟩
  · -- Otherwise the value `θ(a⁻¹) θ(b⁻¹) θ(a b)` of the Laurent series at `u = 1` would vanish.
    have h := hasSum_tripleCoeff q a⁻¹ b⁻¹ (a * b) 1 hq
    simp only [Units.val_one, one_zpow, mul_one] at h
    rcases mul_eq_zero.mp (h.unique (h₀ hγ)) with h' | h'
    · rcases mul_eq_zero.mp h' with h' | h'
      · exact tateTheta_ne_zero q hq (fun h ↦ ha (by simpa using inv_mem h)) h'
      · exact tateTheta_ne_zero q hq (fun h ↦ hb (by simpa using inv_mem h)) h'
    · exact tateTheta_ne_zero q hq hab h'
  · rw [(hasSum_tripleCoeff q a⁻¹ b⁻¹ (a * b) u hq).unique (hid u hu)]
    ring

/-- **The line through three points of the Tate curve.** For units `a, b` with `a, b, a b ∉ q^ℤ`
there is a line `y = μ x + ν` that passes through the point `(X(u), Y(u))`, for a unit
`u ∉ q^ℤ`, exactly when `u` lies in `a q^ℤ`, in `b q^ℤ` or in `(a b)⁻¹ q^ℤ`. -/
theorem exists_tateUniformizationY_eq_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1) {a b : Kˣ}
    (ha : a ∉ Subgroup.zpowers q) (hb : b ∉ Subgroup.zpowers q)
    (hab : a * b ∉ Subgroup.zpowers q) :
    ∃ μ ν : K, ∀ u : Kˣ, u ∉ Subgroup.zpowers q →
      (tateUniformizationY q u = μ * tateUniformizationX q u + ν ↔
        a⁻¹ * u ∈ Subgroup.zpowers q ∨ b⁻¹ * u ∈ Subgroup.zpowers q ∨
          a * b * u ∈ Subgroup.zpowers q) := by
  obtain ⟨α, β, γ, hγ, h⟩ := exists_tateTheta_mul_tateTheta_mul_tateTheta_eq q hq ha hb hab
  refine ⟨-β / γ, -α / γ, fun u hu ↦ ?_⟩
  have hθ := tateTheta_ne_zero q hq hu
  rw [← tateTheta_eq_zero_iff q _ hq, ← tateTheta_eq_zero_iff q _ hq,
    ← tateTheta_eq_zero_iff q _ hq, ← or_assoc, ← mul_eq_zero, ← mul_eq_zero, h u hu,
    mul_eq_zero, or_iff_right (pow_ne_zero 3 hθ)]
  constructor
  · intro h'
    rw [h']
    field_simp
    ring
  · intro h'
    field_simp
    linear_combination h'

/-- **The line through three points of the Tate curve, on the quotient.** For classes `x, y` in
`Kˣ / q^ℤ` with `x, y, x y ≠ 1` there is a line `Y = μ X + ν` that passes through the Tate
coordinates `(X, Y)` of a nonidentity class `w` exactly when `w` is `x`, `y` or `(x y)⁻¹`. -/
theorem exists_tateQuotientCoordinates_snd_eq_iff (q : Kˣ) (hq : ‖(q : K)‖ < 1)
    {x y : Kˣ ⧸ Subgroup.zpowers q} (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x * y ≠ 1) :
    ∃ μ ν : K, ∀ w : Kˣ ⧸ Subgroup.zpowers q, w ≠ 1 →
      ((tateQuotientCoordinates q w).2 = μ * (tateQuotientCoordinates q w).1 + ν ↔
        w = x ∨ w = y ∨ w = (x * y)⁻¹) := by
  induction x using QuotientGroup.induction_on with | H a => ?_
  induction y using QuotientGroup.induction_on with | H b => ?_
  have hnot {u : Kˣ} (hu : (u : Kˣ ⧸ Subgroup.zpowers q) ≠ 1) : u ∉ Subgroup.zpowers q :=
    fun h ↦ hu ((QuotientGroup.eq_one_iff u).mpr h)
  obtain ⟨μ, ν, h⟩ := exists_tateUniformizationY_eq_iff q hq (hnot hx) (hnot hy)
    (hnot (by rwa [QuotientGroup.mk_mul]))
  refine ⟨μ, ν, fun w hw ↦ ?_⟩
  induction w using QuotientGroup.induction_on with | H u => ?_
  rw [tateQuotientCoordinates_mk, h u (hnot hw), ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv]
  simp only [eq_comm (a := (u : Kˣ ⧸ Subgroup.zpowers q)), QuotientGroup.eq, inv_inv]

end Line

end TauCeti

end
