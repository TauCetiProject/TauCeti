/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.Real.Irrational
public import Mathlib.RingTheory.Algebraic.Basic

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.Algebra.CharZero.RatCast
import TauCeti.Analysis.SpecialFunctions.Exp.ExponentialPolynomial
import TauCeti.NumberTheory.Height.House
import TauCeti.NumberTheory.Transcendental.GelfondSchneider.AnalyticBound
import TauCeti.NumberTheory.Transcendental.GelfondSchneider.SchneiderAuxiliary

/-!
# The Gelfond–Schneider theorem for real numbers

This file proves the Gelfond–Schneider theorem in the real case: if `α > 0` and `β` are real
algebraic numbers with `α ≠ 1` and `β` irrational, then `α ^ β = exp (β log α)` is transcendental
(`TauCeti.transcendental_rpow`).

The proof is Schneider's. Suppose that `γ = α ^ β` is algebraic, and let `K = ℚ(α, β, γ) ⊂ ℝ`,
a number field of degree `d`. For an integer `M ≥ 2` put `L = 2 d M²`, `D₁ = (2 d)² M³` and
`D₂ = 2 d M`, so that `D₁ D₂ = 2 d L²`. Siegel's lemma gives integers `a_{ij}`, not all zero, such
that the auxiliary function `F(z) = ∑_{i < D₁, j < D₂} a_{ij} z ^ i exp (j z log α)` vanishes at
the `L²` points `u + v β`, `1 ≤ u, v ≤ L` (`RingHom.exists_schneider_auxiliary`). On the larger
grid `1 ≤ u, v ≤ 2 d L`:

* `F(u + v β)` is the image of an element `y_{uv}` of `K` whose house is at most
  `exp (O (L ^ (3 / 2) log L))` and which becomes an algebraic integer after multiplication by an
  integer of size `exp (O (L ^ (3 / 2)))` (`TauCeti.exists_house_schneider_value_le_exp_rpow`,
  `TauCeti.isIntegral_intCast_pow_mul_schneider_value`,
  `TauCeti.exists_abs_pow_schneider_exponent_le_exp_rpow`);
* `|F(u + v β)| ≤ exp (O (L ^ (3 / 2) log L) - L ²)` by Schwarz's lemma
  (`TauCeti.exists_norm_schneider_auxiliary_le_exp_rpow`).

By Liouville's inequality (`NumberField.eq_zero_of_norm_le_exp_of_house_le_exp`), these bounds
force `y_{uv} = 0` once `M` is large. Then the real exponential polynomial `F` has `(2 d L)²` real
zeros, whereas it has at most `D₁ D₂ - 1 = 2 d L² - 1` of them
(`TauCeti.card_lt_of_sum_eval_mul_exp_eq_zero`); this is the contradiction.

## Main results

* `TauCeti.transcendental_rpow`: the Gelfond–Schneider theorem for `Real.rpow`.

## References

* J.-H. Evertse, *Diophantine Approximation*, lecture notes (2019), ch. 4, §4.4, Theorem 4.21
  and its proof.
-/

public section

open Filter Finset Module NumberField Polynomial

namespace TauCeti

/-- **Few real zeros of Schneider's auxiliary function.** Let `λ ≠ 0` and let `β` be irrational. If
the real function `F(x) = ∑_{i < D₁, j < D₂} a_{ij} x ^ i exp (j λ x)` with real coefficients, not
all zero, vanishes at the `B²` distinct points `u + v β`, `1 ≤ u, v ≤ B`, then `B² < D₁ D₂`. -/
private theorem sq_lt_mul_of_schneider_eq_zero {l β : ℝ} (hl : l ≠ 0) (hβ : Irrational β)
    {D₁ D₂ B : ℕ} {a : Fin D₁ → Fin D₂ → ℝ} (ha : a ≠ 0)
    (hzero : ∀ u v : ℕ, 1 ≤ u → u ≤ B → 1 ≤ v → v ≤ B →
      ∑ i, ∑ j, a i j * ((u : ℝ) + v * β) ^ (i : ℕ) * Real.exp (j * l * (u + v * β)) = 0) :
    B ^ 2 < D₁ * D₂ := by
  classical
  -- Write `F(x) = ∑_j p_j(x) exp (j λ x)` with `p_j = ∑_i a_{ij} X ^ i`, of degree `< D₁`.
  set p : Fin D₂ → ℝ[X] := fun j ↦ ∑ i : Fin D₁, C (a i j) * X ^ (i : ℕ)
  have heval (j : Fin D₂) (x : ℝ) : (p j).eval x = ∑ i, a i j * x ^ (i : ℕ) := by
    simp [p, eval_finsetSum]
  have hcoeff (i : Fin D₁) (j : Fin D₂) : (p j).coeff i = a i j := by
    simp [p, finsetSum_coeff, coeff_C_mul, coeff_X_pow, Fin.val_inj]
  have hdeg (j : Fin D₂) (hj : p j ≠ 0) : (p j).natDegree < D₁ :=
    (natDegree_lt_iff_degree_lt hj).2 (degree_sum_fin_lt _)
  set s := univ.filter fun j ↦ p j ≠ 0
  have hs : s.Nonempty := by
    obtain ⟨i, j, hij⟩ : ∃ i j, a i j ≠ 0 := by
      by_contra! h
      exact ha (funext₂ h)
    exact ⟨j, mem_filter.2 ⟨mem_univ j, fun hp ↦ hij (by rw [← hcoeff, hp, coeff_zero])⟩⟩
  have hinj : Set.InjOn (fun j : Fin D₂ ↦ (j : ℝ) * l) s := fun j _ k _ h ↦
    Fin.ext (by exact_mod_cast mul_right_cancel₀ hl h)
  -- The `B²` distinct zeros `u + v β`.
  set Z : Finset ℝ := (Icc 1 B ×ˢ Icc 1 B).image fun q : ℕ × ℕ ↦ (q.1 : ℝ) + q.2 * β
  have hZ : #Z = B ^ 2 := by
    have hinjZ : Set.InjOn (fun q : ℕ × ℕ ↦ (q.1 : ℝ) + q.2 * β) ↑(Icc 1 B ×ˢ Icc 1 B) := by
      rintro ⟨u, v⟩ - ⟨u', v'⟩ - h
      simpa using ratCast_add_ratCast_mul_injective (fun q hq ↦ hβ ⟨q, hq⟩)
        (a₁ := (u, v)) (a₂ := (u', v')) (by simpa using h)
    rw [card_image_of_injOn hinjZ, card_product, Nat.card_Icc, Nat.add_sub_cancel, sq]
  have hzeroZ : ∀ x ∈ Z, ∑ j ∈ s, (p j).eval x * Real.exp ((j : ℝ) * l * x) = 0 := by
    simp only [Z, mem_image, mem_product, mem_Icc, Prod.exists]
    rintro _ ⟨u, v, ⟨⟨hu₁, hu⟩, hv₁, hv⟩, rfl⟩
    have hsum : ∑ j ∈ s, (p j).eval ((u : ℝ) + v * β) * Real.exp ((j : ℝ) * l * (u + v * β)) =
        ∑ j, (p j).eval ((u : ℝ) + v * β) * Real.exp ((j : ℝ) * l * (u + v * β)) :=
      sum_filter_of_ne fun j _ h hp ↦ h (by rw [hp, eval_zero, zero_mul])
    rw [hsum, ← hzero u v hu₁ hu hv₁ hv, sum_comm]
    simp only [heval, sum_mul]
  have hlt := card_lt_of_sum_eval_mul_exp_eq_zero hs hinj
    (fun j hj ↦ (mem_filter.1 hj).2) hzeroZ
  rw [hZ] at hlt
  calc B ^ 2 < ∑ j ∈ s, ((p j).natDegree + 1) := hlt
    _ ≤ ∑ _j ∈ s, D₁ := sum_le_sum fun j hj ↦ hdeg j (mem_filter.1 hj).2
    _ ≤ ∑ _j : Fin D₂, D₁ := sum_le_sum_of_subset (subset_univ s)
    _ = D₁ * D₂ := by rw [sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

/-- The exponent in Liouville's inequality for Schneider's values is eventually negative: for
real `c₄`, `c₅`, `c₆` and `e ≥ 0`, with `X = x ^ (3 / 2)`,
`c₆ X + (c₄ X log x - x²) + e (c₆ X + c₅ X log x) < 0` for all large `x`. -/
private theorem eventually_schneider_exponent_neg (c₄ c₅ c₆ : ℝ) {e : ℝ} (he : 0 ≤ e) :
    ∀ᶠ x : ℝ in atTop, c₆ * x ^ (3 / 2 : ℝ) + (c₄ * x ^ (3 / 2 : ℝ) * Real.log x - x ^ 2) +
      e * (c₆ * x ^ (3 / 2 : ℝ) + c₅ * x ^ (3 / 2 : ℝ) * Real.log x) < 0 := by
  -- With `K₀ = |c₄| + |c₆| + e (|c₆| + |c₅|)` the left side is at most `K₀ X log x - x²`, and
  -- `log x ≤ x ^ (1 / 2) / (K₀ + 1)` eventually since `log x = o(x ^ (1 / 2))`.
  set K₀ := |c₄| + |c₆| + e * (|c₆| + |c₅|)
  have hK₀ : 0 ≤ K₀ := by positivity
  filter_upwards [(isLittleO_log_rpow_atTop (r := 1 / 2) (by norm_num)).def
    (by positivity : (0 : ℝ) < 1 / (K₀ + 1)), eventually_ge_atTop (Real.exp 1)] with x hx hx1
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx1
  have hlog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx1
  rw [Real.norm_of_nonneg (by linarith), Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
  have hx2 : x ^ (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ 2 := by
    rw [← Real.rpow_add hx0, ← Real.rpow_natCast]
    norm_num
  set X := x ^ (3 / 2 : ℝ)
  have hX : 0 ≤ X := Real.rpow_nonneg hx0.le _
  have h₄ : c₄ * X * Real.log x ≤ |c₄| * X * Real.log x := by
    gcongr
    exact le_abs_self _
  have h₅ : c₅ * X * Real.log x ≤ |c₅| * X * Real.log x := by
    gcongr
    exact le_abs_self _
  have h₆ : c₆ * X ≤ |c₆| * X * Real.log x :=
    (mul_le_mul_of_nonneg_right (le_abs_self c₆) hX).trans
      (le_mul_of_one_le_right (by positivity) hlog)
  have hK : K₀ * X * Real.log x ≤ K₀ / (K₀ + 1) * x ^ 2 := by
    calc K₀ * X * Real.log x ≤ K₀ * X * (1 / (K₀ + 1) * x ^ (1 / 2 : ℝ)) := by gcongr
      _ = K₀ / (K₀ + 1) * x ^ 2 := by
        rw [← hx2]
        field_simp
  have hlt : K₀ / (K₀ + 1) * x ^ 2 < x ^ 2 :=
    mul_lt_of_lt_one_left (pow_pos hx0 2) ((div_lt_one (by positivity)).2 (by linarith))
  have hsum : K₀ * X * Real.log x = |c₄| * X * Real.log x + |c₆| * X * Real.log x +
      e * (|c₆| * X * Real.log x + |c₅| * X * Real.log x) := by
    simp only [K₀]
    ring
  linarith [mul_le_mul_of_nonneg_left h₆ he, mul_le_mul_of_nonneg_left h₅ he]

/-- **Schneider's auxiliary function with more zeros than coefficients.** Let `K` be a number field
with an embedding `σ : K →+* ℂ`, let `λ ∈ ℂ` and `α, β, γ ∈ K` with `σ α = exp λ`,
`σ γ = exp (σ β λ)` and `σ β` irrational. Then there are `D₁`, `D₂`, `B` with `D₁ D₂ ≤ B²` and
integers `a_{ij}`, `i < D₁`, `j < D₂`, not all zero, such that
`F(z) = ∑_{i, j} a_{ij} z ^ i exp (j λ z)` vanishes at `u + v σ β` for all `1 ≤ u, v ≤ B`. -/
private theorem exists_schneider_auxiliary_mul_le_sq {K : Type*} [Field K] [NumberField K]
    (σ : K →+* ℂ) {l : ℂ} {α β γ : K} (hα : σ α = Complex.exp l)
    (hγ : σ γ = Complex.exp (σ β * l)) (hβ : ∀ q : ℚ, (q : ℂ) ≠ σ β) :
    ∃ D₁ D₂ B : ℕ, D₁ * D₂ ≤ B ^ 2 ∧ ∃ a : Fin D₁ → Fin D₂ → ℤ, a ≠ 0 ∧
      ∀ u v : ℕ, 1 ≤ u → u ≤ B → 1 ≤ v → v ≤ B →
        ∑ i, ∑ j, (a i j : ℂ) * ((u : ℂ) + v * σ β) ^ (i : ℕ) *
          Complex.exp (j * l * (u + v * σ β)) = 0 := by
  classical
  -- Take Schneider's parameters `L = 2 d M²`, `D₁ = (2 d)² M³`, `D₂ = 2 d M` and `B = 2 d L` for
  -- a large `M`. On the grid `1 ≤ u, v ≤ B` the upper bound for `|F(u + v σ β)|` contradicts
  -- Liouville's inequality for the corresponding element `y_{uv}` of `K` unless `y_{uv} = 0`.
  set d := finrank ℚ K
  have hd : 1 ≤ d := finrank_pos
  -- The constants of Schneider's construction for the grid `1 ≤ u, v ≤ c L` with `c = 2 d`.
  set c := 2 * d
  obtain ⟨c₁, -, haux⟩ := RingHom.exists_schneider_auxiliary σ hα hγ
  obtain ⟨m, hm, hmS⟩ := exists_integral_multiples ℤ ℚ ({α, β, γ} : Finset K)
  have hint (x) (hx : x ∈ ({α, β, γ} : Finset K)) : IsIntegral ℤ ((m : K) * x) := by
    simpa only [zsmul_eq_mul] using hmS x hx
  obtain ⟨c₅, hc₅⟩ := exists_house_schneider_value_le_exp_rpow α β γ c₁ c
  obtain ⟨c₆, hc₆⟩ := exists_abs_pow_schneider_exponent_le_exp_rpow d c (m : ℝ)
  obtain ⟨c₄, hc₄⟩ := exists_norm_schneider_auxiliary_le_exp_rpow hβ l d c₁ c
  -- Choose `M ≥ 2` so large that Liouville's exponent is negative for `L = 2 d M²`.
  have hLM : Tendsto (fun M : ℕ ↦ ((2 * d * M ^ 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp <| tendsto_atTop_mono
      (fun M ↦ (Nat.le_self_pow two_ne_zero M).trans (Nat.le_mul_of_pos_left _ (by omega)))
      tendsto_id
  obtain ⟨M, hneg, hM⟩ := ((hLM.eventually (eventually_schneider_exponent_neg c₄ c₅ c₆
    (Nat.cast_nonneg (d - 1)))).and (eventually_ge_atTop 2)).exists
  set L := 2 * d * M ^ 2
  have hL : 8 ≤ L :=
    le_trans (by norm_num) (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hd) (Nat.pow_le_pow_left hM 2))
  obtain ⟨a, ha0, ha, hzero⟩ := haux L ((2 * d) ^ 2 * M ^ 3) (2 * d * M) (by omega)
    (le_of_eq (by ring))
  refine ⟨_, _, c * L, ?_, a, ha0, fun u v hu₁ hu hv₁ hv ↦ ?_⟩
  · -- `D₁ D₂ = 2 d L² ≤ (2 d L)²`.
    calc (2 * d) ^ 2 * M ^ 3 * (2 * d * M) = c * L ^ 2 := by simp only [c, L]; ring
      _ ≤ c ^ 2 * L ^ 2 := Nat.mul_le_mul_right _ (Nat.le_self_pow two_ne_zero c)
      _ = (c * L) ^ 2 := (mul_pow c L 2).symm
  -- The value `y_{uv} ∈ K` vanishes by Liouville's inequality, hence so does `F(u + v σ β)`.
  have hσy := hc₄ M L _ _ (by omega) rfl rfl rfl (fun i j ↦ (a i j : ℂ))
    (fun i j ↦ by simpa only [Complex.norm_intCast] using ha i j) hzero u v hu hv
  have hval := eq_zero_of_norm_le_exp_of_house_le_exp σ hm
    (isIntegral_intCast_pow_mul_schneider_value (hint α (by simp)) (hint β (by simp))
      (hint γ (by simp)) a hu hv)
    (by rwa [RingHom.map_schneider_value σ hα hγ])
    (hc₅ M L _ _ (by omega) rfl rfl rfl a ha u v hu hv) (hc₆ M L _ _ rfl rfl rfl) hneg
  rw [← RingHom.map_schneider_value σ hα hγ, hval, map_zero]

/-- **The Gelfond–Schneider theorem for real numbers** (Evertse, Theorem 4.21). If `α > 0` and `β`
are real algebraic numbers with `α ≠ 1` and `β` irrational, then `α ^ β` is transcendental. -/
theorem transcendental_rpow {α β : ℝ} (hα : IsAlgebraic ℚ α) (hβ : IsAlgebraic ℚ β) (h0 : 0 < α)
    (h1 : α ≠ 1) (hirr : Irrational β) : Transcendental ℚ (α ^ β) := by
  intro hγ
  -- The number field `K = ℚ(α, β, α ^ β) ⊂ ℝ`, with its embedding `σ` into `ℂ`.
  set K := IntermediateField.adjoin ℚ ({α, β, α ^ β} : Set ℝ)
  have : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin <| by
    rintro x (rfl | rfl | rfl)
    exacts [hα.isIntegral, hβ.isIntegral, hγ.isIntegral]
  have : NumberField K := { }
  let α' : K := ⟨α, IntermediateField.subset_adjoin _ _ (by simp)⟩
  let β' : K := ⟨β, IntermediateField.subset_adjoin _ _ (by simp)⟩
  let γ' : K := ⟨α ^ β, IntermediateField.subset_adjoin _ _ (by simp)⟩
  let σ : K →+* ℂ := Complex.ofRealHom.comp (algebraMap K ℝ)
  -- `σ` is the inclusion `K ⊂ ℝ ⊂ ℂ`, so it sends `β' = ⟨β, _⟩` to `β` by definition.
  have hσβ : σ β' = β := rfl
  have hσα : σ α' = Complex.exp (Real.log α) := by
    simp [σ, α', ← Complex.ofReal_exp, Real.exp_log h0]
  have hσγ : σ γ' = Complex.exp (σ β' * Real.log α) := by
    simp [σ, β', γ', Real.rpow_def_of_pos h0, mul_comm]
  obtain ⟨D₁, D₂, B, hB, a, ha0, hzero⟩ := exists_schneider_auxiliary_mul_le_sq σ hσα hσγ
    fun q hq ↦ hirr ⟨q, Complex.ofReal_injective (by rw [Complex.ofReal_ratCast, hq, hσβ])⟩
  -- The real exponential polynomial `F` has `B²` zeros, but fewer than `D₁ D₂ ≤ B²` of them.
  refine absurd hB (not_le.2 (sq_lt_mul_of_schneider_eq_zero
    (Real.log_ne_zero_of_pos_of_ne_one h0 h1) hirr (a := fun i j ↦ (a i j : ℝ))
    (fun h ↦ ha0 (funext₂ fun i j ↦ by simpa using congr_fun₂ h i j)) fun u v hu₁ hu hv₁ hv ↦ ?_))
  have := hzero u v hu₁ hu hv₁ hv
  rw [hσβ] at this
  exact_mod_cast this

end TauCeti
