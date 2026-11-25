/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant
import TauCeti.NumberTheory.NumberField.Index.Discriminant
import TauCeti.NumberTheory.NumberField.Minpoly
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace
import TauCeti.NumberTheory.NumberField.Units.Basic
import TauCeti.NumberTheory.NumberField.Units.PrimeDegree
import TauCeti.NumberTheory.NumberField.Units.Regulator.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Explicit discriminant-dependent lower bounds for the regulator of a quadratic field

Let `K` be a quadratic number field of discriminant `D`. When `K` is imaginary quadratic (`D < 0`),
its unit rank is `0` and `NumberField.Units.regulator K = 1` trivially. When `K` is real quadratic
(`D > 0`), `5 ≤ D` (`TauCeti.Multiquadratic.five_le_discr_of_isTotallyReal`), attained by `ℚ(√5)`.

At any real infinite place `w`, every unit `u` of `𝓞 K` with `1 < w(u)` generates `K` over `ℚ`, so
the index formula `disc (minpoly ℤ u) = [𝓞 K : ℤ[u]]² · D` bounds the discriminant `(x - N(u)/x)²`
of `minpoly ℤ u` from below by `D`, where `x > 1` is the real image of `u` at `w` and
`N(u) ∈ {1, -1}` is the field norm of `u`. Solving this quadratic inequality gives:

* `(√D + √(D - 4)) / 2 ≤ x` unconditionally
  (`sqrt_discr_add_sqrt_sub_four_div_two_le_embedding_of_isReal`), attained when `N(u) = -1` and
  `[𝓞 K : ℤ[u]] = 1` (for instance `u = (1 + √5)/2` in `ℚ(√5)`);
* `(√(D + 4) + √D) / 2 ≤ x` whenever `N(u) = 1`
  (`sqrt_discr_add_four_add_sqrt_div_two_le_embedding_of_isReal_of_norm_eq_one`), attained for
  instance by `2 + √3` in `ℚ(√3)` (`D = 12`, `(√16 + √12)/2 = 2 + √3`).

Choosing `u` to be a normalized fundamental unit yields the corresponding sharp lower bounds on
`NumberField.Units.regulator K` for real quadratic fields (which also hold trivially for `D < 0`
because `Real.sqrt` evaluates to `0` on negative arguments and `regulator K = 1`). For the
uniform discriminant-free bound `log ((1 + √5) / 2) ≤ regulator K`, see
`TauCeti.NumberField.Units.log_goldenRatio_le_regulator` in
`TauCeti.NumberTheory.NumberField.Units.Elimination.GoldenRatio`.

## Main results

All declarations are in the `TauCeti.NumberField.Units` namespace:

* `sqrt_discr_add_sqrt_sub_four_div_two_le_embedding_of_isReal`: any unit with real image `x > 1`
  at a real place satisfies `(√D + √(D - 4)) / 2 ≤ x`.
* `sqrt_discr_add_four_add_sqrt_div_two_le_embedding_of_isReal_of_norm_eq_one`: if moreover
  `N(u) = 1`, then `(√(D + 4) + √D) / 2 ≤ x`.
* `exists_one_lt_embedding_of_isReal_and_regulator_eq_log`: existence of a unit with real image
  `x > 1` at a real place `w` whose logarithm equals `regulator K`.
* `log_sqrt_discr_add_sqrt_sub_four_div_two_le_regulator`:
  `log ((√D + √(D - 4)) / 2) ≤ regulator K`, sharp for real quadratic fields (`D > 0`) and trivial
  for `D < 0` (where `Real.sqrt` vanishes on negative reals and `regulator K = 1`).
* `log_sqrt_discr_add_four_add_sqrt_div_two_le_regulator`: when every unit has norm `1`,
  `log ((√(D + 4) + √D) / 2) ≤ regulator K` (sharp for real quadratic fields such as `ℚ(√3)` and
  trivial for `D < 0`).

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, Springer, 1993, §5.7.
* P. Koymans and C. Pagano, *A sharp upper bound for the 2-torsion of class groups of
  multiquadratic fields*, Mathematika **68** (2022), §7.2.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.Units Polynomial
open TauCeti.Multiquadratic
open scoped NumberField

namespace TauCeti.NumberField.Units

variable {K : Type*} [Field K] [NumberField K]

/-- For a unit `u` with real image `x > 1` at a real place of a quadratic field, the index formula
gives `(discr K : ℝ) ≤ (x - N(u) / x) ^ 2`. -/
private theorem discr_le_embedding_of_isReal_sub_norm_div_sq_of_one_lt {w : InfinitePlace K}
    (hw : w.IsReal) (hK : finrank ℚ K = 2) {u : (𝓞 K)ˣ} (hu : 1 < embedding_of_isReal hw (u : K)) :
    (discr K : ℝ) ≤
      (embedding_of_isReal hw (u : K) -
        (Algebra.norm ℚ (u : K) : ℝ) / embedding_of_isReal hw (u : K)) ^ 2 := by
  -- `u` is non-torsion, so in degree `2` it is an integral primitive element of `K`.
  let θ : IntegralPrimitiveElement K :=
    ⟨u, adjoin_eq_top_of_finrank_prime (hK ▸ Nat.prime_two)
      (notMem_torsion_of_one_lt_embedding_of_isReal hw hu)⟩
  set x : ℝ := embedding_of_isReal hw (u : K)
  set f : ℤ[X] := minpoly ℤ (u : 𝓞 K)
  have hmonic : f.Monic := minpoly.monic (u : 𝓞 K).isIntegral
  have hdegf : f.natDegree = 2 := θ.natDegree_minpoly.trans hK
  have hc0 : (f.coeff 0 : ℝ) = Algebra.norm ℚ (u : K) := by
    rw [θ.norm_eq_coeff_zero_minpoly, hK]
    push_cast
    ring
  -- Map `f` to `ℝ[X]`, where `x > 1` is a nonzero root, so `discr f = (x - N(u) / x) ^ 2`.
  have hroot : (f.map (algebraMap ℤ ℝ)).IsRoot x := by
    rw [IsRoot.def, eval_map_algebraMap]
    exact minpoly.aeval_algHom ℤ
      ((embedding_of_isReal hw).comp (algebraMap (𝓞 K) K)).toIntAlgHom (u : 𝓞 K)
  have hfdiscr : (f.discr : ℝ) = (x - (Algebra.norm ℚ (u : K) : ℝ) / x) ^ 2 := by
    rw [← eq_intCast (algebraMap ℤ ℝ), ← hmonic.discr_map (algebraMap ℤ ℝ),
      (hmonic.map _).discr_eq_sub_coeff_zero_div_sq_of_isRoot ((hmonic.natDegree_map _).trans hdegf)
        (zero_lt_one.trans hu).ne' hroot,
      coeff_map, eq_intCast, hc0]
  -- The index formula `f.discr = [𝓞 K : ℤ[u]]² · discr K` bounds `f.discr` below by `discr K > 0`.
  have : IsTotallyReal K := isTotallyReal_of_finrank_eq_two_of_isReal hK hw
  have hD5 : 5 ≤ discr K := five_le_discr_of_isTotallyReal hK
  have hidx : discr K ≤ f.discr := by
    rw [θ.discr_minpoly_eq_index_sq_mul_discr]
    exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (mod_cast θ.index_pos))
  rw [← hfdiscr]
  exact_mod_cast hidx

/-- **Norm-one unit lower bound in a real quadratic field.** If `u` is a unit of norm `1` whose
real image at `w` exceeds `1`, then `(√(D + 4) + √D) / 2 ≤ w(u)`, where `D = discr K`. -/
theorem sqrt_discr_add_four_add_sqrt_div_two_le_embedding_of_isReal_of_norm_eq_one
    {w : InfinitePlace K} (hw : w.IsReal) (hK : finrank ℚ K = 2) {u : (𝓞 K)ˣ}
    (hu : 1 < embedding_of_isReal hw (u : K)) (hnorm : Algebra.norm ℚ (u : K) = 1) :
    (√((discr K : ℝ) + 4) + √(discr K : ℝ)) / 2 ≤ embedding_of_isReal hw (u : K) := by
  have hsq := discr_le_embedding_of_isReal_sub_norm_div_sq_of_one_lt hw hK hu
  rw [hnorm, Rat.cast_one] at hsq
  set x := embedding_of_isReal hw (u : K)
  have hx0 : 0 < x := zero_lt_one.trans hu
  have h1 : √(discr K : ℝ) ≤ x - 1 / x :=
    Real.sqrt_le_iff.mpr ⟨by linarith [div_le_self zero_le_one hu.le], hsq⟩
  have hadd_sq : (discr K : ℝ) + 4 ≤ (x + 1 / x) ^ 2 := by
    have hid : (x + 1 / x) ^ 2 = (x - 1 / x) ^ 2 + 4 := by
      linear_combination 4 * mul_one_div_cancel hx0.ne'
    linarith
  have h2 : √((discr K : ℝ) + 4) ≤ x + 1 / x :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hadd_sq⟩
  linarith

/-- **Sharp discriminant-dependent unit lower bound in a real quadratic field.** Every unit `u`
whose real image at `w` exceeds `1` satisfies `(√D + √(D - 4)) / 2 ≤ w(u)`, where `D = discr K`. -/
theorem sqrt_discr_add_sqrt_sub_four_div_two_le_embedding_of_isReal {w : InfinitePlace K}
    (hw : w.IsReal) (hK : finrank ℚ K = 2) {u : (𝓞 K)ˣ}
    (hu : 1 < embedding_of_isReal hw (u : K)) :
    (√(discr K : ℝ) + √((discr K : ℝ) - 4)) / 2 ≤ embedding_of_isReal hw (u : K) := by
  have : IsTotallyReal K := isTotallyReal_of_finrank_eq_two_of_isReal hK hw
  have : (5 : ℝ) ≤ discr K := mod_cast five_le_discr_of_isTotallyReal hK
  have hsq := discr_le_embedding_of_isReal_sub_norm_div_sq_of_one_lt hw hK hu
  rcases (abs_eq (zero_le_one' ℚ)).mp (NumberField.Units.norm K u) with h1 | hneg1
  · refine le_trans ?_
      (sqrt_discr_add_four_add_sqrt_div_two_le_embedding_of_isReal_of_norm_eq_one hw hK hu h1)
    have hle : √((discr K : ℝ) - 4) ≤ √((discr K : ℝ) + 4) := Real.sqrt_le_sqrt (by linarith)
    linarith
  · rw [hneg1, Rat.cast_neg, Rat.cast_one] at hsq
    set x := embedding_of_isReal hw (u : K)
    have hx0 : 0 < x := zero_lt_one.trans hu
    have hsq' : (discr K : ℝ) ≤ (x + 1 / x) ^ 2 := by
      convert hsq using 2
      ring
    have h1 : √(discr K : ℝ) ≤ x + 1 / x :=
      Real.sqrt_le_iff.mpr ⟨by positivity, hsq'⟩
    have hsub_sq : (discr K : ℝ) - 4 ≤ (x - 1 / x) ^ 2 := by
      have hid : (x - 1 / x) ^ 2 = (x + 1 / x) ^ 2 - 4 := by
        linear_combination -4 * mul_one_div_cancel hx0.ne'
      linarith
    have h2 : √((discr K : ℝ) - 4) ≤ x - 1 / x :=
      Real.sqrt_le_iff.mpr ⟨by linarith [div_le_self zero_le_one hu.le], hsub_sq⟩
    linarith

/-- **Normalized fundamental unit of a real quadratic field.** At any real infinite place `w` of a
quadratic field `K`, there exists a unit `u` whose real image exceeds `1` and whose logarithm is
`regulator K`. -/
theorem exists_one_lt_embedding_of_isReal_and_regulator_eq_log {w : InfinitePlace K} (hw : w.IsReal)
    (hK : finrank ℚ K = 2) :
    ∃ u : (𝓞 K)ˣ, 1 < embedding_of_isReal hw (u : K) ∧
      regulator K = Real.log (embedding_of_isReal hw (u : K)) := by
  have hr : rank K = 1 := rank_eq_one_of_finrank_eq_two_of_isReal hK hw
  obtain ⟨g, hg⟩ := exists_closure_sup_torsion_eq_top_of_rank_eq_one hr
  have hreg : regulator K = |Real.log (w g)| := by
    rw [regulator_eq_mult_abs_log_of_rank_eq_one hr g hg w, hw.mult_eq_one, Nat.cast_one, one_mul]
  have hlog_ne : Real.log (w g) ≠ 0 := fun h0 ↦
    (regulator_pos K).ne' (by rw [hreg, h0, abs_zero])
  have hg_pos : 0 < w g := Units.pos_at_place g w
  obtain ⟨u₀, hu₀_gt, hu₀_reg⟩ : ∃ u₀ : (𝓞 K)ˣ, 1 < w u₀ ∧ regulator K = Real.log (w u₀) := by
    by_cases h1 : 1 < w g
    · exact ⟨g, h1, hreg.trans (abs_of_pos (Real.log_pos h1))⟩
    · have hlt : w g < 1 := lt_of_le_of_ne (not_lt.mp h1) fun he ↦ hlog_ne (by simp [he])
      have hwInv : w (g⁻¹ : (𝓞 K)ˣ) = (w g)⁻¹ := by simp
      have hinv : 1 < w (g⁻¹ : (𝓞 K)ˣ) := by
        rw [hwInv]
        exact (one_lt_inv₀ hg_pos).mpr hlt
      refine ⟨g⁻¹, hinv, ?_⟩
      rw [hreg, abs_of_neg (Real.log_neg hg_pos hlt), hwInv, Real.log_inv]
  obtain ⟨ε, hε⟩ := w.exists_torsion_mul_embedding_eq_abs hw u₀
  exact ⟨ε.val * u₀, hε.symm ▸ hu₀_gt, hu₀_reg.trans (congrArg Real.log hε.symm)⟩

/-- In a real quadratic field (`0 < discr K`), a positive lower bound `B` valid at every real place
on units `u` with `1 < w(u)` gives `log B ≤ regulator K`. -/
private theorem log_le_regulator_of_zero_lt_discr (hK : finrank ℚ K = 2) (hd : 0 < discr K)
    {B : ℝ} (hB : 0 < B)
    (hle : ∀ (w : InfinitePlace K) (hw : w.IsReal) (u : (𝓞 K)ˣ),
      1 < embedding_of_isReal hw (u : K) → B ≤ embedding_of_isReal hw (u : K)) :
    Real.log B ≤ regulator K := by
  have : IsTotallyReal K := IsTotallyReal.of_zero_lt_discr hd (by omega)
  obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
  obtain ⟨u, hu, hreg⟩ :=
    exists_one_lt_embedding_of_isReal_and_regulator_eq_log (IsTotallyReal.isReal w) hK
  rw [hreg]
  exact Real.log_le_log hB (hle w (IsTotallyReal.isReal w) u hu)

/-- **Discriminant-dependent lower bound on the regulator of a quadratic field.** For any quadratic
field `K` of discriminant `D`, `log ((√D + √(D - 4)) / 2) ≤ regulator K`. For real quadratic fields
(`D > 0`) this bound is sharp (attained by `ℚ(√5)`); for imaginary quadratic fields (`D < 0`, where
`regulator K = 1`) it holds trivially because `Real.sqrt` evaluates to `0` on negative reals. -/
theorem log_sqrt_discr_add_sqrt_sub_four_div_two_le_regulator (hK : finrank ℚ K = 2) :
    Real.log ((√(discr K : ℝ) + √((discr K : ℝ) - 4)) / 2) ≤ regulator K := by
  rcases lt_or_gt_of_ne (discr_ne_zero K) with hneg | hpos
  · have hD0 : (discr K : ℝ) ≤ 0 := mod_cast hneg.le
    rw [Real.sqrt_eq_zero_of_nonpos hD0, Real.sqrt_eq_zero_of_nonpos (by linarith)]
    simpa using (regulator_pos K).le
  · have : 0 < √(discr K : ℝ) := Real.sqrt_pos.mpr (Int.cast_pos.mpr hpos)
    exact log_le_regulator_of_zero_lt_discr hK hpos (by positivity) fun _ hw _ hu ↦
      sqrt_discr_add_sqrt_sub_four_div_two_le_embedding_of_isReal hw hK hu

/-- **Regulator lower bound when no unit has norm `-1`.** If `K` is a quadratic field of
discriminant `D` in which every unit has norm `1`, then `log ((√(D + 4) + √D) / 2) ≤ regulator K`.
For real quadratic fields (`D > 0`) this bound is sharp (for instance for `ℚ(√3)`, `D = 12`); for
imaginary quadratic fields (`D < 0`, where `regulator K = 1`) it holds trivially because `Real.sqrt`
vanishes on nonpositive reals. -/
theorem log_sqrt_discr_add_four_add_sqrt_div_two_le_regulator (hK : finrank ℚ K = 2)
    (hnorm : ∀ u : (𝓞 K)ˣ, Algebra.norm ℚ (u : K) = 1) :
    Real.log ((√((discr K : ℝ) + 4) + √(discr K : ℝ)) / 2) ≤ regulator K := by
  rcases lt_or_gt_of_ne (discr_ne_zero K) with hneg | hpos
  · have hD1 : (discr K : ℝ) ≤ -1 := mod_cast Int.le_sub_one_of_lt hneg
    have hsqrt3 : √((discr K : ℝ) + 4) ≤ 2 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
    rw [Real.sqrt_eq_zero_of_nonpos (x := (discr K : ℝ)) (by linarith), add_zero]
    exact (Real.log_nonpos (by positivity) (by linarith)).trans (regulator_pos K).le
  · have : 0 < √(discr K : ℝ) := Real.sqrt_pos.mpr (Int.cast_pos.mpr hpos)
    exact log_le_regulator_of_zero_lt_discr hK hpos (by positivity) fun _ hw u hu ↦
      sqrt_discr_add_four_add_sqrt_div_two_le_embedding_of_isReal_of_norm_eq_one hw hK hu (hnorm u)

end TauCeti.NumberField.Units
