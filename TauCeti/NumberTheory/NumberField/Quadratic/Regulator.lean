/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Units.Regulator
public import Mathlib.NumberTheory.Real.GoldenRatio
public import TauCeti.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant
import TauCeti.NumberTheory.NumberField.Index.Discriminant
import TauCeti.NumberTheory.NumberField.Minpoly
import TauCeti.NumberTheory.NumberField.Units.Basic
import TauCeti.NumberTheory.NumberField.Units.PrimeDegree
import TauCeti.NumberTheory.NumberField.Units.Regulator.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Explicit lower bounds for the regulator of a real quadratic field

Let `K` be a real quadratic number field of discriminant `D`. Because `D` is a positive fundamental
discriminant and `K ≠ ℚ`, we have `5 ≤ D` (`five_le_discr_of_isTotallyReal`), attained by `ℚ(√5)`.

At any real infinite place `w`, every unit `u` of `𝓞 K` with `1 < w(u)` generates `K` over `ℚ`, so
the index formula `disc (minpoly ℤ u) = [𝓞 K : ℤ[u]]² · D` bounds the discriminant `(x - N(u)/x)²`
of `minpoly ℤ u` from below by `D`, where `x > 1` is the real image of `u` at `w` and
`N(u) ∈ {1, -1}` is the field norm of `u`. Solving this quadratic inequality gives:

* `(√D + √(D - 4)) / 2 ≤ x` unconditionally (`sqrt_discr_add_sqrt_sub_four_div_two_le_embedding`),
  attained when `N(u) = -1` and `[𝓞 K : ℤ[u]] = 1` (for instance `u = (1 + √5)/2` in `ℚ(√5)`);
* `(√(D + 4) + √D) / 2 ≤ x` whenever `N(u) = 1`
  (`sqrt_discr_add_four_add_sqrt_div_two_le_embedding_of_norm_eq_one`), attained for instance by
  `2 + √3` in `ℚ(√3)` (`D = 12`, `(√16 + √12)/2 = 2 + √3`).

Choosing `u` to be a normalized fundamental unit yields the corresponding sharp lower bounds on
`NumberField.Units.regulator K`, and substituting `5 ≤ D` (together with `regulator K = 1 > log φ`
in the imaginary quadratic case) gives the universal lower bound
`Real.log Real.goldenRatio ≤ regulator K` (`log_goldenRatio_le_regulator`) for every quadratic
field, with equality for `ℚ(√5)`.

## Main results

* `TauCeti.NumberField.five_le_discr_of_isTotallyReal`: a real quadratic field has discriminant
  at least `5`.
* `TauCeti.NumberField.Units.sqrt_discr_add_sqrt_sub_four_div_two_le_embedding`: any unit with
  real image `x > 1` at a real place satisfies `(√D + √(D - 4)) / 2 ≤ x`.
* `TauCeti.NumberField.Units.sqrt_discr_add_four_add_sqrt_div_two_le_embedding_of_norm_eq_one`:
  if moreover `N(u) = 1`, then `(√(D + 4) + √D) / 2 ≤ x`.
* `TauCeti.NumberField.Units.exists_one_lt_embedding_and_regulator_eq_log`: existence of a unit
  with real image `x > 1` at a real place `w` whose logarithm equals `regulator K`.
* `TauCeti.NumberField.Units.log_sqrt_discr_add_sqrt_sub_four_div_two_le_regulator`:
  `log ((√D + √(D - 4)) / 2) ≤ regulator K` for every quadratic field.
* `TauCeti.NumberField.Units.log_sqrt_discr_add_four_add_sqrt_div_two_le_regulator`: when every
  unit has norm `1`, `log ((√(D + 4) + √D) / 2) ≤ regulator K` for every quadratic field.
* `TauCeti.NumberField.Units.log_goldenRatio_le_regulator`: `log ((1 + √5) / 2) ≤ regulator K`
  for every quadratic field.

## References

* H. Cohen, *A Course in Computational Algebraic Number Theory*, Springer, 1993, §5.7.
* P. Koymans and C. Pagano, *A sharp upper bound for the 2-torsion of class groups of
  multiquadratic fields*, Mathematika **68** (2022), §7.2.
-/

public section

open Module NumberField NumberField.InfinitePlace NumberField.Units Polynomial
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **A real quadratic field has discriminant at least `5`.** Its discriminant is positive (Brill's
sign theorem with zero complex places) and equals `d` (for `d ≡ 1 (mod 4)`) or `4 d` (for
`d ≢ 1 (mod 4)`) for a nonsquare integer `d`. Equality holds for `ℚ(√5)`. -/
theorem five_le_discr_of_isTotallyReal [IsTotallyReal K] (hK : finrank ℚ K = 2) :
    5 ≤ discr K := by
  have hpos : 0 < discr K :=
    (InfinitePlace.even_nrComplexPlaces_iff_zero_lt_discr K).mp (by simp)
  obtain ⟨θ, d, hmin, hgen, hsf⟩ := exists_minpoly_eq_X_sq_sub_C_and_adjoin_eq_top hK
  have hd1 : d ≠ 1 := fun h ↦ not_isSquare_radicand hmin ⟨1, by simp [h]⟩
  rw [TauCeti.Multiquadratic.discr_eq_fundamentalDiscriminant hmin hgen hsf,
    TauCeti.Multiquadratic.fundamentalDiscriminant_def] at hpos ⊢
  split_ifs at hpos ⊢ <;> omega

namespace Units

/-- A quadratic field admitting a real infinite place is totally real. -/
private theorem isTotallyReal_of_isReal {w : InfinitePlace K} (hw : w.IsReal)
    (hK : finrank ℚ K = 2) : IsTotallyReal K := by
  classical
  have hdeg := InfinitePlace.card_add_two_mul_card_eq_rank K
  have hnr : 0 < nrRealPlaces K := Fintype.card_pos_iff.mpr ⟨⟨w, hw⟩⟩
  exact nrComplexPlaces_eq_zero_iff.mp (by omega)

/-- For a unit `u` with real image `x > 1` at a real place of a quadratic field, the index formula
gives `(discr K : ℝ) ≤ (x - N(u) / x) ^ 2`. -/
private theorem discr_le_sq_sub_norm_div_of_one_lt {w : InfinitePlace K} (hw : w.IsReal)
    (hK : finrank ℚ K = 2) {u : (𝓞 K)ˣ} (hu : 1 < embedding_of_isReal hw (u : K)) :
    (discr K : ℝ) ≤
      (embedding_of_isReal hw (u : K) -
        (Algebra.norm ℚ (u : K) : ℝ) / embedding_of_isReal hw (u : K)) ^ 2 := by
  have : IsTotallyReal K := isTotallyReal_of_isReal hw hK
  have hD5 : 5 ≤ discr K := five_le_discr_of_isTotallyReal hK
  set x : ℝ := embedding_of_isReal hw (u : K)
  have hx0 : 0 < x := zero_lt_one.trans hu
  have hut : u ∉ torsion K := fun h ↦ by
    have hw1 := (NumberField.Units.mem_torsion K).mp h w
    rw [← norm_embedding_of_isReal hw, Real.norm_eq_abs, abs_of_pos hx0] at hw1
    exact hu.ne' hw1
  let θ : IntegralPrimitiveElement K :=
    ⟨u, adjoin_eq_top_of_finrank_prime (hK ▸ Nat.prime_two) hut⟩
  set f : ℤ[X] := minpoly ℤ (u : 𝓞 K)
  have hmonic : f.Monic := minpoly.monic (u : 𝓞 K).isIntegral
  have hdegf : f.natDegree = 2 := by
    have h := θ.powerBasis.natDegree_minpoly
    rw [IntegralPrimitiveElement.powerBasis_gen, ← θ.powerBasis.finrank, hK,
      RingOfIntegers.minpoly_rat_coe,
      natDegree_map_eq_of_injective (algebraMap ℤ ℚ).injective_int] at h
    exact h
  have hc2 : f.coeff 2 = 1 := hdegf ▸ hmonic.coeff_natDegree
  have hc0 : (f.coeff 0 : ℝ) = Algebra.norm ℚ (u : K) := by
    have hpb := Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly θ.powerBasis
    have hdim : θ.powerBasis.dim = 2 := by rw [← θ.powerBasis.finrank, hK]
    rw [IntegralPrimitiveElement.powerBasis_gen, hdim, RingOfIntegers.minpoly_rat_coe,
      coeff_map, eq_intCast] at hpb
    exact_mod_cast (by simpa using hpb.symm : (f.coeff 0 : ℚ) = Algebra.norm ℚ (u : K))
  have hroot : x ^ 2 + (f.coeff 1 : ℝ) * x + (f.coeff 0 : ℝ) = 0 := by
    have ha := minpoly.aeval_algHom ℤ
      ((embedding_of_isReal hw).comp (algebraMap (𝓞 K) K)).toIntAlgHom (u : 𝓞 K)
    change aeval x f = 0 at ha
    rw [aeval_eq_sum_range, hdegf] at ha
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zsmul_eq_mul, hc2, Int.cast_one,
      pow_zero, pow_one, zero_add] at ha
    linarith
  have hfdiscr : (f.discr : ℝ) = (x - (f.coeff 0 : ℝ) / x) ^ 2 := by
    have hdeg2 : f.degree = 2 := by rw [degree_eq_natDegree hmonic.ne_zero, hdegf]; rfl
    rw [Polynomial.discr_eq_discrim_of_degree_eq_two hdeg2, discrim, hc2]
    push_cast
    have hm : (f.coeff 1 : ℝ) = -(x + (f.coeff 0 : ℝ) / x) := by field_simp [hx0.ne']; linarith
    rw [hm]; field_simp [hx0.ne']; ring
  have hidx : discr K ≤ f.discr := by
    rw [θ.discr_minpoly_eq_index_sq_mul_discr]
    have h1 : (1 : ℤ) ≤ (θ.index : ℤ) ^ 2 := by
      have : (1 : ℤ) ≤ θ.index := mod_cast θ.index_pos
      nlinarith
    nlinarith
  rw [← hc0, ← hfdiscr]
  exact_mod_cast hidx

/-- **Norm-one unit lower bound in a real quadratic field.** If `u` is a unit of norm `1` whose
real image at `w` exceeds `1`, then `(√(D + 4) + √D) / 2 ≤ w(u)`, where `D = discr K`. -/
theorem sqrt_discr_add_four_add_sqrt_div_two_le_embedding_of_norm_eq_one {w : InfinitePlace K}
    (hw : w.IsReal) (hK : finrank ℚ K = 2) {u : (𝓞 K)ˣ}
    (hu : 1 < embedding_of_isReal hw (u : K)) (hnorm : Algebra.norm ℚ (u : K) = 1) :
    (√((discr K : ℝ) + 4) + √(discr K : ℝ)) / 2 ≤ embedding_of_isReal hw (u : K) := by
  have hsq := discr_le_sq_sub_norm_div_of_one_lt hw hK hu
  rw [hnorm, Rat.cast_one] at hsq
  set x := embedding_of_isReal hw (u : K)
  have hx0 : 0 < x := zero_lt_one.trans hu
  have hsub_pos : 0 ≤ x - 1 / x := by
    rw [le_sub_iff_add_le, zero_add, div_le_iff₀ hx0]
    nlinarith
  have h1 : √(discr K : ℝ) ≤ x - 1 / x := Real.sqrt_le_iff.mpr ⟨hsub_pos, hsq⟩
  have hadd_sq : (discr K : ℝ) + 4 ≤ (x + 1 / x) ^ 2 := by
    have hid : (x + 1 / x) ^ 2 = (x - 1 / x) ^ 2 + 4 := by field_simp [hx0.ne']; ring
    linarith
  have h2 : √((discr K : ℝ) + 4) ≤ x + 1 / x :=
    Real.sqrt_le_iff.mpr ⟨by positivity, hadd_sq⟩
  linarith

/-- **Sharp discriminant-dependent unit lower bound in a real quadratic field.** Every unit `u`
whose real image at `w` exceeds `1` satisfies `(√D + √(D - 4)) / 2 ≤ w(u)`, where `D = discr K`. -/
theorem sqrt_discr_add_sqrt_sub_four_div_two_le_embedding {w : InfinitePlace K} (hw : w.IsReal)
    (hK : finrank ℚ K = 2) {u : (𝓞 K)ˣ} (hu : 1 < embedding_of_isReal hw (u : K)) :
    (√(discr K : ℝ) + √((discr K : ℝ) - 4)) / 2 ≤ embedding_of_isReal hw (u : K) := by
  have : IsTotallyReal K := isTotallyReal_of_isReal hw hK
  have : (5 : ℝ) ≤ discr K := mod_cast five_le_discr_of_isTotallyReal hK
  have hsq := discr_le_sq_sub_norm_div_of_one_lt hw hK hu
  rcases (abs_eq (zero_le_one' ℚ)).mp (NumberField.Units.norm K u) with h1 | hneg1
  · refine le_trans ?_
      (sqrt_discr_add_four_add_sqrt_div_two_le_embedding_of_norm_eq_one hw hK hu h1)
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
    have hsub_pos : 0 ≤ x - 1 / x := by
      rw [le_sub_iff_add_le, zero_add, div_le_iff₀ hx0]
      nlinarith
    have hsub_sq : (discr K : ℝ) - 4 ≤ (x - 1 / x) ^ 2 := by
      have hid : (x - 1 / x) ^ 2 = (x + 1 / x) ^ 2 - 4 := by field_simp [hx0.ne']; ring
      linarith
    have h2 : √((discr K : ℝ) - 4) ≤ x - 1 / x := Real.sqrt_le_iff.mpr ⟨hsub_pos, hsub_sq⟩
    linarith

/-- **Normalized fundamental unit of a real quadratic field.** At any real infinite place `w` of a
quadratic field `K`, there exists a unit `u` whose real image exceeds `1` and whose logarithm is
`regulator K`. -/
theorem exists_one_lt_embedding_and_regulator_eq_log {w : InfinitePlace K} (hw : w.IsReal)
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
  exact ⟨ε.1 * u₀, hε.symm ▸ hu₀_gt, hu₀_reg.trans (congrArg Real.log hε.symm)⟩

/-- **Sharp discriminant-dependent lower bound on the regulator of a quadratic field.** For any
quadratic field `K` of discriminant `D`, `log ((√D + √(D - 4)) / 2) ≤ regulator K`. -/
theorem log_sqrt_discr_add_sqrt_sub_four_div_two_le_regulator (hK : finrank ℚ K = 2) :
    Real.log ((√(discr K : ℝ) + √((discr K : ℝ) - 4)) / 2) ≤ regulator K := by
  rcases lt_or_ge (discr K) 0 with hneg | hnonneg
  · have hD0 : (discr K : ℝ) ≤ 0 := mod_cast hneg.le
    rw [Real.sqrt_eq_zero_of_nonpos hD0, Real.sqrt_eq_zero_of_nonpos (by linarith)]
    simpa using (regulator_pos K).le
  · have hpos_discr : 0 < discr K := lt_of_le_of_ne hnonneg (discr_ne_zero K).symm
    have : IsTotallyReal K := IsTotallyReal.of_zero_lt_discr hpos_discr (by omega)
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    obtain ⟨u, hu, hreg⟩ := exists_one_lt_embedding_and_regulator_eq_log (IsTotallyReal.isReal w) hK
    have hD5 : (5 : ℝ) ≤ discr K := mod_cast five_le_discr_of_isTotallyReal hK
    have hpos : 0 < (√(discr K : ℝ) + √((discr K : ℝ) - 4)) / 2 := by
      have : 0 < √(discr K : ℝ) := Real.sqrt_pos.mpr (by linarith)
      positivity
    rw [hreg]
    exact Real.log_le_log hpos (sqrt_discr_add_sqrt_sub_four_div_two_le_embedding _ hK hu)

/-- **Improved regulator lower bound when no unit has norm `-1`.** If `K` is a quadratic field of
discriminant `D` in which every unit has norm `1`, then
`log ((√(D + 4) + √D) / 2) ≤ regulator K`. -/
theorem log_sqrt_discr_add_four_add_sqrt_div_two_le_regulator (hK : finrank ℚ K = 2)
    (hnorm : ∀ u : (𝓞 K)ˣ, Algebra.norm ℚ (u : K) = 1) :
    Real.log ((√((discr K : ℝ) + 4) + √(discr K : ℝ)) / 2) ≤ regulator K := by
  rcases lt_or_ge (discr K) 0 with hneg | hnonneg
  · have hD1 : (discr K : ℝ) ≤ -1 := mod_cast Int.le_sub_one_of_lt hneg
    have hsqrt3 : √((discr K : ℝ) + 4) ≤ 2 := by
      rw [show (2 : ℝ) = √4 by norm_num]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_eq_zero_of_nonpos (x := (discr K : ℝ)) (by linarith), add_zero]
    exact (Real.log_nonpos (by positivity) (by linarith)).trans (regulator_pos K).le
  · have hpos_discr : 0 < discr K := lt_of_le_of_ne hnonneg (discr_ne_zero K).symm
    have : IsTotallyReal K := IsTotallyReal.of_zero_lt_discr hpos_discr (by omega)
    obtain ⟨w⟩ := (inferInstance : Nonempty (InfinitePlace K))
    obtain ⟨u, hu, hreg⟩ := exists_one_lt_embedding_and_regulator_eq_log (IsTotallyReal.isReal w) hK
    have hD5 : (5 : ℝ) ≤ discr K := mod_cast five_le_discr_of_isTotallyReal hK
    have hpos : 0 < (√((discr K : ℝ) + 4) + √(discr K : ℝ)) / 2 := by
      have : 0 < √(discr K : ℝ) := Real.sqrt_pos.mpr (by linarith)
      positivity
    rw [hreg]
    exact Real.log_le_log hpos
      (sqrt_discr_add_four_add_sqrt_div_two_le_embedding_of_norm_eq_one _ hK hu (hnorm u))

/-- **Universal lower bound on the regulator of a quadratic field.** Every quadratic field `K`
satisfies `Real.log Real.goldenRatio ≤ regulator K`, with equality for `ℚ(√5)`. -/
theorem log_goldenRatio_le_regulator (hK : finrank ℚ K = 2) :
    Real.log Real.goldenRatio ≤ regulator K := by
  rcases lt_or_ge (discr K) 0 with hneg | hnonneg
  · have hdeg := InfinitePlace.card_add_two_mul_card_eq_rank K
    have hc : nrComplexPlaces K = 1 :=
      InfinitePlace.nrComplexPlaces_eq_one_of_discr_lt_zero hneg (by omega)
    have : IsTotallyComplex K := nrRealPlaces_eq_zero_iff.mp (by omega)
    rw [regulator_eq_one_of_isTotallyComplex_of_finrank_eq_two K hK]
    have hsqrt5 : √5 < 3 := (Real.sqrt_lt' (by norm_num)).mpr (by norm_num)
    have hlog := Real.log_le_sub_one_of_pos Real.goldenRatio_pos
    rw [Real.goldenRatio] at hlog ⊢
    linarith
  · have hpos_discr : 0 < discr K := lt_of_le_of_ne hnonneg (discr_ne_zero K).symm
    have : IsTotallyReal K := IsTotallyReal.of_zero_lt_discr hpos_discr (by omega)
    refine le_trans ?_ (log_sqrt_discr_add_sqrt_sub_four_div_two_le_regulator hK)
    refine Real.log_le_log Real.goldenRatio_pos ?_
    have hD5 : (5 : ℝ) ≤ discr K := mod_cast five_le_discr_of_isTotallyReal hK
    have hs5 : √5 ≤ √(discr K : ℝ) := Real.sqrt_le_sqrt hD5
    have hs1 : (1 : ℝ) ≤ √((discr K : ℝ) - 4) := by
      rw [show (1 : ℝ) = √1 by norm_num]
      exact Real.sqrt_le_sqrt (by linarith)
    rw [Real.goldenRatio]
    linarith

end Units

end TauCeti.NumberField
