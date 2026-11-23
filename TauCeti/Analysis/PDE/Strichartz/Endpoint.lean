/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Strichartz.TimeShell
public import TauCeti.MeasureTheory.Function.Lp.DyadicLayer
import TauCeti.Analysis.InnerProductSpace.CotlarStein
import TauCeti.Analysis.SpecificLimits.DyadicSum
import TauCeti.MeasureTheory.Function.Lorentz
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Integral.SchurTest

/-!
# The endpoint Strichartz estimate of Keel and Tao

Let `U(t) : H → L²(X, μ)`, `t ∈ ℝ`, be bounded operators, `‖U(t)‖ ≤ M`, whose time pairings
satisfy the dispersive estimate with a decay rate `σ > 1`,

`‖U(s) U(t)* g‖_∞ ≤ A |s - t| ^ (-σ) ‖g‖₁`,  `s ≠ t`,

and suppose a non-endpoint dual Strichartz estimate `‖∫ U(t)* G(t) dt‖ ≤ K ‖G‖_{L^p_t L^b_x}` is
known, with `1 / b ∈ (1/2, 1/r')` and `1 / p = 1 + σ / 2 - σ / b`, where `r'` is the dual
endpoint exponent, `1 / r' = (σ + 1) / (2σ)`. This file proves the **endpoint dual estimate**

`‖∫ U(t)* F(t) dt‖ ≤ C ‖F‖_{L²_t L^{r'}_x}`

(`TauCeti.exists_enorm_integral_adjoint_le_of_endpoint`), the dual form of the endpoint estimate
`‖U(·) f‖_{L²_t L^r_x} ≤ C ‖f‖`, `1/r + 1/r' = 1`. At the endpoint `q = 2` the time
kernel `|s - t| ^ (-1)` of the `TT*` argument is not integrable, and the Hardy–Littlewood–Sobolev
inequality of the non-endpoint case (`TauCeti.Analysis.PDE.Strichartz.TTStar`) fails.

## The argument

This is the argument of Keel and Tao. They combine three bounds on dyadic time shells by bilinear
real interpolation; here that step is replaced by an atomic decomposition of the Lorentz space
`L^{r',2}` at each time, which leads to the same exponent bookkeeping. By `TT*`,
`‖∫ U(t)* F(t) dt‖² = T(F, F)` for the bilinear form `T(F, G) = ∫∫ ⟪U(s)* F(s), U(t)* G(t)⟫`.

* **Atoms.** At every time, `F(t)` is decomposed into its dyadic layers
  `F(t) = ∑ₖ Fₖ(t)` (`MeasureTheory.Lp.dyadicLayer`): `Fₖ(t)` is bounded by the level
  `aₖ(t) = f*(2ᵏ)` of the decreasing rearrangement of `‖F(t)‖` and supported on a set of measure
  at most `2ᵏ⁺¹`, so `‖Fₖ(t)‖_s ≤ 2^{(k+1)/s} aₖ(t)` for every exponent `s`. Write
  `Xₖ = ‖aₖ‖_{L²_t}`.
* **Three bounds on a dyadic time shell.** On the shell `2ʲ ≤ |s - t| < 2ʲ⁺¹`, the pairing
  `Tⱼ(Fₖ, Fₗ)` is bounded by the dispersive estimate in `L²_t L¹_x`, and by the energy estimate
  together with the non-endpoint dual estimate in `L²_t L²_x × L²_t L^b_x` and in
  `L²_t L^b_x × L²_t L²_x` (`TauCeti.Analysis.PDE.Strichartz.TimeShell`). With the atom bounds,
  the three bounds are `2^{eᵢ(j, k, l)} Xₖ Xₗ` up to constants, with exponents affine in
  `(j, k, l)`.
* **Exponent bookkeeping.** With `u = k - σ j` and `v = l - σ j`, the smallest of the three
  exponents is at most `(k + l) / r' - δ (|u| + |v|)` for some `δ > 0`: the dispersive exponent
  wins when `u, v ≤ 0`, an energy exponent when `u, v ≥ 0`, and a convex combination of the
  dispersive exponent and an energy exponent when `u` and `v` have opposite signs. This is where
  `σ > 1` and the strict non-endpoint condition on `b` enter.
* **Summation.** Summing over the shells `j` gives `2^{(k + l)/r'} 2^{-δ|k - l|/2} Xₖ Xₗ`, and
  Schur's test on `ℤ` bounds the double sum over `k, l` by `∑ₖ (2^{k/r'} Xₖ)²`. This is the
  square of an `L²_t` norm of the dyadic discretization of the Lorentz gauge `‖F(t)‖_{r',2}`, which
  is at most `‖F(t)‖_{r'}` since `r' ≤ 2`
  (`TauCeti.tsum_rpow_mul_decreasingRearrangement_sq_le`).

Truncating the layer decomposition at `|k| ≤ N` and letting `N → ∞` by dominated convergence
transfers the bound from the finite sums of atoms to `F`.

## Main declarations

* `TauCeti.exists_min_exponent_le`: the exponent bookkeeping of Keel and Tao.
* `TauCeti.levelNorm`: the `L²` norm in time of the level `f*(2ᵏ)` of `F(t)`, which bounds the
  mixed norms of the layers (`TauCeti.eLpNorm_eLpNorm_dyadicLayer_le`) and is square summable after
  normalization (`TauCeti.tsum_sq_two_rpow_mul_levelNorm_le`).
* `TauCeti.tsum_enorm_setIntegral_timeShell_dyadicLayer_le`: the pairings of two atoms summed over
  the dyadic time shells.
* `TauCeti.exists_enorm_integral_adjoint_le_of_endpoint`: the endpoint dual estimate.
* `TauCeti.exists_enorm_integral_adjoint_le_of_endpoint_of_four_thirds`: the same estimate from
  a non-endpoint dual estimate in `L^{4/3}_t`.

## References

* M. Keel and T. Tao, *Endpoint Strichartz estimates*, Amer. J. Math. 120 (1998), 955–980.
* T. Tao, *Nonlinear Dispersive Equations: Local and Global Analysis*, CBMS Regional Conference
  Series in Mathematics 106, AMS, 2006, Section 2.3.
-/

public section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal InnerProductSpace InnerProduct

namespace TauCeti

/-! ### Exponent bookkeeping -/

/-- With `u = k - σ j`, `v = l - σ j`, the three exponent excesses over `(k + l) / r'` are
`γ (u + v)`, `-η u - κ v` and `-κ u - η v`, where `γ, η, κ > 0`. Their minimum is at most
`-δ (|u| + |v|)`, a negative multiple of `|u| + |v|` when moreover `κ < η`. -/
private theorem min_le_neg_mul_abs_add_abs {γ η κ : ℝ} (hγ : 0 < γ) (hη : 0 < η) (hκ : 0 < κ)
    (u v : ℝ) :
    min (γ * (u + v)) (min (-(η * u) - κ * v) (-(κ * u) - η * v)) ≤
      -(min (min γ (min η κ)) (γ * (η - κ) / (κ + η + 2 * γ)) * (|u| + |v|)) := by
  set δ := min (min γ (min η κ)) (γ * (η - κ) / (κ + η + 2 * γ))
  have hδγ : δ ≤ γ := (min_le_left _ _).trans (min_le_left _ _)
  have hδη : δ ≤ η := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδκ : δ ≤ κ := (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hδ₃ : δ ≤ γ * (η - κ) / (κ + η + 2 * γ) := min_le_right _ _
  have hw : 0 < κ + η + 2 * γ := by positivity
  -- For `u ≥ 0 ≥ v`, a convex combination of the dispersive and an energy exponent.
  have hmix (u v : ℝ) (hu : 0 ≤ u) (hv : v ≤ 0) (m : ℝ) (h0 : m ≤ γ * (u + v))
      (h1 : m ≤ -(η * u) - κ * v) : m ≤ -(δ * (|u| + |v|)) := by
    have hsum : (κ + η + 2 * γ) * m ≤ -(γ * (η - κ)) * (u - v) := by
      nlinarith [mul_le_mul_of_nonneg_left h0 (by positivity : (0 : ℝ) ≤ κ + η),
        mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * γ)]
    have hm : m ≤ -(γ * (η - κ) / (κ + η + 2 * γ)) * (u - v) := by
      rw [show -(γ * (η - κ) / (κ + η + 2 * γ)) * (u - v) =
        -(γ * (η - κ)) * (u - v) / (κ + η + 2 * γ) by ring, le_div_iff₀ hw, mul_comm]
      exact hsum
    rw [abs_of_nonneg hu, abs_of_nonpos hv]
    nlinarith [mul_le_mul_of_nonneg_right hδ₃ (by linarith : (0 : ℝ) ≤ u - v)]
  rcases le_total 0 u with hu | hu <;> rcases le_total 0 v with hv | hv
  · -- `u, v ≥ 0`: an energy exponent.
    refine (min_le_right _ _).trans ((min_le_left _ _).trans ?_)
    rw [abs_of_nonneg hu, abs_of_nonneg hv]
    nlinarith [mul_le_mul_of_nonneg_right hδη hu, mul_le_mul_of_nonneg_right hδκ hv]
  · exact hmix u v hu hv _ (min_le_left _ _) ((min_le_right _ _).trans (min_le_left _ _))
  · have h := hmix v u hv hu (min (γ * (u + v)) (min (-(η * u) - κ * v) (-(κ * u) - η * v)))
      ((min_le_left _ _).trans_eq (by ring))
      (((min_le_right _ _).trans (min_le_right _ _)).trans_eq (by ring))
    rwa [add_comm |v|] at h
  · -- `u, v ≤ 0`: the dispersive exponent.
    refine (min_le_left _ _).trans ?_
    rw [abs_of_nonpos hu, abs_of_nonpos hv]
    nlinarith [mul_le_mul_of_nonneg_right hδγ (by linarith : (0 : ℝ) ≤ -u - v)]

/-- **The exponent bookkeeping of Keel and Tao.** Let `σ > 1` and `1/2 < β < (σ + 1) / (2σ)`, and
put `π = 1 + σ / 2 - σ β`. There is `δ > 0` such that for all `j, k, l`, the smallest of the
dispersive exponent `(1 - σ) j + k + l` and the two energy exponents `π j + k / 2 + β l`,
`π j + β k + l / 2` is at most `(σ + 1) / (2σ) (k + l) - δ (|k - σ j| + |l - σ j|)`. -/
theorem exists_min_exponent_le {σ β : ℝ} (hσ : 1 < σ) (hβ : 2⁻¹ < β)
    (hβσ : β < (σ + 1) / (2 * σ)) :
    ∃ δ > 0, ∀ j k l : ℝ,
      min ((1 - σ) * j + k + l) (min ((1 + σ / 2 - σ * β) * j + k / 2 + β * l)
        ((1 + σ / 2 - σ * β) * j + β * k + l / 2)) ≤
      (σ + 1) / (2 * σ) * (k + l) - δ * (|k - σ * j| + |l - σ * j|) := by
  set γ := (σ - 1) / (2 * σ)
  set η := 1 / (2 * σ)
  set κ := (σ + 1) / (2 * σ) - β
  have hγ : 0 < γ := div_pos (by linarith) (by positivity)
  have hη : 0 < η := by positivity
  have hκ : 0 < κ := sub_pos.2 hβσ
  have hκη : κ < η := by
    have : η - κ = β - 2⁻¹ := by simp only [η, κ]; field_simp; ring
    linarith
  refine ⟨min (min γ (min η κ)) (γ * (η - κ) / (κ + η + 2 * γ)),
    lt_min (lt_min hγ (lt_min hη hκ)) (by have := sub_pos.2 hκη; positivity), fun j k l ↦ ?_⟩
  set D := (σ + 1) / (2 * σ) * (k + l)
  have h0 : (1 - σ) * j + k + l = D + γ * ((k - σ * j) + (l - σ * j)) := by
    simp only [D, γ]; field_simp; ring
  have h1 : (1 + σ / 2 - σ * β) * j + k / 2 + β * l =
      D + (-(η * (k - σ * j)) - κ * (l - σ * j)) := by
    simp only [D, η, κ]; field_simp; ring
  have h2 : (1 + σ / 2 - σ * β) * j + β * k + l / 2 =
      D + (-(κ * (k - σ * j)) - η * (l - σ * j)) := by
    simp only [D, η, κ]; field_simp; ring
  rw [h0, h1, h2, min_add_add_left, min_add_add_left]
  have := min_le_neg_mul_abs_add_abs hγ hη hκ (k - σ * j) (l - σ * j)
  linarith

variable {𝕜 : Type*} [RCLike 𝕜]

/-! ### Atoms on dyadic time shells -/

variable {X E H : Type*} {mX : MeasurableSpace X} {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]

/-- The `L²` norm in time of the level `f*(2ᵏ)` of the decreasing rearrangement of `‖F(t)‖`. -/
noncomputable def levelNorm (μ : Measure X) (F : ℝ → Lp E 2 μ) (k : ℤ) : ℝ≥0∞ :=
  eLpNorm (fun t ↦ μ.decreasingRearrangement (fun x ↦ ‖F t x‖ₑ) ((2 : ℝ) ^ k)) 2

omit [CompleteSpace E] [NormedSpace ℝ E] in
theorem levelNorm_def (μ : Measure X) (F : ℝ → Lp E 2 μ) (k : ℤ) :
    levelNorm μ F k =
      eLpNorm (fun t ↦ μ.decreasingRearrangement (fun x ↦ ‖F t x‖ₑ) ((2 : ℝ) ^ k)) 2 := (rfl)

private theorem ofReal_two_zpow (m : ℤ) : ENNReal.ofReal ((2 : ℝ) ^ m) = (2 : ℝ≥0∞) ^ (m : ℝ) := by
  rw [← Real.rpow_intCast, ← ENNReal.ofReal_rpow_of_pos two_pos, ENNReal.ofReal_ofNat]

private theorem two_rpow_mul_two_rpow (a b : ℝ) : (2 : ℝ≥0∞) ^ a * 2 ^ b = 2 ^ (a + b) :=
  (ENNReal.rpow_add _ _ two_ne_zero ENNReal.ofNat_ne_top).symm

omit [CompleteSpace E] in
/-- The mixed norm `L²_t L^s_x` of the `k`-th dyadic layers of `F` is at most
`2^{(k+1)/s} ‖f*(2ᵏ)‖_{L²_t}`. -/
theorem eLpNorm_eLpNorm_dyadicLayer_le {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F)
    (k : ℤ) (s : ℝ≥0∞) :
    eLpNorm (fun t ↦ eLpNorm (Lp.dyadicLayer k (F t)) s μ) 2 ≤
      2 ^ (((k : ℝ) + 1) * s.toReal⁻¹) * levelNorm μ F k := by
  rw [levelNorm_def, ← eLpNorm_const_mul_ennreal_of_pos (by norm_num : (0 : ℝ≥0∞) < 2)]
  refine eLpNorm_mono_eNorm ((hF.dyadicLayer k).aemeasurable_eLpNorm_Lp .rfl s).aestronglyMeasurable
    fun t ↦ ?_
  simp only [eNorm_eq_self]
  refine (Lp.eLpNorm_dyadicLayer_le two_ne_zero k (F t) s).trans_eq ?_
  rw [ofReal_two_zpow, ← ENNReal.rpow_mul, Int.cast_add, Int.cast_one]

omit [CompleteSpace E] [NormedSpace ℝ E] in
/-- The normalized level norms are square summable, with sum controlled by the mixed norm
`L²_t L^{r'}_x` of `F`, for `r' ≤ 2`. -/
theorem tsum_sq_two_rpow_mul_levelNorm_le {r' : ℝ≥0∞} (hr'0 : r' ≠ 0) (hr'2 : r' ≤ 2)
    {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) :
    ∑' k : ℤ, (2 ^ ((k : ℝ) * r'.toReal⁻¹) * levelNorm μ F k) ^ 2 ≤
      ENNReal.ofReal (2 ^ (2 / r'.toReal) / Real.log 2) *
        eLpNorm (fun t ↦ eLpNorm (F t) r' μ) 2 ^ 2 := by
  set a : ℤ → ℝ → ℝ≥0∞ := fun k t ↦ μ.decreasingRearrangement (fun x ↦ ‖F t x‖ₑ) ((2 : ℝ) ^ k)
  have ha (k : ℤ) : AEMeasurable (a k) := hF.aemeasurable_decreasingRearrangement_enorm _
  have hsq (k : ℤ) : (2 ^ ((k : ℝ) * r'.toReal⁻¹) * levelNorm μ F k) ^ 2 =
      ∫⁻ t, (ENNReal.ofReal ((2 : ℝ) ^ k) ^ r'.toReal⁻¹ * a k t) ^ (2 : ℝ) := by
    rw [levelNorm_def, ← eLpNorm_const_mul_ennreal_of_pos (by norm_num : (0 : ℝ≥0∞) < 2),
      eLpNorm_two_sq_eq_lintegral_sq ((ha k).const_mul _), ofReal_two_zpow, ← ENNReal.rpow_mul]
    simp_rw [ENNReal.rpow_two]
  calc _ = ∑' k : ℤ, ∫⁻ t, (ENNReal.ofReal ((2 : ℝ) ^ k) ^ r'.toReal⁻¹ * a k t) ^ (2 : ℝ) :=
        tsum_congr hsq
    _ = ∫⁻ t, ∑' k : ℤ, (ENNReal.ofReal ((2 : ℝ) ^ k) ^ r'.toReal⁻¹ * a k t) ^ (2 : ℝ) :=
        (lintegral_tsum fun k ↦ ((ha k).const_mul _).pow_const _).symm
    _ ≤ ∫⁻ t, ENNReal.ofReal (2 ^ (2 / r'.toReal) / Real.log 2) * eLpNorm (F t) r' μ ^ (2 : ℝ) :=
        lintegral_mono fun t ↦
          tsum_rpow_mul_decreasingRearrangement_sq_le (Lp.aestronglyMeasurable (F t)) hr'0 hr'2
    _ = _ := by
        rw [lintegral_const_mul'' _ ((hF.aemeasurable_eLpNorm_Lp .rfl r').pow_const _),
          eLpNorm_two_sq_eq_lintegral_sq (hF.aemeasurable_eLpNorm_Lp .rfl r')]
        simp_rw [ENNReal.rpow_two]

section Shell

private theorem ofReal_two_mul_two_zpow (j : ℤ) :
    ENNReal.ofReal (2 * (2 : ℝ) ^ j) = 2 ^ ((1 : ℝ) + j) := by
  rw [← zpow_one_add₀ two_ne_zero, ofReal_two_zpow, Int.cast_add, Int.cast_one]

/-- The dispersive bound for two atoms on a dyadic time shell, in `L²_t L¹_x`. -/
private theorem enorm_setIntegral_timeShell_dyadicLayer_le_dispersive {σ : ℝ} (hσ : 1 < σ)
    {U : ℝ → H →L[𝕜] Lp E 2 μ} {A : ℝ≥0}
    (hD : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) ∞ μ ≤ A * ‖s - t‖ₑ ^ (-σ) * eLpNorm g 1 μ)
    {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F) (j k l : ℤ) :
    ‖∫ z in timeShell ((2 : ℝ) ^ j), ⟪((U z.1)†) (Lp.dyadicLayer k (F z.1)),
        ((U z.2)†) (Lp.dyadicLayer l (F z.2))⟫_𝕜 ∂(volume.prod volume)‖ₑ ≤
      16 * A * 2 ^ ((1 - σ) * j + k + l) * (levelNorm μ F k * levelNorm μ F l) := by
  refine (eNorm_integral_le_lintegral_eNorm _).trans
    ((setLIntegral_timeShell_enorm_inner_adjoint_le (r := ∞) (r' := 1)
      (by linarith : (0 : ℝ) ≤ σ) _ hD (hF.dyadicLayer k) (hF.dyadicLayer l)).trans ?_)
  have h4 : (4 : ℝ≥0∞) = 2 ^ (2 : ℝ) := by rw [ENNReal.rpow_two]; norm_num
  have h16 : (16 : ℝ≥0∞) = 2 ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast]; norm_num
  have he : (2 : ℝ≥0∞) ^ (2 : ℝ) * 2 ^ ((j : ℝ) * (1 - σ)) * 2 ^ (((k : ℝ) + 1) * 1) *
      2 ^ (((l : ℝ) + 1) * 1) = 2 ^ (4 : ℝ) * 2 ^ ((1 - σ) * j + k + l) := by
    simp only [two_rpow_mul_two_rpow]; congr 1; ring
  calc _ ≤ 4 * A * ENNReal.ofReal ((2 : ℝ) ^ j) ^ (1 - σ) *
        (2 ^ (((k : ℝ) + 1) * (1 : ℝ≥0∞).toReal⁻¹) * levelNorm μ F k) *
        (2 ^ (((l : ℝ) + 1) * (1 : ℝ≥0∞).toReal⁻¹) * levelNorm μ F l) := by
        gcongr <;> exact eLpNorm_eLpNorm_dyadicLayer_le hF _ 1
    _ = A * (levelNorm μ F k * levelNorm μ F l) * (2 ^ (2 : ℝ) * 2 ^ ((j : ℝ) * (1 - σ)) *
        2 ^ (((k : ℝ) + 1) * 1) * 2 ^ (((l : ℝ) + 1) * 1)) := by
        rw [ofReal_two_zpow, ← ENNReal.rpow_mul, h4, ENNReal.toReal_one, inv_one]; ring
    _ = _ := by rw [he, h16]; ring

variable [NormedSpace ℝ H]

/-- The bound for two atoms on a dyadic time shell with an energy factor on the first one, in
`L²_t L²_x × L²_t L^b_x`. -/
private theorem enorm_setIntegral_timeShell_dyadicLayer_le_energy {p b : ℝ≥0∞} (hp2 : p ≤ 2)
    {U : ℝ → H →L[𝕜] Lp E 2 μ} {M K : ℝ≥0} (hM : ∀ t, ‖U t‖ₑ ≤ M)
    (hK : ∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G → Integrable (fun t ↦ ((U t)†) (G t)) →
      ‖∫ t, ((U t)†) (G t)‖ₑ ≤ K * eLpNorm (fun t ↦ eLpNorm (G t) b μ) p)
    {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F)
    (hUF : ∀ k, Integrable fun t ↦ ((U t)†) (Lp.dyadicLayer k (F t))) (j k l : ℤ) :
    ‖∫ z in timeShell ((2 : ℝ) ^ j), ⟪((U z.1)†) (Lp.dyadicLayer k (F z.1)),
        ((U z.2)†) (Lp.dyadicLayer l (F z.2))⟫_𝕜 ∂(volume.prod volume)‖ₑ ≤
      2 ^ (p.toReal⁻¹ + 2⁻¹ + b.toReal⁻¹) * M * K *
        2 ^ (p.toReal⁻¹ * j + k / 2 + b.toReal⁻¹ * l) * (levelNorm μ F k * levelNorm μ F l) := by
  refine (enorm_setIntegral_timeShell_inner_adjoint_le hp2 _ hM hK (hF.dyadicLayer k)
    (hF.dyadicLayer l) (hUF k) (hUF l)).trans ?_
  have he : (2 : ℝ≥0∞) ^ (((1 : ℝ) + j) * p.toReal⁻¹) * 2 ^ (((k : ℝ) + 1) * 2⁻¹) *
      2 ^ (((l : ℝ) + 1) * b.toReal⁻¹) =
        2 ^ (p.toReal⁻¹ + 2⁻¹ + b.toReal⁻¹) * 2 ^ (p.toReal⁻¹ * j + k / 2 + b.toReal⁻¹ * l) := by
    simp only [two_rpow_mul_two_rpow]; congr 1; ring
  calc _ ≤ M * K * ENNReal.ofReal (2 * (2 : ℝ) ^ j) ^ p.toReal⁻¹ *
        (2 ^ (((k : ℝ) + 1) * (2 : ℝ≥0∞).toReal⁻¹) * levelNorm μ F k) *
        (2 ^ (((l : ℝ) + 1) * b.toReal⁻¹) * levelNorm μ F l) := by
        gcongr <;> exact eLpNorm_eLpNorm_dyadicLayer_le hF _ _
    _ = M * K * (levelNorm μ F k * levelNorm μ F l) * (2 ^ (((1 : ℝ) + j) * p.toReal⁻¹) *
        2 ^ (((k : ℝ) + 1) * 2⁻¹) * 2 ^ (((l : ℝ) + 1) * b.toReal⁻¹)) := by
        rw [ofReal_two_mul_two_zpow, ← ENNReal.rpow_mul, ENNReal.toReal_ofNat]; ring
    _ = _ := by rw [he]; ring

/-- The bound for two atoms on a dyadic time shell with an energy factor on the second one, in
`L²_t L^b_x × L²_t L²_x`. -/
private theorem enorm_setIntegral_timeShell_dyadicLayer_le_energy' {p b : ℝ≥0∞} (hp2 : p ≤ 2)
    {U : ℝ → H →L[𝕜] Lp E 2 μ} {M K : ℝ≥0} (hM : ∀ t, ‖U t‖ₑ ≤ M)
    (hK : ∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G → Integrable (fun t ↦ ((U t)†) (G t)) →
      ‖∫ t, ((U t)†) (G t)‖ₑ ≤ K * eLpNorm (fun t ↦ eLpNorm (G t) b μ) p)
    {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F)
    (hUF : ∀ k, Integrable fun t ↦ ((U t)†) (Lp.dyadicLayer k (F t))) (j k l : ℤ) :
    ‖∫ z in timeShell ((2 : ℝ) ^ j), ⟪((U z.1)†) (Lp.dyadicLayer k (F z.1)),
        ((U z.2)†) (Lp.dyadicLayer l (F z.2))⟫_𝕜 ∂(volume.prod volume)‖ₑ ≤
      2 ^ (p.toReal⁻¹ + 2⁻¹ + b.toReal⁻¹) * M * K *
        2 ^ (p.toReal⁻¹ * j + b.toReal⁻¹ * k + l / 2) * (levelNorm μ F k * levelNorm μ F l) := by
  -- Exchanging the two atoms conjugates the pairing.
  rw [setIntegral_timeShell_inner_eq_conj _ (fun s ↦ ((U s)†) (Lp.dyadicLayer k (F s)))
    fun t ↦ ((U t)†) (Lp.dyadicLayer l (F t)), RCLike.eNorm_conj]
  refine (enorm_setIntegral_timeShell_dyadicLayer_le_energy hp2 hM hK hF hUF j l k).trans_eq ?_
  rw [add_right_comm _ ((l : ℝ) / 2), mul_comm (levelNorm μ F l)]

/-- **The pairing of two atoms on a dyadic time shell.** On the shell `2ʲ ≤ |s - t| < 2ʲ⁺¹`, the
pairing of the dyadic layers `Fₖ` and `Fₗ` is at most `c 2^e Xₖ Xₗ`, where `e` is the smallest of
the dispersive exponent `(1 - σ) j + k + l` and the two energy exponents. -/
private theorem enorm_setIntegral_timeShell_dyadicLayer_le {σ : ℝ} (hσ : 1 < σ) {p b : ℝ≥0∞}
    (hp2 : p ≤ 2) {U : ℝ → H →L[𝕜] Lp E 2 μ} {A M K : ℝ≥0} (hM : ∀ t, ‖U t‖ₑ ≤ M)
    (hD : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) ∞ μ ≤ A * ‖s - t‖ₑ ^ (-σ) * eLpNorm g 1 μ)
    (hK : ∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G → Integrable (fun t ↦ ((U t)†) (G t)) →
      ‖∫ t, ((U t)†) (G t)‖ₑ ≤ K * eLpNorm (fun t ↦ eLpNorm (G t) b μ) p)
    {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F)
    (hUF : ∀ k, Integrable fun t ↦ ((U t)†) (Lp.dyadicLayer k (F t))) (j k l : ℤ) :
    ‖∫ z in timeShell ((2 : ℝ) ^ j), ⟪((U z.1)†) (Lp.dyadicLayer k (F z.1)),
        ((U z.2)†) (Lp.dyadicLayer l (F z.2))⟫_𝕜 ∂(volume.prod volume)‖ₑ ≤
      (16 * A + 2 ^ (p.toReal⁻¹ + 2⁻¹ + b.toReal⁻¹) * M * K) *
        2 ^ min ((1 - σ) * j + k + l) (min (p.toReal⁻¹ * j + k / 2 + b.toReal⁻¹ * l)
          (p.toReal⁻¹ * j + b.toReal⁻¹ * k + l / 2)) * (levelNorm μ F k * levelNorm μ F l) := by
  -- The smallest exponent wins.
  rcases min_choice ((1 - σ) * j + k + l) (min (p.toReal⁻¹ * j + k / 2 + b.toReal⁻¹ * l)
      (p.toReal⁻¹ * j + b.toReal⁻¹ * k + l / 2)) with he | he <;> rw [he]
  · exact (enorm_setIntegral_timeShell_dyadicLayer_le_dispersive hσ hD hF j k l).trans
      (by gcongr; exact le_self_add)
  · rcases min_choice (p.toReal⁻¹ * j + k / 2 + b.toReal⁻¹ * l)
      (p.toReal⁻¹ * j + b.toReal⁻¹ * k + l / 2) with he' | he' <;> rw [he']
    · exact (enorm_setIntegral_timeShell_dyadicLayer_le_energy hp2 hM hK hF hUF j k l).trans
        (by gcongr; exact le_add_self)
    · exact (enorm_setIntegral_timeShell_dyadicLayer_le_energy' hp2 hM hK hF hUF j k l).trans
        (by gcongr; exact le_add_self)

/-- **Summing the atom pairings over the time shells.** If the smallest exponent is at most
`ω (k + l) - δ (|k - σ j| + |l - σ j|)`, the pairings of `Fₖ` and `Fₗ` on all the shells add up to
at most `c W 2^{-δ |k - l| / 2} (2^{ω k} Xₖ) (2^{ω l} Xₗ)`, with `W` independent of `k` and `l`. -/
theorem tsum_enorm_setIntegral_timeShell_dyadicLayer_le {σ : ℝ} (hσ : 1 < σ)
    {p b : ℝ≥0∞} (hp2 : p ≤ 2) {ω δ : ℝ} (hδ : 0 < δ)
    (hexp : ∀ j k l : ℝ, min ((1 - σ) * j + k + l) (min (p.toReal⁻¹ * j + k / 2 + b.toReal⁻¹ * l)
        (p.toReal⁻¹ * j + b.toReal⁻¹ * k + l / 2)) ≤
      ω * (k + l) - δ * (|k - σ * j| + |l - σ * j|))
    {U : ℝ → H →L[𝕜] Lp E 2 μ} {A M K : ℝ≥0} (hM : ∀ t, ‖U t‖ₑ ≤ M)
    (hD : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) ∞ μ ≤ A * ‖s - t‖ₑ ^ (-σ) * eLpNorm g 1 μ)
    (hK : ∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G → Integrable (fun t ↦ ((U t)†) (G t)) →
      ‖∫ t, ((U t)†) (G t)‖ₑ ≤ K * eLpNorm (fun t ↦ eLpNorm (G t) b μ) p)
    {F : ℝ → Lp E 2 μ} (hF : AEStronglyMeasurable F)
    (hUF : ∀ k, Integrable fun t ↦ ((U t)†) (Lp.dyadicLayer k (F t))) (k l : ℤ) :
    ∑' j : ℤ, ‖∫ z in timeShell ((2 : ℝ) ^ j), ⟪((U z.1)†) (Lp.dyadicLayer k (F z.1)),
        ((U z.2)†) (Lp.dyadicLayer l (F z.2))⟫_𝕜 ∂(volume.prod volume)‖ₑ ≤
      (16 * A + 2 ^ (p.toReal⁻¹ + 2⁻¹ + b.toReal⁻¹) * M * K) *
        (2 ^ (δ / 2) * ∑' m : ℤ, (2 : ℝ≥0∞) ^ (-(δ / 2 * |(m : ℝ)|))) *
        2 ^ (-(δ / 2 * |(k : ℝ) - l|)) *
        ((2 ^ ((k : ℝ) * ω) * levelNorm μ F k) * (2 ^ ((l : ℝ) * ω) * levelNorm μ F l)) := by
  set c := (16 * A + 2 ^ (p.toReal⁻¹ + 2⁻¹ + b.toReal⁻¹) * M * K : ℝ≥0∞)
  set Xk := levelNorm μ F k
  set Xl := levelNorm μ F l
  -- Each shell contributes `c 2^{ω k} 2^{ω l} 2^{-δ |k - l| / 2} 2^{-δ |k - σ j| / 2} Xₖ Xₗ`.
  have hj (j : ℤ) : ‖∫ z in timeShell ((2 : ℝ) ^ j), ⟪((U z.1)†) (Lp.dyadicLayer k (F z.1)),
      ((U z.2)†) (Lp.dyadicLayer l (F z.2))⟫_𝕜 ∂(volume.prod volume)‖ₑ ≤
        c * 2 ^ (-(δ / 2 * |(k : ℝ) - l|)) * ((2 ^ ((k : ℝ) * ω) * Xk) *
          (2 ^ ((l : ℝ) * ω) * Xl)) * 2 ^ (-(δ / 2 * |(k : ℝ) - σ * j|)) := by
    refine (enorm_setIntegral_timeShell_dyadicLayer_le hσ hp2 hM hD hK hF hUF j k l).trans ?_
    have hle : min ((1 - σ) * j + k + l) (min (p.toReal⁻¹ * j + k / 2 + b.toReal⁻¹ * l)
        (p.toReal⁻¹ * j + b.toReal⁻¹ * k + l / 2)) ≤
          -(δ / 2 * |(k : ℝ) - l|) +
            ((k : ℝ) * ω + (l : ℝ) * ω + -(δ / 2 * |(k : ℝ) - σ * j|)) := by
      refine (hexp j k l).trans ?_
      have := abs_sub_le (k : ℝ) (σ * j) l
      rw [abs_sub_comm (σ * (j : ℝ)) l] at this
      nlinarith [abs_nonneg ((k : ℝ) - σ * j), abs_nonneg ((l : ℝ) - σ * j)]
    calc _ ≤ c * 2 ^ (-(δ / 2 * |(k : ℝ) - l|) +
          ((k : ℝ) * ω + (l : ℝ) * ω + -(δ / 2 * |(k : ℝ) - σ * j|))) * (Xk * Xl) :=
          mul_le_mul' (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hle))
            le_rfl
      _ = _ := by simp only [← two_rpow_mul_two_rpow]; ring
  calc _ ≤ ∑' j : ℤ, c * 2 ^ (-(δ / 2 * |(k : ℝ) - l|)) * ((2 ^ ((k : ℝ) * ω) * Xk) *
          (2 ^ ((l : ℝ) * ω) * Xl)) * 2 ^ (-(δ / 2 * |(k : ℝ) - σ * j|)) := tsum_le_tsum hj
    _ = c * 2 ^ (-(δ / 2 * |(k : ℝ) - l|)) * ((2 ^ ((k : ℝ) * ω) * Xk) *
          (2 ^ ((l : ℝ) * ω) * Xl)) * ∑' j : ℤ, 2 ^ (-(δ / 2 * |(k : ℝ) - σ * j|)) :=
        ENNReal.tsum_mul_left
    _ ≤ c * 2 ^ (-(δ / 2 * |(k : ℝ) - l|)) * ((2 ^ ((k : ℝ) * ω) * Xk) *
          (2 ^ ((l : ℝ) * ω) * Xl)) *
          (2 ^ (δ / 2) * ∑' m : ℤ, (2 : ℝ≥0∞) ^ (-(δ / 2 * |(m : ℝ)|))) := by
        gcongr
        exact tsum_two_rpow_neg_mul_abs_sub_le hσ.le (half_pos hδ) _
    _ = _ := by ring

omit [NormedSpace ℝ E] [NormedSpace ℝ H] in
/-- An energy bound `‖U(t)‖ₑ ≤ M` bounds the adjoints: `‖U(t)* v‖ ≤ M ‖v‖`. -/
private theorem norm_adjoint_le {U : ℝ → H →L[𝕜] Lp E 2 μ} {M : ℝ≥0} (hM : ∀ t, ‖U t‖ₑ ≤ M)
    (t : ℝ) (v : Lp E 2 μ) : ‖((U t)†) v‖ ≤ M * ‖v‖ := by
  have h := hM t
  rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_le_ofReal_iff M.coe_nonneg,
    ← ContinuousLinearMap.adjoint.norm_map] at h
  exact ((U t)†).le_of_opNorm_le h v

/-- The partial sums of the dual integrals of the dyadic layers of `F` converge to the dual
integral of `F`. -/
private theorem tendsto_sum_range_integral_dyadicLayer {U : ℝ → H →L[𝕜] Lp E 2 μ} {M : ℝ≥0}
    (hM : ∀ t, ‖U t‖ₑ ≤ M)
    (hUm : ∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G →
      AEStronglyMeasurable fun t ↦ ((U t)†) (G t))
    {F : ℝ → Lp E 2 μ} (hF : Integrable F)
    (hUF : ∀ k, Integrable fun t ↦ ((U t)†) (Lp.dyadicLayer k (F t))) :
    Tendsto (fun N : ℕ ↦ ∑ i ∈ Finset.range (2 * N),
        ∫ t, ((U t)†) (Lp.dyadicLayer ((i : ℤ) - N) (F t))) atTop
      (𝓝 (∫ t, ((U t)†) (F t))) := by
  have heq (N : ℕ) : ∑ i ∈ Finset.range (2 * N),
      ∫ t, ((U t)†) (Lp.dyadicLayer ((i : ℤ) - N) (F t)) =
        ∫ t, ((U t)†) (∑ i ∈ Finset.range (2 * N), Lp.dyadicLayer ((i : ℤ) - N) (F t)) := by
    rw [← integral_finsetSum _ fun i _ ↦ hUF _]
    simp_rw [map_sum]
  simp_rw [heq]
  refine tendsto_integral_of_dominated_convergence (fun t ↦ M * ‖F t‖)
    (fun N ↦ hUm _ (Finset.aestronglyMeasurable_fun_sum _ fun i _ ↦
      hF.aestronglyMeasurable.dyadicLayer _))
    (hF.norm.const_mul _) (fun N ↦ ae_of_all _ fun t ↦ ?_) (ae_of_all _ fun t ↦ ?_)
  · exact (norm_adjoint_le hM t _).trans <| mul_le_mul_of_nonneg_left
      (Lp.norm_sum_range_dyadicLayer_le two_ne_zero N (F t)) M.coe_nonneg
  · exact (((U t)†).continuous.tendsto _).comp
      (Lp.tendsto_sum_range_dyadicLayer ENNReal.ofNat_ne_top (F t))

/-! ### The endpoint estimate -/

/-- The exponents of the endpoint theorem: the non-endpoint time exponent satisfies `p ≤ 2` and
the dual endpoint exponent satisfies `0 < r' ≤ 2`. -/
private theorem le_two_and_ne_zero_and_le_two_of_endpoint {σ : ℝ} (hσ : 1 < σ) {p b r' : ℝ≥0∞}
    (hbσ : b.toReal⁻¹ < (σ + 1) / (2 * σ)) (hp : p.toReal⁻¹ = 1 + σ / 2 - σ * b.toReal⁻¹)
    (hr' : r'.toReal⁻¹ = (σ + 1) / (2 * σ)) : p ≤ 2 ∧ r' ≠ 0 ∧ r' ≤ 2 := by
  have hσ0 : 0 < σ := one_pos.trans hσ
  -- An exponent whose reciprocal exceeds `1 / 2` is at most `2`.
  have hle {q : ℝ≥0∞} (h : (2 : ℝ)⁻¹ < q.toReal⁻¹) : 0 < q.toReal ∧ q ≤ 2 := by
    have hpos : 0 < q.toReal := inv_pos.1 ((inv_pos.2 two_pos).trans h)
    refine ⟨hpos, ?_⟩
    rw [← ENNReal.ofReal_toReal (ENNReal.toReal_pos_iff.1 hpos).2.ne, ← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_le_ofReal ((inv_lt_inv₀ two_pos hpos).1 h).le
  have hσb : σ * b.toReal⁻¹ < (σ + 1) / 2 := by
    calc σ * b.toReal⁻¹ < σ * ((σ + 1) / (2 * σ)) := mul_lt_mul_of_pos_left hbσ hσ0
      _ = (σ + 1) / 2 := by field_simp
  have hr'half : (2 : ℝ)⁻¹ < r'.toReal⁻¹ := by
    rw [hr', show (σ + 1) / (2 * σ) = 2⁻¹ + 2⁻¹ * σ⁻¹ by field_simp]
    have := inv_pos.2 hσ0
    linarith
  obtain ⟨hr'pos, hr'2⟩ := hle hr'half
  exact ⟨(hle (by rw [hp]; linarith)).2, (ENNReal.toReal_pos_iff.1 hr'pos).1.ne', hr'2⟩

/-- **The squared endpoint estimate.** With the exponent bookkeeping `δ` of
`exists_min_exponent_le`, the square of the dual integral is at most an explicit constant times
`‖F‖²_{L²_t L^{r'}_x}`. -/
private theorem enorm_integral_adjoint_rpow_two_le {σ : ℝ} (hσ : 1 < σ) {p b r' : ℝ≥0∞}
    (hp2 : p ≤ 2) (hr'0 : r' ≠ 0) (hr'2 : r' ≤ 2) {δ : ℝ} (hδ : 0 < δ)
    (hexp : ∀ j k l : ℝ, min ((1 - σ) * j + k + l)
      (min (p.toReal⁻¹ * j + k / 2 + b.toReal⁻¹ * l) (p.toReal⁻¹ * j + b.toReal⁻¹ * k + l / 2)) ≤
        r'.toReal⁻¹ * (k + l) - δ * (|k - σ * j| + |l - σ * j|))
    {U : ℝ → H →L[𝕜] Lp E 2 μ} {A M K : ℝ≥0} (hM : ∀ t, ‖U t‖ₑ ≤ M)
    (hD : ∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
      eLpNorm (U s (((U t)†) g)) ∞ μ ≤ A * ‖s - t‖ₑ ^ (-σ) * eLpNorm g 1 μ)
    (hK : ∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G → Integrable (fun t ↦ ((U t)†) (G t)) →
      ‖∫ t, ((U t)†) (G t)‖ₑ ≤ K * eLpNorm (fun t ↦ eLpNorm (G t) b μ) p)
    (hUm : ∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G →
      AEStronglyMeasurable fun t ↦ ((U t)†) (G t))
    {F : ℝ → Lp E 2 μ} (hF : Integrable F) :
    ‖∫ t, ((U t)†) (F t)‖ₑ ^ (2 : ℝ) ≤
      (16 * A + 2 ^ (p.toReal⁻¹ + 2⁻¹ + b.toReal⁻¹) * M * K) *
        (2 ^ (δ / 2) * ∑' m : ℤ, (2 : ℝ≥0∞) ^ (-(δ / 2 * |(m : ℝ)|))) *
        (∑' m : ℤ, (2 : ℝ≥0∞) ^ (-(δ / 2 * |(m : ℝ)|))) *
        ENNReal.ofReal (2 ^ (2 / r'.toReal) / Real.log 2) *
        eLpNorm (fun t ↦ eLpNorm (F t) r' μ) 2 ^ (2 : ℝ) := by
  -- The dual integrals of the layers are integrable.
  have hUF (k : ℤ) : Integrable fun t ↦ ((U t)†) (Lp.dyadicLayer k (F t)) := by
    refine Integrable.mono' (hF.norm.const_mul M)
      (hUm _ (hF.aestronglyMeasurable.dyadicLayer k)) (ae_of_all _ fun t ↦ ?_)
    refine (norm_adjoint_le hM t _).trans (mul_le_mul_of_nonneg_left ?_ M.coe_nonneg)
    exact Lp.norm_le_norm_of_ae_le ((Lp.enorm_dyadicLayer_le_enorm two_ne_zero k (F t)).mono
      fun x hx ↦ eNorm_le_iff_norm_le.1 hx)
  set c : ℝ≥0∞ := 16 * A + 2 ^ (p.toReal⁻¹ + 2⁻¹ + b.toReal⁻¹) * M * K
  set S : ℝ≥0∞ := ∑' m : ℤ, (2 : ℝ≥0∞) ^ (-(δ / 2 * |(m : ℝ)|))
  let y : ℤ → ℝ≥0∞ := fun k ↦ 2 ^ ((k : ℝ) * r'.toReal⁻¹) * levelNorm μ F k
  let w : ℤ → ℝ≥0∞ := fun m ↦ 2 ^ (-(δ / 2 * |(m : ℝ)|))
  -- `TT*` on the layer decomposition, the shell bounds, Schur's test and the level sums.
  refine (enorm_rpow_two_le_tsum_tsum_enorm_inner (𝕜 := 𝕜)
    (fun k ↦ ∫ t, ((U t)†) (Lp.dyadicLayer k (F t)))
    (s := fun N : ℕ ↦ (Finset.range (2 * N)).image fun i : ℕ ↦ (i : ℤ) - N)
    ((tendsto_sum_range_integral_dyadicLayer hM hUm hF hUF).congr fun N ↦
      (Finset.sum_image fun i _ i' _ h ↦ by simpa using h).symm)).trans ?_
  calc _ ≤ ∑' k : ℤ, ∑' l : ℤ, c * (2 ^ (δ / 2) * S) * (w (k - l) * (y k * y l)) :=
        tsum_le_tsum fun k ↦ tsum_le_tsum fun l ↦
          (enorm_inner_integral_le_tsum (hUF k) (hUF l)).trans
            ((tsum_enorm_setIntegral_timeShell_dyadicLayer_le hσ hp2 hδ hexp hM hD hK
              hF.aestronglyMeasurable hUF k l).trans_eq (by simp only [w, y]; push_cast; ring))
    _ = c * (2 ^ (δ / 2) * S) * ∑' k : ℤ, ∑' l : ℤ, w (k - l) * (y k * y l) := by
        simp_rw [ENNReal.tsum_mul_left]
    _ ≤ c * (2 ^ (δ / 2) * S) * (S * ∑' k : ℤ, y k ^ 2) := by
        gcongr
        exact tsum_tsum_mul_mul_le w y
    _ ≤ c * (2 ^ (δ / 2) * S) * (S * (ENNReal.ofReal (2 ^ (2 / r'.toReal) / Real.log 2) *
          eLpNorm (fun t ↦ eLpNorm (F t) r' μ) 2 ^ 2)) := by
        gcongr
        exact tsum_sq_two_rpow_mul_levelNorm_le hr'0 hr'2 hF.aestronglyMeasurable
    _ = _ := by rw [ENNReal.rpow_two]; ring

/-- **The endpoint dual Strichartz estimate of Keel and Tao.** Let `σ > 1`, let `r'` be the dual
endpoint exponent, `1 / r' = (σ + 1) / (2σ)`, and let `U(t) : H → L²(X, μ)` be bounded operators,
`‖U(t)‖ ≤ M`, that depend measurably on `t` and whose time pairings satisfy the dispersive estimate

`‖U(s) U(t)* g‖_∞ ≤ A |s - t| ^ (-σ) ‖g‖₁`,  `s ≠ t`.

Suppose that `U` satisfies a dual Strichartz estimate `‖∫ U(t)* G(t) dt‖ ≤ K ‖G‖_{L^p_t L^b_x}`
at a non-endpoint pair: `1/2 < 1/b < 1/r'` and `1/p = 1 + σ/2 - σ/b`. Then there is `C` such
that for every integrable `F : ℝ → L²(X, μ)`,

`‖∫ U(t)* F(t) dt‖ ≤ C ‖F‖_{L²_t L^{r'}_x}`.

The constant `C` depends only on `σ`, the exponents and `A`, `M`, `K`, not on the family `U`: it
is uniform over all families satisfying the three bounds with the same constants. -/
theorem exists_enorm_integral_adjoint_le_of_endpoint {σ : ℝ} (hσ : 1 < σ)
    {p b r' : ℝ≥0∞} (hb : 2⁻¹ < b.toReal⁻¹) (hbσ : b.toReal⁻¹ < (σ + 1) / (2 * σ))
    (hp : p.toReal⁻¹ = 1 + σ / 2 - σ * b.toReal⁻¹) (hr' : r'.toReal⁻¹ = (σ + 1) / (2 * σ))
    (A M K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ U : ℝ → H →L[𝕜] Lp E 2 μ, (∀ t, ‖U t‖ₑ ≤ M) →
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) ∞ μ ≤ A * ‖s - t‖ₑ ^ (-σ) * eLpNorm g 1 μ) →
      (∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G → Integrable (fun t ↦ ((U t)†) (G t)) →
        ‖∫ t, ((U t)†) (G t)‖ₑ ≤ K * eLpNorm (fun t ↦ eLpNorm (G t) b μ) p) →
      (∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G →
        AEStronglyMeasurable fun t ↦ ((U t)†) (G t)) →
      ∀ F : ℝ → Lp E 2 μ, Integrable F →
        ‖∫ t, ((U t)†) (F t)‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (F t) r' μ) 2 := by
  obtain ⟨hp2, hr'0, hr'2⟩ := le_two_and_ne_zero_and_le_two_of_endpoint hσ hbσ hp hr'
  obtain ⟨δ, hδ, hexp⟩ := exists_min_exponent_le hσ hb hbσ
  rw [← hp, ← hr'] at hexp
  set S : ℝ≥0∞ := ∑' m : ℤ, (2 : ℝ≥0∞) ^ (-(δ / 2 * |(m : ℝ)|))
  set B : ℝ≥0∞ := (16 * A + 2 ^ (p.toReal⁻¹ + 2⁻¹ + b.toReal⁻¹) * M * K) *
    (2 ^ (δ / 2) * S) * S * ENNReal.ofReal (2 ^ (2 / r'.toReal) / Real.log 2)
  have hS : S ≠ ∞ := tsum_two_rpow_neg_mul_abs_ne_top (half_pos hδ)
  have hB : B ≠ ∞ := by
    have h1 : (2 : ℝ≥0∞) ^ (p.toReal⁻¹ + 2⁻¹ + b.toReal⁻¹) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofNat_ne_top
    have h2 : (2 : ℝ≥0∞) ^ (δ / 2) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofNat_ne_top
    finiteness
  refine ⟨(B ^ (2⁻¹ : ℝ)).toNNReal, fun U hM hD hK hUm F hF ↦ ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg (by positivity) hB)]
  have hrhs : (B ^ (2⁻¹ : ℝ) * eLpNorm (fun t ↦ eLpNorm (F t) r' μ) 2) ^ (2 : ℝ) =
      B * eLpNorm (fun t ↦ eLpNorm (F t) r' μ) 2 ^ (2 : ℝ) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← ENNReal.rpow_mul,
      inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one]
  rw [← ENNReal.rpow_le_rpow_iff (z := 2) two_pos, hrhs]
  exact enorm_integral_adjoint_rpow_two_le hσ hp2 hr'0 hr'2 hδ hexp hM hD hK hUm hF

/-- **The endpoint dual Strichartz estimate from an `L^{4/3}_t` estimate.** The case of
`exists_enorm_integral_adjoint_le_of_endpoint` where the non-endpoint dual estimate is taken in
`L^{4/3}_t L^b_x` with `1/b = 1/2 + 1/(4σ)`, the dual of the pair `(4, r₄)` on the boundary line
`1/r₄ = 1/2 - 1/(4σ)`. The exponent conditions of the general theorem then hold automatically. -/
theorem exists_enorm_integral_adjoint_le_of_endpoint_of_four_thirds {σ : ℝ} (hσ : 1 < σ)
    {b r' : ℝ≥0∞} (hb : b.toReal⁻¹ = 2⁻¹ + (4 * σ)⁻¹) (hr' : r'.toReal⁻¹ = (σ + 1) / (2 * σ))
    (A M K : ℝ≥0) :
    ∃ C : ℝ≥0, ∀ U : ℝ → H →L[𝕜] Lp E 2 μ, (∀ t, ‖U t‖ₑ ≤ M) →
      (∀ s t, s ≠ t → ∀ g : Lp E 2 μ,
        eLpNorm (U s (((U t)†) g)) ∞ μ ≤ A * ‖s - t‖ₑ ^ (-σ) * eLpNorm g 1 μ) →
      (∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G → Integrable (fun t ↦ ((U t)†) (G t)) →
        ‖∫ t, ((U t)†) (G t)‖ₑ ≤
          K * eLpNorm (fun t ↦ eLpNorm (G t) b μ) ((4 / 3 : ℝ≥0) : ℝ≥0∞)) →
      (∀ G : ℝ → Lp E 2 μ, AEStronglyMeasurable G →
        AEStronglyMeasurable fun t ↦ ((U t)†) (G t)) →
      ∀ F : ℝ → Lp E 2 μ, Integrable F →
        ‖∫ t, ((U t)†) (F t)‖ₑ ≤ C * eLpNorm (fun t ↦ eLpNorm (F t) r' μ) 2 := by
  have hσ0 : 0 < σ := by linarith
  refine exists_enorm_integral_adjoint_le_of_endpoint hσ ?_ ?_ ?_ hr' A M K <;> rw [hb]
  · linarith [inv_pos.2 (by positivity : 0 < 4 * σ)]
  · field_simp
    linarith
  · norm_num
    field_simp
    ring

end Shell

end TauCeti
