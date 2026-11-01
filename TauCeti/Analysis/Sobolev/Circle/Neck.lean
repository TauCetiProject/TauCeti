/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import TauCeti.Analysis.Sobolev.Circle.Laurent
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.FDeriv.Analytic

/-!
# The neck transfer of a plumbing node on the circle Sobolev spaces

The neck of the plumbing `xy = a`, `0 < |a| < 1`, is the annulus `|a| ≤ |x| ≤ 1` in the first
branch coordinate, the second branch coordinate being `y = a / x`. Its two outer boundary circles
are `|x| = 1` and `|y| = 1`. A function `G(y) = ∑ₙ Gₙ yⁿ` of the second coordinate, read on the
circle `|x| = 1`, becomes `x ↦ G(a / x)`, whose `(-n)`-th Fourier coefficient is `aⁿ Gₙ`.

This file studies the resulting operator on the circle Sobolev spaces `H^s`. The neck transfer
`CircleSobolev.neckTransfer a` sends `u` to `∑_{n > 0} aⁿ uₙ e^{-inθ}`: it carries the positive
frequencies on one boundary circle to the negative frequencies they produce on the other. For
`‖a‖ ≤ 1` it has norm at most `‖a‖`, it depends holomorphically on `a` in the open unit disc, and
its derivative at `a = 0` is the operator `u ↦ u₁ e^{-iθ}`, which is nonzero for `E ≠ 0`.

The linearized node equation `F(x) + G(a / x) = const` on the neck reads, in the Fourier
coefficients on the two outer circles, `F₋ₙ = -aⁿ Gₙ` and `G₋ₙ = -aⁿ Fₙ` for every `n > 0`. The
pairs `(F, G)` satisfying it form `CircleSobolev.neckGraph s E a`. For `‖a‖ ≤ 1` their negative
frequency parts are `-neckTransfer a G` and `-neckTransfer a F`, so the neck graph is the graph,
over the pair of nonnegative Laurent subspaces, of a bounded operator that vanishes at `a = 0`.
It is a closed complement of the pair of negative Laurent subspaces, and at `a = 0` it is the pair
`H^s_{≥0} × H^s_{≥0}` of boundary values of holomorphic functions on the two branch discs of the
node `xy = 0`. This is the linear model of the Hardy decomposition at a node.

## Main definitions

* `TauCeti.CircleSobolev.neckTransfer a`: the operator `u ↦ ∑_{n > 0} aⁿ uₙ e^{-inθ}` on `H^s`,
  for `‖a‖ ≤ 1` (and `0` otherwise).
* `TauCeti.CircleSobolev.neckGraph s E a`: the pairs `(F, G)` of elements of `H^s` with
  `F₋ₙ = -aⁿ Gₙ` and `G₋ₙ = -aⁿ Fₙ` for every `n > 0`.

## Main statements

* `TauCeti.CircleSobolev.norm_neckTransfer_apply_le`: `‖neckTransfer a u‖ ≤ ‖a‖ ‖u‖`.
* `TauCeti.CircleSobolev.toContinuousMap_neckTransfer`: for `s > 1/2` and `‖a‖ ≤ 1` the continuous
  function of `neckTransfer a u` is `x ↦ diskFunction u (a / x) - u₀`.
* `TauCeti.CircleSobolev.analyticOnNhd_neckTransfer`: `a ↦ neckTransfer a` is analytic on the open
  unit disc, as a map to the bounded operators on `H^s`.
* `TauCeti.CircleSobolev.hasDerivAt_neckTransfer_zero`: its derivative at `0` is `u ↦ u₁ e^{-iθ}`.
* `TauCeti.CircleSobolev.mem_neckGraph_iff_indicator_Iio_eq`: the neck graph is the graph of
  `-neckTransfer a` on the nonnegative frequencies, and `TauCeti.CircleSobolev.isCompl_neckGraph`:
  it is a complement of the pair of negative Laurent subspaces.
* `TauCeti.CircleSobolev.neckGraph_zero`: at `a = 0` it is the pair of nonnegative Laurent
  subspaces.
* `TauCeti.CircleSobolev.hasSum_zpow_smul_coeff_of_mem_neckGraph`: for `s > 1/2`, `a ≠ 0` and
  `(F, G)` in the neck graph, the Laurent series `G(a / x) = ∑ₙ (a / x)ⁿ Gₙ` converges on `|x| = 1`
  and `F(x) + G(a / x) = F₀ + G₀`.

## References

* J. W. Robbin and D. A. Salamon, *A construction of the Deligne–Mumford orbifold*,
  J. Eur. Math. Soc. **8** (2006), 611–699, §§9–12 (Hardy decompositions at the nodes of a
  plumbed Riemann surface).
-/

public section

noncomputable section

open Complex Filter Metric Topology

namespace TauCeti

namespace CircleSobolev

variable {s t : ℝ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {a : ℂ}

/-! ### The neck transfer -/

/-- The coefficient sequence of the neck transfer. -/
private def neckCoeff (a : ℂ) (u : CircleSobolev s E) (n : ℤ) : E :=
  if n < 0 then a ^ n.natAbs • u.coeff (-n) else 0

private theorem weight_mul_norm_neckCoeff_le (ha : ‖a‖ ≤ 1) (u : CircleSobolev s E) (n : ℤ) :
    weight s n * ‖neckCoeff a u n‖ ≤ ‖a‖ * (weight s n * ‖(reflect u).coeff n‖) := by
  rw [mul_left_comm, coeff_reflect]
  refine mul_le_mul_of_nonneg_left ?_ (weight_nonneg s n)
  unfold neckCoeff
  split_ifs with hn
  · rw [norm_smul, norm_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_of_le_one (norm_nonneg a) ha (Int.natAbs_ne_zero.2 hn.ne)) (norm_nonneg _)
  · rw [norm_zero]
    positivity

/-- The neck transfer of `u`, as an element of `H^s`, for `‖a‖ ≤ 1`. -/
private def neckTransferFun (ha : ‖a‖ ≤ 1) (u : CircleSobolev s E) : CircleSobolev s E :=
  ⟨neckCoeff a u, memℓp_of_forall_le (weight_mul_norm_neckCoeff_le ha u)⟩

/-- The **neck transfer** of the plumbing `xy = a`: the operator on `H^s` sending `u` to
`∑_{n > 0} aⁿ uₙ e^{-inθ}`. For `s > 1/2` and complete `E`, on a nonnegative-frequency `u`, the
boundary value of a holomorphic function `U` on the unit disc, it gives the values of
`x ↦ U(a / x) - U(0)` on the unit circle (`CircleSobolev.toContinuousMap_neckTransfer`). It is
defined for `‖a‖ ≤ 1`, where its norm is at most `‖a‖` (`CircleSobolev.opNorm_neckTransfer_le`);
for `‖a‖ > 1` it is the junk value `0`. -/
def neckTransfer (a : ℂ) : CircleSobolev s E →L[ℂ] CircleSobolev s E :=
  if ha : ‖a‖ ≤ 1 then
    LinearMap.mkContinuous
      { toFun := neckTransferFun ha
        map_add' u v := CircleSobolev.ext <| funext fun n ↦ by
          simp only [neckTransferFun, neckCoeff, coeff_add, Pi.add_apply]
          split_ifs <;> simp [smul_add]
        map_smul' c u := CircleSobolev.ext <| funext fun n ↦ by
          simp only [neckTransferFun, neckCoeff, coeff_smul, Pi.smul_apply, RingHom.id_apply]
          split_ifs <;> simp [smul_comm c] }
      ‖a‖ fun u ↦ (norm_le_of_forall_le (b := neckTransferFun ha u) (norm_nonneg a)
        (weight_mul_norm_neckCoeff_le ha u)).trans_eq (by rw [LinearIsometryEquiv.norm_map])
  else 0

/-- The Fourier coefficients of the neck transfer: the `(-n)`-th one, `n > 0`, is `aⁿ uₙ`, and the
nonnegative ones vanish. -/
@[simp]
theorem coeff_neckTransfer (ha : ‖a‖ ≤ 1) (u : CircleSobolev s E) (n : ℤ) :
    (neckTransfer a u).coeff n = if n < 0 then a ^ n.natAbs • u.coeff (-n) else 0 := by
  simp [neckTransfer, ha, neckTransferFun, neckCoeff]

/-- The neck transfer has no nonnegative frequencies. -/
@[simp]
theorem coeff_neckTransfer_of_nonneg (u : CircleSobolev s E) {n : ℤ} (hn : 0 ≤ n) :
    (neckTransfer a u).coeff n = 0 := by
  by_cases ha : ‖a‖ ≤ 1
  · simp [coeff_neckTransfer ha, not_lt.2 hn]
  · simp [neckTransfer, ha]

/-- The neck transfer moves the `n`-th Fourier coefficient, `n > 0`, to frequency `-n` and
multiplies it by `aⁿ`. -/
theorem coeff_neckTransfer_neg_natCast (ha : ‖a‖ ≤ 1) (u : CircleSobolev s E) {n : ℕ}
    (hn : n ≠ 0) : (neckTransfer a u).coeff (-n) = a ^ n • u.coeff n := by
  rw [coeff_neckTransfer ha, ite_eq_left (by omega), Int.natAbs_neg, Int.natAbs_natCast, neg_neg]

/-- Outside the closed unit disc the neck transfer is the junk value `0`. -/
@[simp]
theorem neckTransfer_of_one_lt_norm (ha : 1 < ‖a‖) :
    (neckTransfer a : CircleSobolev s E →L[ℂ] CircleSobolev s E) = 0 := by
  simp [neckTransfer, not_le.2 ha]

/-- The neck transfer of a node, `a = 0`, vanishes. -/
@[simp]
theorem neckTransfer_zero : (neckTransfer 0 : CircleSobolev s E →L[ℂ] CircleSobolev s E) = 0 :=
  ContinuousLinearMap.ext fun u ↦ CircleSobolev.ext <| funext fun n ↦ by
    rw [coeff_neckTransfer (norm_zero.trans_le zero_le_one)]
    split_ifs with hn
    · simp [zero_pow (Int.natAbs_ne_zero.2 hn.ne)]
    · simp

/-- The neck transfer has norm at most `‖a‖`, for every `a` (with the junk value `0` when
`‖a‖ > 1`). -/
theorem norm_neckTransfer_apply_le (a : ℂ) (u : CircleSobolev s E) :
    ‖neckTransfer a u‖ ≤ ‖a‖ * ‖u‖ := by
  by_cases ha : ‖a‖ ≤ 1
  · rw [← LinearIsometryEquiv.norm_map reflect u]
    exact norm_le_of_forall_le (norm_nonneg a) fun n ↦ by
      simpa only [coeff_neckTransfer ha, neckCoeff] using weight_mul_norm_neckCoeff_le ha u n
  · simp only [neckTransfer, ha, dite_false, zero_apply, norm_zero]
    positivity

/-- The operator norm of the neck transfer is at most `‖a‖`. -/
theorem opNorm_neckTransfer_le (a : ℂ) :
    ‖(neckTransfer a : CircleSobolev s E →L[ℂ] CircleSobolev s E)‖ ≤ ‖a‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg a) (norm_neckTransfer_apply_le a)

/-- The neck transfer has only negative frequencies. -/
theorem neckTransfer_mem_supported (a : ℂ) (u : CircleSobolev s E) :
    neckTransfer a u ∈ supported s E (Set.Iio 0) :=
  mem_supported'.2 fun _ hn ↦ coeff_neckTransfer_of_nonneg u (not_lt.1 hn)

/-- The neck transfer only depends on the positive frequencies. -/
@[simp]
theorem neckTransfer_indicator {S : Set ℤ} (hS : Set.Ioi 0 ⊆ S) (a : ℂ) (u : CircleSobolev s E) :
    neckTransfer a (indicator S u) = neckTransfer a u := by
  by_cases ha : ‖a‖ ≤ 1
  · refine CircleSobolev.ext <| funext fun n ↦ ?_
    simp only [coeff_neckTransfer ha, coeff_indicator]
    split_ifs with hn
    · rw [Set.indicator_of_mem (hS (Set.mem_Ioi.2 (by omega)))]
    · rfl
  · simp [neckTransfer_of_one_lt_norm (not_le.1 ha)]

/-- The neck transfer vanishes on elements without positive frequencies. -/
theorem neckTransfer_eq_zero_of_mem_supported (a : ℂ) {u : CircleSobolev s E}
    (hu : u ∈ supported s E (Set.Iic 0)) : neckTransfer a u = 0 := by
  rw [← neckTransfer_indicator subset_rfl, indicator_eq_zero_iff.2 (by rwa [Set.compl_Ioi]),
    map_zero]

/-- The neck transfer of a Fourier monomial of positive frequency `n` is the monomial of frequency
`-n` scaled by `aⁿ`. -/
@[simp]
theorem neckTransfer_single_natCast (ha : ‖a‖ ≤ 1) {n : ℕ} (hn : n ≠ 0) (x : E) :
    neckTransfer a (single (s := s) n x) = single (-n) (a ^ n • x) := by
  refine CircleSobolev.ext <| funext fun m ↦ ?_
  rw [coeff_neckTransfer ha, coeff_single, coeff_single]
  rcases eq_or_ne m (-n) with rfl | hm
  · rw [ite_eq_left (by omega), Pi.single_eq_same, neg_neg, Pi.single_eq_same, Int.natAbs_neg,
      Int.natAbs_natCast]
  · rw [Pi.single_eq_of_ne hm]
    split_ifs with hm'
    · rw [Pi.single_eq_of_ne (by omega), smul_zero]
    · rfl

/-- The neck transfer commutes with the inclusion `H^s ⊆ H^t`. -/
@[simp]
theorem inclusion_neckTransfer (h : t ≤ s) (a : ℂ) (u : CircleSobolev s E) :
    inclusion h (neckTransfer a u) = neckTransfer a (inclusion h u) := by
  by_cases ha : ‖a‖ ≤ 1
  · exact CircleSobolev.ext <| funext fun n ↦ by simp [coeff_neckTransfer ha]
  · simp [neckTransfer_of_one_lt_norm (not_le.1 ha)]

section Boundary

variable {T : ℝ} [Fact (0 < T)] [CompleteSpace E]

/-- **Boundary values of the neck transfer.** For `s > 1/2` and `‖a‖ ≤ 1`, the continuous function
on the circle attached to `neckTransfer a u` is `x ↦ diskFunction u (a / x) - u₀`, where `x` is read
as a point `fourier 1 x` of the unit circle. -/
theorem toContinuousMap_neckTransfer (hs : 1 / 2 < s) (ha : ‖a‖ ≤ 1) (u : CircleSobolev s E)
    (x : AddCircle T) :
    toContinuousMap T hs (neckTransfer a u) x =
      diskFunction u (a / fourier 1 x) - u.coeff 0 := by
  have hw : ‖a / (fourier 1 x : ℂ)‖ ≤ 1 := by
    rw [norm_div, fourier_one, Circle.norm_coe, div_one]
    exact ha
  have hD := (hasSum_diskFunction_of_norm_le_one hs u hw).sub
    (hasSum_ite_eq 0 (u.coeff 0))
  have hfourier (m : ℕ) : fourier (-(m : ℤ)) x = (fourier 1 x ^ m)⁻¹ := by
    rw [fourier_apply, fourier_one, AddCircle.toCircle_zsmul, Circle.coe_zpow, zpow_neg,
      zpow_natCast]
  have hinj : Function.Injective fun m : ℕ ↦ -(m : ℤ) :=
    neg_injective.comp Nat.cast_injective
  have hsum : HasSum (fun n : ℤ ↦ fourier n x • (neckTransfer a u).coeff n)
      (diskFunction u (a / fourier 1 x) - u.coeff 0) := by
    refine (hinj.hasSum_iff fun n hn ↦ ?_).1 (hD.congr_fun fun m ↦ ?_)
    · rw [coeff_neckTransfer_of_nonneg u, smul_zero]
      by_contra h
      exact hn ⟨n.natAbs, by simp only [Int.natCast_natAbs, abs_of_neg (not_le.1 h), neg_neg]⟩
    · rcases eq_or_ne m 0 with rfl | hm
      · simp [coeff_neckTransfer_of_nonneg u le_rfl]
      · simp only [Function.comp_apply, coeff_neckTransfer_neg_natCast ha u hm,
          hfourier, ite_eq_right hm, sub_zero, smul_smul]
        congr 1
        ring
  rw [toContinuousMap_apply]
  exact hsum.tsum_eq

end Boundary

/-! ### Holomorphic dependence on the plumbing parameter -/

/-- The `n`-th mode `u ↦ uₙ e^{-inθ}` of the neck transfer. -/
private def neckMode (n : ℕ) : CircleSobolev s E →L[ℂ] CircleSobolev s E :=
  (single (-(n : ℤ))).comp (coeffCLM n)

private theorem norm_neckMode_le (n : ℕ) :
    ‖(neckMode n : CircleSobolev s E →L[ℂ] CircleSobolev s E)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u ↦ ?_
  rw [neckMode, ContinuousLinearMap.comp_apply, norm_single, coeffCLM_apply, weight_neg_right,
    one_mul]
  calc weight s n * ‖u.coeff n‖ ≤ weight s n * (weight (-s) n * ‖u‖) :=
        mul_le_mul_of_nonneg_left (norm_coeff_le u n) (weight_nonneg s n)
    _ = ‖u‖ := by rw [← mul_assoc, weight_mul_weight_neg, one_mul]

/-- The power series `∑ₙ aⁿ (u ↦ uₙ e^{-inθ})`, whose sum is `neckTransfer a` plus the projection
onto the constants. -/
private def neckSeries : FormalMultilinearSeries ℂ ℂ (CircleSobolev s E →L[ℂ] CircleSobolev s E) :=
  fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (neckMode n)

private theorem neckSeries_apply (n : ℕ) (y : ℂ) :
    (neckSeries n fun _ ↦ y) = y ^ n • (neckMode n : CircleSobolev s E →L[ℂ] _) := by
  simp [neckSeries, ContinuousMultilinearMap.mkPiRing_apply]

private theorem coeff_neckMode_apply (n : ℕ) (u : CircleSobolev s E) (k : ℤ) :
    (neckMode n u).coeff k = if k = -n then u.coeff n else 0 := by
  simp only [neckMode, ContinuousLinearMap.comp_apply, coeff_single, coeffCLM_apply,
    Pi.single_apply]

section Analytic

variable [CompleteSpace E]

private theorem hasSum_neckMode {y : ℂ} (hy : ‖y‖ < 1) :
    HasSum (fun n ↦ y ^ n • (neckMode n : CircleSobolev s E →L[ℂ] CircleSobolev s E))
      (neckTransfer y + neckMode 0) := by
  have hsum : Summable fun n ↦ y ^ n • (neckMode n : CircleSobolev s E →L[ℂ] _) :=
    Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg y) hy) fun n ↦ by
      rw [norm_smul, norm_pow]
      exact mul_le_of_le_one_right (by positivity) (norm_neckMode_le n)
  convert hsum.hasSum using 1
  refine ContinuousLinearMap.ext fun u ↦ CircleSobolev.ext <| funext fun k ↦ ?_
  have h := (hsum.hasSum.mapL (ContinuousLinearMap.apply ℂ _ u)).mapL (coeffCLM k)
  simp only [ContinuousLinearMap.apply_apply, smul_apply,
    coeffCLM_apply, coeff_smul, Pi.smul_apply, coeff_neckMode_apply] at h
  refine HasSum.unique ?_ h
  have hf (n : ℕ) (hn : n ≠ (-k).toNat) :
      (y ^ n • if k = -(n : ℤ) then u.coeff n else 0) = 0 := by
    rw [ite_eq_right (by omega), smul_zero]
  convert _root_.hasSum_single (-k).toNat hf using 1
  rw [add_apply, coeff_add, Pi.add_apply, coeff_neckMode_apply, coeff_neckTransfer hy.le]
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg k <;> rcases eq_or_ne m 0 with rfl | hm
  · simp
  · simp [hm]
  · simp
  · simp [hm]

private theorem hasFPowerSeriesOnBall_neckTransfer_add :
    HasFPowerSeriesOnBall
      (fun y ↦ (neckTransfer y + neckMode 0 : CircleSobolev s E →L[ℂ] CircleSobolev s E))
      neckSeries 0 1 where
  r_le := by
    rw [← ENNReal.coe_one]
    refine FormalMultilinearSeries.le_radius_of_bound _ 1 fun n ↦ ?_
    rw [neckSeries, ContinuousMultilinearMap.norm_mkPiRing, NNReal.coe_one, one_pow, mul_one]
    exact norm_neckMode_le n
  r_pos := one_pos
  hasSum {y} hy := by
    rw [← ENNReal.coe_one, eball_coe, NNReal.coe_one, mem_ball_zero_iff] at hy
    simpa only [zero_add, neckSeries_apply] using hasSum_neckMode hy

/-- **Holomorphy of the neck transfer.** The neck transfer depends holomorphically on the plumbing
parameter `a` in the open unit disc, as a map to the bounded operators on `H^s`. -/
theorem analyticOnNhd_neckTransfer :
    AnalyticOnNhd ℂ (neckTransfer : ℂ → CircleSobolev s E →L[ℂ] CircleSobolev s E) (ball 0 1) :=
  fun y hy ↦ by
    have h := ((hasFPowerSeriesOnBall_neckTransfer_add (s := s) (E := E)).analyticAt_of_mem
      (by rwa [← ENNReal.coe_one, eball_coe, NNReal.coe_one])).sub
        (analyticAt_const (v := (neckMode 0 : CircleSobolev s E →L[ℂ] _)))
    convert h using 1
    funext z
    simp

/-- The derivative of the neck transfer at the node `a = 0` is the operator `u ↦ u₁ e^{-iθ}`,
which is nonzero for `E ≠ 0` although the neck transfer itself vanishes there. -/
theorem hasDerivAt_neckTransfer_zero :
    HasDerivAt (neckTransfer : ℂ → CircleSobolev s E →L[ℂ] CircleSobolev s E)
      ((single (-1)).comp (coeffCLM 1)) 0 := by
  have h := (hasFPowerSeriesOnBall_neckTransfer_add (s := s) (E := E)).hasFPowerSeriesAt
    |>.hasFDerivAt.hasDerivAt.sub_const (neckMode 0)
  simp only [add_sub_cancel_right] at h
  convert h using 1
  simp [neckSeries, neckMode]

end Analytic

/-! ### The linearized node equation -/

variable (s E) in
/-- The **neck graph** of the plumbing `xy = a`: the pairs `(F, G)` of elements of `H^s` whose
Fourier coefficients satisfy `F₋ₙ = -aⁿ Gₙ` and `G₋ₙ = -aⁿ Fₙ` for every `n > 0`. This is the
linearized node equation `F(x) + G(a / x) = const` on the neck, written in the Fourier
coefficients on its two outer boundary circles
(`CircleSobolev.hasSum_zpow_smul_coeff_of_mem_neckGraph`). -/
def neckGraph (a : ℂ) : Submodule ℂ (CircleSobolev s E × CircleSobolev s E) where
  carrier := {p | ∀ n : ℕ, n ≠ 0 →
    p.1.coeff (-n) = -(a ^ n • p.2.coeff n) ∧ p.2.coeff (-n) = -(a ^ n • p.1.coeff n)}
  add_mem' {p q} hp hq n hn := by
    simp only [Prod.fst_add, Prod.snd_add, coeff_add, Pi.add_apply, (hp n hn).1, (hp n hn).2,
      (hq n hn).1, (hq n hn).2, smul_add, neg_add, and_self]
  zero_mem' n _ := by simp
  smul_mem' c p hp n hn := by
    simp only [Prod.smul_fst, Prod.smul_snd, coeff_smul, Pi.smul_apply, (hp n hn).1, (hp n hn).2,
      smul_neg, smul_comm c, and_self]

/-- Membership in the neck graph, in terms of the Fourier coefficients. -/
theorem mem_neckGraph {p : CircleSobolev s E × CircleSobolev s E} :
    p ∈ neckGraph s E a ↔ ∀ n : ℕ, n ≠ 0 →
      p.1.coeff (-n) = -(a ^ n • p.2.coeff n) ∧ p.2.coeff (-n) = -(a ^ n • p.1.coeff n) :=
  Iff.rfl

/-- The neck graph is closed in `H^s × H^s`. -/
theorem isClosed_neckGraph (a : ℂ) :
    IsClosed (neckGraph s E a : Set (CircleSobolev s E × CircleSobolev s E)) := by
  have hc (m : ℤ) : Continuous fun u : CircleSobolev s E ↦ u.coeff m :=
    (coeffCLM m).continuous.congr fun u ↦ coeffCLM_apply m u
  have h : (neckGraph s E a : Set (CircleSobolev s E × CircleSobolev s E)) =
      ⋂ n : ℕ, ⋂ (_ : n ≠ 0), ({p | p.1.coeff (-n) = -(a ^ n • p.2.coeff n)} ∩
        {p | p.2.coeff (-n) = -(a ^ n • p.1.coeff n)}) := by
    ext p
    simp [mem_neckGraph]
  rw [h]
  exact isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
    (isClosed_eq ((hc _).comp continuous_fst) (((hc _).comp continuous_snd).const_smul _).neg).inter
      (isClosed_eq ((hc _).comp continuous_snd) (((hc _).comp continuous_fst).const_smul _).neg)

private theorem indicator_Ici_add_indicator_Iio (u : CircleSobolev s E) :
    indicator (Set.Ici 0) u + indicator (Set.Iio 0) u = u := by
  rw [← Set.compl_Ici]
  exact indicator_add_indicator_compl _ u

private theorem indicator_Iio_eq_zero_of_mem_supported {u : CircleSobolev s E}
    (hu : u ∈ supported s E (Set.Ici 0)) : indicator (Set.Iio 0) u = 0 :=
  indicator_eq_zero_iff.2 (by rwa [Set.compl_Iio])

private theorem indicator_Ici_eq_zero_of_mem_supported {u : CircleSobolev s E}
    (hu : u ∈ supported s E (Set.Iio 0)) : indicator (Set.Ici 0) u = 0 :=
  indicator_eq_zero_iff.2 (by rwa [Set.compl_Ici])

private theorem indicator_Iio_eq_neg_neckTransfer_iff (ha : ‖a‖ ≤ 1) (F G : CircleSobolev s E) :
    indicator (Set.Iio 0) F = -neckTransfer a G ↔
      ∀ n : ℕ, n ≠ 0 → F.coeff (-n) = -(a ^ n • G.coeff n) := by
  constructor
  · intro h n hn
    have h' := congr_arg (fun v : CircleSobolev s E ↦ v.coeff (-n)) h
    simpa [coeff_neckTransfer_neg_natCast ha G hn,
      Set.indicator_of_mem (Set.mem_Iio.2 (by omega : -(n : ℤ) < 0))] using h'
  · intro h
    refine CircleSobolev.ext <| funext fun k ↦ ?_
    rw [coeff_indicator, coeff_neg, Pi.neg_apply]
    rcases lt_or_ge k 0 with hk | hk
    · obtain ⟨m, rfl⟩ : ∃ m : ℕ, k = -m :=
        ⟨k.natAbs, by rw [Int.natCast_natAbs, abs_of_neg hk, neg_neg]⟩
      have hm : m ≠ 0 := by omega
      rw [Set.indicator_of_mem (Set.mem_Iio.2 hk), coeff_neckTransfer_neg_natCast ha G hm, h m hm]
    · rw [Set.indicator_of_notMem (by simpa using hk), coeff_neckTransfer_of_nonneg G hk, neg_zero]

/-- **The neck graph is a graph.** For `‖a‖ ≤ 1`, a pair `(F, G)` lies in the neck graph exactly
when the negative-frequency parts of `F` and `G` are `-neckTransfer a G` and `-neckTransfer a F`;
these only depend on the positive frequencies of `G` and `F`. -/
theorem mem_neckGraph_iff_indicator_Iio_eq (ha : ‖a‖ ≤ 1)
    {p : CircleSobolev s E × CircleSobolev s E} :
    p ∈ neckGraph s E a ↔
      indicator (Set.Iio 0) p.1 = -neckTransfer a p.2 ∧
        indicator (Set.Iio 0) p.2 = -neckTransfer a p.1 := by
  simp only [mem_neckGraph, imp_and, forall_and, indicator_Iio_eq_neg_neckTransfer_iff ha]

/-- At the node `a = 0` the neck graph is the pair of nonnegative Laurent subspaces, the boundary
values of holomorphic functions on the two branch discs. -/
@[simp]
theorem neckGraph_zero :
    neckGraph s E 0 = (supported s E (Set.Ici 0)).prod (supported s E (Set.Ici 0)) := by
  ext p
  simp only [mem_neckGraph_iff_indicator_Iio_eq (norm_zero.trans_le zero_le_one),
    neckTransfer_zero, zero_apply, neg_zero, indicator_eq_zero_iff, Set.compl_Iio,
    Submodule.mem_prod]

/-- **Existence in the neck graph.** Every pair `(F, G)` of nonnegative-frequency elements is the
nonnegative part of the element `(F - neckTransfer a G, G - neckTransfer a F)` of the neck
graph. -/
theorem sub_neckTransfer_mem_neckGraph (ha : ‖a‖ ≤ 1) {F G : CircleSobolev s E}
    (hF : F ∈ supported s E (Set.Ici 0)) (hG : G ∈ supported s E (Set.Ici 0)) :
    (F - neckTransfer a G, G - neckTransfer a F) ∈ neckGraph s E a := by
  have h₁ (u : CircleSobolev s E) : indicator (Set.Iio 0) (neckTransfer a u) = neckTransfer a u :=
    indicator_eq_self_iff.2 (neckTransfer_mem_supported a u)
  have h₂ (u : CircleSobolev s E) : neckTransfer a (neckTransfer a u) = 0 :=
    neckTransfer_eq_zero_of_mem_supported a
      (supported_mono Set.Iio_subset_Iic_self (neckTransfer_mem_supported a u))
  rw [mem_neckGraph_iff_indicator_Iio_eq ha]
  simp only [map_sub, indicator_Iio_eq_zero_of_mem_supported hF,
    indicator_Iio_eq_zero_of_mem_supported hG, h₁, h₂, zero_sub, sub_zero, and_self]

/-- **Uniqueness in the neck graph.** For `‖a‖ ≤ 1`, an element of the neck graph is determined by
its nonnegative-frequency parts. -/
theorem eq_of_mem_neckGraph (ha : ‖a‖ ≤ 1) {p : CircleSobolev s E × CircleSobolev s E}
    (hp : p ∈ neckGraph s E a) :
    p = (indicator (Set.Ici 0) p.1 - neckTransfer a p.2,
      indicator (Set.Ici 0) p.2 - neckTransfer a p.1) := by
  obtain ⟨h₁, h₂⟩ := (mem_neckGraph_iff_indicator_Iio_eq ha).1 hp
  refine Prod.ext ?_ ?_ <;> dsimp only
  · rw [sub_eq_add_neg, ← h₁, indicator_Ici_add_indicator_Iio p.1]
  · rw [sub_eq_add_neg, ← h₂, indicator_Ici_add_indicator_Iio p.2]

/-- **Transversality of the neck graph.** For `‖a‖ ≤ 1` the neck graph is a complement of the
pair of negative Laurent subspaces. -/
theorem isCompl_neckGraph (ha : ‖a‖ ≤ 1) :
    IsCompl (neckGraph s E a) ((supported s E (Set.Iio 0)).prod (supported s E (Set.Iio 0))) := by
  have hT {u : CircleSobolev s E} (hu : u ∈ supported s E (Set.Iio 0)) : neckTransfer a u = 0 :=
    neckTransfer_eq_zero_of_mem_supported a (supported_mono Set.Iio_subset_Iic_self hu)
  constructor
  · rw [Submodule.disjoint_def]
    rintro ⟨F, G⟩ hp ⟨hF, hG⟩
    have h := eq_of_mem_neckGraph ha hp
    simp only [indicator_Ici_eq_zero_of_mem_supported hF, indicator_Ici_eq_zero_of_mem_supported hG,
      hT hF, hT hG, sub_zero] at h
    exact h
  · rw [Submodule.codisjoint_iff_exists_add_eq]
    rintro ⟨F, G⟩
    refine ⟨(indicator (Set.Ici 0) F - neckTransfer a G,
        indicator (Set.Ici 0) G - neckTransfer a F),
      (indicator (Set.Iio 0) F + neckTransfer a G, indicator (Set.Iio 0) G + neckTransfer a F),
      ?_, ?_, ?_⟩
    · simpa only [neckTransfer_indicator Set.Ioi_subset_Ici_self] using
        sub_neckTransfer_mem_neckGraph ha (indicator_mem_supported (Set.Ici 0) F)
        (indicator_mem_supported (Set.Ici 0) G)
    · exact ⟨add_mem (indicator_mem_supported _ _) (neckTransfer_mem_supported a G),
        add_mem (indicator_mem_supported _ _) (neckTransfer_mem_supported a F)⟩
    · refine Prod.ext ?_ ?_
      · simp only [Prod.fst_add, sub_add_add_cancel, indicator_Ici_add_indicator_Iio]
      · simp only [Prod.snd_add, sub_add_add_cancel, indicator_Ici_add_indicator_Iio]

section Boundary

variable {T : ℝ} [Fact (0 < T)] [CompleteSpace E]

/-- **The linearized node equation.** For `s > 1/2`, `a ≠ 0` and `(F, G)` in the neck graph,
the Laurent series `G(a / x) = ∑ₙ (a / x)ⁿ Gₙ` converges at every point `x = fourier 1 x` of the
unit circle, and `F(x) + G(a / x) = F₀ + G₀`, where `F(x)` is the continuous function attached
to `F`. -/
theorem hasSum_zpow_smul_coeff_of_mem_neckGraph (hs : 1 / 2 < s) (ha₀ : a ≠ 0)
    {p : CircleSobolev s E × CircleSobolev s E} (hp : p ∈ neckGraph s E a) (x : AddCircle T) :
    HasSum (fun n : ℤ ↦ (a / fourier 1 x) ^ n • p.2.coeff n)
      (p.1.coeff 0 + p.2.coeff 0 - toContinuousMap T hs p.1 x) := by
  have hF := (hasSum_toContinuousMap T hs p.1).mapL (ContinuousMap.evalCLM ℂ x)
  simp only [ContinuousMap.evalCLM_apply, ContinuousMap.smul_apply', ContinuousMap.const_apply]
    at hF
  replace hF : HasSum (fun n : ℤ ↦ fourier 1 x ^ n • p.1.coeff n) (toContinuousMap T hs p.1 x) :=
    hF.congr_fun fun n ↦ by
      rw [fourier_apply (n := n), fourier_one, AddCircle.toCircle_zsmul, Circle.coe_zpow]
  set z : ℂ := fourier 1 x
  have hpair : HasSum (fun n : ℤ ↦ z ^ n • p.1.coeff n + (a / z) ^ (-n) • p.2.coeff (-n))
      (p.1.coeff 0 + p.2.coeff 0) := by
    convert hasSum_ite_eq (0 : ℤ) (p.1.coeff 0 + p.2.coeff 0) using 1
    funext n
    obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
    · rcases eq_or_ne m 0 with rfl | hm
      · simp
      have hc : ((a / z) ^ m)⁻¹ * a ^ m = z ^ m := by
        rw [div_pow, inv_div, div_mul_cancel₀ _ (pow_ne_zero m ha₀)]
      rw [ite_eq_right (by omega), (hp m hm).2, smul_neg, smul_smul, zpow_neg, zpow_natCast,
        zpow_natCast, hc, add_neg_cancel]
    · rcases eq_or_ne m 0 with rfl | hm
      · simp
      have hc : (z ^ m)⁻¹ * a ^ m = (a / z) ^ m := by
        rw [div_pow, div_eq_mul_inv, mul_comm]
      rw [ite_eq_right (by omega), (hp m hm).1, neg_neg, smul_neg, smul_smul, zpow_neg,
        zpow_natCast, zpow_natCast, hc, neg_add_cancel]
  have h : HasSum (fun n : ℤ ↦ (a / z) ^ (-n) • p.2.coeff (-n))
      (p.1.coeff 0 + p.2.coeff 0 - toContinuousMap T hs p.1 x) :=
    (hpair.sub hF).congr_fun fun n ↦ by rw [add_sub_cancel_left]
  exact (Equiv.neg ℤ).hasSum_iff.1 h

end Boundary

end CircleSobolev

end TauCeti
