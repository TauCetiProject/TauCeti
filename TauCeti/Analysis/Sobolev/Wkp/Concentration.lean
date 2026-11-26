/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Wkp.Zero
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompactSupport
import TauCeti.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Sobolev.Dilation
import TauCeti.Analysis.Distribution.TestFunction.Dilation
import TauCeti.Analysis.Distribution.TestFunction.Translation
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm

/-!
# Concentrating bumps and the critical Sobolev embedding

Let `E` be a real inner product space of dimension `n ≥ 1` and `Ω ⊆ E` a nonempty open set. In
the critical case `k = n + l` of the Sobolev embedding theorem, `W^{k,1}(ℝⁿ)` embeds continuously
into the functions whose derivatives up to order `l` are bounded and continuous, while for
`k > n + l` the embedding of functions supported in a fixed compact set is compact. This file
shows that compactness fails in the critical case, already for functions supported in an
arbitrarily small ball inside `Ω`: the unit ball of `W^{n+l,1}(Ω)` is not relatively compact for
the uniform norm of the `l`-th derivative.

The example is a concentrating bump. For a smooth compactly supported `φ` and `0 < ε ≤ 1`,

`u_ε(x) = ε ^ l φ(ε⁻¹ (x - x₀))`

has `l`-th derivative `D^l u_ε(x) = D^l φ(ε⁻¹ (x - x₀))`, of the same uniform norm as `D^l φ`,
while the `L¹` norm of its `i`-th derivative is `ε ^ (n + l - i)` times that of `D^i φ`. So the
`W^{n+l,1}` norms stay bounded as `ε → 0`, but the `l`-th derivatives concentrate at `x₀`. Taking
`ε = θ ^ j` for a small ratio `θ` and evaluating at a point where `D^l φ` does not vanish, the
`l`-th derivatives of different members of the sequence are a fixed distance apart in the uniform
norm (`TauCeti.Wkp.exists_seq_norm_ofTestFunctionₗ_le_and_le_norm_iteratedFDeriv_sub`).

Consequently no continuous linear map from `W^{n+l,1}(Ω)` to bounded continuous functions that
sends a test function to its `l`-th derivative is a compact operator
(`TauCeti.Wkp.not_isCompactOperator_of_apply_ofTestFunctionₗ_eq_iteratedFDeriv`). At `l = 0` this
says that the critical embedding `W^{n,1}(Ω) → C⁰` is not compact
(`TauCeti.Wkp.not_isCompactOperator_of_apply_ofTestFunctionₗ_eq`). The construction is local, as
the bumps live in an arbitrarily small ball inside `Ω`, so it applies to bounded `Ω`; transport to
compact manifolds is not done here.

## Main results

* `TauCeti.Wkp.exists_seq_norm_ofTestFunctionₗ_le_and_le_norm_iteratedFDeriv_sub`: a sequence of
  test functions in the unit ball of `W^{n+l,1}(Ω)` whose `l`-th derivatives are pairwise
  uniformly separated.
* `TauCeti.Wkp.not_isCompactOperator_of_apply_ofTestFunctionₗ_eq_iteratedFDeriv`: the critical
  map `W^{n+l,1}(Ω) → C^l` is not compact.
* `TauCeti.Wkp.not_isCompactOperator_of_apply_ofTestFunctionₗ_eq`: the critical map
  `W^{n,1}(Ω) → C⁰` is not compact.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Academic Press, 2003,
  Theorem 4.12 (the critical embedding `W^{n,1} → C⁰`) and Theorem 6.3 together with the remarks
  following it (compactness requires a strict margin).
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set TopologicalSpace Metric Module
open scoped ContDiff Distributions ENNReal BoundedContinuousFunction

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### Rescaled profiles -/

/-- The iterated derivatives of the rescaled profile `ε ^ l φ(ε⁻¹ (· - x₀))` are `ε ^ l` times
those of `φ(ε⁻¹ ·)`, translated by `x₀`. -/
private theorem iteratedFDeriv_concentrate {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (ε : ℝ)
    (l i : ℕ) (x₀ : E) :
    (iteratedFDeriv ℝ i fun y => ε ^ l * φ (ε⁻¹ • (y - x₀))) =
      ε ^ l • ((iteratedFDeriv ℝ i fun z => φ (ε⁻¹ • z)) ∘ (· - x₀)) := by
  ext1 x
  have hgx : ContDiffAt ℝ i (fun y => φ (ε⁻¹ • (y - x₀))) x :=
    ((hφ.comp ((contDiff_id.sub contDiff_const).const_smul _)).of_le
      (by exact_mod_cast le_top)).contDiffAt
  simp_rw [← smul_eq_mul (ε ^ l)]
  rw [iteratedFDeriv_const_smul_apply' hgx,
    iteratedFDeriv_comp_sub (f := fun z => φ (ε⁻¹ • z)) i x₀ x, Pi.smul_apply,
    Function.comp_apply]

/-! ### The concentrating sequence -/

/-- A test function on `ball 0 r` whose `l`-th derivative does not vanish at some nonzero point
`y` with `‖y‖ < r`. -/
private theorem exists_profile [FiniteDimensional ℝ E] [Nontrivial E] {r : ℝ} (hr : 0 < r)
    (l : ℕ) :
    ∃ φ : 𝓓(⟨ball (0 : E) r, isOpen_ball⟩, ℝ), ∃ y : E, 0 < ‖y‖ ∧ ‖y‖ < r ∧
      iteratedFDeriv ℝ l φ y ≠ 0 := by
  -- A bump of outer radius `r / 4` centred at a point `a` with `‖a‖ = r / 2`.
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  have : 0 < ‖v‖ := norm_pos_iff.2 hv
  set a : E := (r / (2 * ‖v‖)) • v
  have ha : ‖a‖ = r / 2 := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  let b : ContDiffBump a := ⟨r / 8, r / 4, by positivity, by linarith⟩
  have hsupp : tsupport b = closedBall a (r / 4) := b.tsupport_eq
  have hne : (b : E → ℝ) ≠ 0 := fun h => by
    simpa [h] using b.one_of_mem_closedBall (mem_closedBall_self b.rIn_pos.le)
  obtain ⟨y, hy⟩ := b.hasCompactSupport.exists_iteratedFDeriv_ne_zero (n := l)
    (b.contDiff.of_le (by exact_mod_cast le_top)) hne
  have hyb : y ∈ closedBall a (r / 4) := by
    by_contra h
    exact hy (image_eq_zero_of_notMem_tsupport fun h' =>
      h (hsupp ▸ tsupport_iteratedFDeriv_subset l h'))
  rw [mem_closedBall, dist_eq_norm] at hyb
  refine ⟨⟨b, b.contDiff, b.hasCompactSupport, fun z hz => ?_⟩, y, ?_, ?_, hy⟩
  · rw [hsupp, mem_closedBall, dist_eq_norm] at hz
    rw [TopologicalSpace.Opens.coe_mk, mem_ball_zero_iff]
    linarith [norm_le_norm_add_norm_sub' z a]
  · linarith [norm_le_norm_add_norm_sub' a y, norm_sub_rev a y]
  · linarith [norm_le_norm_add_norm_sub' y a]

/-- The rescaled profile `y ↦ ε ^ l φ(ε⁻¹ (y - x₀))` as a test function on `Ω`, for a test
function `φ` on `ball 0 r`, `ball x₀ r ⊆ Ω` and `0 < ε ≤ 1`: the profile dilated by `ε` and
translated by `x₀`. -/
private def concentrate {r : ℝ} {x₀ : E} {Omega : Opens E} (hΩ : ball x₀ r ⊆ Omega)
    (φ : 𝓓(⟨ball (0 : E) r, isOpen_ball⟩, ℝ)) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) (l : ℕ) :
    𝓓(Omega, ℝ) :=
  ε ^ l • translateTestFunction (V := ⟨ball (0 : E) r, isOpen_ball⟩) (h := x₀)
    (show MapsTo (· + x₀) (ball (0 : E) r) Omega from fun z hz => hΩ <| by
      rwa [mem_ball, dist_eq_norm, add_sub_cancel_right, ← mem_ball_zero_iff])
    (dilateTestFunction (V := ⟨ball (0 : E) r, isOpen_ball⟩) h0.ne'
      (show MapsTo (ε • ·) (ball (0 : E) r) (ball 0 r) from fun z hz => by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg h0.le]
        exact (mul_le_of_le_one_left (norm_nonneg z) h1).trans_lt (mem_ball_zero_iff.1 hz)) φ)

private theorem coe_concentrate {r : ℝ} {x₀ : E} {Omega : Opens E} (hΩ : ball x₀ r ⊆ Omega)
    (φ : 𝓓(⟨ball (0 : E) r, isOpen_ball⟩, ℝ)) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) (l : ℕ) :
    (concentrate hΩ φ h0 h1 l : E → ℝ) = fun y => ε ^ l * φ (ε⁻¹ • (y - x₀)) := by
  ext y
  rw [concentrate, FunLike.coe_smul, Pi.smul_apply, translateTestFunction_apply,
    dilateTestFunction_apply, smul_eq_mul]

/-- The `l`-th derivative of the rescaled profile is `D^l φ(ε⁻¹ (y - x₀))`: the factor `ε ^ l`
exactly compensates the rescaling. -/
private theorem iteratedFDeriv_concentrate_self {r : ℝ} {x₀ : E} {Omega : Opens E}
    (hΩ : ball x₀ r ⊆ Omega) (φ : 𝓓(⟨ball (0 : E) r, isOpen_ball⟩, ℝ)) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε ≤ 1) (l : ℕ) (y : E) :
    iteratedFDeriv ℝ l (concentrate hΩ φ h0 h1 l) y =
      iteratedFDeriv ℝ l φ (ε⁻¹ • (y - x₀)) := by
  rw [coe_concentrate, iteratedFDeriv_concentrate φ.contDiff, Pi.smul_apply, Function.comp_apply,
    iteratedFDeriv_comp_const_smul_apply]
  simp [smul_smul, h0.ne']

/-- Two rescaled profiles at scales `δ` and `ε` are separated at `x₀ + ε • y`: the first has
`l`-th derivative `D^l φ(y)` there, and the second vanishes there as soon as `δ⁻¹ ε y` lies
outside `ball 0 r`. -/
private theorem norm_iteratedFDeriv_concentrate_sub {r : ℝ} {x₀ : E} {Omega : Opens E}
    (hΩ : ball x₀ r ⊆ Omega) (φ : 𝓓(⟨ball (0 : E) r, isOpen_ball⟩, ℝ)) {ε δ : ℝ} (hε0 : 0 < ε)
    (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (l : ℕ) {y : E} (hy : r ≤ δ⁻¹ * ε * ‖y‖) :
    ‖iteratedFDeriv ℝ l (concentrate hΩ φ hε0 hε1 l) (x₀ + ε • y) -
        iteratedFDeriv ℝ l (concentrate hΩ φ hδ0 hδ1 l) (x₀ + ε • y)‖ =
      ‖iteratedFDeriv ℝ l φ y‖ := by
  have hzero : iteratedFDeriv ℝ l φ (δ⁻¹ • (ε • y)) = 0 := by
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have h' : δ⁻¹ • (ε • y) ∈ ball (0 : E) r :=
      φ.tsupport_subset (tsupport_iteratedFDeriv_subset l h)
    rw [mem_ball_zero_iff, smul_smul, norm_smul, Real.norm_of_nonneg (by positivity)] at h'
    linarith
  simp only [iteratedFDeriv_concentrate_self, add_sub_cancel_left, inv_smul_smul₀ hε0.ne', hzero,
    sub_zero]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {mu : Measure E}
  [mu.IsAddHaarMeasure]

/-- The `L¹` norm of the `i`-th derivative of the rescaled profile `ε ^ l φ(ε⁻¹ (· - x₀))` is
`ε ^ l ε ^ (n - i)` times that of `D^i φ`. -/
private theorem lpNorm_iteratedFDeriv_concentrate {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) {ε : ℝ}
    (hε : 0 < ε) (l i : ℕ) (x₀ : E) :
    lpNorm (iteratedFDeriv ℝ i fun y => ε ^ l * φ (ε⁻¹ • (y - x₀))) 1 mu =
      ε ^ l * ε ^ ((finrank ℝ E : ℝ) - i) * lpNorm (iteratedFDeriv ℝ i φ) 1 mu := by
  have hg : ContDiff ℝ ∞ fun z : E => φ (ε⁻¹ • z) := hφ.comp (contDiff_const_smul _)
  rw [iteratedFDeriv_concentrate hφ, ← toReal_eLpNorm,
    eLpNorm_const_smul (ε ^ l) ((iteratedFDeriv ℝ i fun z => φ (ε⁻¹ • z)) ∘ (· - x₀)) 1 mu,
    eLpNorm_comp_measurePreserving
      ((hg.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable)
      (measurePreserving_sub_right mu x₀),
    Measure.eLpNorm_iteratedFDeriv_comp_inv_smul mu (hφ.of_le (by exact_mod_cast le_top)) hε.ne']
  simp [ENNReal.toReal_mul, toReal_eLpNorm, abs_of_pos hε, mul_assoc, Real.rpow_nonneg hε.le]

/-- For `0 < ε ≤ 1` and `i ≤ n + l`, the scaling factor `ε ^ l ε ^ (n - i) = ε ^ (n + l - i)` is
at most one. -/
private theorem pow_mul_rpow_sub_le_one {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) {l i n : ℕ}
    (hi : i ≤ n + l) : ε ^ l * ε ^ ((n : ℝ) - i) ≤ 1 := by
  rw [← Real.rpow_natCast, ← Real.rpow_add h0]
  have hi' : (i : ℝ) ≤ n + l := by exact_mod_cast hi
  exact Real.rpow_le_one h0.le h1 (by linarith)

/-- The `W^{n+l,1}(Ω)` norm of the rescaled profile is at most the sum of the `L¹` norms of the
derivatives of `φ` of orders `0` through `n + l`, uniformly in `0 < ε ≤ 1`. -/
private theorem norm_ofTestFunctionₗ_concentrate_le {r : ℝ} {x₀ : E} {Omega : Opens E}
    (hΩ : ball x₀ r ⊆ Omega) (φ : 𝓓(⟨ball (0 : E) r, isOpen_ball⟩, ℝ)) {ε : ℝ} (h0 : 0 < ε)
    (h1 : ε ≤ 1) (l : ℕ) :
    ‖Wkp.ofTestFunctionₗ (mu := mu) (p := 1) (finrank ℝ E + l) (concentrate hΩ φ h0 h1 l)‖ ≤
      ∑ i ∈ Finset.range (finrank ℝ E + l + 1), lpNorm (iteratedFDeriv ℝ i φ) 1 mu := by
  refine (Wkp.norm_ofTestFunctionₗ_le_sum_lpNorm_iteratedFDeriv _ _).trans
    (Finset.sum_le_sum fun i hi => ?_)
  rw [coe_concentrate, lpNorm_iteratedFDeriv_concentrate φ.contDiff h0]
  exact mul_le_of_le_one_left lpNorm_nonneg
    (pow_mul_rpow_sub_le_one h0 h1 (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)))

/-- The unnormalized concentrating sequence: test functions bounded in `W^{n+l,1}(Ω)` whose
`l`-th derivatives are separated for every pair of indices `i < j`. -/
private theorem exists_seq_norm_ofTestFunctionₗ_le_and_le_norm_iteratedFDeriv_sub_of_lt
    [Nontrivial E] {Omega : Opens E} (hΩ : (Omega : Set E).Nonempty) (l : ℕ) :
    ∃ (w : ℕ → 𝓓(Omega, ℝ)) (C c : ℝ), 0 ≤ C ∧ 0 < c ∧
      (∀ j, ‖Wkp.ofTestFunctionₗ (mu := mu) (p := 1) (finrank ℝ E + l) (w j)‖ ≤ C) ∧
      ∀ i j, i < j → ∃ x, c ≤ ‖iteratedFDeriv ℝ l (w i) x - iteratedFDeriv ℝ l (w j) x‖ := by
  -- A ball `ball x₀ r ⊆ Ω` and a profile on `ball 0 r`.
  obtain ⟨x₀, hx₀⟩ := hΩ
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 Omega.isOpen x₀ hx₀
  obtain ⟨φ, y, hy0, hyr, hy⟩ := exists_profile (E := E) hr l
  -- The scales `θ ^ j` with ratio `θ = ‖y‖ / r < 1`.
  set θ := ‖y‖ / r
  have hθ0 : 0 < θ := div_pos hy0 hr
  have hθ1 : θ ≤ 1 := (div_le_one hr).2 hyr.le
  have hε0 (j : ℕ) : 0 < θ ^ j := pow_pos hθ0 j
  have hε1 (j : ℕ) : θ ^ j ≤ 1 := pow_le_one₀ hθ0.le hθ1
  refine ⟨fun j => concentrate hball φ (hε0 j) (hε1 j) l, _,
    ‖iteratedFDeriv ℝ l φ y‖, Finset.sum_nonneg fun _ _ => lpNorm_nonneg,
    norm_pos_iff.2 hy, fun j => norm_ofTestFunctionₗ_concentrate_le hball φ _ _ l,
    fun i j hij => ⟨x₀ + θ ^ i • y,
      (norm_iteratedFDeriv_concentrate_sub hball φ _ _ _ _ l ?_).ge⟩⟩
  -- At `x₀ + θ ^ i • y` the `j`-th profile vanishes: `θ ^ j ≤ θ ^ i θ` and `r θ = ‖y‖` give
  -- `(θ ^ j)⁻¹ θ ^ i ‖y‖ ≥ r`.
  have hθj : θ ^ j ≤ θ ^ i * θ := by
    rw [← Nat.add_sub_cancel' hij.le, pow_add]
    exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hθ0.le hθ1 (by omega)) (hε0 i).le
  have hrθ : r * θ = ‖y‖ := mul_div_cancel₀ _ hr.ne'
  rw [inv_mul_eq_div, div_mul_eq_mul_div, le_div_iff₀ (hε0 j), ← hrθ]
  nlinarith [hε0 i]

namespace Wkp

/-- **Concentrating bumps.** In a nonempty open set `Ω` of a space of dimension `n ≥ 1`, there is
a sequence of test functions in the closed unit ball of `W^{n+l,1}(Ω)` whose `l`-th derivatives
are pairwise separated by a fixed positive distance in the uniform norm. -/
theorem exists_seq_norm_ofTestFunctionₗ_le_and_le_norm_iteratedFDeriv_sub [Nontrivial E]
    {Omega : Opens E} (hΩ : (Omega : Set E).Nonempty) (l : ℕ) :
    ∃ (u : ℕ → 𝓓(Omega, ℝ)) (c : ℝ), 0 < c ∧
      (∀ j, ‖ofTestFunctionₗ (mu := mu) (p := 1) (finrank ℝ E + l) (u j)‖ ≤ 1) ∧
      ∀ i j, i ≠ j → ∃ x, c ≤ ‖iteratedFDeriv ℝ l (u i) x - iteratedFDeriv ℝ l (u j) x‖ := by
  obtain ⟨w, C, c, hC, hc, hw, hsep⟩ :=
    exists_seq_norm_ofTestFunctionₗ_le_and_le_norm_iteratedFDeriv_sub_of_lt (mu := mu) hΩ l
  -- Normalize by `(C + 1)⁻¹`, and treat `j < i` by symmetry of the distance.
  have hpos : 0 ≤ (C + 1)⁻¹ := by positivity
  have hsmul (k : ℕ) (x : E) : iteratedFDeriv ℝ l ((C + 1)⁻¹ • w k : 𝓓(Omega, ℝ)) x =
      (C + 1)⁻¹ • iteratedFDeriv ℝ l (w k) x := by
    rw [FunLike.coe_smul]
    exact iteratedFDeriv_const_smul_apply
      (((w k).contDiff.of_le (by exact_mod_cast le_top)).contDiffAt)
  refine ⟨fun j => (C + 1)⁻¹ • w j, (C + 1)⁻¹ * c, mul_pos (by positivity) hc, fun j => ?_,
    fun i j hij => ?_⟩
  · rw [map_smul, norm_smul, Real.norm_of_nonneg hpos, inv_mul_le_iff₀ (by positivity), mul_one]
    exact (hw j).trans (le_add_of_nonneg_right zero_le_one)
  · obtain ⟨x, hx⟩ : ∃ x, c ≤ ‖iteratedFDeriv ℝ l (w i) x - iteratedFDeriv ℝ l (w j) x‖ := by
      rcases lt_or_gt_of_ne hij with h | h
      · exact hsep i j h
      · simpa only [norm_sub_rev] using hsep j i h
    refine ⟨x, ?_⟩
    rw [hsmul, hsmul, ← smul_sub, norm_smul, Real.norm_of_nonneg hpos]
    exact mul_le_mul_of_nonneg_left hx hpos

/-- **The critical embedding `W^{n+l,1}(Ω) → C^l` is not compact.** In a nonempty open set `Ω` of
a space of dimension `n ≥ 1`, no continuous linear map from `W^{n+l,1}(Ω)` to bounded continuous
functions with values in `l`-multilinear maps that sends each test function to its `l`-th
derivative is a compact operator. -/
theorem not_isCompactOperator_of_apply_ofTestFunctionₗ_eq_iteratedFDeriv [Nontrivial E]
    {Omega : Opens E} (hΩ : (Omega : Set E).Nonempty) {l : ℕ}
    (T : Wkp mu Omega 1 (finrank ℝ E + l) →L[ℝ] E →ᵇ (E [×l]→L[ℝ] ℝ))
    (hT : ∀ (ψ : 𝓓(Omega, ℝ)) (x : E),
      T (ofTestFunctionₗ (finrank ℝ E + l) ψ) x = iteratedFDeriv ℝ l ψ x) :
    ¬ IsCompactOperator T := by
  intro hK
  obtain ⟨u, c, hc, hu, hsep⟩ :=
    exists_seq_norm_ofTestFunctionₗ_le_and_le_norm_iteratedFDeriv_sub (mu := mu) hΩ l
  obtain ⟨i, j, hij, hlt⟩ := hK.exists_dist_lt_of_norm_le hu hc
  obtain ⟨x, hx⟩ := hsep i j hij.ne
  have h := BoundedContinuousFunction.dist_coe_le_dist
    (f := T (ofTestFunctionₗ (finrank ℝ E + l) (u i)))
    (g := T (ofTestFunctionₗ (finrank ℝ E + l) (u j))) x
  rw [hT, hT, dist_eq_norm] at h
  exact (hx.trans h).not_gt hlt

/-- **The critical embedding `W^{n,1}(Ω) → C⁰` is not compact.** In a nonempty open set `Ω` of a
space of dimension `n ≥ 1`, no continuous linear map from `W^{n,1}(Ω)` to bounded continuous
functions that is the identity on test functions is a compact operator. -/
theorem not_isCompactOperator_of_apply_ofTestFunctionₗ_eq [Nontrivial E] {Omega : Opens E}
    (hΩ : (Omega : Set E).Nonempty) (T : Wkp mu Omega 1 (finrank ℝ E) →L[ℝ] E →ᵇ ℝ)
    (hT : ∀ (ψ : 𝓓(Omega, ℝ)) (x : E), T (ofTestFunctionₗ (finrank ℝ E) ψ) x = ψ x) :
    ¬ IsCompactOperator T := by
  -- Identify `ℝ` with the `0`-multilinear maps and apply the `l = 0` case of the `C^l` statement.
  let g : ℝ →L[ℝ] E [×0]→L[ℝ] ℝ := (continuousMultilinearCurryFin0 ℝ E ℝ).symm
  refine fun hK => not_isCompactOperator_of_apply_ofTestFunctionₗ_eq_iteratedFDeriv (l := 0) hΩ
    ((g.compLeftContinuousBounded E).comp T) (fun ψ x => ?_)
    (by rw [ContinuousLinearMap.coe_comp]; exact hK.clm_comp _)
  rw [iteratedFDeriv_zero_eq_comp, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compLeftContinuousBounded_apply, Function.comp_apply]
  -- The order `finrank ℝ E + 0` must match the domain of `T`, so `rw [Nat.add_zero]` gives an
  -- ill-typed motive; `hT` applies up to the definitional equality `finrank ℝ E + 0 = finrank ℝ E`.
  exact congrArg g (hT ψ x)

end Wkp

end TauCeti
