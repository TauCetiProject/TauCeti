/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Bounds
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Topology.MetricSpace.ProperSpace
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Flat
import TauCeti.Analysis.Calculus.IteratedFDeriv.Homogeneous
import TauCeti.Analysis.Calculus.IteratedFDeriv.Reciprocal

/-!
# Symbols on a punctured ball

A map `f` defined near a point `c` of a real normed space is a *symbol of order `ℓ` at `c`* on the
ball of radius `r` when it is smooth on the punctured ball `B(c, r) ∖ {c}` and each of its iterated
derivatives obeys the bound `‖D^k f z‖ ≤ C_k ‖z - c‖ ^ (ℓ - k)` there, with a constant depending
only on `k` (`TauCeti.IsPuncturedBallSymbol`). The order `ℓ` is any real number. The prototype is
`z ↦ ‖z - c‖ ^ ℓ` (`TauCeti.isPuncturedBallSymbol_norm_sub_rpow`), and more generally every map
that is smooth away from `c` and positively homogeneous of degree `ℓ` about `c`
(`TauCeti.isPuncturedBallSymbol_of_homogeneous`). A smooth map with bounded derivatives whose
derivatives of order less than `n` vanish at `c` is a symbol of order `n`
(`TauCeti.isPuncturedBallSymbol_of_iteratedFDeriv_eq_zero`; in finite dimension, smoothness on a
larger ball suffices, `TauCeti.isPuncturedBallSymbol_of_contDiffOn_of_iteratedFDeriv_eq_zero`).

Such classes measure the order of vanishing of a map at an isolated singular point, derivatives
included. They are the bookkeeping device of the local analysis of pseudoholomorphic curves near a
critical point, in the proof of the Micallef–White normal form, where the coefficients and
remainders of the Cauchy–Riemann equation in adapted coordinates are shown to vanish to a given
order at the singular point.

## The calculus

* Symbols of a fixed order form a vector space; a symbol of order `ℓ` is one of every smaller
  order, on a bounded ball (`TauCeti.IsPuncturedBallSymbol.mono_order`).
* Orders add under every continuous bilinear map, hence under products and scalar multiplication
  (`TauCeti.IsPuncturedBallSymbol.bilinear`, `TauCeti.IsPuncturedBallSymbol.mul`,
  `TauCeti.IsPuncturedBallSymbol.smul`).
* Differentiation lowers the order by one (`TauCeti.IsPuncturedBallSymbol.fderiv`), and `k`
  differentiations by `k` (`TauCeti.IsPuncturedBallSymbol.iteratedFDeriv`).
* A smooth map with bounded derivatives along the image of a symbol of nonnegative order,
  composed with it, gives a symbol of order `0` (`TauCeti.IsPuncturedBallSymbol.comp`). In
  particular the reciprocal of a scalar symbol of order `0` that is bounded away from `0` is again
  of order `0` (`TauCeti.IsPuncturedBallSymbol.inv`).

## Removability

A symbol of positive order extends continuously across `c` by `0`. Above order `m`, the extension
`Function.update f c 0` is `C^m` on the whole ball
(`TauCeti.IsPuncturedBallSymbol.contDiffOn_update`), its derivatives of order less than `ℓ` are
the extensions by `0` of those of `f` (`TauCeti.IsPuncturedBallSymbol.iteratedFDeriv_update`),
and from order `1` it is Lipschitz on the ball
(`TauCeti.IsPuncturedBallSymbol.exists_lipschitzOnWith_update`). So from order `2` the extension
is `C¹` with Lipschitz derivative, that is of class `C^{1,1}`, on the whole ball
(`TauCeti.IsPuncturedBallSymbol.exists_lipschitzOnWith_fderiv_update`).

The solution operators of the Cauchy–Riemann equation on symbols, which raise the order by one,
are not treated here.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  American Mathematical Society Colloquium Publications 52, 2012, Appendix E.5–E.6 (functions of
  order `ℓ` on a punctured disc and their use in the proof of the Micallef–White theorem).
* M. Micallef and B. White, *The structure of branch points in minimal surfaces and in
  pseudoholomorphic curves*, Ann. of Math. (2) **141** (1995), 35–85.
-/

public section

open Set Metric Function Filter Topology
open scoped ContDiff Nat NNReal

namespace TauCeti

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  {ℓ m : ℝ} {c : E} {r : ℝ} {f : E → F}

/-- A map `f` is a *symbol of order `ℓ` at `c`* on the ball of radius `r` when it is smooth on the
punctured ball `B(c, r) ∖ {c}` and, for each `k`, its `k`-th iterated derivative is bounded there
by a constant times `‖z - c‖ ^ (ℓ - k)`. -/
def IsPuncturedBallSymbol (ℓ : ℝ) (c : E) (r : ℝ) (f : E → F) : Prop :=
  ContDiffOn ℝ ∞ f (ball c r \ {c}) ∧
    ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ ball c r \ {c}, ‖iteratedFDeriv ℝ k f z‖ ≤ C * ‖z - c‖ ^ (ℓ - k)

/-- Unfolding `TauCeti.IsPuncturedBallSymbol`. -/
theorem isPuncturedBallSymbol_iff :
    IsPuncturedBallSymbol ℓ c r f ↔ ContDiffOn ℝ ∞ f (ball c r \ {c}) ∧
      ∀ k : ℕ, ∃ C : ℝ, ∀ z ∈ ball c r \ {c}, ‖iteratedFDeriv ℝ k f z‖ ≤ C * ‖z - c‖ ^ (ℓ - k) :=
  Iff.rfl

omit [NormedSpace ℝ E] in
/-- The punctured ball is open. -/
private theorem isOpen_ball_diff : IsOpen (ball c r \ {c}) :=
  isOpen_ball.sdiff isClosed_singleton

omit [NormedSpace ℝ E] in
private theorem norm_sub_pos_of_mem {z : E} (hz : z ∈ ball c r \ {c}) : 0 < ‖z - c‖ :=
  norm_pos_iff.2 (sub_ne_zero.2 hz.2)

omit [NormedSpace ℝ E] in
private theorem norm_sub_lt_of_mem {z : E} (hz : z ∈ ball c r \ {c}) : ‖z - c‖ < r :=
  mem_ball_iff_norm.1 hz.1

namespace IsPuncturedBallSymbol

/-- A symbol is smooth on the punctured ball. -/
theorem contDiffOn (hf : IsPuncturedBallSymbol ℓ c r f) : ContDiffOn ℝ ∞ f (ball c r \ {c}) :=
  hf.1

/-- A symbol is smooth at every point of the punctured ball. -/
theorem contDiffAt (hf : IsPuncturedBallSymbol ℓ c r f) {z : E} (hz : z ∈ ball c r \ {c}) :
    ContDiffAt ℝ ∞ f z :=
  hf.1.contDiffAt (isOpen_ball_diff.mem_nhds hz)

/-- The derivative bounds of a symbol, with a nonnegative constant. -/
theorem exists_bound (hf : IsPuncturedBallSymbol ℓ c r f) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ z ∈ ball c r \ {c}, ‖iteratedFDeriv ℝ k f z‖ ≤ C * ‖z - c‖ ^ (ℓ - k) := by
  obtain ⟨C, hC⟩ := hf.2 k
  refine ⟨max C 0, le_max_right _ _, fun z hz ↦ (hC z hz).trans ?_⟩
  gcongr
  exact le_max_left _ _

/-- A symbol on a ball is a symbol on every smaller ball. -/
theorem mono_radius (hf : IsPuncturedBallSymbol ℓ c r f) {r' : ℝ} (hr : r' ≤ r) :
    IsPuncturedBallSymbol ℓ c r' f :=
  ⟨hf.1.mono (sdiff_subset_sdiff_left (ball_subset_ball hr)), fun k ↦
    (hf.2 k).imp fun _ hC z hz ↦ hC z ⟨ball_subset_ball hr hz.1, hz.2⟩⟩

/-- On a ball of finite radius a symbol of order `ℓ` is a symbol of every smaller order. -/
theorem mono_order (hf : IsPuncturedBallSymbol ℓ c r f) {ℓ' : ℝ} (hℓ : ℓ' ≤ ℓ) :
    IsPuncturedBallSymbol ℓ' c r f := by
  refine ⟨hf.1, fun k ↦ ?_⟩
  obtain ⟨C, hC0, hC⟩ := hf.exists_bound k
  refine ⟨C * r ^ (ℓ - ℓ'), fun z hz ↦ (hC z hz).trans ?_⟩
  have hρ := norm_sub_pos_of_mem hz
  rw [show ℓ - k = (ℓ - ℓ') + (ℓ' - k) by ring, Real.rpow_add hρ, ← mul_assoc]
  gcongr
  exact (norm_sub_lt_of_mem hz).le

end IsPuncturedBallSymbol

/-! ### The vector space of symbols of a given order -/

/-- The zero map is a symbol of every order. -/
theorem isPuncturedBallSymbol_zero (ℓ : ℝ) (c : E) (r : ℝ) :
    IsPuncturedBallSymbol ℓ c r (0 : E → F) :=
  ⟨contDiffOn_const, fun k ↦ ⟨0, fun z _ ↦ by simp⟩⟩

/-- A constant is a symbol of order `0`. -/
theorem isPuncturedBallSymbol_const (y : F) (c : E) (r : ℝ) :
    IsPuncturedBallSymbol 0 c r fun _ : E ↦ y := by
  refine ⟨contDiffOn_const, fun k ↦ ⟨‖y‖, fun z _ ↦ ?_⟩⟩
  rcases k with _ | k
  · simp
  · rw [iteratedFDeriv_const_of_ne k.succ_ne_zero]
    simp only [Pi.zero_apply, norm_zero]
    positivity

namespace IsPuncturedBallSymbol

variable {g : E → F}

/-- Symbols of the same order add. -/
theorem add (hf : IsPuncturedBallSymbol ℓ c r f) (hg : IsPuncturedBallSymbol ℓ c r g) :
    IsPuncturedBallSymbol ℓ c r (f + g) := by
  refine ⟨hf.1.add hg.1, fun k ↦ ?_⟩
  obtain ⟨C, -, hC⟩ := hf.exists_bound k
  obtain ⟨D, -, hD⟩ := hg.exists_bound k
  refine ⟨C + D, fun z hz ↦ ?_⟩
  rw [iteratedFDeriv_add_apply ((hf.contDiffAt hz).of_le (mod_cast le_top))
    ((hg.contDiffAt hz).of_le (mod_cast le_top)), add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hC z hz) (hD z hz))

/-- The negative of a symbol is a symbol of the same order. -/
theorem neg (hf : IsPuncturedBallSymbol ℓ c r f) : IsPuncturedBallSymbol ℓ c r (-f) := by
  refine ⟨hf.1.neg, fun k ↦ (hf.2 k).imp fun C hC z hz ↦ ?_⟩
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact hC z hz

/-- Symbols of the same order subtract. -/
theorem sub (hf : IsPuncturedBallSymbol ℓ c r f) (hg : IsPuncturedBallSymbol ℓ c r g) :
    IsPuncturedBallSymbol ℓ c r (f - g) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

/-! ### Products -/

/-- Orders add under a continuous bilinear map. -/
theorem bilinear (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G}
    (hf : IsPuncturedBallSymbol ℓ c r f) (hg : IsPuncturedBallSymbol m c r g) :
    IsPuncturedBallSymbol (ℓ + m) c r fun z ↦ B (f z) (g z) := by
  refine ⟨(B.contDiff.comp_contDiffOn hf.1).clm_apply hg.1, fun k ↦ ?_⟩
  choose Cf hCf0 hCf using hf.exists_bound
  choose Cg _ hCg using hg.exists_bound
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * Cf i * Cg (k - i), fun z hz ↦ ?_⟩
  have hs : IsOpen (ball c r \ {c}) := isOpen_ball_diff
  have hρ := norm_sub_pos_of_mem hz
  have h := B.norm_iteratedFDerivWithin_le_of_bilinear hf.1 hg.1 hs.uniqueDiffOn hz
    (n := k) (mod_cast le_top)
  simp only [iteratedFDerivWithin_of_isOpen _ hs hz] at h
  refine h.trans ?_
  rw [mul_assoc, Finset.sum_mul]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi ↦ ?_) (norm_nonneg B)
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  calc (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i f z‖ * ‖iteratedFDeriv ℝ (k - i) g z‖
      ≤ (k.choose i : ℝ) * (Cf i * ‖z - c‖ ^ (ℓ - i)) *
          (Cg (k - i) * ‖z - c‖ ^ (m - ↑(k - i))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (hCf i z hz) (Nat.cast_nonneg _)) (hCg (k - i) z hz)
          (norm_nonneg _)
          (mul_nonneg (Nat.cast_nonneg _)
            (mul_nonneg (hCf0 i) (Real.rpow_nonneg (norm_nonneg _) _)))
    _ = (k.choose i : ℝ) * Cf i * Cg (k - i) * ‖z - c‖ ^ (ℓ + m - k) := by
        rw [show ℓ + m - k = (ℓ - i) + (m - ↑(k - i)) by push_cast [Nat.cast_sub hik]; ring,
          Real.rpow_add hρ]
        ring

/-- Orders add under multiplication. -/
theorem mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {f g : E → A}
    (hf : IsPuncturedBallSymbol ℓ c r f) (hg : IsPuncturedBallSymbol m c r g) :
    IsPuncturedBallSymbol (ℓ + m) c r (f * g) := by
  simpa [Pi.mul_def] using hf.bilinear (ContinuousLinearMap.mul ℝ A) hg

/-- Orders add under scalar multiplication. -/
theorem smul {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 F]
    [IsScalarTower ℝ 𝕜 F] {f : E → 𝕜} {g : E → F}
    (hf : IsPuncturedBallSymbol ℓ c r f) (hg : IsPuncturedBallSymbol m c r g) :
    IsPuncturedBallSymbol (ℓ + m) c r (f • g) := by
  simpa [Pi.smul_def'] using hf.bilinear (ContinuousLinearMap.lsmul ℝ 𝕜) hg

/-- A constant multiple of a symbol is a symbol of the same order. -/
theorem const_smul {𝕜 : Type*} [NormedField 𝕜] [NormedAlgebra ℝ 𝕜] [NormedSpace 𝕜 F]
    [IsScalarTower ℝ 𝕜 F] (a : 𝕜) (hg : IsPuncturedBallSymbol m c r g) :
    IsPuncturedBallSymbol m c r (a • g) := by
  have h := (isPuncturedBallSymbol_const a c r).smul hg
  rw [zero_add] at h
  convert h using 1

/-! ### Derivatives and compositions -/

/-- Differentiation lowers the order of a symbol by one. -/
protected theorem fderiv (hf : IsPuncturedBallSymbol ℓ c r f) :
    IsPuncturedBallSymbol (ℓ - 1) c r (fderiv ℝ f) := by
  refine ⟨((contDiffOn_infty_iff_fderiv_of_isOpen isOpen_ball_diff).1 hf.1).2, fun k ↦ ?_⟩
  refine (hf.2 (k + 1)).imp fun C hC z hz ↦ ?_
  rw [norm_iteratedFDeriv_fderiv, show ℓ - 1 - k = ℓ - ↑(k + 1) by push_cast; ring]
  exact hC z hz

/-- At distance `ρ ≤ r` from the center, a derivative bound `C ρ ^ (ℓ - i)` of nonnegative order
is a bound `(K / ρ) ^ i` once `C r ^ ℓ ≤ K` and `1 ≤ K`. This is the form of the bounds that
Faà di Bruno's estimate consumes. -/
private theorem mul_rpow_sub_le_div_pow {C K ρ : ℝ} {i : ℕ} (hℓ : 0 ≤ ℓ) (hC : 0 ≤ C)
    (hρ : 0 < ρ) (hρr : ρ ≤ r) (hCK : C * r ^ ℓ ≤ K) (hK : 1 ≤ K) (hi : 1 ≤ i) :
    C * ρ ^ (ℓ - i) ≤ (K / ρ) ^ i := by
  rw [Real.rpow_sub hρ, Real.rpow_natCast, div_pow, ← mul_div_assoc]
  gcongr
  calc C * ρ ^ ℓ ≤ C * r ^ ℓ := by gcongr
    _ ≤ K := hCK
    _ ≤ K ^ i := le_self_pow₀ hK (by omega)

/-- A symbol of nonnegative order composed with a smooth map whose derivatives are bounded along
its image is a symbol of order `0`. -/
theorem comp {g : F → G} {t : Set F} (hf : IsPuncturedBallSymbol ℓ c r f) (hℓ : 0 ≤ ℓ)
    (hg : ContDiffOn ℝ ∞ g t) (ht : IsOpen t) (hft : MapsTo f (ball c r \ {c}) t)
    (hgb : ∀ k : ℕ, ∃ M, ∀ z ∈ ball c r \ {c}, ‖iteratedFDeriv ℝ k g (f z)‖ ≤ M) :
    IsPuncturedBallSymbol 0 c r fun z ↦ g (f z) := by
  refine ⟨hg.comp hf.1 hft, fun k ↦ ?_⟩
  choose Cf hCf0 hCf using hf.exists_bound
  choose Mg hMg using hgb
  -- Faà di Bruno's bound with the derivatives of `f` measured on the scale `‖z - c‖`: the
  -- derivative of order `i` is at most `(K / ‖z - c‖) ^ i`.
  set M := ∑ i ∈ Finset.range (k + 1), max (Mg i) 0
  set K := 1 + ∑ i ∈ Finset.range (k + 1), Cf i * r ^ ℓ
  refine ⟨k ! * M * K ^ k, fun z hz ↦ ?_⟩
  have hs : IsOpen (ball c r \ {c}) := isOpen_ball_diff
  have hρ := norm_sub_pos_of_mem hz
  have hρr := (norm_sub_lt_of_mem hz).le
  have hK1 : 1 ≤ K := le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ ↦ mul_nonneg (hCf0 i) (Real.rpow_nonneg (hρ.le.trans hρr) _))
  have hM : ∀ i ≤ k, ‖iteratedFDerivWithin ℝ i g t (f z)‖ ≤ M := by
    intro i hi
    rw [iteratedFDerivWithin_of_isOpen i ht (hft hz)]
    exact (hMg i z hz).trans ((le_max_left _ _).trans (Finset.single_le_sum
      (f := fun i ↦ max (Mg i) 0) (fun i _ ↦ le_max_right _ _)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hi))))
  have hD : ∀ i, 1 ≤ i → i ≤ k → ‖iteratedFDerivWithin ℝ i f (ball c r \ {c}) z‖ ≤
      (K / ‖z - c‖) ^ i := by
    intro i hi1 hik
    rw [iteratedFDerivWithin_of_isOpen i hs hz]
    refine (hCf i z hz).trans (mul_rpow_sub_le_div_pow hℓ (hCf0 i) hρ hρr ?_ hK1 hi1)
    exact (Finset.single_le_sum (f := fun j ↦ Cf j * r ^ ℓ)
      (fun j _ ↦ mul_nonneg (hCf0 j) (Real.rpow_nonneg (hρ.le.trans hρr) _))
      (Finset.mem_range.2 (Nat.lt_succ_of_le hik))).trans (le_add_of_nonneg_left zero_le_one)
  have h := norm_iteratedFDerivWithin_comp_le hg hf.1 (mod_cast le_top) ht.uniqueDiffOn
    hs.uniqueDiffOn hft hz hM hD
  rw [iteratedFDerivWithin_of_isOpen k hs hz] at h
  refine h.trans_eq ?_
  rw [div_pow, zero_sub, Real.rpow_neg hρ.le, Real.rpow_natCast]
  ring

/-- The reciprocal of a scalar symbol of order `0` that is bounded away from `0` is a symbol of
order `0`. -/
theorem inv {𝕜 : Type*} [RCLike 𝕜] {f : E → 𝕜} (hf : IsPuncturedBallSymbol 0 c r f) {δ : ℝ}
    (hδ : 0 < δ) (hfδ : ∀ z ∈ ball c r \ {c}, δ ≤ ‖f z‖) :
    IsPuncturedBallSymbol 0 c r fun z ↦ (f z)⁻¹ := by
  have hne : ∀ z ∈ ball c r \ {c}, f z ≠ 0 := fun z hz ↦
    norm_pos_iff.1 (hδ.trans_le (hfδ z hz))
  refine hf.comp le_rfl (contDiffOn_inv ℝ) isOpen_compl_singleton (fun z hz ↦ hne z hz)
    fun k ↦ ⟨k ! / δ ^ (k + 1), fun z hz ↦ ?_⟩
  rw [← (contDiffAt_inv 𝕜 (hne z hz) (n := k)).restrictScalars_iteratedFDeriv (𝕜 := ℝ),
    comp_apply, ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_inv k (f z)]
  gcongr
  exact hfδ z hz

end IsPuncturedBallSymbol

/-! ### Examples -/

/-- A smooth map with bounded derivatives on the ball, whose derivatives of order less than `n`
vanish at the center, is a symbol of order `n`. -/
theorem isPuncturedBallSymbol_of_iteratedFDeriv_eq_zero {n : ℕ}
    (hf : ContDiffOn ℝ ∞ f (ball c r))
    (hbdd : ∀ k : ℕ, ∃ M, ∀ z ∈ ball c r, ‖iteratedFDeriv ℝ k f z‖ ≤ M)
    (hzero : ∀ i < n, iteratedFDeriv ℝ i f c = 0) :
    IsPuncturedBallSymbol n c r f := by
  refine ⟨hf.mono sdiff_subset, fun k ↦ ?_⟩
  rcases le_or_gt r 0 with hr | hr
  · refine ⟨0, fun z hz ↦ ?_⟩
    have := (norm_sub_pos_of_mem hz).trans (norm_sub_lt_of_mem hz)
    linarith
  have hfat : ∀ y ∈ ball c r, ContDiffAt ℝ ∞ f y := fun y hy ↦
    hf.contDiffAt (isOpen_ball.mem_nhds hy)
  obtain ⟨M, hM⟩ := hbdd k
  rcases lt_or_ge k n with hkn | hnk
  · -- Below the order of vanishing, iterate the mean value inequality from the center.
    obtain ⟨p, rfl⟩ : ∃ p, n = p + 1 := ⟨n - 1, by omega⟩
    obtain ⟨M', hM'⟩ := hbdd (p + 1)
    refine ⟨M', fun z hz ↦ ?_⟩
    have h := norm_iteratedFDeriv_sub_le_of_iteratedFDeriv_eq_zero (k := p)
      (fun y hy ↦ (hfat y hy).of_le (mod_cast le_top)) (convex_ball c r) (mem_ball_self hr) hM'
      (fun i _ hi ↦ hzero i (by omega)) (p - k) (by omega) z hz.1
    rw [show p - (p - k) = k by omega, hzero k hkn, sub_zero] at h
    refine h.trans_eq ?_
    rw [← Real.rpow_natCast]
    congr 2
    push_cast [show p - k + 1 = p + 1 - k by omega, Nat.cast_sub hkn.le]
    ring
  · -- Above it, the derivatives are bounded and `‖z - c‖ ^ (n - k)` is bounded below.
    refine ⟨max M 0 * r ^ ((k : ℝ) - n), fun z hz ↦ ?_⟩
    have hρ := norm_sub_pos_of_mem hz
    calc ‖iteratedFDeriv ℝ k f z‖ ≤ max M 0 * (r ^ ((k : ℝ) - n) * r ^ ((n : ℝ) - k)) := by
          rw [← Real.rpow_add hr, show (k : ℝ) - n + (n - k) = 0 by ring, Real.rpow_zero,
            mul_one]
          exact (hM z hz.1).trans (le_max_left _ _)
      _ ≤ max M 0 * r ^ ((k : ℝ) - n) * ‖z - c‖ ^ ((n : ℝ) - k) := by
          rw [← mul_assoc]
          exact mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_nonpos hρ (norm_sub_lt_of_mem hz).le
              (sub_nonpos.2 (Nat.cast_le.2 hnk)))
            (mul_nonneg (le_max_right _ _) (Real.rpow_nonneg hr.le _))

/-- In finite dimension, a map smooth on a larger ball whose derivatives of order less than `n`
vanish at the center is a symbol of order `n`. -/
theorem isPuncturedBallSymbol_of_contDiffOn_of_iteratedFDeriv_eq_zero [FiniteDimensional ℝ E]
    {n : ℕ} {R : ℝ} (hrR : r < R) (hf : ContDiffOn ℝ ∞ f (ball c R))
    (hzero : ∀ i < n, iteratedFDeriv ℝ i f c = 0) :
    IsPuncturedBallSymbol n c r f := by
  refine isPuncturedBallSymbol_of_iteratedFDeriv_eq_zero (hf.mono (ball_subset_ball hrR.le))
    (fun k ↦ ?_) hzero
  have hcont : ContinuousOn (iteratedFDeriv ℝ k f) (closedBall c r) :=
    ((hf.continuousOn_iteratedFDerivWithin (mod_cast le_top) isOpen_ball.uniqueDiffOn).congr
      fun _ hy ↦ (iteratedFDerivWithin_of_isOpen k isOpen_ball hy).symm).mono
      (closedBall_subset_ball hrR)
  obtain ⟨M, hM⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hcont
  exact ⟨M, fun z hz ↦ hM z (ball_subset_closedBall hz)⟩

/-- A map smooth away from the origin and positively homogeneous of degree `ℓ`, translated to `c`,
is a symbol of order `ℓ` at `c` on every ball. -/
theorem isPuncturedBallSymbol_of_homogeneous [ProperSpace E] {g : E → F}
    (hg : ContDiffOn ℝ ∞ g {0}ᶜ) (hhom : ∀ t : ℝ, 0 < t → ∀ x, g (t • x) = t ^ ℓ • g x)
    (c : E) (r : ℝ) :
    IsPuncturedBallSymbol ℓ c r fun z ↦ g (z - c) := by
  refine ⟨hg.comp (contDiff_id.sub contDiff_const).contDiffOn fun z hz ↦ sub_ne_zero.2 hz.2,
    fun k ↦ ?_⟩
  -- The derivative is bounded on the unit sphere, and homogeneity scales it from there.
  have hcont : ContinuousOn (iteratedFDeriv ℝ k g) (sphere 0 1) :=
    ((hg.continuousOn_iteratedFDerivWithin (mod_cast le_top) isOpen_compl_singleton.uniqueDiffOn
      ).congr fun _ hy ↦ (iteratedFDerivWithin_of_isOpen k isOpen_compl_singleton hy).symm).mono
      fun x hx ↦ ne_of_mem_sphere hx one_ne_zero
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn hcont
  refine ⟨M, fun z hz ↦ ?_⟩
  have hρ := norm_sub_pos_of_mem hz
  have hu : ‖z - c‖⁻¹ • (z - c) ∈ sphere (0 : E) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hρ.ne']
  have hscale := norm_iteratedFDeriv_smul_of_homogeneous hhom hρ (x := ‖z - c‖⁻¹ • (z - c)) (j := k)
  rw [smul_inv_smul₀ hρ.ne'] at hscale
  rw [iteratedFDeriv_comp_sub, hscale, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hM _ hu) (by positivity)

/-- The power `‖z - c‖ ^ ℓ` of the distance to `c` is a symbol of order `ℓ` at `c`. -/
theorem isPuncturedBallSymbol_norm_sub_rpow {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] (ℓ : ℝ) (c : E) (r : ℝ) :
    IsPuncturedBallSymbol ℓ c r fun z ↦ ‖z - c‖ ^ ℓ := by
  refine isPuncturedBallSymbol_of_homogeneous (g := fun x : E ↦ ‖x‖ ^ ℓ) (fun x hx ↦ ?_)
    (fun t ht x ↦ ?_) c r
  · exact ((contDiffAt_norm ℝ hx).rpow_const_of_ne (norm_ne_zero_iff.2 hx)).contDiffWithinAt
  · rw [norm_smul, Real.norm_of_nonneg ht.le, Real.mul_rpow ht.le (norm_nonneg x), smul_eq_mul]

/-! ### Removability of the singular point -/

namespace IsPuncturedBallSymbol

/-- The iterated derivatives of a symbol of order `ℓ` are symbols of order `ℓ - k`. -/
protected theorem iteratedFDeriv (hf : IsPuncturedBallSymbol ℓ c r f) (k : ℕ) :
    IsPuncturedBallSymbol (ℓ - k) c r (iteratedFDeriv ℝ k f) := by
  refine ⟨fun z hz ↦ ((hf.contDiffAt hz).iteratedFDeriv_right (m := ∞) (by simp)).contDiffWithinAt,
    fun j ↦ (hf.2 (j + k)).imp fun C hC z hz ↦ ?_⟩
  rw [norm_iteratedFDeriv_iteratedFDeriv, show ℓ - k - j = ℓ - ↑(j + k) by push_cast; ring]
  exact hC z hz

/-- A symbol of positive order tends to `0` at the singular point. -/
theorem tendsto_nhdsNE (hf : IsPuncturedBallSymbol ℓ c r f) (hℓ : 0 < ℓ) (hr : 0 < r) :
    Tendsto f (𝓝[≠] c) (𝓝 0) := by
  obtain ⟨C, -, hC⟩ := hf.exists_bound 0
  refine squeeze_zero_norm' ?_ (a := fun z ↦ C * ‖z - c‖ ^ ℓ) ?_
  · filter_upwards [inter_mem_nhdsWithin {c}ᶜ (ball_mem_nhds c hr)] with z hz
    simpa using hC z ⟨hz.2, hz.1⟩
  · have : Continuous fun z : E ↦ C * ‖z - c‖ ^ ℓ :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        fun _ ↦ Or.inr hℓ.le)
    simpa [Real.zero_rpow hℓ.ne'] using (this.tendsto c).mono_left nhdsWithin_le_nhds

variable [DecidableEq E]

/-- A symbol of positive order extends continuously by `0` to the whole ball. -/
theorem continuousOn_update (hf : IsPuncturedBallSymbol ℓ c r f) (hℓ : 0 < ℓ) :
    ContinuousOn (update f c 0) (ball c r) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  intro z hz
  refine ContinuousAt.continuousWithinAt ?_
  rcases eq_or_ne z c with rfl | hzc
  · exact continuousAt_update_same.2 (hf.tendsto_nhdsNE hℓ hr)
  · refine ((hf.contDiffAt ⟨hz, hzc⟩).continuousAt).congr ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hzc] with y hy
    exact (update_of_ne hy _ _).symm

/-- Above order `1`, the extension of a symbol by `0` is differentiable at the singular point,
with derivative `0`. -/
theorem hasFDerivAt_update (hf : IsPuncturedBallSymbol ℓ c r f) (hℓ : 1 < ℓ) (hr : 0 < r) :
    HasFDerivAt (update f c 0) (0 : E →L[ℝ] F) c := by
  rw [hasFDerivAt_iff_tendsto]
  obtain ⟨C, -, hC⟩ := hf.exists_bound 0
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) ?_
    (g := fun z ↦ C * ‖z - c‖ ^ (ℓ - 1)) ?_
  · filter_upwards [ball_mem_nhds c hr] with z hz
    rcases eq_or_ne z c with rfl | hzc
    · simp [Real.zero_rpow (show ℓ - 1 ≠ 0 by linarith)]
    have hρ : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hzc)
    have h : ‖f z‖ ≤ C * ‖z - c‖ ^ ℓ := by simpa using hC z ⟨hz, hzc⟩
    have hval : ‖update f c 0 z - update f c 0 c - (0 : E →L[ℝ] F) (z - c)‖ = ‖f z‖ := by
      simp [update_of_ne hzc]
    rw [hval, Real.rpow_sub_one hρ.ne', inv_mul_le_iff₀ hρ]
    calc ‖f z‖ ≤ C * ‖z - c‖ ^ ℓ := h
      _ = ‖z - c‖ * (C * (‖z - c‖ ^ ℓ / ‖z - c‖)) := by field_simp
  · have : Continuous fun z : E ↦ C * ‖z - c‖ ^ (ℓ - 1) :=
      continuous_const.mul ((continuous_id.sub continuous_const).norm.rpow_const
        fun _ ↦ Or.inr (by linarith))
    simpa [Real.zero_rpow (show ℓ - 1 ≠ 0 by linarith)] using this.tendsto c

/-- Above order `1`, the extension of a symbol by `0` is differentiable on the whole ball. -/
theorem differentiableOn_update (hf : IsPuncturedBallSymbol ℓ c r f) (hℓ : 1 < ℓ) :
    DifferentiableOn ℝ (update f c 0) (ball c r) := by
  rcases le_or_gt r 0 with hr | hr
  · rw [ball_eq_empty.2 hr]
    exact differentiableOn_empty
  intro z hz
  rcases eq_or_ne z c with rfl | hzc
  · exact (hf.hasFDerivAt_update hℓ hr).differentiableAt.differentiableWithinAt
  · refine (((hf.contDiffAt ⟨hz, hzc⟩).differentiableAt (by simp)).congr_of_eventuallyEq
      ?_).differentiableWithinAt
    filter_upwards [isOpen_compl_singleton.mem_nhds hzc] with y hy
    exact update_of_ne hy _ _

/-- Above order `1`, the derivative of the extension of a symbol by `0` is the extension by `0` of
its derivative. -/
theorem fderiv_update (hf : IsPuncturedBallSymbol ℓ c r f) (hℓ : 1 < ℓ) (hr : 0 < r) :
    fderiv ℝ (update f c 0) = update (fderiv ℝ f) c 0 := by
  funext z
  rcases eq_or_ne z c with rfl | hz
  · rw [update_self, (hf.hasFDerivAt_update hℓ hr).fderiv]
  · rw [update_of_ne hz]
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with y hy
    exact update_of_ne hy _ _

/-- Below the order of a symbol, the iterated derivatives of its extension by `0` are the
extensions by `0` of its iterated derivatives. -/
theorem iteratedFDeriv_update (hf : IsPuncturedBallSymbol ℓ c r f) (hr : 0 < r) {k : ℕ}
    (hk : (k : ℝ) < ℓ) :
    iteratedFDeriv ℝ k (update f c 0) = update (iteratedFDeriv ℝ k f) c 0 := by
  induction k with
  | zero =>
    funext z
    ext v
    rcases eq_or_ne z c with rfl | hz
    · simp
    · simp [update_of_ne hz]
  | succ k ih =>
    have hk' : 1 < ℓ - k := by push_cast at hk; linarith
    rw [iteratedFDeriv_succ_eq_comp_left, ih (by push_cast at hk; linarith),
      (hf.iteratedFDeriv k).fderiv_update hk' hr]
    funext z
    rcases eq_or_ne z c with rfl | hz
    · simp only [comp_apply, update_self]
      exact LinearIsometryEquiv.map_zero _
    · rw [comp_apply, update_of_ne hz, update_of_ne hz, iteratedFDeriv_succ_eq_comp_left,
        comp_apply]

/-- Above order `m`, the extension of a symbol by `0` is `C^m` on the ball. -/
theorem contDiffOn_update (hf : IsPuncturedBallSymbol ℓ c r f) {m : ℕ} (hm : (m : ℝ) < ℓ) :
    ContDiffOn ℝ m (update f c 0) (ball c r) := by
  rcases le_or_gt r 0 with hr | hr
  · simp [ball_eq_empty.2 hr]
  -- On the open ball the iterated derivatives of order below `ℓ` are those of the symbol,
  -- extended by `0`.
  have hD : ∀ j : ℕ, (j : ℝ) < ℓ → EqOn (iteratedFDerivWithin ℝ j (update f c 0) (ball c r))
      (update (iteratedFDeriv ℝ j f) c 0) (ball c r) := fun j hj z hz ↦ by
    rw [iteratedFDerivWithin_of_isOpen j isOpen_ball hz, hf.iteratedFDeriv_update hr hj]
  have h := contDiffOn_of_continuousOn_differentiableOn (𝕜 := ℝ) (f := update f c 0)
    (s := ball c r) (n := (m : ℕ∞)) (fun j hj ↦ ?_) (fun j hj ↦ ?_)
  · exact_mod_cast h
  · have hj : (j : ℝ) ≤ m := by exact_mod_cast hj
    exact ((hf.iteratedFDeriv j).continuousOn_update (by linarith)).congr (hD j (by linarith))
  · have hj : (j : ℝ) + 1 ≤ m := by exact_mod_cast Order.add_one_le_of_lt hj
    exact ((hf.iteratedFDeriv j).differentiableOn_update (by linarith)).congr
      (hD j (by linarith))

omit [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- The extension by `0` of a symbol vanishing to first order at `c` is bounded on the ball by a
multiple of the distance to `c`. -/
private theorem norm_update_le (hℓ : 1 ≤ ℓ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ z ∈ ball c r \ {c}, ‖f z‖ ≤ C * ‖z - c‖ ^ ℓ) {z : E} (hz : z ∈ ball c r) :
    ‖update f c 0 z‖ ≤ C * r ^ (ℓ - 1) * ‖z - c‖ := by
  rcases eq_or_ne z c with rfl | hzc
  · simp
  have hρ : 0 < ‖z - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hzc)
  rw [update_of_ne hzc]
  calc ‖f z‖ ≤ C * ‖z - c‖ ^ ℓ := hC z ⟨hz, hzc⟩
    _ = C * ‖z - c‖ ^ (ℓ - 1) * ‖z - c‖ := by
        rw [mul_assoc, ← Real.rpow_add_one hρ.ne', sub_add_cancel]
    _ ≤ C * r ^ (ℓ - 1) * ‖z - c‖ := by
        gcongr
        exact (mem_ball_iff_norm.1 hz).le

/-- From order `1` on, the extension of a symbol by `0` is Lipschitz on the ball. -/
theorem exists_lipschitzOnWith_update (hf : IsPuncturedBallSymbol ℓ c r f) (hℓ : 1 ≤ ℓ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (update f c 0) (ball c r) := by
  rcases le_or_gt r 0 with hr | hr
  · exact ⟨0, by simp [ball_eq_empty.2 hr]⟩
  obtain ⟨C₀, hC₀0, hC₀⟩ := hf.exists_bound 0
  obtain ⟨C₁, hC₁0, hC₁⟩ := hf.exists_bound 1
  have hC₀' : ∀ z ∈ ball c r \ {c}, ‖f z‖ ≤ C₀ * ‖z - c‖ ^ ℓ := fun z hz ↦ by
    simpa using hC₀ z hz
  have hK0 : 0 ≤ (C₀ + C₁) * r ^ (ℓ - 1) := by positivity
  refine ⟨Real.toNNReal ((C₀ + C₁) * r ^ (ℓ - 1)),
    LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_⟩
  rw [Real.coe_toNNReal _ hK0, dist_eq_norm, dist_eq_norm]
  by_cases hseg : c ∈ segment ℝ x y
  · -- Through the singular point, both values are small compared with the distances to `c`.
    have hxy : ‖x - c‖ + ‖c - y‖ = ‖x - y‖ := by
      simpa [dist_eq_norm] using dist_add_dist_of_mem_segment hseg
    calc ‖update f c 0 x - update f c 0 y‖ ≤ ‖update f c 0 x‖ + ‖update f c 0 y‖ :=
          norm_sub_le _ _
      _ ≤ C₀ * r ^ (ℓ - 1) * ‖x - c‖ + C₀ * r ^ (ℓ - 1) * ‖c - y‖ := by
          rw [norm_sub_rev c y]
          exact add_le_add (norm_update_le hℓ hC₀0 hC₀' hx) (norm_update_le hℓ hC₀0 hC₀' hy)
      _ = C₀ * r ^ (ℓ - 1) * ‖x - y‖ := by rw [← hxy]; ring
      _ ≤ (C₀ + C₁) * r ^ (ℓ - 1) * ‖x - y‖ := by
          gcongr
          linarith
  · -- Away from the singular point, apply the mean value inequality along the segment.
    have hsub : segment ℝ x y ⊆ ball c r \ {c} := fun w hw ↦
      ⟨(convex_ball c r).segment_subset hx hy hw, fun h ↦ hseg (h ▸ hw)⟩
    have hcx : x ≠ c := fun h ↦ hseg (h ▸ left_mem_segment ℝ x y)
    have hcy : y ≠ c := fun h ↦ hseg (h ▸ right_mem_segment ℝ x y)
    rw [update_of_ne hcx, update_of_ne hcy, norm_sub_rev, norm_sub_rev x y]
    refine ((convex_segment x y).norm_image_sub_le_of_norm_fderiv_le (C := C₁ * r ^ (ℓ - 1))
      (fun w hw ↦ (hf.contDiffAt (hsub hw)).differentiableAt (by simp)) (fun w hw ↦ ?_)
      (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)).trans ?_
    · have h := hC₁ w (hsub hw)
      rw [norm_iteratedFDeriv_one, Nat.cast_one] at h
      refine h.trans ?_
      gcongr
      exact (norm_sub_lt_of_mem (hsub hw)).le
    · gcongr
      linarith

/-- From order `2` on, the extension of a symbol by `0` is `C¹` with Lipschitz derivative on the
ball. -/
theorem exists_lipschitzOnWith_fderiv_update (hf : IsPuncturedBallSymbol ℓ c r f) (hℓ : 2 ≤ ℓ) :
    ∃ K : ℝ≥0, LipschitzOnWith K (fderiv ℝ (update f c 0)) (ball c r) := by
  rcases le_or_gt r 0 with hr | hr
  · exact ⟨0, by simp [ball_eq_empty.2 hr]⟩
  rw [hf.fderiv_update (by linarith) hr]
  exact hf.fderiv.exists_lipschitzOnWith_update (by linarith)

end IsPuncturedBallSymbol

end TauCeti
