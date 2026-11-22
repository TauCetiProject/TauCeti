/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.PhragmenLindelof.VerticalStrip
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Phragmén–Lindelöf with polynomial edge bounds

Let `f` be holomorphic on the open vertical strip `a < re s < b`, continuous on its closure and
of finite order there. If `‖f‖ ≤ C₁ (1 + |im s|) ^ α` on the left edge and
`‖f‖ ≤ C₂ (1 + |im s|) ^ β` on the right edge, then on the closed strip

`‖f s‖ ≤ K C₁ ^ (1 - θ) C₂ ^ θ (1 + |im s|) ^ ((1 - θ) α + θ β)`, where `θ = (re s - a) / (b - a)`,

with a constant `K` depending only on `a`, `b`, `α` and `β`, chosen before `f`, `C₁` and `C₂`.
The edge constants are interpolated geometrically and the edge exponents linearly. This is the
form in which convexity bounds for L-functions are derived: the edge constants carry the
arithmetic conductor and the exponents carry the archimedean growth, and the constant `K` is
uniform in both.

The proof divides `f` by the holomorphic weight `x(s) ^ (ℓ(s) / 2)`, where
`x(s) = (1 + (s - a)) (1 + (b - s))` and `ℓ` is the complex affine function with
`re ℓ(s) = (1 - θ) α + θ β`. On the closed strip `x(s)` has real part at least `1 + (im s) ^ 2`,
so it stays in the slit plane, its norm is comparable to `(1 + |im s|) ^ 2`, and its argument is
`O(1 / |im s|)`. The last point makes the factor `exp (arg x(s) * im ℓ(s) / 2)` that the
imaginary part of the exponent contributes bounded, so the weight has norm comparable to
`(1 + |im s|) ^ re ℓ(s)` with constants independent of the height. The quotient has constant
edge bounds and is still of finite order, and the three-lines theorem of
`TauCeti.PhragmenLindelof.norm_le_interp_of_isBigO_exp_rpow` interpolates them.

## Main results

* `TauCeti.PhragmenLindelof.exists_norm_le_interp_mul_one_add_abs_im_rpow`: the bound above, with
  two edge constants.
* `TauCeti.PhragmenLindelof.exists_norm_le_mul_one_add_abs_im_rpow`: the same with one constant
  `C` on both edges.

## References

* E. C. Titchmarsh, *The Theory of Functions*, 2nd ed., §5.65, for the principle with power
  bounds on the edges.
* H. Iwaniec and E. Kowalski, *Analytic Number Theory*, §5.2, for its use in convexity bounds of
  L-functions.
-/

public section

open Complex Set Filter Asymptotics Bornology
open scoped Topology

namespace TauCeti.PhragmenLindelof

/-! ### The weight -/

/-- The quadratic base of the weight. On the closed strip `a ≤ re s ≤ b` its real part is at least
`1 + (im s) ^ 2`. -/
private noncomputable def stripBase (a b : ℝ) (s : ℂ) : ℂ := (1 + (s - a)) * (1 + (b - s))

private theorem stripBase_re (a b : ℝ) (s : ℂ) :
    (stripBase a b s).re = (1 + (s.re - a)) * (1 + (b - s.re)) + s.im ^ 2 := by
  simp only [stripBase, mul_re, add_re, one_re, sub_re, ofReal_re, add_im, one_im, sub_im,
    ofReal_im]
  ring

private theorem stripBase_im (a b : ℝ) (s : ℂ) :
    (stripBase a b s).im = s.im * (a + b - 2 * s.re) := by
  simp only [stripBase, mul_im, add_re, one_re, sub_re, ofReal_re, add_im, one_im, sub_im,
    ofReal_im]
  ring

private theorem one_add_sq_le_stripBase_re {a b : ℝ} {s : ℂ} (hs : s.re ∈ Icc a b) :
    1 + s.im ^ 2 ≤ (stripBase a b s).re := by
  have h₁ : 0 ≤ s.re - a := sub_nonneg.mpr hs.1
  have h₂ : 0 ≤ b - s.re := sub_nonneg.mpr hs.2
  rw [stripBase_re]
  nlinarith [mul_nonneg h₁ h₂]

private theorem stripBase_re_pos {a b : ℝ} {s : ℂ} (hs : s.re ∈ Icc a b) :
    0 < (stripBase a b s).re :=
  lt_of_lt_of_le (by positivity) (one_add_sq_le_stripBase_re hs)

/-- The norm of the base is comparable to `(1 + |im s|) ^ 2`, with ratio at most
`2 (1 + (b - a)) ^ 2` in either direction. -/
private theorem norm_stripBase_bounds {a b : ℝ} {s : ℂ} (hs : s.re ∈ Icc a b) :
    (1 + |s.im|) ^ 2 ≤ 2 * (1 + (b - a)) ^ 2 * ‖stripBase a b s‖ ∧
      ‖stripBase a b s‖ ≤ 2 * (1 + (b - a)) ^ 2 * (1 + |s.im|) ^ 2 := by
  have hab : 0 ≤ b - a := by linarith [hs.1, hs.2]
  have hre := one_add_sq_le_stripBase_re hs
  have hnorm : (stripBase a b s).re ≤ ‖stripBase a b s‖ := re_le_norm _
  have ht : |s.im| ^ 2 = s.im ^ 2 := sq_abs _
  have ht0 := abs_nonneg s.im
  constructor
  · nlinarith [sq_nonneg (|s.im| - 1), sq_nonneg (b - a)]
  · have hup := norm_le_abs_re_add_abs_im (stripBase a b s)
    rw [abs_of_pos (stripBase_re_pos hs), stripBase_im, stripBase_re, abs_mul] at hup
    have him : |a + b - 2 * s.re| ≤ b - a := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h₂ : 0 ≤ 1 + (b - s.re) := by linarith [hs.2]
    have hprod : (1 + (s.re - a)) * (1 + (b - s.re)) ≤ (1 + (b - a)) ^ 2 := by
      rw [sq]
      exact mul_le_mul (by linarith [hs.2]) (by linarith [hs.1]) h₂ (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left him ht0, sq_nonneg (1 + (b - a)),
      mul_nonneg ht0 (sq_nonneg (1 + (b - a))), mul_nonneg (sq_nonneg s.im) hab]

/-- The argument of the base is `O(1 / |im s|)`, uniformly on the closed strip. -/
private theorem abs_arg_stripBase_mul_abs_im_le {a b : ℝ} {s : ℂ} (hs : s.re ∈ Icc a b) :
    |arg (stripBase a b s)| * |s.im| ≤ Real.pi / 2 * (b - a) := by
  set x := stripBase a b s
  have hre : 0 < x.re := stripBase_re_pos hs
  have hx : 0 < ‖x‖ := norm_pos_iff.mpr fun h ↦ by simp [h] at hre
  have harg : |arg x| ≤ Real.pi / 2 := abs_arg_le_pi_div_two_iff.mpr hre.le
  -- Jordan's inequality `2 / π * θ ≤ sin θ` on `[0, π / 2]`, applied to `θ = |arg x|`.
  have hsin : Real.sin |arg x| ≤ |x.im| / ‖x‖ := by
    rcases abs_cases (arg x) with ⟨h, -⟩ | ⟨h, -⟩ <;> rw [h]
    · rw [sin_arg]
      gcongr
      exact le_abs_self _
    · rw [Real.sin_neg, sin_arg, ← neg_div]
      gcongr
      exact neg_le_abs _
  -- Jordan's inequality turns this into `|arg x| * ‖x‖ ≤ π / 2 * |x.im|`.
  have hj : |arg x| * ‖x‖ ≤ Real.pi / 2 * |x.im| := by
    have h := (TauCeti.le_pi_div_two_mul_sin (abs_nonneg _) harg).trans
      (mul_le_mul_of_nonneg_left hsin (by positivity))
    rw [mul_div_assoc', le_div_iff₀ hx] at h
    exact h
  have him : |x.im| ≤ |s.im| * (b - a) := by
    rw [stripBase_im, abs_mul]
    gcongr
    exact abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hnorm : 1 + s.im ^ 2 ≤ ‖x‖ := (one_add_sq_le_stripBase_re hs).trans (re_le_norm x)
  have hab : 0 ≤ b - a := by linarith [hs.1, hs.2]
  -- `|arg x| * |t| * ‖x‖ ≤ π / 2 * |x.im| * |t| ≤ π / 2 (b - a) t² ≤ π / 2 (b - a) ‖x‖`
  have key : |arg x| * |s.im| * ‖x‖ ≤ Real.pi / 2 * (b - a) * ‖x‖ :=
    calc |arg x| * |s.im| * ‖x‖ = |arg x| * ‖x‖ * |s.im| := by ring
      _ ≤ Real.pi / 2 * |x.im| * |s.im| := by gcongr
      _ ≤ Real.pi / 2 * (|s.im| * (b - a)) * |s.im| := by gcongr
      _ = Real.pi / 2 * (b - a) * s.im ^ 2 := by rw [← sq_abs s.im]; ring
      _ ≤ Real.pi / 2 * (b - a) * ‖x‖ := by
        gcongr
        linarith
  exact le_of_mul_le_mul_right key hx

/-- Real powers of `‖x(s)‖` are comparable to the same powers of `(1 + |im s|) ^ 2`, up to the
factor `(2 (1 + (b - a)) ^ 2) ^ P` for every exponent of absolute value at most `P`. -/
private theorem rpow_norm_stripBase_bounds {a b p P : ℝ} {s : ℂ} (hs : s.re ∈ Icc a b)
    (hp : |p| ≤ P) :
    ‖stripBase a b s‖ ^ p ≤ (2 * (1 + (b - a)) ^ 2) ^ P * ((1 + |s.im|) ^ 2) ^ p ∧
      ((1 + |s.im|) ^ 2) ^ p ≤ (2 * (1 + (b - a)) ^ 2) ^ P * ‖stripBase a b s‖ ^ p := by
  set N := 2 * (1 + (b - a)) ^ 2
  have hN : 1 ≤ N := by nlinarith [show 0 ≤ b - a by linarith [hs.1, hs.2]]
  have hN0 : 0 < N := one_pos.trans_le hN
  -- the comparison is symmetric in the two quantities
  have key {r u : ℝ} (hu : 0 < u) (h₁ : u ≤ N * r) (h₂ : r ≤ N * u) : r ^ p ≤ N ^ P * u ^ p := by
    have hr : 0 < r := pos_of_mul_pos_right (hu.trans_le h₁) hN0.le
    have hru := Real.rpow_le_rpow_abs (div_pos hr hu).le ((div_le_iff₀ hu).mpr h₂)
      (by rw [inv_div]; exact (div_le_iff₀ hr).mpr h₁) p
    rw [Real.div_rpow hr.le hu.le, div_le_iff₀ (by positivity)] at hru
    exact hru.trans
      (mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hN hp) (by positivity))
  have hx : 0 < ‖stripBase a b s‖ :=
    lt_of_lt_of_le (by positivity) ((one_add_sq_le_stripBase_re hs).trans (re_le_norm _))
  obtain ⟨hlo, hhi⟩ := norm_stripBase_bounds hs
  exact ⟨key (by positivity) hlo hhi, key hx hhi hlo⟩

/-- The real exponent `(1 - θ) α + θ β`, `θ = (σ - a) / (b - a)`, written as an affine function
of `σ`. -/
private theorem interp_exponent_eq (a b α β σ : ℝ) :
    α + (β - α) / (b - a) * (σ - a) =
      (1 - (σ - a) / (b - a)) * α + (σ - a) / (b - a) * β := by
  ring

/-- On `[a, b]` the interpolated exponent is a convex combination of `α` and `β`. -/
private theorem abs_interp_exponent_le {a b α β σ : ℝ} (hab : a < b) (hσ : σ ∈ Icc a b) :
    |α + (β - α) / (b - a) * (σ - a)| ≤ |α| + |β| := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hθ0 : 0 ≤ (σ - a) / (b - a) := div_nonneg (by linarith [hσ.1]) hba.le
  have hθ1 : (σ - a) / (b - a) ≤ 1 := (div_le_one hba).mpr (by linarith [hσ.2])
  rw [interp_exponent_eq]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by linarith), abs_of_nonneg hθ0]
  nlinarith [abs_nonneg α, abs_nonneg β]

/-- The weight `x(s) ^ (-ℓ(s) / 2)`, where `ℓ` is the complex affine function with
`ℓ(a) = α` and `ℓ(b) = β` on the real axis. -/
private noncomputable def stripWeight (a b α β : ℝ) (s : ℂ) : ℂ :=
  stripBase a b s ^ (-(α + ((β - α) / (b - a) : ℝ) * (s - a)) / 2)

/-- The constant comparing the weight with a power of `1 + |im s|`. -/
private noncomputable def weightConst (a b α β : ℝ) : ℝ :=
  Real.exp (Real.pi / 4 * |β - α|) * (2 * (1 + (b - a)) ^ 2) ^ ((|α| + |β|) / 2)

private theorem one_le_weightConst {a b : ℝ} (hab : a ≤ b) (α β : ℝ) :
    1 ≤ weightConst a b α β := by
  unfold weightConst
  have h1 : 1 ≤ 2 * (1 + (b - a)) ^ 2 := by nlinarith [sub_nonneg.mpr hab]
  exact one_le_mul_of_one_le_of_one_le (Real.one_le_exp (by positivity))
    (Real.one_le_rpow h1 (by positivity))

private theorem weightConst_pos {a b : ℝ} (hab : a ≤ b) (α β : ℝ) :
    0 < weightConst a b α β :=
  one_pos.trans_le (one_le_weightConst hab α β)

/-- The norm of the weight, split into a real power of `‖x(s)‖` and the factor contributed by the
imaginary part of the exponent. -/
private theorem norm_stripWeight_eq {a b α β : ℝ} {s : ℂ} (hs : s.re ∈ Icc a b) :
    ‖stripWeight a b α β s‖ =
      ‖stripBase a b s‖ ^ (-(α + (β - α) / (b - a) * (s.re - a)) / 2) *
        Real.exp (arg (stripBase a b s) * ((β - α) / (b - a) * s.im / 2)) := by
  have hx0 : stripBase a b s ≠ 0 := fun h ↦ by simpa [h] using stripBase_re_pos hs
  rw [stripWeight, norm_cpow_of_ne_zero hx0, div_eq_mul_inv, ← Real.exp_neg]
  congr 2
  · simp only [neg_re, div_ofNat_re, add_re, ofReal_re, mul_re, ofReal_im, sub_re, sub_im,
      zero_mul, sub_zero]
  · simp only [neg_im, div_ofNat_im, add_im, ofReal_im, mul_im, ofReal_re, sub_im, sub_re,
      zero_mul, zero_add, add_zero]
    ring

/-- The factor contributed by the imaginary part of the exponent is bounded independently of the
height. -/
private theorem abs_arg_stripBase_mul_le {a b α β : ℝ} (hab : a < b) {s : ℂ}
    (hs : s.re ∈ Icc a b) :
    |arg (stripBase a b s) * ((β - α) / (b - a) * s.im / 2)| ≤ Real.pi / 4 * |β - α| := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have h := abs_arg_stripBase_mul_abs_im_le hs
  have hc : |(β - α) / (b - a)| * (b - a) = |β - α| := by
    rw [abs_div, abs_of_pos hba, div_mul_cancel₀ _ hba.ne']
  rw [abs_mul, abs_div, abs_mul, abs_two]
  calc |arg (stripBase a b s)| * (|(β - α) / (b - a)| * |s.im| / 2)
      = |(β - α) / (b - a)| / 2 * (|arg (stripBase a b s)| * |s.im|) := by ring
    _ ≤ |(β - α) / (b - a)| / 2 * (Real.pi / 2 * (b - a)) := by gcongr
    _ = Real.pi / 4 * (|(β - α) / (b - a)| * (b - a)) := by ring
    _ = Real.pi / 4 * |β - α| := by rw [hc]

/-- On the closed strip the weight has norm comparable to `(1 + |im s|) ^ (-re ℓ(s))`. -/
private theorem norm_stripWeight_bounds {a b α β : ℝ} (hab : a < b) {s : ℂ}
    (hs : s.re ∈ Icc a b) :
    ‖stripWeight a b α β s‖ ≤
        weightConst a b α β * (1 + |s.im|) ^ (-(α + (β - α) / (b - a) * (s.re - a))) ∧
      (1 + |s.im|) ^ (-(α + (β - α) / (b - a) * (s.re - a))) ≤
        weightConst a b α β * ‖stripWeight a b α β s‖ := by
  set ℓ := α + (β - α) / (b - a) * (s.re - a)
  set x := stripBase a b s
  set e := Real.exp (arg x * ((β - α) / (b - a) * s.im / 2))
  set κ := Real.exp (Real.pi / 4 * |β - α|)
  have hℓ : |-ℓ / 2| ≤ (|α| + |β|) / 2 := by
    rw [abs_div, abs_neg, abs_two]
    gcongr
    exact abs_interp_exponent_le hab hs
  obtain ⟨hup, hdown⟩ := rpow_norm_stripBase_bounds hs hℓ
  rw [Real.sq_rpow_div_two (by positivity)] at hup hdown
  have harg := abs_le.mp (abs_arg_stripBase_mul_le (α := α) (β := β) hab hs)
  have he₁ : e ≤ κ := Real.exp_le_exp.mpr harg.2
  have he₂ : 1 ≤ κ * e := by
    rw [← Real.exp_add]
    exact Real.one_le_exp (by linarith [harg.1])
  rw [norm_stripWeight_eq hs]
  unfold weightConst
  constructor
  · calc ‖x‖ ^ (-ℓ / 2) * e
        ≤ ((2 * (1 + (b - a)) ^ 2) ^ ((|α| + |β|) / 2) * (1 + |s.im|) ^ (-ℓ)) * κ := by gcongr
      _ = _ := by ring
  · calc (1 + |s.im|) ^ (-ℓ) ≤ (2 * (1 + (b - a)) ^ 2) ^ ((|α| + |β|) / 2) * ‖x‖ ^ (-ℓ / 2) :=
          hdown
      _ ≤ (2 * (1 + (b - a)) ^ 2) ^ ((|α| + |β|) / 2) * ‖x‖ ^ (-ℓ / 2) * (κ * e) :=
          le_mul_of_one_le_right (by positivity) he₂
      _ = _ := by ring

private theorem differentiableOn_stripWeight (a b α β : ℝ) :
    DifferentiableOn ℂ (stripWeight a b α β) (re ⁻¹' Icc a b) := by
  intro s hs
  have hslit : stripBase a b s ∈ slitPlane := mem_slitPlane_iff.mpr (Or.inl (stripBase_re_pos hs))
  refine DifferentiableAt.differentiableWithinAt ?_
  exact DifferentiableAt.cpow (by unfold stripBase; fun_prop) (by fun_prop) hslit

/-- On the closed strip the weight grows at most like `exp ((|α| + |β|) ‖s‖)`. -/
private theorem norm_stripWeight_le_exp {a b α β : ℝ} (hab : a < b) {s : ℂ}
    (hs : s.re ∈ Icc a b) :
    ‖stripWeight a b α β s‖ ≤ weightConst a b α β * Real.exp ((|α| + |β|) * ‖s‖) := by
  refine (norm_stripWeight_bounds hab hs).1.trans
    (mul_le_mul_of_nonneg_left ?_ (weightConst_pos hab.le α β).le)
  have hℓ : -(α + (β - α) / (b - a) * (s.re - a)) ≤ |α| + |β| :=
    (neg_le_abs _).trans (abs_interp_exponent_le hab hs)
  calc (1 + |s.im|) ^ (-(α + (β - α) / (b - a) * (s.re - a)))
      ≤ (1 + |s.im|) ^ (|α| + |β|) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg s.im]) hℓ
    _ ≤ Real.exp |s.im| ^ (|α| + |β|) := by
        gcongr
        linarith [Real.add_one_le_exp |s.im|]
    _ = Real.exp (|s.im| * (|α| + |β|)) := (Real.exp_mul _ _).symm
    _ ≤ Real.exp ((|α| + |β|) * ‖s‖) := by
        rw [mul_comm]
        gcongr
        exact abs_im_le_norm s

/-- The weighted function is still of finite order on the strip. -/
private theorem isBigO_stripWeight_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a b α β : ℝ} (hab : a < b)
    (hg : ∃ A B : ℝ, f =O[cobounded ℂ ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      (fun w ↦ Real.exp (B * ‖w‖ ^ A))) :
    ∃ A B : ℝ, (fun s ↦ stripWeight a b α β s • f s) =O[cobounded ℂ ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      (fun w ↦ Real.exp (B * ‖w‖ ^ A)) := by
  obtain ⟨A, B, hf⟩ := hg
  set q := |α| + |β|
  have hq : 0 ≤ q := by positivity
  refine ⟨max A 1, |B| + q, ?_⟩
  have hw : stripWeight a b α β =O[cobounded ℂ ⊓ 𝓟 (re ⁻¹' Ioo a b)]
      fun w ↦ Real.exp (q * ‖w‖) := by
    refine IsBigO.of_bound (weightConst a b α β) ?_
    filter_upwards [(eventually_mem_principal _).filter_mono inf_le_right] with s hs
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact norm_stripWeight_le_exp hab (Ioo_subset_Icc_self hs)
  have hcob : ∀ᶠ s in cobounded ℂ ⊓ 𝓟 (re ⁻¹' Ioo a b), 1 ≤ ‖s‖ :=
    (tendsto_norm_cobounded_atTop.eventually (eventually_ge_atTop 1)).filter_mono inf_le_left
  refine isBigO_norm_left.mp ?_
  simp_rw [norm_smul]
  refine (hw.norm_left.mul hf.norm_left).trans (IsBigO.of_bound 1 ?_)
  filter_upwards [hcob] with s hs1
  rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (Real.exp_nonneg _),
    ← Real.exp_add, Real.exp_le_exp]
  have h1 : ‖s‖ ≤ ‖s‖ ^ max A 1 := by
    simpa using Real.rpow_le_rpow_of_exponent_le hs1 (le_max_right A 1)
  have h2 : ‖s‖ ^ A ≤ ‖s‖ ^ max A 1 := Real.rpow_le_rpow_of_exponent_le hs1 (le_max_left A 1)
  have h3 : B * ‖s‖ ^ A ≤ |B| * ‖s‖ ^ max A 1 :=
    (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity)).trans
      (mul_le_mul_of_nonneg_left h2 (abs_nonneg B))
  nlinarith [mul_le_mul_of_nonneg_left h1 hq]

/-- A polynomial bound of the matching exponent on a vertical line becomes a constant bound after
weighting. -/
private theorem norm_stripWeight_smul_le_of_edge {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {a b α β σ γ C : ℝ} (hab : a < b) (hσ : σ ∈ Icc a b)
    (hℓ : α + (β - α) / (b - a) * (σ - a) = γ)
    (hf : ∀ v : ℂ, v.re = σ → ‖f v‖ ≤ C * (1 + |v.im|) ^ γ) {v : ℂ} (hv : v.re = σ) :
    ‖stripWeight a b α β v • f v‖ ≤ weightConst a b α β * C := by
  have hbound := (norm_stripWeight_bounds (α := α) (β := β) hab (hv ▸ hσ : v.re ∈ Icc a b)).1
  rw [hv, hℓ] at hbound
  have hpos : 0 < 1 + |v.im| := by positivity
  have hK₀ := (weightConst_pos (α := α) (β := β) hab.le).le
  rw [norm_smul]
  calc ‖stripWeight a b α β v‖ * ‖f v‖
      ≤ weightConst a b α β * (1 + |v.im|) ^ (-γ) * (C * (1 + |v.im|) ^ γ) :=
        mul_le_mul hbound (hf v hv) (norm_nonneg _) (mul_nonneg hK₀ (by positivity))
    _ = weightConst a b α β * C * ((1 + |v.im|) ^ (-γ) * (1 + |v.im|) ^ γ) := by ring
    _ = weightConst a b α β * C := by
        rw [← Real.rpow_add hpos, neg_add_cancel, Real.rpow_zero, mul_one]

/-- A bound for the weighted function at a point of the strip gives a polynomial bound for the
function itself. -/
private theorem norm_le_of_norm_stripWeight_smul_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {f : ℂ → E} {a b α β M : ℝ} (hab : a < b) {z : ℂ} (hz : z.re ∈ Icc a b)
    (h : ‖stripWeight a b α β z • f z‖ ≤ M) :
    ‖f z‖ ≤ weightConst a b α β * M *
      (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * α + (z.re - a) / (b - a) * β) := by
  have hlow := (norm_stripWeight_bounds (α := α) (β := β) hab hz).2
  rw [interp_exponent_eq] at hlow
  set ℓ := (1 - (z.re - a) / (b - a)) * α + (z.re - a) / (b - a) * β
  have hpos : 0 < 1 + |z.im| := by positivity
  have hinv : (1 + |z.im|) ^ ℓ * (1 + |z.im|) ^ (-ℓ) = 1 := by
    rw [← Real.rpow_add hpos, add_neg_cancel, Real.rpow_zero]
  have hK₀ := (weightConst_pos (α := α) (β := β) hab.le).le
  rw [norm_smul] at h
  calc ‖f z‖ = (1 + |z.im|) ^ ℓ * ((1 + |z.im|) ^ (-ℓ) * ‖f z‖) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ (1 + |z.im|) ^ ℓ * (weightConst a b α β * ‖stripWeight a b α β z‖ * ‖f z‖) := by
        gcongr
    _ = (1 + |z.im|) ^ ℓ * weightConst a b α β * (‖stripWeight a b α β z‖ * ‖f z‖) := by ring
    _ ≤ (1 + |z.im|) ^ ℓ * weightConst a b α β * M := by gcongr
    _ = weightConst a b α β * M * (1 + |z.im|) ^ ℓ := by ring

/-! ### Polynomial edge bounds -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Phragmén–Lindelöf with polynomial edge bounds.** Let `f` be holomorphic on the open strip
`a < re s < b`, continuous on its closure and of finite order there. If
`‖f s‖ ≤ C₁ (1 + |im s|) ^ α` on `re s = a` and `‖f s‖ ≤ C₂ (1 + |im s|) ^ β` on `re s = b`,
then on the closed strip, with `θ = (re s - a) / (b - a)`,
`‖f s‖ ≤ K C₁ ^ (1 - θ) C₂ ^ θ (1 + |im s|) ^ ((1 - θ) α + θ β)`.
The constant `K` depends only on `a`, `b`, `α` and `β`, and is chosen before `f`, `C₁` and `C₂`. -/
theorem exists_norm_le_interp_mul_one_add_abs_im_rpow (a b α β : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {f : ℂ → E} {C₁ C₂ : ℝ}, DiffContOnCl ℂ f (re ⁻¹' Ioo a b) →
      (∃ A B : ℝ, f =O[cobounded ℂ ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        (fun w ↦ Real.exp (B * ‖w‖ ^ A))) →
      (∀ w : ℂ, w.re = a → ‖f w‖ ≤ C₁ * (1 + |w.im|) ^ α) →
      (∀ w : ℂ, w.re = b → ‖f w‖ ≤ C₂ * (1 + |w.im|) ^ β) →
      ∀ z : ℂ, z.re ∈ Icc a b →
        ‖f z‖ ≤ K * C₁ ^ (1 - (z.re - a) / (b - a)) * C₂ ^ ((z.re - a) / (b - a)) *
          (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * α + (z.re - a) / (b - a) * β) := by
  rcases le_or_gt b a with hba | hab
  · -- A degenerate strip is at most one line, where the left edge bound applies.
    refine ⟨1, one_pos, fun {f C₁ C₂} _ _ ha _ z hz ↦ ?_⟩
    have hza : z.re = a := le_antisymm (hz.2.trans hba) hz.1
    have hab : b - a = 0 := by linarith [hz.1, hz.2]
    simpa [hza, hab] using ha z hza
  set K₀ := weightConst a b α β
  have hK₀ : 0 < K₀ := weightConst_pos hab.le α β
  refine ⟨K₀ * K₀, by positivity, fun {f C₁ C₂} hd hg ha hb z hz ↦ ?_⟩
  set θ := (z.re - a) / (b - a)
  have hC₁ : 0 ≤ C₁ := by simpa using (norm_nonneg _).trans (ha (a : ℂ) (by simp))
  have hC₂ : 0 ≤ C₂ := by simpa using (norm_nonneg _).trans (hb (b : ℂ) (by simp))
  have hℓb : α + (β - α) / (b - a) * (b - a) = β := by
    rw [div_mul_cancel₀ _ (sub_pos.mpr hab).ne']
    ring
  -- the weighted function has constant edge bounds, which the three-lines theorem interpolates
  have hF := norm_le_interp_of_isBigO_exp_rpow hab
    (((differentiableOn_stripWeight a b α β).mono
      (closure_minimal (preimage_mono Ioo_subset_Icc_self)
        (isClosed_Icc.preimage continuous_re))).diffContOnCl.smul hd)
    (isBigO_stripWeight_smul hab hg)
    (fun v hv ↦ norm_stripWeight_smul_le_of_edge hab (left_mem_Icc.mpr hab.le) (by ring) ha hv)
    (fun v hv ↦ norm_stripWeight_smul_le_of_edge hab (right_mem_Icc.mpr hab.le) hℓb hb hv) hz
  have hθ : (K₀ * C₁) ^ (1 - θ) * (K₀ * C₂) ^ θ = K₀ * (C₁ ^ (1 - θ) * C₂ ^ θ) := by
    rw [Real.mul_rpow hK₀.le hC₁, Real.mul_rpow hK₀.le hC₂]
    calc K₀ ^ (1 - θ) * C₁ ^ (1 - θ) * (K₀ ^ θ * C₂ ^ θ)
        = K₀ ^ (1 - θ + θ) * (C₁ ^ (1 - θ) * C₂ ^ θ) := by rw [Real.rpow_add hK₀]; ring
      _ = K₀ * (C₁ ^ (1 - θ) * C₂ ^ θ) := by rw [sub_add_cancel, Real.rpow_one]
  have h := norm_le_of_norm_stripWeight_smul_le hab hz (hF.trans_eq hθ)
  calc ‖f z‖ ≤ K₀ * (K₀ * (C₁ ^ (1 - θ) * C₂ ^ θ)) *
        (1 + |z.im|) ^ ((1 - θ) * α + θ * β) := h
    _ = K₀ * K₀ * C₁ ^ (1 - θ) * C₂ ^ θ * (1 + |z.im|) ^ ((1 - θ) * α + θ * β) := by ring

/-- **Phragmén–Lindelöf with polynomial edge bounds**, with one constant on both edges. If `f` is
holomorphic on the open strip `a < re s < b`, continuous on its closure, of finite order there,
and bounded by `C (1 + |im s|) ^ α` on `re s = a` and by `C (1 + |im s|) ^ β` on `re s = b`, then
`‖f s‖ ≤ K C (1 + |im s|) ^ ((1 - θ) α + θ β)` on the closed strip, `θ = (re s - a) / (b - a)`.
The constant `K` depends only on `a`, `b`, `α` and `β`. -/
theorem exists_norm_le_mul_one_add_abs_im_rpow (a b α β : ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {f : ℂ → E} {C : ℝ}, DiffContOnCl ℂ f (re ⁻¹' Ioo a b) →
      (∃ A B : ℝ, f =O[cobounded ℂ ⊓ 𝓟 (re ⁻¹' Ioo a b)]
        (fun w ↦ Real.exp (B * ‖w‖ ^ A))) →
      (∀ w : ℂ, w.re = a → ‖f w‖ ≤ C * (1 + |w.im|) ^ α) →
      (∀ w : ℂ, w.re = b → ‖f w‖ ≤ C * (1 + |w.im|) ^ β) →
      ∀ z : ℂ, z.re ∈ Icc a b →
        ‖f z‖ ≤ K * C *
          (1 + |z.im|) ^ ((1 - (z.re - a) / (b - a)) * α + (z.re - a) / (b - a) * β) := by
  obtain ⟨K, hK, h⟩ := exists_norm_le_interp_mul_one_add_abs_im_rpow (E := E) a b α β
  refine ⟨K, hK, fun {f C} hd hg ha hb z hz ↦ ?_⟩
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (ha (a : ℂ) (by simp))
  have hCC : C ^ (1 - (z.re - a) / (b - a)) * C ^ ((z.re - a) / (b - a)) = C := by
    rw [← Real.rpow_add' hC (by simp), sub_add_cancel, Real.rpow_one]
  exact (h hd hg ha hb z hz).trans_eq (by rw [mul_assoc K, hCC])

end TauCeti.PhragmenLindelof
