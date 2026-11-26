/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import TauCeti.Analysis.Asymptotics.Volterra
import TauCeti.Analysis.ODE.SecondOrder.Linear
import TauCeti.MeasureTheory.Integral.IntegralEqImproper

/-!
# The Liouville–Green approximation with error bounds

Let `f` be positive and `C²` and `g` continuous on `(a, ∞)`, and let `ξ` be a primitive of
`f^{1/2}` there. The Liouville–Green (or WKB) approximations to the solutions of

  `w'' = (f(x) + g(x)) w`

are `f^{-1/4} e^{±ξ}`. Their accuracy is governed by the *error-control function*, whose
derivative is

  `Φ = f^{-1/4} (f^{-1/4})'' - g f^{-1/2}`.

If `Φ` is integrable on `(x, ∞)` for every `x > a`, then the equation has a `C²` solution

  `w₂(x) = f^{-1/4}(x) e^{-ξ(x)} (1 + ε(x))`,

whose relative error satisfies, with `V(x) = ∫ₓ^∞ |Φ|`,

  `|ε(x)| ≤ exp(V(x) / 2) - 1` and `f^{-1/2}(x) |ε'(x)| / 2 ≤ exp(V(x) / 2) - 1`

(`TauCeti.exists_liouvilleGreen_atTop`; DLMF 2.7.20–2.7.25, Olver, Chapter 6, Theorem 2.1).
Since `V(x) → 0` as `x → ∞`, both bounds tend to `0`. The coefficient `g` may be complex.
The theorem does not assume `ξ(x) → ∞`: it describes the solution characterized by its error
bound at `+∞`. Only when `ξ(x) → ∞` is this the solution recessive at `+∞`; recessivity itself
is not proved here.

## Proof

The two approximants `y_± = f^{-1/4} e^{±ξ}` satisfy `y_±'' = (f + g + f^{1/2} Φ) y_±` exactly.
Variation of parameters turns the equation for `ε` into the Volterra integral equation

  `ε(x) = ∫ₓ^∞ (e^{2ξ(x) - 2ξ(v)} - 1) / 2 · Φ(v) (1 + ε(v)) dv`,

whose kernel is bounded by `1/2` because `ξ` is increasing. Its solution is supplied by
`TauCeti.exists_volterra_solution`, and the sharp bound `|ε| ≤ exp(V / 2) - 1` by
`TauCeti.norm_volterra_solution_le_exp_sub_one`. Writing the solution as
`ε = e^{2ξ} I / 2 - T / 2` with the tail integrals `T = ∫ₓ^∞ Φ (1 + ε)` and
`I = ∫ₓ^∞ e^{-2ξ} Φ (1 + ε)`, the function `w₂ = y_- (1 - T / 2) + y_+ I / 2` is differentiated
twice directly. Since `ε' = f^{1/2} e^{2ξ} I`, the bound on `ε'` follows from
`|e^{2ξ(x)} I(x)| ≤ ∫ₓ^∞ |Φ| exp(V / 2) = 2 (exp(V(x) / 2) - 1)`
(`MeasureTheory.IntegrableOn.integral_Ioi_mul_exp_integral_Ioi`).

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974; reprinted
  A K Peters, 1997. Chapter 6, §2.
* NIST Digital Library of Mathematical Functions, §2.7(iii), equations (2.7.20)–(2.7.25),
  <https://dlmf.nist.gov/2.7.iii>.
-/

public section

open Set Filter MeasureTheory
open scoped Topology

namespace TauCeti

/-- The Liouville–Green approximants. Write `q = f^{-1/4}`, and let `ξ' = f^{1/2}`. For
`σ = ±1`, the function `y = q e^{σξ}` has derivative `(q' + σ f^{1/4}) e^{σξ}`, whose own
derivative is `(q'' + q f) e^{σξ}`. -/
private lemma hasDerivAt_approximant {f ξ : ℝ → ℝ} {a σ x : ℝ} (hf : ContDiffOn ℝ 2 f (Ioi a))
    (hf0 : ∀ x ∈ Ioi a, 0 < f x) (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x) (hσ : σ * σ = 1)
    (hx : x ∈ Ioi a) :
    HasDerivAt (fun t ↦ f t ^ (-(1 / 4) : ℝ) * Real.exp (σ * ξ t))
      ((deriv (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x + σ * f x ^ (1 / 4 : ℝ)) *
        Real.exp (σ * ξ x)) x ∧
    HasDerivAt (fun t ↦ (deriv (fun t ↦ f t ^ (-(1 / 4) : ℝ)) t + σ * f t ^ (1 / 4 : ℝ)) *
        Real.exp (σ * ξ t))
      ((iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x + f x ^ (-(1 / 4) : ℝ) * f x) *
        Real.exp (σ * ξ x)) x := by
  have hfx := hf0 x hx
  have hxs := isOpen_Ioi.mem_nhds hx
  have hq := hf.rpow_const_of_ne (p := -(1 / 4)) fun t ht ↦ (hf0 t ht).ne'
  have hf1 := ((hf.contDiffAt hxs).hasStrictDerivAt_deriv two_ne_zero).hasDerivAt
  have hq1 := ((hq.contDiffAt hxs).hasStrictDerivAt_deriv two_ne_zero).hasDerivAt
  have hq2 : HasDerivAt (deriv fun t ↦ f t ^ (-(1 / 4) : ℝ))
      (iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) x := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact (((hq.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).contDiffAt
      hxs).hasStrictDerivAt_deriv one_ne_zero).hasDerivAt
  have hqd := (hf1.rpow_const (p := -(1 / 4)) (Or.inl hfx.ne')).deriv
  have hm := hf1.rpow_const (p := 1 / 4) (Or.inl hfx.ne')
  have hE := ((hξ x hx).const_mul σ).exp
  have hs : √(f x) = f x ^ (1 / 2 : ℝ) := Real.sqrt_eq_rpow _
  have i1 : f x ^ (-(1 / 4) : ℝ) * √(f x) = f x ^ (1 / 4 : ℝ) := by
    rw [hs, ← Real.rpow_add hfx]; norm_num
  have i2 : f x ^ (1 / 4 - 1 : ℝ) = √(f x) * f x ^ (-(1 / 4) - 1 : ℝ) := by
    rw [hs, ← Real.rpow_add hfx]; norm_num
  have i3 : f x ^ (1 / 4 : ℝ) * √(f x) = f x ^ (-(1 / 4) : ℝ) * f x := by
    rw [← i1, mul_assoc, Real.mul_self_sqrt hfx.le]
  refine ⟨?_, ?_⟩
  · convert hq1.mul hE using 1
    rw [← i1]; ring
  · convert (hq2.add (hm.const_mul σ)).mul hE using 1
    rw [Pi.add_apply, hqd, i2]
    linear_combination (-(f x ^ (1 / 4 : ℝ) * √(f x) * Real.exp (σ * ξ x))) * hσ -
      Real.exp (σ * ξ x) * i3

/-- A primitive of `f^{1/2}` is monotone. -/
private lemma monotoneOn_of_hasDerivAt_sqrt {f ξ : ℝ → ℝ} {a : ℝ}
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x) : MonotoneOn ξ (Ioi a) :=
  monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioi a)
    (fun x hx ↦ (hξ x hx).continuousAt.continuousWithinAt)
    (fun x hx ↦ (hξ x (interior_subset hx)).hasDerivWithinAt) fun _ _ ↦ Real.sqrt_nonneg _

/-- For `a < x ≤ v`, `e^{2ξ(x) - 2ξ(v)} ≤ 1`, because `ξ` is increasing. -/
private lemma exp_two_mul_sub_le_one {ξ : ℝ → ℝ} {a x v : ℝ} (hξm : MonotoneOn ξ (Ioi a))
    (hx : a < x) (hxv : x ≤ v) : Real.exp (2 * (ξ x - ξ v)) ≤ 1 :=
  Real.exp_le_one_iff.2 (by nlinarith [hξm hx (hx.trans_le hxv) hxv])

/-- The Volterra kernel `(e^{2ξ(x) - 2ξ(v)} - 1) / 2` of the Liouville–Green error is bounded by
`1 / 2` for `x ≤ v`, because `ξ` is increasing. -/
private lemma norm_liouvilleGreen_kernel_le {ξ : ℝ → ℝ} {a x v : ℝ} (hξm : MonotoneOn ξ (Ioi a))
    (hx : a < x) (hxv : x ≤ v) :
    ‖(((Real.exp (2 * (ξ x - ξ v)) - 1) / 2 : ℝ) : ℂ)‖ ≤ 1 / 2 := by
  have he := exp_two_mul_sub_le_one hξm hx hxv
  rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
  constructor <;> nlinarith [Real.exp_pos (2 * (ξ x - ξ v))]

/-- The Liouville–Green integrand `Φ (1 + ε)` has norm at most `|Φ| (1 + C)` when `|ε| ≤ C`. -/
private lemma norm_mul_one_add_le {Φ ε : ℂ} {C : ℝ} (hε : ‖ε‖ ≤ C) :
    ‖Φ * (1 + ε)‖ ≤ ‖Φ‖ * (1 + C) := by
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by simp [hε])) (norm_nonneg _)

/-- The Volterra integral equation of the Liouville–Green error has a continuous solution with
the sharp bound `|ε(x)| ≤ exp(V(x) / 2) - 1`, where `V(x) = ∫ₓ^∞ |Φ|`. -/
private lemma exists_liouvilleGreen_volterra {ξ : ℝ → ℝ} {Φ : ℝ → ℂ} {a : ℝ}
    (hξc : ContinuousOn ξ (Ioi a)) (hξm : MonotoneOn ξ (Ioi a)) (hΦc : ContinuousOn Φ (Ioi a))
    (hΦi : ∀ x ∈ Ioi a, IntegrableOn Φ (Ioi x)) :
    ∃ ε : ℝ → ℂ, ContinuousOn ε (Ioi a) ∧
      (∀ x ∈ Ioi a, ε x = ∫ v in Ioi x,
        (((Real.exp (2 * (ξ x - ξ v)) - 1) / 2 : ℝ) : ℂ) * (Φ v * (1 + ε v))) ∧
      ∀ x ∈ Ioi a, ‖ε x‖ ≤ Real.exp ((∫ v in Ioi x, ‖Φ v‖) / 2) - 1 := by
  set S : Set (ℝ × ℝ) := {p | a < p.1 ∧ p.1 ≤ p.2}
  have h1 : ContinuousOn (fun p : ℝ × ℝ ↦ ξ p.1) S := hξc.comp continuousOn_fst fun p hp ↦ hp.1
  have h2 : ContinuousOn (fun p : ℝ × ℝ ↦ ξ p.2) S :=
    hξc.comp continuousOn_snd fun p hp ↦ hp.1.trans_le hp.2
  have hK : ContinuousOn (Function.uncurry fun x v ↦
      (((Real.exp (2 * (ξ x - ξ v)) - 1) / 2 : ℝ) : ℂ)) S :=
    Complex.continuous_ofReal.comp_continuousOn
      (((Real.continuous_exp.comp_continuousOn (continuousOn_const.mul (h1.sub h2))).sub
        continuousOn_const).div_const 2)
  have hKle (x v : ℝ) (hx : a < x) (hxv : x ≤ v) :
      ‖(((Real.exp (2 * (ξ x - ξ v)) - 1) / 2 : ℝ) : ℂ)‖ ≤
        (fun _ ↦ (1 : ℝ)) x * (fun _ ↦ 1 / 2) v :=
    (norm_liouvilleGreen_kernel_le hξm hx hxv).trans_eq (one_mul _).symm
  have hΦi' (x : ℝ) (hx : x ∈ Ioi a) : IntegrableOn (fun v ↦ 1 / 2 * ‖Φ v‖) (Ioi x) :=
    (hΦi x hx).norm.const_mul _
  -- The crude bound of `exists_volterra_solution` shows that `ε` is bounded at infinity, so the
  -- sharp bound of `norm_volterra_solution_le_exp_sub_one` applies.
  obtain ⟨ε, hεc, hεeq, hεle⟩ := exists_volterra_solution (𝕜 := ℂ) (E := ℂ) (J := Φ) (ψ := Φ) hK
    hΦc hΦc continuousOn_const continuousOn_const (fun _ _ ↦ zero_le_one)
    (fun _ _ ↦ by norm_num) hKle (fun x hx ↦ (hΦi x hx).norm.const_mul _)
    (fun x hx ↦ (hΦi x hx).norm.const_mul _)
  have hεO := isBigO_of_norm_le_volterra_bound (fun _ _ ↦ zero_le_one)
    (fun _ _ ↦ by norm_num) (fun x hx ↦ (hΦi x hx).norm.const_mul _)
    (fun x hx ↦ (hΦi x hx).norm.const_mul _) hεle
  refine ⟨ε, hεc, fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · rw [hεeq x hx]
    congr 1 with v
    simp only [smul_eq_mul]
    ring
  · have h := norm_volterra_solution_le_exp_sub_one (Q := fun _ ↦ 1 / 2) (P₀ := 1) hKle
      (fun _ _ ↦ le_rfl) hΦi' hεc hεeq hεO hx
    rw [one_mul, integral_const_mul] at h
    convert h using 3
    ring

/-- With the bound on `ε`, the integrands `Φ (1 + ε)` and `e^{-2ξ} Φ (1 + ε)` are integrable on
`(x, ∞)` for every `x > a`. -/
private lemma integrableOn_liouvilleGreen_tails {ξ : ℝ → ℝ} {Φ ε : ℝ → ℂ} {a x : ℝ}
    (hξc : ContinuousOn ξ (Ioi a)) (hξm : MonotoneOn ξ (Ioi a)) (hΦc : ContinuousOn Φ (Ioi a))
    (hΦi : ∀ x ∈ Ioi a, IntegrableOn Φ (Ioi x)) (hεc : ContinuousOn ε (Ioi a))
    (hεle : ∀ x ∈ Ioi a, ‖ε x‖ ≤ Real.exp ((∫ v in Ioi x, ‖Φ v‖) / 2) - 1) (hx : x ∈ Ioi a) :
    IntegrableOn (fun v ↦ Φ v * (1 + ε v)) (Ioi x) ∧
    IntegrableOn (fun v ↦ (Real.exp (-(2 * ξ v)) : ℂ) * (Φ v * (1 + ε v))) (Ioi x) := by
  set C := Real.exp ((∫ v in Ioi x, ‖Φ v‖) / 2) - 1
  have hV := MeasureTheory.antitoneOn_integral_Ioi (fun v _ ↦ norm_nonneg (Φ v))
    fun y hy ↦ (hΦi y hy).norm
  have hC (v : ℝ) (hv : v ∈ Ioi x) : ‖ε v‖ ≤ C := by
    have hva : v ∈ Ioi a := mem_Ioi.2 (lt_trans hx hv)
    have hle : ∫ t in Ioi v, ‖Φ t‖ ≤ ∫ t in Ioi x, ‖Φ t‖ := hV hx hva (le_of_lt hv)
    exact (hεle v hva).trans (sub_le_sub_right (Real.exp_le_exp.2 (by linarith)) 1)
  have hGc : ContinuousOn (fun v ↦ Φ v * (1 + ε v)) (Ioi a) :=
    hΦc.mul (continuousOn_const.add hεc)
  have hG (v : ℝ) (hv : v ∈ Ioi x) : ‖Φ v * (1 + ε v)‖ ≤ ‖Φ v‖ * (1 + C) :=
    norm_mul_one_add_le (hC v hv)
  -- Each integrand is continuous and dominated on `(x, ∞)` by a multiple of `‖Φ‖`.
  have hsub : Ioi x ⊆ Ioi a := Ioi_subset_Ioi (le_of_lt hx)
  have hdom {F : ℝ → ℂ} (K : ℝ) (hF : ContinuousOn F (Ioi a))
      (hb : ∀ v ∈ Ioi x, ‖F v‖ ≤ ‖Φ v‖ * K) : IntegrableOn F (Ioi x) :=
    Integrable.mono' ((hΦi x hx).norm.mul_const K)
      ((hF.mono hsub).aestronglyMeasurable measurableSet_Ioi)
      ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hb))
  refine ⟨hdom _ hGc hG, hdom (Real.exp (-(2 * ξ x)) * (1 + C))
      ((Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn
        (continuousOn_const.mul hξc).neg)).mul hGc) fun v hv ↦ ?_⟩
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have he : Real.exp (-(2 * ξ v)) ≤ Real.exp (-(2 * ξ x)) := Real.exp_le_exp.2 (by
    linarith [Real.exp_le_one_iff.1 (exp_two_mul_sub_le_one hξm hx (le_of_lt hv))])
  calc Real.exp (-(2 * ξ v)) * ‖Φ v * (1 + ε v)‖
      ≤ Real.exp (-(2 * ξ x)) * (‖Φ v‖ * (1 + C)) :=
        mul_le_mul he (hG v hv) (norm_nonneg _) (Real.exp_pos _).le
    _ = ‖Φ v‖ * (Real.exp (-(2 * ξ x)) * (1 + C)) := by ring

/-- Splitting the kernel, the solution of the Volterra equation is
`ε(x) = e^{2ξ(x)} I(x) / 2 - T(x) / 2` with `T(x) = ∫ₓ^∞ Φ (1 + ε)` and
`I(x) = ∫ₓ^∞ e^{-2ξ} Φ (1 + ε)`. -/
private lemma liouvilleGreen_eq_sub {ξ : ℝ → ℝ} {Φ ε : ℝ → ℂ} {x : ℝ}
    (hεx : ε x = ∫ v in Ioi x,
      (((Real.exp (2 * (ξ x - ξ v)) - 1) / 2 : ℝ) : ℂ) * (Φ v * (1 + ε v)))
    (hG : IntegrableOn (fun v ↦ Φ v * (1 + ε v)) (Ioi x))
    (hE : IntegrableOn (fun v ↦ (Real.exp (-(2 * ξ v)) : ℂ) * (Φ v * (1 + ε v))) (Ioi x)) :
    ε x = ↑(Real.exp (2 * ξ x)) / 2 *
        (∫ v in Ioi x, (Real.exp (-(2 * ξ v)) : ℂ) * (Φ v * (1 + ε v))) -
      (∫ v in Ioi x, Φ v * (1 + ε v)) / 2 := by
  rw [hεx, ← integral_const_mul, ← integral_div, ← integral_sub (hE.const_mul _) (hG.div_const _)]
  congr 1 with v
  have h : Real.exp (2 * (ξ x - ξ v)) = Real.exp (2 * ξ x) * Real.exp (-(2 * ξ v)) := by
    rw [← Real.exp_add]; ring_nf
  rw [h]; push_cast; ring

/-- The weighted tail integral in `ε'` satisfies
`|e^{2ξ(x)} ∫ₓ^∞ e^{-2ξ} Φ (1 + ε)| ≤ 2 (exp(V(x) / 2) - 1)` with `V(x) = ∫ₓ^∞ |Φ|`: its
integrand is bounded by `|Φ| exp(V / 2)`, whose integral over `(x, ∞)` is `2 (exp(V(x) / 2) - 1)`.
-/
private lemma norm_exp_mul_integral_le {ξ : ℝ → ℝ} {Φ ε : ℝ → ℂ} {a x : ℝ}
    (hξm : MonotoneOn ξ (Ioi a)) (hx : x ∈ Ioi a) (hΦi : IntegrableOn Φ (Ioi x))
    (hεle : ∀ v ∈ Ioi x, ‖ε v‖ ≤ Real.exp ((∫ t in Ioi v, ‖Φ t‖) / 2) - 1) :
    ‖(Real.exp (2 * ξ x) : ℂ) *
        ∫ v in Ioi x, (Real.exp (-(2 * ξ v)) : ℂ) * (Φ v * (1 + ε v))‖ ≤
      2 * (Real.exp ((∫ v in Ioi x, ‖Φ v‖) / 2) - 1) := by
  have hg : IntegrableOn (fun v ↦ ‖Φ v‖ / 2) (Ioi x) := hΦi.norm.div_const 2
  have hV (v : ℝ) : ∫ t in Ioi v, ‖Φ t‖ / 2 = (∫ t in Ioi v, ‖Φ t‖) / 2 := integral_div _ _
  have hint := hg.mul_comp_integral_Ioi Real.continuous_exp.continuousOn
  have heq := hg.integral_Ioi_mul_exp_integral_Ioi
  simp only [hV] at hint heq
  rw [← heq, ← integral_const_mul, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hint.const_mul 2)
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun v hv ↦ ?_))
  have he := exp_two_mul_sub_le_one hξm hx (le_of_lt hv)
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_pos _).le, show 2 * ξ x + -(2 * ξ v) = 2 * (ξ x - ξ v) by ring]
  calc _ ≤ 1 * (‖Φ v‖ * (1 + (Real.exp ((∫ t in Ioi v, ‖Φ t‖) / 2) - 1))) :=
        mul_le_mul he (norm_mul_one_add_le (hεle v hv)) (norm_nonneg _) zero_le_one
    _ = _ := by ring

/-- **Variation of parameters.** With `q = f^{-1/4}` and `y_σ = q e^{σξ}`, let `T` and `I` have
derivatives `-Φ (1 + ε)` and `-e^{-2ξ} Φ (1 + ε)` at `x`, where
`Φ = q q'' - g f^{-1/2}` and `ε = e^{2ξ} I / 2 - T / 2` at `x`. Then
`W = y₋ (1 - T / 2) + y₊ I / 2` has derivative `W' = y₋' (1 - T / 2) + y₊' I / 2` at `x`, and
`W'` has derivative `(f + g) W` at `x`. -/
private lemma hasDerivAt_variationOfParameters {f ξ : ℝ → ℝ} {g Φ ε T I : ℝ → ℂ} {a x : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioi a)) (hf0 : ∀ x ∈ Ioi a, 0 < f x)
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x) (hx : x ∈ Ioi a)
    (hΦ : Φ x = ↑(f x ^ (-(1 / 4) : ℝ) * iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) -
      g x / ↑√(f x))
    (hT : HasDerivAt T (-(Φ x * (1 + ε x))) x)
    (hI : HasDerivAt I (-(↑(Real.exp (-(2 * ξ x))) * (Φ x * (1 + ε x)))) x)
    (hε : ε x = ↑(Real.exp (2 * ξ x)) / 2 * I x - T x / 2) :
    HasDerivAt (fun t ↦ ↑(f t ^ (-(1 / 4) : ℝ) * Real.exp (-1 * ξ t)) * (1 - T t / 2) +
        ↑(f t ^ (-(1 / 4) : ℝ) * Real.exp (1 * ξ t)) * I t / 2)
      (↑((deriv (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x + -1 * f x ^ (1 / 4 : ℝ)) *
          Real.exp (-1 * ξ x)) * (1 - T x / 2) +
        ↑((deriv (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x + 1 * f x ^ (1 / 4 : ℝ)) *
          Real.exp (1 * ξ x)) * I x / 2) x ∧
    HasDerivAt (fun t ↦ ↑((deriv (fun t ↦ f t ^ (-(1 / 4) : ℝ)) t + -1 * f t ^ (1 / 4 : ℝ)) *
          Real.exp (-1 * ξ t)) * (1 - T t / 2) +
        ↑((deriv (fun t ↦ f t ^ (-(1 / 4) : ℝ)) t + 1 * f t ^ (1 / 4 : ℝ)) *
          Real.exp (1 * ξ t)) * I t / 2)
      ((↑(f x) + g x) * (↑(f x ^ (-(1 / 4) : ℝ) * Real.exp (-1 * ξ x)) * (1 - T x / 2) +
        ↑(f x ^ (-(1 / 4) : ℝ) * Real.exp (1 * ξ x)) * I x / 2)) x := by
  obtain ⟨hm1, hm2⟩ := hasDerivAt_approximant hf hf0 hξ (σ := -1) (by norm_num) hx
  obtain ⟨hp1, hp2⟩ := hasDerivAt_approximant hf hf0 hξ (σ := 1) (by norm_num) hx
  have hfx := hf0 x hx
  -- Real identities at `x`, transported to `ℂ`.
  have k1 : f x ^ (1 / 4 : ℝ) * f x ^ (-(1 / 4) : ℝ) = 1 := by
    rw [← Real.rpow_add hfx]; norm_num
  have k2 : f x ^ (1 / 4 : ℝ) * (√(f x))⁻¹ = f x ^ (-(1 / 4) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hfx.le, ← Real.rpow_add hfx]; norm_num
  have k3 : Real.exp (-1 * ξ x) * Real.exp (2 * ξ x) = Real.exp (1 * ξ x) := by
    rw [← Real.exp_add]; ring_nf
  have k4 : Real.exp (1 * ξ x) * Real.exp (-(2 * ξ x)) = Real.exp (-1 * ξ x) := by
    rw [← Real.exp_add]; ring_nf
  have c1 := congrArg ((↑) : ℝ → ℂ) k1
  have c2 := congrArg ((↑) : ℝ → ℂ) k2
  have c3 := congrArg ((↑) : ℝ → ℂ) k3
  have c4 := congrArg ((↑) : ℝ → ℂ) k4
  push_cast at c1 c2 c3 c4
  refine ⟨?_, ?_⟩
  · convert (hm1.ofReal_comp.mul (HasDerivAt.const_sub 1 (hT.div_const 2))).add
      ((hp1.ofReal_comp.mul hI).div_const 2) using 1
    push_cast
    linear_combination (↑(f x ^ (-(1 / 4) : ℝ)) * (Φ x * (1 + ε x)) / 2) * c4
  · convert (hm2.ofReal_comp.mul (HasDerivAt.const_sub 1 (hT.div_const 2))).add
      ((hp2.ofReal_comp.mul hI).div_const 2) using 1
    rw [hε, hΦ]
    push_cast
    set Q : ℂ := ↑(f x ^ (-(1 / 4) : ℝ))
    set Q2 : ℂ := ↑(iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x)
    set D : ℂ := ↑(deriv (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x)
    set M : ℂ := ↑(f x ^ (1 / 4 : ℝ))
    set em := Complex.exp (-1 * ↑(ξ x))
    set ep := Complex.exp (1 * ↑(ξ x))
    set e2p := Complex.exp (2 * ↑(ξ x))
    set G := (Q * Q2 - g x / ↑√(f x)) * (1 + (e2p / 2 * I x - T x / 2))
    linear_combination (Q2 * (em * (1 - T x / 2) + ep * I x / 2)) * c1 -
      (g x * (em * (1 - T x / 2) + ep * I x / 2)) * c2 +
      (M * (Q * Q2 - g x / ↑√(f x)) * I x / 2) * c3 + (G / 2 * (D + M)) * c4

/-- **The Liouville–Green solution.** If `ε = e^{2ξ} I / 2 - T / 2` on `(a, ∞)`, where `T` and
`I` have derivatives `-Φ (1 + ε)` and `-e^{-2ξ} Φ (1 + ε)` there, then
`w = f^{-1/4} e^{-ξ} (1 + ε)` is `C²` on `(a, ∞)` and solves `w'' = (f + g) w` there. -/
private lemma liouvilleGreen_solution {f ξ : ℝ → ℝ} {g Φ ε T I : ℝ → ℂ} {a : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioi a)) (hf0 : ∀ x ∈ Ioi a, 0 < f x) (hg : ContinuousOn g (Ioi a))
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x)
    (hΦ : ∀ x ∈ Ioi a, Φ x = ↑(f x ^ (-(1 / 4) : ℝ) *
      iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) - g x / ↑√(f x))
    (hT : ∀ x ∈ Ioi a, HasDerivAt T (-(Φ x * (1 + ε x))) x)
    (hI : ∀ x ∈ Ioi a, HasDerivAt I (-(↑(Real.exp (-(2 * ξ x))) * (Φ x * (1 + ε x)))) x)
    (hε : ∀ x ∈ Ioi a, ε x = ↑(Real.exp (2 * ξ x)) / 2 * I x - T x / 2) :
    ContDiffOn ℝ 2 (fun t ↦ ↑(f t ^ (-(1 / 4) : ℝ) * Real.exp (-ξ t)) * (1 + ε t)) (Ioi a) ∧
    ∀ x ∈ Ioi a,
      iteratedDeriv 2 (fun t ↦ ↑(f t ^ (-(1 / 4) : ℝ) * Real.exp (-ξ t)) * (1 + ε t)) x =
        (f x + g x) * (↑(f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x)) * (1 + ε x)) := by
  -- `w = y₋ (1 + ε)` agrees on `(a, ∞)` with `W = y₋ (1 - T / 2) + y₊ I / 2`.
  set w : ℝ → ℂ := fun t ↦ ↑(f t ^ (-(1 / 4) : ℝ) * Real.exp (-ξ t)) * (1 + ε t)
  set W : ℝ → ℂ := fun t ↦ ↑(f t ^ (-(1 / 4) : ℝ) * Real.exp (-1 * ξ t)) * (1 - T t / 2) +
    ↑(f t ^ (-(1 / 4) : ℝ) * Real.exp (1 * ξ t)) * I t / 2
  set W' : ℝ → ℂ := fun t ↦ ↑((deriv (fun t ↦ f t ^ (-(1 / 4) : ℝ)) t + -1 * f t ^ (1 / 4 : ℝ)) *
      Real.exp (-1 * ξ t)) * (1 - T t / 2) +
    ↑((deriv (fun t ↦ f t ^ (-(1 / 4) : ℝ)) t + 1 * f t ^ (1 / 4 : ℝ)) *
      Real.exp (1 * ξ t)) * I t / 2
  have hwW (t : ℝ) (ht : t ∈ Ioi a) : w t = W t := by
    have h : Real.exp (-ξ t) * Real.exp (2 * ξ t) = Real.exp (1 * ξ t) := by
      rw [← Real.exp_add]; ring_nf
    have hc := congrArg ((↑) : ℝ → ℂ) h
    simp only [w, W, neg_one_mul]
    rw [hε t ht]
    push_cast at hc ⊢
    linear_combination (↑(f t ^ (-(1 / 4) : ℝ)) * I t / 2) * hc
  have hW (x : ℝ) (hx : x ∈ Ioi a) :
      HasDerivAt W (W' x) x ∧ HasDerivAt W' ((f x + g x) * W x) x :=
    hasDerivAt_variationOfParameters hf hf0 hξ hx (hΦ x hx) (hT x hx) (hI x hx) (hε x hx)
  have hw1 (x : ℝ) (hx : x ∈ Ioi a) : HasDerivAt w (W' x) x :=
    (hW x hx).1.congr_of_eventuallyEq (eventually_of_mem (isOpen_Ioi.mem_nhds hx) hwW)
  exact contDiffOn_two_of_hasDerivAt (q := fun x ↦ ↑(f x) + g x) isOpen_Ioi
    ((Complex.continuous_ofReal.comp_continuousOn hf.continuousOn).add hg) hw1
    fun x hx ↦ hwW x hx ▸ (hW x hx).2

/-- The relative error `ε = e^{2ξ} I / 2 - T / 2` has derivative `f^{1/2} e^{2ξ} I`. -/
private lemma hasDerivAt_liouvilleGreen_error {f ξ : ℝ → ℝ} {Φ ε T I : ℝ → ℂ} {a x : ℝ}
    (hξ : HasDerivAt ξ (√(f x)) x) (hT : HasDerivAt T (-(Φ x * (1 + ε x))) x)
    (hI : HasDerivAt I (-(↑(Real.exp (-(2 * ξ x))) * (Φ x * (1 + ε x)))) x)
    (hε : ∀ x ∈ Ioi a, ε x = ↑(Real.exp (2 * ξ x)) / 2 * I x - T x / 2) (hx : x ∈ Ioi a) :
    HasDerivAt ε (↑√(f x) * (↑(Real.exp (2 * ξ x)) * I x)) x := by
  have h := (((hξ.const_mul 2).exp.ofReal_comp.div_const 2).mul hI).sub (hT.div_const 2)
  refine (h.congr_of_eventuallyEq (eventually_of_mem (isOpen_Ioi.mem_nhds hx) hε)).congr_deriv ?_
  have he : Real.exp (2 * ξ x) * Real.exp (-(2 * ξ x)) = 1 := by rw [← Real.exp_add]; simp
  have hc := congrArg ((↑) : ℝ → ℂ) he
  push_cast at hc ⊢
  linear_combination (-(Φ x * (1 + ε x)) / 2) * hc

/-- The error-control integrand `Φ = f^{-1/4} (f^{-1/4})'' - g f^{-1/2}` is continuous. -/
private lemma continuousOn_liouvilleGreen_control {f : ℝ → ℝ} {g Φ : ℝ → ℂ} {a : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioi a)) (hf0 : ∀ x ∈ Ioi a, 0 < f x) (hg : ContinuousOn g (Ioi a))
    (hΦ : ∀ x ∈ Ioi a, Φ x = ↑(f x ^ (-(1 / 4) : ℝ) *
      iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) - g x / ↑√(f x)) :
    ContinuousOn Φ (Ioi a) := by
  have hq := hf.rpow_const_of_ne (p := -(1 / 4)) fun t ht ↦ (hf0 t ht).ne'
  have hq2 : ContinuousOn (iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ))) (Ioi a) := by
    rw [iteratedDeriv_succ, iteratedDeriv_one]
    exact ((hq.deriv_of_isOpen isOpen_Ioi (m := 1) (by norm_num)).deriv_of_isOpen isOpen_Ioi
      (m := 0) (by norm_num)).continuousOn
  refine ContinuousOn.congr ?_ hΦ
  exact (Complex.continuous_ofReal.comp_continuousOn (hq.continuousOn.mul hq2)).sub
    (hg.div (Complex.continuous_ofReal.comp_continuousOn hf.continuousOn.sqrt) fun x hx ↦
      Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 (hf0 x hx)).ne')

/-- **The Liouville–Green theorem, solution controlled at `+∞`.** Let `f` be positive and `C²`
and `g` continuous on `(a, ∞)`, let `ξ` be a primitive of `f^{1/2}` there, and let
`Φ = f^{-1/4} (f^{-1/4})'' - g f^{-1/2}` be integrable on `(x, ∞)` for every `x > a`. Then
`w'' = (f + g) w` has a solution `w`, `C²` on `(a, ∞)`, of the form
`w = f^{-1/4} e^{-ξ} (1 + ε)` with `ε` differentiable and, for `V(x) = ∫ₓ^∞ |Φ|`,
`|ε(x)| ≤ exp(V(x) / 2) - 1` and `|ε'(x)| / (2 f(x)^{1/2}) ≤ exp(V(x) / 2) - 1`
(DLMF 2.7.20–2.7.25; Olver, Chapter 6, Theorem 2.1). No limit of `ξ` at `+∞` is assumed, so
`w` need not be recessive there; it is when `ξ(x) → ∞`. -/
theorem exists_liouvilleGreen_atTop {f ξ : ℝ → ℝ} {g Φ : ℝ → ℂ} {a : ℝ}
    (hf : ContDiffOn ℝ 2 f (Ioi a)) (hf0 : ∀ x ∈ Ioi a, 0 < f x) (hg : ContinuousOn g (Ioi a))
    (hξ : ∀ x ∈ Ioi a, HasDerivAt ξ (√(f x)) x)
    (hΦ : ∀ x ∈ Ioi a, Φ x = ↑(f x ^ (-(1 / 4) : ℝ) *
      iteratedDeriv 2 (fun t ↦ f t ^ (-(1 / 4) : ℝ)) x) - g x / ↑√(f x))
    (hΦi : ∀ x ∈ Ioi a, IntegrableOn Φ (Ioi x)) :
    ∃ w ε : ℝ → ℂ, ContDiffOn ℝ 2 w (Ioi a) ∧ DifferentiableOn ℝ ε (Ioi a) ∧
      ∀ x ∈ Ioi a, iteratedDeriv 2 w x = (f x + g x) * w x ∧
        w x = ↑(f x ^ (-(1 / 4) : ℝ) * Real.exp (-ξ x)) * (1 + ε x) ∧
        ‖ε x‖ ≤ Real.exp ((∫ v in Ioi x, ‖Φ v‖) / 2) - 1 ∧
        ‖deriv ε x‖ / (2 * √(f x)) ≤ Real.exp ((∫ v in Ioi x, ‖Φ v‖) / 2) - 1 := by
  have hξc : ContinuousOn ξ (Ioi a) := fun x hx ↦ (hξ x hx).continuousAt.continuousWithinAt
  have hξm := monotoneOn_of_hasDerivAt_sqrt hξ
  have hΦc := continuousOn_liouvilleGreen_control hf hf0 hg hΦ
  obtain ⟨ε, hεc, hεeq, hεle⟩ := exists_liouvilleGreen_volterra hξc hξm hΦc hΦi
  have hint (x : ℝ) (hx : x ∈ Ioi a) :=
    integrableOn_liouvilleGreen_tails hξc hξm hΦc hΦi hεc hεle hx
  set G : ℝ → ℂ := fun v ↦ Φ v * (1 + ε v)
  set E : ℝ → ℂ := fun v ↦ (Real.exp (-(2 * ξ v)) : ℂ) * G v
  set T : ℝ → ℂ := fun t ↦ ∫ v in Ioi t, G v
  set I : ℝ → ℂ := fun t ↦ ∫ v in Ioi t, E v
  have hGc : ContinuousOn G (Ioi a) := hΦc.mul (continuousOn_const.add hεc)
  have hEc : ContinuousOn E (Ioi a) :=
    (Complex.continuous_ofReal.comp_continuousOn (Real.continuous_exp.comp_continuousOn
      (continuousOn_const.mul hξc).neg)).mul hGc
  have hdec (x : ℝ) (hx : x ∈ Ioi a) : ε x = ↑(Real.exp (2 * ξ x)) / 2 * I x - T x / 2 :=
    liouvilleGreen_eq_sub (hεeq x hx) (hint x hx).1 (hint x hx).2
  have hTI (x : ℝ) (hx : x ∈ Ioi a) : HasDerivAt T (-G x) x ∧ HasDerivAt I (-E x) x :=
    ⟨hasDerivAt_integral_Ioi_of_continuousOn (fun y hy ↦ (hint y hy).1) hGc hx,
      hasDerivAt_integral_Ioi_of_continuousOn (fun y hy ↦ (hint y hy).2) hEc hx⟩
  obtain ⟨hwc, hw⟩ := liouvilleGreen_solution hf hf0 hg hξ hΦ (fun x hx ↦ (hTI x hx).1)
    (fun x hx ↦ (hTI x hx).2) hdec
  have hε1 (x : ℝ) (hx : x ∈ Ioi a) :=
    hasDerivAt_liouvilleGreen_error (hξ x hx) (hTI x hx).1 (hTI x hx).2 hdec hx
  refine ⟨_, ε, hwc, fun x hx ↦ (hε1 x hx).differentiableAt.differentiableWithinAt,
    fun x hx ↦ ⟨hw x hx, rfl, hεle x hx, ?_⟩⟩
  have hs := Real.sqrt_pos.2 (hf0 x hx)
  have hI := norm_exp_mul_integral_le hξm hx (hΦi x hx) fun v hv ↦
    hεle v (mem_Ioi.2 (lt_trans hx hv))
  rw [(hε1 x hx).deriv, norm_mul, Complex.norm_real, Real.norm_of_nonneg hs.le,
    mul_comm (2 : ℝ) (√(f x)), mul_div_mul_left _ _ hs.ne']
  linarith

end TauCeti
