/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.Decomposition
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import TauCeti.Analysis.Normed.Lp.PiLp
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Integral.DyadicMaximalFunction

/-!
# The sharp maximal function and the Fefferman–Stein inequality

The **sharp maximal function** of a locally integrable `f` is

`f^# x = sup_{B ∋ x} ⨍_B ‖f - f_B‖`, where `f_B = ⨍_B f`,

the supremum of the mean oscillations of `f` over the open balls `B` containing `x`. It is bounded
exactly when `f` has bounded mean oscillation, and it measures the local oscillation of `f`
rather than its size: it vanishes for constant `f`. The **Fefferman–Stein inequality** says that
nevertheless, for `1 < p < ∞`, the sharp maximal function controls the `Lᵖ` norm of `f` itself:

`‖f‖_p ≤ C ‖f^#‖_p`

with `C` depending only on the dimension `n` and on `p`, for every `f ∈ L^p₀(ℝⁿ)` with
`1 ≤ p₀ ≤ p`, on `ℝⁿ = ι → ℝ`, `n ≥ 1`, with balls taken in the sup distance
(`TauCeti.eLpNorm_le_eLpNorm_sharpMaximalFunction`). This covers both integrable `f` (`p₀ = 1`)
and `f ∈ Lᵖ` (`p₀ = p`), the case needed to bound operators on `Lᵖ` through their sharp maximal
functions. Some a priori integrability is needed, since `f^#` does not see constants. The
inequality fails in dimension `0`, where `f^#` vanishes identically. It is then transported to
`EuclideanSpace ℝ ι`, with balls of the Euclidean distance and a constant depending only on `ι`
and `p` (`TauCeti.exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow`).

This is the form in which mean oscillation estimates become `Lᵖ` estimates. In the `W^{2,p}`
theory of elliptic equations with coefficients of vanishing mean oscillation, one bounds the mean
oscillation of `D²u` on each small ball by comparison with a constant-coefficient equation; the
Fefferman–Stein inequality, together with the Hardy–Littlewood maximal inequality, turns these
pointwise bounds on `(D²u)^#` into the estimate of `‖D²u‖_p`.

## The argument

The proof is the good-`λ` inequality of Fefferman and Stein, run on the Calderón–Zygmund cubes
(`TauCeti.calderonZygmundCubes`) of `‖f‖`. Write `m(t)` for the measure of the union of the
Calderón–Zygmund cubes at height `t`.

* The mean oscillation of `f` on a dyadic cube `Q` is at most `2ⁿ⁺¹ f^# x` at every `x ∈ Q`
  (`TauCeti.setLAverage_enorm_sub_setAverage_dyadicCube_le`): `Q` lies in an open ball of `2ⁿ`
  times its volume.
* Let `Q` be a Calderón–Zygmund cube at height `t`, with parent `R`. The average of `‖f‖` over
  `R` is at most `t`, so `‖f_R‖ ≤ t`, while every cube `P` at height `2t` meeting `Q` lies in `Q`
  and has `⨍_P ‖f‖ > 2t`, hence `⨍_P ‖f - f_R‖ > t`. Summing over these disjoint `P`, the part
  of the height-`2t` cubes inside `Q` has measure at most `t⁻¹ ∫_R ‖f - f_R‖`, which is at most
  `2²ⁿ⁺¹ γ |Q|` if `f^# ≤ γ t` somewhere in `Q`. Otherwise `Q ⊆ {f^# > γ t}`. Summing over `Q`,

  `m(2t) ≤ 2²ⁿ⁺¹ γ m(t) + |{f^# > γ t}|`.

* Integrating against `p t^(p-1) dt` and substituting `t ↦ 2t` gives
  `∫₀ᴺ p t^(p-1) m(t) dt ≤ 2^p 2²ⁿ⁺¹ γ ∫₀ᴺ p t^(p-1) m(t) dt + 2^p γ^(-p) ∫ (f^#)^p`. The integrals
  on the left are finite: for integrable `f`, `m(t) ≤ ‖f‖₁ / t` and `p > 1`; for `f ∈ L^p₀` with
  `1 < p₀ ≤ p`, the Calderón–Zygmund cubes at height `t` lie in `{2ⁿ M f > t}`, where `M` is the
  Hardy–Littlewood maximal function, and `M f ∈ L^p₀` by the maximal theorem. The choice
  `γ = 2^(-(p + 2n + 2))` lets the first term on the right be absorbed. As `‖f‖ ≤ t`
  almost everywhere off the cubes at height `t`, the layer cake formula bounds `∫ ‖f‖^p` by the
  limit of the left side as `N → ∞`.

## Main declarations

* `TauCeti.sharpMaximalFunction`: the sharp maximal function, with
  `TauCeti.setLAverage_enorm_sub_setAverage_le_sharpMaximalFunction`,
  `TauCeti.sharpMaximalFunction_le` and `TauCeti.lt_sharpMaximalFunction_iff` as its interface,
  `TauCeti.sharpMaximalFunction_const`, `TauCeti.sharpMaximalFunction_zero`,
  `TauCeti.sharpMaximalFunction_congr_ae` and `TauCeti.lowerSemicontinuous_sharpMaximalFunction`.
* `TauCeti.sharpMaximalFunction_add_const`, `TauCeti.sharpMaximalFunction_const_smul` and
  `TauCeti.sharpMaximalFunction_add_le`: the sharp maximal function ignores constants, is
  homogeneous and is subadditive.
* `TauCeti.setLAverage_enorm_sub_setAverage_dyadicCube_le`: dyadic mean oscillation is controlled
  by the sharp maximal function.
* `TauCeti.lintegral_enorm_rpow_le_lintegral_sharpMaximalFunction_rpow` and
  `TauCeti.eLpNorm_le_eLpNorm_sharpMaximalFunction`: the **Fefferman–Stein inequality**.
* `TauCeti.exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow` and
  `TauCeti.exists_eLpNorm_le_mul_eLpNorm_sharpMaximalFunction`: the Fefferman–Stein inequality on
  `EuclideanSpace ℝ ι`, for the sharp maximal function over Euclidean balls. The coordinate map to
  `ι → ℝ` preserves volume and sends each sup-distance ball into a Euclidean ball of comparable
  volume, so the oscillation over the former is controlled by the oscillation over the latter.

## References

* C. Fefferman, E. M. Stein, *`H^p` spaces of several variables*, Acta Math. **129** (1972),
  137–193, Theorem 5.
* E. M. Stein, *Harmonic Analysis: Real-Variable Methods, Orthogonality, and Oscillatory
  Integrals*, Chapter IV, §2.
* L. Grafakos, *Modern Fourier Analysis*, 3rd ed., Section 3.4.
* N. V. Krylov, *Lectures on Elliptic and Parabolic Equations in Sobolev Spaces*, Chapter 3,
  Section 2 (the sharp function theorem as the tool for coefficients of vanishing mean
  oscillation).
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Module Set
open scoped ENNReal Topology

section PseudoMetricSpace

variable {X F : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The **sharp maximal function** of `f` with respect to `μ`: the supremum, over the open balls
`B` containing `x`, of the mean oscillation `⨍_B ‖f - f_B‖ₑ` of `f` on `B` about its average
`f_B = ⨍_B f`.

The supremum is over all balls containing `x`, not only those centred at `x`. The oscillations
are taken in `ℝ≥0∞`, so this is defined for every `f`, taking the value `∞` at the points where
they are unbounded. -/
noncomputable def sharpMaximalFunction (μ : Measure X) (f : X → F) (x : X) : ℝ≥0∞ :=
  ⨆ (c : X) (r : ℝ) (_ : x ∈ ball c r), ⨍⁻ y in ball c r, ‖f y - ⨍ z in ball c r, f z ∂μ‖ₑ ∂μ

variable {μ : Measure X} {f : X → F} {x c : X} {r : ℝ} {a : ℝ≥0∞}

/-- The mean oscillation of `f` on any open ball containing `x` is at most `f^# x`. -/
theorem setLAverage_enorm_sub_setAverage_le_sharpMaximalFunction (μ : Measure X) (f : X → F)
    (hx : x ∈ ball c r) :
    ⨍⁻ y in ball c r, ‖f y - ⨍ z in ball c r, f z ∂μ‖ₑ ∂μ ≤ sharpMaximalFunction μ f x :=
  le_iSup₂_of_le c r (le_iSup_of_le hx le_rfl)

/-- A bound on the mean oscillation of `f` on every open ball containing `x` bounds `f^# x`. -/
theorem sharpMaximalFunction_le
    (h : ∀ c r, x ∈ ball c r → ⨍⁻ y in ball c r, ‖f y - ⨍ z in ball c r, f z ∂μ‖ₑ ∂μ ≤ a) :
    sharpMaximalFunction μ f x ≤ a :=
  iSup₂_le fun c r => iSup_le (h c r)

/-- `f^# x` exceeds `a` exactly when the mean oscillation of `f` on some open ball containing `x`
does. -/
theorem lt_sharpMaximalFunction_iff :
    a < sharpMaximalFunction μ f x ↔
      ∃ c r, x ∈ ball c r ∧ a < ⨍⁻ y in ball c r, ‖f y - ⨍ z in ball c r, f z ∂μ‖ₑ ∂μ := by
  simp only [sharpMaximalFunction, lt_iSup_iff, exists_prop]

/-- The sharp maximal function of a constant with values in a Banach space vanishes, for every
measure: on a ball of finite positive measure the constant is its own average, and otherwise the
average of `‖·‖ₑ` over the ball is `0` by convention. -/
@[simp]
theorem sharpMaximalFunction_const [CompleteSpace F] (μ : Measure X) (b : F) :
    sharpMaximalFunction μ (fun _ => b) = 0 := by
  funext x
  refine le_antisymm (sharpMaximalFunction_le fun c r _ => ?_) (by positivity)
  rcases eq_or_ne (μ (ball c r)) 0 with h0 | h0
  · simp [Measure.restrict_eq_zero.2 h0]
  rcases eq_or_ne (μ (ball c r)) ∞ with htop | htop
  · simp [setLAverage_eq, htop]
  rw [setAverage_const h0 htop b]
  simp

/-- The sharp maximal function of the zero function vanishes. -/
@[simp]
theorem sharpMaximalFunction_zero (μ : Measure X) : sharpMaximalFunction μ (0 : X → F) = 0 := by
  funext x
  simp [sharpMaximalFunction]

/-- The sharp maximal function depends only on the a.e. class of `f`. -/
theorem sharpMaximalFunction_congr_ae {g : X → F} (h : f =ᵐ[μ] g) :
    sharpMaximalFunction μ f = sharpMaximalFunction μ g := by
  funext x
  simp only [sharpMaximalFunction, setLAverage_enorm_sub_setAverage_congr_ae h]

/-- The sharp maximal function does not see constants: adding a constant to an a.e. strongly
measurable `f` leaves `f^#` unchanged. -/
@[simp]
theorem sharpMaximalFunction_add_const [CompleteSpace F] (hf : AEStronglyMeasurable f μ) (b : F) :
    sharpMaximalFunction μ (fun y => f y + b) = sharpMaximalFunction μ f := by
  funext x
  simp only [sharpMaximalFunction, fun s => setLAverage_enorm_add_const_sub (s := s) hf.restrict]

/-- The sharp maximal function is homogeneous: `(k • f)^# = ‖k‖ₑ f^#`. -/
@[simp]
theorem sharpMaximalFunction_const_smul {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [SMulCommClass ℝ 𝕜 F] (k : 𝕜) (x : X) :
    sharpMaximalFunction μ (k • f) x = ‖k‖ₑ * sharpMaximalFunction μ f x := by
  simp only [sharpMaximalFunction, Pi.smul_apply, setLAverage_enorm_const_smul_sub_setAverage,
    ENNReal.mul_iSup]

/-- The sharp maximal function is subadditive on a.e. strongly measurable functions. -/
theorem sharpMaximalFunction_add_le {g : X → F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (x : X) :
    sharpMaximalFunction μ (f + g) x ≤ sharpMaximalFunction μ f x + sharpMaximalFunction μ g x :=
  sharpMaximalFunction_le fun _ _ hx => (setLAverage_enorm_add_sub_le hf.restrict hg.restrict).trans
    (add_le_add (setLAverage_enorm_sub_setAverage_le_sharpMaximalFunction μ f hx)
      (setLAverage_enorm_sub_setAverage_le_sharpMaximalFunction μ g hx))

/-- The superlevel sets of the sharp maximal function are open: a ball witnessing
`a < f^# x` contains a neighbourhood of `x`, at each point of which it witnesses the same
inequality. -/
theorem lowerSemicontinuous_sharpMaximalFunction (μ : Measure X) (f : X → F) :
    LowerSemicontinuous (sharpMaximalFunction μ f) := by
  intro x a ha
  obtain ⟨c, r, hx, hlt⟩ := lt_sharpMaximalFunction_iff.1 ha
  filter_upwards [isOpen_ball.mem_nhds hx] with y hy
  exact hlt.trans_le (setLAverage_enorm_sub_setAverage_le_sharpMaximalFunction μ f hy)

/-- The sharp maximal function is Borel measurable, being lower semicontinuous. -/
@[fun_prop]
theorem measurable_sharpMaximalFunction [OpensMeasurableSpace X] (μ : Measure X) (f : X → F) :
    Measurable (sharpMaximalFunction μ f) :=
  (lowerSemicontinuous_sharpMaximalFunction μ f).measurable

end PseudoMetricSpace

variable {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F]

section DyadicOscillation

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- **Dyadic mean oscillation and the sharp maximal function.** The mean oscillation of a locally
integrable `f` on a dyadic cube is at most `2ⁿ⁺¹` times its sharp maximal function at any point of
the cube, where `n` is the dimension. -/
theorem setLAverage_enorm_sub_setAverage_dyadicCube_le {f : (ι → ℝ) → F}
    (hf : LocallyIntegrable f) {k : ℤ} {m : ι → ℤ} {x : ι → ℝ} (hx : x ∈ dyadicCube k m) :
    ⨍⁻ y in dyadicCube k m, ‖f y - ⨍ z in dyadicCube k m, f z‖ₑ ∂volume ≤
      2 ^ (Fintype.card ι + 1) * sharpMaximalFunction volume f x := by
  set Q := dyadicCube k m
  -- `Q` lies in the open ball `B` about its centre of radius its side length, of volume `2ⁿ |Q|`.
  set B := ball (fun i => ((m i : ℝ) + 2⁻¹) * 2 ^ k) (2 ^ k)
  have hk : (0 : ℝ) < 2 ^ k := zpow_pos two_pos k
  have hQB : Q ⊆ B := (dyadicCube_subset_closedBall k m).trans
    (closedBall_subset_ball (half_lt_self hk))
  have hvol : volume B = 2 ^ Fintype.card ι * volume Q := by
    rw [Real.volume_pi_ball _ hk, volume_dyadicCube, mul_pow, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  have hB : IntegrableOn f B :=
    (hf.integrableOn_isCompact (isCompact_closedBall _ _)).mono_set ball_subset_closedBall
  calc ⨍⁻ y in Q, ‖f y - ⨍ z in Q, f z‖ₑ ∂volume
      ≤ 2 * ⨍⁻ y in Q, ‖f y - ⨍ z in B, f z‖ₑ ∂volume :=
        setLAverage_enorm_sub_setAverage_le (hB.mono_set hQB) _
    _ ≤ 2 * (volume B / volume Q * ⨍⁻ y in B, ‖f y - ⨍ z in B, f z‖ₑ ∂volume) := by
        gcongr
        exact setLAverage_le_div_mul_setLAverage_of_subset hQB measure_ball_lt_top.ne
    _ ≤ 2 * (2 ^ Fintype.card ι * sharpMaximalFunction volume f x) := by
        rw [hvol, ENNReal.mul_div_cancel_right (volume_dyadicCube_pos k m).ne'
            (volume_dyadicCube_ne_top k m)]
        gcongr
        exact setLAverage_enorm_sub_setAverage_le_sharpMaximalFunction _ _ (hQB hx)
    _ = 2 ^ (Fintype.card ι + 1) * sharpMaximalFunction volume f x := by
        rw [pow_succ]
        ring

end DyadicOscillation

section GoodLambda

/-- The union of the Calderón–Zygmund cubes of `‖f‖` at height `t`. -/
private def czUnion (f : (ι → ℝ) → F) (t : ℝ≥0∞) : Set (ι → ℝ) :=
  ⋃ q ∈ calderonZygmundCubes (fun x => ‖f x‖ₑ) t, dyadicCube q.1 q.2

/-- **The Calderón–Zygmund measure estimate** for the union: `t m(t) ≤ ‖f‖₁`. -/
private theorem mul_volume_czUnion_le (f : (ι → ℝ) → F) (t : ℝ≥0∞) :
    t * volume (czUnion f t) ≤ ∫⁻ x, ‖f x‖ₑ :=
  mul_volume_biUnion_calderonZygmundCubes_le.trans (setLIntegral_le_lintegral _ _)

/-- For `f` with `∫ ‖f‖ ^ p₀ < ∞`, `p₀ ≥ 1`, the superlevel set `{‖f‖ > t}` is, up to a null set,
contained in the union of the Calderón–Zygmund cubes at height `t`. -/
private theorem volume_lt_enorm_le_volume_czUnion [Nonempty ι] {f : (ι → ℝ) → F}
    (hf : AEStronglyMeasurable f) {p₀ : ℝ} (hp₀ : 1 ≤ p₀) (hfp₀ : ∫⁻ x, ‖f x‖ₑ ^ p₀ ≠ ∞)
    {t : ℝ≥0∞} (ht : t ≠ 0) :
    volume {x | t < ‖f x‖ₑ} ≤ volume (czUnion f t) := by
  refine measure_mono_ae ?_
  filter_upwards [ae_le_of_forall_notMem_calderonZygmundCubes hf.eNorm hp₀ hfp₀ ht]
    with x hx (hxt : t < ‖f x‖ₑ)
  by_contra hxU
  refine (hx fun q hq hxq => hxU ?_).not_gt hxt
  exact mem_biUnion hq hxq

/-- On a Calderón–Zygmund cube `P` of `‖f‖` at height `2t`, for `t < ∞`, the function `f`
deviates on average by more than `t` from any `a` with `‖a‖ₑ ≤ t`: `t |P| ≤ ∫_P ‖f - a‖ₑ`. -/
private theorem mul_volume_le_setLIntegral_enorm_sub {f : (ι → ℝ) → F} {t : ℝ≥0∞} (ht' : t ≠ ∞)
    {p : ℤ × (ι → ℤ)} (hp : p ∈ calderonZygmundCubes (fun x => ‖f x‖ₑ) (2 * t)) {a : F}
    (ha : ‖a‖ₑ ≤ t) :
    t * volume (dyadicCube p.1 p.2) ≤ ∫⁻ y in dyadicCube p.1 p.2, ‖f y - a‖ₑ := by
  set P := dyadicCube p.1 p.2
  have hfin : t * volume P ≠ ∞ := ENNReal.mul_ne_top ht' (volume_dyadicCube_ne_top _ _)
  refine ENNReal.le_of_add_le_add_right hfin ?_
  calc t * volume P + t * volume P = 2 * t * volume P := by ring
    _ ≤ ∫⁻ y in P, ‖f y‖ₑ := (mul_volume_lt_setLIntegral_of_mem_calderonZygmundCubes hp).le
    _ ≤ ∫⁻ y in P, (‖f y - a‖ₑ + ‖a‖ₑ) :=
        lintegral_mono fun y => by simpa using eNorm_add_le (f y - a) a
    _ = (∫⁻ y in P, ‖f y - a‖ₑ) + ‖a‖ₑ * volume P := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ (∫⁻ y in P, ‖f y - a‖ₑ) + t * volume P := by gcongr

section LevelSets

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- **The good-`λ` estimate on one cube.** Let `Q` be a Calderón–Zygmund cube of `‖f‖` at a
height `t < ∞`. The part of the Calderón–Zygmund cubes at height `2t` lying in `Q` has
measure at most `t⁻¹ 2²ⁿ⁺¹ f^# x |Q|` for every `x ∈ Q`. -/
private theorem mul_volume_czUnion_two_mul_inter_le {f : (ι → ℝ) → F} (hf : LocallyIntegrable f)
    {t : ℝ≥0∞} (ht' : t ≠ ∞) {q : ℤ × (ι → ℤ)}
    (hq : q ∈ calderonZygmundCubes (fun x => ‖f x‖ₑ) t) {x : ι → ℝ}
    (hx : x ∈ dyadicCube q.1 q.2) :
    t * volume (czUnion f (2 * t) ∩ dyadicCube q.1 q.2) ≤
      2 ^ (2 * Fintype.card ι + 1) * sharpMaximalFunction volume f x *
        volume (dyadicCube q.1 q.2) := by
  set Q := dyadicCube q.1 q.2
  set Q' := dyadicCube (q.1 + 1) (dyadicIndex (q.1 + 1) x)
  have hQQ' : Q ⊆ Q' := dyadicCube_subset_dyadicCube (lt_add_one q.1).le hx
  set a := ⨍ z in Q', f z
  -- The average of `f` over the parent cube is at most `t` in norm.
  have ha : ‖a‖ₑ ≤ t := (enorm_setAverage_le_setLAverage _ _ _).trans
    ((mem_calderonZygmundCubes.1 hq).2 _ _ (lt_add_one q.1) hQQ')
  -- Each cube at height `2t` meeting `Q` lies in `Q`, and there `f` deviates from `a` by more
  -- than `t` on average.
  have key : ∀ p ∈ calderonZygmundCubes (fun x => ‖f x‖ₑ) (2 * t),
      t * volume (dyadicCube p.1 p.2 ∩ Q) ≤ ∫⁻ y in dyadicCube p.1 p.2 ∩ Q, ‖f y - a‖ₑ := by
    intro p hp
    rcases (dyadicCube p.1 p.2 ∩ Q).eq_empty_or_nonempty with hpQ | hpQ
    · simp [hpQ]
    rw [inter_eq_left.2 (dyadicCube_subset_of_mem_calderonZygmundCubes_of_le
      (two_mul t ▸ le_self_add) hp hq hpQ)]
    exact mul_volume_le_setLIntegral_enorm_sub ht' hp ha
  have hdisj : Pairwise (Function.onFun Disjoint fun p :
      calderonZygmundCubes (fun x => ‖f x‖ₑ) (2 * t) => dyadicCube p.1.1 p.1.2 ∩ Q) :=
    fun p p' hne => (pairwiseDisjoint_calderonZygmundCubes p.2 p'.2
      (Subtype.coe_ne_coe.2 hne)).mono inter_subset_left inter_subset_left
  have hmeas : ∀ p : calderonZygmundCubes (fun x => ‖f x‖ₑ) (2 * t),
      MeasurableSet (dyadicCube p.1.1 p.1.2 ∩ Q) :=
    fun p => (measurableSet_dyadicCube _ _).inter (measurableSet_dyadicCube _ _)
  have hunion : czUnion f (2 * t) ∩ Q =
      ⋃ p : calderonZygmundCubes (fun x => ‖f x‖ₑ) (2 * t), dyadicCube p.1.1 p.1.2 ∩ Q := by
    rw [czUnion, biUnion_eq_iUnion, iUnion_inter]
  calc t * volume (czUnion f (2 * t) ∩ Q)
      = ∑' p : calderonZygmundCubes (fun x => ‖f x‖ₑ) (2 * t),
          t * volume (dyadicCube p.1.1 p.1.2 ∩ Q) := by
        rw [hunion, measure_iUnion hdisj hmeas, ENNReal.tsum_mul_left]
    _ ≤ ∑' p : calderonZygmundCubes (fun x => ‖f x‖ₑ) (2 * t),
          ∫⁻ y in dyadicCube p.1.1 p.1.2 ∩ Q, ‖f y - a‖ₑ :=
        tsum_le_tsum fun p => key p.1 p.2
    _ = ∫⁻ y in ⋃ p : calderonZygmundCubes (fun x => ‖f x‖ₑ) (2 * t),
          dyadicCube p.1.1 p.1.2 ∩ Q, ‖f y - a‖ₑ :=
        (lintegral_iUnion hmeas hdisj _).symm
    _ ≤ ∫⁻ y in Q', ‖f y - a‖ₑ :=
        lintegral_mono_set (iUnion_subset fun _ => inter_subset_right.trans hQQ')
    _ = volume Q' * ⨍⁻ y in Q', ‖f y - a‖ₑ ∂volume :=
        (measure_mul_setLAverage _ (volume_dyadicCube_ne_top _ _)).symm
    _ ≤ volume Q' * (2 ^ (Fintype.card ι + 1) * sharpMaximalFunction volume f x) := by
        gcongr
        exact setLAverage_enorm_sub_setAverage_dyadicCube_le hf (hQQ' hx)
    _ = 2 ^ (2 * Fintype.card ι + 1) * sharpMaximalFunction volume f x * volume Q := by
        rw [volume_dyadicCube_add_one q.1 q.2]
        ring

/-- **The good-`λ` inequality.** For locally integrable `f` with `∫ ‖f‖ ^ p₀ < ∞`, `p₀ ≥ 1`,
`0 < t < ∞` and every `γ`,

`m(2t) ≤ 2²ⁿ⁺¹ γ m(t) + |{f^# > γ t}|`,

where `m(s)` is the measure of the union of the Calderón–Zygmund cubes of `‖f‖` at height `s`. -/
private theorem volume_czUnion_two_mul_le {f : (ι → ℝ) → F}
    (hf : LocallyIntegrable f) {p₀ : ℝ} (hp₀ : 1 ≤ p₀) (hfp₀ : ∫⁻ x, ‖f x‖ₑ ^ p₀ ≠ ∞) {t : ℝ≥0∞}
    (ht : t ≠ 0) (ht' : t ≠ ∞) (γ : ℝ≥0∞) :
    volume (czUnion f (2 * t)) ≤ 2 ^ (2 * Fintype.card ι + 1) * γ * volume (czUnion f t) +
      volume {x | γ * t < sharpMaximalFunction volume f x} := by
  set S := {x | γ * t < sharpMaximalFunction volume f x}
  have hS : MeasurableSet S := measurableSet_lt measurable_const (by fun_prop)
  set K : ℝ≥0∞ := 2 ^ (2 * Fintype.card ι + 1)
  -- On each cube at height `t`, either `f^# > γ t` throughout, or the good-`λ` estimate applies.
  have hcube : ∀ q ∈ calderonZygmundCubes (fun x => ‖f x‖ₑ) t,
      volume (czUnion f (2 * t) ∩ dyadicCube q.1 q.2) ≤
        K * γ * volume (dyadicCube q.1 q.2) + volume (dyadicCube q.1 q.2 ∩ S) := by
    intro q hq
    by_cases hQS : dyadicCube q.1 q.2 ⊆ S
    · rw [inter_eq_left.2 hQS]
      exact (measure_mono inter_subset_right).trans le_add_self
    obtain ⟨x, hxQ, hxS⟩ := not_subset.1 hQS
    have hle : t * volume (czUnion f (2 * t) ∩ dyadicCube q.1 q.2) ≤
        K * (γ * t) * volume (dyadicCube q.1 q.2) := by
      refine (mul_volume_czUnion_two_mul_inter_le hf ht' hq hxQ).trans ?_
      gcongr
      exact not_lt.1 hxS
    refine le_add_right ?_
    rw [show K * (γ * t) * volume (dyadicCube q.1 q.2) =
      t * (K * γ * volume (dyadicCube q.1 q.2)) by ring] at hle
    exact (ENNReal.mul_le_mul_iff_right ht ht').1 hle
  have hmeas : ∀ q : calderonZygmundCubes (fun x => ‖f x‖ₑ) t,
      MeasurableSet (dyadicCube q.1.1 q.1.2) := fun q => measurableSet_dyadicCube _ _
  have hU : czUnion f t = ⋃ q : calderonZygmundCubes (fun x => ‖f x‖ₑ) t,
      dyadicCube q.1.1 q.1.2 := by
    rw [czUnion, biUnion_eq_iUnion]
  have hdisj : Pairwise (Function.onFun Disjoint fun q :
      calderonZygmundCubes (fun x => ‖f x‖ₑ) t => dyadicCube q.1.1 q.1.2) :=
    fun q q' hne => pairwiseDisjoint_calderonZygmundCubes q.2 q'.2 (Subtype.coe_ne_coe.2 hne)
  have hsub : czUnion f (2 * t) ⊆ czUnion f t :=
    biUnion_calderonZygmundCubes_subset hp₀ hfp₀ ht (two_mul t ▸ le_self_add)
  calc volume (czUnion f (2 * t))
      = volume (⋃ q : calderonZygmundCubes (fun x => ‖f x‖ₑ) t,
          czUnion f (2 * t) ∩ dyadicCube q.1.1 q.1.2) := by
        rw [← inter_iUnion, ← hU, inter_eq_left.2 hsub]
    _ = ∑' q : calderonZygmundCubes (fun x => ‖f x‖ₑ) t,
          volume (czUnion f (2 * t) ∩ dyadicCube q.1.1 q.1.2) :=
        measure_iUnion (fun q q' hne => (hdisj hne).mono
            inter_subset_right inter_subset_right)
          fun q => (measurableSet_biUnion_calderonZygmundCubes (fun x => ‖f x‖ₑ) _).inter (hmeas q)
    _ ≤ ∑' q : calderonZygmundCubes (fun x => ‖f x‖ₑ) t,
          (K * γ * volume (dyadicCube q.1.1 q.1.2) + volume (dyadicCube q.1.1 q.1.2 ∩ S)) :=
        tsum_le_tsum fun q => hcube q.1 q.2
    _ = K * γ * volume (czUnion f t) +
          volume (⋃ q : calderonZygmundCubes (fun x => ‖f x‖ₑ) t, dyadicCube q.1.1 q.1.2 ∩ S) := by
        rw [tsum_add, ENNReal.tsum_mul_left, hU,
          measure_iUnion hdisj hmeas,
          measure_iUnion (fun q q' hne => (hdisj hne).mono
            inter_subset_left inter_subset_left) fun q => (hmeas q).inter hS]
    _ ≤ K * γ * volume (czUnion f t) + volume S := by
        gcongr
        exact iUnion_subset fun _ => inter_subset_right

end LevelSets

end GoodLambda

section FeffermanStein

/-- The union of the Calderón–Zygmund cubes of `‖f‖` at height `t` lies in `{2ⁿ M f > t}`: the
average of `‖f‖` over a cube containing `x` is at most the dyadic maximal function at `x`, which is
at most `2ⁿ M f x`. -/
private theorem czUnion_subset_setOf_lt_two_pow_mul_maximalFunction (f : (ι → ℝ) → F)
    (t : ℝ≥0∞) :
    czUnion f t ⊆ {x | t < 2 ^ Fintype.card ι * maximalFunction volume f x} := by
  simp only [czUnion, iUnion_subset_iff]
  intro q hq x hx
  exact (lt_setLAverage_of_mem_calderonZygmundCubes hq).trans_le
    ((setLAverage_le_dyadicMaximalFunction f hx).trans
      (dyadicMaximalFunction_le_two_pow_mul_maximalFunction f x))

/-- For `f` with `∫ ‖f‖ < ∞` and `1 < p`, the truncated layer cake integral
`∫₀ᴺ m(t) t^(p-1) dt` of the measures `m(t)` of the Calderón–Zygmund unions is finite, since
`m(t) ≤ ‖f‖₁ / t`. -/
private theorem setLIntegral_volume_czUnion_mul_rpow_ne_top_of_lintegral_enorm_ne_top
    {f : (ι → ℝ) → F} {p : ℝ} (hp : 1 < p) (hf : ∫⁻ x, ‖f x‖ₑ ≠ ∞) {N : ℝ} (hN : 0 ≤ N) :
    ∫⁻ t in Ioo 0 N, volume (czUnion f (ENNReal.ofReal t)) * ENNReal.ofReal (t ^ (p - 1)) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' (g := fun t =>
    (∫⁻ x, ‖f x‖ₑ) * ENNReal.ofReal (t ^ (p - 2))) measurableSet_Ioo fun t ht => ?_)
  · rw [lintegral_const_mul' _ _ hf, lintegral_ofReal_rpow_Ioo (by linarith) hN]
    exact ENNReal.mul_ne_top hf ENNReal.ofReal_ne_top
  have hsplit : ENNReal.ofReal (t ^ (p - 1)) =
      ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal t := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.1.le _), ← Real.rpow_add_one ht.1.ne']
    ring_nf
  calc volume (czUnion f (ENNReal.ofReal t)) * ENNReal.ofReal (t ^ (p - 1))
      = ENNReal.ofReal (t ^ (p - 2)) *
          (ENNReal.ofReal t * volume (czUnion f (ENNReal.ofReal t))) := by
        rw [hsplit]
        ring
    _ ≤ ENNReal.ofReal (t ^ (p - 2)) * ∫⁻ x, ‖f x‖ₑ := by
        gcongr
        exact mul_volume_czUnion_le f _
    _ = (∫⁻ x, ‖f x‖ₑ) * ENNReal.ofReal (t ^ (p - 2)) := mul_comm _ _

/-- For `f` with `∫ ‖f‖ ^ p₀ < ∞`, where `1 < p₀ ≤ p`, the truncated layer cake integral
`∫₀ᴺ m(t) t^(p-1) dt` of the measures `m(t)` of the Calderón–Zygmund unions is finite: `m(t)` is
at most the measure of `{2ⁿ M f > t}` and `t^(p-1) ≤ N^(p-p₀) t^(p₀-1)` on `(0, N)`, so the
integral is at most `N^(p-p₀)` times the layer cake integral of `∫ (2ⁿ M f)^p₀`, which is finite
by the maximal theorem. -/
private theorem setLIntegral_volume_czUnion_mul_rpow_ne_top_of_one_lt {f : (ι → ℝ) → F}
    (hf : AEStronglyMeasurable f) {p₀ p : ℝ} (hp₀ : 1 < p₀) (hp₀p : p₀ ≤ p)
    (hfp₀ : ∫⁻ x, ‖f x‖ₑ ^ p₀ ≠ ∞) {N : ℝ} (hN : 0 ≤ N) :
    ∫⁻ t in Ioo 0 N, volume (czUnion f (ENNReal.ofReal t)) * ENNReal.ofReal (t ^ (p - 1)) ≠ ∞ := by
  set g : (ι → ℝ) → ℝ≥0∞ := fun x => 2 ^ Fintype.card ι * maximalFunction volume f x
  have hMf := measurable_maximalFunction volume f
  have hgm : Measurable g := hMf.const_mul _
  -- By the maximal theorem, `∫ g ^ p₀ < ∞`.
  have hg : ∫⁻ x, g x ^ p₀ ≠ ∞ := by
    simp_rw [g, ENNReal.mul_rpow_of_nonneg _ _ (zero_le_one.trans hp₀.le)]
    rw [lintegral_const_mul _ (hMf.pow_const _)]
    refine ENNReal.mul_ne_top (by simp) (ne_top_of_le_ne_top ?_
      (lintegral_rpow_maximalFunction_le volume hf.eNorm hp₀))
    exact ENNReal.mul_ne_top (maximalFunctionConst_ne_top _ _) hfp₀
  -- Hence its layer cake integral is finite.
  have hJ : ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < g x} *
      ENNReal.ofReal (t ^ (p₀ - 1)) ≠ ∞ := by
    intro hJ
    have h := lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul volume hgm.aemeasurable
      (zero_lt_one.trans hp₀)
    rw [hJ, ENNReal.mul_top (ENNReal.ofReal_pos.2 (zero_lt_one.trans hp₀)).ne'] at h
    exact hg h
  refine ne_top_of_le_ne_top
    (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := N ^ (p - p₀))) hJ) ?_
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (setLIntegral_mono' measurableSet_Ioo fun t ht => ?_).trans
    (lintegral_mono_set Ioo_subset_Ioi_self)
  have hpow : ENNReal.ofReal (t ^ (p - 1)) ≤
      ENNReal.ofReal (N ^ (p - p₀)) * ENNReal.ofReal (t ^ (p₀ - 1)) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hN _)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc t ^ (p - 1) = t ^ (p - p₀) * t ^ (p₀ - 1) := by
          rw [← Real.rpow_add ht.1]
          ring_nf
      _ ≤ N ^ (p - p₀) * t ^ (p₀ - 1) := mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow ht.1.le ht.2.le (sub_nonneg.2 hp₀p)) (Real.rpow_nonneg ht.1.le _)
  calc volume (czUnion f (ENNReal.ofReal t)) * ENNReal.ofReal (t ^ (p - 1))
      ≤ volume {x | ENNReal.ofReal t < g x} *
          (ENNReal.ofReal (N ^ (p - p₀)) * ENNReal.ofReal (t ^ (p₀ - 1))) :=
        mul_le_mul' (measure_mono (czUnion_subset_setOf_lt_two_pow_mul_maximalFunction f _)) hpow
    _ = ENNReal.ofReal (N ^ (p - p₀)) *
          (volume {x | ENNReal.ofReal t < g x} * ENNReal.ofReal (t ^ (p₀ - 1))) := by
        ring

/-- For `f` with `∫ ‖f‖ ^ p₀ < ∞`, where `1 ≤ p₀ ≤ p` and `1 < p`, the truncated layer cake
integral `∫₀ᴺ m(t) t^(p-1) dt` of the measures `m(t)` of the Calderón–Zygmund unions is finite. -/
private theorem setLIntegral_volume_czUnion_mul_rpow_ne_top {f : (ι → ℝ) → F}
    (hf : AEStronglyMeasurable f) {p₀ p : ℝ} (hp₀ : 1 ≤ p₀) (hp₀p : p₀ ≤ p) (hp : 1 < p)
    (hfp₀ : ∫⁻ x, ‖f x‖ₑ ^ p₀ ≠ ∞) {N : ℝ} (hN : 0 ≤ N) :
    ∫⁻ t in Ioo 0 N, volume (czUnion f (ENNReal.ofReal t)) * ENNReal.ofReal (t ^ (p - 1)) ≠ ∞ := by
  rcases hp₀.eq_or_lt with rfl | hp₀'
  · exact setLIntegral_volume_czUnion_mul_rpow_ne_top_of_lintegral_enorm_ne_top hp
      (by simpa only [ENNReal.rpow_one] using hfp₀) hN
  · exact setLIntegral_volume_czUnion_mul_rpow_ne_top_of_one_lt hf hp₀' hp₀p hfp₀ hN

/-- The choice `γ = 2^(-(p + 2n + 2))` of the good-`λ` parameter makes the constant
`2^p 2²ⁿ⁺¹ γ` of the rescaled good-`λ` inequality equal to `1 / 2`. -/
private theorem ofReal_two_rpow_mul_two_pow_mul_ofReal_two_rpow (n : ℕ) (p : ℝ) :
    ENNReal.ofReal (2 ^ p) * (2 ^ (2 * n + 1) * ENNReal.ofReal (2 ^ (-(p + 2 * n + 2)))) = 2⁻¹ := by
  have h2 : (2 : ℝ) ^ p * (2 ^ (2 * n + 1) * 2 ^ (-(p + 2 * n + 2))) = 2⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_add two_pos, ← Real.rpow_add two_pos,
      ← Real.rpow_neg_one]
    congr 1
    push_cast
    ring
  have hK : (2 : ℝ≥0∞) ^ (2 * n + 1) = ENNReal.ofReal (2 ^ (2 * n + 1)) := by
    rw [ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]
  rw [hK, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity), h2,
    ENNReal.ofReal_inv_of_pos two_pos, ENNReal.ofReal_ofNat]

variable [NormedSpace ℝ F] [CompleteSpace F]

/-- **The truncated Fefferman–Stein estimate.** For `f` with `∫ ‖f‖ ^ p₀ < ∞`, where
`1 ≤ p₀ ≤ p` and `1 < p`, for `N ≥ 0` and `γ = 2^(-(p + 2n + 2))`,

`∫₀ᴺ m(t) t^(p-1) dt ≤ 2^(p + 1) γ^(-p) ∫₀^∞ |{f^# > t}| t^(p-1) dt`,

where `m(t)` is the measure of the union of the Calderón–Zygmund cubes of `‖f‖` at height `t`.
Substituting `t = 2s` and applying the good-`λ` inequality bounds the left side by half of itself
plus the right side, and the left side is finite, so the first term is absorbed. -/
private theorem setLIntegral_volume_czUnion_mul_rpow_le {f : (ι → ℝ) → F}
    (hf : AEStronglyMeasurable f) {p₀ p : ℝ} (hp₀ : 1 ≤ p₀) (hp₀p : p₀ ≤ p) (hp : 1 < p)
    (hfp₀ : ∫⁻ x, ‖f x‖ₑ ^ p₀ ≠ ∞) {N : ℝ} (hN : 0 ≤ N) :
    ∫⁻ t in Ioo 0 N, volume (czUnion f (ENNReal.ofReal t)) * ENNReal.ofReal (t ^ (p - 1)) ≤
      2 * (ENNReal.ofReal (2 ^ p) *
        (ENNReal.ofReal (((2 : ℝ) ^ (-(p + 2 * Fintype.card ι + 2))) ^ (-p)) *
          ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < sharpMaximalFunction volume f x} *
            ENNReal.ofReal (t ^ (p - 1)))) := by
  set n := Fintype.card ι
  set f' := sharpMaximalFunction volume f
  -- `f` is locally integrable, since it lies in `L^p₀` with `p₀ ≥ 1`.
  have hloc : LocallyIntegrable f := by
    have hp₀' : ENNReal.ofReal p₀ ≠ 0 := (ENNReal.ofReal_pos.2 (zero_lt_one.trans_le hp₀)).ne'
    refine MemLp.locallyIntegrable ((eLpNorm_lt_top_iff_lintegral_rpow_eNorm_lt_top hp₀'
      ENNReal.ofReal_ne_top hf).2 ?_) (ENNReal.one_le_ofReal.2 hp₀)
    rw [ENNReal.toReal_ofReal (zero_le_one.trans hp₀)]
    exact hfp₀.lt_top
  -- `m t` is the measure of the Calderón–Zygmund union at height `t`, `σ t` that of `{f^# > t}`,
  -- and `I N = ∫₀ᴺ m(t) t^(p-1) dt`.
  set m : ℝ → ℝ≥0∞ := fun t => volume (czUnion f (ENNReal.ofReal t))
  set σ : ℝ → ℝ≥0∞ := fun t => volume {x | ENNReal.ofReal t < f' x}
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 1))
  set I : ℝ → ℝ≥0∞ := fun N => ∫⁻ t in Ioo 0 N, m t * w t
  set J := ∫⁻ t in Ioi (0 : ℝ), σ t * w t
  set γ : ℝ := 2 ^ (-(p + 2 * n + 2))
  have hγ : 0 < γ := by positivity
  set K : ℝ≥0∞ := 2 ^ (2 * n + 1)
  have hσ : Antitone σ := fun s t hst => measure_mono fun x (hx : ENNReal.ofReal t < f' x) =>
    (ENNReal.ofReal_le_ofReal hst).trans_lt hx
  -- The good-`λ` inequality at height `s`.
  have hlevel : ∀ s : ℝ, 0 < s → m (2 * s) ≤ K * ENNReal.ofReal γ * m s + σ (γ * s) := by
    intro s hs
    have h := volume_czUnion_two_mul_le hloc hp₀ hfp₀ (ENNReal.ofReal_pos.2 hs).ne'
      ENNReal.ofReal_ne_top (ENNReal.ofReal γ)
    simp only [m, σ, f']
    rwa [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ENNReal.ofReal_mul hγ.le]
  -- Integrated against `w`, the term `σ (γ s)` is `γ^(-p)` times the layer cake integral `J`.
  have hJ : ∫⁻ s in Ioi (0 : ℝ), σ (γ * s) * w s = ENNReal.ofReal (γ ^ (-p)) * J := by
    rw [setLIntegral_comp_mul_left_mul_rpow σ hγ measurableSet_Ioi (S := Ioi 0)
      (fun s => (mul_pos_iff_of_pos_left hγ).symm) Ioi_subset_Ici_self, sub_add_cancel]
  have hconst : ENNReal.ofReal (2 ^ p) * (K * ENNReal.ofReal γ) = 2⁻¹ :=
    ofReal_two_rpow_mul_two_pow_mul_ofReal_two_rpow n p
  -- Substituting `t = 2 s` and applying the good-`λ` inequality bounds `I N` by `I N / 2 + …`.
  have hstep : I N ≤ 2⁻¹ * I N + ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal (γ ^ (-p)) * J) :=
    setLIntegral_Ioo_mul_rpow_le_inv_two_mul_add hγ hN hσ.measurable hlevel hJ hconst
  -- Since `I N` is finite, the first term is absorbed.
  rw [mul_comm]
  refine ENNReal.le_mul_two_of_le_add_div_two
    (setLIntegral_volume_czUnion_mul_rpow_ne_top hf hp₀ hp₀p hp hfp₀ hN) ?_
  rwa [add_comm, ENNReal.div_eq_inv_mul]

/-- **The Fefferman–Stein inequality**, as an inequality between the integrals `∫⁻ ‖·‖ₑ ^ p`.
For `1 < p < ∞` and an a.e. strongly measurable `f` on `ℝⁿ = ι → ℝ`, `n ≥ 1`, with
`∫ ‖f‖ ^ p₀ < ∞` for some `1 ≤ p₀ ≤ p`,

`∫ ‖f‖^p ≤ 2^(p + 1) 2^((p + 2n + 2) p) ∫ (f^#)^p`,

where `f^#` is the sharp maximal function for balls in the sup distance. The case `p₀ = 1` is that
of an integrable `f`, and `p₀ = p` that of `f ∈ Lᵖ`. -/
theorem lintegral_enorm_rpow_le_lintegral_sharpMaximalFunction_rpow [Nonempty ι]
    {f : (ι → ℝ) → F} (hf : AEStronglyMeasurable f) {p₀ p : ℝ} (hp₀ : 1 ≤ p₀) (hp₀p : p₀ ≤ p)
    (hp : 1 < p) (hfp₀ : ∫⁻ x, ‖f x‖ₑ ^ p₀ ≠ ∞) :
    ∫⁻ x, ‖f x‖ₑ ^ p ≤
      ENNReal.ofReal (2 ^ (p + 1) * 2 ^ ((p + 2 * Fintype.card ι + 2) * p)) *
        ∫⁻ x, sharpMaximalFunction volume f x ^ p := by
  set n := Fintype.card ι
  have hp0 : 0 < p := zero_lt_one.trans hp
  set f' := sharpMaximalFunction volume f
  set m : ℝ → ℝ≥0∞ := fun t => volume (czUnion f (ENNReal.ofReal t))
  set w : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (t ^ (p - 1))
  set J := ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < f' x} * w t
  set γ : ℝ := 2 ^ (-(p + 2 * n + 2))
  -- The layer cake formula: `∫ ‖f‖^p` is controlled by the truncated integrals of `m`, and
  -- `∫ (f^#)^p = p J`.
  have hIoi : Ioi (0 : ℝ) = ⋃ N : ℕ, Ioo 0 (N : ℝ) := by
    ext t
    simp only [mem_Ioi, mem_iUnion, mem_Ioo]
    exact ⟨fun ht => (exists_nat_gt t).imp fun N hN => ⟨ht, hN⟩, fun ⟨_, ht, _⟩ => ht⟩
  have hdir : Directed (· ⊆ ·) fun N : ℕ => Ioo (0 : ℝ) N :=
    Monotone.directed_le fun _ _ h => Ioo_subset_Ioo_right (by exact_mod_cast h)
  calc ∫⁻ x, ‖f x‖ₑ ^ p
      = ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < ‖f x‖ₑ} * w t :=
        lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul volume hf.eNorm hp0
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), m t * w t := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_)
        gcongr
        exact volume_lt_enorm_le_volume_czUnion hf hp₀ hfp₀ (ENNReal.ofReal_pos.2 ht).ne'
    _ ≤ ENNReal.ofReal p * (2 * (ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal (γ ^ (-p)) * J))) := by
        rw [hIoi, setLIntegral_iUnion_of_directed _ hdir]
        gcongr
        exact iSup_le fun N =>
          setLIntegral_volume_czUnion_mul_rpow_le hf hp₀ hp₀p hp hfp₀ N.cast_nonneg
    _ = ENNReal.ofReal (2 ^ (p + 1) * 2 ^ ((p + 2 * n + 2) * p)) * ∫⁻ x, f' x ^ p := by
        rw [lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul volume
          (measurable_sharpMaximalFunction volume f).aemeasurable hp0]
        have hγp : γ ^ (-p) = 2 ^ ((p + 2 * n + 2) * p) := by
          rw [← Real.rpow_mul zero_le_two]
          ring_nf
        have h2p : (2 : ℝ) ^ (p + 1) = 2 * 2 ^ p := by
          rw [Real.rpow_add two_pos, Real.rpow_one, mul_comm]
        rw [hγp, h2p, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_ofNat]
        ring

/-- **The Fefferman–Stein inequality.** For `1 < p < ∞` and `f ∈ L^p₀(ℝⁿ)`, `ℝⁿ = ι → ℝ`, `n ≥ 1`,
for some `1 ≤ p₀ ≤ p`, the `Lᵖ` norm of `f` is controlled by that of its sharp maximal function
`f^#`, with a constant depending only on `n` and `p`:

`‖f‖_p ≤ (2^(p + 1) 2^((p + 2n + 2) p))^(1 / p) ‖f^#‖_p`.

The case `p₀ = 1` is that of an integrable `f`, and `p₀ = p` that of `f ∈ Lᵖ`. Balls are taken in
the sup distance of `ι → ℝ`. The a priori integrability of `f` cannot be dropped altogether, since
`f^#` vanishes for constant `f`; and positive dimension is needed, since in dimension `0` every
ball is the whole space and `f^#` vanishes identically. -/
theorem eLpNorm_le_eLpNorm_sharpMaximalFunction [Nonempty ι] {f : (ι → ℝ) → F} {p₀ p : ℝ≥0∞}
    (hf : MemLp f p₀) (hp₀ : 1 ≤ p₀) (hp₀p : p₀ ≤ p) (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm f p volume ≤
      ENNReal.ofReal (2 ^ (p.toReal + 1) * 2 ^ ((p.toReal + 2 * Fintype.card ι + 2) * p.toReal))
          ^ (1 / p.toReal) * eLpNorm (sharpMaximalFunction volume f) p volume := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hp₀_top : p₀ ≠ ∞ := ne_top_of_le_ne_top hp_top hp₀p
  have hpr : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  have hp₀r : 1 ≤ p₀.toReal := by
    simpa using ENNReal.toReal_mono hp₀_top hp₀
  have hfp₀ : ∫⁻ x, ‖f x‖ₑ ^ p₀.toReal ≠ ∞ :=
    (lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top (zero_lt_one.trans_le hp₀).ne' hp₀_top
      hf.eLpNorm_lt_top).ne
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top hf.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp_top
      (measurable_sharpMaximalFunction volume f).aestronglyMeasurable,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  simpa only [eNorm_eq_self] using
    lintegral_enorm_rpow_le_lintegral_sharpMaximalFunction_rpow hf.aestronglyMeasurable hp₀r
      (ENNReal.toReal_mono hp_top hp₀p) hpr hfp₀

end FeffermanStein

section Euclidean

open scoped NNReal

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-- The ratio of the volume of the Euclidean ball of radius `√n r` to that of the sup-distance ball
of radius `r` does not depend on `r`. -/
private theorem volume_ball_sqrt_card_mul_div_volume_ball (c : ι → ℝ) (c' : EuclideanSpace ℝ ι)
    {r : ℝ} (hr : 0 < r) :
    volume (ball c' (√(Fintype.card ι) * r)) / volume (ball c r) =
      ENNReal.ofReal (√(Fintype.card ι) ^ Fintype.card ι) *
        volume (ball (0 : EuclideanSpace ℝ ι) 1) / volume (ball (0 : ι → ℝ) 1) := by
  rw [Measure.addHaar_ball _ _ (by positivity), Measure.addHaar_ball _ _ hr.le]
  simp only [finrank_euclideanSpace, Module.finrank_fintype_fun_eq_card, mul_pow]
  rw [ENNReal.ofReal_mul (by positivity), mul_comm (ENNReal.ofReal (√_ ^ _)), mul_assoc,
    ENNReal.mul_div_mul_left _ _ (ENNReal.ofReal_pos.2 (pow_pos hr _)).ne' ENNReal.ofReal_ne_top,
    mul_div_assoc]

/-- The sharp maximal function of `f` read in coordinates, for sup-distance balls, is at most a
fixed multiple of the sharp maximal function of `f` for Euclidean balls. -/
private theorem sharpMaximalFunction_comp_toLp_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [CompleteSpace F] {f : EuclideanSpace ℝ ι → F} (hf : Integrable f)
    (y : ι → ℝ) :
    sharpMaximalFunction volume (fun z => f (WithLp.toLp 2 z)) y ≤
      2 * (ENNReal.ofReal (√(Fintype.card ι) ^ Fintype.card ι) *
        volume (ball (0 : EuclideanSpace ℝ ι) 1) / volume (ball (0 : ι → ℝ) 1)) *
        sharpMaximalFunction volume f (WithLp.toLp 2 y) := by
  refine sharpMaximalFunction_le fun c r hy => ?_
  have hr : 0 < r := dist_nonneg.trans_lt (mem_ball.1 hy)
  set B := ball (WithLp.toLp 2 c : EuclideanSpace ℝ ι) (√(Fintype.card ι) * r)
  set S : Set (EuclideanSpace ℝ ι) := WithLp.ofLp ⁻¹' ball c r
  have hSB : S ⊆ B := by simpa using PiLp.preimage_ofLp_ball_subset_ball (WithLp.toLp 2 c) r
  have hS : volume S = volume (ball c r) :=
    (PiLp.volume_preserving_ofLp ι).measure_preimage measurableSet_ball.nullMeasurableSet
  -- The coordinate map preserves volume, so the oscillation over `ball c r` is that over `S`.
  have he : volume.map (MeasurableEquiv.toLp 2 (ι → ℝ)).symm = (1 : ℝ≥0∞) • volume := by
    rw [one_smul, (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp ι).map_eq]
  rw [← setLAverage_enorm_sub_setAverage_comp_preimage_of_map_eq_smul he one_ne_zero
    ENNReal.one_ne_top]
  -- Compare with the oscillation about the Euclidean average `f_B`, and enlarge `S` to `B`.
  refine (setLAverage_enorm_sub_setAverage_le (s := S) hf.integrableOn (⨍ x in B, f x)).trans ?_
  rw [mul_assoc]
  gcongr 2 * ?_
  refine (setLAverage_le_div_mul_setLAverage_of_subset hSB measure_ball_lt_top.ne).trans ?_
  rw [hS, volume_ball_sqrt_card_mul_div_volume_ball c _ hr]
  gcongr
  exact setLAverage_enorm_sub_setAverage_le_sharpMaximalFunction volume f
    (PiLp.preimage_ofLp_ball_subset_ball (WithLp.toLp 2 c) r (by simpa using hy))

/- This transport from the sup-distance version is shared with
https://github.com/TauCetiProject/TauCeti/pull/33788. -/
/-- **The Fefferman–Stein inequality for Euclidean balls.** For `1 < p < ∞` there is a constant
`C`, depending only on `ι` and `p`, such that every integrable `f` on `EuclideanSpace ℝ ι`,
`ι` nonempty, with values in any real Banach space, satisfies

`∫ ‖f‖^p ≤ C ∫ (f^#)^p`,

where `f^#` is the sharp maximal function for the balls of the Euclidean distance. -/
theorem exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow {p : ℝ}
    (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : EuclideanSpace ℝ ι → F), Integrable f →
        ∫⁻ x, ‖f x‖ₑ ^ p ≤ C * ∫⁻ x, sharpMaximalFunction volume f x ^ p := by
  have hp0 : 0 ≤ p := zero_le_one.trans hp.le
  set T : (ι → ℝ) → EuclideanSpace ℝ ι := WithLp.toLp 2
  have hT : MeasurePreserving T := PiLp.volume_preserving_toLp ι
  have hTe : MeasurableEmbedding T := (MeasurableEquiv.toLp 2 (ι → ℝ)).measurableEmbedding
  set K : ℝ≥0∞ := 2 * (ENNReal.ofReal (√(Fintype.card ι) ^ Fintype.card ι) *
    volume (ball (0 : EuclideanSpace ℝ ι) 1) / volume (ball (0 : ι → ℝ) 1))
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (by simp) (ENNReal.div_ne_top
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_ball_lt_top.ne)
    (measure_ball_pos _ _ one_pos).ne')
  set C₀ : ℝ≥0∞ := ENNReal.ofReal (2 ^ (p + 1) * 2 ^ ((p + 2 * Fintype.card ι + 2) * p))
  refine ⟨(C₀ * K ^ p).toNNReal, fun {F} _ _ _ f hf => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg hp0 hK))]
  calc ∫⁻ x, ‖f x‖ₑ ^ p
      = ∫⁻ y, ‖f (T y)‖ₑ ^ p := (hT.lintegral_comp_emb hTe (fun x => ‖f x‖ₑ ^ p)).symm
    _ ≤ C₀ * ∫⁻ y, sharpMaximalFunction volume (fun z => f (T z)) y ^ p :=
        lintegral_enorm_rpow_le_lintegral_sharpMaximalFunction_rpow
          (hT.integrable_comp_of_integrable hf).aestronglyMeasurable le_rfl hp.le hp
          (by simpa using (hT.integrable_comp_of_integrable hf).hasFiniteIntegral.ne)
    _ ≤ C₀ * ∫⁻ y, (K * sharpMaximalFunction volume f (T y)) ^ p := by
        gcongr with y
        exact sharpMaximalFunction_comp_toLp_le hf y
    _ = C₀ * K ^ p * ∫⁻ x, sharpMaximalFunction volume f x ^ p := by
        simp_rw [ENNReal.mul_rpow_of_nonneg _ _ hp0]
        rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg hp0 hK), mul_assoc,
          hT.lintegral_comp_emb hTe (fun x => sharpMaximalFunction volume f x ^ p)]

/-- **The Fefferman–Stein inequality for Euclidean balls**, in terms of `Lᵖ` seminorms. For
`1 < p < ∞` there is a constant `C`, depending only on `ι` and `p`, such that every integrable `f`
on `EuclideanSpace ℝ ι`, `ι` nonempty, with values in any real Banach space, satisfies
`‖f‖_p ≤ C ‖f^#‖_p`, where `f^#` is the sharp maximal function for the balls of the Euclidean
distance. -/
theorem exists_eLpNorm_le_mul_eLpNorm_sharpMaximalFunction {p : ℝ≥0∞} (hp : 1 < p)
    (hp_top : p ≠ ∞) :
    ∃ C : ℝ≥0, ∀ {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
      (f : EuclideanSpace ℝ ι → F), Integrable f →
        eLpNorm f p volume ≤ C * eLpNorm (sharpMaximalFunction volume f) p volume := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hpr : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  obtain ⟨C, hC⟩ :=
    exists_lintegral_enorm_rpow_le_mul_lintegral_sharpMaximalFunction_rpow (ι := ι) hpr
  refine ⟨C ^ (1 / p.toReal), fun {F} _ _ _ f hf => ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ hp_top hf.1,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp₀ hp_top
      (measurable_sharpMaximalFunction volume f).aestronglyMeasurable,
    ENNReal.coe_rpow_of_nonneg _ (by positivity), ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  simpa only [eNorm_eq_self] using hC f hf

end Euclidean

end TauCeti
