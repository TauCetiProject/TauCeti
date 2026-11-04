/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.CalderonZygmund.Decomposition
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Integral

/-!
# The sharp maximal function and the Fefferman–Stein inequality

The **sharp maximal function** of a locally integrable `f` is

`f^# x = sup_{B ∋ x} ⨍_B ‖f - f_B‖`, where `f_B = ⨍_B f`,

the supremum of the mean oscillations of `f` over the open balls `B` containing `x`. It is bounded
exactly when `f` has bounded mean oscillation, and it measures the local oscillation of `f`
rather than its size: it vanishes for constant `f`. The **Fefferman–Stein inequality** says that
nevertheless, for `1 < p < ∞`, the sharp maximal function controls the `Lᵖ` norm of `f` itself:

`‖f‖_p ≤ C ‖f^#‖_p`

with `C` depending only on the dimension `n` and on `p`, for every integrable `f` on
`ℝⁿ = ι → ℝ`, `n ≥ 1`, with balls taken in the sup distance
(`TauCeti.eLpNorm_le_eLpNorm_sharpMaximalFunction`). Some a priori integrability is needed, since
`f^#` does not see constants. The inequality fails in dimension `0`, where `f^#` vanishes
identically.

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
  `∫₀ᴺ p t^(p-1) m(t) dt ≤ 2^p 2²ⁿ⁺¹ γ ∫₀ᴺ p t^(p-1) m(t) dt + 2^p γ^(-p) ∫ (f^#)^p`. Since `f` is
  integrable, `m(t) ≤ ‖f‖₁ / t`, so the integrals on the left are finite for `p > 1`, and the
  choice `γ = 2^(-(p + 2n + 2))` lets the first term on the right be absorbed. As `‖f‖ ≤ t`
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
  have hosc (s : Set X) : ⨍⁻ y in s, ‖f y - ⨍ z in s, f z ∂μ‖ₑ ∂μ =
      ⨍⁻ y in s, ‖g y - ⨍ z in s, g z ∂μ‖ₑ ∂μ := by
    have hs : f =ᵐ[μ.restrict s] g := ae_restrict_of_ae h
    rw [average_congr hs]
    exact laverage_congr (hs.mono fun y hy => by simp only [hy])
  funext x
  simp only [sharpMaximalFunction, hosc]

/-- The sharp maximal function does not see constants: adding a constant to an a.e. strongly
measurable `f` leaves `f^#` unchanged. -/
@[simp]
theorem sharpMaximalFunction_add_const [CompleteSpace F] (hf : AEStronglyMeasurable f μ) (b : F) :
    sharpMaximalFunction μ (fun y => f y + b) = sharpMaximalFunction μ f := by
  funext x
  simp only [sharpMaximalFunction, setLAverage_enorm_add_const_sub hf]

/-- The sharp maximal function is homogeneous: `(k • f)^# = ‖k‖ₑ f^#`. -/
@[simp]
theorem sharpMaximalFunction_const_smul {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F]
    [NormSMulClass 𝕜 F] [SMulCommClass ℝ 𝕜 F] (k : 𝕜) (x : X) :
    sharpMaximalFunction μ (k • f) x = ‖k‖ₑ * sharpMaximalFunction μ f x := by
  have hosc (s : Set X) : ⨍⁻ y in s, ‖k • f y - ⨍ z in s, k • f z ∂μ‖ₑ ∂μ =
      ‖k‖ₑ * ⨍⁻ y in s, ‖f y - ⨍ z in s, f z ∂μ‖ₑ ∂μ := by
    have havg : ⨍ z in s, k • f z ∂μ = k • ⨍ z in s, f z ∂μ := integral_smul k f
    simp_rw [havg, ← smul_sub, enorm_smul, setLAverage_eq,
      lintegral_const_mul' _ _ enorm_ne_top, mul_div_assoc]
  simp only [sharpMaximalFunction, Pi.smul_apply, hosc, ENNReal.mul_iSup]

/-- The sharp maximal function is subadditive on a.e. strongly measurable functions. -/
theorem sharpMaximalFunction_add_le {g : X → F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (x : X) :
    sharpMaximalFunction μ (f + g) x ≤ sharpMaximalFunction μ f x + sharpMaximalFunction μ g x :=
  sharpMaximalFunction_le fun _ _ hx => (setLAverage_enorm_add_sub_le hf hg _).trans
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

/-- For integrable `f`, the superlevel set `{‖f‖ > t}` is, up to a null set, contained in the
union of the Calderón–Zygmund cubes at height `t`. -/
private theorem volume_lt_enorm_le_volume_czUnion [Nonempty ι] {f : (ι → ℝ) → F}
    (hf : Integrable f) {t : ℝ≥0∞} (ht : t ≠ 0) :
    volume {x | t < ‖f x‖ₑ} ≤ volume (czUnion f t) := by
  refine measure_mono_ae ?_
  filter_upwards [ae_le_of_forall_notMem_calderonZygmundCubes hf.1.enorm hf.2.ne ht]
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
        lintegral_mono fun y => by simpa using enorm_add_le (f y - a) a
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

/-- **The good-`λ` inequality.** For integrable `f`, `0 < t < ∞` and every `γ`,

`m(2t) ≤ 2²ⁿ⁺¹ γ m(t) + |{f^# > γ t}|`,

where `m(s)` is the measure of the union of the Calderón–Zygmund cubes of `‖f‖` at height `s`. -/
private theorem volume_czUnion_two_mul_le [Nonempty ι] {f : (ι → ℝ) → F} (hf : Integrable f)
    {t : ℝ≥0∞} (ht : t ≠ 0) (ht' : t ≠ ∞) (γ : ℝ≥0∞) :
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
      refine (mul_volume_czUnion_two_mul_inter_le hf.locallyIntegrable ht' hq hxQ).trans ?_
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
    biUnion_calderonZygmundCubes_subset hf.2.ne ht (two_mul t ▸ le_self_add)
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

/-- For integrable `f` and `p > 1`, the truncated layer cake integral
`∫₀ᴺ m(t) t^(p-1) dt` of the measures `m(t)` of the Calderón–Zygmund unions is finite, since
`m(t) ≤ ‖f‖₁ / t`. -/
private theorem setLIntegral_volume_czUnion_mul_rpow_ne_top {f : (ι → ℝ) → F} (hf : Integrable f)
    {p : ℝ} (hp : 1 < p) {N : ℝ} (hN : 0 ≤ N) :
    ∫⁻ t in Ioo 0 N, volume (czUnion f (ENNReal.ofReal t)) * ENNReal.ofReal (t ^ (p - 1)) ≠ ∞ := by
  refine ne_top_of_le_ne_top ?_ (setLIntegral_mono' (g := fun t =>
    (∫⁻ x, ‖f x‖ₑ) * ENNReal.ofReal (t ^ (p - 2))) measurableSet_Ioo fun t ht => ?_)
  · rw [lintegral_const_mul' _ _ hf.2.ne, lintegral_ofReal_rpow_Ioo (by linarith) hN]
    exact ENNReal.mul_ne_top hf.2.ne ENNReal.ofReal_ne_top
  have hsplit : ENNReal.ofReal (t ^ (p - 1)) = ENNReal.ofReal (t ^ (p - 2)) * ENNReal.ofReal t := by
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

/-- **The truncated Fefferman–Stein estimate.** For integrable `f`, `p > 1`, `N ≥ 0` and
`γ = 2^(-(p + 2n + 2))`,

`∫₀ᴺ m(t) t^(p-1) dt ≤ 2^(p + 1) γ^(-p) ∫₀^∞ |{f^# > t}| t^(p-1) dt`,

where `m(t)` is the measure of the union of the Calderón–Zygmund cubes of `‖f‖` at height `t`.
Substituting `t = 2s` and applying the good-`λ` inequality bounds the left side by half of itself
plus the right side, and the left side is finite, so the first term is absorbed. -/
private theorem setLIntegral_volume_czUnion_mul_rpow_le [Nonempty ι] {f : (ι → ℝ) → F}
    (hf : Integrable f) {p : ℝ} (hp : 1 < p) {N : ℝ} (hN : 0 ≤ N) :
    ∫⁻ t in Ioo 0 N, volume (czUnion f (ENNReal.ofReal t)) * ENNReal.ofReal (t ^ (p - 1)) ≤
      2 * (ENNReal.ofReal (2 ^ p) *
        (ENNReal.ofReal (((2 : ℝ) ^ (-(p + 2 * Fintype.card ι + 2))) ^ (-p)) *
          ∫⁻ t in Ioi (0 : ℝ), volume {x | ENNReal.ofReal t < sharpMaximalFunction volume f x} *
            ENNReal.ofReal (t ^ (p - 1)))) := by
  set n := Fintype.card ι
  set f' := sharpMaximalFunction volume f
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
  have hw : Measurable w := ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)
  have hσ : Antitone σ := fun s t hst => measure_mono fun x (hx : ENNReal.ofReal t < f' x) =>
    (ENNReal.ofReal_le_ofReal hst).trans_lt hx
  -- The good-`λ` inequality at height `s`.
  have hlevel : ∀ s : ℝ, 0 < s → m (2 * s) ≤ K * ENNReal.ofReal γ * m s + σ (γ * s) := by
    intro s hs
    have h := volume_czUnion_two_mul_le hf (ENNReal.ofReal_pos.2 hs).ne' ENNReal.ofReal_ne_top
      (ENNReal.ofReal γ)
    simp only [m, σ, f']
    rwa [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat, ENNReal.ofReal_mul hγ.le]
  -- Integrated against `w`, the term `σ (γ s)` is `γ^(-p)` times the layer cake integral `J`.
  have hJ : ∫⁻ s in Ioi (0 : ℝ), σ (γ * s) * w s = ENNReal.ofReal (γ ^ (-p)) * J := by
    rw [setLIntegral_comp_mul_left_mul_rpow σ hγ measurableSet_Ioi (S := Ioi 0)
      (fun s => (mul_pos_iff_of_pos_left hγ).symm) Ioi_subset_Ici_self, sub_add_cancel]
  have hconst : ENNReal.ofReal (2 ^ p) * (K * ENNReal.ofReal γ) = 2⁻¹ :=
    ofReal_two_rpow_mul_two_pow_mul_ofReal_two_rpow n p
  -- Substituting `t = 2 s` and applying the good-`λ` inequality bounds `I N` by `I N / 2 + …`.
  have hscale := setLIntegral_comp_mul_left_mul_rpow m two_pos measurableSet_Ioo
    (S := Ioo 0 N) (T := Ioo 0 (N / 2)) (fun s => by
      simp only [mem_Ioo]
      constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith)
    (fun s hs => le_of_lt hs.1) (p - 1)
  rw [sub_add_cancel] at hscale
  have h2p : ENNReal.ofReal (2 ^ p) * ENNReal.ofReal (2 ^ (-p)) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add two_pos]
    simp
  have hσw : Measurable fun s => σ (γ * s) * w s :=
    ((hσ.comp_monotone fun _ _ h => mul_le_mul_of_nonneg_left h hγ.le).measurable).mul hw
  have hstep : I N ≤ 2⁻¹ * I N + ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal (γ ^ (-p)) * J) :=
    calc I N = ENNReal.ofReal (2 ^ p) * ∫⁻ s in Ioo 0 (N / 2), m (2 * s) * w s := by
          rw [hscale, ← mul_assoc, h2p, one_mul]
      _ ≤ ENNReal.ofReal (2 ^ p) * ∫⁻ s in Ioo 0 (N / 2),
            (K * ENNReal.ofReal γ * (m s * w s) + σ (γ * s) * w s) := by
          refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioo fun s hs => ?_)
          rw [← mul_assoc, ← add_mul]
          gcongr
          exact hlevel s hs.1
      _ = ENNReal.ofReal (2 ^ p) * (K * ENNReal.ofReal γ * I (N / 2) +
            ∫⁻ s in Ioo 0 (N / 2), σ (γ * s) * w s) := by
          rw [lintegral_add_right' _ hσw.aemeasurable,
            lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by simp [K]) ENNReal.ofReal_ne_top)]
      _ ≤ ENNReal.ofReal (2 ^ p) * (K * ENNReal.ofReal γ * I N +
            ∫⁻ s in Ioi (0 : ℝ), σ (γ * s) * w s) := by
          gcongr
          · exact lintegral_mono_set (Ioo_subset_Ioo_right (by linarith))
          · exact Ioo_subset_Ioi_self
      _ = 2⁻¹ * I N + ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal (γ ^ (-p)) * J) := by
          rw [hJ, mul_add, ← mul_assoc, ← mul_assoc, ← hconst]
          ring
  -- Since `I N` is finite, the first term is absorbed.
  have hhalf : 2⁻¹ * I N ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (setLIntegral_volume_czUnion_mul_rpow_ne_top hf hp hN)
  have h : 2⁻¹ * I N + 2⁻¹ * I N ≤
      2⁻¹ * I N + ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal (γ ^ (-p)) * J) := by
    rw [← add_mul, ENNReal.inv_two_add_inv_two, one_mul]
    exact hstep
  calc I N = 2 * (2⁻¹ * I N) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top, one_mul]
    _ ≤ _ := mul_le_mul' le_rfl (ENNReal.le_of_add_le_add_left hhalf h)

/-- **The Fefferman–Stein inequality**, as an inequality between the integrals `∫⁻ ‖·‖ₑ ^ p`.
For `1 < p < ∞` and integrable `f` on `ℝⁿ = ι → ℝ`, `n ≥ 1`,

`∫ ‖f‖^p ≤ 2^(p + 1) 2^((p + 2n + 2) p) ∫ (f^#)^p`,

where `f^#` is the sharp maximal function for balls in the sup distance. -/
theorem lintegral_enorm_rpow_le_lintegral_sharpMaximalFunction_rpow [Nonempty ι]
    {f : (ι → ℝ) → F} (hf : Integrable f) {p : ℝ} (hp : 1 < p) :
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
        lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul volume hf.1.enorm hp0
    _ ≤ ENNReal.ofReal p * ∫⁻ t in Ioi (0 : ℝ), m t * w t := by
        refine mul_le_mul' le_rfl (setLIntegral_mono' measurableSet_Ioi fun t ht => ?_)
        gcongr
        exact volume_lt_enorm_le_volume_czUnion hf (ENNReal.ofReal_pos.2 ht).ne'
    _ ≤ ENNReal.ofReal p * (2 * (ENNReal.ofReal (2 ^ p) * (ENNReal.ofReal (γ ^ (-p)) * J))) := by
        rw [hIoi, setLIntegral_iUnion_of_directed _ hdir]
        gcongr
        exact iSup_le fun N => setLIntegral_volume_czUnion_mul_rpow_le hf hp N.cast_nonneg
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

/-- **The Fefferman–Stein inequality.** For `1 < p < ∞` and integrable `f` on `ℝⁿ = ι → ℝ`,
`n ≥ 1`, the `Lᵖ` norm of `f` is controlled by that of its sharp maximal function `f^#`, with a
constant depending only on `n` and `p`:

`‖f‖_p ≤ (2^(p + 1) 2^((p + 2n + 2) p))^(1 / p) ‖f^#‖_p`.

Balls are taken in the sup distance of `ι → ℝ`. The integrability of `f` cannot be dropped
altogether, since `f^#` vanishes for constant `f`; and positive dimension is needed, since in
dimension `0` every ball is the whole space and `f^#` vanishes identically. -/
theorem eLpNorm_le_eLpNorm_sharpMaximalFunction [Nonempty ι] {f : (ι → ℝ) → F}
    (hf : Integrable f) {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) :
    eLpNorm f p volume ≤
      ENNReal.ofReal (2 ^ (p.toReal + 1) * 2 ^ ((p.toReal + 2 * Fintype.card ι + 2) * p.toReal))
          ^ (1 / p.toReal) * eLpNorm (sharpMaximalFunction volume f) p volume := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hpr : 1 < p.toReal := by
    simpa using (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top hf.1,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp_top
      (measurable_sharpMaximalFunction volume f).aestronglyMeasurable,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
  refine ENNReal.rpow_le_rpow ?_ (by positivity)
  simpa only [enorm_eq_self] using
    lintegral_enorm_rpow_le_lintegral_sharpMaximalFunction_rpow hf hpr

end FeffermanStein

end TauCeti
