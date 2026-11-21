/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Iterated improper tail integrals

For a normed-space-valued function `f : ℝ → E`, its sequence of repeated improper tail integrals
is defined recursively by `I_0 = f` and
`I_{n + 1} x = lim_{R → ∞} ∫ t in x..R, I_n t` (`TauCeti.iteratedTailIntegral`). Unlike iterated
Bochner integrals over `Ioi x`, these improper integrals converge for conditionally integrable
oscillatory functions whose amplitude decays too slowly for absolute integrability.

This file develops the general calculus of `TauCeti.iteratedTailIntegral`:

* Congruence on rays (`Ici a`, `Ioi a`, and `atTop`), vanishing on `0`, and right translation
  invariance.
* Basepoint splitting on `[a, ∞)`, vanishing at `+∞`, continuity on `[a, ∞)`, and local
  integrability of all higher iterates.
* Agreement with Bochner tail integrals on `(x, ∞)` when absolutely integrable.
* One- and two-sided differentiation (`I_{n + 1}' = -I_n`) and higher `iteratedDeriv` formulas.
* Linearity (`const_smul`, `neg`, `add`, `sub`).
* Cauchy's single-integral representation
  `I_{n + 1} x = (n !)⁻¹ • ∫ t in Ioi x, (t - x) ^ n • f t` when the weighted tail is Bochner
  integrable, together with the closed form for decaying exponentials.

## Main declarations

* `TauCeti.iteratedTailIntegral`: repeated improper tail integrals `I_n` of `f : ℝ → E`.
* `TauCeti.iteratedTailIntegral_congr_Ici`, `TauCeti.iteratedTailIntegral_succ_congr_Ioi`,
  `TauCeti.iteratedTailIntegral_congr_atTop`: unconditional ray congruence lemmas.
* `TauCeti.continuousOn_iteratedTailIntegral_succ`,
  `TauCeti.locallyIntegrableOn_iteratedTailIntegral`,
  `TauCeti.tendsto_iteratedTailIntegral_succ_atTop`: continuity on `[a, ∞)`, local integrability of
  higher iterates, and vanishing at `+∞`.
* `TauCeti.hasStrictDerivAt_iteratedTailIntegral_succ`,
  `TauCeti.hasDerivWithinAt_iteratedTailIntegral_succ`,
  `TauCeti.iteratedDeriv_iteratedTailIntegral`: differentiation of iterated tail integrals.
* `TauCeti.iteratedTailIntegral_succ_eq_inv_factorial_smul_integral_Ioi`: Cauchy's repeated
  tail-integral formula on `(x, ∞)`.

## References

* F. W. J. Olver, *Asymptotics and Special Functions*, Academic Press, 1974.
* NIST Digital Library of Mathematical Functions, §9.10(v).
-/

public section

namespace TauCeti

open Filter MeasureTheory Set
open scoped Topology Interval

section Basic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Iterated improper tail integrals** of `f : ℝ → E`: `iteratedTailIntegral f 0 = f`, and
`iteratedTailIntegral f (n + 1) x` is the improper integral
`lim_{R → ∞} ∫ t in x..R, iteratedTailIntegral f n t` defined via `limUnder atTop`. -/
noncomputable def iteratedTailIntegral (f : ℝ → E) : ℕ → ℝ → E
  | 0, x => f x
  | n + 1, x => limUnder atTop fun R : ℝ ↦ ∫ t in x..R, iteratedTailIntegral f n t

@[simp]
theorem iteratedTailIntegral_zero (f : ℝ → E) : iteratedTailIntegral f 0 = f := by rfl

theorem iteratedTailIntegral_zero_apply (f : ℝ → E) (x : ℝ) :
    iteratedTailIntegral f 0 x = f x := by rfl

theorem iteratedTailIntegral_succ_apply (f : ℝ → E) (n : ℕ) (x : ℝ) :
    iteratedTailIntegral f (n + 1) x =
      limUnder atTop fun R : ℝ ↦ ∫ t in x..R, iteratedTailIntegral f n t := by rfl

theorem iteratedTailIntegral_one_apply (f : ℝ → E) (x : ℝ) :
    iteratedTailIntegral f 1 x = limUnder atTop fun R : ℝ ↦ ∫ t in x..R, f t := by rfl

/-- Semigroup law for `iteratedTailIntegral`: taking `m + n` repeated tail integrals is taking `m`
repeated tail integrals of `iteratedTailIntegral f n`. -/
theorem iteratedTailIntegral_add_right (f : ℝ → E) (m n : ℕ) :
    iteratedTailIntegral f (m + n) = iteratedTailIntegral (iteratedTailIntegral f n) m := by
  induction m with
  | zero => simp
  | succ m ih => ext x; simp [Nat.succ_add, iteratedTailIntegral_succ_apply, ih]

/-- Taking `n + 1` repeated tail integrals is taking one tail integral of
`iteratedTailIntegral f n`. -/
theorem iteratedTailIntegral_succ (f : ℝ → E) (n : ℕ) :
    iteratedTailIntegral f (n + 1) = iteratedTailIntegral (iteratedTailIntegral f n) 1 := by
  simpa [Nat.add_comm] using iteratedTailIntegral_add_right f 1 n

/-- Taking `n + 1` repeated tail integrals is taking `n` repeated tail integrals of the first tail
integral `iteratedTailIntegral f 1`. -/
theorem iteratedTailIntegral_succ' (f : ℝ → E) (n : ℕ) :
    iteratedTailIntegral f (n + 1) = iteratedTailIntegral (iteratedTailIntegral f 1) n :=
  iteratedTailIntegral_add_right f n 1

/-- If the truncated integrals `∫ t in x..R, iteratedTailIntegral f n t` tend to `L` as `R → ∞`,
then `iteratedTailIntegral f (n + 1) x = L`. -/
theorem iteratedTailIntegral_succ_eq_of_tendsto {f : ℝ → E} {n : ℕ} {x : ℝ} {L : E}
    (h : Tendsto (fun R : ℝ ↦ ∫ t in x..R, iteratedTailIntegral f n t) atTop (𝓝 L)) :
    iteratedTailIntegral f (n + 1) x = L :=
  h.limUnder_eq

/-- If the truncated integrals `∫ t in x..R, f t` tend to `L` as `R → ∞`, then
`iteratedTailIntegral f 1 x = L`. -/
theorem iteratedTailIntegral_one_eq_of_tendsto {f : ℝ → E} {x : ℝ} {L : E}
    (h : Tendsto (fun R : ℝ ↦ ∫ t in x..R, f t) atTop (𝓝 L)) :
    iteratedTailIntegral f 1 x = L :=
  h.limUnder_eq

@[simp]
theorem iteratedTailIntegral_zero_fun (n : ℕ) : iteratedTailIntegral (0 : ℝ → E) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    ext x
    rw [iteratedTailIntegral_succ_apply, ih]
    simp only [Pi.zero_apply, intervalIntegral.integral_zero]
    exact tendsto_const_nhds.limUnder_eq

theorem iteratedTailIntegral_zero_fun_apply (n : ℕ) (x : ℝ) :
    iteratedTailIntegral (0 : ℝ → E) n x = 0 := by simp

/-- In an incomplete normed space, every Bochner integral vanishes, so every positive-order
`iteratedTailIntegral` is identically `0`. -/
theorem iteratedTailIntegral_succ_of_not_completeSpace (hE : ¬ CompleteSpace E) (f : ℝ → E)
    (n : ℕ) (x : ℝ) : iteratedTailIntegral f (n + 1) x = 0 := by
  rw [iteratedTailIntegral_succ_apply]
  simp_rw [intervalIntegral, integral_of_not_completeSpace hE, sub_zero]
  exact tendsto_const_nhds.limUnder_eq

/-- Translating the argument of `f` by `c` translates every `iteratedTailIntegral` by `c`. -/
@[simp]
theorem iteratedTailIntegral_comp_add_right (f : ℝ → E) (c : ℝ) (n : ℕ) (x : ℝ) :
    iteratedTailIntegral (fun t ↦ f (t + c)) n x = iteratedTailIntegral f n (x + c) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [iteratedTailIntegral_succ_apply, ih, intervalIntegral.integral_comp_add_right]
    rw [limUnder, limUnder,
      ← Function.comp_def (fun R ↦ ∫ t in x + c..R, iteratedTailIntegral f n t) (· + c),
      ← Filter.map_map, Filter.map_add_atTop_eq]

/-- Two functions agreeing on `[a, ∞)` have identical `iteratedTailIntegral` on `[a, ∞)`. -/
theorem iteratedTailIntegral_congr_Ici {f g : ℝ → E} {a : ℝ} (h : EqOn f g (Ici a)) (n : ℕ) :
    EqOn (iteratedTailIntegral f n) (iteratedTailIntegral g n) (Ici a) := by
  induction n with
  | zero => exact h
  | succ n ih =>
    intro x (hx : a ≤ x)
    rw [iteratedTailIntegral_succ_apply, iteratedTailIntegral_succ_apply, limUnder, limUnder]
    congr 1
    refine Filter.map_congr ?_
    filter_upwards [eventually_ge_atTop x] with R hR
    exact intervalIntegral.integral_congr fun t ht ↦ ih (hx.trans ((uIcc_of_le hR ▸ ht).1))

/-- Two functions agreeing on `(a, ∞)` have identical positive-order `iteratedTailIntegral` on
`[a, ∞)` (including at the endpoint `a`). -/
theorem iteratedTailIntegral_succ_congr_Ioi {f g : ℝ → E} {a : ℝ} (h : EqOn f g (Ioi a)) (n : ℕ) :
    EqOn (iteratedTailIntegral f (n + 1)) (iteratedTailIntegral g (n + 1)) (Ici a) := by
  have h1 : EqOn (iteratedTailIntegral f 1) (iteratedTailIntegral g 1) (Ici a) := by
    intro x (hx : a ≤ x)
    rw [iteratedTailIntegral_one_apply, iteratedTailIntegral_one_apply, limUnder, limUnder]
    congr 1
    refine Filter.map_congr ?_
    filter_upwards [eventually_ge_atTop x] with R hR
    rw [intervalIntegral.integral_of_le hR, intervalIntegral.integral_of_le hR]
    exact setIntegral_congr_fun measurableSet_Ioc fun t ht ↦ h (hx.trans_lt ht.1)
  rw [iteratedTailIntegral_succ' f, iteratedTailIntegral_succ' g]
  exact iteratedTailIntegral_congr_Ici h1 n

/-- Two functions agreeing eventually at `+∞` have eventually equal `iteratedTailIntegral` at `+∞`.
-/
theorem iteratedTailIntegral_congr_atTop {f g : ℝ → E} (h : f =ᶠ[atTop] g) (n : ℕ) :
    iteratedTailIntegral f n =ᶠ[atTop] iteratedTailIntegral g n := by
  obtain ⟨a, ha⟩ := eventually_atTop.mp h
  exact eventually_atTop.mpr ⟨a, iteratedTailIntegral_congr_Ici ha n⟩

/-- Under convergence from a basepoint `b ≥ a`, `iteratedTailIntegral f (n + 1) x` for `x ≥ a` is
obtained from `L = iteratedTailIntegral f (n + 1) b` by subtracting the finite integral over
`b..x`. -/
theorem iteratedTailIntegral_succ_eq_sub_intervalIntegral {f : ℝ → E} {n : ℕ} {a b x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a)) (hb : a ≤ b) (hx : a ≤ x)
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in b..R, iteratedTailIntegral f n t) atTop (𝓝 L)) :
    iteratedTailIntegral f (n + 1) x = L - ∫ t in b..x, iteratedTailIntegral f n t :=
  (hloc.tendsto_intervalIntegral_sub hb hx hconv).limUnder_eq

/-- Under convergence from a basepoint `b ≥ a`, subtracting `iteratedTailIntegral f (n + 1) y` from
`iteratedTailIntegral f (n + 1) x` recovers `∫ t in x..y, iteratedTailIntegral f n t` for any
`x, y ≥ a`. -/
theorem iteratedTailIntegral_succ_sub_eq_intervalIntegral {f : ℝ → E} {n : ℕ} {a b x y : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a)) (hb : a ≤ b) (hx : a ≤ x)
    (hy : a ≤ y)
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in b..R, iteratedTailIntegral f n t) atTop (𝓝 L)) :
    iteratedTailIntegral f (n + 1) x - iteratedTailIntegral f (n + 1) y =
      ∫ t in x..y, iteratedTailIntegral f n t := by
  rw [iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc hb hx hconv,
    iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc hb hy hconv,
    sub_sub_sub_cancel_left,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hloc.intervalIntegrable fun _ ht ↦ (le_min hb hx).trans ht.1)
      (hloc.intervalIntegrable fun _ ht ↦ (le_min hx hy).trans ht.1),
    add_sub_cancel_left]

/-- Under convergence from a basepoint `b ≥ a`, subtracting `iteratedTailIntegral f 1 y` from
`iteratedTailIntegral f 1 x` recovers `∫ t in x..y, f t` for any `x, y ≥ a`. -/
theorem iteratedTailIntegral_one_sub_eq_intervalIntegral {f : ℝ → E} {a b x y : ℝ} {L : E}
    (hloc : LocallyIntegrableOn f (Ici a)) (hb : a ≤ b) (hx : a ≤ x) (hy : a ≤ y)
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in b..R, f t) atTop (𝓝 L)) :
    iteratedTailIntegral f 1 x - iteratedTailIntegral f 1 y = ∫ t in x..y, f t :=
  iteratedTailIntegral_succ_sub_eq_intervalIntegral (n := 0) hloc hb hx hy hconv

/-- Every convergent improper tail integral `iteratedTailIntegral f (n + 1)` vanishes at `+∞`. -/
theorem tendsto_iteratedTailIntegral_succ_atTop {f : ℝ → E} {n : ℕ} {a : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L)) :
    Tendsto (iteratedTailIntegral f (n + 1)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ ↦ L - ∫ t in a..x, iteratedTailIntegral f n t) atTop (𝓝 0) := by
    simpa [sub_self] using (tendsto_const_nhds (x := L)).sub hconv
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop a] with x hx using
    (iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc le_rfl hx hconv).symm

/-- Every convergent first improper tail integral `iteratedTailIntegral f 1` vanishes at `+∞`. -/
theorem tendsto_iteratedTailIntegral_one_atTop {f : ℝ → E} {a : ℝ} {L : E}
    (hloc : LocallyIntegrableOn f (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, f t) atTop (𝓝 L)) :
    Tendsto (iteratedTailIntegral f 1) atTop (𝓝 0) :=
  tendsto_iteratedTailIntegral_succ_atTop (n := 0) hloc hconv

/-- If `iteratedTailIntegral f n` is locally integrable on `[a, ∞)`, then
`iteratedTailIntegral f (n + 1)` is continuous on `[a, ∞)`. (If the improper integral diverges,
`iteratedTailIntegral f (n + 1)` is constant on `[a, ∞)` by `Filter.limUnder_of_not_tendsto`.) -/
theorem continuousOn_iteratedTailIntegral_succ {f : ℝ → E} {n : ℕ} {a : ℝ}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a)) :
    ContinuousOn (iteratedTailIntegral f (n + 1)) (Ici a) := by
  by_cases hconv : ∃ L, Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L)
  · obtain ⟨L, hL⟩ := hconv
    refine ContinuousOn.congr (continuousOn_const.sub fun x (hx : a ≤ x) ↦ ?_)
      fun _ hx ↦ iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc le_rfl hx hL
    have hprim := intervalIntegral.continuousOn_primitive_interval'
      (hloc.intervalIntegrable fun _ ht ↦ (le_min le_rfl (by linarith : a ≤ x + 1)).trans ht.1)
      left_mem_uIcc
    rw [uIcc_of_le (by linarith : a ≤ x + 1)] at hprim
    refine (hprim x ⟨hx, by linarith⟩).mono_of_mem_nhdsWithin ?_
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (lt_add_one x))] with
      _ h1 h2 using ⟨h1, h2.le⟩
  · refine (continuousOn_const (c := Classical.choice (inferInstance : Nonempty E))).congr
      fun x (hx : a ≤ x) ↦ ?_
    rw [iteratedTailIntegral_succ_apply]
    exact limUnder_of_not_tendsto fun ⟨L, hL⟩ ↦
      hconv ⟨L - ∫ t in x..a, iteratedTailIntegral f n t,
        hloc.tendsto_intervalIntegral_sub hx le_rfl hL⟩

/-- If `f` is locally integrable on `[a, ∞)`, then `iteratedTailIntegral f 1` is continuous on
`[a, ∞)`. -/
theorem continuousOn_iteratedTailIntegral_one {f : ℝ → E} {a : ℝ}
    (hloc : LocallyIntegrableOn f (Ici a)) :
    ContinuousOn (iteratedTailIntegral f 1) (Ici a) :=
  continuousOn_iteratedTailIntegral_succ (n := 0) hloc

/-- If `f` is locally integrable on `[a, ∞)`, then every `iteratedTailIntegral f n` is locally
integrable on `[a, ∞)`. -/
theorem locallyIntegrableOn_iteratedTailIntegral {f : ℝ → E} {a : ℝ}
    (hloc : LocallyIntegrableOn f (Ici a)) (n : ℕ) :
    LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a) := by
  induction n with
  | zero => exact hloc
  | succ n ih =>
    exact (continuousOn_iteratedTailIntegral_succ ih).locallyIntegrableOn measurableSet_Ici

/-- When `iteratedTailIntegral f n` is Bochner integrable on `(x, ∞)`, its improper integral from
`x` converges to `∫ t in Ioi x, iteratedTailIntegral f n t`, so `iteratedTailIntegral f (n + 1) x`
agrees with the Bochner tail integral. -/
theorem iteratedTailIntegral_succ_eq_integral_Ioi {f : ℝ → E} {n : ℕ} {x : ℝ}
    (hint : IntegrableOn (iteratedTailIntegral f n) (Ioi x)) :
    iteratedTailIntegral f (n + 1) x = ∫ t in Ioi x, iteratedTailIntegral f n t :=
  (intervalIntegral_tendsto_integral_Ioi x hint tendsto_id).limUnder_eq

/-- When `f` is Bochner integrable on `(x, ∞)`, `iteratedTailIntegral f 1 x` equals the Bochner
tail integral `∫ t in Ioi x, f t`. -/
theorem iteratedTailIntegral_one_eq_integral_Ioi {f : ℝ → E} {x : ℝ}
    (hint : IntegrableOn f (Ioi x)) :
    iteratedTailIntegral f 1 x = ∫ t in Ioi x, f t :=
  iteratedTailIntegral_succ_eq_integral_Ioi (n := 0) hint

section Complete

variable [CompleteSpace E]

/-- At an interior point `x > a` where `iteratedTailIntegral f n` is continuous, the next tail
integral `iteratedTailIntegral f (n + 1)` has strict derivative `-iteratedTailIntegral f n x`. -/
theorem hasStrictDerivAt_iteratedTailIntegral_succ {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hcont : ContinuousAt (iteratedTailIntegral f n) x) (hx : a < x) :
    HasStrictDerivAt (iteratedTailIntegral f (n + 1)) (-iteratedTailIntegral f n x) x := by
  have hftc := intervalIntegral.integral_hasStrictDerivAt_right
    (hloc.intervalIntegrable fun _ ht ↦ (le_min le_rfl hx.le).trans ht.1)
    (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hloc.aestronglyMeasurable
      (Ici_mem_nhds hx)) hcont
  refine (hftc.const_sub L).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with _ hu using
    (iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc le_rfl hu.le hconv).symm

/-- At an interior point `x > a` where `iteratedTailIntegral f n` is continuous, the next tail
integral `iteratedTailIntegral f (n + 1)` has derivative `-iteratedTailIntegral f n x`. -/
theorem hasDerivAt_iteratedTailIntegral_succ {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hcont : ContinuousAt (iteratedTailIntegral f n) x) (hx : a < x) :
    HasDerivAt (iteratedTailIntegral f (n + 1)) (-iteratedTailIntegral f n x) x :=
  (hasStrictDerivAt_iteratedTailIntegral_succ hloc hconv hcont hx).hasDerivAt

/-- Derivative formula `deriv (iteratedTailIntegral f (n + 1)) x = -iteratedTailIntegral f n x`
at an interior continuity point `x > a`. -/
theorem deriv_iteratedTailIntegral_succ {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hcont : ContinuousAt (iteratedTailIntegral f n) x) (hx : a < x) :
    deriv (iteratedTailIntegral f (n + 1)) x = -iteratedTailIntegral f n x :=
  (hasDerivAt_iteratedTailIntegral_succ hloc hconv hcont hx).deriv

/-- On `[a, ∞)` (including at the endpoint `x = a`), if `iteratedTailIntegral f n` is continuous
within `[a, ∞)` at `x`, then `iteratedTailIntegral f (n + 1)` has derivative within `[a, ∞)` equal
to `-iteratedTailIntegral f n x`. -/
theorem hasDerivWithinAt_iteratedTailIntegral_succ {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hcont : ContinuousWithinAt (iteratedTailIntegral f n) (Ici a) x) (hx : a ≤ x) :
    HasDerivWithinAt (iteratedTailIntegral f (n + 1)) (-iteratedTailIntegral f n x) (Ici a) x := by
  rcases hx.eq_or_lt with rfl | hlt
  · have hftc := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici a) (t := Ioi a)
      (hloc.intervalIntegrable fun _ ht ↦ (le_min le_rfl le_rfl).trans ht.1)
      (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
        (hloc.aestronglyMeasurable.mono_set Ioi_subset_Ici_self) self_mem_nhdsWithin)
      (hcont.mono Ioi_subset_Ici_self)
    exact (hftc.const_sub L).congr
      (fun _ hu ↦ iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc le_rfl hu hconv)
      (iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc le_rfl le_rfl hconv)
  · exact (hasDerivAt_iteratedTailIntegral_succ hloc hconv
      (hcont.continuousAt (Ici_mem_nhds hlt)) hlt).hasDerivWithinAt

/-- Higher iterated derivatives of `iteratedTailIntegral f n` at an interior point `x > a`:
when `f` is locally integrable on `[a, ∞)`, continuous at `x` if `k = n ≠ 0`, and the improper tail
integrals of orders `n - k ≤ m < n` converge at `a`,
`iteratedDeriv k (iteratedTailIntegral f n) x = (-1) ^ k • iteratedTailIntegral f (n - k) x` for
`k ≤ n`. -/
theorem iteratedDeriv_iteratedTailIntegral {f : ℝ → E} {n k : ℕ} {a x : ℝ}
    (hf_loc : LocallyIntegrableOn f (Ici a))
    (hcont : k = n → k ≠ 0 → ContinuousAt f x)
    (hconv : ∀ m, n - k ≤ m → m < n → ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hk : k ≤ n) (hx : a < x) :
    iteratedDeriv k (iteratedTailIntegral f n) x =
      (-1 : ℝ) ^ k • iteratedTailIntegral f (n - k) x := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel (by omega)).symm⟩
    obtain ⟨L, hL⟩ := hconv m (by omega) (Nat.lt_succ_self m)
    cases k with
    | zero =>
      have hcont_m : ContinuousAt (iteratedTailIntegral f m) x := by
        cases m with
        | zero => exact hcont rfl one_ne_zero
        | succ j => exact (continuousOn_iteratedTailIntegral_succ
            (locallyIntegrableOn_iteratedTailIntegral hf_loc j)).continuousAt (Ici_mem_nhds hx)
      rw [iteratedDeriv_one, deriv_iteratedTailIntegral_succ
        (locallyIntegrableOn_iteratedTailIntegral hf_loc m) hL hcont_m hx]
      simp
    | succ k' =>
      obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, (Nat.sub_add_cancel (by omega)).symm⟩
      have hcont_m : ContinuousOn (iteratedTailIntegral f (j + 1)) (Ici a) :=
        continuousOn_iteratedTailIntegral_succ (locallyIntegrableOn_iteratedTailIntegral hf_loc j)
      have hderiv_eq : deriv (iteratedTailIntegral f (j + 2)) =ᶠ[𝓝 x]
          fun u ↦ -iteratedTailIntegral f (j + 1) u := by
        filter_upwards [Ioi_mem_nhds hx] with u hu using
          deriv_iteratedTailIntegral_succ (hcont_m.locallyIntegrableOn measurableSet_Ici) hL
            (hcont_m.continuousAt (Ici_mem_nhds hu)) hu
      rw [iteratedDeriv_succ', hderiv_eq.iteratedDeriv_eq (k' + 1), iteratedDeriv_fun_neg,
        ih (fun heq _ ↦ hcont (by omega) (by omega))
          (fun r hr₁ hr₂ ↦ hconv r (by omega) (by omega)) (by omega)]
      simp [pow_succ]

end Complete

/-- Scalar multiplication commutes with `iteratedTailIntegral` on `[a, ∞)` when `f` is locally
integrable on `[a, ∞)` (for `n > 0`) and its improper tail integrals up to order `n` converge at
`a`. -/
theorem iteratedTailIntegral_const_smul {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E]
    [SMulCommClass ℝ R E] {f : ℝ → E} {n : ℕ} {a x : ℝ} (c : R)
    (hloc : 0 < n → LocallyIntegrableOn f (Ici a))
    (hconv : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral (fun t ↦ c • f t) n x = c • iteratedTailIntegral f n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hf_loc := hloc (Nat.succ_pos n)
    have hloc_n := locallyIntegrableOn_iteratedTailIntegral hf_loc n
    obtain ⟨L, hL⟩ := hconv n (Nat.lt_succ_self n)
    have htend := hloc_n.tendsto_intervalIntegral_sub le_rfl hx hL
    have hcongr : (fun R : ℝ ↦ ∫ t in x..R, iteratedTailIntegral (fun s ↦ c • f s) n t) =ᶠ[atTop]
        fun R ↦ c • ∫ t in x..R, iteratedTailIntegral f n t := by
      filter_upwards [eventually_ge_atTop x] with R hR
      rw [← (hloc_n.intervalIntegrable fun _ ht ↦
        (le_min hx (hx.trans hR)).trans ht.1).integral_smul c]
      refine intervalIntegral.integral_congr fun t ht ↦ ih (fun _ ↦ hf_loc)
        (fun m hm ↦ hconv m (Nat.lt_succ_of_lt hm)) (hx.trans ((uIcc_of_le hR ▸ ht).1))
    rw [iteratedTailIntegral_succ_eq_of_tendsto ((htend.const_smul c).congr' hcongr.symm),
      iteratedTailIntegral_succ_apply, htend.limUnder_eq]

/-- Negation commutes with `iteratedTailIntegral` on `[a, ∞)` when `f` is locally integrable on
`[a, ∞)` (for `n > 0`) and its improper tail integrals up to order `n` converge at `a`. -/
theorem iteratedTailIntegral_neg {f : ℝ → E} {n : ℕ} {a x : ℝ}
    (hloc : 0 < n → LocallyIntegrableOn f (Ici a))
    (hconv : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral (-f) n x = -iteratedTailIntegral f n x := by
  have hneg : (-f) = fun t ↦ (-1 : ℝ) • f t := by ext; simp
  rw [hneg, iteratedTailIntegral_const_smul (-1 : ℝ) hloc hconv hx, neg_one_smul]

/-- Addition commutes with `iteratedTailIntegral` on `[a, ∞)` when `f` and `g` are locally
integrable on `[a, ∞)` (for `n > 0`) and their improper tail integrals up to order `n` converge at
`a`. -/
theorem iteratedTailIntegral_add {f g : ℝ → E} {n : ℕ} {a x : ℝ}
    (hloc_f : 0 < n → LocallyIntegrableOn f (Ici a))
    (hconv_f : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hloc_g : 0 < n → LocallyIntegrableOn g (Ici a))
    (hconv_g : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral g m t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral (f + g) n x =
      iteratedTailIntegral f n x + iteratedTailIntegral g n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    have hf_loc := hloc_f (Nat.succ_pos n)
    have hg_loc := hloc_g (Nat.succ_pos n)
    have hloc_fn := locallyIntegrableOn_iteratedTailIntegral hf_loc n
    have hloc_gn := locallyIntegrableOn_iteratedTailIntegral hg_loc n
    obtain ⟨Lf, hLf⟩ := hconv_f n (Nat.lt_succ_self n)
    obtain ⟨Lg, hLg⟩ := hconv_g n (Nat.lt_succ_self n)
    have htf := hloc_fn.tendsto_intervalIntegral_sub le_rfl hx hLf
    have htg := hloc_gn.tendsto_intervalIntegral_sub le_rfl hx hLg
    have hcongr : (fun R : ℝ ↦ ∫ t in x..R, iteratedTailIntegral (f + g) n t) =ᶠ[atTop]
        fun R ↦ (∫ t in x..R, iteratedTailIntegral f n t) +
          ∫ t in x..R, iteratedTailIntegral g n t := by
      filter_upwards [eventually_ge_atTop x] with R hR
      rw [← intervalIntegral.integral_add
        (hloc_fn.intervalIntegrable fun _ ht ↦ (le_min hx (hx.trans hR)).trans ht.1)
        (hloc_gn.intervalIntegrable fun _ ht ↦ (le_min hx (hx.trans hR)).trans ht.1)]
      refine intervalIntegral.integral_congr fun t ht ↦ ih (fun _ ↦ hf_loc)
        (fun m hm ↦ hconv_f m (Nat.lt_succ_of_lt hm)) (fun _ ↦ hg_loc)
        (fun m hm ↦ hconv_g m (Nat.lt_succ_of_lt hm)) (hx.trans ((uIcc_of_le hR ▸ ht).1))
    rw [iteratedTailIntegral_succ_eq_of_tendsto ((htf.add htg).congr' hcongr.symm),
      iteratedTailIntegral_succ_apply, iteratedTailIntegral_succ_apply, htf.limUnder_eq,
      htg.limUnder_eq]

/-- Subtraction commutes with `iteratedTailIntegral` on `[a, ∞)` when `f` and `g` are locally
integrable on `[a, ∞)` (for `n > 0`) and their improper tail integrals up to order `n` converge at
`a`. -/
theorem iteratedTailIntegral_sub {f g : ℝ → E} {n : ℕ} {a x : ℝ}
    (hloc_f : 0 < n → LocallyIntegrableOn f (Ici a))
    (hconv_f : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hloc_g : 0 < n → LocallyIntegrableOn g (Ici a))
    (hconv_g : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral g m t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral (f - g) n x =
      iteratedTailIntegral f n x - iteratedTailIntegral g n x := by
  have hneg_eq {m : ℕ} (hm : m < n) {y : ℝ} (hy : a ≤ y) :
      iteratedTailIntegral (-g) m y = -iteratedTailIntegral g m y :=
    iteratedTailIntegral_neg (fun _ ↦ hloc_g (Nat.zero_lt_of_lt hm))
      (fun k hk ↦ hconv_g k (hk.trans hm)) hy
  have hconv_ng : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral (-g) m t) atTop (𝓝 L) := by
    intro m hm
    obtain ⟨L, hL⟩ := hconv_g m hm
    refine ⟨-L, hL.neg.congr' ?_⟩
    filter_upwards [eventually_ge_atTop a] with R hR
    rw [← intervalIntegral.integral_neg]
    exact intervalIntegral.integral_congr fun _ ht ↦ (hneg_eq hm ((uIcc_of_le hR ▸ ht).1)).symm
  rw [sub_eq_add_neg,
    iteratedTailIntegral_add hloc_f hconv_f (fun hn ↦ (hloc_g hn).neg) hconv_ng hx,
    iteratedTailIntegral_neg hloc_g hconv_g hx, ← sub_eq_add_neg]

/-- **Cauchy's repeated tail-integral formula.** If `t ↦ (t - x) ^ n • f t` is Bochner integrable
on `(x, ∞)`, then
`iteratedTailIntegral f (n + 1) x = (n !)⁻¹ • ∫ t in Ioi x, (t - x) ^ n • f t`. -/
theorem iteratedTailIntegral_succ_eq_inv_factorial_smul_integral_Ioi {f : ℝ → E} {x : ℝ} {n : ℕ}
    (hf_top : IntegrableOn (fun t : ℝ ↦ (t - x) ^ n • f t) (Ioi x)) :
    iteratedTailIntegral f (n + 1) x =
      (n.factorial : ℝ)⁻¹ • ∫ t in Ioi x, (t - x) ^ n • f t := by
  by_cases hE : CompleteSpace E
  swap
  · rw [iteratedTailIntegral_succ_of_not_completeSpace hE, integral_of_not_completeSpace hE,
      smul_zero]
  induction n generalizing x with
  | zero =>
    simp only [pow_zero, one_smul, Nat.factorial_zero, Nat.cast_one, inv_one] at hf_top ⊢
    exact iteratedTailIntegral_one_eq_integral_Ioi hf_top
  | succ m ih =>
    have hsub (s : ℝ) (hs : x < s) :
        IntegrableOn (fun t : ℝ ↦ (t - s) ^ m • f t) (Ioi s) := by
      have hf_meas : AEStronglyMeasurable f (volume.restrict (Ioi x)) := by
        refine (((by fun_prop : Measurable fun t : ℝ ↦ ((t - x) ^ (m + 1))⁻¹
          ).aestronglyMeasurable).smul hf_top.aestronglyMeasurable).congr ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : x < t)
        rw [Pi.smul_apply', smul_smul,
          inv_mul_cancel₀ (pow_ne_zero _ (sub_pos.mpr ht).ne'), one_smul]
      refine ((hf_top.mono_set (Ioi_subset_Ioi hs.le)).norm.const_mul ((s - x)⁻¹)).mono'
        (((by fun_prop : Continuous fun t : ℝ ↦ (t - s) ^ m).aestronglyMeasurable).smul
          (hf_meas.mono_set (Ioi_subset_Ioi hs.le))) ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : s < t)
      have htx : 0 < t - x := sub_pos.mpr (hs.trans ht)
      have hts : 0 < t - s := sub_pos.mpr ht
      have hsx : 0 < s - x := sub_pos.mpr hs
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg hts.le _),
        Real.norm_of_nonneg (pow_nonneg htx.le _), ← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      rw [inv_mul_eq_div, le_div_iff₀' hsx, pow_succ']
      exact mul_le_mul (by linarith) (pow_le_pow_left₀ hts.le (by linarith) m)
        (pow_nonneg hts.le _) htx.le
    have heq_on : EqOn (iteratedTailIntegral f (m + 1))
        (fun s ↦ (m.factorial : ℝ)⁻¹ • ∫ t in Ioi s, (t - s) ^ m • f t) (Ioi x) :=
      fun s hs ↦ ih (hsub s hs)
    have hint_swap := integrableOn_integral_Ioi_sub_pow_smul hf_top
    rw [iteratedTailIntegral_succ_eq_integral_Ioi
        (IntegrableOn.congr_fun (hint_swap.smul (m.factorial : ℝ)⁻¹) heq_on.symm
          measurableSet_Ioi),
      setIntegral_congr_fun measurableSet_Ioi heq_on, integral_smul,
      integral_Ioi_integral_Ioi_sub_pow_smul hf_top, smul_smul]
    congr 1
    simp [Nat.factorial_succ, mul_comm]

/-- Closed form of `iteratedTailIntegral` for a decaying exponential `t ↦ exp (-(a * t))` with
`0 < a`: `iteratedTailIntegral (fun t ↦ exp (-(a * t))) n x = exp (-(a * x)) / a ^ n`. -/
theorem iteratedTailIntegral_exp_neg_mul {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    iteratedTailIntegral (fun t : ℝ ↦ Real.exp (-(a * t))) n x = Real.exp (-(a * x)) / a ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hint : IntegrableOn (fun t : ℝ ↦ Real.exp (-(a * t)) / a ^ n) (Ioi x) :=
      IntegrableOn.congr_fun ((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) x).mul_const (a ^ n)⁻¹)
        (fun _ _ ↦ by rw [← neg_mul, div_eq_mul_inv]) measurableSet_Ioi
    rw [iteratedTailIntegral_succ_eq_integral_Ioi
        (hint.congr_fun (fun t _ ↦ (ih t).symm) measurableSet_Ioi),
      setIntegral_congr_fun measurableSet_Ioi (fun t _ ↦ ih t)]
    simp_rw [div_eq_mul_inv, ← neg_mul]
    rw [integral_mul_const, integral_exp_mul_Ioi (neg_lt_zero.mpr ha)]
    field_simp [ha.ne']; ring

end Basic

end TauCeti
