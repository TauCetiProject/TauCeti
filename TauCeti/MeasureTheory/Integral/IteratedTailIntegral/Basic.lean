/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.IntegralEqImproper
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Iterated improper tail integrals

For a normed-space-valued function `f : ℝ → E`, its sequence of repeated improper tail integrals
`TauCeti.iteratedTailIntegral` is defined recursively as a totalized limit by `I_0 = f` and
`I_{n + 1} x = lim_{R → ∞} ∫ t in x..R, I_n t` (via `Filter.limUnder` and `intervalIntegral`),
taking fallback values when convergence or local integrability fails or when `E` is incomplete.
Unlike iterated Bochner integrals over `Ioi x`, oscillatory functions locally integrable on `[x, ∞)`
(under the hypotheses in `TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Oscillatory` and
`CompleteSpace E`) admit genuine repeated conditional integration even when their amplitudes decay
too slowly for absolute integrability.

This file develops the general calculus of `TauCeti.iteratedTailIntegral`:

* Congruence on rays (`Ici a`, `Ioi a`, and `atTop`), vanishing on `0`, and right translation
  invariance.
* Basepoint splitting on `[a, ∞)`, vanishing at `+∞`, continuity on `[a, ∞)`, and local
  integrability of all higher iterates.
* Agreement with Bochner tail integrals on `(x, ∞)` when absolutely integrable.
* One- and two-sided differentiation (`I_{n + 1}' = -I_n`) and higher `iteratedDeriv` formulas.
* Linearity (`const_smul`, `neg`, `add`, `sub`).

Single-integral Cauchy representations and exponential evaluations live in
`TauCeti.MeasureTheory.Integral.IteratedTailIntegral.Evaluation`.

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
`iteratedTailIntegral f (n + 1) x` is the totalized improper integral
`lim_{R → ∞} ∫ t in x..R, iteratedTailIntegral f n t` defined via `Filter.limUnder atTop`.

Because both `Filter.limUnder` and `intervalIntegral` are totalized in Lean, three fallback
conventions apply when convergence, local integrability, or completeness fails:
1. If `R ↦ ∫ t in x..R, iteratedTailIntegral f n t` does not converge as `R → ∞`,
   `Filter.limUnder` returns the junk value `Classical.arbitrary E` (by
   `Filter.limUnder_of_not_tendsto`).
2. If `iteratedTailIntegral f n` is not locally integrable on `[x, ∞)`, Mathlib's
   `intervalIntegral.integral_undef` returns `0` for all sufficiently large `R`, so the truncated
   integrals collapse to `0` and `iteratedTailIntegral f (n + 1) x = 0`
   (`TauCeti.tendsto_intervalIntegral_zero_of_not_locallyIntegrableOn_Ici`).
3. If `E` is not complete (`¬ CompleteSpace E`), every Bochner integral collapses to `0`
   (`integral_of_not_completeSpace`), so `iteratedTailIntegral f (n + 1) x = 0`
   (`TauCeti.iteratedTailIntegral_succ_of_not_completeSpace`). -/
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
    iteratedTailIntegral f (n + 1) x = L := by
  rw [iteratedTailIntegral_succ_apply]
  exact h.limUnder_eq

/-- If the truncated integrals `∫ t in x..R, f t` tend to `L` as `R → ∞`, then
`iteratedTailIntegral f 1 x = L`. -/
theorem iteratedTailIntegral_one_eq_of_tendsto {f : ℝ → E} {x : ℝ} {L : E}
    (h : Tendsto (fun R : ℝ ↦ ∫ t in x..R, f t) atTop (𝓝 L)) :
    iteratedTailIntegral f 1 x = L :=
  iteratedTailIntegral_succ_eq_of_tendsto (n := 0)
    (by simpa only [iteratedTailIntegral_zero] using h)

@[simp]
theorem iteratedTailIntegral_zero_fun (n : ℕ) : iteratedTailIntegral (0 : ℝ → E) n = 0 := by
  induction n with
  | zero => exact iteratedTailIntegral_zero 0
  | succ n ih =>
    ext x
    exact iteratedTailIntegral_succ_eq_of_tendsto (by simp [ih])

theorem iteratedTailIntegral_zero_fun_apply (n : ℕ) (x : ℝ) :
    iteratedTailIntegral (0 : ℝ → E) n x = 0 := by simp

/-- In an incomplete normed space, every Bochner integral vanishes, so every positive-order
`iteratedTailIntegral` is identically `0`. -/
theorem iteratedTailIntegral_succ_of_not_completeSpace (hE : ¬ CompleteSpace E) (f : ℝ → E)
    (n : ℕ) (x : ℝ) : iteratedTailIntegral f (n + 1) x = 0 := by
  refine iteratedTailIntegral_succ_eq_of_tendsto ?_
  simp_rw [intervalIntegral, integral_of_not_completeSpace hE, sub_zero]
  exact tendsto_const_nhds

/-- Translating the argument of `f` by `c` translates every `iteratedTailIntegral` by `c`. -/
@[simp]
theorem iteratedTailIntegral_comp_add_right (f : ℝ → E) (c : ℝ) (n : ℕ) (x : ℝ) :
    iteratedTailIntegral (fun t ↦ f (t + c)) n x = iteratedTailIntegral f n (x + c) := by
  induction n generalizing x with
  | zero => simp only [iteratedTailIntegral_zero_apply]
  | succ n ih =>
    simp only [iteratedTailIntegral_succ_apply, ih, intervalIntegral.integral_comp_add_right]
    rw [limUnder, limUnder,
      ← Function.comp_def (fun R ↦ ∫ t in x + c..R, iteratedTailIntegral f n t) (· + c),
      ← Filter.map_map, Filter.map_add_atTop_eq]

/-- Two functions agreeing on `[a, ∞)` have identical `iteratedTailIntegral` on `[a, ∞)`. -/
theorem iteratedTailIntegral_congr_Ici {f g : ℝ → E} {a : ℝ} (h : EqOn f g (Ici a)) (n : ℕ) :
    EqOn (iteratedTailIntegral f n) (iteratedTailIntegral g n) (Ici a) := by
  induction n with
  | zero => simpa only [iteratedTailIntegral_zero] using h
  | succ n ih =>
    intro x (hx : a ≤ x)
    rw [iteratedTailIntegral_succ_apply, iteratedTailIntegral_succ_apply, limUnder, limUnder]
    congr 1
    refine Filter.map_congr ?_
    filter_upwards [eventually_ge_atTop x] with R hR
    exact intervalIntegral.integral_congr fun _ ht ↦
      ih (ordConnected_Ici.uIcc_subset hx (hx.trans hR) ht)

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

/-- If `iteratedTailIntegral f n` is locally integrable on `[a, ∞)` and its improper integral from
a basepoint `b ≥ a` converges to `L`, then `iteratedTailIntegral f (n + 1) x` for `x ≥ a` is
obtained from `L` by subtracting the finite integral over `b..x`. -/
theorem iteratedTailIntegral_succ_eq_sub_intervalIntegral {f : ℝ → E} {n : ℕ} {a b x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a)) (hb : a ≤ b) (hx : a ≤ x)
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in b..R, iteratedTailIntegral f n t) atTop (𝓝 L)) :
    iteratedTailIntegral f (n + 1) x = L - ∫ t in b..x, iteratedTailIntegral f n t :=
  iteratedTailIntegral_succ_eq_of_tendsto (hloc.tendsto_intervalIntegral_sub hb hx hconv)

/-- If `iteratedTailIntegral f n` is locally integrable on `[a, ∞)` and its improper integral from
a basepoint `b ≥ a` converges to `L`, then subtracting `iteratedTailIntegral f (n + 1) y` from
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
      (hloc.intervalIntegrable (ordConnected_Ici.uIcc_subset hb hx))
      (hloc.intervalIntegrable (ordConnected_Ici.uIcc_subset hx hy)),
    add_sub_cancel_left]

/-- If `f` is locally integrable on `[a, ∞)` and its improper integral from a basepoint `b ≥ a`
converges to `L`, then subtracting `iteratedTailIntegral f 1 y` from `iteratedTailIntegral f 1 x`
recovers `∫ t in x..y, f t` for any `x, y ≥ a`. -/
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
      (hloc.intervalIntegrable (ordConnected_Ici.uIcc_subset le_rfl (by linarith : a ≤ x + 1)))
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
  iteratedTailIntegral_succ_eq_of_tendsto (intervalIntegral_tendsto_integral_Ioi x hint tendsto_id)

/-- When `f` is Bochner integrable on `(x, ∞)`, `iteratedTailIntegral f 1 x` equals the Bochner
tail integral `∫ t in Ioi x, f t`. -/
theorem iteratedTailIntegral_one_eq_integral_Ioi {f : ℝ → E} {x : ℝ}
    (hint : IntegrableOn f (Ioi x)) :
    iteratedTailIntegral f 1 x = ∫ t in Ioi x, f t :=
  iteratedTailIntegral_succ_eq_integral_Ioi (n := 0) hint

section Complete

variable [CompleteSpace E]

/-- When `iteratedTailIntegral f n` is locally integrable on `[a, ∞)`, its improper integral from
`a` converges (`Tendsto (fun R ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L)`), and
`iteratedTailIntegral f n` is continuous at an interior point `x > a`, the next tail integral
`iteratedTailIntegral f (n + 1)` has strict derivative `-iteratedTailIntegral f n x` at `x`. -/
theorem hasStrictDerivAt_iteratedTailIntegral_succ {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hcont : ContinuousAt (iteratedTailIntegral f n) x) (hx : a < x) :
    HasStrictDerivAt (iteratedTailIntegral f (n + 1)) (-iteratedTailIntegral f n x) x := by
  have hftc := intervalIntegral.integral_hasStrictDerivAt_right
    (hloc.intervalIntegrable (ordConnected_Ici.uIcc_subset le_rfl hx.le))
    (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hloc.aestronglyMeasurable
      (Ici_mem_nhds hx)) hcont
  refine (hftc.const_sub L).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with _ hu using
    (iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc le_rfl hu.le hconv).symm

/-- Under the same local integrability on `[a, ∞)` and convergence from `a` hypotheses as
`hasStrictDerivAt_iteratedTailIntegral_succ`, at an interior point `x > a` where
`iteratedTailIntegral f n` is continuous, the next tail integral `iteratedTailIntegral f (n + 1)`
has derivative `-iteratedTailIntegral f n x`. -/
theorem hasDerivAt_iteratedTailIntegral_succ {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hcont : ContinuousAt (iteratedTailIntegral f n) x) (hx : a < x) :
    HasDerivAt (iteratedTailIntegral f (n + 1)) (-iteratedTailIntegral f n x) x :=
  (hasStrictDerivAt_iteratedTailIntegral_succ hloc hconv hcont hx).hasDerivAt

/-- Under the same local integrability on `[a, ∞)` and convergence from `a` hypotheses as
`hasStrictDerivAt_iteratedTailIntegral_succ`,
`deriv (iteratedTailIntegral f (n + 1)) x = -iteratedTailIntegral f n x` at an interior continuity
point `x > a`. -/
theorem deriv_iteratedTailIntegral_succ {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hcont : ContinuousAt (iteratedTailIntegral f n) x) (hx : a < x) :
    deriv (iteratedTailIntegral f (n + 1)) x = -iteratedTailIntegral f n x :=
  (hasDerivAt_iteratedTailIntegral_succ hloc hconv hcont hx).deriv

/-- When `iteratedTailIntegral f n` is locally integrable on `[a, ∞)`, its improper integral from
`a` converges (`Tendsto (fun R ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L)`), and
`iteratedTailIntegral f n` is continuous within `[a, ∞)` at `x ≥ a` (including at the endpoint
`x = a`), `iteratedTailIntegral f (n + 1)` has derivative within `[a, ∞)` equal to
`-iteratedTailIntegral f n x`. -/
theorem hasDerivWithinAt_iteratedTailIntegral_succ {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hcont : ContinuousWithinAt (iteratedTailIntegral f n) (Ici a) x) (hx : a ≤ x) :
    HasDerivWithinAt (iteratedTailIntegral f (n + 1)) (-iteratedTailIntegral f n x) (Ici a) x := by
  rcases hx.eq_or_lt with rfl | hlt
  · have hftc := intervalIntegral.integral_hasDerivWithinAt_right (s := Ici a) (t := Ioi a)
      (hloc.intervalIntegrable (ordConnected_Ici.uIcc_subset le_rfl le_rfl))
      (AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
        (hloc.aestronglyMeasurable.mono_set Ioi_subset_Ici_self) self_mem_nhdsWithin)
      (hcont.mono Ioi_subset_Ici_self)
    exact (hftc.const_sub L).congr
      (fun _ hu ↦ iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc le_rfl hu hconv)
      (iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc le_rfl le_rfl hconv)
  · exact (hasDerivAt_iteratedTailIntegral_succ hloc hconv
      (hcont.continuousAt (Ici_mem_nhds hlt)) hlt).hasDerivWithinAt

/-- Higher iterated derivatives of `iteratedTailIntegral f n` at an interior point `x > a`:
when `f` is locally integrable on `[a, ∞)`, continuous at `x` if `k = n ≠ 0`, and the truncated
integrals of `iteratedTailIntegral f m` converge at `a` for `n - k ≤ m < n` (equivalently, the
improper tail integrals of orders `m + 1` converge at `a`),
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
integrable on `[a, ∞)` (for `n > 0`) and the truncated integrals of `iteratedTailIntegral f m`
for `m < n` (equivalently, the tail integrals of orders `1 ≤ m + 1 ≤ n`) converge at `a`. -/
theorem iteratedTailIntegral_const_smul {R : Type*} [NormedRing R] [Module R E] [IsBoundedSMul R E]
    [SMulCommClass ℝ R E] {f : ℝ → E} {n : ℕ} {a x : ℝ} (c : R)
    (hloc : 0 < n → LocallyIntegrableOn f (Ici a))
    (hconv : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral (fun t ↦ c • f t) n x = c • iteratedTailIntegral f n x := by
  induction n generalizing x with
  | zero => simp only [iteratedTailIntegral_zero_apply]
  | succ n ih =>
    have hf_loc := hloc (Nat.succ_pos n)
    have hloc_n := locallyIntegrableOn_iteratedTailIntegral hf_loc n
    obtain ⟨L, hL⟩ := hconv n (Nat.lt_succ_self n)
    have htend := hloc_n.tendsto_intervalIntegral_sub le_rfl hx hL
    have hcongr : (fun R : ℝ ↦ ∫ t in x..R, iteratedTailIntegral (fun s ↦ c • f s) n t) =ᶠ[atTop]
        fun R ↦ c • ∫ t in x..R, iteratedTailIntegral f n t := by
      filter_upwards [eventually_ge_atTop x] with R hR
      rw [← (hloc_n.intervalIntegrable
        (ordConnected_Ici.uIcc_subset hx (hx.trans hR))).integral_smul c]
      refine intervalIntegral.integral_congr fun t ht ↦ ih (fun _ ↦ hf_loc)
        (fun m hm ↦ hconv m (Nat.lt_succ_of_lt hm))
        (ordConnected_Ici.uIcc_subset hx (hx.trans hR) ht)
    rw [iteratedTailIntegral_succ_eq_of_tendsto ((htend.const_smul c).congr' hcongr.symm),
      iteratedTailIntegral_succ_eq_of_tendsto htend]

/-- Negation commutes with `iteratedTailIntegral` on `[a, ∞)` when `f` is locally integrable on
`[a, ∞)` (for `n > 0`) and the truncated integrals of `iteratedTailIntegral f m` for `m < n`
converge at `a`. -/
theorem iteratedTailIntegral_neg {f : ℝ → E} {n : ℕ} {a x : ℝ}
    (hloc : 0 < n → LocallyIntegrableOn f (Ici a))
    (hconv : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral (-f) n x = -iteratedTailIntegral f n x := by
  have hneg : (-f) = fun t ↦ (-1 : ℝ) • f t := by ext; simp
  rw [hneg, iteratedTailIntegral_const_smul (-1 : ℝ) hloc hconv hx, neg_one_smul]

/-- Addition commutes with `iteratedTailIntegral` on `[a, ∞)` when `f` and `g` are locally
integrable on `[a, ∞)` (for `n > 0`) and the truncated integrals of `iteratedTailIntegral f m`
and `iteratedTailIntegral g m` for `m < n` converge at `a`. -/
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
  | zero => simp only [iteratedTailIntegral_zero_apply, Pi.add_apply]
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
        (hloc_fn.intervalIntegrable (ordConnected_Ici.uIcc_subset hx (hx.trans hR)))
        (hloc_gn.intervalIntegrable (ordConnected_Ici.uIcc_subset hx (hx.trans hR)))]
      refine intervalIntegral.integral_congr fun t ht ↦ ih (fun _ ↦ hf_loc)
        (fun m hm ↦ hconv_f m (Nat.lt_succ_of_lt hm)) (fun _ ↦ hg_loc)
        (fun m hm ↦ hconv_g m (Nat.lt_succ_of_lt hm))
        (ordConnected_Ici.uIcc_subset hx (hx.trans hR) ht)
    rw [iteratedTailIntegral_succ_eq_of_tendsto ((htf.add htg).congr' hcongr.symm),
      iteratedTailIntegral_succ_eq_of_tendsto htf, iteratedTailIntegral_succ_eq_of_tendsto htg]

/-- Subtraction commutes with `iteratedTailIntegral` on `[a, ∞)` when `f` and `g` are locally
integrable on `[a, ∞)` (for `n > 0`) and the truncated integrals of `iteratedTailIntegral f m`
and `iteratedTailIntegral g m` for `m < n` converge at `a`. -/
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
    exact intervalIntegral.integral_congr fun _ ht ↦
      (hneg_eq hm (ordConnected_Ici.uIcc_subset le_rfl hR ht)).symm
  rw [sub_eq_add_neg,
    iteratedTailIntegral_add hloc_f hconv_f (fun hn ↦ (hloc_g hn).neg) hconv_ng hx,
    iteratedTailIntegral_neg hloc_g hconv_g hx, ← sub_eq_add_neg]

end Basic

end TauCeti
