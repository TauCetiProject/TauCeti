/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Iterated improper tail integrals

For a normed-space-valued function `f : ℝ → E`, its sequence of repeated improper tail integrals
is defined recursively by `I_0 = f` and
`I_{n + 1} x = lim_{R → ∞} ∫ t in x..R, I_n t` (`TauCeti.iteratedTailIntegral`). Unlike iterated
Bochner integrals over `Ioi x`, these improper integrals converge for conditionally integrable
oscillatory functions whose amplitude decays too slowly for absolute integrability.

This file develops the general calculus of `TauCeti.iteratedTailIntegral`:

* Basepoint splitting on `[a, ∞)`, vanishing at `+∞`, and continuity on `[a, ∞)`.
* Agreement with Bochner tail integrals on `(x, ∞)` when absolutely integrable.
* One- and two-sided differentiation (`I_{n + 1}' = -I_n`) and higher `iteratedDeriv` formulas.
* Linearity (`const_smul`, `neg`, `add`, `sub`) and right translation invariance.
* Cauchy's single-integral representation
  `I_{n + 1} x = (n !)⁻¹ • ∫ t in Ioi x, (t - x) ^ n • f t` when the weighted tail is Bochner
  integrable, together with the closed form for decaying exponentials.

## Main declarations

* `TauCeti.iteratedTailIntegral`: repeated improper tail integrals `I_n` of `f : ℝ → E`.
* `TauCeti.continuousOn_iteratedTailIntegral_succ`,
  `TauCeti.tendsto_iteratedTailIntegral_succ_atTop`: continuity on `[a, ∞)` and vanishing at `+∞`.
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
theorem iteratedTailIntegral_zero (f : ℝ → E) (x : ℝ) :
    iteratedTailIntegral f 0 x = f x := by rfl

@[simp]
theorem iteratedTailIntegral_zero_eq (f : ℝ → E) :
    iteratedTailIntegral f 0 = f := by rfl

theorem iteratedTailIntegral_succ (f : ℝ → E) (n : ℕ) (x : ℝ) :
    iteratedTailIntegral f (n + 1) x =
      limUnder atTop fun R : ℝ ↦ ∫ t in x..R, iteratedTailIntegral f n t := by rfl

theorem iteratedTailIntegral_one (f : ℝ → E) (x : ℝ) :
    iteratedTailIntegral f 1 x = limUnder atTop fun R : ℝ ↦ ∫ t in x..R, f t := by rfl

/-- Semigroup law for `iteratedTailIntegral`: taking `m + n` repeated tail integrals is taking `m`
repeated tail integrals of `iteratedTailIntegral f n`. -/
theorem iteratedTailIntegral_add_right (f : ℝ → E) (m n : ℕ) :
    iteratedTailIntegral f (m + n) = iteratedTailIntegral (iteratedTailIntegral f n) m := by
  induction m with
  | zero => simp
  | succ m ih =>
    ext x
    simp [Nat.succ_add, iteratedTailIntegral_succ, ih]

theorem iteratedTailIntegral_succ_eq_one (f : ℝ → E) (n : ℕ) :
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

@[simp]
theorem iteratedTailIntegral_zero_fun (n : ℕ) (x : ℝ) :
    iteratedTailIntegral (0 : ℝ → E) n x = 0 := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [iteratedTailIntegral_succ]
    simp_rw [ih, intervalIntegral.integral_zero]
    exact tendsto_const_nhds.limUnder_eq

/-- Translating the argument of `f` by `c` translates every `iteratedTailIntegral` by `c`. -/
theorem iteratedTailIntegral_comp_add_right (f : ℝ → E) (c : ℝ) (n : ℕ) (x : ℝ) :
    iteratedTailIntegral (fun t ↦ f (t + c)) n x = iteratedTailIntegral f n (x + c) := by
  have hmap : Filter.map (fun R : ℝ ↦ R + c) atTop = atTop := by
    ext s
    simp only [mem_map, mem_atTop_sets]
    exact ⟨fun ⟨a, ha⟩ ↦ ⟨a + c, fun b hb ↦ by simpa [mem_preimage] using ha (b - c) (by linarith)⟩,
      fun ⟨a, ha⟩ ↦ ⟨a - c, fun b hb ↦ ha (b + c) (by linarith)⟩⟩
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [iteratedTailIntegral_succ, ih, intervalIntegral.integral_comp_add_right]
    rw [limUnder, limUnder, show (fun R ↦ ∫ t in x + c..R + c, iteratedTailIntegral f n t) =
      (fun R ↦ ∫ t in x + c..R, iteratedTailIntegral f n t) ∘ (fun R ↦ R + c) from rfl,
      ← Filter.map_map, hmap]

omit [NormedSpace ℝ E] in
/-- If `g` is locally integrable on `[a, ∞)`, it is interval integrable between any two points of
`[a, ∞)`. -/
private theorem intervalIntegrable_of_locallyIntegrableOn_Ici {g : ℝ → E} {a x y : ℝ}
    (hg : LocallyIntegrableOn g (Ici a)) (hx : a ≤ x) (hy : a ≤ y) :
    IntervalIntegrable g volume x y := by
  refine (hg.integrableOn_compact_subset ?_ isCompact_uIcc).intervalIntegrable
  intro t ht
  rcases le_total x y with hxy | hyx
  · rw [uIcc_of_le hxy] at ht
    exact hx.trans ht.1
  · rw [uIcc_of_ge hyx] at ht
    exact hy.trans ht.1

/-- **Basepoint splitting for improper tail integrals.** If `iteratedTailIntegral f n` is locally
integrable on `[a, ∞)` and its improper integral from `a` converges to `L`, then for every `x ≥ a`
its improper integral from `x` converges to `L - ∫ t in a..x, iteratedTailIntegral f n t`. -/
theorem tendsto_intervalIntegral_iteratedTailIntegral_of_ge {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hx : a ≤ x) :
    Tendsto (fun R : ℝ ↦ ∫ t in x..R, iteratedTailIntegral f n t) atTop
      (𝓝 (L - ∫ t in a..x, iteratedTailIntegral f n t)) := by
  refine (hconv.sub_const (∫ t in a..x, iteratedTailIntegral f n t)).congr' ?_
  filter_upwards [eventually_ge_atTop x] with R hR
  have h1 := intervalIntegrable_of_locallyIntegrableOn_Ici hloc le_rfl hx
  have h2 := intervalIntegrable_of_locallyIntegrableOn_Ici hloc hx (hx.trans hR)
  rw [← intervalIntegral.integral_add_adjacent_intervals h1 h2, add_sub_cancel_left]

/-- Under convergence from a basepoint `a`, `iteratedTailIntegral f (n + 1) x` on `[a, ∞)` is
obtained from `L = iteratedTailIntegral f (n + 1) a` by subtracting the finite integral over
`a..x`. -/
theorem iteratedTailIntegral_succ_eq_sub_intervalIntegral {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral f (n + 1) x = L - ∫ t in a..x, iteratedTailIntegral f n t :=
  (tendsto_intervalIntegral_iteratedTailIntegral_of_ge hloc hconv hx).limUnder_eq

/-- Under convergence from `a`, subtracting `iteratedTailIntegral f (n + 1) x` from
`iteratedTailIntegral f (n + 1) a` recovers `∫ t in a..x, iteratedTailIntegral f n t`. -/
theorem iteratedTailIntegral_succ_sub_eq_intervalIntegral {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral f (n + 1) a - iteratedTailIntegral f (n + 1) x =
      ∫ t in a..x, iteratedTailIntegral f n t := by
  rw [iteratedTailIntegral_succ_eq_of_tendsto hconv,
    iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc hconv hx, sub_sub_cancel]

/-- Every convergent improper tail integral `iteratedTailIntegral f (n + 1)` vanishes at `+∞`. -/
theorem tendsto_iteratedTailIntegral_succ_atTop {f : ℝ → E} {n : ℕ} {a : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L)) :
    Tendsto (iteratedTailIntegral f (n + 1)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun x : ℝ ↦ L - ∫ t in a..x, iteratedTailIntegral f n t) atTop (𝓝 0) := by
    simpa [sub_self] using (tendsto_const_nhds (x := L)).sub hconv
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop a] with x hx
  exact (iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc hconv hx).symm

/-- If `iteratedTailIntegral f n` is locally integrable on `[a, ∞)` and its improper integral from
`a` converges, then `iteratedTailIntegral f (n + 1)` is continuous on `[a, ∞)`. -/
theorem continuousOn_iteratedTailIntegral_succ {f : ℝ → E} {n : ℕ} {a : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L)) :
    ContinuousOn (iteratedTailIntegral f (n + 1)) (Ici a) := by
  have heq : EqOn (iteratedTailIntegral f (n + 1))
      (fun x : ℝ ↦ L - ∫ t in a..x, iteratedTailIntegral f n t) (Ici a) :=
    fun x hx ↦ iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc hconv hx
  refine ContinuousOn.congr ?_ heq
  refine continuousOn_const.sub fun x (hx : a ≤ x) ↦ ?_
  have hint : IntervalIntegrable (iteratedTailIntegral f n) volume a (x + 1) :=
    intervalIntegrable_of_locallyIntegrableOn_Ici hloc le_rfl (by linarith)
  have hprim : ContinuousOn (fun u ↦ ∫ t in a..u, iteratedTailIntegral f n t) [[a, x + 1]] :=
    intervalIntegral.continuousOn_primitive_interval' hint left_mem_uIcc
  rw [uIcc_of_le (by linarith : a ≤ x + 1)] at hprim
  have hmem : Icc a (x + 1) ∈ 𝓝[Ici a] x := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (lt_add_one x))] with y hy1 hy2
    exact ⟨hy1, hy2.le⟩
  exact (hprim x ⟨hx, by linarith⟩).mono_of_mem_nhdsWithin hmem

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
    iteratedTailIntegral f 1 x = ∫ t in Ioi x, f t := by
  simpa using iteratedTailIntegral_succ_eq_integral_Ioi (f := f) (n := 0) (by simpa using hint)

section Complete

variable [CompleteSpace E]

/-- At an interior point `x > a` where `iteratedTailIntegral f n` is continuous, the next tail
integral `iteratedTailIntegral f (n + 1)` has strict derivative `-iteratedTailIntegral f n x`. -/
theorem hasStrictDerivAt_iteratedTailIntegral_succ {f : ℝ → E} {n : ℕ} {a x : ℝ} {L : E}
    (hloc : LocallyIntegrableOn (iteratedTailIntegral f n) (Ici a))
    (hconv : Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f n t) atTop (𝓝 L))
    (hcont : ContinuousAt (iteratedTailIntegral f n) x) (hx : a < x) :
    HasStrictDerivAt (iteratedTailIntegral f (n + 1)) (-iteratedTailIntegral f n x) x := by
  have hint : IntervalIntegrable (iteratedTailIntegral f n) volume a x :=
    intervalIntegrable_of_locallyIntegrableOn_Ici hloc le_rfl hx.le
  have hmeas : StronglyMeasurableAtFilter (iteratedTailIntegral f n) (𝓝 x) :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hloc.aestronglyMeasurable
      (Ici_mem_nhds hx)
  have hftc : HasStrictDerivAt (fun u ↦ ∫ t in a..u, iteratedTailIntegral f n t)
      (iteratedTailIntegral f n x) x :=
    intervalIntegral.integral_hasStrictDerivAt_right hint hmeas hcont
  refine (hftc.const_sub L).congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hx] with u hu
  exact (iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc hconv hu.le).symm

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
  have hint : IntervalIntegrable (iteratedTailIntegral f n) volume a x :=
    intervalIntegrable_of_locallyIntegrableOn_Ici hloc le_rfl hx
  have hmeas : StronglyMeasurableAtFilter (iteratedTailIntegral f n) (𝓝[>] x) :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      (hloc.aestronglyMeasurable.mono_set (Ioi_subset_Ici hx)) self_mem_nhdsWithin
  have hftc : HasDerivWithinAt (fun u ↦ ∫ t in a..u, iteratedTailIntegral f n t)
      (iteratedTailIntegral f n x) (Ici x) x :=
    intervalIntegral.integral_hasDerivWithinAt_right hint
      (s := Ici x) (t := Ioi x) hmeas (hcont.mono (Ioi_subset_Ici hx))
  rcases hx.eq_or_lt with rfl | hlt
  · refine (hftc.const_sub L).congr
      (fun u hu ↦ iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc hconv hu)
      (iteratedTailIntegral_succ_eq_sub_intervalIntegral hloc hconv le_rfl)
  · have hca : ContinuousAt (iteratedTailIntegral f n) x :=
      hcont.continuousAt (Ici_mem_nhds hlt)
    exact (hasDerivAt_iteratedTailIntegral_succ hloc hconv hca hlt).hasDerivWithinAt

/-- Higher iterated derivatives of `iteratedTailIntegral f n` at an interior point `x > a`:
when `f` is continuous on `[a, ∞)` and the improper tail integrals up to order `n` converge at `a`,
`iteratedDeriv k (iteratedTailIntegral f n) x = (-1) ^ k • iteratedTailIntegral f (n - k) x` for
`k ≤ n`. -/
theorem iteratedDeriv_iteratedTailIntegral {f : ℝ → E} {n k : ℕ} {a x : ℝ}
    (hf_cont : ContinuousOn f (Ici a))
    (hconv : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hk : k ≤ n) (hx : a < x) :
    iteratedDeriv k (iteratedTailIntegral f n) x =
      (-1 : ℝ) ^ k • iteratedTailIntegral f (n - k) x := by
  induction k generalizing n with
  | zero => simp
  | succ k ih =>
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, (Nat.sub_add_cancel (by omega)).symm⟩
    have hcont_m : ContinuousOn (iteratedTailIntegral f m) (Ici a) := by
      clear ih hk
      induction m with
      | zero => exact hf_cont
      | succ j ihj =>
        obtain ⟨L, hL⟩ := hconv j (by omega)
        exact continuousOn_iteratedTailIntegral_succ
          ((ihj (fun i hi ↦ hconv i (by omega))).locallyIntegrableOn measurableSet_Ici) hL
    obtain ⟨L, hL⟩ := hconv m (Nat.lt_succ_self m)
    have hloc_m : LocallyIntegrableOn (iteratedTailIntegral f m) (Ici a) :=
      hcont_m.locallyIntegrableOn measurableSet_Ici
    have hderiv_eq : deriv (iteratedTailIntegral f (m + 1)) =ᶠ[𝓝 x]
        fun u ↦ -iteratedTailIntegral f m u := by
      filter_upwards [Ioi_mem_nhds hx] with u hu
      exact deriv_iteratedTailIntegral_succ hloc_m hL
        (hcont_m.continuousAt (Ici_mem_nhds hu)) hu
    rw [iteratedDeriv_succ', hderiv_eq.iteratedDeriv_eq k, iteratedDeriv_fun_neg,
      ih (fun j hj ↦ hconv j (Nat.lt_succ_of_lt hj)) (by omega),
      Nat.succ_sub_succ_eq_sub, pow_succ, mul_smul, neg_one_smul, smul_neg]

end Complete

/-- Scalar multiplication commutes with `iteratedTailIntegral` on `[a, ∞)` when the improper tail
integrals of `f` up to order `n` converge at `a` and are locally integrable on `[a, ∞)`. -/
theorem iteratedTailIntegral_const_smul {f : ℝ → E} {n : ℕ} {a x : ℝ} (c : ℝ)
    (hloc : ∀ m < n, LocallyIntegrableOn (iteratedTailIntegral f m) (Ici a))
    (hconv : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral (fun t ↦ c • f t) n x = c • iteratedTailIntegral f n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    obtain ⟨L, hL⟩ := hconv n (Nat.lt_succ_self n)
    have hln := hloc n (Nat.lt_succ_self n)
    have htend := tendsto_intervalIntegral_iteratedTailIntegral_of_ge hln hL hx
    have hcongr : (fun R : ℝ ↦ ∫ t in x..R, iteratedTailIntegral (fun s ↦ c • f s) n t) =ᶠ[atTop]
        fun R ↦ c • ∫ t in x..R, iteratedTailIntegral f n t := by
      filter_upwards [eventually_ge_atTop x] with R hR
      rw [← intervalIntegral.integral_smul]
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le hR] at ht
      exact ih (fun m hm ↦ hloc m (Nat.lt_succ_of_lt hm))
        (fun m hm ↦ hconv m (Nat.lt_succ_of_lt hm)) (hx.trans ht.1)
    rw [iteratedTailIntegral_succ_eq_of_tendsto ((htend.const_smul c).congr' hcongr.symm),
      iteratedTailIntegral_succ, htend.limUnder_eq]

/-- Negation commutes with `iteratedTailIntegral` on `[a, ∞)` under convergence of the improper
tail integrals of `f` up to order `n` at `a`. -/
theorem iteratedTailIntegral_neg {f : ℝ → E} {n : ℕ} {a x : ℝ}
    (hloc : ∀ m < n, LocallyIntegrableOn (iteratedTailIntegral f m) (Ici a))
    (hconv : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral (-f) n x = -iteratedTailIntegral f n x := by
  have hneg : (-f) = fun t ↦ (-1 : ℝ) • f t := by ext; simp
  rw [hneg, iteratedTailIntegral_const_smul (-1 : ℝ) hloc hconv hx, neg_one_smul]

/-- Addition commutes with `iteratedTailIntegral` on `[a, ∞)` when the improper tail integrals of
both `f` and `g` up to order `n` converge at `a` and are locally integrable on `[a, ∞)`. -/
theorem iteratedTailIntegral_add {f g : ℝ → E} {n : ℕ} {a x : ℝ}
    (hloc_f : ∀ m < n, LocallyIntegrableOn (iteratedTailIntegral f m) (Ici a))
    (hconv_f : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hloc_g : ∀ m < n, LocallyIntegrableOn (iteratedTailIntegral g m) (Ici a))
    (hconv_g : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral g m t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral (f + g) n x =
      iteratedTailIntegral f n x + iteratedTailIntegral g n x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    obtain ⟨Lf, hLf⟩ := hconv_f n (Nat.lt_succ_self n)
    obtain ⟨Lg, hLg⟩ := hconv_g n (Nat.lt_succ_self n)
    have htf := tendsto_intervalIntegral_iteratedTailIntegral_of_ge
      (hloc_f n (Nat.lt_succ_self n)) hLf hx
    have htg := tendsto_intervalIntegral_iteratedTailIntegral_of_ge
      (hloc_g n (Nat.lt_succ_self n)) hLg hx
    have hcongr : (fun R : ℝ ↦ ∫ t in x..R, iteratedTailIntegral (f + g) n t) =ᶠ[atTop]
        fun R ↦ (∫ t in x..R, iteratedTailIntegral f n t) +
          ∫ t in x..R, iteratedTailIntegral g n t := by
      filter_upwards [eventually_ge_atTop x] with R hR
      have hif := intervalIntegrable_of_locallyIntegrableOn_Ici
        (hloc_f n (Nat.lt_succ_self n)) hx (hx.trans hR)
      have hig := intervalIntegrable_of_locallyIntegrableOn_Ici
        (hloc_g n (Nat.lt_succ_self n)) hx (hx.trans hR)
      rw [← intervalIntegral.integral_add hif hig]
      refine intervalIntegral.integral_congr fun t ht ↦ ?_
      rw [uIcc_of_le hR] at ht
      exact ih (fun m hm ↦ hloc_f m (Nat.lt_succ_of_lt hm))
        (fun m hm ↦ hconv_f m (Nat.lt_succ_of_lt hm))
        (fun m hm ↦ hloc_g m (Nat.lt_succ_of_lt hm))
        (fun m hm ↦ hconv_g m (Nat.lt_succ_of_lt hm)) (hx.trans ht.1)
    rw [iteratedTailIntegral_succ_eq_of_tendsto ((htf.add htg).congr' hcongr.symm),
      iteratedTailIntegral_succ, iteratedTailIntegral_succ, htf.limUnder_eq, htg.limUnder_eq]

/-- Subtraction commutes with `iteratedTailIntegral` on `[a, ∞)` under convergence of the improper
tail integrals of `f` and `g` up to order `n` at `a`. -/
theorem iteratedTailIntegral_sub {f g : ℝ → E} {n : ℕ} {a x : ℝ}
    (hloc_f : ∀ m < n, LocallyIntegrableOn (iteratedTailIntegral f m) (Ici a))
    (hconv_f : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral f m t) atTop (𝓝 L))
    (hloc_g : ∀ m < n, LocallyIntegrableOn (iteratedTailIntegral g m) (Ici a))
    (hconv_g : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral g m t) atTop (𝓝 L))
    (hx : a ≤ x) :
    iteratedTailIntegral (f - g) n x =
      iteratedTailIntegral f n x - iteratedTailIntegral g n x := by
  have hloc_ng : ∀ m < n, LocallyIntegrableOn (iteratedTailIntegral (-g) m) (Ici a) := by
    intro m hm
    refine (hloc_g m hm).neg.congr (ae_restrict_of_forall_mem measurableSet_Ici fun y hy ↦ ?_)
    exact (iteratedTailIntegral_neg (fun k hk ↦ hloc_g k (hk.trans hm))
      (fun k hk ↦ hconv_g k (hk.trans hm)) hy).symm
  have hconv_ng : ∀ m < n, ∃ L,
      Tendsto (fun R : ℝ ↦ ∫ t in a..R, iteratedTailIntegral (-g) m t) atTop (𝓝 L) := by
    intro m hm
    obtain ⟨L, hL⟩ := hconv_g m hm
    refine ⟨-L, hL.neg.congr' ?_⟩
    filter_upwards [eventually_ge_atTop a] with R hR
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le hR] at ht
    exact (iteratedTailIntegral_neg (fun k hk ↦ hloc_g k (hk.trans hm))
      (fun k hk ↦ hconv_g k (hk.trans hm)) ht.1).symm
  rw [sub_eq_add_neg, iteratedTailIntegral_add hloc_f hconv_f hloc_ng hconv_ng hx,
    iteratedTailIntegral_neg hloc_g hconv_g hx, ← sub_eq_add_neg]

/-- Local integrability on `[a, ∞)` together with integrability of `(t - a) ^ n • f t` on `(a, ∞)`
implies integrability of `(t - y) ^ k • f t` on `(y, ∞)` for every `y ≥ a` and `k ≤ n`. -/
private theorem integrableOn_sub_pow_smul_of_le {f : ℝ → E} {a y : ℝ} {k n : ℕ}
    (hf_loc : LocallyIntegrableOn f (Ici a))
    (hf_top : IntegrableOn (fun t : ℝ ↦ (t - a) ^ n • f t) (Ioi a))
    (hy : a ≤ y) (hk : k ≤ n) :
    IntegrableOn (fun t : ℝ ↦ (t - y) ^ k • f t) (Ioi y) := by
  rw [← Ioc_union_Ioi_eq_Ioi (le_add_of_nonneg_right zero_le_one)]
  refine IntegrableOn.union ?_ ?_
  · exact ((hf_loc.integrableOn_compact_subset
        (fun t (ht : t ∈ Icc y (y + 1)) ↦ hy.trans ht.1) isCompact_Icc).continuousOn_smul
        (by fun_prop) isCompact_Icc).mono_set Ioc_subset_Icc_self
  · have hsub : Ioi (y + 1) ⊆ Ioi a := fun t ht ↦ lt_of_le_of_lt (by linarith) (mem_Ioi.mp ht)
    have hmeas_f : AEStronglyMeasurable f (volume.restrict (Ioi (y + 1))) :=
      hf_loc.aestronglyMeasurable.mono_set (hsub.trans Ioi_subset_Ici_self)
    refine Integrable.mono (hf_top.mono_set hsub)
      (((by fun_prop : Continuous fun t : ℝ ↦ (t - y) ^ k).aestronglyMeasurable).smul hmeas_f) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hty1 : 1 ≤ t - y := by linarith [mem_Ioi.mp ht]
    have hty0 : 0 ≤ t - y := by linarith
    have htya : t - y ≤ t - a := by linarith
    have hta0 : 0 ≤ t - a := by linarith
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg hty0 k),
      Real.norm_of_nonneg (pow_nonneg hta0 n)]
    exact mul_le_mul_of_nonneg_right
      ((pow_le_pow_right₀ hty1 hk).trans (pow_le_pow_left₀ hty0 htya n)) (norm_nonneg _)

/-- Evaluation `∫ s in y..t, (t - s) ^ m = (t - y) ^ (m + 1) / (m + 1)` used in the Cauchy
triangle Fubini calculation. -/
private theorem intervalIntegral_sub_pow (y t : ℝ) (m : ℕ) :
    ∫ s in y..t, (t - s) ^ m = (t - y) ^ (m + 1) / (m + 1 : ℝ) := by
  have h := intervalIntegral.integral_comp_sub_left (a := y) (b := t) (fun u : ℝ ↦ u ^ m) t
  rw [sub_self, integral_pow, zero_pow (Nat.succ_ne_zero m), sub_zero] at h
  linarith

/-- Triangular Cauchy kernel `(s, t) ↦ (t - s) ^ m • f t` supported on `y < s < t`. -/
private noncomputable def cauchyTriangleKernel (f : ℝ → E) (y : ℝ) (m : ℕ) : ℝ × ℝ → E :=
  {p : ℝ × ℝ | y < p.1 ∧ p.1 < p.2}.indicator
    fun p ↦ (p.2 - p.1) ^ m • (Ioi y).indicator f p.2

/-- Horizontal slice of `cauchyTriangleKernel` at fixed `t`. -/
private theorem cauchyTriangleKernel_snd (f : ℝ → E) (y : ℝ) (m : ℕ) (t : ℝ) :
    (fun s : ℝ ↦ cauchyTriangleKernel f y m (s, t)) =
      if y < t then (Ioo y t).indicator fun s ↦ (t - s) ^ m • f t else (0 : ℝ → E) := by
  split_ifs with ht
  · ext s
    dsimp only [cauchyTriangleKernel]
    by_cases hs : s ∈ Ioo y t
    · rw [indicator_of_mem (show (s, t) ∈ {p : ℝ × ℝ | y < p.1 ∧ p.1 < p.2} from ⟨hs.1, hs.2⟩),
        indicator_of_mem ht, indicator_of_mem hs]
    · rw [indicator_of_notMem (show (s, t) ∉ {p : ℝ × ℝ | y < p.1 ∧ p.1 < p.2} from
        fun h ↦ hs ⟨h.1, h.2⟩), indicator_of_notMem hs]
  · ext s
    simp only [cauchyTriangleKernel, Pi.zero_apply]
    exact indicator_of_notMem (show (s, t) ∉ {p : ℝ × ℝ | y < p.1 ∧ p.1 < p.2} from
      fun h ↦ ht (h.1.trans h.2)) _

/-- Vertical slice of `cauchyTriangleKernel` at fixed `s`. -/
private theorem cauchyTriangleKernel_fst (f : ℝ → E) (y : ℝ) (m : ℕ) (s : ℝ) :
    (fun t : ℝ ↦ cauchyTriangleKernel f y m (s, t)) =
      if y < s then (Ioi s).indicator fun t ↦ (t - s) ^ m • f t else (0 : ℝ → E) := by
  split_ifs with hs
  · ext t
    dsimp only [cauchyTriangleKernel]
    by_cases hst : s < t
    · rw [indicator_of_mem (show (s, t) ∈ {p : ℝ × ℝ | y < p.1 ∧ p.1 < p.2} from ⟨hs, hst⟩),
        indicator_of_mem (hs.trans hst), indicator_of_mem hst]
    · rw [indicator_of_notMem (show (s, t) ∉ {p : ℝ × ℝ | y < p.1 ∧ p.1 < p.2} from
        fun h ↦ hst h.2), indicator_of_notMem hst]
  · ext t
    simp only [cauchyTriangleKernel, Pi.zero_apply]
    exact indicator_of_notMem (show (s, t) ∉ {p : ℝ × ℝ | y < p.1 ∧ p.1 < p.2} from
      fun h ↦ hs h.1) _

/-- Product integrability of `cauchyTriangleKernel` on `ℝ × ℝ`. -/
private theorem integrable_cauchyTriangleKernel {f : ℝ → E} {y : ℝ} {m : ℕ}
    (hf0 : IntegrableOn f (Ioi y))
    (hfm1 : IntegrableOn (fun t : ℝ ↦ (t - y) ^ (m + 1) • f t) (Ioi y)) :
    Integrable (cauchyTriangleKernel f y m) (volume.prod volume) := by
  have hS : MeasurableSet {p : ℝ × ℝ | y < p.1 ∧ p.1 < p.2} :=
    (isOpen_lt continuous_const continuous_fst).measurableSet.inter
      (isOpen_lt continuous_fst continuous_snd).measurableSet
  have hf₀ : Integrable ((Ioi y).indicator f) volume :=
    (integrable_indicator_iff measurableSet_Ioi).mpr hf0
  have hmeas : AEStronglyMeasurable (cauchyTriangleKernel f y m) (volume.prod volume) :=
    (((by fun_prop : Continuous fun p : ℝ × ℝ ↦ (p.2 - p.1) ^ m).aestronglyMeasurable).smul
      (hf₀.aestronglyMeasurable.comp_snd)).indicator hS
  rw [integrable_prod_iff' hmeas]
  refine ⟨ae_of_all _ fun t ↦ ?_, ?_⟩
  · rw [cauchyTriangleKernel_snd]
    split_ifs with ht
    · rw [integrable_indicator_iff measurableSet_Ioo]
      exact (((by fun_prop : Continuous fun s : ℝ ↦ (t - s) ^ m).integrableOn_Icc).mono_set
        Ioo_subset_Icc_self).smul_const (f t)
    · exact integrable_zero _ _ _
  · have hnorm_t : (fun t : ℝ ↦ ∫ s, ‖cauchyTriangleKernel f y m (s, t)‖) =
        (Ioi y).indicator fun t ↦ ((m + 1 : ℝ)⁻¹ * (t - y) ^ (m + 1)) * ‖f t‖ := by
      ext t
      by_cases ht : y < t
      · rw [indicator_of_mem ht]
        have hpt : (fun s : ℝ ↦ ‖cauchyTriangleKernel f y m (s, t)‖) =
            (Ioo y t).indicator fun s ↦ (t - s) ^ m * ‖f t‖ := by
          ext s
          have hs_eq : cauchyTriangleKernel f y m (s, t) =
              (if y < t then (Ioo y t).indicator fun r ↦ (t - r) ^ m • f t else 0) s :=
            congrFun (cauchyTriangleKernel_snd f y m t) s
          rw [hs_eq]
          simp only [ht, ↓reduceIte]
          by_cases hs : s ∈ Ioo y t
          · rw [indicator_of_mem hs, indicator_of_mem hs, norm_smul,
              Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr hs.2.le) m)]
          · simp [hs]
        rw [hpt, integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
          ← intervalIntegral.integral_of_le ht.le, intervalIntegral.integral_mul_const,
          intervalIntegral_sub_pow, div_eq_inv_mul]
      · have hpt : (fun s : ℝ ↦ ‖cauchyTriangleKernel f y m (s, t)‖) = 0 := by
          ext s
          have hs_eq : cauchyTriangleKernel f y m (s, t) =
              (if y < t then (Ioo y t).indicator fun r ↦ (t - r) ^ m • f t else 0) s :=
            congrFun (cauchyTriangleKernel_snd f y m t) s
          simp [hs_eq, ht]
        simp [ht, hpt]
    rw [hnorm_t, integrable_indicator_iff measurableSet_Ioi]
    refine IntegrableOn.congr_fun (hfm1.norm.const_mul (m + 1 : ℝ)⁻¹) (fun t ht ↦ ?_)
      measurableSet_Ioi
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr (mem_Ioi.mp ht).le) _),
      mul_assoc]

/-- Fubini swap for Cauchy's repeated tail-integral formula on `(y, ∞)`. -/
private theorem integrableOn_and_integral_sub_pow_smul_swap [CompleteSpace E] {f : ℝ → E} {y : ℝ}
    {m : ℕ} (hf0 : IntegrableOn f (Ioi y))
    (hfm1 : IntegrableOn (fun t : ℝ ↦ (t - y) ^ (m + 1) • f t) (Ioi y)) :
    IntegrableOn (fun s : ℝ ↦ ∫ t in Ioi s, (t - s) ^ m • f t) (Ioi y) ∧
      ∫ s in Ioi y, (∫ t in Ioi s, (t - s) ^ m • f t) =
        ((m + 1 : ℝ)⁻¹) • ∫ t in Ioi y, (t - y) ^ (m + 1) • f t := by
  have hK : Integrable (cauchyTriangleKernel f y m) (volume.prod volume) :=
    integrable_cauchyTriangleKernel hf0 hfm1
  have hslice_s (s : ℝ) : (∫ t, cauchyTriangleKernel f y m (s, t)) =
      (Ioi y).indicator (fun r ↦ ∫ t in Ioi r, (t - r) ^ m • f t) s := by
    rw [cauchyTriangleKernel_fst]
    by_cases hs : y < s
    · simp only [hs, ↓reduceIte]
      rw [indicator_of_mem hs, integral_indicator measurableSet_Ioi]
    · simp [hs]
  have hslice_t (t : ℝ) : (∫ s, cauchyTriangleKernel f y m (s, t)) =
      (Ioi y).indicator (fun r ↦ ((m + 1 : ℝ)⁻¹ * (r - y) ^ (m + 1)) • f r) t := by
    rw [cauchyTriangleKernel_snd]
    by_cases ht : y < t
    · simp only [ht, ↓reduceIte]
      rw [indicator_of_mem ht, integral_indicator measurableSet_Ioo,
        ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le ht.le,
        intervalIntegral.integral_smul_const, intervalIntegral_sub_pow, div_eq_inv_mul]
    · simp [ht]
  refine ⟨(integrable_indicator_iff measurableSet_Ioi).mp
      (hK.integral_prod_left.congr (ae_of_all _ hslice_s)), ?_⟩
  calc
    ∫ s in Ioi y, (∫ t in Ioi s, (t - s) ^ m • f t)
        = ∫ s, ∫ t, cauchyTriangleKernel f y m (s, t) := by
          rw [← integral_indicator measurableSet_Ioi]
          exact integral_congr_ae (ae_of_all _ fun s ↦ (hslice_s s).symm)
    _ = ∫ t, ∫ s, cauchyTriangleKernel f y m (s, t) := integral_integral_swap hK
    _ = ((m + 1 : ℝ)⁻¹) • ∫ t in Ioi y, (t - y) ^ (m + 1) • f t := by
          rw [← integral_smul, ← integral_indicator measurableSet_Ioi]
          refine integral_congr_ae (ae_of_all _ fun t ↦ ?_)
          dsimp only
          rw [hslice_t]
          by_cases ht : y < t <;> simp [ht, mul_smul]

/-- **Cauchy's repeated tail-integral formula.** If `f : ℝ → E` is locally integrable on `[x, ∞)`
and `t ↦ (t - x) ^ n • f t` is Bochner integrable on `(x, ∞)`, then
`iteratedTailIntegral f (n + 1) x = (n !)⁻¹ • ∫ t in Ioi x, (t - x) ^ n • f t`. -/
theorem iteratedTailIntegral_succ_eq_inv_factorial_smul_integral_Ioi {f : ℝ → E} {x : ℝ} {n : ℕ}
    (hf_loc : LocallyIntegrableOn f (Ici x))
    (hf_top : IntegrableOn (fun t : ℝ ↦ (t - x) ^ n • f t) (Ioi x)) :
    iteratedTailIntegral f (n + 1) x =
      (n.factorial : ℝ)⁻¹ • ∫ t in Ioi x, (t - x) ^ n • f t := by
  by_cases hE : CompleteSpace E
  swap
  · have hzero : ∀ k y, iteratedTailIntegral f (k + 1) y = 0 := fun k y ↦ by
      rw [iteratedTailIntegral_succ]
      simp_rw [intervalIntegral, integral_of_not_completeSpace hE, sub_zero]
      exact tendsto_const_nhds.limUnder_eq
    rw [hzero, integral_of_not_completeSpace hE, smul_zero]
  suffices h : ∀ k ≤ n, ∀ y, x ≤ y →
      iteratedTailIntegral f (k + 1) y =
        (k.factorial : ℝ)⁻¹ • ∫ t in Ioi y, (t - y) ^ k • f t from h n le_rfl x le_rfl
  intro k hk
  induction k with
  | zero =>
    intro y hy
    have hi := integrableOn_sub_pow_smul_of_le hf_loc hf_top hy hk
    simp only [pow_zero, one_smul] at hi ⊢
    rw [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul]
    exact iteratedTailIntegral_succ_eq_integral_Ioi hi
  | succ m ih =>
    intro y hy
    have hf0 := integrableOn_sub_pow_smul_of_le hf_loc hf_top hy (Nat.zero_le n)
    simp only [pow_zero, one_smul] at hf0
    have hfm1 := integrableOn_sub_pow_smul_of_le hf_loc hf_top hy hk
    obtain ⟨hint_swap, hval_swap⟩ := integrableOn_and_integral_sub_pow_smul_swap hf0 hfm1
    have heq_on : EqOn (iteratedTailIntegral f (m + 1))
        (fun s ↦ (m.factorial : ℝ)⁻¹ • ∫ t in Ioi s, (t - s) ^ m • f t) (Ioi y) :=
      fun s (hs : y < s) ↦ ih (Nat.le_of_succ_le hk) s (hy.trans hs.le)
    have hint_m1 : IntegrableOn (iteratedTailIntegral f (m + 1)) (Ioi y) :=
      IntegrableOn.congr_fun (hint_swap.smul (m.factorial : ℝ)⁻¹) heq_on.symm measurableSet_Ioi
    rw [iteratedTailIntegral_succ_eq_integral_Ioi hint_m1,
      setIntegral_congr_fun measurableSet_Ioi heq_on, integral_smul, hval_swap, smul_smul,
      Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, mul_inv, mul_comm]

/-- Closed form of `iteratedTailIntegral` for a decaying exponential `t ↦ exp (-(a * t))` with
`0 < a`: `iteratedTailIntegral (fun t ↦ exp (-(a * t))) n x = exp (-(a * x)) / a ^ n`. -/
theorem iteratedTailIntegral_exp_neg_mul {a : ℝ} (ha : 0 < a) (n : ℕ) (x : ℝ) :
    iteratedTailIntegral (fun t : ℝ ↦ Real.exp (-(a * t))) n x = Real.exp (-(a * x)) / a ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hexp : IntegrableOn (fun t : ℝ ↦ Real.exp (-a * t)) (Ioi x) :=
      integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) x
    have hint : IntegrableOn (fun t : ℝ ↦ Real.exp (-(a * t)) / a ^ n) (Ioi x) := by
      refine IntegrableOn.congr_fun (hexp.mul_const (a ^ n)⁻¹) (fun t _ ↦ ?_) measurableSet_Ioi
      rw [← neg_mul, div_eq_mul_inv]
    have hint' : IntegrableOn (iteratedTailIntegral (fun t ↦ Real.exp (-(a * t))) n) (Ioi x) :=
      hint.congr_fun (fun t _ ↦ (ih t).symm) measurableSet_Ioi
    rw [iteratedTailIntegral_succ_eq_integral_Ioi hint',
      setIntegral_congr_fun measurableSet_Ioi (fun t _ ↦ ih t)]
    have hpull : (∫ t in Ioi x, Real.exp (-(a * t)) / a ^ n) =
        (∫ t in Ioi x, Real.exp (-a * t)) / a ^ n := by
      simp_rw [div_eq_mul_inv, ← neg_mul]
      exact integral_mul_const _ _
    rw [hpull, integral_exp_mul_Ioi (neg_lt_zero.mpr ha)]
    field_simp [ha.ne']
    ring

end Basic

end TauCeti
