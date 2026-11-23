/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Factorial.DoubleFactorial
public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Kolmogorov
public import Mathlib.Topology.MetricSpace.Holder

import TauCeti.Probability.Process.Indistinguishable
import TauCeti.Probability.Process.Kolmogorov.Basic
import TauCeti.Probability.Process.Kolmogorov.Chentsov

/-!
# Path regularity and continuous modifications of real Brownian motion

For any standard real pre-Brownian motion `B` under a measure `P` (`IsPreBrownianReal B P`), the
Gaussian increment laws yield the `(2 m, m)` Kolmogorov moment bound for every `m ≥ 1`. Applying
the one-dimensional Kolmogorov–Chentsov theorem gives an all-paths continuous, coordinatewise
measurable Brownian modification and, for any `IsBrownianReal` process, simultaneous local
`γ`-Hölder continuity on every compact horizon `Iic T` for all `γ < 1 / 2`.

These path-regularity results apply to arbitrary `(pre-)Brownian` processes without importing the
Wiener-measure projective-limit construction.

## Main results

* `ProbabilityTheory.IsPreBrownianReal.isAEKolmogorovProcess_two_mul`: `(2 m, m)` Kolmogorov moment
  condition for pre-Brownian motion (`m ≥ 1`).
* `ProbabilityTheory.IsPreBrownianReal.exists_continuous_modification`: every pre-Brownian motion
  admits an all-paths continuous, coordinatewise measurable Brownian modification.
* `ProbabilityTheory.IsBrownianReal.ae_exists_holderOnWith`: almost every path of a Brownian motion
  is simultaneously `γ`-Hölder continuous on `Iic T` for all `γ < 1 / 2` and all `T : ℝ≥0`.

## References

* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Springer, 2021, Theorem 14.2.
* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, 2nd ed., Springer, 1991,
  §2.2.
-/

public section

open MeasureTheory Set
open scoped Nat NNReal

namespace ProbabilityTheory

variable {Ω : Type*} {_ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- For every `m ≥ 1`, a pre-Brownian motion satisfies `IsAEKolmogorovProcess` with exponents
`p = 2 m`, `q = m`, and constant `(2 m - 1)‼`. -/
theorem IsPreBrownianReal.isAEKolmogorovProcess_two_mul (hB : IsPreBrownianReal B P)
    {m : ℕ} (hm : 1 ≤ m) :
    IsAEKolmogorovProcess B P (2 * m) m (2 * m - 1)‼ := by
  let Y : ℝ≥0 → Ω → ℝ := fun t ↦ (hB.aemeasurable t).mk (B t)
  have hY_ae (t : ℝ≥0) : B t =ᵐ[P] Y t := (hB.aemeasurable t).ae_eq_mk
  have hkol := isKolmogorovProcess_of_hasLaw_sub_gaussianReal
    (fun t ↦ (hB.aemeasurable t).measurable_mk)
    (fun s t ↦ (hB.congr hY_ae).hasLaw_sub s t) (n := m) (by omega)
  push_cast at hkol
  exact ⟨Y, hkol, hY_ae⟩

/-- Every pre-Brownian motion admits a coordinatewise measurable, all-paths continuous Brownian
modification. -/
theorem IsPreBrownianReal.exists_continuous_modification (hB : IsPreBrownianReal B P) :
    ∃ W : ℝ≥0 → Ω → ℝ,
      (∀ t : ℝ≥0, Measurable (W t)) ∧
      (∀ ω : Ω, Continuous (W · ω)) ∧
      IsBrownianReal W P ∧
      (∀ t : ℝ≥0, W t =ᵐ[P] B t) := by
  have hkol : IsAEKolmogorovProcess B P 4 2 3 := by
    convert hB.isAEKolmogorovProcess_two_mul (m := 2) (by omega) <;> norm_num
  obtain ⟨W, hW_meas, hW_cont, hW_ae, _⟩ := hkol.exists_continuous_modification one_lt_two
  exact ⟨W, hW_meas, hW_cont,
    { toIsPreBrownianReal := hB.congr fun t ↦ (hW_ae t).symm
      cont := ae_of_all _ hW_cont },
    hW_ae⟩

/-- **Lévy–Kolmogorov local Hölder regularity of Brownian motion.** Almost every sample path of a
real Brownian motion is simultaneously `γ`-Hölder continuous on `Iic T` for every `γ : ℝ≥0` with
`(γ : ℝ) < 1 / 2` and every compact horizon `T : ℝ≥0`. -/
theorem IsBrownianReal.ae_exists_holderOnWith (hB : IsBrownianReal B P) :
    ∀ᵐ ω ∂P, ∀ (γ : ℝ≥0), (γ : ℝ) < 1 / 2 → ∀ T : ℝ≥0,
      ∃ C : ℝ≥0, HolderOnWith C γ (B · ω) (Iic T) := by
  have hW (k : ℕ) : ∃ W : ℝ≥0 → Ω → ℝ, W ≡ᵐ[P] B ∧
      ∀ (ω : Ω) (γ : ℝ≥0), (γ : ℝ) < (((k + 2 : ℕ) : ℝ) - 1) / (2 * ((k + 2 : ℕ) : ℝ)) →
        ∀ T : ℝ≥0, ∃ C : ℝ≥0, HolderOnWith C γ (W · ω) (Iic T) := by
    have hm1 : 1 < ((k + 2 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 < k + 2)
    obtain ⟨W, _, hW_cont, hWB, hWh⟩ :=
      (hB.toIsPreBrownianReal.isAEKolmogorovProcess_two_mul (m := k + 2) (by omega))
        |>.exists_continuous_modification hm1
    exact ⟨W, TauCeti.indist_of_ae_continuous (ae_of_all _ hW_cont) hB.cont hWB, hWh⟩
  choose W hWB hWh using hW
  filter_upwards [ae_all_iff.2 hWB] with ω hω γ hγ T
  have hgap : 0 < 1 - 2 * (γ : ℝ) := by linarith
  let k : ℕ := ⌊(1 - 2 * (γ : ℝ))⁻¹⌋₊
  have hinv_lt : (1 - 2 * (γ : ℝ))⁻¹ < ((k + 2 : ℕ) : ℝ) := by
    have hlt : (1 - 2 * (γ : ℝ))⁻¹ < (k : ℝ) + 1 := Nat.lt_floor_add_one _
    push_cast
    linarith
  have hmul : 1 < ((k + 2 : ℕ) : ℝ) * (1 - 2 * (γ : ℝ)) :=
    (inv_lt_iff_one_lt_mul₀ hgap).mp hinv_lt
  have hγ_lt : (γ : ℝ) < (((k + 2 : ℕ) : ℝ) - 1) / (2 * ((k + 2 : ℕ) : ℝ)) := by
    rw [lt_div_iff₀ (by positivity)]
    linarith
  obtain ⟨C, hC⟩ := hWh k ω γ hγ_lt T
  refine ⟨C, ?_⟩
  have heq : (B · ω) = (W k · ω) := funext fun t ↦ (hω k t).symm
  rwa [heq]

end ProbabilityTheory
