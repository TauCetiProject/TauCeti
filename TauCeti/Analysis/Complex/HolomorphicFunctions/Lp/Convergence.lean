/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.HolomorphicFunctions.Lp.Estimates
public import Mathlib.Analysis.Complex.LocallyUniformLimit

/-!
# Locally uniform holomorphic limits of L² Cauchy sequences

Native `L²` Cauchy sequences with holomorphic representatives are uniformly Cauchy on compact
subsets of their domain and converge locally uniformly to a holomorphic function. The values
may lie in any complete complex normed space; the domain may have infinite measure.

## References

* J. B. Conway, *Functions of One Complex Variable II*, Chapter I.
-/

public noncomputable section

open MeasureTheory Filter Metric Set TopologicalSpace Topology
open scoped ENNReal

namespace TauCeti.HolomorphicFunctions

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] {U : Opens ℂ}

/-- A sequence of holomorphic representatives Cauchy in native `L²` is uniformly Cauchy on
every compact subset of its holomorphic domain. -/
theorem uniformCauchySeqOn_of_cauchySeq
    {u : ℕ → Lp F 2 (volume.restrict (U : Set ℂ))} {f : ℕ → ℂ → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hu : ∀ n, u n =ᵐ[volume.restrict (U : Set ℂ)] f n) (hc : CauchySeq u)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) :
    UniformCauchySeqOn f atTop K := by
  obtain ⟨r, hr, hrU⟩ := hK.exists_cthickening_subset_open U.isOpen hKU
  let C := (volume.real (ball (0 : ℂ) r))⁻¹ *
    ((volume (ball (0 : ℂ) r)) ^ (1 / 2 : ℝ)).toReal
  have hC : 0 ≤ C := by positivity
  refine Metric.uniformCauchySeqOn_iff.2 fun ε hε ↦ ?_
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.1 hc (ε / (C + 1))
    (div_pos hε (by positivity))
  refine ⟨N, fun m hm n hn x hx ↦ ?_⟩
  have hae : u m - u n =ᵐ[volume.restrict (U : Set ℂ)] f m - f n :=
    (Lp.coeFn_sub _ _).trans ((hu m).sub (hu n))
  have hbound := norm_le_Lp_norm ((hf m).sub (hf n)) hae hr
    ((closedBall_subset_cthickening hx r).trans hrU)
  rw [Pi.sub_apply, ← dist_eq_norm] at hbound
  calc
    dist (f m x) (f n x) ≤ C * ‖u m - u n‖ := hbound
    _ ≤ (C + 1) * dist (u m) (u n) := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (C + 1) * (ε / (C + 1)) :=
      mul_lt_mul_of_pos_left (hN m hm n hn) (by positivity)
    _ = ε := mul_div_cancel₀ ε (by positivity)

/-- A sequence of holomorphic representatives that is Cauchy in native `L²` converges
locally uniformly to a holomorphic function. No finite measure assumption on `U` is needed. -/
theorem exists_tendstoLocallyUniformlyOn_of_cauchySeq
    {u : ℕ → Lp F 2 (volume.restrict (U : Set ℂ))} {f : ℕ → ℂ → F}
    (hf : ∀ n, DifferentiableOn ℂ (f n) U)
    (hu : ∀ n, u n =ᵐ[volume.restrict (U : Set ℂ)] f n) (hc : CauchySeq u) :
    ∃ g : ℂ → F, DifferentiableOn ℂ g U ∧ TendstoLocallyUniformlyOn f g atTop U := by
  let g := fun x ↦ limUnder atTop (fun n ↦ f n x)
  have hpoint : ∀ x ∈ U, Tendsto (fun n ↦ f n x) atTop (𝓝 (g x)) := by
    intro x hx
    exact ((uniformCauchySeqOn_of_cauchySeq hf hu hc isCompact_singleton
      (singleton_subset_iff.2 hx)).cauchySeq (mem_singleton x)).tendsto_limUnder
  have hlocal : TendstoLocallyUniformlyOn f g atTop U := by
    refine (tendstoLocallyUniformlyOn_iff_forall_isCompact U.isOpen).2 fun K hKU hK ↦ ?_
    exact (uniformCauchySeqOn_of_cauchySeq hf hu hc hK hKU).tendstoUniformlyOn_of_tendsto
      fun x hx ↦ hpoint x (hKU hx)
  exact ⟨g, hlocal.differentiableOn (Eventually.of_forall hf) U.isOpen, hlocal⟩

end TauCeti.HolomorphicFunctions
