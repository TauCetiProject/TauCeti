/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Wirtinger.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Holomorphy and the conjugate Wirtinger derivative

For a real-differentiable map between complex normed spaces, vanishing of the conjugate
Wirtinger derivative characterizes complex differentiability. The real-differentiability
hypothesis is essential because the totalized real derivative vanishes at nondifferentiable
points. In one variable the real differential has coefficients `wirtingerDeriv f x 1` and
`conjWirtingerDeriv f x 1` in the basis `dz`, `dbar z`; testing the latter coefficient alone
detects its vanishing.

On the coordinate space `ι → ℂ` the conjugate Wirtinger derivative is conjugate-linear, so it
vanishes as soon as it vanishes on the coordinate vectors: a real-differentiable map is holomorphic
exactly when all its partial derivatives `∂g/∂(conj z_j)` vanish
(`TauCeti.differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero`).

Adding a holomorphic function does not change the conjugate Wirtinger derivative, so a function
that is locally a `Cⁿ` function plus a holomorphic one is `Cⁿ` with the same conjugate Wirtinger
derivatives (`TauCeti.contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add`). This glues the
local solutions in exhaustion proofs of the `\bar∂`-lemma.

These statements connect the real differential and its type decomposition with holomorphy.

## References

* L. Hörmander, *An Introduction to Complex Analysis in Several Variables*, Chapter II.
-/

public noncomputable section

open Complex Set
open scoped ComplexConjugate

namespace TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-- A real-differentiable map between complex normed spaces is complex differentiable
exactly when its conjugate Wirtinger derivative vanishes. -/
theorem differentiableAt_iff_conjWirtingerDeriv_eq_zero {g : V → W} {x : V}
    (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℂ g x ↔ conjWirtingerDeriv g x = 0 := by
  constructor
  · exact fun h ↦ h.conjWirtingerDeriv_eq_zero
  · intro h
    apply (differentiableAt_iff_restrictScalars ℝ hg).mpr
    refine ⟨wirtingerDeriv g x, ?_⟩
    ext v
    simpa only [ContinuousLinearMap.coe_restrictScalars', h, zero_apply, add_zero] using
      wirtingerDeriv_add_conjWirtingerDeriv g x v

/-- For a real-differentiable function of one complex variable, the single equation
`conjWirtingerDeriv f x 1 = 0` characterizes complex differentiability. -/
theorem differentiableAt_iff_conjWirtingerDeriv_apply_one_eq_zero {f : ℂ → W} {x : ℂ}
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℂ f x ↔ conjWirtingerDeriv f x 1 = 0 := by
  rw [differentiableAt_iff_conjWirtingerDeriv_eq_zero hf,
    conjWirtingerDeriv_eq_zero_iff_apply_one_eq_zero]

/-- On `ι → ℂ`, a real-differentiable map is complex differentiable exactly when its conjugate
Wirtinger derivatives `∂g/∂(conj z_j)` in the coordinate directions all vanish. -/
theorem differentiableAt_iff_forall_conjWirtingerDeriv_apply_single_eq_zero {ι : Type*}
    [Fintype ι] [DecidableEq ι] {g : (ι → ℂ) → W} {x : ι → ℂ} (hg : DifferentiableAt ℝ g x) :
    DifferentiableAt ℂ g x ↔ ∀ j, conjWirtingerDeriv g x (Pi.single j 1) = 0 := by
  rw [differentiableAt_iff_conjWirtingerDeriv_eq_zero hg]
  refine ⟨fun h j ↦ by simp [h], fun h ↦ ContinuousLinearMap.ext fun v ↦ ?_⟩
  have hv : v = ∑ j, v j • Pi.single j (1 : ℂ) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    simp [← Pi.single_smul]
  rw [hv, map_sum]
  simp [h]

/-- **Gluing modulo holomorphic functions.** If near each point of `U` the function `G` is a
`Cⁿ` function `a`, `n ≥ 1`, plus a holomorphic `Cⁿ` function, and the conjugate Wirtinger
derivatives of `a` in the directions `v j` are `f j`, then `G` is `Cⁿ` on `U` with the same
conjugate Wirtinger derivatives. -/
theorem contDiffOn_and_conjWirtingerDeriv_eq_of_locally_eq_add {ι : Type*} {n : WithTop ℕ∞}
    {G : V → W} {v : ι → V} {f : ι → V → W} {U : Set V} (hn : 1 ≤ n)
    (hG : ∀ z ∈ U, ∃ O : Set V, IsOpen O ∧ z ∈ O ∧ ∃ a K : V → W, ContDiffOn ℝ n a O ∧
      (∀ w ∈ O, ∀ j, conjWirtingerDeriv a w (v j) = f j w) ∧ ContDiffOn ℂ n K O ∧
        EqOn G (a + K) O) :
    ContDiffOn ℝ n G U ∧ ∀ z ∈ U, ∀ j, conjWirtingerDeriv G z (v j) = f j z := by
  refine ⟨contDiffOn_of_locally_contDiffOn fun z hz ↦ ?_, fun z hz j ↦ ?_⟩
  · obtain ⟨O, hO, hzO, a, K, ha, -, hK, hGK⟩ := hG z hz
    exact ⟨O, hO, hzO, ((ha.add (hK.restrict_scalars ℝ)).congr hGK).mono inter_subset_right⟩
  · obtain ⟨O, hO, hzO, a, K, ha, haf, hK, hGK⟩ := hG z hz
    have hn0 : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
    have hKz := (hK.contDiffAt (hO.mem_nhds hzO)).differentiableAt hn0
    rw [(hGK.eventuallyEq_of_mem (hO.mem_nhds hzO)).conjWirtingerDeriv_eq,
      conjWirtingerDeriv_add ((ha.contDiffAt (hO.mem_nhds hzO)).differentiableAt hn0)
        (hKz.restrictScalars ℝ), add_apply, hKz.conjWirtingerDeriv_eq_zero, zero_apply,
      add_zero, haf z hzO j]

end TauCeti
