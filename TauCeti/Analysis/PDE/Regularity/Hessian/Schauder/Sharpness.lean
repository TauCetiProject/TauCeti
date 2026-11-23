/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Topology.MetricSpace.Holder

/-!
# The Hölder exponent of the Schauder estimate is sharp

The interior Schauder estimate for `-aⁱʲ ∂ᵢ∂ⱼu = f` bounds the `α`-Hölder seminorm of `D²u` by the
`α`-Hölder seminorm of `f` (see
`TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_of_sum_smul_fderiv_fderiv_of_holderOnWith`):
the Hessian is exactly as regular as the data. This file shows that the exponent on the left cannot
be raised, already for the Laplacian, `a = 1`. On a nontrivial finite-dimensional real inner
product space `E` of dimension `n` and for `0 < α ≤ 1`, the radial function

`u(x) = -‖x‖ ^ (2 + α) / ((2 + α) (n + α))`

is `C²` and solves `-Δu = ‖x‖ ^ α` at every point, including the origin. Its datum `‖x‖ ^ α` is
`α`-Hölder with constant one (`TauCeti.holderWith_norm_rpow`), and its Hessian is `α`-Hölder on
the whole space (`TauCeti.holderWith_iteratedFDeriv_two_norm_rpow_two_add`). But for every
`β > α` the Hessian is not `β`-Hölder on any neighbourhood of the origin, with any constant
(`TauCeti.not_holderOnWith_iteratedFDeriv_two_norm_rpow`): it vanishes at the origin and grows like
`‖x‖ ^ α` along every ray. So `u ∈ C^{2,α}` exactly, and an estimate of `[D²u]_β` by `[f]_α` fails
for every `β > α`
(`TauCeti.PDE.exists_contDiff_neg_laplacian_eq_and_holderWith_and_not_holderOnWith`).
In dimension one this is the example `-u'' = |x| ^ α`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 4 and Theorem 6.2 (the interior Schauder estimate).
-/

public section

open Filter InnerProductSpace Laplacian Topology
open scoped NNReal

namespace TauCeti.PDE

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The Hölder exponent of the Schauder estimate is sharp.** On a nontrivial finite-dimensional
real inner product space and for `0 < α ≤ 1`, there is a `C²` solution `u` of Poisson's equation
`-Δu = ‖x‖ ^ α`, whose datum is `α`-Hölder (`TauCeti.holderWith_norm_rpow`), such that the Hessian
of `u` is `α`-Hölder on the whole space but, for every `β > α`, not `β`-Hölder with any constant
on any neighbourhood of the origin. The solution is `-‖x‖ ^ (2 + α) / ((2 + α) (dim E + α))`. -/
theorem exists_contDiff_neg_laplacian_eq_and_holderWith_and_not_holderOnWith [Nontrivial E]
    {α : ℝ≥0} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ u : E → ℝ, ContDiff ℝ 2 u ∧ (∀ x, -Δ u x = ‖x‖ ^ (α : ℝ)) ∧
      (∃ C : ℝ≥0, HolderWith C α (iteratedFDeriv ℝ 2 u)) ∧
      ∀ β : ℝ≥0, α < β → ∀ (C : ℝ≥0) (s : Set E), s ∈ 𝓝 0 →
        ¬ HolderOnWith C β (iteratedFDeriv ℝ 2 u) s := by
  have ha0 : (0 : ℝ) < α := hα0
  set f : E → ℝ := fun y ↦ ‖y‖ ^ (2 + (α : ℝ)) with hf_def
  set c : ℝ := -((2 + (α : ℝ)) * (Module.finrank ℝ E + (α : ℝ)))⁻¹ with hc_def
  have hn : 0 < (2 + (α : ℝ)) * (Module.finrank ℝ E + α) := by positivity
  have hc : c ≠ 0 := neg_ne_zero.mpr (inv_ne_zero hn.ne')
  have hf : ContDiff ℝ 2 f := contDiff_norm_rpow_of_lt (by push_cast; linarith)
  -- The Hessian of `c • f` is `c` times that of `f`.
  have hD : iteratedFDeriv ℝ 2 (c • f) = c • iteratedFDeriv ℝ 2 f :=
    funext fun x ↦ iteratedFDeriv_const_smul_apply hf.contDiffAt
  refine ⟨c • f, hf.const_smul c, fun x ↦ ?_, ⟨30 * ‖c‖₊, ?_⟩, fun β hβ C s hs hH ↦ ?_⟩
  · rw [laplacian_smul c hf.contDiffAt, hf_def,
      laplacian_norm_rpow_of_two_lt (by linarith : 2 < 2 + (α : ℝ)) x, smul_eq_mul, hc_def,
      show 2 + (α : ℝ) - 2 = α by ring]
    field_simp
    ring
  · rw [hD]
    exact (holderWith_iteratedFDeriv_two_norm_rpow_two_add (E := E) hα0 hα1).smul c
  · -- Dividing by `c` would make the Hessian of `‖x‖ ^ (2 + α)` itself `β`-Hölder near `0`.
    rw [hD] at hH
    have h := hH.smul c⁻¹
    rw [smul_smul, inv_mul_cancel₀ hc, one_smul] at h
    have hβ' : (α : ℝ) < β := hβ
    exact not_holderOnWith_iteratedFDeriv_two_norm_rpow (by linarith : 2 < 2 + (α : ℝ))
      (by linarith) hs h

end TauCeti.PDE
