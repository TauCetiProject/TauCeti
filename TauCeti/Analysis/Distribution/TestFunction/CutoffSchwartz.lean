/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.TestFunction.Schwartz

/-!
# Cutting off Schwartz functions to test functions

The product `ψ • u` of a real test function `ψ` on an open set `Ω` and a Schwartz function `u` is
a test function on `Ω`, supported in the support of `ψ` (`TestFunction.smulSchwartzMap`). This
file shows that it depends continuously on `u` (`TestFunction.smulSchwartzMapCLM`): by the Leibniz
rule, the `i`-th derivative of `ψ • u` is bounded by the first `i` derivatives of `u`, with
constants given by the sup norms of the derivatives of `ψ`.

So an operator which is continuous on Schwartz space, followed by a cutoff, lands continuously in
the test functions on `Ω`. This is how operators defined on Schwartz functions, such as the
quantizations of symbols, are read back on a manifold through a chart.

## Main declarations

* `TestFunction.smulSchwartzMapCLM`: the map `u ↦ ψ • u` from Schwartz functions to test
  functions on `Ω`, as a continuous linear map.
-/

public section

noncomputable section

open Set TopologicalSpace
open scoped Distributions ContDiff SchwartzMap

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {Ω : Opens E}

/-- The product `ψ • u` of a test function `ψ` and a Schwartz function `u`, as a smooth function
supported in the compact set `tsupport ψ`, depending continuously on `u`. -/
private def smulSchwartzMapSupportedInCLM (ψ : 𝓓(Ω, ℝ)) :
    𝓢(E, F) →L[ℝ] 𝓓_{⟨tsupport ψ, ψ.hasCompactSupport⟩}(E, F) :=
  letI P : 𝓢(E, F) →ₗ[ℝ] 𝓓_{⟨tsupport ψ, ψ.hasCompactSupport⟩}(E, F) :=
    { toFun u := ContDiffMapSupportedIn.of_support_subset (ψ.contDiff.smul (u.smooth ⊤))
        ((Function.support_smul_subset_left _ _).trans (subset_tsupport _))
      map_add' u v := ContDiffMapSupportedIn.ext fun x ↦ smul_add (ψ x) (u x) (v x)
      map_smul' c u := ContDiffMapSupportedIn.ext fun x ↦ smul_comm (ψ x) c (u x) }
  { toLinearMap := P
    cont := by
      -- Leibniz: the `i`-th derivative is controlled by the first `i` derivatives of `u`, with
      -- constants given by bounds for the derivatives of `ψ`.
      choose M hM using fun j : ℕ ↦
        (ψ.contDiff.continuous_iteratedFDeriv (m := j) (mod_cast le_top)).norm
          |>.bddAbove_range_of_hasCompactSupport (ψ.hasCompactSupport.iteratedFDeriv j).norm
      refine WithSeminorms.continuous_of_isBounded (schwartz_withSeminorms ℝ E F)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      refine ⟨{0} ×ˢ Finset.range (i + 1), ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * |M j|,
        fun u ↦ ((P u).seminorm_le_iff ℝ (mul_nonneg (Finset.sum_nonneg fun _ _ ↦ by positivity)
          (apply_nonneg _ _)) i).2 fun _ x _ ↦ ?_⟩
      refine (norm_iteratedFDeriv_smul_le ψ.contDiff (u.smooth ⊤) x (mod_cast le_top)).trans ?_
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun j hj ↦ ?_
      have hj : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      have hψj : ‖iteratedFDeriv ℝ j ψ x‖ ≤ |M j| := (hM j ⟨x, rfl⟩).trans (le_abs_self _)
      have hmem : ((0, i - j) : ℕ × ℕ) ∈ ({0} ×ˢ Finset.range (i + 1)) := by
        simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, true_and]
        omega
      have huj : ‖iteratedFDeriv ℝ (i - j) u x‖ ≤
          (({0} ×ˢ Finset.range (i + 1)).sup (schwartzSeminormFamily ℝ E F)) u :=
        (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ u (i - j) x).trans
          (Seminorm.le_finset_sup_apply (p := schwartzSeminormFamily ℝ E F) hmem)
      calc (i.choose j : ℝ) * ‖iteratedFDeriv ℝ j ψ x‖ * ‖iteratedFDeriv ℝ (i - j) u x‖
          ≤ (i.choose j : ℝ) * |M j| *
              (({0} ×ˢ Finset.range (i + 1)).sup (schwartzSeminormFamily ℝ E F)) u := by
            gcongr }

/-- **Cutting off Schwartz functions.** The product `ψ • u` of a real test function `ψ` on `Ω`
and a Schwartz function `u` (`TestFunction.smulSchwartzMap`), as a continuous linear map from
Schwartz functions to test functions on `Ω`. -/
def smulSchwartzMapCLM (ψ : 𝓓(Ω, ℝ)) : 𝓢(E, F) →L[ℝ] 𝓓(Ω, F) :=
  (ofSupportedInCLM ℝ ψ.tsupport_subset).comp (smulSchwartzMapSupportedInCLM ψ)

@[simp]
theorem smulSchwartzMapCLM_apply (ψ : 𝓓(Ω, ℝ)) (u : 𝓢(E, F)) (x : E) :
    smulSchwartzMapCLM ψ u x = ψ x • u x :=
  (rfl)

/-- The continuous linear map `smulSchwartzMapCLM ψ` is `TestFunction.smulSchwartzMap ψ`. -/
theorem smulSchwartzMapCLM_eq_smulSchwartzMap (ψ : 𝓓(Ω, ℝ)) (u : 𝓢(E, F)) :
    smulSchwartzMapCLM ψ u = ψ.smulSchwartzMap u :=
  TestFunction.ext fun x ↦ by simp

end TestFunction
