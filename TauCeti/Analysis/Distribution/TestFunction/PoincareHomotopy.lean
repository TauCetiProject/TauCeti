/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.DifferentialForm.Poincare
public import TauCeti.Analysis.Distribution.TestFunction.ExtDeriv

/-!
# Scalar multiples of the Poincaré homotopy operator on test forms

For a centre `x₀` in a real normed space `E` and a test `(k + 1)`-form `ω` on `Ω'`, the Poincaré
homotopy operator `TauCeti.poincareHomotopy x₀ ω` is smooth (`TauCeti.contDiff_poincareHomotopy`)
but need not be compactly supported: along every ray from `x₀` meeting the support of `ω`, the
radial integral can remain nonzero arbitrarily far from `x₀`.

Multiplying by a scalar test function `χ : 𝓓(Ω, ℝ)` restores compact support inside `Ω`, and
produces a continuous linear map `TestFunction.smulPoincareHomotopyCLM x₀ χ` from test
`(k + 1)`-forms on `Ω'` to test `k`-forms on `Ω` for the LF topologies. When `χ` is equal to `1`
near the support of a compactly supported `k`-current `T` on `Ω`, precomposing `T` with
`smulPoincareHomotopyCLM x₀ χ` defines the Euclidean cone current with apex `x₀`.

Where `χ = 1` near a set `s`, the operator satisfies the local germ homotopy identities
`d (χ • K ω) + χ • K (d ω) =ᶠ[𝓝ˢ s] ω` in positive degree and `χ • K (d f) =ᶠ[𝓝ˢ s] f - χ • f x₀`
in degree zero. Moreover, whenever the topological support of `ω` is disjoint from all segments
`[x₀, x]` for `x ∈ s`, the tube lemma along `[0, 1]` shows that `K ω` and `χ • K ω` vanish on a
neighbourhood of `s`.

## Main declarations

* `TestFunction.smulPoincareHomotopyCLM`: the continuous linear map `ω ↦ χ • poincareHomotopy x₀ ω`
  on test forms.
* `TestFunction.coe_smulPoincareHomotopyCLM`, `TestFunction.smulPoincareHomotopyCLM_apply`: its
  pointwise values.
* `TestFunction.tsupport_smulPoincareHomotopyCLM_subset_left`: its support lies in `tsupport χ`.
* `TestFunction.smulPoincareHomotopyCLM_eventuallyEq_zero_of_disjoint`: vanishing in a
  neighbourhood of any set whose cone rays from `x₀` miss `tsupport ω`.
* `TestFunction.norm_smulPoincareHomotopyCLM_apply_le`: the sharp radial pointwise bound
  `‖χ x • K ω x‖ ≤ |χ x| * (B * ‖x - x₀‖ / (k + 1))`.
* `TestFunction.extDerivCLM_smulPoincareHomotopyCLM_add_eventuallyEq`,
  `TestFunction.smulPoincareHomotopyCLM_extDerivCLM_finZero_eventuallyEq`: the homotopy identities
  in `𝓝ˢ s` when `χ =ᶠ[𝓝ˢ s] 1`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.11 (cones over currents).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the homotopy formula and
  cone construction).
-/

public section

noncomputable section

open Filter Set TopologicalSpace TauCeti
open scoped Distributions Topology

namespace TestFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {Ω Ω' Ω₁ Ω₂ : Opens E} {k : ℕ}

section Bounds

variable [CompleteSpace F]

/-- The operator `ω ↦ χ • poincareHomotopy x₀ ω` on forms supported in a compact set `K`, landing
in forms supported in `tsupport χ`. -/
private def smulPoincareHomotopySupportedInCLM (x₀ : E) (χ : 𝓓(Ω, ℝ)) (K : Compacts E) :
    𝓓_{K}(E, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ]
      𝓓_{⟨tsupport χ, χ.hasCompactSupport⟩}(E, E [⋀^Fin k]→L[ℝ] F) :=
  letI P : 𝓓_{K}(E, E [⋀^Fin (k + 1)]→L[ℝ] F) →ₗ[ℝ]
      𝓓_{⟨tsupport χ, χ.hasCompactSupport⟩}(E, E [⋀^Fin k]→L[ℝ] F) :=
    { toFun ω := .of_support_subset
        (χ.contDiff.smul (contDiff_poincareHomotopy x₀ ω.contDiff))
        ((Function.support_smul_subset_left (χ : E → ℝ)
          (poincareHomotopy x₀ (ω : E → _))).trans (subset_tsupport _))
      map_add' ω η := ContDiffMapSupportedIn.ext fun x ↦ by
        simp [poincareHomotopy_add_apply ω.continuous.continuousOn η.continuous.continuousOn,
          smul_add]
      map_smul' c ω := ContDiffMapSupportedIn.ext fun x ↦ by
        simp [poincareHomotopy_smul, smul_comm (χ x) c] }
  { toLinearMap := P
    cont := by
      refine WithSeminorms.continuous_of_isBounded (ContDiffMapSupportedIn.withSeminorms ..)
        (ContDiffMapSupportedIn.withSeminorms ..) _ (.of_real fun i ↦ ?_)
      obtain ⟨A, hA, h⟩ := exists_norm_iteratedFDeriv_smul_poincareHomotopy_le (F := F) x₀ k
        (i := i) (χ.contDiff.of_le (by simp)) χ.hasCompactSupport
      refine ⟨Finset.range (i + 1), A, fun ω ↦ ((P ω).seminorm_le_iff ℝ
        (mul_nonneg hA (apply_nonneg _ _)) i).2 fun _ x _ ↦ ?_⟩
      have hP : (P ω : E → E [⋀^Fin k]→L[ℝ] F) = fun y ↦ χ y • poincareHomotopy x₀ ω y := rfl
      rw [hP]
      refine h (ω.contDiff.of_le (by simp)) fun j hj _ _ ↦ ?_
      exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_finset_sup_apply (Finset.mem_range.2 (Nat.lt_succ_of_le hj))) }

/-- **Scalar multiple of the Poincaré homotopy operator on test forms.** Given a centre `x₀ : E`
and a scalar test function `χ : 𝓓(Ω, ℝ)`, `smulPoincareHomotopyCLM x₀ χ` sends a test
`(k + 1)`-form `ω` on `Ω'` to the test `k`-form `x ↦ χ x • poincareHomotopy x₀ ω x` on `Ω`,
continuously for the LF topologies. -/
def smulPoincareHomotopyCLM (x₀ : E) (χ : 𝓓(Ω, ℝ)) :
    𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
  letI T (ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)) : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) :=
    ⟨fun x ↦ χ x • poincareHomotopy x₀ ω x,
      χ.contDiff.smul (contDiff_poincareHomotopy x₀ ω.contDiff),
      χ.hasCompactSupport.smul_right,
      (tsupport_smul_subset_left (χ : E → ℝ)
        (poincareHomotopy x₀ (ω : E → _))).trans χ.tsupport_subset⟩
  TestFunction.limitCLM ℝ T
    (fun K _ ↦ ofSupportedInCLM ℝ χ.tsupport_subset ∘L
      smulPoincareHomotopySupportedInCLM x₀ χ K)
    (fun _ _ _ ↦ rfl)

@[simp]
theorem coe_smulPoincareHomotopyCLM (x₀ : E) (χ : 𝓓(Ω, ℝ))
    (ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    ⇑(smulPoincareHomotopyCLM x₀ χ ω) = ⇑χ • poincareHomotopy x₀ ω :=
  (rfl)

theorem smulPoincareHomotopyCLM_apply (x₀ : E) (χ : 𝓓(Ω, ℝ))
    (ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)) (x : E) :
    smulPoincareHomotopyCLM x₀ χ ω x = χ x • poincareHomotopy x₀ ω x :=
  (rfl)

@[simp]
theorem smulPoincareHomotopyCLM_zero (x₀ : E) :
    (smulPoincareHomotopyCLM x₀ (0 : 𝓓(Ω, ℝ)) :
      𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) = 0 := by
  ext ω x : 2
  simp

theorem smulPoincareHomotopyCLM_add (x₀ : E) (χ₁ χ₂ : 𝓓(Ω, ℝ)) :
    (smulPoincareHomotopyCLM x₀ (χ₁ + χ₂) :
      𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) =
      smulPoincareHomotopyCLM x₀ χ₁ + smulPoincareHomotopyCLM x₀ χ₂ := by
  ext ω x : 2
  simp [add_smul]

theorem smulPoincareHomotopyCLM_smul (x₀ : E) (c : ℝ) (χ : 𝓓(Ω, ℝ)) :
    (smulPoincareHomotopyCLM x₀ (c • χ) :
      𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F)) =
      c • smulPoincareHomotopyCLM x₀ χ := by
  ext ω x : 2
  simp [smul_smul]

/-- Extending the multiplier `χ` from `Ω₁` to `Ω₂` commutes with extending the resulting test
form. -/
theorem smulPoincareHomotopyCLM_monoCLM (x₀ : E) (χ : 𝓓(Ω₁, ℝ)) :
    (smulPoincareHomotopyCLM x₀ (monoCLM ℝ χ : 𝓓(Ω₂, ℝ)) :
      𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω₂, E [⋀^Fin k]→L[ℝ] F)) =
      (monoCLM ℝ : 𝓓(Ω₁, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] 𝓓(Ω₂, E [⋀^Fin k]→L[ℝ] F)) ∘L
        (smulPoincareHomotopyCLM x₀ χ :
          𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] 𝓓(Ω₁, E [⋀^Fin k]→L[ℝ] F)) := by
  ext ω x : 2
  by_cases h : Ω₁ ≤ Ω₂ <;> simp [monoCLM_apply, h]

/-- The topological support of `smulPoincareHomotopyCLM x₀ χ ω` lies in `tsupport χ`. -/
theorem tsupport_smulPoincareHomotopyCLM_subset_left (x₀ : E) (χ : 𝓓(Ω, ℝ))
    (ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    tsupport (smulPoincareHomotopyCLM x₀ χ ω : E → E [⋀^Fin k]→L[ℝ] F) ⊆ tsupport χ := by
  rw [coe_smulPoincareHomotopyCLM]
  exact tsupport_smul_subset_left (χ : E → ℝ) (poincareHomotopy x₀ (ω : E → _))

/-- If the topological support of `ω` is disjoint from every segment `[x₀, x]` for `x ∈ s`, then
`smulPoincareHomotopyCLM x₀ χ ω` vanishes on a neighbourhood of `s`. -/
theorem smulPoincareHomotopyCLM_eventuallyEq_zero_of_disjoint (x₀ : E) (χ : 𝓓(Ω, ℝ)) {s : Set E}
    {ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)}
    (h : Disjoint (tsupport ω) (⋃ x ∈ s, segment ℝ x₀ x)) :
    (smulPoincareHomotopyCLM x₀ χ ω : E → E [⋀^Fin k]→L[ℝ] F) =ᶠ[𝓝ˢ s] 0 := by
  filter_upwards [poincareHomotopy_eventuallyEq_zero_of_disjoint h] with x hx
  simp [hx]

/-- Pointwise radial norm bound for `smulPoincareHomotopyCLM`: if `‖ω y‖ ≤ B` along `[x₀, x]`,
then `‖χ x • K ω x‖ ≤ |χ x| * (B * ‖x - x₀‖ / (k + 1))`. -/
theorem norm_smulPoincareHomotopyCLM_apply_le (x₀ : E) (χ : 𝓓(Ω, ℝ))
    (ω : 𝓓(Ω', E [⋀^Fin (k + 1)]→L[ℝ] F)) {x : E} {B : ℝ}
    (h : ∀ y ∈ segment ℝ x₀ x, ‖ω y‖ ≤ B) :
    ‖smulPoincareHomotopyCLM x₀ χ ω x‖ ≤ |χ x| * (B * ‖x - x₀‖ / (k + 1)) := by
  rw [smulPoincareHomotopyCLM_apply, norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (norm_poincareHomotopy_le h) (abs_nonneg _)

/-- **Local homotopy formula in positive degree.** Where `χ` is equal to `1` on a neighbourhood of
`s`, `d (χ • K ω) + χ • K (d ω)` agrees with `ω` on a neighbourhood of `s`. -/
theorem extDerivCLM_smulPoincareHomotopyCLM_add_eventuallyEq (x₀ : E) {χ : 𝓓(Ω, ℝ)} {s : Set E}
    (hχ : ∀ᶠ x in 𝓝ˢ s, χ x = 1) (ω : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F)) :
    (extDerivCLM (smulPoincareHomotopyCLM x₀ χ ω) +
      smulPoincareHomotopyCLM x₀ χ (extDerivCLM ω) : E → E [⋀^Fin (k + 1)]→L[ℝ] F) =ᶠ[𝓝ˢ s] ω := by
  filter_upwards [hχ, hχ.eventually_nhdsSet] with y hy1 hy_nhds
  have hloc : (smulPoincareHomotopyCLM x₀ χ ω : E → E [⋀^Fin k]→L[ℝ] F) =ᶠ[𝓝 y]
      poincareHomotopy x₀ ω :=
    hy_nhds.mono fun z hz ↦ by simp [hz]
  rw [Pi.add_apply, extDerivCLM_apply, smulPoincareHomotopyCLM_apply, coe_extDerivCLM, hy1,
    one_smul ℝ, hloc.extDeriv_eq]
  exact extDeriv_poincareHomotopy_add_poincareHomotopy_extDeriv x₀ (ω.contDiff.of_le (by simp)) y

/-- **Local homotopy formula in degree zero.** Where `χ` is equal to `1` on a neighbourhood of
`s`, `χ • K (d ω)` agrees on a neighbourhood of `s` with `ω - χ • ω x₀`, written using
`TestFunction.postcompCLM` so both terms are test `0`-forms on `Ω`. -/
theorem smulPoincareHomotopyCLM_extDerivCLM_finZero_eventuallyEq (x₀ : E) {χ : 𝓓(Ω, ℝ)}
    {s : Set E} (hχ : ∀ᶠ x in 𝓝ˢ s, χ x = 1) (ω : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F)) :
    (smulPoincareHomotopyCLM x₀ χ (extDerivCLM ω) : E → E [⋀^Fin 0]→L[ℝ] F) =ᶠ[𝓝ˢ s]
      ⇑(ω - postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (ω x₀)) χ) := by
  filter_upwards [hχ] with y hy
  rw [FunLike.coe_sub, Pi.sub_apply, smulPoincareHomotopyCLM_apply, coe_extDerivCLM,
    postcompCLM_apply, Function.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, hy,
    one_smul ℝ, one_smul ℝ]
  exact poincareHomotopy_extDeriv_eq_sub x₀ (ω.contDiff.of_le (by simp)) y

end Bounds

end TestFunction
