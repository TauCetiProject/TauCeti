/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Order
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ
import TauCeti.Geometry.Manifold.ContMDiff.Analytic

/-!
# Maximal-ideal separatedness of holomorphic stalks

Let `X` be a complex analytic manifold modelled without boundary on a complex normed space `E`.
This file proves that the stalk `(holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x` is
separated (`IsHausdorff`) with respect to its maximal ideal: a holomorphic germ lying in every
power of the maximal ideal is zero.

The argument requires neither finite-dimensionality of `E` nor Noetherianity of the stalk (so
Krull's intersection theorem is not needed). If a germ `s` lies in `𝔪_x ^ n`, restricting any local
representative of `s` read in a holomorphic chart `e` to any complex line `z ↦ e x + z • v`
through `e x` produces a one-variable holomorphic function vanishing to order at least `n` at
`0`. Lying in `𝔪_x ^ n` for every `n` therefore forces infinite analytic order at `0` along every
complex line, hence vanishing on an open ball around `e x` by one-variable analytic continuation
along radial discs. (For complex curves `E = ℂ`,
`TauCeti.Geometry.Manifold.Complex.StructureSheaf.Order` obtains separatedness from local
coordinate division instead.)

## Main results

* `OpenPartialHomeomorph.iInf_pow_ker_eval_eq_bot`: at the center `x` of any chart
  `e ∈ maximalAtlas 𝓘(ℂ, E) ω X`, the intersection of all powers of `RingHom.ker (eval 𝓘(ℂ, E) X x)`
  is `⊥`.
* `OpenPartialHomeomorph.isHausdorff_maximalIdeal_stalk`: the stalk at `x` is `IsHausdorff` with
  respect to its maximal ideal.
* `TauCeti.holomorphicStructureSheaf.instIsHausdorffMaximalIdealStalkOfOmega`: `IsHausdorff`
  instance on stalks of any complex analytic manifold `[IsManifold 𝓘(ℂ, E) ω X]`, with no
  finite-dimensionality assumption on `E`.
* `TauCeti.holomorphicStructureSheaf.instIsHausdorffMaximalIdealStalk`: `IsHausdorff` instance on
  stalks of any finite-dimensional complex manifold
  `[FiniteDimensional ℂ E] [IsManifold 𝓘(ℂ, E) 1 X]`.

## References

* J.-P. Demailly, *Complex Analytic and Differential Geometry*, Chapter II, §3.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
-/

public noncomputable section

open Filter IsManifold Metric Set TopologicalSpace Topology
open scoped ContDiff Manifold
open TauCeti TauCeti.holomorphicStructureSheaf

namespace OpenPartialHomeomorph

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X]
  (e : OpenPartialHomeomorph X E) (he : e ∈ maximalAtlas 𝓘(ℂ, E) ω X)

include he in
/-- Reading any representative of a holomorphic germ at `x` in the chart `e` along a complex line
through `e x` gives a function analytic at `0`. -/
private theorem analyticAt_line_of_toFilterGerm_eq {x : X} (hx : x ∈ e.source)
    {s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x} {φ : X → ℂ}
    (hφ : toFilterGerm 𝓘(ℂ, E) X x (𝓝 x) le_rfl s = φ) (v : E) :
    AnalyticAt ℂ (fun z : ℂ ↦ φ (e.symm (e x + z • v))) 0 := by
  have hφe : AnalyticAt ℂ (φ ∘ e.symm) (e x) := by
    simpa using ((exists_toFilterGerm_nhds_eq_iff.1 ⟨s, hφ⟩).self_of_nhds
      |>.analyticAt_comp_extend_symm he hx)
  exact hφe.comp_of_eq (by fun_prop) (by simp)

include he in
/-- Every representative of a germ in `RingHom.ker (eval 𝓘(ℂ, E) X x) ^ n` vanishes to analytic
order at least `n` at `0` along every complex line through `e x` in the chart `e`. -/
private theorem natCast_le_analyticOrderAt_line_of_mem_pow_ker_eval {x : X} (hx : x ∈ e.source) :
    ∀ {n : ℕ} {s : (holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x},
      s ∈ RingHom.ker (eval 𝓘(ℂ, E) X x) ^ n →
      ∀ {φ : X → ℂ}, toFilterGerm 𝓘(ℂ, E) X x (𝓝 x) le_rfl s = φ →
      ∀ v : E, (n : ℕ∞) ≤ analyticOrderAt (fun z : ℂ ↦ φ (e.symm (e x + z • v))) 0
  | 0, _, _, _, _, _ => by simp
  | n + 1, s, hs, φ, hφ, v => by
    have hline : Tendsto (fun z : ℂ ↦ e.symm (e x + z • v)) (𝓝 0) (𝓝 x) := by
      simpa only [Function.comp_def, e.left_inv hx] using
        (e.continuousAt_symm (e.map_source hx)).tendsto.comp
          (by simpa using (by fun_prop : Continuous fun z : ℂ ↦ e x + z • v).tendsto 0)
    rw [pow_succ] at hs
    refine Submodule.mul_induction_on
      (C := fun t ↦ ∀ ψ : X → ℂ, toFilterGerm 𝓘(ℂ, E) X x (𝓝 x) le_rfl t = ψ →
        ((n + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fun z : ℂ ↦ ψ (e.symm (e x + z • v))) 0)
      hs (fun a ha b hb ψ hψ ↦ ?_) (fun a b ha hb ψ hψ ↦ ?_) φ hφ
    · obtain ⟨α, -, hα⟩ := exists_toFilterGerm_eq x a
      obtain ⟨β, -, hβ⟩ := exists_toFilterGerm_eq x b
      have hf₁ := analyticAt_line_of_toFilterGerm_eq e he hx (hα _ le_rfl) v
      have hf₂ := analyticAt_line_of_toFilterGerm_eq e he hx (hβ _ le_rfl) v
      have hev : ψ =ᶠ[𝓝 x] α * β := Germ.coe_eq.1 (by rw [← hψ, map_mul, hα, hβ, Germ.coe_mul])
      have hcongr : (fun z : ℂ ↦ ψ (e.symm (e x + z • v))) =ᶠ[𝓝 0]
          (fun z ↦ α (e.symm (e x + z • v))) * fun z ↦ β (e.symm (e x + z • v)) :=
        hline.eventually hev
      have hf₂0 : β (e.symm (e x + (0 : ℂ) • v)) = 0 := by
        simpa [e.left_inv hx] using (eval_eq_of_toFilterGerm_eq (hβ _ le_rfl)).symm.trans hb
      rw [analyticOrderAt_congr hcongr, analyticOrderAt_mul hf₁ hf₂, Nat.cast_add, Nat.cast_one]
      exact add_le_add (natCast_le_analyticOrderAt_line_of_mem_pow_ker_eval hx ha (hα _ le_rfl) v)
        (Order.one_le_iff_ne_zero.2 (hf₂.analyticOrderAt_ne_zero.2 hf₂0))
    · obtain ⟨α, -, hα⟩ := exists_toFilterGerm_eq x a
      obtain ⟨β, -, hβ⟩ := exists_toFilterGerm_eq x b
      have hev : ψ =ᶠ[𝓝 x] α + β := Germ.coe_eq.1 (by rw [← hψ, map_add, hα, hβ, Germ.coe_add])
      have hcongr : (fun z : ℂ ↦ ψ (e.symm (e x + z • v))) =ᶠ[𝓝 0]
          (fun z ↦ α (e.symm (e x + z • v))) + fun z ↦ β (e.symm (e x + z • v)) :=
        hline.eventually hev
      rw [analyticOrderAt_congr hcongr]
      exact (le_min (ha α (hα _ le_rfl)) (hb β (hβ _ le_rfl))).trans le_analyticOrderAt_add

include he in
/-- At the center of a complex analytic chart, the powers of the evaluation kernel have trivial
intersection. -/
theorem iInf_pow_ker_eval_eq_bot {x : X} (hx : x ∈ e.source) :
    (⨅ n : ℕ, RingHom.ker (eval 𝓘(ℂ, E) X x) ^ n) = ⊥ := by
  refine eq_bot_iff.2 fun s hs ↦ Ideal.mem_bot.2 ?_
  obtain ⟨φ, -, hφ⟩ := exists_toFilterGerm_eq x s
  have hφe : AnalyticAt ℂ (φ ∘ e.symm) (e x) := by
    simpa using ((exists_toFilterGerm_nhds_eq_iff.1 ⟨s, hφ _ le_rfl⟩).self_of_nhds
      |>.analyticAt_comp_extend_symm he hx)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 (isOpen_analyticAt ℂ (φ ∘ e.symm)) (e x) hφe
  have hline_zero (v : E) : ∀ᶠ z : ℂ in 𝓝 0, φ (e.symm (e x + z • v)) = 0 := by
    rw [← analyticOrderAt_eq_top]
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
    exact (Nat.lt_succ_self m).not_ge <| ENat.natCast_le_natCast.1 <| hm ▸
      natCast_le_analyticOrderAt_line_of_mem_pow_ker_eval e he hx
        (Ideal.mem_iInf.1 hs (m + 1)) (hφ _ le_rfl) v
  have hzero_on_ball : ∀ y ∈ ball (e x) r, (φ ∘ e.symm) y = 0 := fun y hy ↦ by
    set v := y - e x
    rcases eq_or_ne v 0 with hv0 | hv0
    · simpa [sub_eq_zero.1 hv0] using (hline_zero 0).self_of_nhds
    · have hv_pos : 0 < ‖v‖ := norm_pos_iff.2 hv0
      have h1R : 1 < r / ‖v‖ := (one_lt_div hv_pos).2 (by simpa [v, dist_eq_norm] using hy)
      have hg_an : AnalyticOnNhd ℂ (fun z : ℂ ↦ (φ ∘ e.symm) (e x + z • v)) (ball 0 (r / ‖v‖)) :=
        fun z hz ↦ (hball (by
          rw [mem_ball, dist_self_add_left, norm_smul]
          exact (mul_lt_mul_of_pos_right (by simpa using hz) hv_pos).trans_eq
            (div_mul_cancel₀ r hv_pos.ne'))).comp_of_eq (by fun_prop) rfl
      simpa [v] using hg_an.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        (convex_ball (0 : ℂ) (r / ‖v‖)).isPreconnected (mem_ball_self (zero_lt_one.trans h1R))
        (hline_zero v) (mem_ball_zero_iff.2 ((norm_one (α := ℂ)).trans_lt h1R))
  apply toFilterGerm_nhds_injective x
  rw [hφ _ le_rfl, map_zero, ← Germ.coe_zero, Germ.coe_eq]
  filter_upwards [e.open_source.mem_nhds hx, (e.continuousAt hx).eventually (ball_mem_nhds _ hr)]
    with y hys hyb
  simpa only [Function.comp_apply, e.left_inv hys, Pi.zero_apply] using hzero_on_ball (e y) hyb

include he in
/-- At the center of a complex analytic chart, the holomorphic stalk is Hausdorff with respect to
its maximal ideal. -/
theorem isHausdorff_maximalIdeal_stalk {x : X} (hx : x ∈ e.source) :
    IsHausdorff
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x))
      ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) := by
  refine ⟨fun s hs ↦ Ideal.mem_bot.1 ?_⟩
  rw [← iInf_pow_ker_eval_eq_bot e he hx, Ideal.mem_iInf]
  intro n
  simpa [maximalIdeal_stalk, smul_eq_mul, Ideal.mul_top, SModEq.zero] using hs n

end OpenPartialHomeomorph

namespace TauCeti.holomorphicStructureSheaf

section Omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) ω X]

/-- On a complex analytic manifold (without assuming finite-dimensionality), the powers of the
evaluation kernel on any holomorphic stalk have trivial intersection. -/
@[simp]
theorem iInf_pow_ker_eval_eq_bot_of_omega (x : X) :
    (⨅ n : ℕ, RingHom.ker (eval 𝓘(ℂ, E) X x) ^ n) = ⊥ :=
  (chartAt E x).iInf_pow_ker_eval_eq_bot (chart_mem_maximalAtlas x) (mem_chart_source E x)

/-- On a complex analytic manifold (without assuming finite-dimensionality), the powers of the
maximal ideal of any holomorphic stalk have trivial intersection. -/
theorem iInf_pow_maximalIdeal_stalk_eq_bot_of_omega (x : X) :
    (⨅ n : ℕ,
      IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) ^ n) =
      ⊥ := by
  simp

/-- On a complex analytic manifold (without assuming finite-dimensionality), every holomorphic
stalk is Hausdorff with respect to its maximal ideal. -/
instance instIsHausdorffMaximalIdealStalkOfOmega (x : X) :
    IsHausdorff
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x))
      ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) :=
  (chartAt E x).isHausdorff_maximalIdeal_stalk (chart_mem_maximalAtlas x) (mem_chart_source E x)

end Omega

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {X : Type} [TopologicalSpace X] [ChartedSpace E X] [IsManifold 𝓘(ℂ, E) 1 X]

/-- On a finite-dimensional complex manifold, the powers of the maximal ideal of any holomorphic
stalk have trivial intersection. -/
theorem iInf_pow_maximalIdeal_stalk_eq_bot (x : X) :
    (⨅ n : ℕ,
      IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) ^ n) =
      ⊥ := by
  let : IsManifold 𝓘(ℂ, E) ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  exact iInf_pow_maximalIdeal_stalk_eq_bot_of_omega x

/-- On a finite-dimensional complex manifold, every holomorphic stalk is Hausdorff with respect to
its maximal ideal. -/
instance instIsHausdorffMaximalIdealStalk (x : X) :
    IsHausdorff
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x))
      ((holomorphicStructureSheaf 𝓘(ℂ, E) X).presheaf.stalk x) := by
  let : IsManifold 𝓘(ℂ, E) ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  infer_instance

end FiniteDimensional

end TauCeti.holomorphicStructureSheaf
