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
import TauCeti.Analysis.Analytic.Uniqueness
import TauCeti.Geometry.Manifold.Complex.Analytic
import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ
import TauCeti.Geometry.Manifold.ContMDiff.Analytic

/-!
# Maximal-ideal separatedness of holomorphic stalks

Let `X` be a complex analytic manifold modelled without boundary on a complex normed space `E`
via any boundaryless `ModelWithCorners ℂ E H`. This file proves that the stalk
`(holomorphicStructureSheaf I X).presheaf.stalk x` is separated (`IsHausdorff`) with respect to
its maximal ideal: a holomorphic germ lying in every power of the maximal ideal is zero.

The argument requires neither finite-dimensionality of `E` nor Noetherianity of the stalk (so
Krull's intersection theorem is not needed). If a germ `s` lies in `𝔪_x ^ n`, restricting any local
representative of `s` read in an extended holomorphic chart `e.extend I` to any complex line
`z ↦ e.extend I x + z • v` through `e.extend I x` produces a one-variable holomorphic function
vanishing to order at least `n` at `0`. Lying in `𝔪_x ^ n` for every `n` therefore forces infinite
analytic order at `0` along every complex line, hence vanishing near `e.extend I x` by one-variable
analytic continuation along radial discs
(`AnalyticAt.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul`). For finite-dimensional
`E`, every `C^1` complex manifold is automatically `C^ω`, giving the `[IsManifold I 1 X]` instance
as an immediate specialization. (For complex curves `E = ℂ`,
`TauCeti.Geometry.Manifold.Complex.StructureSheaf.Order` obtains separatedness from local
coordinate division instead.)

## Main results

* `OpenPartialHomeomorph.iInf_pow_ker_eval_eq_bot`: at any point `x ∈ e.source` of an analytic
  chart `e ∈ maximalAtlas I ω X` for a boundaryless model `I`, the intersection of all powers of
  `RingHom.ker (eval I X x)` is `⊥`.
* `OpenPartialHomeomorph.isHausdorff_maximalIdeal_stalk`: at any point `x ∈ e.source` of an
  analytic chart `e`, the stalk at `x` is `IsHausdorff` with respect to its maximal ideal.
* `TauCeti.holomorphicStructureSheaf.instIsHausdorffMaximalIdealStalkOfOmega`: `IsHausdorff`
  instance on stalks of any boundaryless complex analytic manifold
  `[I.Boundaryless] [IsManifold I ω X]`, with no finite-dimensionality assumption on `E`.
* `TauCeti.holomorphicStructureSheaf.instIsHausdorffMaximalIdealStalk`: `IsHausdorff` instance on
  stalks of any finite-dimensional boundaryless complex manifold
  `[FiniteDimensional ℂ E] [I.Boundaryless] [IsManifold I 1 X]`.

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
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X]
  (e : OpenPartialHomeomorph X H) (he : e ∈ maximalAtlas I ω X)

include he in
/-- Reading any representative of a holomorphic germ at `x` in the extended chart `e.extend I`
along a complex line through `e.extend I x` gives a function analytic at `0`. -/
private theorem analyticAt_line_of_toFilterGerm_eq {x : X} (hx : x ∈ e.source)
    {s : (holomorphicStructureSheaf I X).presheaf.stalk x} {φ : X → ℂ}
    (hφ : toFilterGerm I X x (𝓝 x) le_rfl s = φ) (v : E) :
    AnalyticAt ℂ (fun z : ℂ ↦ φ ((e.extend I).symm (e.extend I x + z • v))) 0 := by
  have hφe : AnalyticAt ℂ (φ ∘ (e.extend I).symm) (e.extend I x) := by
    simpa only [OpenPartialHomeomorph.extend_coe, Function.comp_apply] using
      ((exists_toFilterGerm_nhds_eq_iff.1 ⟨s, hφ⟩).self_of_nhds.analyticAt_comp_extend_symm he hx)
  exact hφe.comp_of_eq (by fun_prop) (by simp)

include he in
/-- Every representative of a germ in `RingHom.ker (eval I X x) ^ n` vanishes to analytic order at
least `n` at `0` along every complex line through `e.extend I x` in the extended chart
`e.extend I`. -/
private theorem natCast_le_analyticOrderAt_line_of_mem_pow_ker_eval {x : X} (hx : x ∈ e.source) :
    ∀ {n : ℕ} {s : (holomorphicStructureSheaf I X).presheaf.stalk x},
      s ∈ RingHom.ker (eval I X x) ^ n →
      ∀ {φ : X → ℂ}, toFilterGerm I X x (𝓝 x) le_rfl s = φ →
      ∀ v : E,
        (n : ℕ∞) ≤ analyticOrderAt (fun z : ℂ ↦ φ ((e.extend I).symm (e.extend I x + z • v))) 0
  | 0, _, _, _, _, _ => by simp
  | n + 1, s, hs, φ, hφ, v => by
    have hline : Tendsto (fun z : ℂ ↦ (e.extend I).symm (e.extend I x + z • v)) (𝓝 0) (𝓝 x) := by
      simpa only [Function.comp_def, e.extend_left_inv hx] using
        (e.continuousAt_extend_symm hx).tendsto.comp
          (by simpa using (by fun_prop : Continuous fun z : ℂ ↦ e.extend I x + z • v).tendsto 0)
    rw [pow_succ] at hs
    refine Submodule.mul_induction_on
      (C := fun t ↦ ∀ ψ : X → ℂ, toFilterGerm I X x (𝓝 x) le_rfl t = ψ →
        ((n + 1 : ℕ) : ℕ∞) ≤
          analyticOrderAt (fun z : ℂ ↦ ψ ((e.extend I).symm (e.extend I x + z • v))) 0)
      hs (fun a ha b hb ψ hψ ↦ ?_) (fun a b ha hb ψ hψ ↦ ?_) φ hφ
    · obtain ⟨α, -, hα⟩ := exists_toFilterGerm_eq x a
      obtain ⟨β, -, hβ⟩ := exists_toFilterGerm_eq x b
      have hf₁ := analyticAt_line_of_toFilterGerm_eq e he hx (hα _ le_rfl) v
      have hf₂ := analyticAt_line_of_toFilterGerm_eq e he hx (hβ _ le_rfl) v
      have hev : ψ =ᶠ[𝓝 x] α * β := Germ.coe_eq.1 (by rw [← hψ, map_mul, hα, hβ, Germ.coe_mul])
      have hcongr : (fun z : ℂ ↦ ψ ((e.extend I).symm (e.extend I x + z • v))) =ᶠ[𝓝 0]
          (fun z ↦ α ((e.extend I).symm (e.extend I x + z • v))) *
            fun z ↦ β ((e.extend I).symm (e.extend I x + z • v)) :=
        hline.eventually hev
      have hf₂0 : β ((e.extend I).symm (e.extend I x + (0 : ℂ) • v)) = 0 := by
        simpa only [zero_smul, add_zero, e.extend_left_inv hx] using
          (eval_eq_of_toFilterGerm_eq (hβ _ le_rfl)).symm.trans hb
      rw [analyticOrderAt_congr hcongr, analyticOrderAt_mul hf₁ hf₂, Nat.cast_add, Nat.cast_one]
      exact add_le_add (natCast_le_analyticOrderAt_line_of_mem_pow_ker_eval hx ha (hα _ le_rfl) v)
        (Order.one_le_iff_ne_zero.2 (hf₂.analyticOrderAt_ne_zero.2 hf₂0))
    · obtain ⟨α, -, hα⟩ := exists_toFilterGerm_eq x a
      obtain ⟨β, -, hβ⟩ := exists_toFilterGerm_eq x b
      have hev : ψ =ᶠ[𝓝 x] α + β := Germ.coe_eq.1 (by rw [← hψ, map_add, hα, hβ, Germ.coe_add])
      have hcongr : (fun z : ℂ ↦ ψ ((e.extend I).symm (e.extend I x + z • v))) =ᶠ[𝓝 0]
          (fun z ↦ α ((e.extend I).symm (e.extend I x + z • v))) +
            fun z ↦ β ((e.extend I).symm (e.extend I x + z • v)) :=
        hline.eventually hev
      rw [analyticOrderAt_congr hcongr]
      exact (le_min (ha α (hα _ le_rfl)) (hb β (hβ _ le_rfl))).trans le_analyticOrderAt_add

include he in
/-- At any point of the source of a complex analytic chart for a boundaryless model, the powers of
the evaluation kernel have trivial intersection. -/
theorem iInf_pow_ker_eval_eq_bot {x : X} (hx : x ∈ e.source) :
    (⨅ n : ℕ, RingHom.ker (eval I X x) ^ n) = ⊥ := by
  refine eq_bot_iff.2 fun s hs ↦ Ideal.mem_bot.2 ?_
  obtain ⟨φ, -, hφ⟩ := exists_toFilterGerm_eq x s
  have hφe : AnalyticAt ℂ (φ ∘ (e.extend I).symm) (e.extend I x) := by
    simpa only [OpenPartialHomeomorph.extend_coe, Function.comp_apply] using
      ((exists_toFilterGerm_nhds_eq_iff.1 ⟨s, hφ _ le_rfl⟩).self_of_nhds.analyticAt_comp_extend_symm
        he hx)
  have hline_zero (v : E) : ∀ᶠ z : ℂ in 𝓝 0, φ ((e.extend I).symm (e.extend I x + z • v)) = 0 := by
    rw [← analyticOrderAt_eq_top]
    by_contra hne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.1 hne
    exact (Nat.lt_succ_self m).not_ge <| ENat.natCast_le_natCast.1 <| hm ▸
      natCast_le_analyticOrderAt_line_of_mem_pow_ker_eval e he hx
        (Ideal.mem_iInf.1 hs (m + 1)) (hφ _ le_rfl) v
  have h0 : φ ∘ (e.extend I).symm =ᶠ[𝓝 (e.extend I x)] 0 :=
    hφe.eventuallyEq_zero_iff_forall_eventuallyEq_zero_comp_add_smul.2 hline_zero
  refine (eq_zero_iff_of_toFilterGerm_eq (hφ _ le_rfl)).2 ?_
  filter_upwards [e.open_source.mem_nhds hx, (e.continuousAt_extend hx).eventually h0] with
    y hys hy0
  simpa only [Function.comp_apply, e.extend_left_inv hys, Pi.zero_apply] using hy0

include he in
/-- At any point of the source of a complex analytic chart for a boundaryless model, the
holomorphic stalk is Hausdorff with respect to its maximal ideal. -/
theorem isHausdorff_maximalIdeal_stalk {x : X} (hx : x ∈ e.source) :
    IsHausdorff
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x))
      ((holomorphicStructureSheaf I X).presheaf.stalk x) := by
  refine ⟨fun s hs ↦ Ideal.mem_bot.1 ?_⟩
  rw [← iInf_pow_ker_eval_eq_bot e he hx, Ideal.mem_iInf]
  intro n
  simpa [maximalIdeal_stalk, smul_eq_mul, Ideal.mul_top, SModEq.zero] using hs n

end OpenPartialHomeomorph

namespace TauCeti.holomorphicStructureSheaf

section Omega

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ω X]

/-- On a boundaryless complex analytic manifold (without assuming finite-dimensionality), the
powers of the evaluation kernel on any holomorphic stalk have trivial intersection. -/
@[simp]
theorem iInf_pow_ker_eval_eq_bot_of_omega (x : X) :
    (⨅ n : ℕ, RingHom.ker (eval I X x) ^ n) = ⊥ :=
  (chartAt H x).iInf_pow_ker_eval_eq_bot (chart_mem_maximalAtlas x) (mem_chart_source H x)

/-- On a boundaryless complex analytic manifold (without assuming finite-dimensionality), the
powers of the maximal ideal of any holomorphic stalk have trivial intersection. -/
theorem iInf_pow_maximalIdeal_stalk_eq_bot_of_omega (x : X) :
    (⨅ n : ℕ,
      IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x) ^ n) =
      ⊥ := by
  simp

/-- On a boundaryless complex analytic manifold (without assuming finite-dimensionality), every
holomorphic stalk is Hausdorff with respect to its maximal ideal. -/
instance instIsHausdorffMaximalIdealStalkOfOmega (x : X) :
    IsHausdorff
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x))
      ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  (chartAt H x).isHausdorff_maximalIdeal_stalk (chart_mem_maximalAtlas x) (mem_chart_source H x)

end Omega

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℂ E H} [I.Boundaryless]
  {X : Type} [TopologicalSpace X] [ChartedSpace H X] [IsManifold I 1 X]

/-- On a finite-dimensional boundaryless complex manifold, every holomorphic stalk is Hausdorff with
respect to its maximal ideal. -/
instance instIsHausdorffMaximalIdealStalk (x : X) :
    IsHausdorff
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x))
      ((holomorphicStructureSheaf I X).presheaf.stalk x) :=
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  instIsHausdorffMaximalIdealStalkOfOmega x

/-- On a finite-dimensional boundaryless complex manifold, the powers of the maximal ideal of any
holomorphic stalk have trivial intersection. -/
theorem iInf_pow_maximalIdeal_stalk_eq_bot (x : X) :
    (⨅ n : ℕ,
      IsLocalRing.maximalIdeal ((holomorphicStructureSheaf I X).presheaf.stalk x) ^ n) = ⊥ :=
  let : IsManifold I ω X := IsManifold.of_ne_zero ω one_ne_zero inferInstance
  iInf_pow_maximalIdeal_stalk_eq_bot_of_omega x

end FiniteDimensional

end TauCeti.holomorphicStructureSheaf
