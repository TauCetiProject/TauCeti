/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import TauCeti.MeasureTheory.Function.Lp.Indicator

/-!
# Elements of a Bochner space of `Lʳ` functions with integrable `Lˢ`-valued representatives

An element `Φ` of the Bochner space `L^p(ρ; L^r(μ))` is a class of functions `α → L^r(μ)`. A family
`G : α → L^s(μ)` for a second exponent `s` represents `Φ` when `Φ(b) = G(b)` almost everywhere for
almost every `b`. Such representatives are unique almost everywhere
(`MeasureTheory.Lp.ae_eq_of_ae_ae_eq`) and are compatible with addition and scalar multiplication
(`MeasureTheory.Lp.ae_ae_eq_add`, `MeasureTheory.Lp.ae_ae_eq_smul`).

The elements with a representative integrable for `ρ` form the submodule
`MeasureTheory.Lp.integrableRepSubmodule 𝕜 F r μ p ρ s`. For finite `p` and `r` and Lebesgue-type
measures `μ` on a finite-dimensional space it is dense
(`MeasureTheory.Lp.dense_integrableRepSubmodule`): the indicators `1_A c` of sets of finite measure
span a dense subspace of `L^p(ρ; L^r(μ))`, and every `c ∈ L^r(μ)` is a limit of Schwartz functions,
which lie in every `L^s(μ)`. For `s = 2` this lets operators defined on `L²`-valued forcings, such
as Duhamel integrals of dispersive equations, extend by continuity to the whole Bochner space.
-/

public section

noncomputable section

open Filter Set Topology
open scoped ENNReal

namespace MeasureTheory

namespace Lp

variable {𝕜 α X F : Type*} [NormedRing 𝕜] {mX : MeasurableSpace X} [NormedAddCommGroup F]
  [Module 𝕜 F] [IsBoundedSMul 𝕜 F] {r : ℝ≥0∞} {μ : Measure X} {p : ℝ≥0∞} {mα : MeasurableSpace α}
  {ρ : Measure α} {s : ℝ≥0∞} [Fact (1 ≤ r)]

/-- Two `Lˢ`-valued representatives of the same element of `L^p(ρ; L^r(μ))` agree almost
everywhere. -/
theorem ae_eq_of_ae_ae_eq {Φ : Lp (Lp F r μ) p ρ} {G H : α → Lp F s μ}
    (hG : ∀ᵐ b ∂ρ, (Φ b : X → F) =ᵐ[μ] G b) (hH : ∀ᵐ b ∂ρ, (Φ b : X → F) =ᵐ[μ] H b) :
    G =ᵐ[ρ] H := by
  filter_upwards [hG, hH] with b h₁ h₂
  exact Lp.ext (h₁.symm.trans h₂)

/-- If `G` and `H` represent `Φ, Ψ ∈ L^p(ρ; L^r(μ))`, then `G + H` represents `Φ + Ψ`. -/
theorem ae_ae_eq_add {Φ Ψ : Lp (Lp F r μ) p ρ} {G H : α → Lp F s μ}
    (hG : ∀ᵐ b ∂ρ, (Φ b : X → F) =ᵐ[μ] G b) (hH : ∀ᵐ b ∂ρ, (Ψ b : X → F) =ᵐ[μ] H b) :
    ∀ᵐ b ∂ρ, ((Φ + Ψ) b : X → F) =ᵐ[μ] (G + H) b := by
  filter_upwards [Lp.coeFn_add Φ Ψ, hG, hH] with b hb h₁ h₂
  rw [hb]
  filter_upwards [Lp.coeFn_add (Φ b) (Ψ b), Lp.coeFn_add (G b) (H b), h₁, h₂] with x hx₁ hx₂
    hx₃ hx₄
  simp only [Pi.add_apply] at hx₁ hx₂ ⊢
  rw [hx₁, hx₂, hx₃, hx₄]

/-- If `G` represents `Φ ∈ L^p(ρ; L^r(μ))`, then `c • G` represents `c • Φ`. -/
theorem ae_ae_eq_smul {Φ : Lp (Lp F r μ) p ρ} {G : α → Lp F s μ}
    (hG : ∀ᵐ b ∂ρ, (Φ b : X → F) =ᵐ[μ] G b) (c : 𝕜) :
    ∀ᵐ b ∂ρ, ((c • Φ) b : X → F) =ᵐ[μ] (c • G) b := by
  filter_upwards [Lp.coeFn_smul c Φ, hG] with b hb h
  rw [hb]
  filter_upwards [Lp.coeFn_smul c (Φ b), Lp.coeFn_smul c (G b), h] with x h₁ h₂ h₃
  simp only [Pi.smul_apply] at h₁ h₂ ⊢
  rw [h₁, h₂, h₃]

variable [Fact (1 ≤ s)]

variable (𝕜 F r μ p ρ s) in
/-- The elements `Φ` of the Bochner space `L^p(ρ; L^r(μ))` with a representative
`G : α → L^s(μ)` integrable for `ρ`: `Φ(b) = G(b)` almost everywhere for almost every `b`. -/
def integrableRepSubmodule : Submodule 𝕜 (Lp (Lp F r μ) p ρ) where
  carrier := {Φ | ∃ G : α → Lp F s μ, Integrable G ρ ∧ ∀ᵐ b ∂ρ, (Φ b : X → F) =ᵐ[μ] G b}
  add_mem' := by
    rintro Φ Ψ ⟨G, hG, hΦ⟩ ⟨H, hH, hΨ⟩
    exact ⟨G + H, hG.add hH, ae_ae_eq_add hΦ hΨ⟩
  zero_mem' := ⟨0, integrable_zero _ _ _, by
    filter_upwards [Lp.coeFn_zero (Lp F r μ) p ρ] with b hb
    rw [hb]
    filter_upwards [Lp.coeFn_zero F r μ, Lp.coeFn_zero F s μ] with x h₁ h₂
    simp only [Pi.zero_apply] at h₁ h₂ ⊢
    rw [h₁, h₂]⟩
  smul_mem' := by
    rintro c Φ ⟨G, hG, hΦ⟩
    exact ⟨c • G, hG.smul c, ae_ae_eq_smul hΦ c⟩

/-- `Φ` lies in `integrableRepSubmodule 𝕜 F r μ p ρ s` when it has an `Lˢ`-valued representative
integrable for `ρ`. -/
theorem mem_integrableRepSubmodule_iff {Φ : Lp (Lp F r μ) p ρ} :
    Φ ∈ integrableRepSubmodule 𝕜 F r μ p ρ s ↔
      ∃ G : α → Lp F s μ, Integrable G ρ ∧ ∀ᵐ b ∂ρ, (Φ b : X → F) =ᵐ[μ] G b :=
  Iff.rfl

/-- For finite `p` and `r`, the elements of `L^p(ρ; L^r(μ))` with an integrable `Lˢ`-valued
representative are dense, when `μ` is a measure of temperate growth, finite on compact sets, on a
finite-dimensional real normed space: the indicators `1_A c` of sets of finite measure span a dense
subspace, and `c ∈ L^r(μ)` is a limit of Schwartz functions, which lie in `L^s(μ)`. -/
theorem dense_integrableRepSubmodule {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
    [μ.HasTemperateGrowth] [IsFiniteMeasureOnCompacts μ] [NormedSpace ℝ F] [Fact (1 ≤ p)]
    (hp : p ≠ ∞) (hr : r ≠ ∞) :
    Dense (integrableRepSubmodule 𝕜 F r μ p ρ s : Set (Lp (Lp F r μ) p ρ)) := by
  intro Φ
  induction Φ using Lp.induction hp with
  | @indicatorConst c A hA hρA =>
    rw [Lp.simpleFunc.coe_indicatorConst, ← TauCeti.indicatorConstLpL_apply (𝕜 := ℝ)]
    refine map_mem_closure (TauCeti.indicatorConstLpL ℝ p hA hρA.ne).continuous
      (SchwartzMap.denseRange_toLpCLM (F := F) (μ := μ) hr c) ?_
    rintro _ ⟨φ, rfl⟩
    rw [TauCeti.indicatorConstLpL_apply]
    refine ⟨A.indicator fun _ ↦ φ.toLp s μ,
      (integrable_indicator_iff hA).2 (integrableOn_const hρA.ne eNorm_ne_top), ?_⟩
    filter_upwards [indicatorConstLp_coeFn (p := p) (hs := hA) (hμs := hρA.ne)
      (c := SchwartzMap.toLpCLM ℝ F r μ φ)] with b hb
    rw [hb]
    by_cases hbA : b ∈ A
    · simp only [indicator_of_mem hbA, SchwartzMap.toLpCLM_apply]
      exact (φ.coeFn_toLp r μ).trans (φ.coeFn_toLp s μ).symm
    · simp only [indicator_of_notMem hbA]
      exact (Lp.coeFn_zero F r μ).trans (Lp.coeFn_zero F s μ).symm
  | add _ _ _ hf hg =>
    rw [← Submodule.topologicalClosure_coe] at hf hg ⊢
    exact Submodule.add_mem _ hf hg
  | isClosed => exact isClosed_closure

end Lp

end MeasureTheory
