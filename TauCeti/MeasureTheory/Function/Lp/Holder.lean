/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import TauCeti.MeasureTheory.Function.Lp.Restriction

/-!
# Convergence of Hölder bilinear products

Continuous bilinear maps send convergent pairs of `Lp` classes at Hölder exponents to convergent
products. On finite-measure subsets, this gives convergence in the `L¹` distance of arbitrary
almost-everywhere representatives.

Hölder multiplication also preserves compactness. If `V : X → L^q` is a compact operator and
`ι : X → L^s` is a bounded operator with the same values, then for `a ∈ L^p` with `p < ∞` and
`1/p + 1/s = 1/q` the operator `u ↦ B(a, ι u) : X → L^q` is compact, although `ι` itself need not
be. For a simple function `a`, which lies in `L^∞`, the operator factors through `V`. Simple
functions are dense in `L^p`, the operator depends continuously on `a`, and compact operators form
a closed set.
-/


public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace ContinuousLinearMap

/-- A Hölder product agrees with the bilinear product of chosen representatives for any
dominated measure. -/
theorem holderL_ae_eq_of_measure_le {E F G H : Type*} [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {μ : Measure E} {p q r : ENNReal}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [ENNReal.HolderTriple p q r]
    (B : F →L[ℝ] G →L[ℝ] H) {ν : Measure E} (hν : ν ≤ μ)
    (a : Lp F p μ) (c : Lp G q μ)
    {f : E → F} {g : E → G} (ha : a =ᵐ[ν] f) (hc : c =ᵐ[ν] g) :
    B.holderL μ p q r a c =ᵐ[ν] fun x => B (f x) (g x) := by
  filter_upwards [(B.coeFn_holder (r := r) a c).filter_mono (ae_mono hν), ha, hc] with x h₁ h₂ h₃
  exact h₁.trans (congrArg₂ (fun u v => B u v) h₂ h₃)

/-- **Hölder multiplication preserves compactness.** Let `V : X → L^q` be a compact operator and
`ι : X → L^s` a bounded operator with the same values. For `a ∈ L^p` with `p < ∞` and
`1/p + 1/s = 1/q`, the operator `u ↦ B(a, ι u) : X → L^q` is compact.

The operator `ι` need not be compact: in the application to Sobolev spaces it is a critical
Sobolev embedding, while `V` is the Rellich--Kondrachov embedding. -/
theorem isCompactOperator_holderL_comp_of_ae_eq {α X E F G : Type*} [MeasurableSpace α]
    {μ : Measure α} [SeminormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G] {p s q : ENNReal}
    [Fact (1 ≤ p)] [Fact (1 ≤ s)] [Fact (1 ≤ q)] [ENNReal.HolderTriple p s q]
    (B : E →L[ℝ] F →L[ℝ] G) (hp : p ≠ ∞) {V : X →L[ℝ] Lp F q μ} (hV : IsCompactOperator V)
    (ι : X →L[ℝ] Lp F s μ) (hι : ∀ u, ι u =ᵐ[μ] V u) (a : Lp E p μ) :
    IsCompactOperator ((B.holderL μ p s q a).comp ι) := by
  -- The operator depends continuously and linearly on the multiplier.
  let Φ : Lp E p μ →L[ℝ] X →L[ℝ] Lp G q μ :=
    ((ContinuousLinearMap.compL ℝ X (Lp F s μ) (Lp G q μ)).flip ι).comp (B.holderL μ p s q)
  change IsCompactOperator (Φ a)
  refine (Lp.simpleFunc.denseRange hp).induction_on a
    (isClosed_setOfPred_isCompactOperator.preimage Φ.continuous) fun f => ?_
  -- A simple multiplier lies in `L^∞`, so the operator factors through `V`.
  let g : Lp E ∞ μ := (SimpleFunc.memLp_top (Lp.simpleFunc.toSimpleFunc f) μ).toLp _
  have hfac : Φ f = (B.holderL μ ∞ q q g).comp V := by
    ext u : 1
    apply Lp.ext
    filter_upwards [B.coeFn_holder (r := q) (f : Lp E p μ) (ι u),
      B.coeFn_holder (r := q) g (V u), hι u, Lp.simpleFunc.toSimpleFunc_eq_toFun f,
      MemLp.coeFn_toLp (SimpleFunc.memLp_top (Lp.simpleFunc.toSimpleFunc f) μ)]
      with x h₁ h₂ h₃ h₄ h₅
    simp only [Φ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.holderL_apply_apply]
    rw [h₁, h₂, h₃, h₅, h₄]
  rw [hfac]
  exact hV.clm_comp (B.holderL μ ∞ q q g)

end ContinuousLinearMap

namespace TauCeti

/-- Hölder bilinear products of convergent `Lp` classes converge in `L¹` on finite-measure sets,
with the limits and approximants stated for arbitrary almost-everywhere representatives. -/
theorem tendsto_setLIntegral_enorm_bilin_sub {E F G H ι : Type*} [MeasurableSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H] {μ : Measure E} {p q r : ENNReal}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)] [ENNReal.HolderTriple p q r]
    (B : F →L[ℝ] G →L[ℝ] H) {W : Set E} (hW : μ W < ⊤)
    {l : Filter ι} {A : ι → Lp F p μ} {A₀ : Lp F p μ}
    {C : ι → Lp G q μ} {C₀ : Lp G q μ}
    (hA : Tendsto A l (𝓝 A₀)) (hC : Tendsto C l (𝓝 C₀))
    {a : ι → E → F} {a₀ : E → F} {c : ι → E → G} {c₀ : E → G}
    (ha : ∀ n, A n =ᵐ[μ] a n) (ha₀ : A₀ =ᵐ[μ.restrict W] a₀)
    (hc : ∀ n, C n =ᵐ[μ] c n) (hc₀ : C₀ =ᵐ[μ.restrict W] c₀) :
    Tendsto (fun n => ∫⁻ x in W, ‖B (a n x) (c n x) - B (a₀ x) (c₀ x)‖ₑ ∂μ) l (𝓝 0) := by
  have ht := ((B.holderL μ p q r).continuous₂.tendsto (A₀, C₀)).comp (hA.prodMk_nhds hC)
  apply tendsto_setLIntegral_enorm_sub_of_tendsto_Lp hW ht
  · intro n
    filter_upwards [B.coeFn_holder (r := r) (A n) (C n), ha n, hc n] with x h₁ h₂ h₃
    exact h₁.trans (congrArg₂ (fun u v => B u v) h₂ h₃)
  · exact B.holderL_ae_eq_of_measure_le Measure.restrict_le_self A₀ C₀ ha₀ hc₀

end TauCeti
