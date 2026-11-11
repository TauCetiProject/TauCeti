/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Positive.FunctionalCalculus
public import TauCeti.Analysis.InnerProductSpace.Positive.MetricChange.Composition
public import TauCeti.Analysis.Calculus.Bilinear

/-!
# Smooth dependence of metric-change transports

The canonical inverse-square-root transport of a positive real bilinear form, and its
square-root inverse, depend smoothly on that form in finite dimension. Consequently a smooth
family of positive metrics gives a smooth family of transports. The same holds for transport
between two varying metrics, including noncommuting ones.

These results apply in fixed local bundle coordinates. They concern the existing native
operators `ContinuousLinearMap.metricChangeTransport` and `metricChangeBetween`; they do not
choose eigenbases or install a new inner product. Smoothness is within the positive cone,
so a parameterized statement retains positivity throughout the parameter set.

The construction uses the inverse-square-root metric transport and its composition comparison,
and the exponential/logarithm proof of smooth matrix powers. See R. Bhatia,
*Positive Definite Matrices*, Chapter 1, for positive square roots and congruences of metrics.
-/

public section

open InnerProductSpace
open scoped ContDiff

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n : ℕ∞ω}

local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

/-- The canonical inverse-square-root metric transport is smooth on positive metrics in
finite dimension, including real analyticity. -/
theorem contDiffOn_metricChangeTransport :
    ContDiffOn ℝ n (metricChangeTransport : (E →L[ℝ] E →L[ℝ] ℝ) → E →L[ℝ] E)
      {h | IsStrictlyPositive h♯} := by
  have h := (contDiffOn_rpow (E := E) (n := n) (-(1 / 2))).comp
    (contDiff_continuousLinearMapOfBilin.contDiffOn (s := {h | IsStrictlyPositive h♯}))
    (fun _ hh ↦ hh)
  exact h.congr fun h _ ↦ metricChangeTransport_def h

/-- The inverse transport, the positive square root of the Riesz operator, is smooth on
positive metrics in finite dimension. -/
theorem contDiffOn_sqrt_continuousLinearMapOfBilin :
    ContDiffOn ℝ n (fun h : E →L[ℝ] E →L[ℝ] ℝ ↦ CFC.sqrt h♯)
      {h | IsStrictlyPositive h♯} :=
  contDiffOn_sqrt.comp contDiff_continuousLinearMapOfBilin.contDiffOn (fun _ hh ↦ hh)

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {s : Set P} {h k : P → E →L[ℝ] E →L[ℝ] ℝ}

/-- A smooth family of positive metrics has a smooth family of canonical transports. -/
theorem _root_.ContDiffOn.metricChangeTransport (hh : ContDiffOn ℝ n h s)
    (hpos : ∀ x ∈ s, IsStrictlyPositive (h x)♯) :
    ContDiffOn ℝ n (fun x ↦ (h x).metricChangeTransport) s :=
  contDiffOn_metricChangeTransport.comp hh hpos

/-- A smooth family of positive metrics has a smooth family of inverse transports. -/
theorem _root_.ContDiffOn.sqrt_continuousLinearMapOfBilin (hh : ContDiffOn ℝ n h s)
    (hpos : ∀ x ∈ s, IsStrictlyPositive (h x)♯) :
    ContDiffOn ℝ n (fun x ↦ CFC.sqrt (h x)♯) s :=
  contDiffOn_sqrt_continuousLinearMapOfBilin.comp hh hpos

/-- Canonical transport between two smoothly varying positive metrics is smooth. No
commutation hypothesis on their Riesz operators is needed. -/
theorem _root_.ContDiffOn.metricChangeBetween (hh : ContDiffOn ℝ n h s)
    (hk : ContDiffOn ℝ n k s)
    (hpos : ∀ x ∈ s, IsStrictlyPositive (h x)♯)
    (kpos : ∀ x ∈ s, IsStrictlyPositive (k x)♯) :
    ContDiffOn ℝ n (fun x ↦ (h x).metricChangeBetween (k x)) s := by
  have hT := hh.metricChangeTransport hpos
  have hS := hh.sqrt_continuousLinearMapOfBilin hpos
  have hK : ContDiffOn ℝ n (fun x ↦
      (k x).bilinearComp (h x).metricChangeTransport (h x).metricChangeTransport) s :=
    hk.clm_bilinearComp hT hT
  have hKT := hK.metricChangeTransport fun x hx ↦
    isStrictlyPositive_bilinearComp_metricChangeTransport (h x) (k x) (hpos x hx) (kpos x hx)
  exact ((hT.mul hKT).mul hS).congr fun x _ ↦ metricChangeBetween_def (h x) (k x)

end ContinuousLinearMap
