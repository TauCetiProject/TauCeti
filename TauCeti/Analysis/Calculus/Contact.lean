/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import TauCeti.Topology.Algebra.Module.Contact

/-!
# Smoothness of the continuous symplectization form

The continuous symplectization form `ContinuousLinearMap.symplectizationForm` of a covector `a`
and a bilinear form `b` on `E` is the bilinear form
`((s, v), (s', w)) ↦ s a(w) - a(v) s' + b(v, w)` on `𝕜 × E`. It depends linearly on `(a, b)`, so
it is `C^n` along `C^n` families (`ContDiffOn.symplectizationForm`). Local contact Moser arguments
solve their linear equations with this form, and need it to vary smoothly with the point.

## Main results

* `ContDiffOn.symplectizationForm`: the continuous symplectization form of `C^n` families is
  `C^n`.
-/

public section

variable {𝕜 E P : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup P] [NormedSpace 𝕜 P]

/-- The continuous symplectization form of `C^n` families of covectors and bilinear forms is
`C^n`. -/
theorem ContDiffOn.symplectizationForm {n : WithTop ℕ∞} {s : Set P} {a : P → E →L[𝕜] 𝕜}
    {b : P → E →L[𝕜] E →L[𝕜] 𝕜} (ha : ContDiffOn 𝕜 n a s) (hb : ContDiffOn 𝕜 n b s) :
    ContDiffOn 𝕜 n (fun p ↦ (a p).symplectizationForm (b p)) s := by
  have ha' : ContDiffOn 𝕜 n (fun p ↦ (a p).comp (ContinuousLinearMap.snd 𝕜 𝕜 E)) s :=
    ha.clm_comp contDiffOn_const
  have h : ContDiffOn 𝕜 n (fun p ↦
      (ContinuousLinearMap.fst 𝕜 𝕜 E).smulRight ((a p).comp (ContinuousLinearMap.snd 𝕜 𝕜 E)) -
        ((a p).comp (ContinuousLinearMap.snd 𝕜 𝕜 E)).smulRight (ContinuousLinearMap.fst 𝕜 𝕜 E) +
        ((ContinuousLinearMap.compL 𝕜 (𝕜 × E) E 𝕜).flip (ContinuousLinearMap.snd 𝕜 𝕜 E)).comp
          ((b p).comp (ContinuousLinearMap.snd 𝕜 𝕜 E))) s :=
    ((contDiffOn_const.smulRight ha').sub (ha'.smulRight contDiffOn_const)).add
      (contDiffOn_const.clm_comp (hb.clm_comp contDiffOn_const))
  refine h.congr fun p _ ↦ ContinuousLinearMap.ext fun q ↦ ContinuousLinearMap.ext fun q' ↦ ?_
  simp
