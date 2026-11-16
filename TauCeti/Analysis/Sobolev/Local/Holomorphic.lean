/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphic maps are locally Sobolev

A holomorphic map on an open set `s` of the plane is smooth there, so it lies in every local
Sobolev class `W^{k,p}` on every subset of `s`, for every exponent (`DifferentiableOn.memWkpLoc`).
In particular entire maps lie in every class on every set (`Differentiable.memWkpLoc`).

These corollaries of `ContDiffOn.memWkpLoc` are kept apart from
`TauCeti/Analysis/Sobolev/Local/Basic.lean` because they need the Cauchy integral formula.
-/

public section

namespace TauCeti

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
  [IsScalarTower ℝ ℂ F] [CompleteSpace F] {p : ENNReal} {U s : Set ℂ} {k : ℕ} {f : ℂ → F}

/-- A holomorphic map on an open set `s` is in every local Sobolev class on every subset of `s`,
for every exponent: it is smooth on `s`. -/
theorem _root_.DifferentiableOn.memWkpLoc (hf : DifferentiableOn ℂ f s) (hs : IsOpen s)
    (hU : U ⊆ s) : MemWkpLoc p U k f :=
  ((hf.contDiffOn hs (n := k)).restrict_scalars ℝ).memWkpLoc (Ω := ⟨s, hs⟩) hU

/-- An entire map is in every local Sobolev class on every set, for every exponent. -/
theorem _root_.Differentiable.memWkpLoc (hf : Differentiable ℂ f) : MemWkpLoc p U k f :=
  ((hf.contDiff (n := k)).restrict_scalars ℝ).memWkpLoc

end TauCeti
