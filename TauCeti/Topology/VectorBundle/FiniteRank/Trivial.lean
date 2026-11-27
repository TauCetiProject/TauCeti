/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Basic

/-!
# Multiplication by a scalar function on a trivial core

A continuous function `f : B → 𝕜` acts on the trivial core `B × 𝕜ⁿ` by multiplication on each
fibre (`TauCeti.FiniteRankBundleCore.smulTrivial`). For `n = 1` this presents the function `f` as a
section of the trivial line core, its value on the constant vector `1`.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.FiniteRankBundleCore

variable {𝕜 B : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace B] {n : ℕ}

/-- Multiplying the coordinates of the trivial core by a continuous scalar function is continuous
on its total space. -/
theorem continuous_smul_trivial (f : B → 𝕜) (hf : Continuous f) :
    Continuous fun p : (trivial 𝕜 B n).core.TotalSpace ↦
      (f p.proj • ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) p.snd := by
  have h : Continuous fun p : (trivial 𝕜 B n).core.TotalSpace ↦ f p.proj • (p.snd : Fin n → 𝕜) :=
    (hf.comp (trivial 𝕜 B n).core.continuous_proj).smul continuous_trivial_snd
  have e (c : 𝕜) (v : Fin n → 𝕜) : c • v = (c • ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) v := by
    rw [_root_.smul_apply, ContinuousLinearMap.id_apply]
  -- The fibres of the trivial core are `Fin n → 𝕜` (`rank_trivial`).
  exact h.congr fun p ↦ e _ p.snd

variable [CompleteSpace 𝕜]

/-- Multiplication by a continuous scalar function, as a bundle map of the trivial core. -/
def smulTrivial (f : B → 𝕜) (hf : Continuous f) : trivial 𝕜 B n ⟶ trivial 𝕜 B n :=
  toTrivial (fun x ↦ f x • ContinuousLinearMap.id 𝕜 (Fin n → 𝕜)) (continuous_smul_trivial f hf)

@[simp] theorem fiberMap_smulTrivial (f : B → 𝕜) (hf : Continuous f) (x : B) :
    (smulTrivial (n := n) f hf).fiberMap x = f x • ContinuousLinearMap.id 𝕜 (Fin n → 𝕜) :=
  fiberMap_toTrivial _ (continuous_smul_trivial f hf) x

end TauCeti.FiniteRankBundleCore
