/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude Opus 5, GPT-6
-/
module

import TauCeti.Analysis.OperatorIdeal.ApproximationNumber.Diagonal
import Mathlib.Analysis.InnerProductSpace.l2Space
public import TauCeti.Analysis.OperatorIdeal.Family.SymmetricGauge

/-!
# Faithfulness of induced symmetric operator-ideal families

The family of operator-ideal gauges induced by a symmetric gauge determines its
extension to every antitone `ℝ≥0∞`-valued sequence. In particular, equality
of induced operator-ideal families over any `RCLike` scalar field implies equality
of the extended gauges on all such sequences.

When the initial entry is finite, every entry is finite by antitonicity, and
a diagonal operator on `ℓ²` realizes the sequence of entries as its
approximation numbers. When the initial entry is `⊤`, each extended gauge is
`⊤` by its lower bound from the supremum of the sequence.

## Main result

* `TauCeti.SymmetricGauge.extend_eq_of_operatorIdealFamily_eq`: equality of induced
  operator-ideal families over any `RCLike` field determines the extended gauges on
  antitone sequences.

## Provenance

Adapted from `ForTauCeti/Analysis/OperatorIdeal/Family/SymmetricGauge.lean`
in the Kitware Davis--Kahan formalization (Apache-2.0).
-/

public section

open scoped ENNReal NNReal lp

namespace TauCeti
namespace SymmetricGauge

/-- Two symmetric gauges that induce the same operator-ideal family over a
`RCLike` scalar field have equal extensions on every antitone `ℝ≥0∞`-valued sequence. -/
theorem extend_eq_of_operatorIdealFamily_eq
    {𝕜 : Type} [RCLike 𝕜]
    {Φ Ψ : SymmetricGauge}
    (h : Φ.operatorIdealFamily.{0, 0, 0} 𝕜 = Ψ.operatorIdealFamily.{0, 0, 0} 𝕜)
    {a : ℕ → ℝ≥0∞} (ha : Antitone a) :
    Φ.extend a = Ψ.extend a := by
  classical
  by_cases htop : a 0 = ⊤
  · have htop_ext (Θ : SymmetricGauge) : Θ.extend a = ⊤ := by
      apply top_le_iff.mp
      calc
        ⊤ = a 0 := htop.symm
        _ ≤ ⨆ n, a n := le_iSup (fun n => a n) 0
        _ ≤ Θ.extend a := Θ.iSup_le_extend a
    rw [htop_ext Φ, htop_ext Ψ]
  · have hfinite (n : ℕ) : a n ≠ ⊤ :=
      ne_top_of_le_ne_top htop (ha (Nat.zero_le n))
    let c : ℕ → ℝ≥0 := fun n => (a n).toNNReal
    have hc (n : ℕ) : (c n : ℝ≥0∞) = a n :=
      ENNReal.coe_toNNReal (hfinite n)
    have hcanti : Antitone c := by
      intro i j hij
      apply ENNReal.coe_le_coe.mp
      simpa only [hc] using ha hij
    obtain ⟨d, hd⟩ :=
      lp.exists_singularValue_diagonalCLM_eq (p := 2) (𝕜 := 𝕜) hcanti
    let T : ℓ²(ℕ, 𝕜) →L[𝕜] ℓ²(ℕ, 𝕜) := lp.diagonalCLM d
    have hs : (fun n => (T.singularValue n : ℝ≥0∞)) = a := by
      funext n
      dsimp only [T]
      rw [congrFun hd n]
      exact hc n
    have heq := congrArg
      (fun F : OperatorIdealFamily.{0, 0, 0} 𝕜 => F.gauge T) h
    simp only [operatorIdealFamily_gauge] at heq
    simpa only [opGauge_def, hs] using heq

end SymmetricGauge
end TauCeti
