/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Circle.LinearODE.Basic
import TauCeti.Analysis.Normed.Operator.CompactFamily

/-!
# Uniform inverses for compact families of periodic differential operators

For continuous families of real-linear coefficient loops `S p` and `J p`, invertibility of
`ζ ↦ ζ' - S p ζ` on a compact parameter set persists for `S p - δ • J p`, on a common closed
interval of weights about zero. The inverses are uniformly bounded from `H⁰` to `H¹`.
The period can be any positive real number. These are estimates for periodic loop operators;
they do not assert invertibility of a differential operator on an entire cylinder.

The weighted coefficient `S - δ J` is the end-operator perturbation occurring in Floer theory.
The Sobolev realization is the existing `CircleSobolev.loopOperator`; the uniformity follows
from operator-norm continuity and compactness.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, for the periodic asymptotic operator at a nondegenerate orbit.
-/

public section

open Filter Set Topology

namespace TauCeti.CircleSobolev

variable {P E : Type*} [TopologicalSpace P]
  [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  (T : ℝ) [Fact (0 < T)]

/-- On a compact parameter set where the unweighted periodic operators are invertible,
all sufficiently small positive or negative weights have uniformly bounded inverses
`H⁰(E) →L[ℝ] H¹(E)`. No positivity or complex-linearity assumption on `J` is needed. -/
theorem exists_pos_isInvertible_loopOperator_sub_smul_norm_inverse_le
    {K : Set P} (hK : IsCompact K)
    (S J : P → C(AddCircle T, E →L[ℝ] E)) (hS : ContinuousOn S K) (hJ : ContinuousOn J K)
    (hinv : ∀ p ∈ K, (loopOperator T (S p)).IsInvertible) :
    ∃ ε > 0, ∃ C ≥ 0, ∀ p ∈ K, ∀ δ : ℝ, |δ| ≤ ε →
      (loopOperator T (S p - δ • J p)).IsInvertible ∧
        ‖(loopOperator T (S p - δ • J p)).inverse‖ ≤ C := by
  let : CompleteSpace E := FiniteDimensional.completeSpace ℂ E
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let L : K × ℝ → CircleSobolev 1 E →L[ℝ] CircleSobolev 0 E :=
    fun z ↦ loopOperator T (S z.1 - z.2 • J z.1)
  have hL : Continuous L :=
    (continuous_loopOperator T).comp
      ((hS.domRestrict.comp continuous_fst).sub
        (continuous_snd.smul (hJ.domRestrict.comp continuous_fst)))
  obtain ⟨V, hV, C, hC, hbound⟩ :=
    isCompact_univ.exists_mem_nhds_isInvertible_norm_inverse_le L 0
      (fun _ _ ↦ hL.continuousAt) (by
        intro p _
        dsimp only [L]
        rw [zero_smul ℝ (J p), sub_zero]
        exact hinv p p.2)
  obtain ⟨r, hr, hrV⟩ := Metric.mem_nhds_iff.1 hV
  refine ⟨r / 2, by positivity, C, hC, fun p hp δ hδ ↦ hbound ⟨p, hp⟩ (mem_univ _) δ (hrV ?_)⟩
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using
    hδ.trans_lt (half_lt_self hr)

end TauCeti.CircleSobolev
