/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Mass.Normal
public import TauCeti.Analysis.Distribution.TestFunction.SegmentCurrent
import Mathlib.Analysis.Normed.Module.HahnBanach
import TauCeti.Analysis.Convex.Topology
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# The mass of the oriented segment current

Let `Ω` be an open set of a real normed space `E`. The oriented segment current `[[p, q]]`
(`Distribution.segmentCurrent`) integrates test `1`-forms along the segment from `p` to `q`. The
pointwise norm of a `1`-form used by `Distribution.mass` is its operator norm, which is the dual
norm of `E`. This file shows that the mass of `[[p, q]]` is at most the length `‖q - p‖` of the
segment, with equality when `E` is finite-dimensional and the closed segment lies in `Ω`, and that
`[[p, q]]` is a normal current: its boundary `δ_q - δ_p` has mass at most `2`.

The equality is the simplest case of the comparison between the mass of a current carried by a
smooth curve and the length of the curve. It needs no inner product: the extremal test form is a
cutoff equal to one near the segment times a norming functional of `q - p`, given by the
Hahn–Banach theorem. When the segment leaves `Ω`, the mass is in general smaller, since only the
part of the segment inside `Ω` is tested.

## Main declarations

* `Distribution.mass_segmentCurrent_le`: `M([[p, q]]) ≤ ‖q - p‖`.
* `Distribution.mass_segmentCurrent`: `M([[p, q]]) = ‖q - p‖` when `E` is finite-dimensional and
  `[p, q] ⊆ Ω`.
* `Distribution.mass_segmentCurrent_comp_extDerivCLM_le`: `M(∂[[p, q]]) ≤ 2`.
* `Distribution.isNormal_segmentCurrent`: `[[p, q]]` is a normal current.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (mass and normal currents) and §4.1.8
  (oriented simplexes).
-/

public section

noncomputable section

open Set TopologicalSpace TestFunction AffineMap Filter
open scoped Distributions ENNReal

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {n : ℕ∞}

/-- The mass of the segment current `[[p, q]]` is at most the length `‖q - p‖` of the segment. -/
theorem mass_segmentCurrent_le (p q : E) :
    mass (segmentCurrent p q : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ) ≤ ‖q - p‖ₑ := by
  refine mass_le_iff.2 fun ω hω => ?_
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal <| (norm_segmentCurrent_apply_le p q ω hω).trans_eq (one_mul _)

/-- **The mass of a segment current is its length.** When `E` is finite-dimensional and the closed
segment `[p, q]` lies in `Ω`, `M([[p, q]]) = ‖q - p‖`. -/
theorem mass_segmentCurrent [FiniteDimensional ℝ E] {p q : E} (h : segment ℝ p q ⊆ Ω) :
    mass (segmentCurrent p q : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ) = ‖q - p‖ₑ := by
  refine le_antisymm (mass_segmentCurrent_le p q) ?_
  rcases eq_or_ne (q - p) 0 with hpq | hpq
  · simp [hpq]
  -- Test against `χ • ℓ` for a cutoff `χ` equal to one near the segment and a norming
  -- functional `ℓ` of `q - p`.
  obtain ⟨ℓ, hℓ, hℓpq⟩ := exists_dual_vector ℝ (q - p) (norm_ne_zero_iff.2 hpq)
  obtain ⟨χ, hχ, hχ01⟩ := exists_eventually_eq_one (n := n) (TauCeti.isCompact_segment ℝ p q) h
  let α : E [⋀^Fin 1]→L[ℝ] ℝ := ContinuousAlternatingMap.ofSubsingleton ℝ E ℝ 0 ℓ
  let ω : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ) := postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ α) χ
  have hω (x : E) : ‖ω x‖ ≤ 1 := by
    simpa [ω, α, norm_smul, hℓ, abs_of_nonneg (hχ01 x).1] using (hχ01 x).2
  have hχγ (t : ℝ) (ht : t ∈ uIcc 0 1) : χ (lineMap p q t) = 1 := by
    rw [uIcc_of_le zero_le_one] at ht
    exact hχ.self_of_nhdsSet _ (lineMap_mem_segment ℝ p q ht)
  have hval : segmentCurrent p q ω = ‖q - p‖ := by
    rw [segmentCurrent_apply_eq_intervalIntegral_lineMap,
      intervalIntegral.integral_congr (g := fun _ => ‖q - p‖)
        fun t ht => by simp [ω, α, hχγ t ht, hℓpq]]
    simp
  have := enorm_le_mass (f := (segmentCurrent p q : 𝓓^{n}(Ω, E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ)) hω
  rwa [hval, Real.enorm_of_nonneg (norm_nonneg _), ofReal_norm] at this

/-- The boundary `∂[[p, q]] = δ_q - δ_p` of a segment current has mass at most `2`. -/
theorem mass_segmentCurrent_comp_extDerivCLM_le (p q : E) :
    mass (segmentCurrent p q ∘L extDerivCLM : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) ≤ 2 := by
  refine mass_le_iff.2 fun g hg => ?_
  have hev (x : E) : ‖g x ![]‖ ≤ 1 := by
    have h := (g x).le_opNorm ![]
    simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one] at h
    exact h.trans (hg x)
  rw [ContinuousLinearMap.comp_apply, segmentCurrent_extDerivCLM, ← ofReal_norm,
    show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
  exact ENNReal.ofReal_le_ofReal <|
    (norm_sub_le _ _).trans (by linarith [hev q, hev p])

/-- **Segment currents are normal**: `[[p, q]]` and its boundary `δ_q - δ_p` have finite mass. -/
theorem isNormal_segmentCurrent (p q : E) :
    IsNormal (segmentCurrent p q : 𝓓(Ω, E [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
  isNormal_succ_iff.2 ⟨ne_top_of_le_ne_top enorm_ne_top (mass_segmentCurrent_le p q),
    ne_top_of_le_ne_top ENNReal.ofNat_ne_top (mass_segmentCurrent_comp_extDerivCLM_le p q)⟩

end Distribution
