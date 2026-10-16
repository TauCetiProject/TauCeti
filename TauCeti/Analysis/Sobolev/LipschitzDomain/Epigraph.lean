/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Analysis.Normed.Lp.GraphDomain

/-!
# Lipschitz epigraphs are Lipschitz domains

Every strict epigraph of a globally Lipschitz function is a Lipschitz domain. At a boundary point,
translation to the origin turns the defining function `φ` into
`y ↦ φ (y + x.snd) - x.fst`, with the same Lipschitz constant. In particular, every normal
half-space is a Lipschitz domain with constant zero.

This supplies the basic non-flat models for `Set.IsLipschitzDomainWith`.

## Main declarations

* `LipschitzWith.isLipschitzDomainWith_normalEpigraph`: a Lipschitz epigraph has Lipschitz boundary.
* `TauCeti.isLipschitzDomainWith_normalHalfSpace`: a normal half-space has Lipschitz constant zero.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.5.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set TopologicalSpace
open scoped NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A globally Lipschitz graph function defines a Lipschitz domain with the same constant. -/
theorem _root_.LipschitzWith.isLipschitzDomainWith_normalEpigraph {L : ℝ≥0} {φ : C(E, ℝ)}
    (hφ : LipschitzWith L φ) :
    Set.IsLipschitzDomainWith (E := E) (normalEpigraph φ) L := by
  rw [Set.isLipschitzDomainWith_iff]
  refine ⟨(normalEpigraph φ).2, fun x hx ↦ ?_⟩
  rw [coe_normalEpigraph] at hx
  have hxGraph : φ x.snd = x.fst :=
    frontier_lt_subset_eq
      (φ.continuous.comp (WithLp.prod_continuous_ofLp 2 ℝ E).snd)
      (WithLp.prod_continuous_ofLp 2 ℝ E).fst hx
  let e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E) :=
    (AffineIsometryEquiv.vaddConst ℝ x).symm
  let ψ : E → ℝ := fun y ↦ φ (y + x.snd) - x.fst
  have hψ : LipschitzWith L ψ := by
    intro y z
    simpa [ψ] using hφ (y + x.snd) (z + x.snd)
  rw [Set.isLipschitzDomainAtWith_iff]
  refine ⟨e, ψ, 1, 1, zero_lt_one, zero_lt_one, ?_, ?_, hψ, ?_⟩
  · simp [e]
  · simp [ψ, hxGraph]
  · intro z _
    simp only [SetLike.mem_coe, mem_normalEpigraph, e, ψ,
      AffineIsometryEquiv.symm_symm, AffineIsometryEquiv.coe_vaddConst, vadd_eq_add,
      WithLp.add_fst, WithLp.add_snd]
    constructor <;> intro h <;> linarith

/-- A normal half-space is a Lipschitz domain with Lipschitz constant zero. -/
theorem isLipschitzDomainWith_normalHalfSpace (a : ℝ) :
    Set.IsLipschitzDomainWith (E := E) (normalHalfSpace (E := E) a) 0 := by
  let φ : C(E, ℝ) := ⟨fun _ ↦ a, continuous_const⟩
  have hφ : LipschitzWith 0 φ := LipschitzWith.const _
  convert hφ.isLipschitzDomainWith_normalEpigraph using 1
  ext z
  simp [φ]

end TauCeti

end
