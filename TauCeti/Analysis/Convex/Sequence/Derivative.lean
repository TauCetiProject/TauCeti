/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Sequence.Face
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Supporting values near a finite face

At a finite face of a convex height sequence, the supporting value is affine on
each side of the face slope in a sufficiently small interval. Its left derivative
is minus the absolute left endpoint, and its right derivative is minus the absolute
right endpoint. The supporting value is differentiable exactly when the face is a
singleton.

The statements allow unbounded finite domains. Finiteness of the face provides a
strict gap to each adjacent finite slope; no conclusion is asserted at an infinite
terminal face. A singleton face has the same derivative on both sides.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Chapter IV §3.
* M. Lazard, *Les zéros d'une fonction analytique d'une variable sur un corps valué complet*,
  Publications Mathématiques de l'IHÉS 14 (1962), §1.
-/

public section

open Set Filter Topology

namespace TauCeti
namespace IsFiniteFace

variable {h : ℕ → WithTop ℝ} {σ : ℝ} {l u : ℕ}

/-- Immediately to the left of a finite face slope, the supporting value is computed
at the face's left endpoint. The interval includes the face slope itself. -/
theorem exists_pos_supportingValue_eq_left (hf : IsFiniteFace h σ l u)
    (hh : IsConvexSeq h) :
    ∃ ε > (0 : ℝ), ∀ τ ∈ Icc (σ - ε) σ,
      supportingValue h τ = (((h l).untop₀ - τ * l : ℝ) : EReal) := by
  have hthrough := hf.isSupportingLine_untop₀_sub ⟨le_rfl, hf.left_le_right⟩
  have hbounds := (hh.isSupportingLine_iff_unitSlope hf.left_ne_top σ).mp hthrough
  have hgap : ∃ ε > (0 : ℝ), ∀ i, i + 1 = l → h i ≠ ⊤ →
      unitSlope h i ≤ σ - ε := by
    by_cases hp : ∃ i, i + 1 = l ∧ h i ≠ ⊤
    · obtain ⟨i, hi, hif⟩ := hp
      have hs := hf.unitSlope_lt hh (i := i)
        (mem_finiteEdges.mpr ⟨hif, hi ▸ hf.left_ne_top⟩) (by omega)
      refine ⟨σ - unitSlope h i, sub_pos.mpr hs, fun j hj _ => ?_⟩
      have : j = i := by omega
      subst j
      linarith
    · exact ⟨1, zero_lt_one, fun i hi hif => (hp ⟨i, hi, hif⟩).elim⟩
  obtain ⟨ε, hε, hgap⟩ := hgap
  refine ⟨ε, hε, fun τ hτ => ?_⟩
  have ht : IsSupportingLine h τ ((h l).untop₀ - τ * l) :=
    (hh.isSupportingLine_iff_unitSlope hf.left_ne_top τ).mpr
      ⟨fun i hi hif => (hgap i hi hif).trans hτ.1,
        fun hn => hτ.2.trans (hbounds.2 hn)⟩
  apply supportingValue_eq_coe_of_mem_supportingFace ht (n := l)
  simp [mem_supportingFace, sub_add_cancel, WithTop.coe_untop₀_of_ne_top hf.left_ne_top]

/-- Immediately to the right of a finite face slope, the supporting value is computed
at the face's right endpoint. The interval includes the face slope itself. -/
theorem exists_pos_supportingValue_eq_right (hf : IsFiniteFace h σ l u)
    (hh : IsConvexSeq h) :
    ∃ ε > (0 : ℝ), ∀ τ ∈ Icc σ (σ + ε),
      supportingValue h τ = (((h u).untop₀ - τ * u : ℝ) : EReal) := by
  have hthrough := hf.isSupportingLine_untop₀_sub ⟨hf.left_le_right, le_rfl⟩
  have hbounds := (hh.isSupportingLine_iff_unitSlope hf.right_ne_top σ).mp hthrough
  have hgap : ∃ ε > (0 : ℝ), h (u + 1) ≠ ⊤ → σ + ε ≤ unitSlope h u := by
    by_cases hn : h (u + 1) ≠ ⊤
    · have hs := hf.lt_unitSlope hh (i := u) (mem_finiteEdges.mpr ⟨hf.right_ne_top, hn⟩) le_rfl
      exact ⟨unitSlope h u - σ, sub_pos.mpr hs, fun _ => by linarith⟩
    · exact ⟨1, zero_lt_one, fun h => (hn h).elim⟩
  obtain ⟨ε, hε, hgap⟩ := hgap
  refine ⟨ε, hε, fun τ hτ => ?_⟩
  have ht : IsSupportingLine h τ ((h u).untop₀ - τ * u) :=
    (hh.isSupportingLine_iff_unitSlope hf.right_ne_top τ).mpr
      ⟨fun i hi hif => (hbounds.1 i hi hif).trans hτ.1,
        fun hn => hτ.2.trans (hgap hn)⟩
  apply supportingValue_eq_coe_of_mem_supportingFace ht (n := u)
  simp [mem_supportingFace, sub_add_cancel, WithTop.coe_untop₀_of_ne_top hf.right_ne_top]

/-- The left derivative of the real supporting value at a finite face is minus
its absolute left endpoint. -/
theorem hasDerivWithinAt_supportingValue_toReal_left (hf : IsFiniteFace h σ l u)
    (hh : IsConvexSeq h) :
    HasDerivWithinAt (fun τ => (supportingValue h τ).toReal) (-(l : ℝ)) (Iic σ) σ := by
  obtain ⟨ε, hε, heq⟩ := hf.exists_pos_supportingValue_eq_left hh
  have hd := ((hasDerivAt_const σ (h l).untop₀).sub
    ((hasDerivAt_id σ).mul_const (l : ℝ))).hasDerivWithinAt (s := Iic σ)
  simp only [zero_sub, one_mul] at hd
  apply hd.congr_of_eventuallyEq_of_mem ?_ self_mem_Iic
  filter_upwards [Icc_mem_nhdsLE (sub_lt_self σ hε)] with τ hτ
  simp only [heq τ hτ, EReal.toReal_coe, Pi.sub_apply, id_eq]

/-- The right derivative of the real supporting value at a finite face is minus
its absolute right endpoint. -/
theorem hasDerivWithinAt_supportingValue_toReal_right (hf : IsFiniteFace h σ l u)
    (hh : IsConvexSeq h) :
    HasDerivWithinAt (fun τ => (supportingValue h τ).toReal) (-(u : ℝ)) (Ici σ) σ := by
  obtain ⟨ε, hε, heq⟩ := hf.exists_pos_supportingValue_eq_right hh
  have hd := ((hasDerivAt_const σ (h u).untop₀).sub
    ((hasDerivAt_id σ).mul_const (u : ℝ))).hasDerivWithinAt (s := Ici σ)
  simp only [zero_sub, one_mul] at hd
  apply hd.congr_of_eventuallyEq_of_mem ?_ self_mem_Ici
  filter_upwards [Icc_mem_nhdsGE (lt_add_of_pos_right σ hε)] with τ hτ
  simp only [heq τ hτ, EReal.toReal_coe, Pi.sub_apply, id_eq]

/-- At a singleton finite face, the real supporting value is differentiable, with
derivative minus the absolute contact index. -/
theorem hasDerivAt_supportingValue_toReal (hf : IsFiniteFace h σ l l)
    (hh : IsConvexSeq h) :
    HasDerivAt (fun τ => (supportingValue h τ).toReal) (-(l : ℝ)) σ := by
  have hd := (hf.hasDerivWithinAt_supportingValue_toReal_left hh).union
    (hf.hasDerivWithinAt_supportingValue_toReal_right hh)
  simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hd

/-- At a finite face, the real supporting value is differentiable exactly when
the face is a singleton. A face of positive length gives a corner. -/
theorem differentiableAt_supportingValue_toReal_iff (hf : IsFiniteFace h σ l u)
    (hh : IsConvexSeq h) :
    DifferentiableAt ℝ (fun τ => (supportingValue h τ).toReal) σ ↔ l = u := by
  constructor
  · intro hd
    have hleft := (uniqueDiffWithinAt_Iic σ).eq_deriv _
      (hf.hasDerivWithinAt_supportingValue_toReal_left hh) hd.hasDerivAt.hasDerivWithinAt
    have hright := (uniqueDiffWithinAt_Ici σ).eq_deriv _
      (hf.hasDerivWithinAt_supportingValue_toReal_right hh) hd.hasDerivAt.hasDerivWithinAt
    exact_mod_cast neg_injective (hleft.trans hright.symm)
  · rintro rfl
    exact (hf.hasDerivAt_supportingValue_toReal hh).differentiableAt

end IsFiniteFace
end TauCeti
