/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.HalfDisc.Complex
public import TauCeti.Analysis.Sobolev.Local.W1p
public import TauCeti.Analysis.Sobolev.Local.Wkp.HalfDisc
public import TauCeti.Analysis.Sobolev.W1p.MeasurePreserving

/-!
# Transport of local Sobolev functions to the model half-disc

A real local Sobolev function up to the real axis is represented in the model `W^{1,p}` space
on each admissible half-disc (`TauCeti.MemWkpLoc.exists_w1p_halfDisc`). Finite local Sobolev norm
also gives a representative with no larger norm (`TauCeti.exists_w1p_halfDisc_enorm_le`). These
comparisons use affine-isometry transport and require neither traces nor Morrey theory.
-/

public section

noncomputable section

open Metric Set MeasureTheory TopologicalSpace Filter Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {p : ℝ≥0∞} [Fact (1 ≤ p)] {f : ℂ → ℝ}

/-! ### Existence of the transported Sobolev function -/

/-- **A half-disc Sobolev function is Sobolev on every admissible model half-disc.** If
`f ∈ MemWkpLoc p (Ω ∩ {0 ≤ im}) 1` is real, `x` is real and `closedBall x r ∩ {0 ≤ im} ⊆ Ω`,
then the transported function `f ∘ (TauCeti.halfDiscChart x)⁻¹` is represented by an element of
`W^{1,p}(halfDisc r)`. -/
theorem MemWkpLoc.exists_w1p_halfDisc {Ω : Opens ℂ}
    (hf : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 f) {x : ℂ} (hx : x.im = 0) {r : ℝ}
    (hxr : closedBall x r ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    ∃ v : W1p volume (halfDisc r) p,
      W1p.value v =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
        fun w => f ((halfDiscChart x).symm w) := by
  -- Enlarge `Ω` by the open lower half-plane, which does not change `Ω ∩ {0 ≤ im}`.
  let Ω' : Opens ℂ := Ω ⊔ ⟨{z | z.im < 0}, isOpen_lt Complex.continuous_im continuous_const⟩
  have hΩ' : (Ω' : Set ℂ) ∩ {z | 0 ≤ z.im} = (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} := by
    ext z
    simp only [Ω', Opens.coe_sup, mem_inter_iff, mem_union, SetLike.mem_coe, Opens.mem_mk,
      mem_ofPred_eq]
    constructor
    · rintro ⟨hz | hz, hz'⟩
      · exact ⟨hz, hz'⟩
      · exact absurd hz' (not_le.2 hz)
    · exact fun hz => ⟨Or.inl hz.1, hz.2⟩
  have hsub : closure (ball x r) ⊆ (Ω' : Set ℂ) := by
    intro z hz
    replace hz := closure_ball_subset_closedBall hz
    rcases le_or_gt 0 z.im with h0 | h0
    · exact Or.inl (hxr ⟨hz, h0⟩).1
    · exact Or.inr h0
  rw [← hΩ'] at hf
  obtain ⟨v, hv⟩ := hf.exists_wkp_upperHalf (W := ⟨ball x r, isOpen_ball⟩)
    ((isCompact_closedBall x r).of_isClosed_subset isClosed_closure closure_ball_subset_closedBall)
    hsub
  rw [Wkp.value_one] at hv
  refine ⟨W1p.compAffineIsometryEquivL (halfDiscChart x).symm
    (halfDiscChart_symm_preimage hx r) v, ?_⟩
  refine (W1p.value_compAffineIsometryEquivL_ae _ _ v).trans ?_
  exact ae_eq_comp_halfDiscChart_symm hx subset_rfl hv

/-- A real function of finite `W^{1,p}` norm on the upper half-disc `D_r(x) ∩ {0 < im}` about a real
point is represented on the model half-disc by an element of no larger norm. -/
theorem exists_w1p_halfDisc_enorm_le {x : ℂ} (hx : x.im = 0) {r : ℝ}
    (hfin : eLpNormWkp p (upperHalfDisc x r) 1 f ≠ ∞) :
    ∃ w : W1p volume (halfDisc r) p,
      W1p.value w =ᵐ[volume.restrict (halfDisc r : Set (WithLp 2 (ℝ × ℝ)))]
        (fun y => f ((halfDiscChart x).symm y)) ∧
      ‖w‖ₑ ≤ eLpNormWkp p (upperHalfDisc x r) 1 f := by
  obtain ⟨w, hw, hwn⟩ := exists_w1p_enorm_le_eLpNormWkp hfin
  refine ⟨W1p.compAffineIsometryEquivL (halfDiscChart x).symm (halfDiscChart_symm_preimage hx r) w,
    (W1p.value_compAffineIsometryEquivL_ae _ _ w).trans
      (ae_eq_comp_halfDiscChart_symm hx subset_rfl hw), le_trans ?_ hwn⟩
  rw [← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (W1p.norm_compAffineIsometryEquivL_le _ _ w)

end TauCeti
