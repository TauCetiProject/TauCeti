/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.Morse.ContinuousLevelSlice
public import TauCeti.Dynamics.Flow.TimeSlice

/-!
# Proper time translation on connecting gradient trajectories

For a negative-gradient flow, any level strictly between the endpoint values gives a
continuous time coordinate on `Wᵘ(p) ∩ Wˢ(q)`. We construct the resulting product
homeomorphism with `ℝ` times the level slice and prove properness of time translation.
These are statements about the subspace topology on the connecting set; neither
Morse nondegeneracy nor Morse--Smale transversality is needed.

The time coordinate is the negative of the time needed to reach the chosen level, so
forward flow adds to that coordinate. The product homeomorphism reconstructs a connecting
point by flowing a point of the level slice for the given time. Constant trajectories
are excluded by the strict inequalities on the level.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer, 2014, Chapter 2
  (connecting trajectories modulo time translation).
-/

public section

open Set Topology

noncomputable section

namespace Flow.IsNegativeGradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  {φ : Flow ℝ E} {f : E → ℝ} {p q : E}
  (hφ : IsNegativeGradient φ f)
  (hf : ∀ x ∈ unstableSet φ p ∩ stableSet φ q, DifferentiableAt ℝ f x)
  (hfp : ContinuousAt f p) (hfq : ContinuousAt f q)
  {c : ℝ} (hc : f q < c ∧ c < f p)

/-- Identify the zero fibre of the negative crossing time with the potential level slice. -/
private def zeroCrossingTimeHomeomorphLevelSlice :
    {x : ↥(unstableSet φ p ∩ stableSet φ q) |
      -hφ.levelCrossingTime hf hfp hfq hc x = 0} ≃ₜ
      ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}) where
  toFun x := ⟨x.1.1, x.1.2,
    (hφ.levelCrossingTime_eq_zero_iff hf hfp hfq hc x.1).mp (neg_eq_zero.mp x.2)⟩
  invFun x := ⟨⟨x.1, x.2.1⟩,
    neg_eq_zero.mpr ((hφ.levelCrossingTime_eq_zero_iff hf hfp hfq hc _).mpr x.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

private theorem zeroCrossingTimeHomeomorphLevelSlice_apply_coe
    (x : {x : ↥(unstableSet φ p ∩ stableSet φ q) |
      -hφ.levelCrossingTime hf hfp hfq hc x = 0}) :
    (hφ.zeroCrossingTimeHomeomorphLevelSlice hf hfp hfq hc x : E) = x.1.1 := (rfl)

private theorem zeroCrossingTimeHomeomorphLevelSlice_symm_apply_coe
    (x : ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})) :
    ((hφ.zeroCrossingTimeHomeomorphLevelSlice hf hfp hfq hc).symm x).1.1 = x.1 := (rfl)

/-- The connecting locus is the product of flow time with an intermediate level slice.
The inverse is the flow itself, restricted to the slice. -/
def connectingHomeomorphProdLevelSlice :
    ↥(unstableSet φ p ∩ stableSet φ q) ≃ₜ
      ℝ × ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}) :=
  ((φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q)).timeSliceHomeomorph
    (fun x ↦ -hφ.levelCrossingTime hf hfp hfq hc x)
    (hφ.continuous_levelCrossingTime hf hfp hfq hc).neg
    (hφ.neg_levelCrossingTime_flow hf hfp hfq hc)).trans
    ((Homeomorph.refl ℝ).prodCongr (hφ.zeroCrossingTimeHomeomorphLevelSlice hf hfp hfq hc))

@[simp]
theorem connectingHomeomorphProdLevelSlice_symm_apply
    (tx : ℝ × ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})) :
    ((hφ.connectingHomeomorphProdLevelSlice hf hfp hfq hc).symm tx : E) =
      φ tx.1 tx.2.1 := by
  simp only [connectingHomeomorphProdLevelSlice, Homeomorph.symm_trans_apply,
    Homeomorph.prodCongr_symm, Homeomorph.coe_prodCongr, Prod.map_fst, Prod.map_snd,
    Homeomorph.refl_symm, Homeomorph.refl_apply, id_eq, Flow.timeSliceHomeomorph_symm_apply,
    Flow.coe_restrict_apply, zeroCrossingTimeHomeomorphLevelSlice_symm_apply_coe]

@[simp]
theorem connectingHomeomorphProdLevelSlice_fst
    (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    (hφ.connectingHomeomorphProdLevelSlice hf hfp hfq hc x).1 =
      -hφ.levelCrossingTime hf hfp hfq hc x := by
  simp only [connectingHomeomorphProdLevelSlice, Homeomorph.trans_apply,
    Homeomorph.coe_prodCongr, Prod.map_fst, Homeomorph.refl_apply,
    Flow.timeSliceHomeomorph_fst, id_eq]

@[simp]
theorem connectingHomeomorphProdLevelSlice_snd_coe
    (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    ((hφ.connectingHomeomorphProdLevelSlice hf hfp hfq hc x).2 : E) =
      φ (hφ.levelCrossingTime hf hfp hfq hc x) x.1 := by
  simp only [connectingHomeomorphProdLevelSlice, Homeomorph.trans_apply,
    Homeomorph.coe_prodCongr, Prod.map_snd, zeroCrossingTimeHomeomorphLevelSlice_apply_coe,
    Flow.timeSliceHomeomorph_snd_coe, Flow.coe_restrict_apply, neg_neg]

/-- In product coordinates time translation changes only the real coordinate. -/
@[simp]
theorem connectingHomeomorphProdLevelSlice_flow (t : ℝ)
    (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    hφ.connectingHomeomorphProdLevelSlice hf hfp hfq hc
      ((φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q)) t x) =
      (t + (hφ.connectingHomeomorphProdLevelSlice hf hfp hfq hc x).1,
        (hφ.connectingHomeomorphProdLevelSlice hf hfp hfq hc x).2) := by
  simp only [connectingHomeomorphProdLevelSlice, Homeomorph.trans_apply,
    Flow.timeSliceHomeomorph_flow, Homeomorph.coe_prodCongr, Prod.map_apply,
    Prod.map_fst, Prod.map_snd, Homeomorph.refl_apply, id_eq]

include hφ hf hfp hfq hc in
/-- Time translation on the connecting set is proper for its subspace topology. This is
properness of the action map, not properness of an individual trajectory in the ambient space. -/
theorem isProperMap_restrict_pair :
    IsProperMap (fun tx : ℝ × ↥(unstableSet φ p ∩ stableSet φ q) ↦
      ((φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q)) tx.1 tx.2, tx.2)) :=
  Flow.isProperMap_flow_pair_of_timeCoordinate
    (φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q))
    (fun x ↦ -hφ.levelCrossingTime hf hfp hfq hc x)
    (hφ.continuous_levelCrossingTime hf hfp hfq hc).neg
    (hφ.neg_levelCrossingTime_flow hf hfp hfq hc)

end Flow.IsNegativeGradient
