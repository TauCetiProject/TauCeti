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

/-- The time needed for a connecting point to reach the intermediate level `c`. -/
def levelCrossingTime (x : ↥(unstableSet φ p ∩ stableSet φ q)) : ℝ :=
  Classical.choose (hφ.exists_continuous_levelCrossingTime hf hfp hfq hc) x

/-- The crossing time depends continuously on the connecting point. -/
theorem continuous_levelCrossingTime :
    Continuous (hφ.levelCrossingTime hf hfp hfq hc) :=
  (Classical.choose_spec (hφ.exists_continuous_levelCrossingTime hf hfp hfq hc)).1

theorem apply_flow_levelCrossingTime (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    f (φ (hφ.levelCrossingTime hf hfp hfq hc x) x.1) = c :=
  (Classical.choose_spec (hφ.exists_continuous_levelCrossingTime hf hfp hfq hc)).2 x

/-- A time reaches the chosen level exactly when it is the crossing time. -/
theorem eq_levelCrossingTime_iff (x : ↥(unstableSet φ p ∩ stableSet φ q)) (t : ℝ) :
    t = hφ.levelCrossingTime hf hfp hfq hc x ↔ f (φ t x.1) = c := by
  have huniq := hφ.existsUnique_time_value_of_mem_unstableSet_inter_stableSet
    (fun s ↦ hf _ ⟨isInvariant_unstableSet φ p s x.2.1,
      isInvariant_stableSet φ q s x.2.2⟩) hfp hfq x.2 hc
  constructor
  · rintro rfl
    exact hφ.apply_flow_levelCrossingTime hf hfp hfq hc x
  · intro ht
    exact huniq.unique ht (hφ.apply_flow_levelCrossingTime hf hfp hfq hc x)

/-- A point lies on the selected level exactly when its crossing time is zero. -/
@[simp]
theorem levelCrossingTime_eq_zero_iff (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    hφ.levelCrossingTime hf hfp hfq hc x = 0 ↔ f x.1 = c := by
  simpa only [eq_comm, Flow.map_zero_apply] using
    hφ.eq_levelCrossingTime_iff hf hfp hfq hc x 0

/-- Translating a trajectory by `t` subtracts `t` from the time still needed to reach
an intermediate level. -/
theorem levelCrossingTime_flow (t : ℝ) (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    hφ.levelCrossingTime hf hfp hfq hc
      ((φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q)) t x) =
      hφ.levelCrossingTime hf hfp hfq hc x - t := by
  apply Eq.symm
  rw [hφ.eq_levelCrossingTime_iff hf hfp hfq hc, Flow.coe_restrict_apply,
    ← φ.map_add, sub_add_cancel]
  exact hφ.apply_flow_levelCrossingTime hf hfp hfq hc x

/-- The connecting locus is the product of flow time with an intermediate level slice.
The inverse is the flow itself, restricted to the slice. -/
def connectingHomeomorphProdLevelSlice :
    ↥(unstableSet φ p ∩ stableSet φ q) ≃ₜ
      ℝ × ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}) := by
  let ψ := φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q)
  let a := hφ.levelCrossingTime hf hfp hfq hc
  have ha : Continuous (fun x ↦ -a x) :=
    (hφ.continuous_levelCrossingTime hf hfp hfq hc).neg
  have hshift (t : ℝ) (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
      -a (ψ t x) = t + -a x := by
    have ht := hφ.levelCrossingTime_flow hf hfp hfq hc t x
    dsimp only [ψ, a]
    rw [ht]
    ring
  let e : {x : ↥(unstableSet φ p ∩ stableSet φ q) | -a x = 0} ≃ₜ
      ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c}) :=
    { toFun := fun x ↦ ⟨x.1.1, x.1.2,
        (hφ.levelCrossingTime_eq_zero_iff hf hfp hfq hc x.1).mp (neg_eq_zero.mp x.2)⟩
      invFun := fun x ↦ ⟨⟨x.1, x.2.1⟩,
        neg_eq_zero.mpr ((hφ.levelCrossingTime_eq_zero_iff hf hfp hfq hc _).mpr x.2.2)⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }
  exact (ψ.timeSliceHomeomorph (fun x ↦ -a x) ha hshift).trans
    ((Homeomorph.refl ℝ).prodCongr e)

@[simp]
theorem connectingHomeomorphProdLevelSlice_symm_apply
    (tx : ℝ × ↥((unstableSet φ p ∩ stableSet φ q) ∩ {x | f x = c})) :
    ((hφ.connectingHomeomorphProdLevelSlice hf hfp hfq hc).symm tx : E) =
      φ tx.1 tx.2.1 := by
  simp [connectingHomeomorphProdLevelSlice]

@[simp]
theorem connectingHomeomorphProdLevelSlice_fst
    (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    (hφ.connectingHomeomorphProdLevelSlice hf hfp hfq hc x).1 =
      -hφ.levelCrossingTime hf hfp hfq hc x := by
  simp [connectingHomeomorphProdLevelSlice]

@[simp]
theorem connectingHomeomorphProdLevelSlice_snd_coe
    (x : ↥(unstableSet φ p ∩ stableSet φ q)) :
    ((hφ.connectingHomeomorphProdLevelSlice hf hfp hfq hc x).2 : E) =
      φ (hφ.levelCrossingTime hf hfp hfq hc x) x.1 := by
  simp [connectingHomeomorphProdLevelSlice]

include hφ hf hfp hfq hc in
/-- Time translation on the connecting set is proper for its subspace topology. This is
properness of the action map, not properness of an individual trajectory in the ambient space. -/
theorem isProperMap_connecting_pair :
    IsProperMap (fun tx : ℝ × ↥(unstableSet φ p ∩ stableSet φ q) ↦
      ((φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q)) tx.1 tx.2, tx.2)) := by
  apply Flow.isProperMap_pair_of_timeCoordinate
    (φ.restrict (isInvariant_unstableSet_inter_stableSet φ p q))
    (fun x ↦ -hφ.levelCrossingTime hf hfp hfq hc x)
    (hφ.continuous_levelCrossingTime hf hfp hfq hc).neg
  intro t x
  rw [hφ.levelCrossingTime_flow hf hfp hfq hc]
  ring

end Flow.IsNegativeGradient
