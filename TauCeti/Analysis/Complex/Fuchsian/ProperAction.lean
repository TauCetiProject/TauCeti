/-
Copyright (c) 2026 The Tau Ceti authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti authors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.ProperAction
public import TauCeti.Analysis.Complex.UpperHalfPlane.PSLAction

import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Proper action of `PSL(2, ℝ)` on the upper half-plane

The Möbius action of `PSL(2, ℝ)` on the upper half-plane is continuous and proper. The
properness is descended from Mathlib's proper `SL(2, ℝ)` action using the surjective quotient
map `SL(2, ℝ) → PSL(2, ℝ)`. Consequently, every discrete subgroup of `PSL(2, ℝ)` acts
properly discontinuously on the upper half-plane.

This supplies the proper-discontinuity input needed to construct Hausdorff orbit quotients and
to control stabilizers of Fuchsian groups.
-/

public section

noncomputable section

open scoped MatrixGroups

open Matrix.SpecialLinearGroup UpperHalfPlane

namespace TauCeti

/-- The projective special linear group `PSL(2, ℝ)` is Hausdorff. -/
instance : T2Space PSL(2, ℝ) := by
  let _ : NeZero (max (Fintype.card (Fin 2)) 1) := ⟨by simp⟩
  let _ : Finite (Subgroup.center SL(2, ℝ)) :=
    Finite.of_equiv (rootsOfUnity (max (Fintype.card (Fin 2)) 1) ℝ)
      (Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity (n := Fin 2) (R := ℝ)).symm
  let _ : IsClosed ((Subgroup.center SL(2, ℝ) : Subgroup SL(2, ℝ)) : Set SL(2, ℝ)) :=
    Set.toFinite _ |>.isClosed
  infer_instance

/-- The effective `PSL(2, ℝ)` action on the upper half-plane is jointly continuous. -/
instance : ContinuousSMul PSL(2, ℝ) ℍ where
  continuous_smul := by
    rw [← (QuotientGroup.isOpenQuotientMap_mk.prodMap IsOpenQuotientMap.id).continuous_comp_iff]
    have hfun :
        (fun p : PSL(2, ℝ) × ℍ ↦ p.1 • p.2) ∘
            Prod.map (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) id =
          fun p : SL(2, ℝ) × ℍ ↦ p.1 • p.2 := by
      funext p
      exact UpperHalfPlane.pslMk_smul p.1 p.2
    rw [hfun]
    exact continuous_smul

/-- The effective `PSL(2, ℝ)` action on the upper half-plane is transitive. -/
instance : MulAction.IsPretransitive PSL(2, ℝ) ℍ where
  exists_smul_eq x y := by
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq SL(2, ℝ) x y
    exact ⟨(g : PSL(2, ℝ)), by simpa only [UpperHalfPlane.pslMk_smul] using hg⟩

/-- The orbit map at `I` for the effective `PSL(2, ℝ)` action is proper. -/
theorem isProperMap_psl_smul_I : IsProperMap fun g : PSL(2, ℝ) ↦ g • I := by
  apply isProperMap_of_comp_of_surj QuotientGroup.continuous_mk (by fun_prop)
  · have hfun :
        (fun g : PSL(2, ℝ) ↦ g • I) ∘
            (QuotientGroup.mk : SL(2, ℝ) → PSL(2, ℝ)) =
          fun g : SL(2, ℝ) ↦ g • I := by
      funext g
      exact UpperHalfPlane.pslMk_smul g I
    rw [hfun]
    exact isProperMap_smul_I
  · exact QuotientGroup.mk_surjective

/-- The effective `PSL(2, ℝ)` action on the upper half-plane is proper. -/
instance : ProperSMul PSL(2, ℝ) ℍ :=
  MulAction.properSMul_of_proper_orbitMap isProperMap_psl_smul_I

/-- Every discrete subgroup of `PSL(2, ℝ)` acts properly discontinuously on the upper
half-plane. -/
instance (G : Subgroup PSL(2, ℝ)) [DiscreteTopology G] : ProperlyDiscontinuousSMul G ℍ := by
  have : IsClosed (G : Set PSL(2, ℝ)) := Subgroup.isClosed_of_discrete
  rw [properlyDiscontinuousSMul_iff_properSMul]
  infer_instance

end TauCeti
