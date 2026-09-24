/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LyapunovPerron.Local
public import TauCeti.Topology.Algebra.Module.ProjectionGraph

/-!
# Embedded local Lyapunov--Perron graphs

The local stable and unstable sets of a hyperbolic equilibrium are described in
`LyapunovPerron.Local` as graphs over complementary spectral subspaces.  This file records that
these descriptions are actual topological embeddings: projection onto the relevant spectral
subspace is the continuous inverse of the graph parameterization on its image.

This supplies the topological parameterizations used when passing from local invariant sets to
the stable and unstable manifolds used in Morse trajectory spaces.

## Main declarations

* `ContinuousLinearMap.localStableSetHomeomorph` and
  `ContinuousLinearMap.localUnstableSetHomeomorph` parameterize the confined local invariant
  sets by closed balls in their respective spectral subspaces.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 2.
* C. Chicone, *Ordinary Differential Equations with Applications*, 2nd ed., Springer, 2006,
  Section 4.3.
-/

public section

open Metric Set Topology

open scoped NNReal

noncomputable section

namespace ContinuousLinearMap

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
variable {K α ε : ℝ≥0} {A P : X →L[ℝ] X} {N : X → X} {r : ℝ}
variable (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
      ‖NormedSpace.exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
      ‖NormedSpace.exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
    (hsmall : 2 * K * (ε * 2) < α) (hN0 : N 0 = 0)
    (hP : IsIdempotentElem P) (hAP : Commute A P) {ρ : ℝ}
    (hρ : (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ ≤ r)

omit [NormedSpace ℝ X] [CompleteSpace X] in
/-- The closed ball `{v | ‖v‖ ≤ ρ}` in a subtype of `X`, as a preimage of `closedBall 0 ρ`. -/
private theorem setOf_norm_coe_le_eq_preimage (S : Set X) (ρ : ℝ) :
    {v : S | ‖(v : X)‖ ≤ ρ} = Subtype.val ⁻¹' closedBall 0 ρ := by
  ext v
  simp only [mem_ofPred_eq, mem_preimage, mem_closedBall_zero_iff]

/-- The local stable set of confined forward solutions, truncated by the norm of its stable
projection, is homeomorphic to the corresponding closed ball in the stable spectral subspace. -/
noncomputable def localStableSetHomeomorph :
    {v : range P | ‖(v : X)‖ ≤ ρ} ≃ₜ
      {x : X | (∃ y : ℝ → X, IsIntegralCurveOn y (fun _ z ↦ A z + N z) (Ici 0) ∧
          y 0 = x ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P x‖ ≤ ρ} :=
  (Homeomorph.setCongr (setOf_norm_coe_le_eq_preimage _ ρ)).trans <|
    (graphHomeomorph P hP (localStableGraphMap A P N r hs hu hr hN hsmall)
      (apply_localStableGraphMap hs hu hr hN hsmall hP hAP)
      (lipschitzWith_localStableGraphMap hs hu hr hN hsmall).continuous _).trans <|
    Homeomorph.setCongr
      (setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image hs hu hr hN hsmall
        hN0 hP hAP hρ).symm

/-- The local stable set homeomorphism is the graph parameterization `v ↦ v + h(v)`. -/
@[simp]
theorem coe_localStableSetHomeomorph_apply (v : {v : range P | ‖(v : X)‖ ≤ ρ}) :
    (localStableSetHomeomorph hs hu hr hN hsmall hN0 hP hAP hρ v : X) =
      (v : X) + localStableGraphMap A P N r hs hu hr hN hsmall v := by
  simp only [localStableSetHomeomorph, Homeomorph.trans_apply]
  exact coe_graphHomeomorph_apply _ _ _ _ _ _ _

/-- The inverse of the local stable set homeomorphism is the stable projection. -/
@[simp]
theorem coe_localStableSetHomeomorph_symm_apply
    (x : {x : X | (∃ y : ℝ → X, IsIntegralCurveOn y (fun _ z ↦ A z + N z) (Ici 0) ∧
          y 0 = x ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P x‖ ≤ ρ}) :
    (((localStableSetHomeomorph hs hu hr hN hsmall hN0 hP hAP hρ).symm x : range P) : X) =
      P x :=
  coe_graphHomeomorph_symm_apply P hP _ _ _ _ _

/-- The local unstable set of confined backward solutions, truncated by the norm of its
complementary projection, is homeomorphic to the corresponding closed ball in the unstable
spectral subspace. -/
noncomputable def localUnstableSetHomeomorph :
    {v : range (ContinuousLinearMap.id ℝ X - P) | ‖(v : X)‖ ≤ ρ} ≃ₜ
      {x : X | (∃ y : ℝ → X, IsIntegralCurveOn y (fun _ z ↦ A z + N z) (Iic 0) ∧
          y 0 = x ∧ MapsTo y (Iic 0) (closedBall 0 r)) ∧
          ‖(ContinuousLinearMap.id ℝ X - P) x‖ ≤ ρ} :=
  (Homeomorph.setCongr (setOf_norm_coe_le_eq_preimage _ ρ)).trans <|
    (graphHomeomorph (ContinuousLinearMap.id ℝ X - P) hP.one_sub
      (localUnstableGraphMap A P N r hs hu hr hN hsmall)
      (sub_apply_localUnstableGraphMap hs hu hr hN hsmall hP hAP)
      (lipschitzWith_localUnstableGraphMap hs hu hr hN hsmall).continuous _).trans <|
    Homeomorph.setCongr
      (setOf_exists_isIntegralCurveOn_Iic_mapsTo_closedBall_eq_image hs hu hr hN hsmall
        hN0 hP hAP hρ).symm

/-- The local unstable set homeomorphism is the graph parameterization `v ↦ v + h(v)`. -/
@[simp]
theorem coe_localUnstableSetHomeomorph_apply
    (v : {v : range (ContinuousLinearMap.id ℝ X - P) | ‖(v : X)‖ ≤ ρ}) :
    (localUnstableSetHomeomorph hs hu hr hN hsmall hN0 hP hAP hρ v : X) =
      (v : X) + localUnstableGraphMap A P N r hs hu hr hN hsmall v := by
  simp only [localUnstableSetHomeomorph, Homeomorph.trans_apply]
  exact coe_graphHomeomorph_apply _ _ _ _ _ _ _

/-- The inverse of the local unstable set homeomorphism is the unstable projection. -/
@[simp]
theorem coe_localUnstableSetHomeomorph_symm_apply
    (x : {x : X | (∃ y : ℝ → X, IsIntegralCurveOn y (fun _ z ↦ A z + N z) (Iic 0) ∧
          y 0 = x ∧ MapsTo y (Iic 0) (closedBall 0 r)) ∧
          ‖(ContinuousLinearMap.id ℝ X - P) x‖ ≤ ρ}) :
    (((localUnstableSetHomeomorph hs hu hr hN hsmall hN0 hP hAP hρ).symm x :
        range (ContinuousLinearMap.id ℝ X - P)) : X) = (ContinuousLinearMap.id ℝ X - P) x :=
  coe_graphHomeomorph_symm_apply (ContinuousLinearMap.id ℝ X - P) hP.one_sub _ _ _ _ _

end ContinuousLinearMap

end
