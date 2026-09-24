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

* `ContinuousLinearMap.localStableGraphHomeomorphRange` parameterizes a local stable graph by
  the range of the stable projection.
* `ContinuousLinearMap.localUnstableGraphHomeomorphRange` is the corresponding result for the
  complementary projection and the local unstable graph map.
* `ContinuousLinearMap.localStableSetHomeomorph` and
  `ContinuousLinearMap.localUnstableSetHomeomorph` restrict these graph embeddings to the
  confined local invariant sets characterized in `LyapunovPerron.Local`.

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

/-- The local stable graph is a topological embedding over the range of its stable
projection.  The inverse on its range is induced by that projection. -/
def localStableGraphHomeomorphRange
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
      ‖NormedSpace.exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
      ‖NormedSpace.exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
    (hsmall : 2 * K * (ε * 2) < α) (hP : IsIdempotentElem P) (hAP : Commute A P) :
    range P ≃ₜ range (fun v : range P ↦
      (v : X) + localStableGraphMap A P N r hs hu hr hN hsmall v) :=
  graphHomeomorphRange P hP (localStableGraphMap A P N r hs hu hr hN hsmall)
    (apply_localStableGraphMap hs hu hr hN hsmall hP hAP)
    (lipschitzWith_localStableGraphMap hs hu hr hN hsmall).continuous

/-- The stable graph parameterization sends a point of the stable spectral subspace to the
corresponding point of the graph. -/
@[simp]
theorem coe_localStableGraphHomeomorphRange_apply
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
      ‖NormedSpace.exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
      ‖NormedSpace.exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
    (hsmall : 2 * K * (ε * 2) < α) (hP : IsIdempotentElem P) (hAP : Commute A P)
    (v : range P) :
    ↑(localStableGraphHomeomorphRange hs hu hr hN hsmall hP hAP v) =
      (v : X) + localStableGraphMap A P N r hs hu hr hN hsmall v :=
  coe_graphHomeomorphRange_apply ..

/-- The inverse of the stable graph parameterization is the stable projection. -/
@[simp]
theorem coe_localStableGraphHomeomorphRange_symm_apply
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
      ‖NormedSpace.exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
      ‖NormedSpace.exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
    (hsmall : 2 * K * (ε * 2) < α) (hP : IsIdempotentElem P) (hAP : Commute A P)
    (z : range (fun v : range P ↦ (v : X) + localStableGraphMap A P N r hs hu hr hN hsmall v)) :
    ↑((localStableGraphHomeomorphRange hs hu hr hN hsmall hP hAP).symm z) = P z :=
  coe_graphHomeomorphRange_symm_apply ..

/-- The local stable set of confined forward solutions, truncated by the norm of its stable
projection, is homeomorphic to the corresponding closed ball in the stable spectral subspace. -/
noncomputable def localStableSetHomeomorph
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
      ‖NormedSpace.exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
      ‖NormedSpace.exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
    (hsmall : 2 * K * (ε * 2) < α) (hN0 : N 0 = 0)
    (hP : IsIdempotentElem P) (hAP : Commute A P) {ρ : ℝ}
    (hρ : (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ ≤ r) :
    {v : range P | ‖(v : X)‖ ≤ ρ} ≃ₜ
      {x : X | (∃ y : ℝ → X, IsIntegralCurveOn y (fun _ z ↦ A z + N z) (Ici 0) ∧
          y 0 = x ∧ MapsTo y (Ici 0) (closedBall 0 r)) ∧ ‖P x‖ ≤ ρ} :=
  ((isEmbedding_graph P hP (localStableGraphMap A P N r hs hu hr hN hsmall)
    (apply_localStableGraphMap hs hu hr hN hsmall hP hAP)
    (lipschitzWith_localStableGraphMap hs hu hr hN hsmall).continuous).homeomorphImage _).trans
    (Homeomorph.setCongr <|
      (image_graph_closedBall P (localStableGraphMap A P N r hs hu hr hN hsmall) ρ).trans
        (setOf_exists_isIntegralCurveOn_mapsTo_closedBall_eq_image hs hu hr hN hsmall
          hN0 hP hAP hρ).symm)

/-- The local unstable graph is a topological embedding over the range of the complementary
projection.  The inverse on its range is induced by that complementary projection. -/
def localUnstableGraphHomeomorphRange
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
      ‖NormedSpace.exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
      ‖NormedSpace.exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
    (hsmall : 2 * K * (ε * 2) < α) (hP : IsIdempotentElem P) (hAP : Commute A P) :
    range (ContinuousLinearMap.id ℝ X - P) ≃ₜ
      range (fun v : range (ContinuousLinearMap.id ℝ X - P) ↦
        (v : X) + localUnstableGraphMap A P N r hs hu hr hN hsmall v) :=
  graphHomeomorphRange (ContinuousLinearMap.id ℝ X - P) hP.one_sub
    (localUnstableGraphMap A P N r hs hu hr hN hsmall)
    (by
      intro v
      rw [sub_apply, id_apply, apply_localUnstableGraphMap hs hu hr hN hsmall hP hAP,
        sub_self])
    (lipschitzWith_localUnstableGraphMap hs hu hr hN hsmall).continuous

/-- The unstable graph parameterization sends a point of the unstable spectral subspace to the
corresponding point of the graph. -/
@[simp]
theorem coe_localUnstableGraphHomeomorphRange_apply
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
      ‖NormedSpace.exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
      ‖NormedSpace.exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
    (hsmall : 2 * K * (ε * 2) < α) (hP : IsIdempotentElem P) (hAP : Commute A P)
    (v : range (ContinuousLinearMap.id ℝ X - P)) :
    ↑(localUnstableGraphHomeomorphRange hs hu hr hN hsmall hP hAP v) =
      (v : X) + localUnstableGraphMap A P N r hs hu hr hN hsmall v :=
  coe_graphHomeomorphRange_apply ..

/-- The inverse of the unstable graph parameterization is the complementary projection. -/
@[simp]
theorem coe_localUnstableGraphHomeomorphRange_symm_apply
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
      ‖NormedSpace.exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
      ‖NormedSpace.exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
    (hsmall : 2 * K * (ε * 2) < α) (hP : IsIdempotentElem P) (hAP : Commute A P)
    (z : range (fun v : range (ContinuousLinearMap.id ℝ X - P) ↦
      (v : X) + localUnstableGraphMap A P N r hs hu hr hN hsmall v)) :
    ↑((localUnstableGraphHomeomorphRange hs hu hr hN hsmall hP hAP).symm z) =
      (ContinuousLinearMap.id ℝ X - P) z :=
  coe_graphHomeomorphRange_symm_apply ..

/-- The local unstable set of confined backward solutions, truncated by the norm of its
complementary projection, is homeomorphic to the corresponding closed ball in the unstable
spectral subspace. -/
noncomputable def localUnstableSetHomeomorph
    (hs : ∀ t : ℝ, 0 ≤ t → ∀ v : X,
      ‖NormedSpace.exp (t • A) (P v)‖ ≤ K * Real.exp (-α * t) * ‖v‖)
    (hu : ∀ t : ℝ, t ≤ 0 → ∀ v : X,
      ‖NormedSpace.exp (t • A) (v - P v)‖ ≤ K * Real.exp (α * t) * ‖v‖)
    (hr : 0 ≤ r) (hN : LipschitzOnWith ε N (closedBall 0 r))
    (hsmall : 2 * K * (ε * 2) < α) (hN0 : N 0 = 0)
    (hP : IsIdempotentElem P) (hAP : Commute A P) {ρ : ℝ}
    (hρ : (K : ℝ) / (1 - 2 * K * ((ε : ℝ) * 2) / α) * ρ ≤ r) :
    {v : range (ContinuousLinearMap.id ℝ X - P) | ‖(v : X)‖ ≤ ρ} ≃ₜ
      {x : X | (∃ y : ℝ → X, IsIntegralCurveOn y (fun _ z ↦ A z + N z) (Iic 0) ∧
          y 0 = x ∧ MapsTo y (Iic 0) (closedBall 0 r)) ∧
          ‖(ContinuousLinearMap.id ℝ X - P) x‖ ≤ ρ} :=
  ((isEmbedding_graph (ContinuousLinearMap.id ℝ X - P) hP.one_sub
    (localUnstableGraphMap A P N r hs hu hr hN hsmall)
    (by
      intro v
      rw [sub_apply, id_apply, apply_localUnstableGraphMap hs hu hr hN hsmall hP hAP,
        sub_self])
    (lipschitzWith_localUnstableGraphMap hs hu hr hN hsmall).continuous).homeomorphImage _).trans
    (Homeomorph.setCongr <|
      (image_graph_closedBall (ContinuousLinearMap.id ℝ X - P)
        (localUnstableGraphMap A P N r hs hu hr hN hsmall) ρ).trans
        (setOf_exists_isIntegralCurveOn_Iic_mapsTo_closedBall_eq_image hs hu hr hN hsmall
          hN0 hP hAP hρ).symm)

end ContinuousLinearMap

end
