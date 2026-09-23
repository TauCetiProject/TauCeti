/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.LyapunovPerron.Local

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

private def graphHomeomorphRange (P : X →L[ℝ] X) (hP : IsIdempotentElem P) (g : X → X)
    (hPg : ∀ v, P (g v) = 0) (hg : Continuous g) :
    range P ≃ₜ range (fun v : range P ↦ (v : X) + g v) where
  toEquiv :=
    { toFun := fun v ↦ ⟨v + g v, ⟨v, rfl⟩⟩
      invFun := fun z ↦ ⟨P z, ⟨z, rfl⟩⟩
      left_inv := by
        rintro ⟨v, ⟨w, rfl⟩⟩
        apply Subtype.ext
        have h : P (P w + g (P w)) = P w := by
          rw [map_add, hPg, add_zero, ← mul_apply_eq_comp, hP.eq]
        exact h
      right_inv := by
        rintro ⟨_, ⟨v, rfl⟩⟩
        apply Subtype.ext
        obtain ⟨w, hw⟩ := v.2
        have hPv : P (v : X) = v := by
          rw [← hw, ← mul_apply_eq_comp, hP.eq]
        have h : P ((v : X) + g v) + g (P ((v : X) + g v)) = (v : X) + g v := by
          rw [map_add, hPg, add_zero, hPv]
        exact h }
  continuous_toFun :=
    Continuous.subtype_mk
      (continuous_subtype_val.add (hg.comp continuous_subtype_val)) fun _ ↦ ⟨_, rfl⟩
  continuous_invFun :=
    Continuous.subtype_mk (P.continuous.comp continuous_subtype_val) fun z ↦ ⟨z, rfl⟩

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
  by
    unfold localStableGraphHomeomorphRange graphHomeomorphRange
    rfl

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
  by
    unfold localStableGraphHomeomorphRange graphHomeomorphRange
    rfl

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
  by
    unfold localUnstableGraphHomeomorphRange graphHomeomorphRange
    rfl

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
  by
    unfold localUnstableGraphHomeomorphRange graphHomeomorphRange
    rfl

end ContinuousLinearMap

end
