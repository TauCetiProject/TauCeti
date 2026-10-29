/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.DeformationRetract
public import TauCeti.Topology.Homotopy.HurewiczFibration.Basic

/-!
# Preimages of weak deformation retracts under Hurewicz fibrations

Let `p : E → B` be a Hurewicz fibration and let `K` deform `B` onto a subset `S` in the weak
sense: `K` starts at the identity, ends inside `S` and keeps `S` inside `S`. Lifting `K` along `p`,
starting at the identity (`TauCeti.IsHurewiczFibration.liftDeformation`), deforms `E` onto
`p⁻¹ S` in the same sense, so the inclusion `p⁻¹ S → E` is a homotopy equivalence
(`TauCeti.IsHurewiczFibration.preimageHomotopyEquiv`).

## Main definitions

* `TauCeti.IsHurewiczFibration.preimageHomotopyEquiv`: the inclusion of the preimage of a weak
  deformation retract under a Hurewicz fibration, as a homotopy equivalence.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0, Exercise 4
  (deformation retractions in the weak sense).
-/

public section

open Set unitInterval ContinuousMap

universe u v

namespace TauCeti.IsHurewiczFibration

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] {p : E → B}
  {S : Set B}

/-- **The preimage of a weak deformation retract under a Hurewicz fibration.** Let `K` deform the
base of a Hurewicz fibration `p` onto `S` in the weak sense: it starts at the identity, ends inside
`S` and keeps `S` inside `S`. Then the inclusion of `p⁻¹ S` into the total space is a homotopy
equivalence, whose homotopy inverse is the end of the lift of `K` starting at the identity. -/
noncomputable def preimageHomotopyEquiv (hp : IsHurewiczFibration.{u} p) (K : C(I × B, B))
    (h₀ : ∀ b, K (0, b) = b) (h₁ : ∀ b, K (1, b) ∈ S) (hS : ∀ t b, b ∈ S → K (t, b) ∈ S) :
    p ⁻¹' S ≃ₕ E :=
  (HomotopyEquiv.ofWeakDeformationRetraction (subset_univ (p ⁻¹' S))
    (fun z : I × (univ : Set E) ↦ hp.liftDeformation K h₀ (z.1, z.2)) (by fun_prop)
    (fun _ ↦ mem_univ _) (fun e ↦ hp.liftDeformation_zero K h₀ e)
    (fun e ↦ mem_preimage.2 (by rw [hp.apply_liftDeformation K h₀]; exact h₁ _))
    (fun t e he ↦ mem_preimage.2 (by rw [hp.apply_liftDeformation K h₀]; exact hS t _ he))).trans
    (Homeomorph.Set.univ E).toHomotopyEquiv

/-- The homotopy equivalence `TauCeti.IsHurewiczFibration.preimageHomotopyEquiv` is the
inclusion. -/
@[simp]
theorem preimageHomotopyEquiv_apply (hp : IsHurewiczFibration.{u} p) (K : C(I × B, B))
    (h₀ : ∀ b, K (0, b) = b) (h₁ : ∀ b, K (1, b) ∈ S) (hS : ∀ t b, b ∈ S → K (t, b) ∈ S)
    (e : p ⁻¹' S) : hp.preimageHomotopyEquiv K h₀ h₁ hS e = e := by
  simp [preimageHomotopyEquiv]

/-- The homotopy inverse of `TauCeti.IsHurewiczFibration.preimageHomotopyEquiv` is the end of
the lift of the deformation. -/
@[simp]
theorem coe_preimageHomotopyEquiv_symm_apply (hp : IsHurewiczFibration.{u} p) (K : C(I × B, B))
    (h₀ : ∀ b, K (0, b) = b) (h₁ : ∀ b, K (1, b) ∈ S) (hS : ∀ t b, b ∈ S → K (t, b) ∈ S)
    (e : E) :
    ((hp.preimageHomotopyEquiv K h₀ h₁ hS).symm e : E) = hp.liftDeformation K h₀ (1, e) :=
  -- The homotopy inverse of `Homeomorph.Set.univ E` is the identity on underlying points.
  HomotopyEquiv.coe_ofWeakDeformationRetraction_symm_apply ..

end TauCeti.IsHurewiczFibration
