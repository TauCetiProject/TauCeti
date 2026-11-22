/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Topology.Grassmannian.Oriented
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient

/-!
# Unoriented Grassmannians as quotients of orientation covers

The orientation cover of the tautological bundle has two orientation rays over every plane,
including a zero-dimensional plane. Its deck action identifies these rays. The quotient is
homeomorphic to the existing finite real Grassmannian in every rank.
-/

@[expose] public section

noncomputable section

open Topology

namespace TauCeti.finiteGrassmannian

/-- The unoriented Grassmannian is the quotient of the tautological orientation cover by
orientation reversal. This comparison includes rank zero, where the orientation cover still
has two rays over each plane. -/
def orientationCoverQuotientHomeomorph (r N : ℕ) :
    MulAction.orbitRel.Quotient ℤˣ
      (VectorBundleOrientationCover (Fin r → ℝ) (Tautological ℝ r N) (Fin r)) ≃ₜ
        finiteGrassmannian ℝ r N := by
  let q : VectorBundleOrientationCover (Fin r → ℝ) (Tautological ℝ r N) (Fin r) →
      finiteGrassmannian ℝ r N := VectorBundleOrientationCover.proj
  have hcover : IsQuotientCoveringMap q ℤˣ :=
    VectorBundleOrientationCover.isQuotientCoveringMap_proj
      (F := Fin r → ℝ) (E := Tautological ℝ r N) (ι := Fin r) (by simp)
  have hq : IsQuotientMap q :=
    hcover.toIsQuotientMap
  exact (Homeomorph.Quotient.congrRight
    (r' := Setoid.ker q)
    (fun _ _ ↦ MulAction.orbitRel_apply.trans
      hcover.apply_eq_iff_mem_orbit.symm)).trans
      (IsQuotientMap.homeomorph (f := ⟨q, hq.continuous⟩) hq)

/-- Even a zero-dimensional plane has two orientation rays in the orientation cover.
The quotient homeomorphism above identifies them. -/
theorem encard_orientationCover_preimage_zero (N : ℕ)
    (V : finiteGrassmannian ℝ 0 N) :
    (VectorBundleOrientationCover.proj ⁻¹' {V} :
      Set (VectorBundleOrientationCover (Fin 0 → ℝ) (Tautological ℝ 0 N) (Fin 0))).encard = 2 :=
  VectorBundleOrientationCover.encard_preimage_proj_singleton (by simp) V

end TauCeti.finiteGrassmannian
