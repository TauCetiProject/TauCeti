/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.GroupAction.Quotient
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient
public import TauCeti.Topology.Grassmannian.Tautological

/-!
# Unoriented Grassmannians as quotients of orientation covers

The orientation cover of the tautological bundle modulo reversal is the finite real
Grassmannian in every rank. This includes rank zero: the cover has two orientation rays
over each zero-dimensional plane by
`TauCeti.VectorBundleOrientationCover.encard_preimage_proj_singleton`.

Adapted from Riccardo Brasca's `ForTauCeti` formalization in
[`ColdingMinicozziTheory`](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/da0b24e3e36d7cea357e89c727969582ebee8353/ForTauCeti/Topology/Grassmannian/Unoriented.lean).
-/

public section

noncomputable section

namespace TauCeti.finiteGrassmannian

/-- The unoriented Grassmannian is the deck quotient of the tautological orientation
cover in every rank. -/
def orientationCoverQuotientHomeomorph (r N : ℕ) :
    MulAction.orbitRel.Quotient ℤˣ
      (VectorBundleOrientationCover (Fin r → ℝ) (Tautological ℝ r N) (Fin r)) ≃ₜ
        finiteGrassmannian ℝ r N :=
  let hq := VectorBundleOrientationCover.isQuotientCoveringMap_proj
    (F := Fin r → ℝ) (E := Tautological ℝ r N) (ι := Fin r) (by simp)
  hq.toIsQuotientMap.orbitRelQuotientHomeomorph (fun _ _ ↦ hq.apply_eq_iff_mem_orbit)

@[simp]
theorem orientationCoverQuotientHomeomorph_mk (r N : ℕ)
    (p : VectorBundleOrientationCover (Fin r → ℝ) (Tautological ℝ r N) (Fin r)) :
    orientationCoverQuotientHomeomorph r N (Quotient.mk _ p) = p.proj := by
  unfold orientationCoverQuotientHomeomorph
  exact Topology.IsQuotientMap.orbitRelQuotientHomeomorph_mk _ _ p

@[simp]
theorem orientationCoverQuotientHomeomorph_symm_proj (r N : ℕ)
    (p : VectorBundleOrientationCover (Fin r → ℝ) (Tautological ℝ r N) (Fin r)) :
    (orientationCoverQuotientHomeomorph r N).symm p.proj = Quotient.mk _ p := by
  unfold orientationCoverQuotientHomeomorph
  exact Topology.IsQuotientMap.orbitRelQuotientHomeomorph_symm_apply _ _ p

end TauCeti.finiteGrassmannian
