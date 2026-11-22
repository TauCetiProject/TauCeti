/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Orientation.Cover.Quotient
public import TauCeti.Topology.Grassmannian.Tautological

/-!
# Unoriented Grassmannians as quotients of orientation covers

The orientation cover of the tautological bundle modulo reversal is the finite real
Grassmannian in every rank. This includes rank zero: the cover has two orientation rays
over each zero-dimensional plane by
`TauCeti.VectorBundleOrientationCover.encard_preimage_proj_singleton`.
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
  VectorBundleOrientationCover.orbitQuotientHomeomorph (by simp)

@[simp]
theorem orientationCoverQuotientHomeomorph_mk (r N : ℕ)
    (p : VectorBundleOrientationCover (Fin r → ℝ) (Tautological ℝ r N) (Fin r)) :
    orientationCoverQuotientHomeomorph r N (Quotient.mk _ p) = p.proj :=
  VectorBundleOrientationCover.orbitQuotientHomeomorph_mk (by simp) p

@[simp]
theorem orientationCoverQuotientHomeomorph_symm_proj (r N : ℕ)
    (p : VectorBundleOrientationCover (Fin r → ℝ) (Tautological ℝ r N) (Fin r)) :
    (orientationCoverQuotientHomeomorph r N).symm p.proj = Quotient.mk _ p :=
  VectorBundleOrientationCover.orbitQuotientHomeomorph_symm_proj (by simp) p

end TauCeti.finiteGrassmannian
