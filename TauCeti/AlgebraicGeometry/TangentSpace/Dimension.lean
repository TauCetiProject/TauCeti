/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.AlgebraicGeometry.TangentSpace.Affine

/-!
# Dimension and regularity at a rational point

For an augmentation `f : A →ₐ[k] k`, the dimension of `ker(f) / ker(f)²` over `k`
is the embedding dimension of the local ring at the corresponding rational point.
When this local ring is Noetherian, this bounds its Krull dimension, with equality exactly when
the local ring is regular. These statements allow tangent-space calculations in the
coordinate algebra to detect regularity of the affine scheme.

## References

* M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Chapter 11.
-/

public section

open AlgebraicGeometry IsLocalRing

namespace TauCeti

open TauCeti.AlgHom

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] (f : A →ₐ[k] k)

/-- The dimension of the augmentation cotangent space over the ground field equals the
embedding dimension at its rational point, computed over the native residue field. -/
theorem finrank_kernelCotangent_eq_finrank_residueFieldCotangent :
    Module.finrank k (RingHom.ker (f : A →+* k)).Cotangent =
      Module.finrank
        (ResidueField ((Spec (CommRingCat.of A)).presheaf.stalk (kernelPoint f)))
        (IsLocalRing.CotangentSpace
          ((Spec (CommRingCat.of A)).presheaf.stalk (kernelPoint f))) := by
  have h := lift_rank_eq_of_equiv_equiv (kernelResidueFieldRingEquiv f)
    (kernelCotangentLinearEquivZariski f).toAddEquiv
    (kernelResidueFieldRingEquiv f).bijective (fun r x ↦
      ((kernelCotangentLinearEquivZariski f).map_smul r x).trans
        (kernelCotangentLinearEquivZariski_smul f r x))
  simpa only [Cardinal.toNat_lift, Module.finrank] using congrArg Cardinal.toNat h

/-- At a rational point with Noetherian local ring, local dimension is bounded by the
dimension of the augmentation cotangent space. -/
theorem ringKrullDim_kernelStalk_le_finrank_kernelCotangent
    [IsNoetherianRing ((Spec (CommRingCat.of A)).presheaf.stalk (kernelPoint f))] :
    ringKrullDim ((Spec (CommRingCat.of A)).presheaf.stalk (kernelPoint f)) ≤
      Module.finrank k (RingHom.ker (f : A →+* k)).Cotangent := by
  let S := (Spec (CommRingCat.of A)).presheaf.stalk (kernelPoint f)
  rw [finrank_kernelCotangent_eq_finrank_residueFieldCotangent,
    ← spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  exact ringKrullDim_le_spanFinrank_maximalIdeal S

/-- A Noetherian local ring at a rational point of an affine scheme is regular exactly when
its dimension equals the dimension of the augmentation cotangent space. -/
theorem isRegularLocalRing_kernelStalk_iff
    [IsNoetherianRing ((Spec (CommRingCat.of A)).presheaf.stalk (kernelPoint f))] :
    IsRegularLocalRing ((Spec (CommRingCat.of A)).presheaf.stalk (kernelPoint f)) ↔
      (Module.finrank k (RingHom.ker (f : A →+* k)).Cotangent : WithBot ℕ∞) =
        ringKrullDim ((Spec (CommRingCat.of A)).presheaf.stalk (kernelPoint f)) := by
  rw [IsRegularLocalRing.iff_finrank_cotangentSpace,
    finrank_kernelCotangent_eq_finrank_residueFieldCotangent]

end TauCeti
