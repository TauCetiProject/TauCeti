/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Scheme-theoretic images

This file contains general results about Mathlib's scheme-theoretic image construction.
For a quasi-compact morphism the map onto its scheme-theoretic image is
scheme-theoretically dominant. In particular, a reduced source gives a reduced image.
When the topological image is closed, the factorization is surjective on points.

## Main declarations

* `TauCeti.specTargetImageIdeal_specMap`: the ideal defining the image of a spectrum map is the
  kernel of the corresponding ring homomorphism.

## References

* The Stacks Project, Tag 01R5, especially Lemmas 29.6.3 and 29.6.7.
-/

public section

open CategoryTheory Opposite

namespace TauCeti

open AlgebraicGeometry

universe u

variable {R S : CommRingCat.{u}}

/-- The ideal defining the scheme-theoretic image of a spectrum map is the kernel of the
corresponding ring homomorphism. -/
@[simp]
theorem specTargetImageIdeal_specMap (f : R ⟶ S) :
    specTargetImageIdeal (Spec.map f) = RingHom.ker f.hom := by
  rw [specTargetImageIdeal]
  rw [Adjunction.homEquiv_symm_apply]
  -- The image ideal is phrased through the `Γ ⊣ Spec` adjunction. Normalize its recovered
  -- coordinate map to the explicit global-sections map before using naturality of `ΓSpecIso`.
  change RingHom.ker (((Scheme.ΓSpecIso R).inv ≫ (Spec.map f).appTop).hom) = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  exact (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.map_eq_zero_iff

end TauCeti

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]

/-- The factorization through the scheme-theoretic image is scheme-theoretically dominant. -/
instance isSchemeTheoreticallyDominant_toImage : IsSchemeTheoreticallyDominant f.toImage := by
  let U : Y.affineOpens → f.image.affineOpens := fun U ↦
    ⟨f.imageι ⁻¹ᵁ U, U.2.preimage _⟩
  have hU : ⨆ V, (U V).1 = ⊤ := by
    simp only [U]
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  constructor
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top U hU
  intro V
  rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot]
  exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective V)

/-- The scheme-theoretic image of a quasi-compact morphism from a reduced scheme is reduced. -/
instance isReduced_image [IsReduced X] : IsReduced f.image :=
  IsSchemeTheoreticallyDominant.isReduced f.toImage

/-- If a quasi-compact morphism has closed topological image, its map to the
scheme-theoretic image is surjective. -/
theorem toImage_surjective_of_isClosed_range (h : IsClosed (Set.range f)) :
    Function.Surjective f.toImage := by
  apply (surjective_of_isDominant_of_isClosed_range f.toImage ?_).surj
  have h' := h.preimage f.imageι.continuous
  simpa only [← f.toImage_imageι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    f.imageι.isEmbedding.injective.preimage_image] using h'

end AlgebraicGeometry.Scheme.Hom
