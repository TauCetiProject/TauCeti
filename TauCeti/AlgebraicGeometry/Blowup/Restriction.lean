/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.IdealSheaf
public import TauCeti.AlgebraicGeometry.Blowup.AwayFromCenter
import TauCeti.AlgebraicGeometry.Blowup.BaseChange
import TauCeti.AlgebraicGeometry.Restrict

/-!
# Restricting a blowup away from its centre

The blowup of a scheme along an ideal sheaf is an isomorphism over every open disjoint
from the closed subscheme defined by the ideal. No finite-generation hypothesis is needed.
This allows blowups with centre in a special fibre to preserve the complementary open,
including its identification with the generic fibre.

The proof uses the affine blowup calculation and the affine charts of relative `Proj`.
It does not require a global universal property for the blowup.

## References

* The Stacks Project, Lemma 31.32.4, Tag 02OG.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace
open TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.IdealSheafData

universe u

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The affine chart of a blowup changes nothing on an open contained in its base chart
and disjoint from the centre. -/
private theorem isIso_blowupToBase_restrict_of_le_affine {U V : X.Opens}
    (hV : IsAffineOpen V) (hUV : U ≤ V)
    (hU : Disjoint (U : Set X) (I.support : Set X)) :
    IsIso (I.blowupToBase ∣_ U) := by
  have hj : IsIso (hV.fromSpec ∣_ U) :=
    hV.fromSpec.isIso_morphismRestrict_of_le_opensRange (by
      rw [hV.opensRange_fromSpec]
      exact hUV)
  have hdisj : Disjoint (hV.fromSpec ⁻¹' (U : Set X))
      (PrimeSpectrum.zeroLocus (I.ideal ⟨V, hV⟩ : Set Γ(X, V))) := by
    refine Set.disjoint_left.mpr fun x hx hxI ↦ ?_
    have hxV : hV.fromSpec x ∈ V := hV.range_fromSpec.le ⟨x, rfl⟩
    have hxS : hV.fromSpec x ∈ I.support := by
      rw [mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV]
      exact (hV.fromSpec_image_zeroLocus _).le ⟨x, hxI, rfl⟩ |>.1
    exact Set.disjoint_left.mp hU hx hxS
  have hg : IsIso (Proj.toSpecCoeff (reesAlgebra.grade (I.ideal ⟨V, hV⟩)) ∣_
      hV.fromSpec ⁻¹ᵁ U) := by
    rw [toSpecCoeff_reesAlgebra]
    exact isIso_morphismRestrict_toSpecZero_reesAlgebra_of_disjoint_zeroLocus
      (U := hV.fromSpec ⁻¹ᵁ U) hdisj
  refine I.blowupToBase.isIso_morphismRestrict_of_isIso_comp (I.blowupChart hV) ?_ ?_
  · rw [I.opensRange_blowupChart hV]
    exact I.blowupToBase.preimage_mono hUV
  · rw [I.blowupChart_blowupToBase hV, morphismRestrict_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hg hj

/-- **A blowup is an isomorphism away from its centre.** For any ideal sheaf on any scheme,
the blowup restricts to an isomorphism over every open disjoint from the support of the
ideal sheaf. In particular, neither finite type nor Noetherianity is required. -/
theorem isIso_blowupToBase_restrict_of_disjoint_support {U : X.Opens}
    (hU : Disjoint (U : Set X) (I.support : Set X)) :
    IsIso (I.blowupToBase ∣_ U) := by
  let V (W : X.affineOpens) : U.toScheme.Opens := U.ι ⁻¹ᵁ W.1
  have hV : ⨆ W, V W = ⊤ := by
    simp only [V, ← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top,
      Scheme.Hom.preimage_top]
  rw [← MorphismProperty.isomorphisms.iff,
    IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := .isomorphisms _) V hV]
  intro W
  refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict I.blowupToBase U (V W))).mpr ?_
  exact (MorphismProperty.isomorphisms.iff _).mpr
    (I.isIso_blowupToBase_restrict_of_le_affine W.2 (U.ι.image_preimage_le W.1)
      (hU.mono_left (by
        intro x hx
        obtain ⟨y, _, rfl⟩ := hx
        exact y.2)))

/-- The blowup is canonically isomorphic to the base over the complement of its centre. -/
instance isIso_blowupToBase_restrict_compl_support :
    IsIso (I.blowupToBase ∣_ I.support.compl) :=
  I.isIso_blowupToBase_restrict_of_disjoint_support disjoint_compl_left

end AlgebraicGeometry.Scheme.IdealSheafData
