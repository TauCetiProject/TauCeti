/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Blowup.ExceptionalDivisor
public import TauCeti.AlgebraicGeometry.Blowup.Restriction
public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.SchematicDensity
public import TauCeti.AlgebraicGeometry.Morphisms.Modification.Centre
import TauCeti.AlgebraicGeometry.IdealSheaf.Comap

/-!
# Blowups are modifications

Let `I` be an ideal sheaf on a scheme `X` whose support `V(I)` has empty interior. The open
complement `X ∖ V(I)` is then dense in `X`, the blowup `Bl_I X ⟶ X` is an isomorphism over it
(`AlgebraicGeometry.Scheme.IdealSheafData.isIso_blowupToBase_restrict_compl_support`), and its
preimage is the complement of the exceptional divisor, an effective Cartier divisor
(`AlgebraicGeometry.Scheme.IdealSheafData.isEffectiveCartier_comap_blowupToBase`). The complement
of an effective Cartier divisor is dense
(`AlgebraicGeometry.Scheme.IdealSheafData.IsEffectiveCartier.dense_support_compl`). So `X ∖ V(I)`
is a modification witness for the blowup (`IdealSheafData.witness_blowupToBase`), and when `I` is
of finite type on affines, so that the blowup is proper, the blowup is a modification
(`IdealSheafData.isModification_blowupToBase`). Its centre lies in `V(I)`.

On an irreducible scheme the interior condition says only that `V(I)` is not everything
(`IdealSheafData.isModification_blowupToBase_of_irreducibleSpace`).

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.witness_blowupToBase`: the complement of `V(I)` is a
  modification witness for the blowup.
* `AlgebraicGeometry.Scheme.IdealSheafData.isModification_blowupToBase`: the blowup along an ideal
  sheaf of finite type whose support has empty interior is a modification.
* `AlgebraicGeometry.Scheme.IdealSheafData.centre_blowupToBase_subset`: its centre lies in the
  support of `I`.

## References

* [Stacks Project, Definition 29.52.11](https://stacks.math.columbia.edu/tag/0AAZ).
-/

public section

open CategoryTheory TopologicalSpace TauCeti.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

namespace Scheme.IdealSheafData

variable {I : X.IdealSheafData}

/-- **The complement of the support of `I` is a modification witness for the blowup.** If the
support of `I` has empty interior, then its open complement is dense, the blowup is an isomorphism
over it, and its preimage, the complement of the exceptional divisor, is dense in the blowup. -/
theorem witness_blowupToBase (hI : interior (I.support : Set X) = ∅) :
    IsModification.Witness I.blowupToBase I.support.compl where
  dense := by
    rw [interior_eq_empty_iff_dense_compl] at hI
    simpa using hI
  dense_preimage := by
    rw [← compl_support_comap]
    exact I.isEffectiveCartier_comap_blowupToBase.dense_support_compl
  isIso := inferInstance

/-- **Blowups are modifications.** The blowup of `X` along an ideal sheaf `I` that is finitely
generated on every affine open, and whose support has empty interior, is a modification of `X`. -/
theorem isModification_blowupToBase (hI : ∀ U : X.affineOpens, (I.ideal U).FG)
    (hint : interior (I.support : Set X) = ∅) : IsModification I.blowupToBase :=
  have := I.isProper_blowupToBase hI
  IsModification.of_witness _ (witness_blowupToBase hint)

/-- The centre of the blowup lies in the support of `I`. -/
theorem centre_blowupToBase_subset : I.blowupToBase.centre ⊆ I.support := by
  intro x hx
  by_contra hxI
  exact (I.blowupToBase.mem_centre_iff.1 hx) I.support.compl hxI inferInstance

/-- On an irreducible locally Noetherian scheme, the blowup along an ideal sheaf whose support is
not everything is a modification. -/
theorem isModification_blowupToBase_of_irreducibleSpace [IrreducibleSpace X]
    [IsLocallyNoetherian X] (hI : I.support ≠ ⊤) : IsModification I.blowupToBase := by
  refine IsModification.of_witness _ (witness_blowupToBase ?_)
  -- In an irreducible space a nonempty open set is dense, and a dense closed set is everything.
  refine Set.not_nonempty_iff_eq_empty.1 fun ⟨x, hx⟩ ↦ hI (SetLike.coe_injective ?_)
  simpa using I.support.isClosed.dense_iff.1
    ((isOpen_interior.dense ⟨x, hx⟩).mono interior_subset)

end Scheme.IdealSheafData

end AlgebraicGeometry
