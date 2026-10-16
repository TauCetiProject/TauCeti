/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Extension

/-!
# Restriction to subextensions in identified separable closures

A field extension identifies its absolute Galois group with the subgroup fixing its image
in a separable closure of the base. When normal subextensions in the two separable closures
are identified by a compatible ring embedding, restriction to those subextensions commutes
with this subgroup identification. This is the finite-level group square used to compare
inflation of cocycles with restriction of Galois cohomology classes.

## References

* J.-P. Serre, *Local Fields*, GTM 67 (1979), Chapter X, §5.
-/

public section

namespace TauCeti

variable (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L]
  (σ : L →ₐ[K] SeparableClosure K)

/-- Restriction to normal subextensions commutes with the identification of absolute Galois
groups along a field extension. The ring embedding `ι` identifies the subextensions inside the
two separable closures, and `π` intertwines their finite-level automorphisms. -/
theorem restrictNormalHom_equivFixingSubgroup
    (E : IntermediateField K (SeparableClosure K)) [Normal K E]
    (F : IntermediateField L (SeparableClosure L)) [Normal L F]
    (ι : E →+* F) (π : (F ≃ₐ[L] F) →* (E ≃ₐ[K] E))
    (hι : ∀ x : E, (separableClosureRingEquiv K L σ).symm (E.val x) = F.val (ι x))
    (hπ : ∀ g x, ι (π g x) = g (ι x)) (g : AbsoluteGaloisGroup L) :
    π (AlgEquiv.restrictNormalHom F g) =
      AlgEquiv.restrictNormalHom E
        (absoluteGaloisGroupEquivFixingSubgroup K L σ g : AbsoluteGaloisGroup K) := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.val_injective
  apply (separableClosureRingEquiv K L σ).symm.injective
  calc
    (separableClosureRingEquiv K L σ).symm
        (E.val (π (AlgEquiv.restrictNormalHom F g) x)) =
      F.val (ι (π (AlgEquiv.restrictNormalHom F g) x)) := hι _
    _ = F.val (AlgEquiv.restrictNormalHom F g (ι x)) := congrArg F.val (hπ _ x)
    _ = g (F.val (ι x)) := AlgEquiv.restrictNormal_commutes g F (ι x)
    _ = g ((separableClosureRingEquiv K L σ).symm (E.val x)) := congrArg g (hι x).symm
    _ = _ := by
      have hr : E.val (AlgEquiv.restrictNormalHom E
          (absoluteGaloisGroupEquivFixingSubgroup K L σ g : AbsoluteGaloisGroup K) x) =
          (absoluteGaloisGroupEquivFixingSubgroup K L σ g : AbsoluteGaloisGroup K) (E.val x) :=
        AlgEquiv.restrictNormal_commutes _ E x
      simpa only [absoluteGaloisGroupEquivFixingSubgroup_apply, RingEquiv.symm_apply_apply,
        IntermediateField.coe_val]
        using (congrArg (separableClosureRingEquiv K L σ).symm hr).symm

end TauCeti
