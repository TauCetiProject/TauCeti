/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Tangent.KrullDimension
public import TauCeti.Algebra.AlgebraicGroup.Smooth.AlgebraicallyClosed
import Mathlib.Algebra.Field.ULift
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.LocalProperties.Reduced
import TauCeti.Algebra.AlgebraicGroup.GeometricallyReduced.BaseChange
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.BaseChange
import TauCeti.AlgebraicGeometry.Scheme.RegularLocalRing
import TauCeti.RingTheory.FiniteType.PointSeparation
import TauCeti.RingTheory.KrullDimension.FiniteType
import TauCeti.RingTheory.RegularLocalRing.Basic
import TauCeti.RingTheory.Smooth.Regular

/-!
# Smoothness detected by Lie dimension

A finite-type affine group over a field is smooth exactly when its dimension equals the
dimension of its tangent Lie algebra at the identity. No reducedness, connectedness, or
perfection hypothesis is needed, and the criterion detects non-smooth group schemes in
positive characteristic.

Over an algebraically closed field, translations identify the local rings at rational points
with the local ring at the identity. Regularity at the identity therefore makes every maximal
localization reduced, hence makes the coordinate ring reduced and the group smooth. The
dimension criterion follows from the existing cotangent-space characterization of regularity.
Extension to an algebraic closure preserves both dimensions and detects smoothness, giving the
criterion over an arbitrary field.

## References

* J. S. Milne, *Algebraic Groups* (2017), §§1.e and 10.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §11.

The formal ingredients are `TauCeti.HopfAlgebra.isRegularLocalRing_augmentationStalk_iff`,
`TauCeti.IsRegularLocalRing.isDomain`, and Mathlib's `isReduced_ofLocalizationMaximal`.
The translation calculation uses `TauCeti.HopfAlgebra.counitAlgHom_comp_rightTranslationAlgHom`,
as in the proof of `TauCeti.HopfAlgebra.height_kernel_eq_height_augmentation`.
-/

public section

open AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti.HopfAlgebra

universe u v

variable {k : Type u} {H : Type v} [Field k] [CommRing H] [_root_.HopfAlgebra k H]

section AlgebraicallyClosed

variable [IsAlgClosed k]

/-- A finite-type affine group over an algebraically closed field is smooth exactly when its
local ring at the identity is regular. -/
theorem smooth_iff_isRegularLocalRing_augmentationStalk [Algebra.FiniteType k H] :
    Algebra.Smooth k H ↔ IsRegularLocalRing
      ((Spec (CommRingCat.of H)).presheaf.stalk (Bialgebra.augmentationPoint k H)) := by
  constructor
  · intro hs
    let _ := hs
    let _ : IsRegularRing H := IsRegularRing.of_smooth (R := k)
    infer_instance
  · intro hr
    let _ := hr
    have hreg : IsRegularLocalRing (Localization.AtPrime (Bialgebra.AugmentationIdeal k H)) :=
      _root_.IsRegularLocalRing.of_ringEquiv
        (IsLocalization.algEquiv (Bialgebra.AugmentationIdeal k H).primeCompl
          ((Spec (CommRingCat.of H)).presheaf.stalk (Bialgebra.augmentationPoint k H))
          (Localization.AtPrime (Bialgebra.AugmentationIdeal k H))).toRingEquiv
    have hred : IsReduced H := by
      apply isReduced_ofLocalizationMaximal H
      intro m hm
      let _ := hm
      obtain ⟨g, hmg, -⟩ := exists_algHom_apply_ne_zero_of_notMem_radical
        (k := k) (K := k) m (x := 1) (by simpa only [hm.isPrime.radical] using m.one_notMem)
      have hker : RingHom.ker (g : H →+* k) = m :=
        (hm.eq_of_le (RingHom.ker_ne_top g.toRingHom) hmg).symm
      let e := (rightTranslationAlgEquiv (WithConv.toConv g)).toRingEquiv
      have hcomap : (Bialgebra.AugmentationIdeal k H).comap e = m := by
        rw [← hker, ← Ideal.comap_coe (f := e)]
        simpa only [e, RingHom.comap_ker, AlgHom.comp_toRingHom,
          ← rightTranslationAlgEquiv_toAlgHom, AlgEquiv.toAlgHom_toRingHom,
          AlgEquiv.toRingEquiv_toRingHom] using
          congrArg (fun f : H →ₐ[k] k ↦ RingHom.ker (f : H →+* k))
            (counitAlgHom_comp_rightTranslationAlgHom (WithConv.toConv g))
      let t := IsLocalization.ringEquivOfRingEquiv
        (Localization.AtPrime ((Bialgebra.AugmentationIdeal k H).comap e))
        (Localization.AtPrime (Bialgebra.AugmentationIdeal k H)) e
        (e.map_primeCompl_comap_eq (Bialgebra.AugmentationIdeal k H))
      have hlocal := _root_.IsRegularLocalRing.of_ringEquiv t.symm
      cases hcomap
      let _ := hlocal
      infer_instance
    let _ := hred
    exact (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_isAlgClosed_of_isReduced k (_root_.CommHopfAlgCat.of k H))

end AlgebraicallyClosed

/-- A finite-type affine group over any field is smooth exactly when its Lie dimension equals
its Krull dimension. This criterion includes non-reduced group schemes and imperfect fields. -/
theorem smooth_iff_finrank_lie_eq_ringKrullDim [Algebra.FiniteType k H] :
    Algebra.Smooth k H ↔
      (Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) : WithBot ℕ∞) =
        ringKrullDim H := by
  let K := AlgebraicClosure (ULift.{v} k)
  let _ : Algebra k K := Algebra.compHom K (algebraMap k (ULift.{v} k))
  have hdim :
      (Module.finrank K
        (Derivation K (K ⊗[k] H) (Bialgebra.CounitAlgebra K (K ⊗[k] H) K)) : WithBot ℕ∞) =
          ringKrullDim (K ⊗[k] H) ↔
      (Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) : WithBot ℕ∞) =
          ringKrullDim H := by
    rw [finrank_lie_baseChange, ringKrullDim_tensorProduct_field_of_finiteType]
  rw [← hdim, ← isRegularLocalRing_augmentationStalk_iff (k := K) (H := K ⊗[k] H),
    ← smooth_iff_isRegularLocalRing_augmentationStalk]
  constructor
  · intro hs
    let _ := hs
    exact Algebra.Smooth.baseChange k H K
  · intro hs
    have hgeom : geometricallyReducedCommHopfAlgProperty K
        (CommHopfAlgCat.baseChange (K := K) (_root_.CommHopfAlgCat.of k H)) :=
      geometricallyReducedCommHopfAlgProperty_of_smooth K
        (CommHopfAlgCat.baseChange (K := K) (_root_.CommHopfAlgCat.of k H))
        ((smoothCommHopfAlgProperty_iff _).mpr hs)
    exact (smoothCommHopfAlgProperty_iff _).mp
      (smoothCommHopfAlgProperty_of_geometricallyReduced k (_root_.CommHopfAlgCat.of k H)
        (geometricallyReducedCommHopfAlgProperty.of_baseChange K
          (_root_.CommHopfAlgCat.of k H) hgeom))

end TauCeti.HopfAlgebra
