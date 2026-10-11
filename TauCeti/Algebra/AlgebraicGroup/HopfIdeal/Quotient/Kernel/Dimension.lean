/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.Tangent
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Quotient.Kernel.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Regularity
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import TauCeti.RingTheory.Spectrum.Prime.Topology
import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Flat
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
import TauCeti.Algebra.Lie.Submodule.Finrank
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Geometric dimensions of scheme-theoretic kernels

For a schematically dominant homomorphism of finite-type affine groups over a field with
geometrically reduced target, the dimension of its scheme-theoretic kernel plus that of the
target equals the dimension of the source. The source and kernel may be nonreduced, and the
field need not be perfect. Over an algebraically closed field the more general formula holds
for every flat homomorphism, without reducedness assumptions.

For smooth source and target, the kernel is smooth exactly when the differential at the identity
is surjective. This compares the geometric dimension formula with the kernel of the Lie
differential; it detects inseparability even when both ambient groups are smooth.

## References

* J. S. Milne, *Algebraic Groups* (2017), §1.e, Proposition 1.63, and §10.a.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §§11 and 14.

The dimension calculation uses Mathlib's
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` at the augmentation ideals, together
with `HopfAlgebra.ringKrullDim_eq_height_augmentation`. The smoothness criterion uses
`CommHopfAlgCat.kernelLieEquiv` and `HopfAlgebra.smooth_iff_finrank_lie_eq_ringKrullDim`.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{v} k}

/-- For a flat homomorphism of finite-type affine groups over an algebraically closed field,
the dimension of the scheme-theoretic kernel plus that of the target is that of the source.
The coordinate arrow `f : H ⟶ K` represents `Spec K → Spec H`; no smoothness or reducedness
assumption is needed. -/
theorem ringKrullDim_kernel_add_eq_of_flat [IsAlgClosed k]
    [Algebra.FiniteType k H] [Algebra.FiniteType k K]
    (f : H ⟶ K) (hf : f.hom.toAlgHom.toRingHom.Flat) :
    ringKrullDim (K ⧸ (kernelHopfIdeal f).toIdeal) + ringKrullDim H = ringKrullDim K := by
  let _ := f.hom.toAlgHom.toAlgebra
  let _ : Module.Flat H K := hf
  let _ : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  let _ : IsNoetherianRing K := Algebra.FiniteType.isNoetherianRing k K
  let p := Bialgebra.AugmentationIdeal k H
  let P := Bialgebra.AugmentationIdeal k K
  have hcomap : P.comap (algebraMap H K) = p := by
    ext x
    simp [P, p, Bialgebra.AugmentationIdeal, RingHom.mem_ker,
      RingHom.algebraMap_toAlgebra, CoalgHomClass.counit_comp_apply]
  let _ : P.LiesOver p := ⟨hcomap.symm⟩
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown p P
  have hkernel : p.map (algebraMap H K) = (kernelHopfIdeal f).toIdeal := by
    rw [kernelHopfIdeal_toIdeal, HopfIdeal.augmentation_toIdeal]
    rfl
  rw [hkernel] at hheight
  have hmap : P.map (Ideal.Quotient.mk (kernelHopfIdeal f).toIdeal) =
      Bialgebra.AugmentationIdeal k (K ⧸ (kernelHopfIdeal f).toIdeal) := by
    have h := congrArg HopfIdeal.toIdeal
      (kernelHopfIdeal_eq_augmentation_of_surjective
        (mkQuotient K (kernelHopfIdeal f)) (mkQuotient_surjective _ _))
    rw [kernelHopfIdeal_toIdeal, HopfIdeal.augmentation_toIdeal] at h
    rw [HopfIdeal.augmentation_toIdeal] at h
    have hq : ((mkQuotient K (kernelHopfIdeal f)).hom :
        K →+* (K ⧸ (kernelHopfIdeal f).toIdeal)) =
        Ideal.Quotient.mk (kernelHopfIdeal f).toIdeal := by
      ext x
      rfl
    rw [hq] at h
    simpa only [P, Bialgebra.AugmentationIdeal, RingHom.ker_coe_toRingHom] using h
  rw [hmap] at hheight
  rw [HopfAlgebra.ringKrullDim_eq_height_augmentation (k := k),
    HopfAlgebra.ringKrullDim_eq_height_augmentation (k := k),
    HopfAlgebra.ringKrullDim_eq_height_augmentation (k := k)]
  exact_mod_cast (add_comm _ _).trans hheight.symm

/-- A schematically dominant homomorphism of finite-type affine groups with geometrically
reduced target satisfies the kernel dimension formula over any field. The source and kernel
need not be smooth or reduced. -/
theorem ringKrullDim_kernel_add_eq_of_injective
    [Algebra.FiniteType k H] [Algebra.FiniteType k K]
    [Algebra.IsGeometricallyReduced k H]
    (f : H ⟶ K) (hf : Function.Injective f.hom) :
    ringKrullDim (K ⧸ (kernelHopfIdeal f).toIdeal) + ringKrullDim H = ringKrullDim K := by
  let L := AlgebraicClosure k
  let HL := baseChange (K := L) H
  let KL := baseChange (K := L) K
  let fL := baseChangeMap (K := L) f
  have hinj : Function.Injective fL.hom := baseChangeMap_injective f hf
  have hflat := faithfullyFlat_of_dominant fL
    ((RingHom.denseRange_comap_iff_injective _).mpr hinj)
  have hdim := ringKrullDim_kernel_add_eq_of_flat fL hflat.flat
  let e := quotientBaseChangeIso (K := L) (kernelHopfIdeal f)
  have hkerdim : ringKrullDim (KL ⧸ (kernelHopfIdeal fL).toIdeal) =
      ringKrullDim (K ⧸ (kernelHopfIdeal f).toIdeal) := by
    rw [← baseChangeHopfIdeal_kernelHopfIdeal]
    exact (ringKrullDim_eq_of_ringEquiv
      (_root_.CommHopfAlgCat.ofIso e).toAlgEquiv.toRingEquiv).trans
        (ringKrullDim_tensorProduct_field_of_finiteType L _)
  rw [hkerdim] at hdim
  simpa only [HL, KL, baseChange, ringKrullDim_tensorProduct_field_of_finiteType] using hdim

/-- For a schematically dominant homomorphism between smooth finite-type affine groups, its
scheme-theoretic kernel is smooth exactly when the Lie differential is surjective. This holds
over any field and in arbitrary characteristic. -/
theorem algebraSmooth_quotient_kernelHopfIdeal_iff_surjective_derivationCompLieHom
    [Algebra.Smooth k H] [Algebra.Smooth k K]
    (f : H ⟶ K) (hf : Function.Injective f.hom) :
    Algebra.Smooth k (K ⧸ (kernelHopfIdeal f).toIdeal) ↔
      Function.Surjective (derivationCompLieHom (B := k) f.hom) := by
  let _ : Algebra.IsGeometricallyReduced k H := isGeometricallyReduced_of_smooth k H
  have hdim := ringKrullDim_kernel_add_eq_of_injective f hf
  have hH := (HopfAlgebra.smooth_iff_finrank_lie_eq_ringKrullDim (k := k) (H := H)).mp
    (inferInstance : Algebra.Smooth k H)
  have hK := (HopfAlgebra.smooth_iff_finrank_lie_eq_ringKrullDim (k := k) (H := K)).mp
    (inferInstance : Algebra.Smooth k K)
  rw [HopfAlgebra.smooth_iff_finrank_lie_eq_ringKrullDim, finrank_kernelLie]
  let df := (derivationCompLieHom (B := k) f.hom).toLinearMap
  have hrank := df.finrank_range_add_finrank_ker
  rw [← finrank_toSubmodule, LieHom.ker_toSubmodule]
  constructor
  · intro hker
    have hsum : Module.finrank k (LinearMap.ker df) +
        Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) =
        Module.finrank k (Derivation k K (Bialgebra.CounitAlgebra k K k)) := by
      rw [← hker, ← hH, ← hK] at hdim
      exact_mod_cast hdim
    have hrange : Module.finrank k (LinearMap.range df) =
        Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) := by omega
    exact LinearMap.range_eq_top.mp (Submodule.eq_top_of_finrank_eq hrange)
  · intro hsurj
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrank
    have hsum : (Module.finrank k (LinearMap.ker df) : WithBot ℕ∞) + ringKrullDim H =
        ringKrullDim K := by
      rw [← hH, ← hK]
      exact_mod_cast (by omega : Module.finrank k (LinearMap.ker df) +
        Module.finrank k (Derivation k H (Bialgebra.CounitAlgebra k H k)) =
        Module.finrank k (Derivation k K (Bialgebra.CounitAlgebra k K k)))
    have hcancel := hsum.trans hdim.symm
    rw [← hH] at hcancel
    exact ((ENat.addLECancellable_natCast _).withBot).injective_left hcancel

end TauCeti.CommHopfAlgCat
