/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.Translation
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Surjective
import TauCeti.RingTheory.Spectrum.Prime.GenericFreeness
import TauCeti.RingTheory.RingHom.Flat

/-!
# Flatness of affine group morphisms

Over an algebraically closed field, an affine group morphism with finite-type source is
flat if and only if it is flat at the identity. Right translation identifies the flatness
conditions at rational points, and every closed point of the source is rational. No
smoothness, reducedness, or finite-type hypothesis on the target is needed.

The criterion is stated using the map to the localization of the source coordinate ring.
Equivalently, one can also localize the target coordinate ring at the image point, by
`Module.flat_iff_of_isLocalization`. This is the propagation step in proving flatness of
quotient morphisms: it leaves only flatness at the identity to establish.

Combined with generic freeness, it shows that a dominant homomorphism of finite-type affine
groups onto a reduced group over an algebraically closed field is faithfully flat. Generic
freeness makes the source coordinate ring free over a dense open subset of the target,
dominance and density of rational points produce a rational source point lying over it, and
translation propagates flatness from there to the identity. The source may be nonreduced, and
the morphism need not be finite.

## Main declarations

* `TauCeti.CommHopfAlgCat.flat_iff_flat_localization_augmentation`: flatness can be checked at
  the identity.
* `TauCeti.CommHopfAlgCat.faithfullyFlat_of_dominant`: a dominant homomorphism onto a reduced
  finite-type affine group over an algebraically closed field is faithfully flat.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, for flatness of group homomorphisms
  and the translation argument, and Propositions 1.65(a) and 1.70.
* H. Matsumura, *Commutative Ring Theory*, Theorem 24.1, for generic freeness.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §14, for faithful flatness of
  dominant homomorphisms via generic flatness and translation.
-/

public section

open CategoryTheory WithConv

attribute [local instance] RingHom.ker_isPrime

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] {H K : _root_.CommHopfAlgCat.{v} k}

/-- Flatness at a rational point of the source of an affine group morphism is equivalent
to flatness at the identity. No finiteness or algebraic-closedness assumption is needed. -/
theorem flat_localization_kernel_iff (f : H ⟶ K) (g : WithConv (K →ₐ[k] k)) :
    ((algebraMap K (Localization.AtPrime (RingHom.ker g.ofConv.toRingHom))).comp
      f.hom.toAlgHom.toRingHom).Flat ↔
    ((algebraMap K (Localization.AtPrime
      (RingHom.ker (_root_.Bialgebra.counitAlgHom k K).toRingHom))).comp
      f.hom.toAlgHom.toRingHom).Flat := by
  let eH := HopfAlgebra.rightTranslationAlgEquiv (AlgHom.mapDomain f.hom g)
  let eK := HopfAlgebra.rightTranslationAlgEquiv g
  let p := RingHom.ker (_root_.Bialgebra.counitAlgHom k K).toRingHom
  have hp : p.comap eK.toRingEquiv = RingHom.ker g.ofConv.toRingHom := by
    dsimp only [p]
    rw [← Ideal.comap_coe, RingHom.comap_ker]
    exact congrArg (fun h : K →ₐ[k] k ↦ RingHom.ker h.toRingHom)
      (by simpa only [← HopfAlgebra.rightTranslationAlgEquiv_toAlgHom]
        using HopfAlgebra.counitAlgHom_comp_rightTranslationAlgHom g)
  have hcomm : eK.toRingEquiv.toRingHom.comp f.hom.toAlgHom.toRingHom =
      f.hom.toAlgHom.toRingHom.comp eH.toRingEquiv.toRingHom := by
    exact congrArg (fun h : H →ₐ[k] K ↦ h.toRingHom) (by
      simpa only [← HopfAlgebra.rightTranslationAlgEquiv_toAlgHom]
        using (f.hom.comp_rightTranslationAlgHom g).symm)
  have ht := RingHom.flat_localization_comap_iff
    f.hom.toAlgHom.toRingHom f.hom.toAlgHom.toRingHom
    eH.toRingEquiv eK.toRingEquiv hcomm p
  -- Index by prime-spectrum points so the ideal and its primality proof travel together.
  have hpoint : (⟨p.comap eK.toRingEquiv, inferInstance⟩ : PrimeSpectrum K) =
      ⟨RingHom.ker g.ofConv.toRingHom, inferInstance⟩ := PrimeSpectrum.ext hp
  have heq := congrArg (fun q : PrimeSpectrum K ↦
    ((algebraMap K (Localization.AtPrime q.asIdeal)).comp f.hom.toAlgHom.toRingHom).Flat)
    hpoint
  exact heq ▸ ht

/-- An affine group morphism over an algebraically closed field with finite-type source
is flat exactly when its coordinate map becomes flat after localizing at the augmentation
ideal of the source. -/
theorem flat_iff_flat_localization_augmentation [IsAlgClosed k] [Algebra.FiniteType k K]
    (f : H ⟶ K) :
    f.hom.toAlgHom.toRingHom.Flat ↔
      ((algebraMap K (Localization.AtPrime
        (RingHom.ker (_root_.Bialgebra.counitAlgHom k K).toRingHom))).comp
        f.hom.toAlgHom.toRingHom).Flat := by
  constructor
  · intro hf
    exact hf.comp (RingHom.flat_algebraMap_iff.mpr
      (IsLocalization.flat _
        (RingHom.ker (_root_.Bialgebra.counitAlgHom k K).toRingHom).primeCompl))
  · intro hf
    let := f.hom.toAlgHom.toAlgebra
    apply Module.flat_of_isLocalized_maximal K K
      (fun p ↦ Localization.AtPrime p) (fun p ↦ Algebra.linearMap K _)
    intro p hp
    let : Field (K ⧸ p) := Ideal.Quotient.field p
    let : Module.Finite k (K ⧸ p) := finite_of_finite_type_of_isJacobsonRing k (K ⧸ p)
    let e : k ≃ₐ[k] K ⧸ p := AlgEquiv.ofBijective (Algebra.ofId k (K ⧸ p))
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let g : K →ₐ[k] k := e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ k p)
    have hg : RingHom.ker g.toRingHom = p := by
      ext x
      simp [RingHom.mem_ker, g, Ideal.Quotient.eq_zero_iff_mem]
    have hflat := (flat_localization_kernel_iff f (toConv g)).mpr hf
    -- Prime-spectrum equality transports the localization's dependent instances as well.
    have hpoint : (⟨RingHom.ker g.toRingHom, inferInstance⟩ : PrimeSpectrum K) =
        ⟨p, inferInstance⟩ := PrimeSpectrum.ext hg
    have hlocal := (congrArg (fun q : PrimeSpectrum K ↦
      ((algebraMap K (Localization.AtPrime q.asIdeal)).comp f.hom.toAlgHom.toRingHom).Flat)
      hpoint).mp hflat
    have heq : (algebraMap K (Localization.AtPrime p)).comp f.hom.toAlgHom.toRingHom =
        algebraMap H (Localization.AtPrime p) :=
      (IsScalarTower.algebraMap_eq H K (Localization.AtPrime p)).symm
    rwa [heq, RingHom.flat_algebraMap_iff] at hlocal

/-- A dominant homomorphism from a finite-type affine group to a reduced finite-type affine
group over an algebraically closed field is faithfully flat. The source may be nonreduced, and
the homomorphism need not be finite. -/
theorem faithfullyFlat_of_dominant [IsAlgClosed k] [Algebra.FiniteType k H] [IsReduced H]
    [Algebra.FiniteType k K] (f : H ⟶ K)
    (hdom : DenseRange (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom)) :
    f.hom.toAlgHom.toRingHom.FaithfullyFlat := by
  let := f.hom.toAlgHom.toAlgebra
  have : IsScalarTower k H K := .of_algebraMap_eq fun x ↦ (f.hom.toAlgHom.commutes x).symm
  have : Algebra.FiniteType H K := .of_restrictScalars_finiteType k H K
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  have : Nontrivial H := (Bialgebra.counitAlgHom k H).toRingHom.domain_nontrivial
  have hd := hdom.comp (denseRange_kernelPoint (k := k) (A := K))
    (PrimeSpectrum.continuous_comap f.hom.toAlgHom.toRingHom)
  -- Generic freeness gives a dense open set over which `K` is free; dominance and density of
  -- rational points give a rational point of the source lying over it.
  obtain ⟨g, hg⟩ := hd.exists_mem_open isOpen_interior
    (Module.dense_interior_freeLocus_of_finiteType (A := H) (B := K) K).nonempty
  have := (AlgHom.kernelPoint g).isPrime
  have hlocal : Module.Flat H
      (Localization.AtPrime (AlgHom.kernelPoint g).asIdeal) :=
    PrimeSpectrum.flat_localization_of_comap_mem_freeLocus (AlgHom.kernelPoint g)
      (interior_subset hg)
  have hflat : f.hom.toAlgHom.toRingHom.Flat := by
    apply (flat_iff_flat_localization_augmentation f).mpr
    apply (flat_localization_kernel_iff f (toConv g)).mp
    rw [← RingHom.algebraMap_toAlgebra f.hom.toAlgHom.toRingHom,
      ← IsScalarTower.algebraMap_eq H K, RingHom.flat_algebraMap_iff]
    -- Transport the prime together with its primality proof, so localization instances agree.
    have hp : (AlgHom.kernelPoint g : PrimeSpectrum K) =
        ⟨RingHom.ker g.toRingHom, RingHom.ker_isPrime _⟩ :=
      PrimeSpectrum.ext (AlgHom.kernelPoint_asIdeal g)
    exact (congrArg (fun p : PrimeSpectrum K ↦
      Module.Flat H (Localization.AtPrime p.asIdeal)) hp).mp hlocal
  have hinj : Function.Injective f.hom :=
    (RingHom.denseRange_comap_iff_injective _).mp hdom
  exact (faithfullyFlat_iff_flat_of_injective f hinj).mpr hflat

end TauCeti.CommHopfAlgCat
