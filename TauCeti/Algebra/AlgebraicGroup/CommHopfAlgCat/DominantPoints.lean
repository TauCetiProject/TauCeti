/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.Translation
public import TauCeti.AlgebraicGeometry.AugmentationPoint.Dense
public import TauCeti.RingTheory.FiniteType.FaithfullyFlatPoints
public import TauCeti.Topology.Constructible
public import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!
# Dominant affine group morphisms on algebraically closed points

A dominant homomorphism between finite-type affine group schemes over an algebraically
closed field is surjective on rational points. No smoothness, reducedness, or flatness
assumption is needed. In particular, an injective coordinate homomorphism gives a surjection
on points. The injective-coordinate-map case supplies the point-surjectivity step toward
faithful flatness. Topological dominance alone does not imply flatness for nonreduced groups.

Chevalley's theorem gives a dense open subset contained in the spectral image. Rational
points of the source are dense in the target; translating this open subset then expresses
each target point as a quotient of two image points.

## References

* J. S. Milne, *Algebraic Groups* (2017), §5, homomorphism theorems.
-/

public section

open CategoryTheory WithConv Topology

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H K : _root_.CommHopfAlgCat.{v} k}
  [Algebra.FiniteType k H] [Algebra.FiniteType k K]

/-- A dominant morphism of finite-type affine group schemes over an algebraically closed
field is surjective on rational points, without a flatness or reducedness hypothesis. -/
theorem mapPointsFunctor_app_surjective_of_dominant (f : H ⟶ K)
    (hf : DenseRange (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom)) :
    Function.Surjective ((mapPointsFunctor f).app (CommAlgCat.of k k)) := by
  have hft : f.hom.toAlgHom.FiniteType := by
    exact RingHom.FiniteType.of_comp_finiteType (f := algebraMap k H)
      (g := f.hom.toAlgHom.toRingHom)
      (f.hom.toAlgHom.comp_algebraMap.symm ▸ RingHom.finiteType_algebraMap.mpr
        (inferInstance : Algebra.FiniteType k K))
  let : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  have hfp := RingHom.FinitePresentation.of_finiteType.mp hft
  have hU := (PrimeSpectrum.isConstructible_range_comap hfp).dense_interior hf
  let U := interior (Set.range (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom))
  have hUopen : IsOpen U := isOpen_interior
  let : Nonempty (PrimeSpectrum H) := ⟨AlgHom.kernelPoint (Bialgebra.counitAlgHom k H)⟩
  have hUne : U.Nonempty := hU.nonempty
  have hd := hf.comp (denseRange_kernelPoint (k := k) (A := K))
    (PrimeSpectrum.continuous_comap f.hom.toAlgHom.toRingHom)
  intro p
  let t : PrimeSpectrum H ≃ₜ PrimeSpectrum H := HopfAlgebra.rightTranslationHomeomorph p
  obtain ⟨q, hq⟩ := hd.exists_mem_open
    (hUopen.preimage t.continuous) (t.surjective.nonempty_preimage.mpr hUne)
  let φ := (mapPointsFunctor f).app (CommAlgCat.of k k)
  have he : t (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom (AlgHom.kernelPoint q)) =
      AlgHom.kernelPoint (φ (toConv q) * p).ofConv := by
    exact (congrArg t (AlgHom.comap_kernelPoint q f.hom.toAlgHom)).trans
      (HopfAlgebra.rightTranslationHomeomorph_kernelPoint
        (toConv (q.comp f.hom.toAlgHom)) p)
  have hqp : AlgHom.kernelPoint (φ (toConv q) * p).ofConv ∈ U := he ▸ hq
  obtain ⟨P, hP⟩ := interior_subset hqp
  have hP' : PrimeSpectrum.comap f.hom.toAlgHom.toRingHom P =
      ⟨RingHom.ker (φ (toConv q) * p).ofConv.toRingHom,
        RingHom.ker_isPrime (φ (toConv q) * p).ofConv.toRingHom⟩ := by
    apply PrimeSpectrum.ext
    exact (congrArg PrimeSpectrum.asIdeal hP).trans (AlgHom.kernelPoint_asIdeal _)
  obtain ⟨r, hr⟩ := _root_.AlgHom.exists_comp_eq_of_comap_eq_ker
    f.hom.toAlgHom hft (φ (toConv q) * p).ofConv P hP'
  have hr' : φ (toConv r) = φ (toConv q) * p := by
    apply ofConv_injective
    simpa only [φ, mapPointsFunctor_app_apply, ofConv_toConv] using hr
  refine ⟨(toConv q)⁻¹ * toConv r, ?_⟩
  exact (map_mul φ.hom _ _).trans
    ((congrArg₂ (· * ·) (map_inv φ.hom _) hr').trans (inv_mul_cancel_left _ _))

/-- An injective homomorphism of finite-type commutative Hopf algebras over an
algebraically closed field is surjective contravariantly on rational points. -/
theorem mapPointsFunctor_app_surjective_of_injective (f : H ⟶ K)
    (hf : Function.Injective f.hom) :
    Function.Surjective ((mapPointsFunctor f).app (CommAlgCat.of k k)) := by
  apply mapPointsFunctor_app_surjective_of_dominant f
  rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical,
    (RingHom.injective_iff_ker_eq_bot f.hom.toAlgHom.toRingHom).mp hf]
  exact bot_le

end TauCeti.CommHopfAlgCat
