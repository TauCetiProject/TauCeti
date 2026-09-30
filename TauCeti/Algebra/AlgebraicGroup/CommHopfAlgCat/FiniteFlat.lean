/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Flat
public import TauCeti.Algebra.AlgebraicGroup.CommHopfAlgCat.Surjective
public import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Faithful flatness of finite dominant affine group homomorphisms

A finite dominant homomorphism to a reduced affine group of finite type over an
algebraically closed field is faithfully flat. The source need not be reduced or smooth.
This supplies the flatness condition for finite isogenies without putting that condition
into the hypotheses.

The coordinate module is free on a nonempty open subset of the target. Dominance and
density of rational points produce a rational source point where the morphism is flat;
translation then propagates flatness to the identity and hence everywhere.

## References

* J. S. Milne, *Algebraic Groups* (2017), Propositions 1.65(a) and 1.70.
* The Stacks Project, Tag 051Z, generic freeness over a reduced ring.
-/

public section

open CategoryTheory WithConv

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]
  {H K : _root_.CommHopfAlgCat.{v} k} [Algebra.FiniteType k H] [IsReduced H]

/-- A finite dominant homomorphism to a reduced finite-type affine group over an
algebraically closed field is faithfully flat. The source may be nonreduced. -/
theorem faithfullyFlat_of_finite_of_dominant (f : H ⟶ K)
    (hfin : f.hom.toAlgHom.Finite)
    (hdom : DenseRange (PrimeSpectrum.comap f.hom.toAlgHom.toRingHom)) :
    f.hom.toAlgHom.toRingHom.FaithfullyFlat := by
  let := f.hom.toAlgHom.toAlgebra
  have : Module.Finite H K := hfin
  have : Algebra.FiniteType H K := inferInstance
  have : Algebra.FiniteType k K :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType k H) inferInstance
  have : IsNoetherianRing H := Algebra.FiniteType.isNoetherianRing k H
  have : Module.FinitePresentation H K := Module.finitePresentation_of_finite H K
  have : Nontrivial H := (Bialgebra.counitAlgHom k H).toRingHom.domain_nontrivial
  have hd := hdom.comp (denseRange_kernelPoint (k := k) (A := K))
    (PrimeSpectrum.continuous_comap f.hom.toAlgHom.toRingHom)
  obtain ⟨g, hg⟩ := hd.exists_mem_open Module.isOpen_freeLocus
    (Module.freeLocus_nonempty H K)
  have := (AlgHom.kernelPoint g).isPrime
  have hlocal : Module.Flat H
      (Localization.AtPrime (AlgHom.kernelPoint g).asIdeal) :=
    PrimeSpectrum.flat_localization_of_comap_mem_freeLocus (AlgHom.kernelPoint g) hg
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
  have hinj : Function.Injective f.hom := by
    apply (RingHom.injective_iff_ker_eq_bot f.hom.toAlgHom.toRingHom).mpr
    apply bot_unique
    simpa only [nilradical_eq_zero, Ideal.zero_eq_bot] using
      (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mp hdom
  exact (faithfullyFlat_iff_flat_of_injective f hinj).mpr hflat

end TauCeti.CommHopfAlgCat
