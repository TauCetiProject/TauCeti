/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.RingTheory.Spectrum.Prime.FiberDimension
import Mathlib.RingTheory.LocalProperties.Reduced
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Constant fibre dimension over reduced rings

A surjection from a finite free module over a reduced ring is an isomorphism if all its
fibres have the same dimension as the source. Consequently, over a reduced local ring a
finite module with constant fibre dimension is free. Globally, a finite module with locally
constant fibre dimension is flat, and is projective if it is finitely presented. These are the
reduced-base freeness criteria used in cohomology and base change. All fibre dimensions below
are dimensions over residue fields, not ranks of possibly nonfree localized modules.

## References

* R. Hartshorne, *Algebraic Geometry*, the proof of Theorem III.12.9.
* The Stacks Project, Tag 00NX, finite locally free modules.
-/

public section

open TensorProduct Module

namespace LinearMap

variable {R F M : Type*} [CommRing R] [IsReduced R]
  [AddCommGroup F] [Module R F] [Module.Free R F] [Module.Finite R F]
  [AddCommGroup M] [Module R M]

/-- Over a reduced ring, a surjection from a finite free module is bijective if the dimension
of every fibre of its target equals the rank of its source. -/
theorem bijective_of_surjective_of_finrank_fiber_eq (f : F →ₗ[R] M)
    (hf : Function.Surjective f)
    (hr : ∀ p : PrimeSpectrum R,
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) = finrank R F) :
    Function.Bijective f := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : Subsingleton F := Module.subsingleton R F
    exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, hf⟩
  have : Module.Finite R M := Module.Finite.of_surjective f hf
  refine ⟨?_, hf⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  let b := Module.Free.chooseBasis R F
  apply b.repr.injective
  ext i
  simp only [map_zero, Finsupp.zero_apply]
  -- Every coordinate of a kernel element vanishes in every residue field, hence is nilpotent.
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro p hp
  let := hp
  have hinj : Function.Injective (f.baseChange p.ResidueField) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
      rw [Module.finrank_baseChange, hr ⟨p, hp⟩])).mpr
      (f.baseChange_surjective p.ResidueField hf)
  have ht : (1 : p.ResidueField) ⊗ₜ[R] x = 0 := by
    apply hinj
    simp [hx]
  have hc := congrArg
    (fun z ↦ TensorProduct.rid R p.ResidueField
      ((b.coord i).lTensor p.ResidueField z)) ht
  simpa [Algebra.smul_def] using hc

end LinearMap

namespace Module

variable {R : Type*} [CommRing R] [IsReduced R] [IsLocalRing R]
  (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module over a reduced local ring is free if all its fibres have the same dimension
as its closed fibre. No finite-presentation assumption is required. -/
theorem free_of_finrank_fiber_eq
    (hr : ∀ p : PrimeSpectrum R,
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M) =
        finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] M)) :
    Module.Free R M := by
  -- Lift a basis of the closed fibre; Nakayama makes the lifts generate the whole module.
  let k := IsLocalRing.ResidueField R
  let b := Module.Free.chooseBasis k (k ⊗[R] M)
  obtain ⟨v, hv⟩ := (TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective).comp_left b
  have hsp := IsLocalRing.span_eq_top_of_tmul_eq_basis (R := R) v b (congr_fun hv)
  let f := Finsupp.linearCombination R v
  have hf : Function.Surjective f := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    exact hsp
  have := Module.Finite.finite_basis b
  have hbij : Function.Bijective f :=
    f.bijective_of_surjective_of_finrank_fiber_eq hf fun p ↦ by
      rw [hr p, Module.finrank_eq_card_basis b, Module.finrank_finsupp_self]
  exact Module.Free.of_equiv (LinearEquiv.ofBijective f hbij)

/-- Over a reduced local ring, a finite module with locally constant fibre dimension is free.
This applies to non-Noetherian rings and does not require a finite presentation. -/
theorem free_of_isLocallyConstant_finrank_fiber
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M)) : Module.Free R M := by
  apply free_of_finrank_fiber_eq M
  intro p
  have heq := (((PrimeSpectrum.le_iff_specializes p
    ⟨IsLocalRing.maximalIdeal R, inferInstance⟩).mp
      (IsLocalRing.le_maximalIdeal p.2.1)).map h.continuous).eq
  refine heq.trans ?_
  exact ((IsLocalRing.maximalIdeal R).finrank_tensorProduct_eq_finrank_fiber M
    (IsLocalRing.ResidueField R) (by
      rw [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.ker_residue])).symm

end Module

namespace Module

section Finite

variable {R : Type*} [CommRing R] [IsReduced R]
  (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- A finite module over a reduced ring is flat if its fibre dimensions are locally constant.
No Noetherianity or finite-presentation hypothesis is needed. -/
theorem flat_of_isLocallyConstant_finrank_fiber
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M)) : Module.Flat R M := by
  apply Module.flat_of_localized_maximal
  intro p hp
  let A := Localization.AtPrime p
  have hlc : IsLocallyConstant fun q : PrimeSpectrum A ↦
      finrank q.asIdeal.ResidueField (q.asIdeal.Fiber (A ⊗[R] M)) := by
    convert h.comp_continuous (PrimeSpectrum.continuous_comap (algebraMap R A)) using 1
    funext q
    exact q.asIdeal.finrank_fiber_baseChange (M := M)
  have := free_of_isLocallyConstant_finrank_fiber (A ⊗[R] M) hlc
  have : Module.Flat A (LocalizedModule p.primeCompl M) :=
    Module.Flat.of_linearEquiv (LocalizedModule.isBaseChange p.primeCompl M).equiv.symm
  exact Module.Flat.trans R A _

end Finite

variable {R : Type*} [CommRing R] [IsReduced R]
  (M : Type*) [AddCommGroup M] [Module R M] [Module.FinitePresentation R M]

/-- A finitely presented module over a reduced ring is projective if its fibre dimensions are
locally constant. This is the finite locally free form of the reduced-base flatness criterion. -/
theorem projective_of_isLocallyConstant_finrank_fiber
    (h : IsLocallyConstant fun p : PrimeSpectrum R ↦
      finrank p.asIdeal.ResidueField (p.asIdeal.Fiber M)) : Module.Projective R M := by
  have := flat_of_isLocallyConstant_finrank_fiber M h
  exact Module.Flat.projective_of_finitePresentation

end Module
