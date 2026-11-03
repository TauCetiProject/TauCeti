/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.EulerCharacteristic.Finite
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import TauCeti.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Euler characteristics of fibres of bounded complexes

For a bounded complex `K` of finite modules over a commutative ring `R`, the Euler
characteristic of the homology of `κ(p) ⊗ K` is the alternating sum of the dimensions of
its terms. If the terms of `K` are projective, these dimensions are their ranks at `p`,
so this Euler characteristic is locally constant on `Spec R`.

This is the algebraic Euler-characteristic calculation for cohomology computed universally
by a bounded complex of finite projective modules. The result concerns homology of the
base-changed complex, not base change of its homology: no flatness of the residue field
is assumed. The base ring need not be Noetherian or reduced.

We use Mathlib's `homologyEulerChar`, and also state the equality as a finite alternating
sum over the bounding interval, so no infinite-support or infinite-dimensional junk values
enter the calculation. Euler--Poincaré is applied over the residue field, not over `R`.

## References

* D. Mumford, *Abelian Varieties*, §5, Corollary (b).
* R. Hartshorne, *Algebraic Geometry*, Theorem III.12.8.
-/

public section

open CategoryTheory Module

namespace CochainComplex

universe u

variable {R : Type u} [CommRing R]
  (K : CochainComplex (ModuleCat.{u} R) ℤ)
  (hK : ∀ i, Module.Finite R (K.X i))
  (a b : ℤ) [K.IsStrictlyGE a] [K.IsStrictlyLE b]

include hK

/-- Euler--Poincaré on a fibre of a bounded complex of finite modules: the homology Euler
characteristic is the alternating sum of its term dimensions. Projectivity of the terms,
Noetherianity of the base, and flatness of the residue field are not needed. -/
theorem homologyEulerChar_fiber_eq_sum_finrank (p : PrimeSpectrum R) :
    (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homologyEulerChar =
        ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) *
          finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (K.X i)) := by
  let F := ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)
  let L := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hfin (i : ℤ) : Module.Finite p.asIdeal.ResidueField (L.X i) := by
    have := hK i
    exact Module.Finite.equiv (ModuleCat.extendScalarsAlgebraMapIso (K.X i)).toLinearEquiv.symm
  rw [← CochainComplex.eulerChar_eq_homologyEulerChar L hfin a b,
    HomologicalComplex.eulerChar_eq_sum_finSet_of_finrankSupport_subset L (Finset.Icc a b)
      (HomologicalComplex.finrankSupport_X_subset_Icc L a b)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [ComplexShape.χ, ComplexShape.eulerCharSignsUpInt_χ]
  dsimp only [L, F, Functor.mapHomologicalComplex_obj_X]
  rw [(ModuleCat.extendScalarsAlgebraMapIso (S := p.asIdeal.ResidueField)
    (K.X i)).toLinearEquiv.finrank_eq]

/-- The finite alternating sum of the dimensions of the fibre homology of a bounded complex
of finite modules equals the alternating sum of its fibre term dimensions. The sum includes
all possibly nonzero homology groups. -/
theorem sum_finrank_homology_fiber_eq_sum_finrank (p : PrimeSpectrum R) :
    (∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) *
      finrank p.asIdeal.ResidueField
        ((((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K).homology i)) =
      ∑ i ∈ Finset.Icc a b, (i.negOnePow : ℤ) *
        finrank p.asIdeal.ResidueField (p.asIdeal.Fiber (K.X i)) := by
  rw [← homologyEulerChar_fiber_eq_sum_finrank K hK a b p,
    HomologicalComplex.homologyEulerChar_eq_sum_finSet_of_finrankSupport_subset _
      (Finset.Icc a b) (HomologicalComplex.finrankSupport_homology_subset_Icc _ a b)]
  simp only [ComplexShape.eulerCharSignsUpInt_χ]

include a b in
/-- The homology Euler characteristic of the fibres of a bounded complex of finite
projective modules is locally constant on the prime spectrum. The homology modules themselves
need not be projective or commute with base change. -/
theorem isLocallyConstant_homologyEulerChar_fiber
    (hproj : ∀ i, Module.Projective R (K.X i)) :
    IsLocallyConstant fun p : PrimeSpectrum R ↦
      (((ModuleCat.extendScalars (algebraMap R p.asIdeal.ResidueField)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homologyEulerChar := by
  simp_rw [homologyEulerChar_fiber_eq_sum_finrank K hK a b]
  have hsum (s : Finset ℤ) : IsLocallyConstant fun p : PrimeSpectrum R ↦
      ∑ i ∈ s, (i.negOnePow : ℤ) * rankAtStalk (K.X i) p := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact IsLocallyConstant.const (0 : ℤ)
    | @insert i s hi hs =>
      have := hK i
      have := hproj i
      have := Module.finitePresentation_of_projective R (K.X i)
      simpa only [Finset.sum_insert hi] using
        ((isLocallyConstant_rankAtStalk (R := R) (M := K.X i)).comp₂ hs
          (fun n : ℕ ↦ fun v : ℤ ↦ (i.negOnePow : ℤ) * n + v))
  convert hsum (Finset.Icc a b) using 1
  ext p
  apply Finset.sum_congr rfl
  intro i _
  have := hK i
  have := hproj i
  rw [rankAtStalk_eq]

end CochainComplex
