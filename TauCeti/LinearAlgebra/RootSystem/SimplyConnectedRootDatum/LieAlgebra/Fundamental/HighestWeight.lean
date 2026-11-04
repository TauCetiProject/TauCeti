/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.SimplyConnectedRootDatum.LieAlgebra.Fundamental.Lattice
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.Orbit.HighestWeight

/-!
# The highest weight line in a fundamental lattice

The rational highest weight space of `L(ϖᵢ)` is the line through its distinguished vector `v⁺ᵢ`.
Its intersection with the integral Kostant orbit is exactly `ℤ · v⁺ᵢ`, rather than a larger
lattice in that line. Thus the chosen highest weight vector fixes the integral normalization:
a rational multiple of it lies in the fundamental lattice precisely when its coefficient is an
integer. This is the integral highest weight line used when constructing root subgroup actions
on fundamental lattices.

The main result `TauCeti.DynkinType.fundamentalLattice_inf_genWeightSpace` identifies that
intersection as a submodule of the rational fundamental module. The coefficient criterion
`TauCeti.DynkinType.smul_fundamentalModuleGenerator_mem_fundamentalLattice_iff` lets callers use
this normalization without manipulating weight spaces.

The integral assertion specializes
`LieAlgebra.Basis.exists_eq_zsmul_of_mem_orbitOfRep_kostantForm`; the rational highest weight
space is identified by `TauCeti.DynkinType.genWeightSpace_fundamentalModule_fundamentalWeight`.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, AMS University Lecture Series 66 (2016),
  Chapter 2, Corollary 1 to Theorem 2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §27.1.
-/

public section

namespace TauCeti.DynkinType

open LieModule _root_.TauCeti.UniversalEnvelopingAlgebra

variable (t : DynkinType) (ht : t.Valid)

-- Isolate the specialization so that elaborating the intersection does not also elaborate
-- the enveloping-algebra representation and its orbit at every occurrence.
private theorem exists_eq_zsmul_of_mem_fundamentalLattice
    (i : Fin t.rank) {x : t.fundamentalModule ht i}
    (hx : x ∈ t.fundamentalLattice ht i)
    (hxw : IsCartanWeightVector (t.lieBasis ht).h
      (representation ℚ (t.lieAlgebra ht) (t.fundamentalModule ht i))
      (Pi.single i 1) x) :
    ∃ n : ℤ, x = n • t.fundamentalModuleGenerator ht i := by
  rw [t.fundamentalLattice_def ht, t.kostantForm_def ht] at hx
  exact (t.lieBasis ht).exists_eq_zsmul_of_mem_orbitOfRep_kostantForm
    (t.isCartanWeightVector_fundamentalModuleGenerator ht i)
    (fun j => by rw [representation_ι_apply,
      t.lie_lieBasis_e_fundamentalModuleGenerator ht i j]) hx hxw

/-- The highest weight part of the fundamental lattice is exactly the integral line through
its distinguished highest weight vector. -/
theorem fundamentalLattice_inf_genWeightSpace (i : Fin t.rank) :
    t.fundamentalLattice ht i ⊓
        (genWeightSpace (t.fundamentalModule ht i)
          (t.fundamentalWeight ht i : t.cartanSubalgebra ht → ℚ) :
          Submodule ℚ _).restrictScalars ℤ =
      ℤ ∙ t.fundamentalModuleGenerator ht i := by
  rw [t.genWeightSpace_fundamentalModule_fundamentalWeight ht i]
  ext x
  constructor
  · rintro ⟨hx, hxw⟩
    obtain ⟨q, rfl⟩ := (Submodule.mem_span_singleton (R := ℚ)).mp hxw
    have hv := t.isCartanWeightVector_fundamentalModuleGenerator ht i
    obtain ⟨n, hn⟩ := exists_eq_zsmul_of_mem_fundamentalLattice t ht i hx (hv.smul q)
    exact Submodule.mem_span_singleton.mpr ⟨n, hn.symm⟩
  · intro hx
    obtain ⟨n, rfl⟩ := Submodule.mem_span_singleton.mp hx
    exact ⟨(t.fundamentalLattice ht i).smul_mem n
        (t.fundamentalModuleGenerator_mem_fundamentalLattice ht i),
      ((ℚ ∙ t.fundamentalModuleGenerator ht i).restrictScalars ℤ).smul_mem n
        (Submodule.mem_span_singleton_self _)⟩

/-- A rational multiple of the highest weight generator belongs to the fundamental lattice
exactly when its coefficient is an integer. -/
@[simp]
theorem smul_fundamentalModuleGenerator_mem_fundamentalLattice_iff
    (i : Fin t.rank) (q : ℚ) :
    q • t.fundamentalModuleGenerator ht i ∈ t.fundamentalLattice ht i ↔
      ∃ n : ℤ, (n : ℚ) = q := by
  have hline : q • t.fundamentalModuleGenerator ht i ∈
      (genWeightSpace (t.fundamentalModule ht i)
        (t.fundamentalWeight ht i : t.cartanSubalgebra ht → ℚ) :
        Submodule ℚ _).restrictScalars ℤ := by
    rw [t.genWeightSpace_fundamentalModule_fundamentalWeight ht i]
    exact Submodule.mem_span_singleton.mpr ⟨q, rfl⟩
  constructor
  · intro hx
    have hmem := Submodule.mem_inf.mpr ⟨hx, hline⟩
    rw [t.fundamentalLattice_inf_genWeightSpace ht i, Submodule.mem_span_singleton] at hmem
    obtain ⟨n, hn⟩ := hmem
    exact ⟨n, smul_left_injective ℚ (t.fundamentalModuleGenerator_ne_zero ht i)
      (by simpa only [Int.cast_smul_eq_zsmul] using hn)⟩
  · rintro ⟨n, rfl⟩
    rw [Int.cast_smul_eq_zsmul]
    exact (t.fundamentalLattice ht i).smul_mem n
      (t.fundamentalModuleGenerator_mem_fundamentalLattice ht i)

end TauCeti.DynkinType
