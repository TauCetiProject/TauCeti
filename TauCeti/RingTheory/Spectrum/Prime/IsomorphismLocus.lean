/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Spectrum.Prime.Module
public import TauCeti.Algebra.Module.LocalizedModule.Submodule

/-!
# The isomorphism locus of a linear map

The isomorphism locus of `f : M →ₗ[R] N` consists of the primes at which its localization is
bijective. Its complement is the union of the supports of its kernel and cokernel. Consequently,
this locus is open when those two modules are finite; in particular, this applies to maps between
finite modules over a Noetherian ring.

The basic-open criterion identifies containment of `D(a)` in this locus with bijectivity of
`f[1/a]`. Thus an isomorphism at one prime extends to a basic-open neighbourhood, and a map
that is an isomorphism at every prime is an isomorphism globally. These are the affine support
arguments used to compare finite algebras by their localizations.

The support calculations reuse Mathlib's `Module.support` and its localization criteria, together
with `LinearMap.localizedMap_injective_iff_subsingleton_localized_ker`.

## References

* The Stacks Project, Section 10.40 (Tag 00L0), supports and annihilators of modules.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, proof of Theorem 6.2.1,
  for the kernel–cokernel support argument comparing finite algebras.
-/

public section

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- The primes where a linear map becomes an isomorphism after localization. -/
def isoLocus (f : M →ₗ[R] N) : Set (PrimeSpectrum R) :=
  {p | Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f)}

/-- Membership in the isomorphism locus means bijectivity of the localized map. -/
@[simp]
theorem mem_isoLocus (f : M →ₗ[R] N) (p : PrimeSpectrum R) :
    p ∈ f.isoLocus ↔ Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl f) :=
  Iff.rfl

/-- A prime is in the isomorphism locus exactly when neither the kernel nor the cokernel
has support there. -/
theorem mem_isoLocus_iff_notMem_support (f : M →ₗ[R] N) (p : PrimeSpectrum R) :
    p ∈ f.isoLocus ↔
      p ∉ Module.support R (ker f) ∧ p ∉ Module.support R (N ⧸ range f) := by
  rw [mem_isoLocus, Function.Bijective,
    localizedMap_injective_iff_subsingleton_localized_ker,
    localizedMap_surjective_iff_subsingleton_localized_coker,
    Module.notMem_support_iff, Module.notMem_support_iff]

/-- The obstruction to a map being an isomorphism is the support of its kernel and cokernel. -/
theorem isoLocus_eq_compl_support (f : M →ₗ[R] N) :
    f.isoLocus = (Module.support R (ker f) ∪ Module.support R (N ⧸ range f))ᶜ := by
  ext p
  simp only [mem_isoLocus_iff_notMem_support, Set.mem_compl_iff, Set.mem_union, not_or]

/-- If the kernel and cokernel are finite, the isomorphism locus is open. In particular, this
holds for a map between finite modules over a Noetherian ring. -/
theorem isOpen_isoLocus (f : M →ₗ[R] N) [Module.Finite R (ker f)]
    [Module.Finite R (N ⧸ range f)] : IsOpen f.isoLocus := by
  rw [isoLocus_eq_compl_support]
  exact (Module.isClosed_support.union Module.isClosed_support).isOpen_compl

/-- A basic open is contained in the isomorphism locus exactly when the map localized away
from its defining element is bijective. No finiteness assumptions are needed. -/
theorem basicOpen_subset_isoLocus_iff (f : M →ₗ[R] N) (a : R) :
    (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum R)) ⊆ f.isoLocus ↔
      Function.Bijective (LocalizedModule.map (Submonoid.powers a) f) := by
  rw [isoLocus_eq_compl_support, Set.subset_compl_iff_disjoint_right,
    Set.disjoint_union_right, ← LocalizedModule.subsingleton_iff_disjoint,
    ← LocalizedModule.subsingleton_iff_disjoint, Function.Bijective,
    localizedMap_injective_iff_subsingleton_localized_ker,
    localizedMap_surjective_iff_subsingleton_localized_coker]

/-- An isomorphism at a prime extends to an isomorphism on a basic-open neighbourhood when
the kernel and cokernel are finite. -/
theorem exists_localizedMap_away_bijective (f : M →ₗ[R] N) [Module.Finite R (ker f)]
    [Module.Finite R (N ⧸ range f)] (p : PrimeSpectrum R) (hp : p ∈ f.isoLocus) :
    ∃ a ∉ p.asIdeal, Function.Bijective (LocalizedModule.map (Submonoid.powers a) f) := by
  obtain ⟨_, ⟨a, rfl⟩, hpa, ha⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hp f.isOpen_isoLocus
  exact ⟨a, (PrimeSpectrum.mem_basicOpen a p).mp hpa,
    (f.basicOpen_subset_isoLocus_iff a).mp ha⟩

/-- A map is an isomorphism at every prime exactly when it is bijective. -/
@[simp]
theorem isoLocus_eq_univ_iff (f : M →ₗ[R] N) :
    f.isoLocus = Set.univ ↔ Function.Bijective f := by
  simp only [isoLocus_eq_compl_support, Set.compl_univ_iff, Set.union_empty_iff,
    Module.support_eq_empty_iff, Submodule.subsingleton_iff_eq_bot,
    Submodule.Quotient.subsingleton_iff, ker_eq_bot, range_eq_top, Function.Bijective]

/-- The isomorphism locus of a bijective map is the whole prime spectrum. -/
theorem isoLocus_eq_univ (f : M →ₗ[R] N) (hf : Function.Bijective f) :
    f.isoLocus = Set.univ :=
  (f.isoLocus_eq_univ_iff).mpr hf

/-- For finite kernel and cokernel, the isomorphism locus is the complement of the zero locus
of the product of their annihilators. -/
theorem isoLocus_eq_compl_zeroLocus (f : M →ₗ[R] N) [Module.Finite R (ker f)]
    [Module.Finite R (N ⧸ range f)] :
    f.isoLocus = (PrimeSpectrum.zeroLocus
      ((Module.annihilator R (ker f) *
        Module.annihilator R (N ⧸ range f) : Ideal R) : Set R))ᶜ := by
  rw [isoLocus_eq_compl_support, Module.support_eq_zeroLocus, Module.support_eq_zeroLocus,
    PrimeSpectrum.zeroLocus_mul]

end LinearMap
