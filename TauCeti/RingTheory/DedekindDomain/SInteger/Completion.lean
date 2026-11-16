/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Basic
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic

/-!
# Adic-completion characterization of `S`-integers

Let `R` be a Dedekind domain with fraction field `K` and `S` a set of height-one primes of `R`. An
element `x ∈ K` lies in the subalgebra `S.integer K` of `S`-integers if and only if its diagonal
image in every `v`-adic completion `v.adicCompletion K` for `v ∉ S` lies in the valuation subring
`v.adicCompletionIntegers K` (`Set.mem_integer_iff_forall_adicCompletionIntegers`).

This local-global characterization bridges global `S`-integrality with valuation-ring membership in
individual nonarchimedean completions, and underlies the local-global characterization of
`S`-integral points of affine group schemes over number fields. For convenience in number-field
applications, we also package the specialization `TauCeti.SIntegers F S` to a number field `F` and
a finite set `S : Finset (HeightOneSpectrum (𝓞 F))` of finite places, together with its
monotonicity and inclusion scalar-tower helpers.

## Main declarations

* `Set.mem_integer_iff_forall_adicCompletionIntegers`: adic-completion characterization of
  `x ∈ S.integer K` over any Dedekind domain `R`.
* `TauCeti.SIntegers`: the subalgebra `𝒪_{F,S}` of `S`-integers of a number field `F`.
* `TauCeti.mem_sIntegers_iff_forall_adicCompletionIntegers`, `TauCeti.sIntegers_mono`:
  number-field specializations of completion membership and monotonicity.
* `TauCeti.sIntegersAlgebraOfSubset`, `TauCeti.sIntegersTowerOfSubset`: canonical inclusion
  algebra structure and scalar tower `𝒪_{F,S} → 𝒪_{F,T} → F` for `S ⊆ T`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §§14–15.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 and Chapter VI, §1.
-/

public section

open IsDedekindDomain NumberField

namespace IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] {S : Set (HeightOneSpectrum R)}

/-- An element of `K` is an `S`-integer if and only if its image in the `v`-adic completion
`v.adicCompletion K` lies in the valuation ring `v.adicCompletionIntegers K` for every height-one
prime `v ∉ S`. -/
theorem _root_.Set.mem_integer_iff_forall_adicCompletionIntegers {x : K} :
    x ∈ S.integer K ↔
      ∀ v ∉ S, algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K := by
  rw [← FiniteAdeleRing.algebraMap_mem_sIntegralAdeles_iff (R := R) S x,
    FiniteAdeleRing.mem_sIntegralAdeles]
  simp only [FiniteAdeleRing.algebraMap_apply, HeightOneSpectrum.algebraMap_adicCompletion,
    Function.comp_apply, Algebra.algebraMap_self, RingHom.id_apply]

end IsDedekindDomain

namespace TauCeti

variable (F : Type*) [Field F] [NumberField F]

/-- The subalgebra `𝒪_{F,S}` of `S`-integers of `F`, consisting of elements with `v`-adic valuation
at most `1` at every height-one prime `v ∉ S`. -/
noncomputable abbrev SIntegers (S : Finset (HeightOneSpectrum (𝓞 F))) : Subalgebra (𝓞 F) F :=
  (S : Set (HeightOneSpectrum (𝓞 F))).integer F

variable {F}

/-- An element of `F` is an `S`-integer if and only if its image in `F_v` is `v`-integral for every
`v ∉ S`. -/
theorem mem_sIntegers_iff_forall_adicCompletionIntegers
    {S : Finset (HeightOneSpectrum (𝓞 F))} {x : F} :
    x ∈ SIntegers F S ↔
      ∀ v ∉ S, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F := by
  simpa only [Finset.mem_coe] using
    (Set.mem_integer_iff_forall_adicCompletionIntegers (R := 𝓞 F) (S := (S : Set _)) (x := x))

/-- Enlarging the finite exceptional set `S` enlarges the subalgebra of `S`-integers. -/
theorem sIntegers_mono {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) :
    SIntegers F S ≤ SIntegers F T :=
  Set.integer_mono (Finset.coe_subset.mpr hST)

/-- For `S ⊆ T`, the canonical `𝒪_{F,S}`-algebra structure on `𝒪_{F,T}` induced by the subalgebra
inclusion `SIntegers F S ≤ SIntegers F T`. -/
@[instance_reducible]
noncomputable def sIntegersAlgebraOfSubset {S T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) : Algebra (SIntegers F S) (SIntegers F T) :=
  Set.integerAlgebraOfSubset F (Finset.coe_subset.mpr hST)

/-- For `S ⊆ T`, the `𝒪_{F,S}`-algebra structure `sIntegersAlgebraOfSubset hST` on `𝒪_{F,T}` forms
a scalar tower with `F`. -/
theorem sIntegersTowerOfSubset {S T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) :
    @IsScalarTower (SIntegers F S) (SIntegers F T) F
      (sIntegersAlgebraOfSubset hST).toSMul Algebra.toSMul Algebra.toSMul :=
  Set.integerTowerOfSubset F (Finset.coe_subset.mpr hST)

end TauCeti

end
