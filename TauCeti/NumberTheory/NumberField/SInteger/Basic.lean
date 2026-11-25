/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Basic
public import TauCeti.RingTheory.DedekindDomain.SInteger.Basic

/-!
# Rings of `S`-integers of a number field

For a number field `F` and a finite set `S : Finset (HeightOneSpectrum (𝓞 F))` of height-one primes
of its ring of integers `𝓞 F`, this file defines the subalgebra `TauCeti.SIntegers F S` of
`S`-integers `𝒪_{F,S} = (S : Set (HeightOneSpectrum (𝓞 F))).integer F` and packages its basic
algebraic inclusion API: monotonicity in `S`, the induced algebra structure for `S ⊆ T`, and the
resulting scalar tower `𝒪_{F,S} → 𝒪_{F,T} → F`.

This module is purely algebraic and does not depend on completions or adeles; for the local-global
completion characterization of `S`-integers of `F`, see
`TauCeti.NumberTheory.NumberField.SInteger.Completion`.

## Main declarations

* `TauCeti.SIntegers`: the subalgebra `𝒪_{F,S}` of `S`-integers of a number field `F`.
* `TauCeti.sIntegers_mono`: enlarging `S` enlarges `SIntegers F S`.
* `TauCeti.sIntegersAlgebraOfSubset`, `TauCeti.isScalarTower_sIntegersAlgebraOfSubset`,
  `TauCeti.toAlgHom_sIntegers_injective`: canonical inclusion algebra structure, scalar tower
  `𝒪_{F,S} → 𝒪_{F,T} → F`, and injectivity of `𝒪_{F,T} →ₐ[𝒪_{F,S}] F` for `S ⊆ T`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §§14–15.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 and Chapter VI, §1.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti

variable (F : Type*) [Field F] [NumberField F]

/-- The subalgebra `𝒪_{F,S}` of `S`-integers of `F`, consisting of elements with `v`-adic valuation
at most `1` at every height-one prime `v ∉ S`. -/
noncomputable abbrev SIntegers (S : Finset (HeightOneSpectrum (𝓞 F))) : Subalgebra (𝓞 F) F :=
  (S : Set (HeightOneSpectrum (𝓞 F))).integer F

variable {F}

/-- Enlarging the finite exceptional set `S` enlarges the subalgebra of `S`-integers. -/
theorem sIntegers_mono {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) :
    SIntegers F S ≤ SIntegers F T :=
  Set.integer_mono F (Finset.coe_subset.mpr hST)

/-- For `S ⊆ T`, the canonical `𝒪_{F,S}`-algebra structure on `𝒪_{F,T}` induced by the subalgebra
inclusion `SIntegers F S ≤ SIntegers F T`. -/
@[instance_reducible]
noncomputable def sIntegersAlgebraOfSubset {S T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) : Algebra (SIntegers F S) (SIntegers F T) :=
  Set.integerAlgebraOfSubset F (Finset.coe_subset.mpr hST)

/-- For `S ⊆ T`, the `𝒪_{F,S}`-algebra structure `sIntegersAlgebraOfSubset hST` on `𝒪_{F,T}` forms
a scalar tower with `F`. -/
theorem isScalarTower_sIntegersAlgebraOfSubset {S T : Finset (HeightOneSpectrum (𝓞 F))}
    (hST : S ⊆ T) :
    @IsScalarTower (SIntegers F S) (SIntegers F T) F
      (sIntegersAlgebraOfSubset hST).toSMul Algebra.toSMul Algebra.toSMul :=
  Set.isScalarTower_integerAlgebraOfSubset F (Finset.coe_subset.mpr hST)

/-- For `S ⊆ T`, the canonical `𝒪_{F,S}`-algebra map `𝒪_{F,T} →ₐ[𝒪_{F,S}] F` is injective. -/
theorem toAlgHom_sIntegers_injective {S T : Finset (HeightOneSpectrum (𝓞 F))} (hST : S ⊆ T) :
    letI : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
    letI := isScalarTower_sIntegersAlgebraOfSubset hST
    Function.Injective (IsScalarTower.toAlgHom (SIntegers F S) (SIntegers F T) F) := by
  let _ : Algebra (SIntegers F S) (SIntegers F T) := sIntegersAlgebraOfSubset hST
  let _ := isScalarTower_sIntegersAlgebraOfSubset hST
  rw [IsScalarTower.coe_toAlgHom']
  exact FaithfulSMul.algebraMap_injective (SIntegers F T) F

end TauCeti

end
