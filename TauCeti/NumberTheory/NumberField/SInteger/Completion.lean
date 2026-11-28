/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.SInteger.Basic
public import TauCeti.RingTheory.DedekindDomain.SInteger.Completion
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Adic-completion characterization of `S`-integers of a number field

For a number field `F` and a finite set `S : Finset (HeightOneSpectrum (𝓞 F))` of height-one primes
of `𝓞 F`, this file specializes `Set.mem_integer_iff_forall_adicCompletionIntegers` to characterize
membership in `TauCeti.SIntegers F S` in terms of membership in the local valuation subrings
`v.adicCompletionIntegers F` at all places `v ∉ S`, and packages `v.adicCompletionIntegers F` for
`v ∉ S` as a compact `SIntegers F S`-subalgebra `TauCeti.localIntegerSubalgebra F S v hv` of
`v.adicCompletion F`.

## Main declarations

* `TauCeti.mem_sIntegers_iff_forall_adicCompletionIntegers`: an element of `F` lies in
  `SIntegers F S` if and only if its image in `v.adicCompletion F` lies in
  `v.adicCompletionIntegers F` for every `v ∉ S`.
* `TauCeti.localIntegerSubalgebra`, `TauCeti.compactSpace_localIntegerSubalgebra`: for `v ∉ S`, the
  valuation ring `v.adicCompletionIntegers F` viewed as a compact `𝒪_{F,S}`-subalgebra of
  `v.adicCompletion F`.

## References

* J. W. S. Cassels and A. Fröhlich, eds., *Algebraic Number Theory*, Chapter II, §§14–15.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §4 and Chapter VI, §1.
-/

public section

open IsDedekindDomain NumberField

namespace TauCeti

variable {F : Type*} [Field F] [NumberField F]

/-- An element of `F` is an `S`-integer if and only if its image in `F_v` is `v`-integral for every
`v ∉ S`. -/
theorem mem_sIntegers_iff_forall_adicCompletionIntegers
    {S : Finset (HeightOneSpectrum (𝓞 F))} {x : F} :
    x ∈ SIntegers F S ↔
      ∀ v ∉ S, algebraMap F (v.adicCompletion F) x ∈ v.adicCompletionIntegers F := by
  simpa only [Finset.mem_coe] using
    (Set.mem_integer_iff_forall_adicCompletionIntegers (R := 𝓞 F) (S := (S : Set _)) (x := x))

variable (F) in
/-- For `v ∉ S`, the valuation ring `𝒪_v` of `F_v` viewed as an `𝒪_{F,S}`-subalgebra of `F_v`. -/
noncomputable def localIntegerSubalgebra (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    Subalgebra (SIntegers F S) (v.adicCompletion F) :=
  { (v.adicCompletionIntegers F).toSubring with
    algebraMap_mem' r := by
      rw [IsScalarTower.algebraMap_apply (SIntegers F S) F (v.adicCompletion F)]
      exact (mem_sIntegers_iff_forall_adicCompletionIntegers.mp r.property) v hv }

@[simp]
theorem toSubring_localIntegerSubalgebra (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    (localIntegerSubalgebra F S v hv).toSubring = (v.adicCompletionIntegers F).toSubring := by
  rw [localIntegerSubalgebra]

@[simp]
theorem mem_localIntegerSubalgebra_iff (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) {x : v.adicCompletion F} :
    x ∈ localIntegerSubalgebra F S v hv ↔ x ∈ v.adicCompletionIntegers F :=
  Iff.rfl

@[simp]
theorem coe_localIntegerSubalgebra (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    (localIntegerSubalgebra F S v hv : Set (v.adicCompletion F)) =
      (v.adicCompletionIntegers F : Set (v.adicCompletion F)) :=
  Set.ext fun _ ↦ mem_localIntegerSubalgebra_iff S v hv

/-- For `v ∉ S`, `localIntegerSubalgebra F S v hv` is compact in the `v`-adic topology. -/
instance compactSpace_localIntegerSubalgebra (S : Finset (HeightOneSpectrum (𝓞 F)))
    (v : HeightOneSpectrum (𝓞 F)) (hv : v ∉ S) :
    CompactSpace (localIntegerSubalgebra F S v hv) := by
  have : Finite (𝓞 F ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
  have : IsNonarchimedeanLocalField (v.adicCompletion F) :=
    HeightOneSpectrum.isNonarchimedeanLocalField_adicCompletion v
  have : CompactSpace (v.adicCompletionIntegers F) :=
    HeightOneSpectrum.compactSpace_adicCompletionIntegers v
  exact (Homeomorph.setCongr (coe_localIntegerSubalgebra S v hv).symm).compactSpace

end TauCeti

end
