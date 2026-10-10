/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import TauCeti.NumberTheory.ClassFieldTheory.Brauer.Invariant
public import TauCeti.NumberTheory.ClassFieldTheory.Global.InvariantSum
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import TauCeti.NumberTheory.NumberField.LocalGlobal.Completion
import TauCeti.RepresentationTheory.Homological.ContCohomology.Torsion

/-!
# Cyclotomic extensions that split a Brauer class locally

A class of the Brauer group of a number field becomes trivial at every completion after
extension to a suitable cyclotomic field. At a finite place with residue cardinality `q`,
adjoining a primitive `(q^n - 1)`-st root of unity gives an unramified subextension of degree
`n`. Thus an `n`-torsion local Brauer class vanishes there. There are only finitely many
nontrivial finite localizations, so one cyclotomic modulus handles them all. A factor of four
in the modulus makes every infinite place complex.

The conclusion is local splitting, not global splitting: deducing the latter requires
injectivity of Brauer localization. The local statement supplies the cyclotomic splitting
input to the sum-of-local-invariants argument without assuming a global reciprocity law.

## Main results

* `TauCeti.ClassFieldTheory.exists_cyclotomicField_brLocalization_eq_zero`: one cyclotomic
  extension kills all localizations of a global Brauer class.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Proposition 7.2 and Lemma 7.3.
-/

public section
noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain NumberField
open _root_.ValuativeRel
open scoped AdicCompletionExtension

variable (K : Type) [Field K] [NumberField K]

/-- A cyclotomic extension of a number field kills all localizations of a given Brauer class.
The modulus is divisible by four, so the resulting field has no real places. This theorem
makes no assertion that the global base-changed class itself vanishes. -/
theorem exists_cyclotomicField_brLocalization_eq_zero (x : Br K) :
    ∃ m : ℕ, m ≠ 0 ∧ 4 ∣ m ∧
      brLocalization (CyclotomicField m K) (brBaseChange K (CyclotomicField m K) x) = 0 := by
  classical
  obtain ⟨n, hn, hx⟩ := isOfFinAddOrder_iff_nsmul_eq_zero.mp
    (ContinuousCohomology.isAddTorsion_continuousCohomology (X := unitsRep K) 1 x)
  let S := brauerSupport K x
  let c (v : HeightOneSpectrum (𝓞 K)) := Nat.card 𝓀[v.adicCompletion K] ^ n - 1
  have hc (v : HeightOneSpectrum (𝓞 K)) : c v ≠ 0 :=
    Nat.sub_ne_zero_of_lt (Nat.one_lt_pow hn.ne' Finite.one_lt_card)
  let m := 4 * ∏ v ∈ S, c v
  have hm : m ≠ 0 := mul_ne_zero (by decide) (Finset.prod_ne_zero_iff.mpr fun v _ => hc v)
  have h4 : 4 ∣ m := dvd_mul_right _ _
  let L := CyclotomicField m K
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L
    (Set.mem_singleton m) hm
  refine ⟨m, hm, h4, Prod.ext (DFinsupp.ext fun w => ?_) (funext fun w => ?_)⟩
  · let v := w.under (𝓞 K)
    simp only [brLocalization_fst_apply, Prod.fst_zero, DFinsupp.zero_apply]
    rw [brBaseChange_brBaseChange K L (w.adicCompletion L),
      ← brBaseChange_brBaseChange K (v.adicCompletion K) (w.adicCompletion L)]
    by_cases hv : v ∈ S
    · have hd : c v ∣ m := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem c hv) 4
      have hroot := (hζ.pow (Nat.pos_of_ne_zero hm) (Nat.div_mul_cancel hd).symm).map_of_injective
        (FaithfulSMul.algebraMap_injective L (w.adicCompletion L))
      exact brBaseChange_eq_zero_of_isPrimitiveRoot hn.ne' hroot
        (brBaseChange K (v.adicCompletion K) x) (by rw [← map_nsmul, hx, map_zero])
    · rw [(finiteInvAt_eq_zero_iff K v x).mp
        (finiteInvAt_eq_zero_of_notMem_brauerSupport K hv), map_zero]
  · simp only [brLocalization_snd_apply, Prod.snd_zero, Pi.zero_apply]
    have hroot := hζ.pow (Nat.pos_of_ne_zero hm) (Nat.div_mul_cancel h4).symm
    have : IsTotallyComplex L := nrRealPlaces_eq_zero_iff.mp
      (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by decide) hroot)
    exact brCompletion_eq_zero_of_isComplex w (IsTotallyComplex.isComplex w) _

end TauCeti.ClassFieldTheory
