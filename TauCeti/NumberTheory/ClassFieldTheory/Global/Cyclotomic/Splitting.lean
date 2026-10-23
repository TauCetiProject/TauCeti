/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.NumberTheory.ClassFieldTheory.Global.InvariantSum
public import TauCeti.RingTheory.DedekindDomain.AdicCompletionExtension
import TauCeti.NumberTheory.NumberField.Cyclotomic.CyclicSubextension
import TauCeti.NumberTheory.NumberField.Cyclotomic.LocalDegree
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

A class killed by a power `ℓ ^ k` of a prime `ℓ` is already split locally by the cyclotomic
field of level `ℓ ^ r` for all large `r`: the local degrees of these fields at a given place
become divisible by `ℓ ^ k` (`IsCyclotomicExtension.eventually_pow_dvd_finrank_adicCompletion`),
and a local extension of degree divisible by `ℓ ^ k` splits every `ℓ ^ k`-torsion local class.
For `ℓ` odd this field is a cyclic extension, which is what the computation of the sum of the
local invariants through the local Artin symbols of a character requires. For `ℓ = 2` it is not
cyclic once `r ≥ 3`, but it contains a totally complex subfield, cyclic over `K`, of index at most
two (`TauCeti.NumberField.exists_isTotallyComplex_isCyclic_subextension_prime_pow`). Its local
degrees above a given place are those of the cyclotomic field divided by at most two, so they too
become divisible by `ℓ ^ k`
(`IsCyclotomicExtension.eventually_pow_dvd_finrank_adicCompletion_of_finrank_le`), and it still
splits the class locally. Hence, for every prime `ℓ`, every cyclotomic extension of level `ℓ ^ r`
with `r` large contains a cyclic extension of `K` that kills all localizations of a class killed
by a power of `ℓ` (`eventually_exists_isCyclic_brLocalization_eq_zero`).

The conclusion is local splitting, not global splitting: deducing the latter requires
injectivity of Brauer localization. The local statement supplies the cyclotomic splitting
input to the sum-of-local-invariants argument without assuming a global reciprocity law.

## Main results

* `TauCeti.ClassFieldTheory.brLocalization_brBaseChange_eq_zero_of_forall`: an extension without
  real places kills all localizations of a Brauer class once it kills them above its support.
* `TauCeti.ClassFieldTheory.exists_cyclotomicField_brLocalization_eq_zero`: one cyclotomic
  extension kills all localizations of a global Brauer class.
* `TauCeti.ClassFieldTheory.eventually_cyclotomicField_brLocalization_eq_zero`: the cyclotomic
  fields of level `ℓ ^ r`, for all large `r`, kill all localizations of a Brauer class killed by
  a power of `ℓ`.
* `TauCeti.ClassFieldTheory.eventually_exists_isCyclic_brLocalization_eq_zero`: so do cyclic
  subextensions of the cyclotomic extensions of level `ℓ ^ r`, for all large `r`.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, Proposition 7.2 and Lemma 7.3.
-/

public section
noncomputable section

namespace TauCeti.ClassFieldTheory

open IsDedekindDomain _root_.NumberField
open _root_.ValuativeRel
open scoped AdicCompletionExtension

variable (K : Type) [Field K] [NumberField K]

/-- An extension `L` of a number field `K` without real places kills all localizations of a
Brauer class `x` of `K` as soon as, at every place `w` of `L` above a place `v` in the support of
`x`, the local class of `x` at `v` dies in the extension `L_w / K_v`. -/
theorem brLocalization_brBaseChange_eq_zero_of_forall (L : Type) [Field L] [NumberField L]
    [Algebra K L] [IsTotallyComplex L] (x : Br K)
    (h : ∀ w : HeightOneSpectrum (𝓞 L), w.under (𝓞 K) ∈ brauerSupport K x →
      brBaseChange ((w.under (𝓞 K)).adicCompletion K) (w.adicCompletion L)
        (brBaseChange K _ x) = 0) :
    brLocalization L (brBaseChange K L x) = 0 := by
  refine Prod.ext (DFinsupp.ext fun w => ?_) (funext fun w => ?_)
  · let v := w.under (𝓞 K)
    simp only [brLocalization_fst_apply, Prod.fst_zero, DFinsupp.zero_apply]
    rw [brBaseChange_brBaseChange K L (w.adicCompletion L),
      ← brBaseChange_brBaseChange K (v.adicCompletion K) (w.adicCompletion L)]
    by_cases hv : v ∈ brauerSupport K x
    · exact h w hv
    · rw [(finiteInvAt_eq_zero_iff K v x).mp
        (finiteInvAt_eq_zero_of_notMem_brauerSupport K hv), map_zero]
  · simp only [brLocalization_snd_apply, Prod.snd_zero, Pi.zero_apply]
    exact brCompletion_eq_zero_of_isComplex w (IsTotallyComplex.isComplex w) _

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
  have : IsTotallyComplex L := nrRealPlaces_eq_zero_iff.mp
    (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt (by decide)
      (hζ.pow (Nat.pos_of_ne_zero hm) (Nat.div_mul_cancel h4).symm))
  refine ⟨m, hm, h4, brLocalization_brBaseChange_eq_zero_of_forall K L x fun w hv => ?_⟩
  have hd : c (w.under (𝓞 K)) ∣ m := dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem c hv) 4
  have hroot := (hζ.pow (Nat.pos_of_ne_zero hm) (Nat.div_mul_cancel hd).symm).map_of_injective
    (FaithfulSMul.algebraMap_injective L (w.adicCompletion L))
  exact brBaseChange_eq_zero_of_isPrimitiveRoot hn.ne' hroot _
    (by rw [← map_nsmul, hx, map_zero])

/-- **The cyclotomic tower of level `ℓ ^ r` splits `ℓ`-primary Brauer classes locally.** A Brauer
class of a number field killed by a power of a prime `ℓ` has trivial localizations at every place
after extension to the cyclotomic field of level `ℓ ^ r`, for all large `r`. For `ℓ` odd this
extension is cyclic (`IsCyclotomicExtension.isCyclic_aut`, with `ZMod.isCyclic_units_of_prime_pow`).
This theorem makes no assertion that the global base-changed class itself vanishes. -/
theorem eventually_cyclotomicField_brLocalization_eq_zero {ℓ : ℕ} (hℓ : ℓ.Prime) {k : ℕ}
    (x : Br K) (hx : ℓ ^ k • x = 0) :
    ∀ᶠ r in Filter.atTop, brLocalization (CyclotomicField (ℓ ^ r) K)
      (brBaseChange K (CyclotomicField (ℓ ^ r) K) x) = 0 := by
  classical
  -- For large `r`, the local degree at every place above `brauerSupport K x` is divisible by
  -- `ℓ ^ k`, and `ℓ ^ r > 2`.
  filter_upwards [Filter.eventually_ge_atTop 2,
    (Filter.eventually_all_finset (brauerSupport K x)).2 fun v _ =>
      IsCyclotomicExtension.eventually_pow_dvd_finrank_adicCompletion.{0} hℓ k v] with r hr hloc
  have : NeZero (ℓ ^ r) := ⟨pow_ne_zero r hℓ.ne_zero⟩
  let L := CyclotomicField (ℓ ^ r) K
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L
    (Set.mem_singleton (ℓ ^ r)) (NeZero.ne _)
  have h2 : 2 < ℓ ^ r := lt_of_lt_of_le (by norm_num)
    ((Nat.pow_le_pow_left hℓ.two_le 2).trans (Nat.pow_le_pow_right hℓ.pos hr))
  have : IsTotallyComplex L := nrRealPlaces_eq_zero_iff.mp
    (InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt h2 hζ)
  exact brLocalization_brBaseChange_eq_zero_of_forall K L x fun w hv =>
    brBaseChange_eq_zero_of_dvd_finrank _ _ (hloc _ hv L w) _ (by rw [← map_nsmul, hx, map_zero])

/-- **Cyclic cyclotomic extensions split `ℓ`-primary Brauer classes locally.** Let `x` be a
Brauer class of a number field `K` killed by a power of a prime `ℓ`. For all large `r`, every
cyclotomic extension `F/K` of level `ℓ ^ r` contains an intermediate field `E`, Galois with cyclic
Galois group over `K`, after extension to which all localizations of `x` vanish. This theorem
makes no assertion that the global base-changed class itself vanishes. -/
theorem eventually_exists_isCyclic_brLocalization_eq_zero {ℓ : ℕ} (hℓ : ℓ.Prime) {k : ℕ}
    (x : Br K) (hx : ℓ ^ k • x = 0) :
    ∀ᶠ r in Filter.atTop, ∀ (F : Type) [Field F] [NumberField F] [Algebra K F]
      [IsCyclotomicExtension {ℓ ^ r} K F], ∃ E : IntermediateField K F,
        IsGalois K E ∧ IsCyclic Gal(E/K) ∧ brLocalization E (brBaseChange K E x) = 0 := by
  -- For large `r`, the local degree above every place of `brauerSupport K x` of every subfield
  -- of index at most two is divisible by `ℓ ^ k`, and `ℓ ^ r > 2`.
  filter_upwards [Filter.eventually_ge_atTop 2,
    (Filter.eventually_all_finset (brauerSupport K x)).2 fun v _ =>
      IsCyclotomicExtension.eventually_pow_dvd_finrank_adicCompletion_of_finrank_le.{0} hℓ k 2 v]
    with r hr hloc F _ _ _ _
  have h2 : 2 < ℓ ^ r := lt_of_lt_of_le (by norm_num)
    ((Nat.pow_le_pow_left hℓ.two_le 2).trans (Nat.pow_le_pow_right hℓ.pos hr))
  obtain ⟨E, hgal, hcyc, hdeg, hcx⟩ :=
    TauCeti.NumberField.exists_isTotallyComplex_isCyclic_subextension_prime_pow K F hℓ h2
  exact ⟨E, hgal, hcyc, brLocalization_brBaseChange_eq_zero_of_forall K E x fun w hv =>
    brBaseChange_eq_zero_of_dvd_finrank _ _ (hloc _ hv F E hdeg w) _
      (by rw [← map_nsmul, hx, map_zero])⟩

end TauCeti.ClassFieldTheory
