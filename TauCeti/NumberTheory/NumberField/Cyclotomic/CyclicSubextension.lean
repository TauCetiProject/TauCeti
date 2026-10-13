/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Cyclotomic.Gal
public import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
public import TauCeti.Data.ZMod.TwoPowerCharacter
public import TauCeti.NumberTheory.NumberField.ComplexConjugation.Cyclotomic
import TauCeti.NumberTheory.Cyclotomic.Aut

/-!
# Imaginary cyclic subextensions of prime-power cyclotomic extensions

A cyclotomic extension `L/K` of a number field of prime-power level `ℓ ^ r > 2` has a totally
complex intermediate field that is cyclic over the base and has relative index at most two
(`exists_isTotallyComplex_isCyclic_subextension_prime_pow`).

When `(ZMod (ℓ ^ r))ˣ` is cyclic, that is, for `ℓ` odd and for `ℓ ^ r = 4`, the whole extension
does: its Galois group embeds in `(ZMod (ℓ ^ r))ˣ` through the cyclotomic character, and it is
totally complex because it contains a primitive root of unity of order greater than two. For the
levels `2 ^ (n + 3)` the group `(ZMod (2 ^ (n + 3)))ˣ` is not cyclic, and the subextension
(`exists_isTotallyComplex_isCyclic_subextension_two_pow`) is the fixed field of the kernel of a
character of the modular unit group that detects both the unit `5` and `-1`. The former bounds
its kernel; the latter excludes real places of its fixed field. Characters are extended using
`TauCeti.CharacterModule.exists_apply_eq_inv_addOrderOf`, and the order of `5` is Mathlib's
`ZMod.orderOf_five`.

These are the cyclic cyclotomic extensions along which a primary Brauer class of `K` is split at
every place.

## Main results

* `TauCeti.NumberField.exists_isTotallyComplex_isCyclic_subextension_two_pow`: the subextension at
  the levels `2 ^ (n + 3)`.
* `TauCeti.NumberField.exists_isTotallyComplex_isCyclic_subextension_prime_pow`: the subextension
  at every prime-power level `ℓ ^ r > 2`.

## Reference

* J. S. Milne, *Class Field Theory*, Chapter VII, Lemma 7.3,
  <https://www.jmilne.org/math/CourseNotes/CFT.pdf>.
-/

public section

noncomputable section

open NumberField NumberField.InfinitePlace
open scoped NumberField

namespace TauCeti.NumberField

variable (K L : Type*) [Field K] [NumberField K] [Field L]
  [Algebra K L]

/-- A `2^(n+3)`-cyclotomic extension of a number field contains a totally complex cyclic
extension of the base whose relative index in the full extension is at most two. No
irreducibility assumption on the cyclotomic polynomial over the base is required. -/
theorem exists_isTotallyComplex_isCyclic_subextension_two_pow (n : ℕ)
    [IsCyclotomicExtension {2 ^ (n + 3)} K L] :
    ∃ E : IntermediateField K L,
      IsGalois K E ∧ IsCyclic (Gal(E/K)) ∧ Module.finrank E L ≤ 2 ∧ IsTotallyComplex E := by
  let : NeZero (2 ^ (n + 3)) := ⟨by positivity⟩
  have : NumberField L := IsCyclotomicExtension.numberField {2 ^ (n + 3)} K L
  let : IsGalois K L := IsCyclotomicExtension.isGalois {2 ^ (n + 3)} K L
  let ζ := IsCyclotomicExtension.zeta (2 ^ (n + 3)) K L
  have hζ : IsPrimitiveRoot ζ (2 ^ (n + 3)) := IsCyclotomicExtension.zeta_spec _ K L
  obtain ⟨χ, _, hχneg, hχker⟩ := CharacterModule.exists_character_units_two_pow n
  let f := χ.toMultiplicativeRight.comp (hζ.autToPow K)
  let E := IntermediateField.fixedField f.ker
  have hgal : IsGalois K E := inferInstance
  -- The cyclotomic character embeds the new kernel into the modular character's kernel.
  let i : f.ker → χ.ker := fun σ ↦ ⟨Additive.ofMul (hζ.autToPow K σ), by
    have hs : f σ.val = 1 := MonoidHom.mem_ker.mp σ.property
    simpa only [f, MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply,
      ofAdd_eq_one, AddMonoidHom.mem_ker] using hs⟩
  have hi : Function.Injective i := by
    intro σ τ h
    apply Subtype.ext
    exact hζ.autToPow_injective K (Additive.ofMul.injective (congrArg Subtype.val h))
  have hdegree : Module.finrank E L ≤ 2 := by
    rw [IntermediateField.finrank_fixedField_eq_card]
    exact (Nat.card_le_card_of_injective i hi).trans hχker
  -- A finite subgroup of ℚ/ℤ is cyclic; the first isomorphism theorem transfers this to E/K.
  obtain ⟨d, hd, hχrange⟩ := AddCircle.exists_eq_torsionBy (1 : ℚ) (H := χ.range)
  have : IsAddCyclic χ.range := by
    rw [hχrange]
    exact AddCircle.isAddCyclic_torsionBy (1 : ℚ) (Nat.cast_ne_zero.mpr hd.ne')
  let j : f.range →* Multiplicative χ.range := {
    toFun := fun y ↦ Multiplicative.ofAdd ⟨y.val.toAdd, by
      obtain ⟨σ, hσ⟩ := y.property
      exact ⟨Additive.ofMul (hζ.autToPow K σ), by
        simpa [f] using congrArg Multiplicative.toAdd hσ⟩⟩
    map_one' := rfl
    map_mul' := fun _ _ ↦ rfl }
  have hj : Function.Injective j := by
    intro y z h
    apply Subtype.ext
    have he : y.val.toAdd = z.val.toAdd :=
      congrArg (fun t : Multiplicative χ.range ↦ (t.toAdd : AddCircle (1 : ℚ))) h
    exact Multiplicative.toAdd.injective he
  have : IsCyclic f.range := isCyclic_of_injective j hj
  have : IsCyclic ((Gal(L/K)) ⧸ f.ker) :=
    isCyclic_of_injective (QuotientGroup.quotientKerEquivRange f).toMonoidHom
      (QuotientGroup.quotientKerEquivRange f).injective
  have hcyclic : IsCyclic (Gal(E/K)) :=
    isCyclic_of_surjective (IsGalois.normalAutEquivQuotient f.ker).toMonoidHom
      (IsGalois.normalAutEquivQuotient f.ker).surjective
  -- A real place of E would make complex conjugation belong to the kernel, contradicting χ(-1).
  have : IsTotallyComplex L := nrRealPlaces_eq_zero_iff.mp
    (hζ.nrRealPlaces_eq_zero_of_two_lt (by
      have : 2 ^ 3 ≤ 2 ^ (n + 3) := Nat.pow_le_pow_right (by decide) (by omega)
      omega))
  have hcomplex : IsTotallyComplex E := ⟨fun v ↦ by
    rw [← not_isReal_iff_isComplex]
    intro hv
    obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (K := L) v
    have hwreal : (w.comap (algebraMap E L)).IsReal := by simpa only [hw] using hv
    have hbase : (w.comap (algebraMap K L)).IsReal := by
      simpa only [InfinitePlace.comap_comp, IsScalarTower.algebraMap_eq K E L] using
        hwreal.comap (algebraMap K E)
    have hram : w.IsRamified K := isRamified_iff.mpr ⟨IsTotallyComplex.isComplex w, hbase⟩
    let c := complexConjugationAt K w hram
    have hres : c.restrictNormal E = 1 :=
      complexConjugationAt_restrictNormal_eq_one_of_isReal K w hram hwreal
    have hc : c ∈ f.ker := by
      rw [← IntermediateField.fixingSubgroup_fixedField f.ker,
        ← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker]
      exact hres
    have hzero : χ (Additive.ofMul (hζ.autToPow K c)) = 0 := by
      have he : f c = 1 := MonoidHom.mem_ker.mp hc
      simpa only [f, MonoidHom.comp_apply, AddMonoidHom.toMultiplicativeRight_apply_apply,
        ofAdd_eq_one] using he
    rw [hζ.autToPow_complexConjugationAt w hram] at hzero
    exact hχneg hzero⟩
  exact ⟨E, hgal, hcyclic, hdegree, hcomplex⟩

/-- A cyclotomic extension of a number field of prime-power level `ℓ ^ r > 2` contains a totally
complex cyclic extension of the base whose relative index in the full extension is at most two.
No irreducibility assumption on the cyclotomic polynomial over the base is required. -/
theorem exists_isTotallyComplex_isCyclic_subextension_prime_pow {ℓ r : ℕ} (hℓ : ℓ.Prime)
    (hr : 2 < ℓ ^ r) [IsCyclotomicExtension {ℓ ^ r} K L] :
    ∃ E : IntermediateField K L,
      IsGalois K E ∧ IsCyclic (Gal(E/K)) ∧ Module.finrank E L ≤ 2 ∧ IsTotallyComplex E := by
  by_cases h8 : ℓ = 2 ∧ 3 ≤ r
  · obtain ⟨rfl, hr3⟩ := h8
    obtain ⟨n, rfl⟩ : ∃ n, r = n + 3 := ⟨r - 3, by omega⟩
    exact exists_isTotallyComplex_isCyclic_subextension_two_pow K L n
  -- Otherwise `(ZMod (ℓ ^ r))ˣ` is cyclic, and the whole extension is cyclic.
  have : IsCyclic (ZMod (ℓ ^ r))ˣ := by
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      obtain rfl : r = 2 := by
        have : r ≤ 2 := by omega
        interval_cases r <;> simp_all
      exact ZMod.isCyclic_units_four
    · exact ZMod.isCyclic_units_of_prime_pow ℓ hℓ hℓ2 r
  have : NeZero (ℓ ^ r) := ⟨by omega⟩
  have : NumberField L := IsCyclotomicExtension.numberField {ℓ ^ r} K L
  have : IsGalois K L := IsCyclotomicExtension.isGalois {ℓ ^ r} K L
  have : IsCyclic Gal(L/K) := IsCyclotomicExtension.isCyclic_aut (n := ℓ ^ r) K L
  have : IsTotallyComplex L := nrRealPlaces_eq_zero_iff.mp
    ((IsCyclotomicExtension.zeta_spec (ℓ ^ r) K L).nrRealPlaces_eq_zero_of_two_lt hr)
  -- `⊤` is `L` itself, read through `IntermediateField.topEquiv`.
  let e : (⊤ : IntermediateField K L) ≃ₐ[K] L := IntermediateField.topEquiv
  let : Algebra L (⊤ : IntermediateField K L) := e.symm.toRingHom.toAlgebra
  exact ⟨⊤, isGalois_iff_isGalois_top.mpr inferInstance,
    isCyclic_of_surjective (AlgEquiv.autCongr e).symm.toMonoidHom
      (AlgEquiv.autCongr e).symm.surjective,
    IntermediateField.finrank_top.trans_le one_le_two, isTotallyComplex_of_algebra L _⟩

end TauCeti.NumberField
