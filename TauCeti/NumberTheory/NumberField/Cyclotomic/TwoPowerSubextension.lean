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

/-!
# Imaginary cyclic subextensions of two-power cyclotomic extensions

A two-power cyclotomic extension of a number field has a totally complex intermediate field
that is cyclic over the base and has relative index at most two.

The construction uses a character of the modular unit group that detects both the unit `5`
and `-1`. The former bounds its kernel; the latter excludes real places of its fixed field.
Characters are extended using `TauCeti.CharacterModule.exists_apply_eq_inv_addOrderOf`, and the
order of `5` is Mathlib's `ZMod.orderOf_five`.

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

end TauCeti.NumberField
