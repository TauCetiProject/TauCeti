/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.ExponentNorms
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles
public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic

/-!
# Kummer idele subgroups contained in norm groups

Let `L/K` be a finite Galois extension of number fields whose Galois group has exponent dividing
`n`. If a finite set `S` contains every prime ramified in `L`, then the Kummer idele subgroup
`E_S` of ideles that are local `n`-th powers at `S` and at infinity, and units outside `S`, is
contained in the idele norm group of `L/K`. Consequently its image in the idele class group is
contained in the idele-class norm group.

The proof is placewise. At the places of `S` and at infinity, exponent divisibility makes every
`n`-th power a local norm. Outside `S`, the extension is unramified and local units are norms.
The resulting inclusion is the norm half of the Kummer computation of the second fundamental
inequality. It converts the index of the idele-class norm group into a divisor of the index of the
Kummer idele-class subgroup.

## Main statements

* `TauCeti.ClassFieldTheory.kummerIdeleSubgroup_le_range_ideleNormMap`: the Kummer idele subgroup
  is contained in the idele norm group.
* `TauCeti.ClassFieldTheory.kummerIdeleClassSubgroup_le_range_ideleClassNormMap`: the corresponding
  inclusion after passage to idele classes.
* `TauCeti.ClassFieldTheory.index_range_ideleClassNormMap_dvd_index_kummerIdeleClassSubgroup`:
  the resulting divisibility of indices.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §§5--6.
-/

public section

noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable (K : Type) [Field K] [NumberField K]
variable (L : Type*) [Field L] [NumberField L] [Algebra K L] [IsGalois K L]

/-- **The Kummer idele subgroup consists of norms.** If the exponent of `Gal(L/K)` divides `n`
and `S` contains every finite place ramified in `L`, then every idele in the Kummer subgroup
`E_S` is the norm of an idele of `L`. -/
theorem kummerIdeleSubgroup_le_range_ideleNormMap {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S) :
    kummerIdeleSubgroup S n ≤
      (GlobalNumberFields.ideleNormMap K L).toMonoidHom.range := by
  intro x hx
  rw [mem_kummerIdeleSubgroup_iff] at hx
  refine mem_range_ideleNormMap_of_exponent_dvd K L hn (S := (S : Set _)) (T := ∅)
    (by simp) ?_ ?_ ?_ ?_
  · intro v hvS _
    obtain ⟨w, hw⟩ := HeightOneSpectrum.under_surjective (𝓞 K) (𝓞 L) v
    have hw' : w.asIdeal.LiesOver v.asIdeal := ⟨congrArg HeightOneSpectrum.asIdeal hw.symm⟩
    let _ : w.asIdeal.LiesOver v.asIdeal := hw'
    exact ⟨⟨w, hw'⟩, TauCeti.NumberField.isUnramifiedAway_ramifiedSupport v
      (fun hv ↦ hvS (hram hv)) w.asIdeal⟩
  · intro v hvS
    rw [powerSubgroup_eq_range_powMonoidHom]
    exact hx.1 v hvS
  · intro v hvS _
    exact hx.2.2 v hvS
  · intro v
    rw [powerSubgroup_eq_range_powMonoidHom]
    exact hx.2.1 v

/-- **The Kummer idele-class subgroup consists of norms.** Under the same hypotheses as
`kummerIdeleSubgroup_le_range_ideleNormMap`, every class represented by a Kummer idele is in
`N_{L/K}(C_L)`. -/
theorem kummerIdeleClassSubgroup_le_range_ideleClassNormMap {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S) :
    kummerIdeleClassSubgroup S n ≤
      (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ := (mem_kummerIdeleClassSubgroup_iff S n c).mp hc
  obtain ⟨y, hy⟩ := kummerIdeleSubgroup_le_range_ideleNormMap K L hn S hram hx
  refine ⟨(y : IdeleClassGroup (𝓞 L) L), ?_⟩
  change GlobalNumberFields.ideleClassNormMap K L (y : IdeleClassGroup (𝓞 L) L) =
    (x : IdeleClassGroup (𝓞 K) K)
  rw [GlobalNumberFields.ideleClassNormMap_mk]
  exact congrArg (fun z : IdeleGroup (𝓞 K) K ↦ (z : IdeleClassGroup (𝓞 K) K)) hy

/-- **The idele-class norm index divides the Kummer subgroup index.** If `S` contains the
ramified places and `n` is divisible by the exponent of `Gal(L/K)`, then
`[C_K : N_{L/K}(C_L)]` divides `[C_K : E_S]`. -/
theorem index_range_ideleClassNormMap_dvd_index_kummerIdeleClassSubgroup {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S : Finset (HeightOneSpectrum (𝓞 K)))
    (hram : TauCeti.NumberField.ramifiedSupport K L ⊆ S) :
    (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range.index ∣
      (kummerIdeleClassSubgroup S n).index :=
  Subgroup.index_dvd_of_le
    (kummerIdeleClassSubgroup_le_range_ideleClassNormMap K L hn S hram)

end TauCeti.ClassFieldTheory
