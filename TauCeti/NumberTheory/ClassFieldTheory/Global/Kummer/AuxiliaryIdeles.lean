/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ClassFieldTheory.Global.ExponentNorms
public import TauCeti.NumberTheory.ClassFieldTheory.Global.Kummer.Ideles
public import TauCeti.NumberTheory.NumberField.Global.Places.PowerClasses

/-!
# The auxiliary Kummer idele subgroup

Let `S` and `T` be finite sets of finite places of a number field `K`. The auxiliary Kummer
idele subgroup `E_{S,T}` consists of the ideles that are `n`-th powers at `S` and at every
infinite place, arbitrary at `T \ S`, and integral units outside `S ∪ T`; the power condition
continues to apply on `S ∩ T`. This is the subgroup used in the Kummer proof of the second
fundamental inequality. The freedom at `T \ S` is what allows those places to split completely
in the extension under consideration.

The index of `E_{S,T}` in the group of `(S ∪ T)`-ideles is the product of the power-class
counts at `S` and at the infinite places. If `K` contains the `n`-th roots of unity and `S`
contains the places above `n`, the product formula evaluates this index as

`n ^ (2 * (#S + r₁ + r₂))`.

If an extension has exponent dividing `n`, splits at `T`, and is unramified outside `S ∪ T`,
then `E_{S,T}` consists of idele norms. Thus its image in the idele class group is contained in
the idele-class norm subgroup.

## Main definitions

* `TauCeti.ClassFieldTheory.auxiliaryKummerIdeleSubgroup`: the subgroup `E_{S,T}`.
* `TauCeti.ClassFieldTheory.auxiliaryKummerIdeleClassSubgroup`: its image in the idele class
  group.

## Main results

* `TauCeti.ClassFieldTheory.relIndex_auxiliaryKummerIdeleSubgroup`: the exact local-product
  formula for the index of `E_{S,T}`.
* `TauCeti.ClassFieldTheory.relIndex_auxiliaryKummerIdeleSubgroup_eq_pow`: the evaluation of that
  product when `K` contains the `n`-th roots of unity.
* `TauCeti.ClassFieldTheory.auxiliaryKummerIdeleSubgroup_le_range_ideleNormMap`: `E_{S,T}`
  consists of norms under the split and unramified hypotheses.

## References

* J. S. Milne, *Class Field Theory*, v4.03, Chapter VII, §6, Lemmas 6.4 and 6.6.
-/

public noncomputable section

open IsDedekindDomain NumberField
open scoped AdicCompletionExtension NumberField.LiesOver

namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- If `K` contains the `n`-th roots of unity and `S` contains every place above `n`, then the
relative index of `E_{S,T}` in the `(S ∪ T)`-ideles is
`n ^ (2 * (#S + r₁ + r₂))`. -/
theorem relIndex_auxiliaryKummerIdeleSubgroup_eq_pow
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) [NeZero n]
    [HasEnoughRootsOfUnity K n]
    (hS : ∀ v : HeightOneSpectrum (𝓞 K), (n : 𝓞 K) ∈ v.asIdeal → v ∈ S) :
    (auxiliaryKummerIdeleSubgroup S T n).relIndex
        (auxiliaryKummerIdeleSubgroup S T 1) =
      n ^ (2 * (S.card + Fintype.card (InfinitePlace K))) := by
  rw [relIndex_auxiliaryKummerIdeleSubgroup]
  exact GlobalNumberFields.prod_card_powerClasses n S hS

variable (K : Type) (L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

/-- **The auxiliary Kummer ideles are norms.** If the exponent of `Gal(L/K)` divides `n`, the
places in `T` split locally in `L`, and `L/K` is unramified outside `S ∪ T`, then every idele
in `E_{S,T}` is a norm from `L`. -/
theorem auxiliaryKummerIdeleSubgroup_le_range_ideleNormMap {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (hU : ∀ v ∉ S, v ∉ T →
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) :
    auxiliaryKummerIdeleSubgroup S T n ≤
      (GlobalNumberFields.ideleNormMap K L).toMonoidHom.range := by
  intro x hx
  rw [mem_auxiliaryKummerIdeleSubgroup_iff] at hx
  refine mem_range_ideleNormMap_of_exponent_dvd K L hn
    (S := (S : Set _)) (T := (T : Set _)) hT hU ?_ ?_ ?_
  · intro v hv
    rw [powerSubgroup_eq_range_powMonoidHom]
    exact hx.1 v hv
  · intro v hvS hvT
    exact hx.2.2 v hvS hvT
  · intro w
    rw [powerSubgroup_eq_range_powMonoidHom]
    exact hx.2.1 w

/-- Under the split and unramified hypotheses, the image of `E_{S,T}` in the idele class group
is contained in the idele-class norm subgroup. -/
theorem auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (hU : ∀ v ∉ S, v ∉ T →
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) :
    auxiliaryKummerIdeleClassSubgroup (K := K) S T n ≤
      (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range := by
  intro c hc
  obtain ⟨x, hx, rfl⟩ :=
    (mem_auxiliaryKummerIdeleClassSubgroup_iff (K := K) S T n c).mp hc
  obtain ⟨y, hy⟩ :=
    auxiliaryKummerIdeleSubgroup_le_range_ideleNormMap K L hn S T hT hU hx
  refine ⟨(y : IdeleClassGroup (𝓞 L) L), ?_⟩
  exact (GlobalNumberFields.ideleClassNormMap_mk y).trans
    (congrArg (fun z : IdeleGroup (𝓞 K) K ↦ (z : IdeleClassGroup (𝓞 K) K)) hy)

/-- The idele-class norm index divides the index of the image of `E_{S,T}`. -/
theorem index_range_ideleClassNormMap_dvd_index_auxiliaryKummerIdeleClassSubgroup {n : ℕ}
    (hn : Monoid.exponent Gal(L/K) ∣ n) (S T : Finset (HeightOneSpectrum (𝓞 K)))
    (hT : ∀ v ∈ T, ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
      Module.finrank (v.adicCompletion K) (w.1.adicCompletion L) = 1)
    (hU : ∀ v ∉ S, v ∉ T →
      ∃ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal) :
    (GlobalNumberFields.ideleClassNormMap K L :
        IdeleClassGroup (𝓞 L) L →* IdeleClassGroup (𝓞 K) K).range.index ∣
      (auxiliaryKummerIdeleClassSubgroup (K := K) S T n).index :=
  Subgroup.index_dvd_of_le
    (auxiliaryKummerIdeleClassSubgroup_le_range_ideleClassNormMap K L hn S T hT hU)

end TauCeti.ClassFieldTheory
