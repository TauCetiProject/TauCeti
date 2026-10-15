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
infinite place, arbitrary at `T`, and integral units outside `S ∪ T`. This is the subgroup used
in the Kummer proof of the second fundamental inequality. The freedom at `T` is what allows the
places there to split completely in the extension under consideration.

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

/-- The **auxiliary Kummer idele subgroup** `E_{S,T}`: `n`-th powers at the finite places in
`S` and at every infinite place, arbitrary coordinates at `T`, and integral units at the finite
places outside `S ∪ T`. -/
def auxiliaryKummerIdeleSubgroup (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Subgroup (IdeleGroup (𝓞 K) K) :=
  (⨅ v : S, (powMonoidHom n).range.comap v.1.ideleFiniteCoord) ⊓
    (⨅ w : InfinitePlace K, (powMonoidHom n).range.comap w.ideleInfiniteCoord) ⊓
    ⨅ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S ∧ v ∉ T},
      (v.1.adicCompletionIntegers K).units.comap v.1.ideleFiniteCoord

/-- Membership in `E_{S,T}` is given by the power conditions at `S` and infinity and the
integral-unit condition outside `S ∪ T`. -/
@[simp]
theorem mem_auxiliaryKummerIdeleSubgroup_iff
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) (x : IdeleGroup (𝓞 K) K) :
    x ∈ auxiliaryKummerIdeleSubgroup S T n ↔
      (∀ v ∈ S, v.ideleFiniteCoord x ∈ (powMonoidHom n).range) ∧
      (∀ w : InfinitePlace K, w.ideleInfiniteCoord x ∈ (powMonoidHom n).range) ∧
      ∀ v ∉ S, v ∉ T → Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  simp [auxiliaryKummerIdeleSubgroup, Subgroup.mem_iInf,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one, and_assoc]

/-- At exponent one, `E_{S,T}` is the full group of `(S ∪ T)`-ideles. -/
theorem mem_auxiliaryKummerIdeleSubgroup_one_iff
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (x : IdeleGroup (𝓞 K) K) :
    x ∈ auxiliaryKummerIdeleSubgroup S T 1 ↔
      ∀ v ∉ S, v ∉ T → Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  simp

/-- Every auxiliary Kummer idele is an `(S ∪ T)`-idele. -/
theorem auxiliaryKummerIdeleSubgroup_le_one
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    auxiliaryKummerIdeleSubgroup S T n ≤ auxiliaryKummerIdeleSubgroup S T 1 := by
  intro x hx
  exact (mem_auxiliaryKummerIdeleSubgroup_one_iff S T x).mpr
    ((mem_auxiliaryKummerIdeleSubgroup_iff S T n x).mp hx).2.2

private abbrev AuxiliaryLocalPowerClasses
    (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :=
  (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ (powMonoidHom n).range) ×
    (∀ w : InfinitePlace K, w.Completionˣ ⧸ (powMonoidHom n).range)

private def auxiliaryLocalPowerClassMap
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    auxiliaryKummerIdeleSubgroup S T 1 →* AuxiliaryLocalPowerClasses S n where
  toFun x := (fun v ↦ QuotientGroup.mk (v.1.ideleFiniteCoord x.1),
    fun w ↦ QuotientGroup.mk (w.ideleInfiniteCoord x.1))
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [QuotientGroup.mk_mul]

private theorem auxiliaryLocalPowerClassMap_apply
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (x : auxiliaryKummerIdeleSubgroup S T 1) :
    auxiliaryLocalPowerClassMap S T n x =
      (fun v ↦ QuotientGroup.mk (v.1.ideleFiniteCoord x.1),
        fun w ↦ QuotientGroup.mk (w.ideleInfiniteCoord x.1)) :=
  (rfl)

private theorem auxiliaryLocalPowerClassMap_surjective
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Function.Surjective (auxiliaryLocalPowerClassMap S T n) := by
  classical
  rintro ⟨xf, xi⟩
  choose z hz using fun v : S ↦ QuotientGroup.mk_surjective (xf v)
  choose zi hzi using fun w : InfinitePlace K ↦ QuotientGroup.mk_surjective (xi w)
  let zf (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
    if hv : v ∈ S then z ⟨v, hv⟩ else 1
  have hzfu : ∀ᶠ v in Filter.cofinite, zf v ∈ (v.adicCompletionIntegers K).units :=
    S.eventually_cofinite_notMem.mono fun v hv ↦ by simp [zf, hv]
  let x := GlobalNumberFields.ideleOfUnits zi zf hzfu
  have hx : x ∈ auxiliaryKummerIdeleSubgroup S T 1 := by
    rw [mem_auxiliaryKummerIdeleSubgroup_one_iff]
    intro v hvS hvT
    simp [x, zf, hvS]
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Prod.ext
  · funext v
    simpa [auxiliaryLocalPowerClassMap, x, zf, v.2] using hz v
  · funext w
    simpa [auxiliaryLocalPowerClassMap, x] using hzi w

private theorem ker_auxiliaryLocalPowerClassMap
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    (auxiliaryLocalPowerClassMap S T n).ker =
      (auxiliaryKummerIdeleSubgroup S T n).subgroupOf
        (auxiliaryKummerIdeleSubgroup S T 1) := by
  ext x
  have hx := (mem_auxiliaryKummerIdeleSubgroup_one_iff S T x.1).mp x.2
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, auxiliaryLocalPowerClassMap_apply]
  simp only [mem_auxiliaryKummerIdeleSubgroup_iff, Prod.ext_iff, funext_iff, Prod.fst_one,
    Prod.snd_one, Pi.one_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨hf, hi⟩
    exact ⟨fun v hv ↦ hf ⟨v, hv⟩, hi, hx⟩
  · rintro ⟨hf, hi, -⟩
    exact ⟨fun v ↦ hf v.1 v.2, hi⟩

/-- The relative index of `E_{S,T}` in the group of `(S ∪ T)`-ideles is the product of the
power-class counts at the places in `S` and at the infinite places. -/
theorem relIndex_auxiliaryKummerIdeleSubgroup
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    (auxiliaryKummerIdeleSubgroup S T n).relIndex
        (auxiliaryKummerIdeleSubgroup S T 1) =
      (∏ v ∈ S, Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n).range)) *
        ∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸ (powMonoidHom n).range) := by
  rw [Subgroup.relIndex, ← ker_auxiliaryLocalPowerClassMap]
  calc
    _ = Nat.card (AuxiliaryLocalPowerClasses S n) := Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective (auxiliaryLocalPowerClassMap S T n)
        (auxiliaryLocalPowerClassMap_surjective S T n)).toEquiv
    _ = _ := by
      rw [Nat.card_prod, Nat.card_pi, Nat.card_pi]
      congr 1
      let f (v : HeightOneSpectrum (𝓞 K)) :=
        Nat.card ((v.adicCompletion K)ˣ ⧸ (powMonoidHom n).range)
      change (∏ v : S, f v) = ∏ v ∈ S, f v
      exact Finset.prod_coe_sort S f

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

/-- The image of `E_{S,T}` in the idele class group. -/
def auxiliaryKummerIdeleClassSubgroup
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Subgroup (IdeleClassGroup (𝓞 K) K) :=
  (auxiliaryKummerIdeleSubgroup S T n).map
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))

/-- An idele class belongs to the auxiliary Kummer subgroup exactly when it has a representative
in `E_{S,T}`. -/
@[simp]
theorem mem_auxiliaryKummerIdeleClassSubgroup_iff
    (S T : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (c : IdeleClassGroup (𝓞 K) K) :
    c ∈ auxiliaryKummerIdeleClassSubgroup S T n ↔
      ∃ x ∈ auxiliaryKummerIdeleSubgroup S T n,
        (x : IdeleClassGroup (𝓞 K) K) = c :=
  (Iff.rfl)

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
