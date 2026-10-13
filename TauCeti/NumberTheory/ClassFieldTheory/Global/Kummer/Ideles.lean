/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.FiniteIdeal
public import Mathlib.GroupTheory.Index

/-!
# The Kummer idele subgroup and its local index

For a finite set `S` of finite places, `kummerIdeleSubgroup S n` consists of the ideles whose
coordinates are `n`-th powers at `S` and at every infinite place, and integral units elsewhere.
At exponent one it is the full group of `S`-ideles. The index of the exponent-`n` subgroup in
that group is the product of the local power-class counts. No roots-of-unity hypothesis is
needed for this identity.

If the primes in `S` generate the ideal class group, every idele class has an `S`-idele
representative. Consequently the index of the image of the Kummer subgroup in the idele class
group divides the same product. This separates the idelic index calculation used in Kummer
norm arguments from the arithmetic computations of the individual local factors.

## References

* J. S. Milne, *Class Field Theory*, Chapter VII, §§5 and 9.
-/

public noncomputable section

open IsDedekindDomain NumberField

namespace TauCeti.ClassFieldTheory

variable {K : Type*} [Field K] [NumberField K]

/-- The Kummer idele subgroup: local `n`-th powers at `S` and at all infinite places, and
integral units at the finite places outside `S`. -/
def kummerIdeleSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Subgroup (IdeleGroup (𝓞 K) K) :=
  (⨅ v : S, (powMonoidHom n).range.comap v.1.ideleFiniteCoord) ⊓
    (⨅ w : InfinitePlace K, (powMonoidHom n).range.comap w.ideleInfiniteCoord) ⊓
    ⨅ v : {v : HeightOneSpectrum (𝓞 K) // v ∉ S},
      (v.1.adicCompletionIntegers K).units.comap v.1.ideleFiniteCoord

/-- Membership is given by the local power and integral-unit conditions. -/
@[simp]
theorem mem_kummerIdeleSubgroup_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (x : IdeleGroup (𝓞 K) K) :
    x ∈ kummerIdeleSubgroup S n ↔
      (∀ v ∈ S, v.ideleFiniteCoord x ∈ (powMonoidHom n).range) ∧
      (∀ w : InfinitePlace K, w.ideleInfiniteCoord x ∈ (powMonoidHom n).range) ∧
      ∀ v ∉ S, Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  simp [kummerIdeleSubgroup, Subgroup.mem_iInf,
    HeightOneSpectrum.adicCompletionIntegers.mem_units_iff_valued_eq_one, and_assoc]

/-- At exponent one the Kummer subgroup is the full group of `S`-ideles. -/
theorem mem_kummerIdeleSubgroup_one_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (x : IdeleGroup (𝓞 K) K) :
    x ∈ kummerIdeleSubgroup S 1 ↔
      ∀ v ∉ S, Valued.v (v.ideleFiniteCoord x : v.adicCompletion K) = 1 := by
  simp

/-- Every Kummer idele is an `S`-idele. -/
theorem kummerIdeleSubgroup_le_one (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    kummerIdeleSubgroup S n ≤ kummerIdeleSubgroup S 1 := by
  intro x hx
  exact (mem_kummerIdeleSubgroup_one_iff S x).mpr
    ((mem_kummerIdeleSubgroup_iff S n x).mp hx).2.2

private abbrev LocalPowerClasses (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :=
  (∀ v : S, (v.1.adicCompletion K)ˣ ⧸ (powMonoidHom n).range) ×
    (∀ w : InfinitePlace K, w.Completionˣ ⧸ (powMonoidHom n).range)

private def localPowerClassMap (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    kummerIdeleSubgroup S 1 →* LocalPowerClasses S n where
  toFun x := (fun v => QuotientGroup.mk (v.1.ideleFiniteCoord x.1),
    fun w => QuotientGroup.mk (w.ideleInfiniteCoord x.1))
  map_one' := by ext <;> simp
  map_mul' x y := by ext <;> simp [QuotientGroup.mk_mul]

private theorem localPowerClassMap_apply (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (x : kummerIdeleSubgroup S 1) :
    localPowerClassMap S n x = (fun v => QuotientGroup.mk (v.1.ideleFiniteCoord x.1),
      fun w => QuotientGroup.mk (w.ideleInfiniteCoord x.1)) :=
  (rfl)

private theorem localPowerClassMap_surjective (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Function.Surjective (localPowerClassMap S n) := by
  classical
  rintro ⟨xf, xi⟩
  choose z hz using fun v : S => QuotientGroup.mk_surjective (xf v)
  choose zi hzi using fun w : InfinitePlace K => QuotientGroup.mk_surjective (xi w)
  let zf (v : HeightOneSpectrum (𝓞 K)) : (v.adicCompletion K)ˣ :=
    if hv : v ∈ S then z ⟨v, hv⟩ else 1
  have hzfu : ∀ᶠ v in Filter.cofinite, zf v ∈ (v.adicCompletionIntegers K).units :=
    S.eventually_cofinite_notMem.mono fun v hv => by simp [zf, hv]
  let x := GlobalNumberFields.ideleOfUnits zi zf hzfu
  have hx : x ∈ kummerIdeleSubgroup S 1 := by
    rw [mem_kummerIdeleSubgroup_one_iff]
    intro v hv
    simp [x, zf, hv]
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Prod.ext
  · funext v
    simpa [localPowerClassMap, x, zf, v.2] using hz v
  · funext w
    simpa [localPowerClassMap, x] using hzi w

private theorem ker_localPowerClassMap (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    (localPowerClassMap S n).ker =
      (kummerIdeleSubgroup S n).subgroupOf (kummerIdeleSubgroup S 1) := by
  ext x
  have hx := (mem_kummerIdeleSubgroup_one_iff S x.1).mp x.2
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  rw [localPowerClassMap_apply]
  simp only [mem_kummerIdeleSubgroup_iff, Prod.ext_iff, funext_iff, Prod.fst_one, Prod.snd_one,
    Pi.one_apply, QuotientGroup.eq_one_iff]
  constructor
  · rintro ⟨hf, hi⟩
    exact ⟨fun v hv => hf ⟨v, hv⟩, hi, hx⟩
  · rintro ⟨hf, hi, _⟩
    exact ⟨fun v => hf v.1 v.2, hi⟩

/-- The relative index of the Kummer subgroup in the `S`-ideles is the product of the finite
and infinite local power-class counts. As usual, `Nat.card` and the index are zero for an
infinite quotient. -/
theorem relIndex_kummerIdeleSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    (kummerIdeleSubgroup S n).relIndex (kummerIdeleSubgroup S 1) =
      (∏ v : S, Nat.card ((v.1.adicCompletion K)ˣ ⧸ (powMonoidHom n).range)) *
        ∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸ (powMonoidHom n).range) := by
  rw [Subgroup.relIndex, ← ker_localPowerClassMap]
  calc
    _ = Nat.card (LocalPowerClasses S n) := Nat.card_congr
      (QuotientGroup.quotientKerEquivOfSurjective (localPowerClassMap S n)
        (localPowerClassMap_surjective S n)).toEquiv
    _ = _ := by simp [Nat.card_prod, Nat.card_pi, LocalPowerClasses]

/-- The image of the Kummer idele subgroup in the idele class group. -/
def kummerIdeleClassSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ) :
    Subgroup (IdeleClassGroup (𝓞 K) K) :=
  (kummerIdeleSubgroup S n).map (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K))

/-- An idele class lies in the Kummer idele class subgroup exactly when it has a Kummer idele
representative. -/
@[simp]
theorem mem_kummerIdeleClassSubgroup_iff (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (c : IdeleClassGroup (𝓞 K) K) :
    c ∈ kummerIdeleClassSubgroup S n ↔
      ∃ x ∈ kummerIdeleSubgroup S n, (x : IdeleClassGroup (𝓞 K) K) = c :=
  (Iff.rfl)

/-- If the classes of `S` generate the ideal class group, the index of the Kummer idele class
subgroup divides the product of the local power-class counts. -/
theorem index_kummerIdeleClassSubgroup_dvd (S : Finset (HeightOneSpectrum (𝓞 K))) (n : ℕ)
    (hS : Subgroup.closure
      (HeightOneSpectrum.classGroupMk (R := 𝓞 K) '' (S : Set (HeightOneSpectrum (𝓞 K)))) = ⊤) :
    (kummerIdeleClassSubgroup S n).index ∣
      (∏ v : S, Nat.card ((v.1.adicCompletion K)ˣ ⧸ (powMonoidHom n).range)) *
        ∏ w : InfinitePlace K, Nat.card (w.Completionˣ ⧸ (powMonoidHom n).range) := by
  let f : kummerIdeleSubgroup S 1 →* IdeleClassGroup (𝓞 K) K :=
    (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 K) K)).comp
      (kummerIdeleSubgroup S 1).subtype
  have hf : Function.Surjective f := by
    intro c
    obtain ⟨x, hx, hc⟩ := IdeleClassGroup.exists_valued_ideleFiniteCoord_eq_one_and_mk_eq hS c
    exact ⟨⟨x, (mem_kummerIdeleSubgroup_one_iff S x).mpr hx⟩, hc⟩
  have hmap : ((kummerIdeleSubgroup S n).subgroupOf (kummerIdeleSubgroup S 1)).map f =
      kummerIdeleClassSubgroup S n := by
    dsimp only [f]
    rw [kummerIdeleClassSubgroup, ← Subgroup.map_map, Subgroup.subgroupOf_map_subtype]
    exact congrArg (Subgroup.map _) (inf_eq_left.mpr (kummerIdeleSubgroup_le_one S n))
  rw [← relIndex_kummerIdeleSubgroup, Subgroup.relIndex, ← hmap]
  exact Subgroup.index_map_dvd _ hf

end TauCeti.ClassFieldTheory
