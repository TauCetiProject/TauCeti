/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Range
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.ClassQuotient
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Ray.OpenSubgroup
import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Open
import TauCeti.NumberTheory.NumberField.InfinitePlace.Completion.Norm
import TauCeti.RingTheory.DedekindDomain.AdicValuation.ValuativeRel

/-!
# Openness of idele norms and finite index of idele-class norms

Let `L/K` be a finite extension of number fields. The idele norm group `N_{L/K}(I_L)` contains an
idele congruence subgroup of `I_K` (`exists_ideleCongruenceSubgroup_le_range_ideleNormMap`), so it
is open (`isOpen_range_ideleNormMap`). Its image `N_{L/K}(C_L)` in the idele class group therefore
contains a ray subgroup (`exists_raySubgroup_le_range_ideleClassNormMap`): the conductor of `L/K`
exists. Hence `N_{L/K}(C_L)` is open (`isOpen_range_ideleClassNormMap`) and, the ray class groups
being finite, of finite index in `C_K` (`finiteIndex_range_ideleClassNormMap`). No Galois
hypothesis is needed.

The modulus is read off the placewise norm criterion `mem_range_ideleNormMap_iff`. At a finite
place unramified in `L`, every unit of `K_v` is a norm from `K_v ⊗[K] L`
(`TauCeti.exists_unit_preimages_of_isUnramifiedAt`). At each of the finitely many ramified
places, and at the infinite places, an `[L : K]`-th power is a norm, and the `[L : K]`-th powers
contain the units congruent to one to a sufficient level (`TauCeti.isOpen_range_powMonoidHom`), the
positive real numbers and all complex numbers. A modulus deep enough at the ramified places and
divisible by every real place therefore works.

These are the topological facts about norm groups through which the global class-field
correspondence is stated on the open subgroups of finite index of `C_K`.

## Main results

* `TauCeti.GlobalNumberFields.exists_ideleCongruenceSubgroup_le_range_ideleNormMap`: the idele
  norm group contains an idele congruence subgroup.
* `TauCeti.GlobalNumberFields.isOpen_range_ideleNormMap`: the idele norm group is open.
* `TauCeti.GlobalNumberFields.exists_raySubgroup_le_range_ideleClassNormMap`: the idele-class norm
  group contains a ray subgroup.
* `TauCeti.GlobalNumberFields.isOpen_range_ideleClassNormMap` and
  `TauCeti.GlobalNumberFields.finiteIndex_range_ideleClassNormMap`: the idele-class norm group is
  open and of finite index.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §§1 and 2.
-/

public section
noncomputable section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField NumberField.InfinitePlace
open scoped TensorProduct AdicCompletionExtension

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The idele norm group contains an idele congruence subgroup.** For a finite extension `L/K`
of number fields there is a modulus `𝔪` of `K` such that every idele of `K` congruent to one
modulo `𝔪`, and a unit at every finite place, is the norm of an idele of `L`. -/
theorem exists_ideleCongruenceSubgroup_le_range_ideleNormMap :
    ∃ 𝔪 : Modulus K, ideleCongruenceSubgroup 𝔪 ≤ (ideleNormMap K L).toMonoidHom.range := by
  classical
  set n := Module.finrank K L with hn_def
  have hn : n ≠ 0 := Module.finrank_pos.ne'
  -- The finite set `S` of finite places of `K` ramified in `L`.
  obtain ⟨S, hS⟩ : ∃ S : Finset (HeightOneSpectrum (𝓞 K)), ∀ v ∉ S,
      ∀ w : {w : HeightOneSpectrum (𝓞 L) // w.asIdeal.LiesOver v.asIdeal},
        Algebra.IsUnramifiedAt (𝓞 K) w.1.asIdeal := by
    have hfin := Filter.eventually_cofinite.mp (eventually_isUnramifiedAt_liesOver K L)
    exact ⟨hfin.toFinset, fun v hv ↦ by simpa using hv⟩
  -- At each finite place, the `n`-th powers contain a step of the unit filtration.
  have hdeep (v : HeightOneSpectrum (𝓞 K)) : ∃ m : ℕ,
      unitFiltration (v.adicCompletion K) m ≤
        (powMonoidHom n : (v.adicCompletion K)ˣ →* (v.adicCompletion K)ˣ).range := by
    let _ : Finite (𝓞 K ⧸ v.asIdeal) := Ring.HasFiniteQuotients.finiteQuotient v.ne_bot
    obtain ⟨m, -, hm⟩ := hasBasis_nhds_one_unitFiltration.mem_iff.mp <|
      (isOpen_range_powMonoidHom ((Nat.cast_ne_zero (R := v.adicCompletion K)).2 hn)).mem_nhds
        (Subgroup.one_mem _)
    exact ⟨m, hm⟩
  choose m hm using hdeep
  -- An `n`-th power of a local unit is a local norm.
  have hpow := Algebra.range_powMonoidHom_le_range_normUnits_baseChange K L
  -- The modulus `∏_{v ∈ S} v ^ m v`, divisible by every real place.
  let 𝔪 : Modulus K :=
    { finitePart := ∏ v ∈ S, v.asIdeal ^ m v
      finitePart_ne_bot := by
        rw [← Ideal.zero_eq_bot, Finset.prod_ne_zero_iff]
        exact fun v _ ↦ pow_ne_zero _ (by simpa using v.ne_bot)
      infinitePart := (narrowModulus K).infinitePart }
  refine ⟨𝔪, fun x hx ↦ (mem_range_ideleNormMap_iff K L x).mpr ⟨fun v ↦ ?_, fun w ↦ ?_⟩⟩
  · by_cases hv : v ∈ S
    · -- A ramified place: the coordinate lies deep in the unit filtration, so it is a power.
      have hexp : m v ≤ 𝔪.exponent v :=
        (Modulus.pow_dvd_finitePart_iff_le_exponent 𝔪 v).mp (Finset.dvd_prod_of_mem _ hv)
      exact hpow _ (hm v (unitFiltration_antitone hexp
        (ideleCongruenceSubgroup.ideleFiniteCoord_mem_unitFiltration hx v)))
    · -- An unramified place: the coordinate is a unit, and units are norms there.
      obtain ⟨P, hP, hPv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral
        (S := 𝓞 L) v.asIdeal
      have hP0 := Ideal.ne_bot_of_mem_primesOver v.ne_bot ⟨hP.isPrime, hPv⟩
      obtain ⟨u, hu, -⟩ := exists_unit_preimages_of_isUnramifiedAt K L v _
        (ideleCongruenceSubgroup.valued_ideleFiniteCoord_eq_one hx v)
        ⟨⟨⟨P, hP.isPrime, hP0⟩, hPv⟩, hS v hv _⟩
      exact (mem_range_normUnits_adicCompletion_iff K L v _).mpr ⟨u, hu⟩
  · -- An infinite place: the coordinate is positive at a real place, hence a power.
    exact hpow _ (Completion.mem_range_powMonoidHom hn _ fun hw ↦
      ideleCongruenceSubgroup.extensionEmbeddingOfIsReal_pos hx (w := ⟨w, hw⟩)
        (mem_narrowModulus_infinitePart ⟨w, hw⟩))

/-- **The idele norm group is open.** -/
theorem isOpen_range_ideleNormMap :
    IsOpen ((ideleNormMap K L).toMonoidHom.range : Set (IdeleGroup (𝓞 K) K)) :=
  (isOpen_iff_exists_ideleCongruenceSubgroup_le _).mpr
    (exists_ideleCongruenceSubgroup_le_range_ideleNormMap K L)

/-- **The idele-class norm group contains a ray subgroup.** For a finite extension `L/K` of number
fields there is a modulus `𝔪` of `K` whose ray subgroup lies in `N_{L/K}(C_L)`; classically, the
conductor of `L/K` exists. -/
theorem exists_raySubgroup_le_range_ideleClassNormMap :
    ∃ 𝔪 : Modulus K, raySubgroup 𝔪 ≤ (ideleClassNormMap K L).toMonoidHom.range := by
  obtain ⟨𝔪, h𝔪⟩ := exists_ideleCongruenceSubgroup_le_range_ideleNormMap K L
  refine ⟨𝔪, fun c hc ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := mem_raySubgroup_iff.mp hc
  obtain ⟨y, hy⟩ := h𝔪 hx
  rw [ContinuousMonoidHom.coe_toMonoidHom] at hy
  exact ⟨(y : IdeleClassGroup (𝓞 L) L), (ideleClassNormMap_mk y).trans (congrArg _ hy)⟩

/-- **The idele-class norm group is open.** -/
theorem isOpen_range_ideleClassNormMap :
    IsOpen ((ideleClassNormMap K L).toMonoidHom.range : Set (IdeleClassGroup (𝓞 K) K)) :=
  (isOpen_iff_exists_raySubgroup_le _).mpr (exists_raySubgroup_le_range_ideleClassNormMap K L)

/-- **The idele-class norm group has finite index**, since it contains a ray subgroup, whose index
is the order of the finite ray class group. -/
theorem finiteIndex_range_ideleClassNormMap :
    (ideleClassNormMap K L).toMonoidHom.range.FiniteIndex := by
  obtain ⟨𝔪, h𝔪⟩ := exists_raySubgroup_le_range_ideleClassNormMap K L
  exact Subgroup.finiteIndex_of_le h𝔪

end TauCeti.GlobalNumberFields
