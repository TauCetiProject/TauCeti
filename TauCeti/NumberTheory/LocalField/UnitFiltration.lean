/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NormalizedValuation

/-!
# The unit filtration of a nonarchimedean local field

For a nonarchimedean local field `K` this file defines the unit filtration

`TauCeti.unitFiltration K i : Subgroup Kˣ`,

the subgroup `U(K,i)` of those units of `𝒪[K]` that are congruent to `1` modulo `𝓂[K] ^ i`.
The indexing is by natural numbers, and the depth-zero case is part of the definition rather
than a separate convention: `𝓂[K] ^ 0 = ⊤`, so `U(K,0)` is the whole image of `𝒪[K]ˣ` in `Kˣ`,
while `U(K,i) = 1 + 𝓂[K] ^ i` for `i ≥ 1`.

The filtration is the standard tool for resolving the multiplicative structure of `K` near `1`.
Its steps are a neighbourhood basis of `1` in `Kˣ`, so they carry the topology of the unit group
and reduce statements about `Kˣ` to statements about the finite quotients `𝒪[K]ˣ ⧸ U(K,i)`. Its
successive quotients are where ramification is measured: `U(K,0) ⧸ U(K,1)` is the multiplicative
group of the residue field and `U(K,i) ⧸ U(K,i+1)` is its additive group for `i ≥ 1`. Later work
uses the filtration in that role, through its graded pieces, its stability under the Galois
action on a finite extension, and its behaviour under a field embedding.

## Main definitions

* `TauCeti.unitFiltration`: the unit filtration `U(K,i)` of a nonarchimedean local field, as a
  subgroup of `Kˣ`.

## Main results

* `TauCeti.mem_unitFiltration_iff_exists` and `TauCeti.mem_unitFiltration_succ_congr`: the
  congruence form of membership, `x ≡ 1 mod 𝓂[K] ^ i` inside `𝒪[K]`.
* `TauCeti.mem_unitFiltration_iff_valuation_le` and
  `TauCeti.mem_unitFiltration_succ_valuation`: the valuation form of membership, an
  inequality on `x - 1` measured against a uniformizer. At positive depth the inequality alone
  already forces `x` to be a unit of `𝒪[K]`.
* `TauCeti.unitFiltration_zero` and `TauCeti.unitFiltration_one`: the two shallow steps are
  Mathlib's `ValuationSubring.unitGroup` and `ValuationSubring.principalUnitGroup`.
* `TauCeti.unitFiltration_antitone`: the filtration is decreasing.
* `TauCeti.iInf_unitFiltration`: the filtration separates points, `⨅ i, U(K,i) = ⊥`.
* `TauCeti.isOpen_unitFiltration`, `TauCeti.isCompact_unitFiltration` and
  `TauCeti.hasBasis_nhds_one_unitFiltration`: every `U(K,i)` is an open compact subgroup of
  `Kˣ`, and the family is a neighbourhood basis of `1`.

## Implementation notes

Two membership criteria are maintained. The congruence form is definitional and is the one used
for the algebraic statements; the valuation form is stated against an arbitrary uniformizer `π`
of `K`, which simultaneously records that the criterion does not depend on the choice of `π`.

The valuation appearing in the criteria is Mathlib's multiplicative `ValuativeRel.valuation K`,
for which greater depth means a smaller value and for which `0` is the smallest value; this is
what lets `1` belong to every step. The additively normalized `TauCeti.normalizedValuation` is
used in the proofs, where an integer depth is needed.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §2.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §§3–5.
-/

public section
noncomputable section

open Filter Topology ValuativeRel IsNonarchimedeanLocalField

namespace TauCeti

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

-- Provenance: the declaration sequence follows the human-authored specification in
-- `TauCetiRoadmap/LocalFieldsRamification/Suggested.lean`, and the additive normalization of the
-- valuation is the convention fixed in that directory's `README.md`.
variable (K) in
/-- The unit filtration `U(K,i)` of a nonarchimedean local field `K`: the units of `𝒪[K]` that
are congruent to `1` modulo `𝓂[K] ^ i`, viewed inside `Kˣ`. The depth-zero step is included in
the definition through `𝓂[K] ^ 0 = ⊤`, so that `U(K,0)` is the image of `𝒪[K]ˣ`, while
`U(K,i) = 1 + 𝓂[K] ^ i` for `i ≥ 1`. -/
def unitFiltration (i : ℕ) : Subgroup Kˣ :=
  ((Units.map (Ideal.Quotient.mk (𝓂[K] ^ i)).toMonoidHom).ker).map
    (Units.map (Subring.subtype 𝒪[K]).toMonoidHom)

/-- Membership in the unit filtration, congruence form: `x` is the image of a unit `u` of `𝒪[K]`
with `u ≡ 1 mod 𝓂[K] ^ i`. -/
theorem mem_unitFiltration_iff_exists {i : ℕ} {x : Kˣ} :
    x ∈ unitFiltration K i ↔
      ∃ u : 𝒪[K]ˣ, (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ i ∧ ((u : 𝒪[K]) : K) = (x : K) := by
  simp only [unitFiltration, Subgroup.mem_map, MonoidHom.mem_ker, Units.ext_iff, Units.coe_map,
    Units.val_one, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Subring.coe_subtype,
    ← (Ideal.Quotient.mk (𝓂[K] ^ i)).map_one, Ideal.Quotient.mk_eq_mk_iff_sub_mem]

/-- Membership in the unit filtration at positive depth for a unit of `𝒪[K]`: the congruence
`u ≡ 1 mod 𝓂[K] ^ (i + 1)`. The general-depth statement is `mem_unitFiltration_iff_exists`.

This is deliberately not `@[simp]`: `simp` rewrites `RingHom.toMonoidHom` to the bundled
coercion, so the roadmap-fixed left-hand side is not in simp-normal form and `simpNF` rejects
the attribute. -/
theorem mem_unitFiltration_succ_congr (i : ℕ) (u : 𝒪[K]ˣ) :
    Units.map (Subring.subtype 𝒪[K]).toMonoidHom u ∈ unitFiltration K (i + 1) ↔
      (u : 𝒪[K]) - 1 ∈ 𝓂[K] ^ (i + 1) := by
  rw [mem_unitFiltration_iff_exists]
  refine ⟨?_, fun h ↦ ⟨u, h, rfl⟩⟩
  rintro ⟨w, hw, hwu⟩
  rwa [Units.ext (Subtype.coe_injective hwu : (w : 𝒪[K]) = (u : 𝒪[K]))] at hw

/-- The depth-zero step of the unit filtration is the image of `𝒪[K]ˣ` in `Kˣ`, that is, the set
of units of valuation one. -/
theorem mem_unitFiltration_zero (x : Kˣ) :
    x ∈ unitFiltration K 0 ↔ valuation K (x : K) = 1 := by
  rw [mem_unitFiltration_iff_exists]
  refine ⟨?_, fun hx ↦ ?_⟩
  · rintro ⟨u, -, hu⟩
    rw [← hu]
    exact (Valuation.integer.integers (valuation K)).valuation_unit u
  · have hx' : (x : K) ∈ 𝒪[K] := (Valuation.mem_integer_iff (valuation K) (x : K)).mpr hx.le
    have hu : IsUnit (⟨(x : K), hx'⟩ : 𝒪[K]) :=
      (Valuation.integer.integers (valuation K)).isUnit_of_one' hx
    exact ⟨hu.unit, by simp, by rw [hu.unit_spec]⟩

/-- The depth-zero step of the unit filtration is Mathlib's unit group of the valuation subring
of `K`. -/
@[simp]
theorem unitFiltration_zero :
    unitFiltration K 0 = (valuation K).valuationSubring.unitGroup :=
  Subgroup.ext fun x ↦ (mem_unitFiltration_zero x).trans
    (Valuation.mem_unitGroup_iff (v := valuation K) (x := x)).symm

/-- Membership in the unit filtration, valuation form: an inequality on `x - 1` measured against
an arbitrary uniformizer `π` of `K`. The right-hand side is therefore independent of the choice
of `π`. -/
theorem mem_unitFiltration_iff_valuation_le {i : ℕ} {x : Kˣ} {π : 𝒪[K]} (hπ : Irreducible π) :
    x ∈ unitFiltration K i ↔
      valuation K (x : K) = 1 ∧ valuation K ((x : K) - 1) ≤ valuation K (π : K) ^ i := by
  have hmem : ∀ y : 𝒪[K], y ∈ 𝓂[K] ^ i ↔ valuation K (y : K) ≤ valuation K (π : K) ^ i :=
    fun y ↦ Set.ext_iff.mp (hπ.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow (valuation K) i) y
  rw [mem_unitFiltration_iff_exists]
  constructor
  · rintro ⟨u, hu, hux⟩
    rw [← hux]
    exact ⟨(Valuation.integer.integers (valuation K)).valuation_unit u,
      by simpa using (hmem _).mp hu⟩
  · rintro ⟨hx, hx1⟩
    have hx' : (x : K) ∈ 𝒪[K] := (Valuation.mem_integer_iff (valuation K) (x : K)).mpr hx.le
    have hu : IsUnit (⟨(x : K), hx'⟩ : 𝒪[K]) :=
      (Valuation.integer.integers (valuation K)).isUnit_of_one' hx
    refine ⟨hu.unit, (hmem _).mpr ?_, by rw [hu.unit_spec]⟩
    simpa [hu.unit_spec] using hx1

/-- Membership in the unit filtration at positive depth, valuation form: the inequality on
`x - 1` already forces `x` to be a unit of `𝒪[K]`, so no further hypothesis is needed. -/
theorem mem_unitFiltration_succ_valuation (i : ℕ) (x : Kˣ) (π : 𝒪[K]) (hπ : Irreducible π) :
    x ∈ unitFiltration K (i + 1) ↔
      valuation K ((x : K) - 1) ≤ valuation K ((π : K) ^ (i + 1)) := by
  have hπ1 : valuation K (π : K) ^ (i + 1) < 1 :=
    pow_lt_one₀ zero_le (Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ)
      i.succ_ne_zero
  rw [mem_unitFiltration_iff_valuation_le hπ, map_pow, and_iff_right_iff_imp]
  intro hx1
  have h : valuation K ((x : K) - 1 + 1) = 1 := by
    rw [add_comm]
    exact (valuation K).map_one_add_of_lt (hx1.trans_lt hπ1)
  simpa using h

/-- The depth-one step of the unit filtration is Mathlib's principal unit group of the valuation
subring of `K`. -/
@[simp]
theorem unitFiltration_one :
    unitFiltration K 1 = (valuation K).valuationSubring.principalUnitGroup := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  -- Being divisible by `π` is having valuation less than one, which is Mathlib's criterion for
  -- the principal unit group, transported along the equivalence of the two valuations.
  have hdvd : ∀ y : K, valuation K y ≤ valuation K (π : K) ↔ valuation K y < 1 := by
    refine fun y ↦ ⟨fun h ↦
      h.trans_lt (Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ), fun h ↦ ?_⟩
    have hy : y ∈ 𝒪[K] := (Valuation.mem_integer_iff (valuation K) y).mpr h.le
    have hmem : (⟨y, hy⟩ : 𝒪[K]) ∈ 𝓂[K] := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
      exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mpr h
    have hset := Set.ext_iff.mp (hπ.maximalIdeal_eq_setOfPred_le_v_coe (valuation K)) ⟨y, hy⟩
    simpa using hset.mp hmem
  refine Subgroup.ext fun x ↦ ?_
  rw [mem_unitFiltration_succ_valuation 0 x π hπ, ValuationSubring.mem_principalUnitGroup_iff,
    ← (Valuation.isEquiv_valuation_valuationSubring (valuation K)).lt_one_iff_lt_one, zero_add,
    pow_one]
  exact hdvd _

/-- The unit filtration is decreasing. -/
theorem unitFiltration_antitone : Antitone (unitFiltration K) := by
  intro i j hij x hx
  rw [mem_unitFiltration_iff_exists] at hx ⊢
  obtain ⟨u, hu, hux⟩ := hx
  exact ⟨u, Ideal.pow_le_pow_right hij hu, hux⟩

/-- The unit filtration separates points: an element lying in every step is `1`. -/
theorem iInf_unitFiltration : ⨅ i, unitFiltration K i = ⊥ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  simp only [Subgroup.mem_iInf] at hx
  rw [Subgroup.mem_bot, ← Units.val_eq_one, ← sub_eq_zero]
  by_contra h
  obtain ⟨i, hi⟩ := exists_pow_lt₀ (Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ)
      (Units.mk0 (valuation K ((x : K) - 1)) (by simpa using h))
  exact absurd ((mem_unitFiltration_iff_valuation_le hπ).mp (hx i)).2 hi.not_ge

section Topology

/-- Each step of the unit filtration is a neighbourhood of `1` in `Kˣ`. -/
theorem unitFiltration_mem_nhds_one (i : ℕ) :
    (unitFiltration K i : Set Kˣ) ∈ 𝓝 (1 : Kˣ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  have hπ0 : valuation K (π : K) ≠ 0 := by
    simpa using (Valuation.integer.v_irreducible_pos (v := valuation K) hπ).ne'
  have hball : {y : K | valuation K (y - 1) < valuation K (π : K) ^ (i + 1)} ∈ 𝓝 (1 : K) := by
    simpa using (IsValuativeTopology.hasBasis_nhds (1 : K)).mem_of_mem
      (i := (Units.mk0 _ hπ0) ^ (i + 1)) trivial
  -- Continuity of `Units.val` at `1`, read as a statement about filter membership.
  have hpre : (Units.val ⁻¹' {y : K | valuation K (y - 1) < valuation K (π : K) ^ (i + 1)})
      ∈ 𝓝 (1 : Kˣ) :=
    Units.continuous_val.continuousAt (by simpa using hball)
  refine mem_of_superset hpre fun x hx ↦ ?_
  exact unitFiltration_antitone i.le_succ
    ((mem_unitFiltration_succ_valuation i x π hπ).mpr (by simpa using hx.le))

/-- Each step of the unit filtration is an open subgroup of `Kˣ`. -/
theorem isOpen_unitFiltration (i : ℕ) : IsOpen (unitFiltration K i : Set Kˣ) :=
  (unitFiltration K i).isOpen_of_mem_nhds (unitFiltration_mem_nhds_one i)

/-- The image in `K` of the depth-zero step of the unit filtration. -/
private theorem image_unitFiltration_zero :
    Units.val '' (unitFiltration K 0 : Set Kˣ) = {y : K | valuation K y = 1} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (mem_unitFiltration_zero x).mp hx
  · intro hy
    have hy0 : y ≠ 0 := fun h ↦ by simp [h] at hy
    exact ⟨Units.mk0 y hy0, (mem_unitFiltration_zero _).mpr (by simpa using hy), rfl⟩

/-- The image in `K` of a positive-depth step of the unit filtration. -/
private theorem image_unitFiltration_succ {i : ℕ} {π : 𝒪[K]} (hπ : Irreducible π) :
    Units.val '' (unitFiltration K (i + 1) : Set Kˣ)
      = (1 + ·) '' {z : K | valuation K z ≤ valuation K (π : K) ^ (i + 1)} := by
  have hπ1 : valuation K (π : K) ^ (i + 1) < 1 :=
    pow_lt_one₀ zero_le (Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ)
      i.succ_ne_zero
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨(x : K) - 1, by simpa using (mem_unitFiltration_succ_valuation i x π hπ).mp hx,
      by ring⟩
  · rintro ⟨z, hz, rfl⟩
    have hval : valuation K (1 + z) = 1 := (valuation K).map_one_add_of_lt (hz.trans_lt hπ1)
    have h0 : (1 : K) + z ≠ 0 := fun h ↦ by simp [h] at hval
    refine ⟨Units.mk0 _ h0, (mem_unitFiltration_succ_valuation i _ π hπ).mpr ?_, rfl⟩
    simpa using hz

/-- Each step of the unit filtration is a compact subset of `Kˣ`. -/
theorem isCompact_unitFiltration (i : ℕ) : IsCompact (unitFiltration K i : Set Kˣ) := by
  rw [Units.isEmbedding_val₀.isCompact_iff]
  match i with
  | 0 =>
    have hdiff : {y : K | valuation K y = 1}
        = {y : K | valuation K y ≤ 1} \ {y : K | valuation K y < 1} := by
      ext y; simp [le_antisymm_iff, and_comm]
    have hset : {y : K | valuation K y < 1}
        = ((Valuation.ltAddSubgroup (valuation K) 1 : AddSubgroup K) : Set K) := by
      ext y; simp
    have hopen : IsOpen {y : K | valuation K y < 1} := by
      rw [hset]
      refine (Valuation.ltAddSubgroup (valuation K) 1).isOpen_of_mem_nhds (g := 0) ?_
      rw [← hset]
      simpa using (IsValuativeTopology.hasBasis_nhds_zero K).mem_of_mem (i := 1) trivial
    rw [image_unitFiltration_zero, hdiff]
    exact (isCompact_closedBall K 1).diff hopen
  | i + 1 =>
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
    rw [image_unitFiltration_succ hπ]
    exact (isCompact_closedBall K _).image (by fun_prop)

/-- The unit filtration is a neighbourhood basis of `1` in `Kˣ`. -/
theorem hasBasis_nhds_one_unitFiltration :
    (𝓝 (1 : Kˣ)).HasBasis (fun _ : ℕ ↦ True) fun i ↦ (unitFiltration K i : Set Kˣ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (R := 𝒪[K])
  refine ⟨fun s ↦ ⟨fun hs ↦ ?_, ?_⟩⟩
  · rw [Units.isEmbedding_val₀.isInducing.nhds_eq_comap, Filter.mem_comap] at hs
    obtain ⟨t, ht, hts⟩ := hs
    obtain ⟨γ, -, hγ⟩ := (IsValuativeTopology.hasBasis_nhds (1 : K)).mem_iff.mp
      (by simpa using ht)
    obtain ⟨i, hi⟩ :=
      exists_pow_lt₀ (Valuation.integer.v_irreducible_lt_one (v := valuation K) hπ) γ
    refine ⟨i, trivial, fun x hx ↦ hts ?_⟩
    exact hγ (((mem_unitFiltration_iff_valuation_le hπ).mp hx).2.trans_lt hi)
  · rintro ⟨i, -, hi⟩
    exact mem_of_superset (unitFiltration_mem_nhds_one i) hi

end Topology

end TauCeti
