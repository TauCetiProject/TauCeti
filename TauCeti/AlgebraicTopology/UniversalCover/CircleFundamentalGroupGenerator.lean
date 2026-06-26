/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Algebra.Group.Int.TypeTags
public import TauCeti.AlgebraicTopology.UniversalCover.CircleFundamentalGroup

/-!
# Generators for fundamental groups of real additive circles

The file `TauCeti.AlgebraicTopology.UniversalCover.CircleFundamentalGroup` identifies
the fundamental group of any real additive circle `AddCircle p`, for `p ≠ 0`, with
`Multiplicative ℤ`. This file packages the corresponding positive generator of the
fundamental group and records the elementary cyclic-group API following from that identification.

The generator is defined as the inverse image of `Multiplicative.ofAdd 1` under
`AddCircle.fundamentalGroupMulEquiv`, for a chosen lift of the basepoint. Its powers are
therefore exactly the loop classes whose monodromy translates the chosen lift by the
corresponding integer multiple of the period. In particular, it has infinite order and its
integer powers generate the whole fundamental group.

## Main declarations

* `TauCeti.AddCircle.fundamentalGroupGenerator`: the positive generator of
  `FundamentalGroup (AddCircle p) x` for a chosen lift of `x`.
* `TauCeti.UnitAddCircle.fundamentalGroupGenerator`: the positive generator of
  `FundamentalGroup UnitAddCircle 0`.
* `TauCeti.AddCircle.fundamentalGroupGenerator_zpow`: integer powers of the generator
  correspond to integers under `fundamentalGroupMulEquiv`.
* `TauCeti.AddCircle.fundamentalGroupGenerator_zpowers_eq_top`: the generator's cyclic
  subgroup is the whole fundamental group.
* `TauCeti.AddCircle.isCyclic_fundamentalGroup`: `π₁(AddCircle p, x)` is cyclic.

## References

This advances the Tau Ceti universal-covers roadmap, Stage 4 target 12 (`π₁(S¹) ≅ ℤ`,
`TauCetiRoadmap/UniversalCovers/README.md`), by adding the generator API downstream of the
existing equivalence `AddCircle.fundamentalGroupMulEquiv`.
-/

public section

namespace TauCeti

namespace AddCircle

/-- The positive generator of `π₁(AddCircle p, x)`, for `p ≠ 0` and a chosen lift of `x`,
defined as the loop class corresponding to `1 : ℤ` under `AddCircle.fundamentalGroupMulEquiv`. -/
noncomputable def fundamentalGroupGenerator {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) : FundamentalGroup (AddCircle p) x :=
  (fundamentalGroupMulEquiv p hp e).symm (Multiplicative.ofAdd (1 : ℤ))

/-- The chosen generator maps to `Multiplicative.ofAdd 1` under
`AddCircle.fundamentalGroupMulEquiv`. -/
@[simp]
lemma fundamentalGroupMulEquiv_generator {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) :
    fundamentalGroupMulEquiv p hp e (fundamentalGroupGenerator hp e) =
      Multiplicative.ofAdd (1 : ℤ) := by
  simp [fundamentalGroupGenerator]

/-- Integer powers of the chosen generator correspond to the same integers under the
fundamental-group equivalence with `Multiplicative ℤ`. -/
@[simp]
lemma fundamentalGroupGenerator_zpow {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (n : ℤ) :
    fundamentalGroupGenerator hp e ^ n =
      (fundamentalGroupMulEquiv p hp e).symm (Multiplicative.ofAdd n) := by
  apply (fundamentalGroupMulEquiv p hp e).injective
  calc
    fundamentalGroupMulEquiv p hp e (fundamentalGroupGenerator hp e ^ n) =
        fundamentalGroupMulEquiv p hp e (fundamentalGroupGenerator hp e) ^ n := map_zpow _ _ _
    _ = Multiplicative.ofAdd (1 : ℤ) ^ n := by rw [fundamentalGroupMulEquiv_generator]
    _ = Multiplicative.ofAdd n := by
      simpa using (Int.ofAdd_mul (1 : ℤ) n).symm
    _ = fundamentalGroupMulEquiv p hp e
        ((fundamentalGroupMulEquiv p hp e).symm (Multiplicative.ofAdd n)) := by
      rw [(fundamentalGroupMulEquiv p hp e).apply_symm_apply]

/-- Natural powers of the chosen generator correspond to nonnegative integers. -/
@[simp]
lemma fundamentalGroupGenerator_pow {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (n : ℕ) :
    fundamentalGroupGenerator hp e ^ n =
      (fundamentalGroupMulEquiv p hp e).symm (Multiplicative.ofAdd (n : ℤ)) := by
  simpa using fundamentalGroupGenerator_zpow hp e (n : ℤ)

/-- The chosen generator is nontrivial. -/
@[simp]
lemma fundamentalGroupGenerator_ne_one {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) : fundamentalGroupGenerator hp e ≠ 1 := by
  intro h
  have hmap : Multiplicative.ofAdd (1 : ℤ) = (1 : Multiplicative ℤ) := by
    rw [← fundamentalGroupMulEquiv_generator hp e, h, map_one]
  exact one_ne_zero (congrArg (fun x : Multiplicative ℤ => x.toAdd) hmap)

/-- The chosen generator has infinite order. -/
lemma fundamentalGroupGenerator_not_isOfFinOrder {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) :
    ¬ IsOfFinOrder (fundamentalGroupGenerator hp e) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, hpow⟩
  have hmap : Multiplicative.ofAdd (1 : ℤ) ^ n = (1 : Multiplicative ℤ) := by
    rw [← fundamentalGroupMulEquiv_generator hp e, ← map_pow, hpow, map_one]
  have htoAdd : (n : ℤ) = 0 := by
    simpa [Int.toAdd_pow] using congrArg (fun x : Multiplicative ℤ => x.toAdd) hmap
  exact (Nat.cast_ne_zero.mpr hn.ne') htoAdd

/-- The order of the chosen generator is zero in Mathlib's convention for infinite order. -/
@[simp]
lemma orderOf_fundamentalGroupGenerator {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) : orderOf (fundamentalGroupGenerator hp e) = 0 :=
  orderOf_eq_zero (fundamentalGroupGenerator_not_isOfFinOrder hp e)

/-- An integer power of the chosen generator is trivial exactly for exponent `0`. -/
@[simp]
lemma fundamentalGroupGenerator_zpow_eq_one_iff {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (n : ℤ) :
    fundamentalGroupGenerator hp e ^ n = 1 ↔ n = 0 := by
  rw [fundamentalGroupGenerator_zpow]
  constructor
  · intro h
    have hmap : Multiplicative.ofAdd n = (1 : Multiplicative ℤ) := by
      rw [← (fundamentalGroupMulEquiv p hp e).apply_symm_apply (Multiplicative.ofAdd n), h,
        map_one]
    simpa using congrArg (fun x : Multiplicative ℤ => x.toAdd) hmap
  · intro hn
    simp [hn]

/-- A natural power of the chosen generator is trivial exactly for exponent `0`. -/
@[simp]
lemma fundamentalGroupGenerator_pow_eq_one_iff {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (n : ℕ) :
    fundamentalGroupGenerator hp e ^ n = 1 ↔ n = 0 := by
  rw [← zpow_natCast, fundamentalGroupGenerator_zpow_eq_one_iff, Int.natCast_eq_zero]

/-- The monodromy of the `n`th power of the generator translates the chosen lift by `n • p`. -/
@[simp]
lemma fundamentalGroupGenerator_zpow_monodromy {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (n : ℤ) :
    ((AddCircle.isCoveringMap_coe p).monodromy (fundamentalGroupGenerator hp e ^ n) e : ℝ) =
      (e : ℝ) + n • p := by
  rw [fundamentalGroupGenerator_zpow]
  simp

/-- A loop class is a power of the chosen generator exactly when it has the corresponding
integer under `fundamentalGroupMulEquiv`. -/
lemma eq_fundamentalGroupGenerator_zpow_iff {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) (γ : FundamentalGroup (AddCircle p) x) (n : ℤ) :
    γ = fundamentalGroupGenerator hp e ^ n ↔
      fundamentalGroupMulEquiv p hp e γ = Multiplicative.ofAdd n := by
  constructor
  · intro h
    rw [h, fundamentalGroupGenerator_zpow]
    exact (fundamentalGroupMulEquiv p hp e).apply_symm_apply (Multiplicative.ofAdd n)
  · intro h
    apply (fundamentalGroupMulEquiv p hp e).injective
    simpa [fundamentalGroupGenerator_zpow] using h

/-- The integer powers of the chosen generator are the whole fundamental group. -/
lemma fundamentalGroupGenerator_zpowers_eq_top {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) :
    Subgroup.zpowers (fundamentalGroupGenerator hp e) = ⊤ := by
  rw [eq_top_iff]
  intro γ _
  refine Subgroup.mem_zpowers_iff.2 ⟨(fundamentalGroupMulEquiv p hp e γ).toAdd, ?_⟩
  rw [fundamentalGroupGenerator_zpow]
  exact (fundamentalGroupMulEquiv p hp e).symm_apply_apply γ

/-- The fundamental group of a real additive circle, at any basepoint with a chosen lift, is
cyclic. -/
lemma isCyclic_fundamentalGroup {p : ℝ} (hp : p ≠ 0) {x : AddCircle p}
    (e : ((↑) : ℝ → AddCircle p) ⁻¹' {x}) : IsCyclic (FundamentalGroup (AddCircle p) x) :=
  isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨fundamentalGroupGenerator hp e, fundamentalGroupGenerator_zpowers_eq_top hp e⟩

end AddCircle

namespace UnitAddCircle

/-- The positive generator of `π₁(S¹, 0)`, defined as the loop class corresponding to
`1 : ℤ` under `UnitAddCircle.fundamentalGroupMulEquiv`. -/
noncomputable def fundamentalGroupGenerator : FundamentalGroup UnitAddCircle 0 :=
  fundamentalGroupMulEquiv.symm (Multiplicative.ofAdd (1 : ℤ))

/-- The chosen generator maps to `Multiplicative.ofAdd 1` under
`UnitAddCircle.fundamentalGroupMulEquiv`. -/
@[simp]
lemma fundamentalGroupMulEquiv_generator :
    fundamentalGroupMulEquiv fundamentalGroupGenerator = Multiplicative.ofAdd (1 : ℤ) := by
  simp [fundamentalGroupGenerator]

/-- Integer powers of the chosen generator correspond to the same integers under the
fundamental-group equivalence with `Multiplicative ℤ`. -/
@[simp]
lemma fundamentalGroupGenerator_zpow (n : ℤ) :
    fundamentalGroupGenerator ^ n =
      fundamentalGroupMulEquiv.symm (Multiplicative.ofAdd n) := by
  apply fundamentalGroupMulEquiv.injective
  calc
    fundamentalGroupMulEquiv (fundamentalGroupGenerator ^ n) =
        fundamentalGroupMulEquiv fundamentalGroupGenerator ^ n := map_zpow _ _ _
    _ = Multiplicative.ofAdd (1 : ℤ) ^ n := by rw [fundamentalGroupMulEquiv_generator]
    _ = Multiplicative.ofAdd n := by
      simpa using (Int.ofAdd_mul (1 : ℤ) n).symm
    _ = fundamentalGroupMulEquiv (fundamentalGroupMulEquiv.symm (Multiplicative.ofAdd n)) := by
      rw [fundamentalGroupMulEquiv.apply_symm_apply]

/-- Natural powers of the chosen generator correspond to nonnegative integers. -/
@[simp]
lemma fundamentalGroupGenerator_pow (n : ℕ) :
    fundamentalGroupGenerator ^ n =
      fundamentalGroupMulEquiv.symm (Multiplicative.ofAdd (n : ℤ)) := by
  simpa using fundamentalGroupGenerator_zpow (n : ℤ)

/-- The chosen generator is nontrivial. -/
@[simp]
lemma fundamentalGroupGenerator_ne_one : fundamentalGroupGenerator ≠ 1 := by
  intro h
  have hmap : Multiplicative.ofAdd (1 : ℤ) = (1 : Multiplicative ℤ) := by
    rw [← fundamentalGroupMulEquiv_generator, h, map_one]
  exact one_ne_zero (congrArg (fun x : Multiplicative ℤ => x.toAdd) hmap)

/-- The chosen generator has infinite order. -/
lemma fundamentalGroupGenerator_not_isOfFinOrder : ¬ IsOfFinOrder fundamentalGroupGenerator := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, hpow⟩
  have hmap : Multiplicative.ofAdd (1 : ℤ) ^ n = (1 : Multiplicative ℤ) := by
    rw [← fundamentalGroupMulEquiv_generator, ← map_pow, hpow, map_one]
  have htoAdd : (n : ℤ) = 0 := by
    simpa [Int.toAdd_pow] using congrArg (fun x : Multiplicative ℤ => x.toAdd) hmap
  exact (Nat.cast_ne_zero.mpr hn.ne') htoAdd

/-- The order of the chosen generator is zero in Mathlib's convention for infinite order. -/
@[simp]
lemma orderOf_fundamentalGroupGenerator : orderOf fundamentalGroupGenerator = 0 :=
  orderOf_eq_zero fundamentalGroupGenerator_not_isOfFinOrder

/-- An integer power of the chosen generator is trivial exactly for exponent `0`. -/
@[simp]
lemma fundamentalGroupGenerator_zpow_eq_one_iff (n : ℤ) :
    fundamentalGroupGenerator ^ n = 1 ↔ n = 0 := by
  rw [fundamentalGroupGenerator_zpow]
  constructor
  · intro h
    have hmap : Multiplicative.ofAdd n = (1 : Multiplicative ℤ) := by
      rw [← fundamentalGroupMulEquiv.apply_symm_apply (Multiplicative.ofAdd n), h, map_one]
    simpa using congrArg (fun x : Multiplicative ℤ => x.toAdd) hmap
  · intro hn
    simp [hn]

/-- A natural power of the chosen generator is trivial exactly for exponent `0`. -/
@[simp]
lemma fundamentalGroupGenerator_pow_eq_one_iff (n : ℕ) :
    fundamentalGroupGenerator ^ n = 1 ↔ n = 0 := by
  rw [← zpow_natCast, fundamentalGroupGenerator_zpow_eq_one_iff, Int.natCast_eq_zero]

/-- The monodromy of the `n`th power of the generator translates the zero lift by `n`. -/
@[simp]
lemma fundamentalGroupGenerator_zpow_monodromy (n : ℤ) :
    ((AddCircle.isCoveringMap_coe 1).monodromy (fundamentalGroupGenerator ^ n) ⟨0, by simp⟩ :
      ℝ) = n := by
  rw [fundamentalGroupGenerator_zpow]
  simp

/-- A loop class is a power of the chosen generator exactly when it has the corresponding
integer under `fundamentalGroupMulEquiv`. -/
lemma eq_fundamentalGroupGenerator_zpow_iff
    (γ : FundamentalGroup UnitAddCircle 0) (n : ℤ) :
    γ = fundamentalGroupGenerator ^ n ↔
      fundamentalGroupMulEquiv γ = Multiplicative.ofAdd n := by
  constructor
  · intro h
    rw [h, fundamentalGroupGenerator_zpow]
    exact fundamentalGroupMulEquiv.apply_symm_apply (Multiplicative.ofAdd n)
  · intro h
    apply fundamentalGroupMulEquiv.injective
    simpa [fundamentalGroupGenerator_zpow] using h

/-- The integer powers of the chosen generator are all of `π₁(S¹, 0)`. -/
lemma fundamentalGroupGenerator_zpowers_eq_top :
    Subgroup.zpowers fundamentalGroupGenerator = ⊤ := by
  rw [eq_top_iff]
  intro γ _
  refine Subgroup.mem_zpowers_iff.2 ⟨(fundamentalGroupMulEquiv γ).toAdd, ?_⟩
  rw [fundamentalGroupGenerator_zpow]
  exact fundamentalGroupMulEquiv.symm_apply_apply γ

/-- The fundamental group of the unit circle, based at `0`, is cyclic. -/
instance isCyclic_fundamentalGroup : IsCyclic (FundamentalGroup UnitAddCircle 0) :=
  isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨fundamentalGroupGenerator, fundamentalGroupGenerator_zpowers_eq_top⟩

end UnitAddCircle

end TauCeti
