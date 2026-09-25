/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.GaloisAction
public import TauCeti.RingTheory.LocalRing.RamificationGroup

/-!
# Lower ramification groups of a local field extension

For a finite Galois extension `L/K` of nonarchimedean local fields, the canonical lower
ramification group consists of automorphisms acting trivially on the integer ring modulo
the `(i + 1)`-st power of its maximal ideal. The integer index is total: at `i ≤ -1` the
group is the full Galois group.

This is the local field specialization of `TauCeti.IsLocalRing.ramificationGroup`. Besides the
integer-indexed filtration, the file provides the real indexing `G_u = G_{⌈u⌉}` on which the
Herbrand function is built, the largest jump of the filtration, and its compatibility with the
subgroup `Gal(L/K') ≤ Gal(L/K)` of a tower `L/K'/K`.

## Main definitions

* `TauCeti.LocalFieldsRamification.lowerRamificationGroup K L i`: the `i`-th lower-numbering
  ramification group of `L/K`.
* `TauCeti.LocalFieldsRamification.lowerRamificationGroupReal K L u`: the same filtration indexed
  by `u : ℝ` through the ceiling.
* `TauCeti.LocalFieldsRamification.largestLowerJump K L`: for a nontrivial Galois group, the
  largest index `t` with `G_t ≠ 1`; it is `-1` by convention when the Galois group is trivial.

## Main results

* `TauCeti.LocalFieldsRamification.mem_lowerRamificationGroup_iff`: the defining congruence
  `σ • x ≡ x mod 𝔪 ^ (i + 1)` on `𝒪[L]`.
* `TauCeti.LocalFieldsRamification.lowerRamificationGroup_eq_top_of_le_neg_one`,
  `TauCeti.LocalFieldsRamification.lowerRamificationGroup_zero` and
  `TauCeti.LocalFieldsRamification.lowerRamificationGroup_antitone`: the filtration is `⊤` below
  `0`, starts with the inertia group of the maximal ideal, and decreases.
* `TauCeti.LocalFieldsRamification.lowerRamificationGroup_natCast`: at a nonnegative index it is
  `Ideal.ramificationGroup` of the maximal ideal of `𝒪[L]`.
* `TauCeti.LocalFieldsRamification.lowerRamificationGroup_zero_eq_map_inertiaSubgroup`: `G_0` is
  Mathlib's `ValuationSubring.inertiaSubgroup` of the valuation subring of `L`.
* `TauCeti.LocalFieldsRamification.instNormalLowerRamificationGroup`: each `G_i` is normal.
* `TauCeti.LocalFieldsRamification.exists_forall_lowerRamificationGroup_eq_bot` and
  `TauCeti.LocalFieldsRamification.lowerRamificationGroup_eq_bot_iff`: `G_i = 1` for large `i`,
  precisely for `i` past the largest jump when the Galois group is nontrivial.
* `TauCeti.LocalFieldsRamification.lowerRamificationGroupReal_eq_of_sub_one_lt_of_le`: the real
  indexing is constant on each interval `(i - 1, i]`.
* `TauCeti.LocalFieldsRamification.lowerRamificationGroupReal_eq_bot_iff`: for a nontrivial
  Galois group, `G_u = 1` exactly for real `u` past the largest jump.
* `TauCeti.LocalFieldsRamification.map_restrictScalarsHom_lowerRamificationGroup`: for a tower
  `L/K'/K`, the filtration of `H = Gal(L/K')` is `H ∩ G_i`.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter IV, §1.
-/

public section
noncomputable section

open ValuativeRel

namespace TauCeti.LocalFieldsRamification

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Module.Finite K L]

/-- The lower-numbering ramification group of a finite extension of local fields. -/
def lowerRamificationGroup (i : ℤ) : Subgroup (L ≃ₐ[K] L) :=
  TauCeti.IsLocalRing.ramificationGroup (L ≃ₐ[K] L) 𝒪[L] i

/-- The local-field filtration is the ramification filtration of its integer ring. -/
theorem lowerRamificationGroup_def (i : ℤ) :
    lowerRamificationGroup K L i =
      TauCeti.IsLocalRing.ramificationGroup (L ≃ₐ[K] L) 𝒪[L] i :=
  (rfl)

variable {K L} in
/-- The defining membership criterion of the lower ramification groups. -/
@[simp]
theorem mem_lowerRamificationGroup_iff {i : ℤ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroup K L i ↔
      ∀ x : 𝒪[L], σ • x - x ∈ IsLocalRing.maximalIdeal 𝒪[L] ^ (i + 1).toNat := by
  rw [lowerRamificationGroup_def, TauCeti.IsLocalRing.mem_ramificationGroup_iff]

/-- Below the index `0` the lower filtration is the whole Galois group. -/
theorem lowerRamificationGroup_eq_top_of_le_neg_one {i : ℤ} (hi : i ≤ -1) :
    lowerRamificationGroup K L i = ⊤ := by
  rw [lowerRamificationGroup_def, TauCeti.IsLocalRing.ramificationGroup_eq_top_of_le_neg_one _ _ hi]

/-- The zeroth lower ramification group is the inertia group of the maximal ideal of `𝒪[L]`. -/
theorem lowerRamificationGroup_zero :
    lowerRamificationGroup K L 0 = Ideal.inertia (L ≃ₐ[K] L) (IsLocalRing.maximalIdeal 𝒪[L]) := by
  rw [lowerRamificationGroup_def, TauCeti.IsLocalRing.ramificationGroup_zero_eq_inertia]

/-- The lower ramification filtration is decreasing. -/
theorem lowerRamificationGroup_antitone : Antitone (lowerRamificationGroup K L) :=
  TauCeti.IsLocalRing.ramificationGroup_antitone _ _

/-- At nonnegative indices, the canonical lower group is the maximal-ideal ramification group. -/
@[simp]
theorem lowerRamificationGroup_natCast (i : ℕ) :
    lowerRamificationGroup K L i =
      (IsLocalRing.maximalIdeal 𝒪[L]).ramificationGroup (L ≃ₐ[K] L) i := by
  rw [lowerRamificationGroup_def, TauCeti.IsLocalRing.ramificationGroup_natCast]

/-- Every lower ramification group is normal in the Galois group. -/
instance instNormalLowerRamificationGroup (i : ℤ) : (lowerRamificationGroup K L i).Normal := by
  rw [lowerRamificationGroup_def]
  infer_instance

/-! ### Comparison with Mathlib's inertia subgroup of a valuation subring -/

/-- The zeroth lower ramification group is Mathlib's `ValuationSubring.inertiaSubgroup` of the
valuation subring of `L`, viewed inside the decomposition subgroup, which is everything by
`TauCeti.decompositionSubgroup_valuationSubring_eq_top`. -/
theorem lowerRamificationGroup_zero_eq_map_inertiaSubgroup :
    lowerRamificationGroup K L 0 =
      ((valuation L).valuationSubring.inertiaSubgroup K).map
        ((valuation L).valuationSubring.decompositionSubgroup K).subtype := by
  set A := (valuation L).valuationSubring
  -- Both groups are cut out by `v (σ x - x) < 1`. The restatements below close by unfolding:
  -- `A` is built on `Valuation.integer`, so it has the same carrier as `𝒪[L]`, and both actions
  -- are the action of `σ` on `L`.
  have hG : ∀ σ : L ≃ₐ[K] L, σ ∈ lowerRamificationGroup K L 0 ↔
      ∀ x ∈ 𝒪[L], valuation L (σ x - x) < 1 := fun σ ↦ by
    rw [lowerRamificationGroup_def, TauCeti.IsLocalRing.mem_ramificationGroup_zero_iff,
      Subtype.forall]
    exact forall₂_congr fun x hx ↦ Valuation.Integer.not_isUnit_iff_valuation_lt_one
  have hI : ∀ σ : A.decompositionSubgroup K, σ ∈ A.inertiaSubgroup K ↔
      ∀ x ∈ 𝒪[L], valuation L ((σ : L ≃ₐ[K] L) x - x) < 1 := fun σ ↦ by
    rw [← TauCeti.IsLocalRing.ramificationGroup_zero_eq_inertiaSubgroup,
      TauCeti.IsLocalRing.mem_ramificationGroup_zero_iff, Subtype.forall]
    exact forall₂_congr fun x hx ↦ Valuation.mem_maximalIdeal_iff (v := valuation L)
  ext σ
  have hσ : σ ∈ A.decompositionSubgroup K := by
    rw [TauCeti.decompositionSubgroup_valuationSubring_eq_top]
    exact Subgroup.mem_top σ
  refine ⟨fun h ↦ ⟨⟨σ, hσ⟩, (hI _).2 ((hG σ).1 h), rfl⟩, ?_⟩
  rintro ⟨τ, hτ, rfl⟩
  exact (hG _).2 ((hI τ).1 hτ)

/-! ### Eventual triviality and the largest jump -/

/-- The lower ramification filtration separates the automorphisms of `L/K`. -/
theorem iInf_lowerRamificationGroup_eq_bot : ⨅ i : ℤ, lowerRamificationGroup K L i = ⊥ :=
  TauCeti.IsLocalRing.iInf_ramificationGroup_eq_bot _ _

/-- The lower ramification groups are trivial from some index on. -/
theorem exists_forall_lowerRamificationGroup_eq_bot :
    ∃ N : ℤ, ∀ i : ℤ, N ≤ i → lowerRamificationGroup K L i = ⊥ :=
  TauCeti.IsLocalRing.exists_forall_ramificationGroup_eq_bot _ _

/-- The **largest jump** `t` of the lower ramification filtration. For a nontrivial Galois group
it is the largest index with `G_t ≠ 1`, so that `G_t ≠ 1` and `G_{t + 1} = 1`
(`lowerRamificationGroup_largestLowerJump_ne_bot` and `lowerRamificationGroup_eq_bot_iff`); it is
at least `-1` because `G_{-1}` is the whole Galois group. When `L ≃ₐ[K] L` is trivial every `G_i`
is trivial and there is no jump; the value is then `-1` by convention. -/
noncomputable def largestLowerJump : ℤ :=
  (sInf {n : ℕ | lowerRamificationGroup K L n = ⊥} : ℕ) - 1

/-- The set of natural indices at which the lower filtration is trivial is nonempty. -/
private theorem nonempty_setOf_lowerRamificationGroup_eq_bot :
    {n : ℕ | lowerRamificationGroup K L n = ⊥}.Nonempty := by
  obtain ⟨N, hN⟩ := exists_forall_lowerRamificationGroup_eq_bot K L
  exact ⟨N.toNat, hN _ (Int.self_le_toNat N)⟩

/-- The largest lower jump is at least `-1`. -/
theorem neg_one_le_largestLowerJump : -1 ≤ largestLowerJump K L := by
  rw [largestLowerJump]
  omega

variable {K L} in
/-- The lower ramification groups past the largest jump are trivial. -/
theorem lowerRamificationGroup_eq_bot_of_largestLowerJump_lt {i : ℤ}
    (hi : largestLowerJump K L < i) : lowerRamificationGroup K L i = ⊥ := by
  have hmem := Nat.sInf_mem (nonempty_setOf_lowerRamificationGroup_eq_bot K L)
  rw [largestLowerJump] at hi
  refine eq_bot_iff.2 ((lowerRamificationGroup_antitone K L ?_).trans (eq_bot_iff.1 hmem))
  omega

/-- For a nontrivial automorphism group, the lower ramification group at the largest jump is
nontrivial. -/
theorem lowerRamificationGroup_largestLowerJump_ne_bot [Nontrivial (L ≃ₐ[K] L)] :
    lowerRamificationGroup K L (largestLowerJump K L) ≠ ⊥ := by
  rw [largestLowerJump]
  rcases hn : sInf {n : ℕ | lowerRamificationGroup K L n = ⊥} with _ | m
  · rw [Nat.cast_zero, zero_sub, lowerRamificationGroup_eq_top_of_le_neg_one K L le_rfl]
    exact top_ne_bot
  · have hm : m ∉ {n : ℕ | lowerRamificationGroup K L n = ⊥} :=
      Nat.notMem_of_lt_sInf (by omega)
    rwa [Nat.cast_add_one, add_sub_cancel_right]

variable {K L} in
/-- For a nontrivial automorphism group, `G_i` is trivial exactly past the largest lower jump. -/
@[simp]
theorem lowerRamificationGroup_eq_bot_iff [Nontrivial (L ≃ₐ[K] L)] {i : ℤ} :
    lowerRamificationGroup K L i = ⊥ ↔ largestLowerJump K L < i := by
  refine ⟨fun h ↦ ?_, lowerRamificationGroup_eq_bot_of_largestLowerJump_lt⟩
  by_contra! hi
  exact lowerRamificationGroup_largestLowerJump_ne_bot K L
    (eq_bot_iff.2 ((lowerRamificationGroup_antitone K L hi).trans (eq_bot_iff.1 h)))

/-! ### Real indexing -/

/-- The lower ramification filtration indexed by a real number through the ceiling, as needed by
the Herbrand function: `G_u = G_{⌈u⌉}`, a step function constant on each interval `(i - 1, i]`. -/
noncomputable def lowerRamificationGroupReal (u : ℝ) : Subgroup (L ≃ₐ[K] L) :=
  TauCeti.IsLocalRing.ramificationGroupReal (L ≃ₐ[K] L) 𝒪[L] u

/-- The real-indexed lower ramification group at `u` is the integer-indexed one at `⌈u⌉`. -/
theorem lowerRamificationGroupReal_def (u : ℝ) :
    lowerRamificationGroupReal K L u = lowerRamificationGroup K L ⌈u⌉ :=
  TauCeti.IsLocalRing.ramificationGroupReal_def _ _ u

variable {K L} in
/-- Membership in the real-indexed lower ramification groups. -/
@[simp]
theorem mem_lowerRamificationGroupReal_iff {u : ℝ} {σ : L ≃ₐ[K] L} :
    σ ∈ lowerRamificationGroupReal K L u ↔ σ ∈ lowerRamificationGroup K L ⌈u⌉ := by
  rw [lowerRamificationGroupReal_def]

/-- At an integer the real indexing agrees with the integer indexing. -/
@[simp]
theorem lowerRamificationGroupReal_intCast (i : ℤ) :
    lowerRamificationGroupReal K L (i : ℝ) = lowerRamificationGroup K L i :=
  TauCeti.IsLocalRing.ramificationGroupReal_intCast _ _ i

/-- The real-indexed lower filtration is constant on each interval `(i - 1, i]`. -/
theorem lowerRamificationGroupReal_eq_of_sub_one_lt_of_le {i : ℤ} {u : ℝ}
    (hleft : (i : ℝ) - 1 < u) (hright : u ≤ i) :
    lowerRamificationGroupReal K L u = lowerRamificationGroup K L i :=
  TauCeti.IsLocalRing.ramificationGroupReal_eq_of_sub_one_lt_of_le _ _ hleft hright

/-- The real-indexed lower filtration is decreasing. -/
theorem lowerRamificationGroupReal_antitone : Antitone (lowerRamificationGroupReal K L) :=
  TauCeti.IsLocalRing.ramificationGroupReal_antitone _ _

variable {K L} in
/-- For a nontrivial automorphism group, `G_u` is trivial exactly for real `u` past the largest
lower jump. -/
@[simp]
theorem lowerRamificationGroupReal_eq_bot_iff [Nontrivial (L ≃ₐ[K] L)] {u : ℝ} :
    lowerRamificationGroupReal K L u = ⊥ ↔ (largestLowerJump K L : ℝ) < u := by
  rw [lowerRamificationGroupReal_def, lowerRamificationGroup_eq_bot_iff, Int.lt_ceil]

/-- Every real-indexed lower ramification group is normal in the Galois group. -/
instance instNormalLowerRamificationGroupReal (u : ℝ) :
    (lowerRamificationGroupReal K L u).Normal := by
  rw [lowerRamificationGroupReal_def]
  infer_instance

/-! ### Compatibility with subgroups

For a tower `L/K'/K`, the group `Gal(L/K')` is the subgroup `H` of `Gal(L/K)` fixing `K'`, embedded
by `AlgEquiv.restrictScalarsHom`. Its lower filtration is the trace of that of `L/K`:
`H_i = H ∩ G_i`. -/

section Tower

variable (K' : Type*) [Field K'] [ValuativeRel K'] [TopologicalSpace K']
  [IsNonarchimedeanLocalField K'] [Algebra K K'] [Algebra K' L] [IsScalarTower K K' L]
  [ValuativeExtension K' L] [Module.Finite K' L]

/-- An automorphism of `L/K'` lies in the `i`-th lower ramification group of `L/K'` exactly when
it lies in that of `L/K` after restricting scalars. -/
theorem comap_restrictScalarsHom_lowerRamificationGroup (i : ℤ) :
    (lowerRamificationGroup K L i).comap (AlgEquiv.restrictScalarsHom (S := K') K) =
      lowerRamificationGroup K' L i := by
  ext σ
  simp [AlgEquiv.restrictScalarsHom_apply]

/-- **Compatibility with subgroups**: the image of the lower filtration of `L/K'` in `Gal(L/K)`
is the trace `H ∩ G_i` of the lower filtration of `L/K` on the image `H` of `Gal(L/K')`. -/
theorem map_restrictScalarsHom_lowerRamificationGroup (i : ℤ) :
    (lowerRamificationGroup K' L i).map (AlgEquiv.restrictScalarsHom (S := K') K) =
      (AlgEquiv.restrictScalarsHom (S := K') K).range ⊓ lowerRamificationGroup K L i := by
  rw [← comap_restrictScalarsHom_lowerRamificationGroup K L K', Subgroup.map_comap_eq]

/-- The real-indexed form of `comap_restrictScalarsHom_lowerRamificationGroup`. -/
theorem comap_restrictScalarsHom_lowerRamificationGroupReal (u : ℝ) :
    (lowerRamificationGroupReal K L u).comap (AlgEquiv.restrictScalarsHom (S := K') K) =
      lowerRamificationGroupReal K' L u := by
  rw [lowerRamificationGroupReal_def, lowerRamificationGroupReal_def,
    comap_restrictScalarsHom_lowerRamificationGroup]

/-- The real-indexed form of `map_restrictScalarsHom_lowerRamificationGroup`. -/
theorem map_restrictScalarsHom_lowerRamificationGroupReal (u : ℝ) :
    (lowerRamificationGroupReal K' L u).map (AlgEquiv.restrictScalarsHom (S := K') K) =
      (AlgEquiv.restrictScalarsHom (S := K') K).range ⊓ lowerRamificationGroupReal K L u := by
  rw [← comap_restrictScalarsHom_lowerRamificationGroupReal K L K', Subgroup.map_comap_eq]

end Tower

end TauCeti.LocalFieldsRamification
