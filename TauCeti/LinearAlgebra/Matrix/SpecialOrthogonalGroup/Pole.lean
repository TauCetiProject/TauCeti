/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.CardCommute
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.LinearAlgebra.Matrix.Action
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Axis

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# The poles of a finite group of rotations

Let `K` be a group of rotations of `ℝ³`, a subgroup of `SO(3) = Matrix.specialOrthogonalGroup
(Fin 3) ℝ`, acting on `ℝ³` by matrix multiplication. A **pole** of `K` is a unit vector fixed by
some nonidentity element of `K`: a point where the axis of a nonidentity rotation of `K` meets the
unit sphere. The poles form a `K`-stable subset of `ℝ³`, since `k` carries the poles of `g` to the
poles of `k g k⁻¹`, so `K` permutes them (`TauCeti.Matrix.SpecialOrthogonalGroup.poles`).

A nonidentity rotation fixes exactly two unit vectors, the two endpoints of its axis
(`Matrix.exists_setOf_mulVec_eq_self_eq_pair`). So when `K` is finite it has finitely many poles,
and every nonidentity element of `K` fixes exactly two of them. Counting the fixed points of all
elements of `K` on the pole set with Burnside's lemma gives

`|P| + 2 (|K| - 1) = s |K|`,

where `P` is the pole set and `s` the number of `K`-orbits on it. If the orbits have stabilizers of
orders `m₁, …, mₛ`, the class formula `|P| = Σⱼ |K| / mⱼ` turns this into the **pole-orbit
equation**

`Σⱼ (1 - 1 / mⱼ) = 2 - 2 / |K|`.

Every stabilizer of a pole contains a nonidentity rotation, so `mⱼ ≥ 2` and each summand lies in
`[1/2, 1)`, while for nontrivial `K` the right side lies in `[1, 2)`; hence `s = 2` or `s = 3`. When
`s = 2` the equation forces `m₁ = m₂ = |K|`, so all of `K` fixes every pole: this is the case of a
group of rotations about a single axis. The three-orbit case is the one that leads to the dihedral,
tetrahedral, octahedral and icosahedral rotation groups. This is the start of the classical
classification of the finite subgroups of `SO(3)`, and through the double cover `SU(2) → SO(3)`
of those of `SU(2)`.

## Main definitions

All declarations are in the namespace `TauCeti.Matrix.SpecialOrthogonalGroup`.

* `poles K`: the poles of a group `K` of rotations, as a `K`-stable subset of `ℝ³`.

## Main results

* `card_fixedBy_poles`: a nonidentity element of `K` fixes exactly two poles.
* `nonempty_poles_iff`: `K` has a pole exactly when it is nontrivial.
* `card_poles_add_two_mul`: the double count `|P| + 2 (|K| - 1) = s |K|`.
* `finsum_one_sub_inv_card_stabilizer_eq_two_sub_two_div_card`: the pole-orbit equation
  `Σⱼ (1 - 1 / mⱼ) = 2 - 2 / |K|`.
* `card_orbitRel_quotient_poles_eq_two_or_three`: a nontrivial finite group of rotations has two
  or three orbits of poles.
* `stabilizer_eq_top_of_card_orbitRel_quotient_poles_eq_two`: if there are two orbits, every pole
  is fixed by all of `K`.

## References

* M. Artin, *Algebra*, second edition, Pearson, 2011, Section 6.12 (the finite subgroups of the
  rotation group, counted through their poles).
-/

public section

open Matrix MulAction

namespace TauCeti.Matrix.SpecialOrthogonalGroup

variable {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)}

/-- The **poles** of a group `K` of rotations of `ℝ³`: the unit vectors fixed by some nonidentity
element of `K`. Conjugation shows that `K` permutes them. -/
def poles (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) : SubMulAction K (Fin 3 → ℝ) where
  carrier := {p | p ⬝ᵥ p = 1 ∧ ∃ g : K, g ≠ 1 ∧ g • p = p}
  smul_mem' k p := by
    rintro ⟨hp, g, hg, hgp⟩
    refine ⟨?_, k * g * k⁻¹, by simpa using hg, by rw [mul_smul, mul_smul, inv_smul_smul, hgp]⟩
    -- A rotation preserves the dot product.
    have hk := (mem_specialOrthogonalGroup_iff.mp (k : specialOrthogonalGroup (Fin 3) ℝ).2).1
    simpa [Subgroup.smul_def, Submonoid.smul_def, hp] using
      mem_orthogonalGroup_iff_dotProduct_mulVec.mp hk p p

@[simp]
theorem mem_poles {p : Fin 3 → ℝ} : p ∈ poles K ↔ p ⬝ᵥ p = 1 ∧ ∃ g : K, g ≠ 1 ∧ g • p = p :=
  Iff.rfl

/-- The unit vectors fixed by a nonidentity element `g` of `K`: a pair `{v, -v}` of poles. -/
private theorem exists_setOf_smul_eq_self_eq_pair {g : K} (hg : g ≠ 1) :
    ∃ v : Fin 3 → ℝ, v ⬝ᵥ v = 1 ∧ {w | w ⬝ᵥ w = 1 ∧ g • w = w} = {v, -v} := by
  simpa [Subgroup.smul_def, Submonoid.smul_def] using
    exists_setOf_mulVec_eq_self_eq_pair (g : specialOrthogonalGroup (Fin 3) ℝ).2 (by simpa using hg)

/-- **A nonidentity element of `K` fixes exactly two poles**, the two endpoints of its axis on the
unit sphere. -/
theorem card_fixedBy_poles {g : K} (hg : g ≠ 1) : Nat.card (fixedBy (poles K) g) = 2 := by
  obtain ⟨v, hv, hpair⟩ := exists_setOf_smul_eq_self_eq_pair hg
  have hmem {w : Fin 3 → ℝ} (hw : w ∈ ({v, -v} : Set (Fin 3 → ℝ))) : w ∈ poles K := by
    rw [← hpair] at hw
    exact ⟨hw.1, g, hg, hw.2⟩
  have hfix : fixedBy (poles K) g =
      {⟨v, hmem (.inl rfl)⟩, ⟨-v, hmem (.inr rfl)⟩} := by
    ext ⟨w, hw⟩
    have hw' := Set.ext_iff.mp hpair w
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff] at hw'
    simp only [mem_fixedBy, Subtype.ext_iff, SubMulAction.val_smul, Set.mem_insert_iff,
      Set.mem_singleton_iff, ← hw']
    exact ⟨fun h ↦ ⟨hw.1, h⟩, And.right⟩
  -- The two endpoints of the axis are distinct, as `v ≠ 0`.
  have hne : v ≠ -v := fun h ↦ by
    have h2 : (2 : ℝ) • v = 0 := by rw [two_smul, ← sub_neg_eq_add, ← h, sub_self]
    simp [(smul_eq_zero.mp h2).resolve_left two_ne_zero] at hv
  rw [Nat.card_coe_set_eq, hfix, Set.ncard_pair (by simpa [Subtype.ext_iff] using hne)]

/-- **A group of rotations has a pole exactly when it is nontrivial**: by Euler's rotation theorem
every nonidentity rotation has an axis. -/
theorem nonempty_poles_iff : Nonempty (poles K) ↔ Nontrivial K := by
  refine ⟨fun ⟨⟨_, _, g, hg, _⟩⟩ ↦ nontrivial_of_ne g 1 hg, fun _ ↦ ?_⟩
  obtain ⟨g, hg⟩ := exists_ne (1 : K)
  obtain ⟨v, hv, hpair⟩ := exists_setOf_smul_eq_self_eq_pair hg
  have hv' : v ∈ {w | w ⬝ᵥ w = 1 ∧ g • w = w} := hpair ▸ Set.mem_insert v _
  exact ⟨⟨v, hv, g, hg, hv'.2⟩⟩

/-- **A finite group of rotations has finitely many poles**: each of its finitely many nonidentity
elements contributes the two endpoints of its axis. -/
instance [Finite K] : Finite (poles K) := by
  have hfin : (poles K : Set (Fin 3 → ℝ)).Finite := by
    have hg (g : K) : {p : Fin 3 → ℝ | p ⬝ᵥ p = 1 ∧ g ≠ 1 ∧ g • p = p}.Finite := by
      by_cases hg : g = 1
      · simp [hg]
      obtain ⟨v, -, hpair⟩ := exists_setOf_smul_eq_self_eq_pair hg
      exact (Set.toFinite {v, -v}).subset (hpair ▸ fun p ⟨hp, _, hgp⟩ ↦ ⟨hp, hgp⟩)
    exact (Set.finite_iUnion hg).subset fun p ⟨hp, g, hg, hgp⟩ ↦
      Set.mem_iUnion.mpr ⟨g, hp, hg, hgp⟩
  exact hfin.to_subtype

/-- **The stabilizer of a pole is nontrivial**: it contains the nonidentity rotation the pole is an
axis endpoint of. -/
theorem one_lt_card_stabilizer [Finite K] (p : poles K) : 1 < Nat.card (stabilizer K p) := by
  obtain ⟨p, -, g, hg, hgp⟩ := p
  refine (Subgroup.one_lt_card_iff_ne_bot _).mpr fun h ↦ hg ?_
  rw [← Subgroup.mem_bot, ← h, mem_stabilizer_iff]
  exact Subtype.ext hgp

/-- **The double count of fixed poles.** For a finite group `K` of rotations with pole set `P` and
`s` orbits of poles, `|P| + 2 (|K| - 1) = s |K|`: by Burnside's lemma both sides count the pairs
`(g, p)` with `g p = p`, the identity fixing all `|P|` poles and each of the `|K| - 1` other
elements exactly two. -/
theorem card_poles_add_two_mul [Finite K] :
    Nat.card (poles K) + 2 * (Nat.card K - 1) =
      Nat.card (orbitRel.Quotient K (poles K)) * Nat.card K := by
  classical
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (poles K)
  have := Fintype.ofFinite (orbitRel.Quotient K (poles K))
  have hB := sum_card_fixedBy_eq_card_orbits_mul_card_group K (poles K)
  simp only [Fintype.card_eq_nat_card] at hB
  rw [← hB, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1), fixedBy_one_eq_univ, Nat.card_univ,
    Finset.sum_congr rfl fun g hg ↦ card_fixedBy_poles (Finset.ne_of_mem_erase hg),
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_eq_nat_card, smul_eq_mul, mul_comm]

/-- **The class formula for the poles**, over `ℚ`: the pole set is the disjoint union of its
orbits, and the orbit of a pole with stabilizer of order `m` has `|K| / m` points. -/
private theorem card_poles_eq_sum [Finite K] :
    (Nat.card (poles K) : ℚ) = ∑ᶠ ω : orbitRel.Quotient K (poles K),
      (Nat.card K : ℚ) / Nat.card (stabilizer K ω.out) := by
  classical
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (poles K)
  have := Fintype.ofFinite (orbitRel.Quotient K (poles K))
  rw [finsum_eq_sum_of_fintype, ← Fintype.card_eq_nat_card,
    card_eq_sum_card_group_div_card_stabilizer K (poles K), Nat.cast_sum]
  refine Finset.sum_congr rfl fun ω _ ↦ ?_
  rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card,
    Nat.cast_div (Subgroup.card_subgroup_dvd_card _) (Nat.cast_ne_zero.mpr Nat.card_pos.ne')]

/-- **The pole-orbit equation.** If a finite group `K` of rotations of `ℝ³` has orbits of poles
whose stabilizers have orders `m₁, …, mₛ`, then `Σⱼ (1 - 1 / mⱼ) = 2 - 2 / |K|`. For the trivial
group both sides vanish. -/
theorem finsum_one_sub_inv_card_stabilizer_eq_two_sub_two_div_card [Finite K] :
    ∑ᶠ ω : orbitRel.Quotient K (poles K), (1 - (Nat.card (stabilizer K ω.out) : ℚ)⁻¹) =
      2 - 2 / Nat.card K := by
  classical
  have := Fintype.ofFinite (orbitRel.Quotient K (poles K))
  have hN : (0 : ℚ) < Nat.card K := Nat.cast_pos.mpr Nat.card_pos
  -- Divide the class formula by `|K|`, then use the double count.
  have hsum : ∑ ω : orbitRel.Quotient K (poles K), (Nat.card (stabilizer K ω.out) : ℚ)⁻¹ =
      Nat.card (poles K) / Nat.card K := by
    rw [card_poles_eq_sum, finsum_eq_sum_of_fintype, Finset.sum_div]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [div_div_cancel_left₀ hN.ne']
  have hcount : (Nat.card (poles K) : ℚ) + 2 * (Nat.card K - 1) =
      Nat.card (orbitRel.Quotient K (poles K)) * Nat.card K := by
    have h := congrArg (Nat.cast : ℕ → ℚ) (card_poles_add_two_mul (K := K))
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne')] at h
    exact h
  rw [finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
    Fintype.card_eq_nat_card, nsmul_eq_mul, mul_one]
  field_simp
  linear_combination -hcount

/-- The stabilizer of a pole has order at most `|K|`, so each term `1 - 1 / mⱼ` of the pole-orbit
equation is at most `1 - 1 / |K|`; and it is at least `1 / 2`, since `mⱼ ≥ 2`. -/
private theorem one_sub_inv_card_stabilizer_mem [Finite K] (p : poles K) :
    (1 : ℚ) / 2 ≤ 1 - (Nat.card (stabilizer K p) : ℚ)⁻¹ ∧
      1 - (Nat.card (stabilizer K p) : ℚ)⁻¹ ≤ 1 - (Nat.card K : ℚ)⁻¹ := by
  have h2 : (2 : ℚ) ≤ Nat.card (stabilizer K p) := by exact_mod_cast one_lt_card_stabilizer p
  have hle : (Nat.card (stabilizer K p) : ℚ) ≤ Nat.card K := by
    exact_mod_cast Subgroup.card_le_card_group _
  constructor
  · linarith [inv_anti₀ (by norm_num : (0 : ℚ) < 2) h2]
  · linarith [inv_anti₀ (by linarith) hle]

/-- **A nontrivial finite group of rotations has two or three orbits of poles.** Each term
`1 - 1 / mⱼ` of the pole-orbit equation lies in `[1/2, 1 - 1/|K|]`, while its right side
`2 - 2 / |K|` lies in `[1, 2)`. -/
theorem card_orbitRel_quotient_poles_eq_two_or_three [Finite K] [Nontrivial K] :
    Nat.card (orbitRel.Quotient K (poles K)) = 2 ∨
      Nat.card (orbitRel.Quotient K (poles K)) = 3 := by
  classical
  have := Fintype.ofFinite (orbitRel.Quotient K (poles K))
  have heq := finsum_one_sub_inv_card_stabilizer_eq_two_sub_two_div_card (K := K)
  rw [finsum_eq_sum_of_fintype] at heq
  set s := Nat.card (orbitRel.Quotient K (poles K))
  have hcard : (Finset.univ : Finset (orbitRel.Quotient K (poles K))).card = s := by
    rw [Finset.card_univ, Fintype.card_eq_nat_card]
  have hN : (2 : ℚ) ≤ Nat.card K := by exact_mod_cast Finite.one_lt_card
  have hlo : (s : ℚ) * (1 / 2) ≤ 2 - 2 / Nat.card K := by
    rw [← heq, ← hcard, ← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ fun ω _ ↦ (one_sub_inv_card_stabilizer_mem ω.out).1
  have hhi : 2 - 2 / (Nat.card K : ℚ) ≤ s * (1 - (Nat.card K : ℚ)⁻¹) := by
    rw [← heq, ← hcard, ← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun ω _ ↦ (one_sub_inv_card_stabilizer_mem ω.out).2
  have hinv : (Nat.card K : ℚ)⁻¹ ≤ 1 / 2 := by
    rw [one_div]; exact inv_anti₀ (by norm_num) hN
  have hs4 : (s : ℚ) < 4 := by
    have : (0 : ℚ) < 2 / Nat.card K := div_pos two_pos (by linarith)
    linarith
  -- `2 (1 - 1/|K|) ≤ s (1 - 1/|K|)` with `1 - 1/|K| > 0`.
  have hs2 : (2 : ℚ) ≤ s := by
    rw [div_eq_mul_inv, ← mul_one_sub] at hhi
    exact le_of_mul_le_mul_right hhi (by linarith)
  have hs4' : s < 4 := by exact_mod_cast hs4
  have hs2' : 2 ≤ s := by exact_mod_cast hs2
  omega

/-- **The two-orbit case is the cyclic axis case.** If a finite group `K` of rotations has exactly
two orbits of poles, then every pole is fixed by all of `K`: the pole-orbit equation reads
`1 / m₁ + 1 / m₂ = 2 / |K|` with `m₁, m₂ ≤ |K|`, forcing `m₁ = m₂ = |K|`. -/
theorem stabilizer_eq_top_of_card_orbitRel_quotient_poles_eq_two [Finite K]
    (h : Nat.card (orbitRel.Quotient K (poles K)) = 2) (p : poles K) : stabilizer K p = ⊤ := by
  classical
  have := Fintype.ofFinite (orbitRel.Quotient K (poles K))
  have heq := finsum_one_sub_inv_card_stabilizer_eq_two_sub_two_div_card (K := K)
  rw [finsum_eq_sum_of_fintype] at heq
  -- The terms `1 / mⱼ - 1 / |K|` are nonnegative and sum to zero, so they all vanish.
  have hzero : ∑ ω : orbitRel.Quotient K (poles K),
      ((Nat.card (stabilizer K ω.out) : ℚ)⁻¹ - (Nat.card K : ℚ)⁻¹) = 0 := by
    have hcard : (Finset.univ : Finset (orbitRel.Quotient K (poles K))).card = 2 := by
      rw [Finset.card_univ, Fintype.card_eq_nat_card, h]
    have hsplit : ∑ ω : orbitRel.Quotient K (poles K),
        ((Nat.card (stabilizer K ω.out) : ℚ)⁻¹ - (Nat.card K : ℚ)⁻¹) =
          2 - ∑ ω : orbitRel.Quotient K (poles K), (1 - (Nat.card (stabilizer K ω.out) : ℚ)⁻¹) -
            2 * (Nat.card K : ℚ)⁻¹ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
        hcard]
      ring
    rw [hsplit, heq, div_eq_mul_inv]
    ring
  have hnonneg (ω : orbitRel.Quotient K (poles K)) :
      0 ≤ (Nat.card (stabilizer K ω.out) : ℚ)⁻¹ - (Nat.card K : ℚ)⁻¹ := by
    linarith [(one_sub_inv_card_stabilizer_mem ω.out).2]
  -- The representative `q` of the orbit of `p` is fixed by all of `K`.
  set q := (Quotient.mk'' p : orbitRel.Quotient K (poles K)).out
  have hq : stabilizer K q = ⊤ := by
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun ω _ ↦ hnonneg ω).mp hzero
      (Quotient.mk'' p) (Finset.mem_univ _)
    rw [sub_eq_zero, _root_.inv_inj, Nat.cast_inj] at hterm
    exact (Subgroup.card_eq_iff_eq_top _).mp hterm
  -- So the orbit of `q` is `{q}`, and `p`, which lies in it, is `q`.
  obtain ⟨g, hg : g • p = q⟩ : q ∈ orbit K p := orbitRel_apply.mp (Quotient.exact'
    (Quotient.out_eq' (Quotient.mk'' p : orbitRel.Quotient K (poles K))))
  have hpq : p = q := by
    rw [← inv_smul_smul g p, hg]
    exact mem_stabilizer_iff.mp (hq ▸ Subgroup.mem_top g⁻¹)
  rw [hpq, hq]

end TauCeti.Matrix.SpecialOrthogonalGroup
