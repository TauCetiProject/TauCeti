/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.GroupAction.SubMulAction
public import Mathlib.LinearAlgebra.Matrix.Action
public import TauCeti.GroupTheory.GroupAction.Stabilizer.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Axis
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Stabilizer

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.NumberTheory.ADEInequality
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import TauCeti.GroupTheory.GroupAction.CardCommute
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# The poles of a finite group of rotations

Let `K` be a group of rotations of `ℝ³`, a subgroup of `SO(3) = Matrix.specialOrthogonalGroup
(Fin 3) ℝ`, acting on `ℝ³` by matrix multiplication. A **pole** of `K` is a unit vector fixed by
some nonidentity element of `K`: a point where the axis of a nonidentity rotation of `K` meets the
unit sphere. The poles form a `K`-stable subset of `ℝ³`, since `k` carries the poles of `g` to the
poles of `k g k⁻¹`, so `K` permutes them (`TauCeti.Matrix.SpecialOrthogonalGroup.poles`).

A nonidentity rotation fixes exactly two unit vectors, the two endpoints of its axis
(`Matrix.exists_setOf_mulVec_eq_self_eq_pair_of_mem_specialOrthogonalGroup`). So the poles come in
antipodal pairs `{p, -p}`, when `K` is finite it has finitely many poles, and every nonidentity
element of `K` fixes exactly two of them. Counting the fixed points of all elements of `K` on the
pole set with Burnside's lemma gives

`|P| + 2 (|K| - 1) = s |K|`,

where `P` is the pole set and `s` the number of `K`-orbits on it. If the orbits have stabilizers of
orders `m₁, …, mₛ`, the class formula `|P| = Σⱼ |K| / mⱼ`
(`TauCeti.card_eq_finsum_card_group_div_cardStabilizerOnOrbit`) turns this into the **pole-orbit
equation**

`Σⱼ (1 - 1 / mⱼ) = 2 - 2 / |K|`.

Every stabilizer of a pole contains a nonidentity rotation, so `mⱼ ≥ 2` and each summand lies in
`[1/2, 1)`, while for nontrivial `K` the right side lies in `[1, 2)`; hence `s = 2` or `s = 3`. When
`s = 2` the equation forces `m₁ = m₂ = |K|`, so all of `K` fixes every pole: this is the case of a
group of rotations about a single axis. When `s = 3`, ordering the stabilizer orders as
`m₁ ≤ m₂ ≤ m₃`, the equation reads `1/m₁ + 1/m₂ + 1/m₃ = 1 + 2/|K| > 1`, whose solutions are
classified in Mathlib (`ADEInequality.classification`). Since every `mⱼ ≥ 2`, the triple is
`(2, 2, n)`, `(2, 3, 3)`, `(2, 3, 4)` or `(2, 3, 5)`, and the equation then fixes
`|K| = 2n, 12, 24, 60`: these are the orders of the dihedral, tetrahedral, octahedral and
icosahedral rotation groups. In particular a finite group of rotations with three orbits of poles
has even order, so a finite group of rotations of odd order fixes each of its poles. This is the
start of the classical classification of the finite subgroups of `SO(3)`, and through the double
cover `SU(2) → SO(3)` of those of `SU(2)`.

## Main definitions

All declarations are in the namespace `TauCeti.Matrix.SpecialOrthogonalGroup`.

* `poles K`: the poles of a group `K` of rotations, as a `K`-stable subset of `ℝ³`.

## Main results

* `neg_mem_poles`, `poles.stabilizer_neg`: the antipode `-p` of a pole `p` is a pole with the
  same stabilizer.
* `fixedBy_poles_eq_pair`, `exists_fixedBy_poles_eq_pair`: the poles fixed by a nonidentity
  element of `K` are a pair `{p, -p}`, and `card_fixedBy_poles`: there are exactly two of them.
* `nonempty_poles_iff`: `K` has a pole exactly when it is nontrivial.
* `one_lt_cardStabilizerOnOrbit_poles`: for finite `K`, every orbit of poles has a stabilizer of
  order at least `2`.
* `card_poles_add_two_mul`: the double count `|P| + 2 (|K| - 1) = s |K|`.
* `finsum_one_sub_inv_cardStabilizerOnOrbit_poles_eq_two_sub_two_div_card`: the pole-orbit
  equation `Σⱼ (1 - 1 / mⱼ) = 2 - 2 / |K|`, with the stabilizer orders read off as
  `TauCeti.cardStabilizerOnOrbit`.
* `card_orbitRel_quotient_poles_eq_two_or_three`: a nontrivial finite group of rotations has two
  or three orbits of poles.
* `stabilizer_eq_top_of_card_orbitRel_quotient_poles_eq_two`: if there are two orbits, every pole
  is fixed by all of `K`, and `isCyclic_of_card_orbitRel_quotient_poles_eq_two`: `K` is then cyclic.
* `exists_equiv_cardStabilizerOnOrbit_poles_of_card_orbitRel_quotient_poles_eq_three`: if there
  are three orbits, their stabilizer orders and the order of `K` are `(2, 2, n; 2n)`,
  `(2, 3, 3; 12)`, `(2, 3, 4; 24)` or `(2, 3, 5; 60)`.
* `even_card_of_card_orbitRel_quotient_poles_eq_three`: if there are three orbits, `K` has even
  order.
* `stabilizer_eq_top_of_odd_card`: a finite group of rotations of odd order fixes each of its poles.
* The stabilizer of a pole is cyclic, an instance deduced from
  `isCyclic_stabilizer_of_ne_zero`.

## References

* M. Artin, *Algebra*, second edition, Pearson, 2011, Section 6.12 (the finite subgroups of the
  rotation group, counted through their poles).
-/

public section

open Matrix MulAction

namespace TauCeti.Matrix.SpecialOrthogonalGroup

variable {K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)}

/-- The **poles** of a group `K` of rotations of `ℝ³`: the unit vectors fixed by some nonidentity
element of `K`, as a `K`-stable subset of `ℝ³`. -/
def poles (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ)) : SubMulAction K (Fin 3 → ℝ) where
  carrier := {p | p ⬝ᵥ p = 1 ∧ ∃ g : K, g ≠ 1 ∧ g • p = p}
  smul_mem' k p := by
    rintro ⟨hp, g, hg, hgp⟩
    refine ⟨?_, k * g * k⁻¹, by simpa using hg, by rw [mul_smul, mul_smul, inv_smul_smul, hgp]⟩
    -- A rotation preserves the dot product.
    have hk := (mem_specialOrthogonalGroup_iff.mp (k : specialOrthogonalGroup (Fin 3) ℝ).property).1
    simpa [Subgroup.smul_def, Submonoid.smul_def, hp] using
      mem_orthogonalGroup_iff_dotProduct_mulVec.mp hk p p

@[simp]
theorem mem_poles {p : Fin 3 → ℝ} : p ∈ poles K ↔ p ⬝ᵥ p = 1 ∧ ∃ g : K, g ≠ 1 ∧ g • p = p :=
  Iff.rfl

/-- The antipode of a vector is a pole exactly when the vector is. -/
theorem neg_mem_poles {p : Fin 3 → ℝ} : -p ∈ poles K ↔ p ∈ poles K := by
  suffices ∀ {p : Fin 3 → ℝ}, p ∈ poles K → -p ∈ poles K from
    ⟨fun h ↦ neg_neg p ▸ this h, this⟩
  rintro p ⟨hp, g, hg, hgp⟩
  exact ⟨by rw [neg_dotProduct, dotProduct_neg, neg_neg, hp], g, hg, by rw [smul_neg, hgp]⟩

namespace poles

/-- A pole is a unit vector. -/
@[simp]
theorem coe_dotProduct_self (p : poles K) : (p : Fin 3 → ℝ) ⬝ᵥ p = 1 :=
  p.property.1

/-- A pole is nonzero. -/
@[simp]
theorem coe_ne_zero (p : poles K) : (p : Fin 3 → ℝ) ≠ 0 := fun h ↦ by
  simpa [h] using coe_dotProduct_self p

/-- The antipodal map on the poles. -/
instance : InvolutiveNeg (poles K) where
  neg p := ⟨-p, neg_mem_poles.mpr p.property⟩
  neg_neg p := Subtype.ext (neg_neg (p : Fin 3 → ℝ))

@[simp, norm_cast]
theorem coe_neg (p : poles K) : ((-p : poles K) : Fin 3 → ℝ) = -p :=
  rfl

/-- A pole is distinct from its antipode. -/
theorem neg_ne_self (p : poles K) : -p ≠ p :=
  mt (congrArg Subtype.val) (_root_.neg_ne_self.mpr (coe_ne_zero p))

/-- The action of `K` on the poles commutes with the antipodal map. -/
@[simp]
theorem smul_neg (k : K) (p : poles K) : k • -p = -(k • p) :=
  Subtype.ext (by
    rw [SubMulAction.val_smul, coe_neg, coe_neg, SubMulAction.val_smul, _root_.smul_neg])

/-- A pole and its antipode have the same stabilizer.

Not a `simp` lemma: `simp` tries `IsCancelSMul.stabilizer_eq_bot` on both sides, whose instance
search times out in large environments. -/
theorem stabilizer_neg (p : poles K) : stabilizer K (-p) = stabilizer K p := by
  ext k
  simp only [mem_stabilizer_iff, smul_neg, neg_inj]

end poles

/-- **The poles fixed by a nonidentity element `g` of `K` are a pole `p` fixed by `g` and its
antipode `-p`.** -/
theorem fixedBy_poles_eq_pair {g : K} (hg : g ≠ 1) {p : poles K} (hgp : g • p = p) :
    fixedBy (poles K) g = {p, -p} := by
  have hgp' : g • (p : Fin 3 → ℝ) = p := by rw [← SubMulAction.val_smul, hgp]
  have hpair := setOf_mulVec_eq_self_eq_pair_of_mem_specialOrthogonalGroup
    (g : specialOrthogonalGroup (Fin 3) ℝ).property (by simpa using hg)
    (by simpa [Subgroup.smul_def, Submonoid.smul_def, smul_eq_mulVec] using hgp')
  ext q
  have hq := Set.ext_iff.mp hpair q
  simp only [Set.mem_ofPred_eq, poles.coe_dotProduct_self, true_and, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hq
  simp only [mem_fixedBy, Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff,
    SubMulAction.val_smul, poles.coe_neg, Subgroup.smul_def, Submonoid.smul_def, smul_eq_mulVec,
    hq]

/-- **A nonidentity element of `K` fixes a pair `{p, -p}` of poles**, the two endpoints of its axis
on the unit sphere. -/
theorem exists_fixedBy_poles_eq_pair {g : K} (hg : g ≠ 1) :
    ∃ p : poles K, fixedBy (poles K) g = {p, -p} := by
  obtain ⟨v, hv, hgv⟩ := exists_dotProduct_self_eq_one_mulVec_eq_self_of_mem_specialOrthogonalGroup
    (by decide) (g : specialOrthogonalGroup (Fin 3) ℝ).property
  have hgv' : g • v = v := by simpa [Subgroup.smul_def, Submonoid.smul_def] using hgv
  exact ⟨⟨v, hv, g, hg, hgv'⟩,
    fixedBy_poles_eq_pair hg (Subtype.ext (by rw [SubMulAction.val_smul]; exact hgv'))⟩

/-- **A nonidentity element of `K` fixes exactly two poles.** -/
theorem card_fixedBy_poles {g : K} (hg : g ≠ 1) : Nat.card (fixedBy (poles K) g) = 2 := by
  obtain ⟨p, hp⟩ := exists_fixedBy_poles_eq_pair hg
  rw [Nat.card_coe_set_eq, hp, Set.ncard_pair (poles.neg_ne_self p).symm]

/-- **A group of rotations has a pole exactly when it is nontrivial.** -/
theorem nonempty_poles_iff : Nonempty (poles K) ↔ Nontrivial K := by
  refine ⟨fun ⟨⟨_, _, g, hg, _⟩⟩ ↦ nontrivial_of_ne g 1 hg, fun _ ↦ ?_⟩
  obtain ⟨g, hg⟩ := exists_ne (1 : K)
  obtain ⟨p, -⟩ := exists_fixedBy_poles_eq_pair hg
  exact ⟨p⟩

instance [Nontrivial K] : Nonempty (poles K) :=
  nonempty_poles_iff.mpr ‹_›

instance [Subsingleton K] : IsEmpty (poles K) :=
  not_nonempty_iff.mp fun h ↦ not_nontrivial K (nonempty_poles_iff.mp h)

/-- **A finite group of rotations has finitely many poles.** -/
instance [Finite K] : Finite (poles K) := by
  -- Each nonidentity element contributes the two endpoints of its axis.
  refine Set.finite_univ_iff.mp ((Set.finite_iUnion
    (f := fun g : {g : K // g ≠ 1} ↦ fixedBy (poles K) (g : K)) fun g ↦ ?_).subset ?_)
  · obtain ⟨p, hp⟩ := exists_fixedBy_poles_eq_pair g.property
    rw [hp]
    exact Set.toFinite _
  · rintro p -
    obtain ⟨-, g, hg, hgp⟩ := p.property
    exact Set.mem_iUnion.mpr
      ⟨⟨g, hg⟩, mem_fixedBy.mpr (Subtype.ext (by rw [SubMulAction.val_smul, hgp]))⟩

/-- The stabilizer of a pole is nontrivial. -/
instance (p : poles K) : Nontrivial (stabilizer K p) := by
  obtain ⟨-, g, hg, hgp⟩ := p.property
  exact ⟨⟨g, mem_stabilizer_iff.mpr (Subtype.ext (by rw [SubMulAction.val_smul, hgp]))⟩, 1,
    fun h ↦ hg ((Subgroup.mk_eq_one _).mp h)⟩

/-- **The stabilizer of a pole is cyclic**, for a finite group of rotations: it is a finite group
of rotations about the axis through the pole (`isCyclic_stabilizer_of_ne_zero`). -/
instance [Finite K] (p : poles K) : IsCyclic (stabilizer K p) := by
  rw [SubMulAction.stabilizer_of_subMul]
  exact isCyclic_stabilizer_of_ne_zero K (poles.coe_ne_zero p)

/-- **Every orbit of poles has a stabilizer of order at least `2`**, for a finite group of
rotations: the stabilizer of a pole contains a nonidentity rotation. -/
theorem one_lt_cardStabilizerOnOrbit_poles [Finite K] (ω : orbitRel.Quotient K (poles K)) :
    1 < cardStabilizerOnOrbit ω := by
  induction ω using Quotient.inductionOn' with | h p => ?_
  rw [cardStabilizerOnOrbit_mk]
  exact Finite.one_lt_card

variable (K) in
/-- **The double count of fixed poles.** For a finite group `K` of rotations with pole set `P` and
`s` orbits of poles, `|P| + 2 (|K| - 1) = s |K|`. -/
theorem card_poles_add_two_mul [Finite K] :
    Nat.card (poles K) + 2 * (Nat.card K - 1) =
      Nat.card (orbitRel.Quotient K (poles K)) * Nat.card K := by
  classical
  have := Fintype.ofFinite K
  have := Fintype.ofFinite (poles K)
  have := Fintype.ofFinite (orbitRel.Quotient K (poles K))
  -- By Burnside's lemma both sides count the pairs `(g, p)` with `g p = p`: the identity fixes all
  -- poles, and each of the `|K| - 1` other elements exactly two.
  have hB := sum_card_fixedBy_eq_card_orbits_mul_card_group K (poles K)
  simp only [Fintype.card_eq_nat_card] at hB
  have hfix : ∑ g ∈ Finset.univ.erase (1 : K), Nat.card (fixedBy (poles K) g) =
      2 * (Nat.card K - 1) := by
    rw [Finset.sum_congr rfl fun g hg ↦ card_fixedBy_poles (Finset.ne_of_mem_erase hg)]
    simp [Finset.card_erase_of_mem, mul_comm]
  rw [← hB, ← Finset.add_sum_erase _ _ (Finset.mem_univ 1), hfix]
  simp

variable (K) in
/-- **The pole-orbit equation.** For a finite group `K` of rotations of `ℝ³`, the orders `m_ω` of
the stabilizers of its orbits `ω` of poles satisfy `Σ_ω (1 - 1 / m_ω) = 2 - 2 / |K|`. -/
theorem finsum_one_sub_inv_cardStabilizerOnOrbit_poles_eq_two_sub_two_div_card [Finite K] :
    ∑ᶠ ω : orbitRel.Quotient K (poles K), (1 - (cardStabilizerOnOrbit ω : ℚ)⁻¹) =
      2 - 2 / Nat.card K := by
  classical
  have := Fintype.ofFinite (orbitRel.Quotient K (poles K))
  have hN : (0 : ℚ) < Nat.card K := Nat.cast_pos.mpr Nat.card_pos
  -- Divide the class formula by `|K|`, then use the double count.
  have hsum : ∑ ω : orbitRel.Quotient K (poles K), (cardStabilizerOnOrbit ω : ℚ)⁻¹ =
      Nat.card (poles K) / Nat.card K := by
    rw [card_eq_finsum_card_group_div_cardStabilizerOnOrbit K (poles K) ℚ,
      finsum_eq_sum_of_fintype, Finset.sum_div]
    refine Finset.sum_congr rfl fun ω _ ↦ ?_
    rw [div_div_cancel_left₀ hN.ne']
  have hcount : (Nat.card (poles K) : ℚ) + 2 * (Nat.card K - 1) =
      Nat.card (orbitRel.Quotient K (poles K)) * Nat.card K := by
    have h := congrArg (Nat.cast : ℕ → ℚ) (card_poles_add_two_mul K)
    push_cast [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr Nat.card_pos.ne')] at h
    exact h
  rw [finsum_eq_sum_of_fintype, Finset.sum_sub_distrib, hsum, Finset.sum_const, Finset.card_univ,
    Fintype.card_eq_nat_card, nsmul_eq_mul, mul_one]
  field_simp
  linear_combination -hcount

/-- For a finite group `K` of rotations, each term `1 - 1 / m_ω` of the pole-orbit equation lies
in `[1/2, 1 - 1/|K|]`. -/
private theorem one_sub_inv_cardStabilizerOnOrbit_mem [Finite K]
    (ω : orbitRel.Quotient K (poles K)) :
    (1 : ℚ) / 2 ≤ 1 - (cardStabilizerOnOrbit ω : ℚ)⁻¹ ∧
      1 - (cardStabilizerOnOrbit ω : ℚ)⁻¹ ≤ 1 - (Nat.card K : ℚ)⁻¹ := by
  have h2 : (2 : ℚ) ≤ cardStabilizerOnOrbit ω := by
    exact_mod_cast one_lt_cardStabilizerOnOrbit_poles ω
  have hle : (cardStabilizerOnOrbit ω : ℚ) ≤ Nat.card K := by
    exact_mod_cast cardStabilizerOnOrbit_le_card ω
  constructor
  · linarith [inv_anti₀ (by norm_num : (0 : ℚ) < 2) h2]
  · linarith [inv_anti₀ (by linarith) hle]

variable (K) in
/-- **A nontrivial finite group of rotations has two or three orbits of poles.** -/
theorem card_orbitRel_quotient_poles_eq_two_or_three [Finite K] [Nontrivial K] :
    Nat.card (orbitRel.Quotient K (poles K)) = 2 ∨
      Nat.card (orbitRel.Quotient K (poles K)) = 3 := by
  classical
  have := Fintype.ofFinite (orbitRel.Quotient K (poles K))
  have heq := finsum_one_sub_inv_cardStabilizerOnOrbit_poles_eq_two_sub_two_div_card K
  rw [finsum_eq_sum_of_fintype] at heq
  set s := Nat.card (orbitRel.Quotient K (poles K))
  have hcard : (Finset.univ : Finset (orbitRel.Quotient K (poles K))).card = s := by
    rw [Finset.card_univ, Fintype.card_eq_nat_card]
  -- Each term of the pole-orbit equation lies in `[1/2, 1 - 1/|K|]`, while its right side
  -- `2 - 2 / |K|` lies in `[1, 2)`.
  have hN : (2 : ℚ) ≤ Nat.card K := by exact_mod_cast Finite.one_lt_card
  have hlo : (s : ℚ) * (1 / 2) ≤ 2 - 2 / Nat.card K := by
    rw [← heq, ← hcard, ← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ fun ω _ ↦ (one_sub_inv_cardStabilizerOnOrbit_mem ω).1
  have hhi : 2 - 2 / (Nat.card K : ℚ) ≤ s * (1 - (Nat.card K : ℚ)⁻¹) := by
    rw [← heq, ← hcard, ← nsmul_eq_mul]
    exact Finset.sum_le_card_nsmul _ _ _ fun ω _ ↦ (one_sub_inv_cardStabilizerOnOrbit_mem ω).2
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

/-- **In the two-orbit case, every pole is fixed by all of `K`.** If a finite group `K` of
rotations has exactly two orbits of poles, then the stabilizer of every pole is `K`. -/
theorem stabilizer_eq_top_of_card_orbitRel_quotient_poles_eq_two [Finite K]
    (h : Nat.card (orbitRel.Quotient K (poles K)) = 2) (p : poles K) : stabilizer K p = ⊤ := by
  classical
  have := Fintype.ofFinite (orbitRel.Quotient K (poles K))
  have heq := finsum_one_sub_inv_cardStabilizerOnOrbit_poles_eq_two_sub_two_div_card K
  rw [finsum_eq_sum_of_fintype] at heq
  -- With two orbits of stabilizer orders `m₁, m₂ ≤ |K|`, the pole-orbit equation reads
  -- `1 / m₁ + 1 / m₂ = 2 / |K|`: the terms `1 / m_ω - 1 / |K|` are nonnegative and sum to zero, so
  -- they all vanish.
  have hzero : ∑ ω : orbitRel.Quotient K (poles K),
      ((cardStabilizerOnOrbit ω : ℚ)⁻¹ - (Nat.card K : ℚ)⁻¹) = 0 := by
    have hcard : (Finset.univ : Finset (orbitRel.Quotient K (poles K))).card = 2 := by
      rw [Finset.card_univ, Fintype.card_eq_nat_card, h]
    have hsplit : ∑ ω : orbitRel.Quotient K (poles K),
        ((cardStabilizerOnOrbit ω : ℚ)⁻¹ - (Nat.card K : ℚ)⁻¹) =
          2 - ∑ ω : orbitRel.Quotient K (poles K), (1 - (cardStabilizerOnOrbit ω : ℚ)⁻¹) -
            2 * (Nat.card K : ℚ)⁻¹ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_const,
        hcard]
      ring
    rw [hsplit, heq, div_eq_mul_inv]
    ring
  have hnonneg (ω : orbitRel.Quotient K (poles K)) :
      0 ≤ (cardStabilizerOnOrbit ω : ℚ)⁻¹ - (Nat.card K : ℚ)⁻¹ := by
    linarith [(one_sub_inv_cardStabilizerOnOrbit_mem ω).2]
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun ω _ ↦ hnonneg ω).mp hzero
    (Quotient.mk'' p) (Finset.mem_univ _)
  rw [cardStabilizerOnOrbit_mk, sub_eq_zero, _root_.inv_inj, Nat.cast_inj] at hterm
  exact (Subgroup.card_eq_iff_eq_top _).mp hterm

/-- **In the two-orbit case, `K` is cyclic.** If a finite group `K` of rotations has exactly two
orbits of poles, then `K` fixes every pole, so it is the stabilizer of a pole, which is cyclic. -/
theorem isCyclic_of_card_orbitRel_quotient_poles_eq_two [Finite K]
    (h : Nat.card (orbitRel.Quotient K (poles K)) = 2) : IsCyclic K := by
  obtain ⟨ω⟩ : Nonempty (orbitRel.Quotient K (poles K)) := (Nat.card_pos_iff.mp (by omega)).1
  rw [← (Subgroup.topEquiv (G := K)).isCyclic,
    ← stabilizer_eq_top_of_card_orbitRel_quotient_poles_eq_two h ω.out]
  infer_instance

/-- The solutions of the three-orbit pole equation. If `2 ≤ a ≤ b ≤ c` and
`1/a + 1/b + 1/c = 1 + 2/N` with `N > 0`, then `(a, b, c; N)` is `(2, 2, c; 2c)`, `(2, 3, 3; 12)`,
`(2, 3, 4; 24)` or `(2, 3, 5; 60)`. -/
private theorem eq_of_inv_add_inv_add_inv_eq_one_add_two_div {a b c N : ℕ} (ha : 2 ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c) (hN : 0 < N)
    (h : (a : ℚ)⁻¹ + (b : ℚ)⁻¹ + (c : ℚ)⁻¹ = 1 + 2 / N) :
    a = 2 ∧ b = 2 ∧ N = 2 * c ∨ a = 2 ∧ b = 3 ∧ c = 3 ∧ N = 12 ∨
      a = 2 ∧ b = 3 ∧ c = 4 ∧ N = 24 ∨ a = 2 ∧ b = 3 ∧ c = 5 ∧ N = 60 := by
  -- The equation says `1/a + 1/b + 1/c > 1`, and Mathlib's classification of the solutions of
  -- this inequality bounds `a`, then `b`, then `c`.
  have hbound : a < 3 ∧ (a = 2 → b < 4) ∧ (a = 2 → b = 3 → c < 6) := by
    lift a to ℕ+ using by omega
    lift b to ℕ+ using by omega
    lift c to ℕ+ using by omega
    have H : 1 < ADEInequality.sumInv {a, b, c} := by
      rw [ADEInequality.sumInv_pqr, h, lt_add_iff_pos_right]
      positivity
    refine ⟨mod_cast ADEInequality.lt_three (mod_cast hab) (mod_cast hbc) H, fun ha ↦ ?_,
      fun ha hb ↦ ?_⟩
    · rw [show a = 2 from PNat.coe_injective ha] at H
      exact mod_cast ADEInequality.lt_four (mod_cast hbc) H
    · rw [show a = 2 from PNat.coe_injective ha, show b = 3 from PNat.coe_injective hb] at H
      exact mod_cast ADEInequality.lt_six H
  obtain rfl : a = 2 := by omega
  have hN' : (N : ℚ) ≠ 0 := by positivity
  -- In each remaining case the equation is linear in `N`.
  obtain rfl | rfl : b = 2 ∨ b = 3 := by have := hbound.2.1 rfl; omega
  · have hc : (c : ℚ) ≠ 0 := by norm_cast; omega
    norm_num at h
    field_simp at h
    refine Or.inl ⟨rfl, rfl, ?_⟩
    rw [← Nat.cast_inj (R := ℚ)]
    push_cast
    linarith
  · have := hbound.2.2 rfl rfl
    obtain rfl | rfl | rfl : c = 3 ∨ c = 4 ∨ c = 5 := by omega
    all_goals
      norm_num at h ⊢
      field_simp at h
      rw [← Nat.cast_inj (R := ℚ)]
      push_cast
      linarith

variable (K) in
/-- **The three-orbit case of the pole-orbit equation.** If a finite group `K` of rotations has
three orbits of poles, they can be listed as `e 0`, `e 1`, `e 2` so that their stabilizer orders
and the order of `K` are `(2, 2, n; 2n)`, `(2, 3, 3; 12)`, `(2, 3, 4; 24)` or `(2, 3, 5; 60)`: the
dihedral, tetrahedral, octahedral and icosahedral cases. -/
theorem exists_equiv_cardStabilizerOnOrbit_poles_of_card_orbitRel_quotient_poles_eq_three
    [Finite K] (h : Nat.card (orbitRel.Quotient K (poles K)) = 3) :
    ∃ e : Fin 3 ≃ orbitRel.Quotient K (poles K),
      cardStabilizerOnOrbit (e 0) = 2 ∧ cardStabilizerOnOrbit (e 1) = 2 ∧
          Nat.card K = 2 * cardStabilizerOnOrbit (e 2) ∨
        cardStabilizerOnOrbit (e 0) = 2 ∧ cardStabilizerOnOrbit (e 1) = 3 ∧
          cardStabilizerOnOrbit (e 2) = 3 ∧ Nat.card K = 12 ∨
        cardStabilizerOnOrbit (e 0) = 2 ∧ cardStabilizerOnOrbit (e 1) = 3 ∧
          cardStabilizerOnOrbit (e 2) = 4 ∧ Nat.card K = 24 ∨
        cardStabilizerOnOrbit (e 0) = 2 ∧ cardStabilizerOnOrbit (e 1) = 3 ∧
          cardStabilizerOnOrbit (e 2) = 5 ∧ Nat.card K = 60 := by
  classical
  have := Fintype.ofFinite (orbitRel.Quotient K (poles K))
  -- List the three orbits in increasing order of their stabilizer orders.
  let e₀ : Fin 3 ≃ orbitRel.Quotient K (poles K) :=
    (finCongr h.symm).trans (Finite.equivFin _).symm
  let σ := Tuple.sort fun i ↦ cardStabilizerOnOrbit (e₀ i)
  have hmono := Tuple.monotone_sort fun i ↦ cardStabilizerOnOrbit (e₀ i)
  refine ⟨σ.trans e₀, eq_of_inv_add_inv_add_inv_eq_one_add_two_div
    (one_lt_cardStabilizerOnOrbit_poles _) (hmono (by decide : (0 : Fin 3) ≤ 1))
    (hmono (by decide : (1 : Fin 3) ≤ 2)) Nat.card_pos ?_⟩
  have heq := finsum_one_sub_inv_cardStabilizerOnOrbit_poles_eq_two_sub_two_div_card K
  rw [finsum_eq_sum_of_fintype, ← (σ.trans e₀).sum_comp, Fin.sum_univ_three] at heq
  simp only [Equiv.trans_apply] at heq ⊢
  linarith

variable (K) in
/-- **A group of rotations with three orbits of poles has even order.** For an infinite group this
holds because `Nat.card K = 0`. -/
theorem even_card_of_card_orbitRel_quotient_poles_eq_three
    (h : Nat.card (orbitRel.Quotient K (poles K)) = 3) : Even (Nat.card K) := by
  obtain hK | hK := finite_or_infinite K
  · obtain ⟨e, he | he | he | he⟩ :=
      exists_equiv_cardStabilizerOnOrbit_poles_of_card_orbitRel_quotient_poles_eq_three K h
    · exact ⟨_, he.2.2.trans (two_mul _)⟩
    all_goals rw [he.2.2.2]; decide
  · simp [Nat.card_eq_zero_of_infinite]

/-- **A finite group of rotations of odd order fixes each of its poles**: it has two orbits of
poles, since three orbits force even order, so it is a group of rotations about a single axis. -/
theorem stabilizer_eq_top_of_odd_card (hK : Odd (Nat.card K)) (p : poles K) :
    stabilizer K p = ⊤ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rintro h; simp [h] at hK)
  have : Nontrivial K := nonempty_poles_iff.mp ⟨p⟩
  obtain h | h := card_orbitRel_quotient_poles_eq_two_or_three K
  · exact stabilizer_eq_top_of_card_orbitRel_quotient_poles_eq_two h p
  · exact absurd (even_card_of_card_orbitRel_quotient_poles_eq_three K h)
      (Nat.not_even_iff_odd.mpr hK)

end TauCeti.Matrix.SpecialOrthogonalGroup
