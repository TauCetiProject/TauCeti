/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import TauCeti.GroupTheory.GroupAction.Burnside
public import TauCeti.LinearAlgebra.Matrix.SpecialOrthogonalGroup.Axis
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import TauCeti.LinearAlgebra.Matrix.OrthogonalGroup.Basic

/-!
# The poles of a group of rotations

Let `K` be a group of rotations of real three-space, a subgroup of `SO(3)`. A **pole** of `K` is a
unit vector fixed by some nonidentity element of `K`. Each nonidentity rotation fixes exactly two
unit vectors, the two ends `±p` of its axis (`Matrix.exists_setOf_mulVec_eq_self_eq_pair`), so a
finite `K` has finitely many poles. Conjugating a rotation by an element of `K` moves its axis by
that element, so `K` acts on its set of poles, and every nonidentity element of `K` fixes exactly
two poles.

Burnside's lemma then gives the **orbit equation** of the finite rotation groups: if `K` is finite
and `m₁, …, mₛ` are the orders of the stabilizers of the orbits of `K` on its poles, then

`∑ⱼ (1 - 1 / mⱼ) = 2 - 2 / |K|`.

Each stabilizer of a pole is nontrivial, so every term lies in `[1/2, 1)`, while the right-hand
side lies in `[1, 2)` for nontrivial `K`; hence a nontrivial finite group of rotations has two or
three orbits of poles. This is the counting step of Klein's classification of the finite
subgroups of `SO(3)`, whose solutions are the cyclic, dihedral, tetrahedral, octahedral and
icosahedral rotation groups. The trivial group is the only one without poles.

## Main declarations

* `Subgroup.poles`: the poles of a group of rotations.
* `Subgroup.mulVec_mem_poles`: rotating a pole by an element of the group gives a pole.
* `Subgroup.finite_poles`: a finite group of rotations has finitely many poles.
* `Subgroup.instMulActionPoles`: the action of the group on its poles.
* `Subgroup.card_fixedBy_poles`: every nonidentity element fixes exactly two poles.
* `Subgroup.sum_one_sub_one_div_card_stabilizer_poles`: the orbit equation.
* `Subgroup.poles_eq_empty_iff`: only the trivial group has no poles.
* `Subgroup.card_orbitRel_quotient_poles_eq_two_or_three`: a nontrivial finite group of rotations
  has two or three orbits of poles.

## References

* M. Artin, *Algebra*, second edition, Pearson, 2011, Section 6.12.
* M. A. Armstrong, *Groups and Symmetry*, Springer, 1988, Chapter 19.
-/

public section

open Matrix MulAction

namespace Subgroup

variable (K : Subgroup (specialOrthogonalGroup (Fin 3) ℝ))

/-- The **poles** of a group `K` of rotations of real three-space: the unit vectors fixed by some
nonidentity element of `K`. -/
def poles : Set (Fin 3 → ℝ) :=
  {x | x ⬝ᵥ x = 1 ∧ ∃ g ∈ K, g ≠ 1 ∧ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x = x}

variable {K}

/-- A pole of `K` is a unit vector fixed by a nonidentity element of `K`. -/
@[simp]
theorem mem_poles {x : Fin 3 → ℝ} :
    x ∈ K.poles ↔ x ⬝ᵥ x = 1 ∧ ∃ g ∈ K, g ≠ 1 ∧ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x = x :=
  Iff.rfl

/-- The antipode of a pole is a pole, of the same rotation. -/
theorem neg_mem_poles {x : Fin 3 → ℝ} (hx : x ∈ K.poles) : -x ∈ K.poles := by
  obtain ⟨hx1, g, hg, hg1, hgx⟩ := hx
  exact ⟨by rwa [neg_dotProduct, dotProduct_neg, neg_neg], g, hg, hg1, by rw [mulVec_neg, hgx]⟩

/-- Every unit vector fixed by a nonidentity element of `K` is a pole of `K`. -/
theorem setOf_mulVec_eq_self_subset_poles {g : specialOrthogonalGroup (Fin 3) ℝ} (hg : g ∈ K)
    (hg1 : g ≠ 1) :
    {x : Fin 3 → ℝ | x ⬝ᵥ x = 1 ∧ (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x = x} ⊆ K.poles :=
  fun _ ⟨hx1, hx⟩ ↦ ⟨hx1, g, hg, hg1, hx⟩

/-- Rotating a pole of `K` by an element `g` of `K` gives a pole of `K`: if `h` fixes `x`, then
`g h g⁻¹` fixes `g x`. -/
theorem mulVec_mem_poles {g : specialOrthogonalGroup (Fin 3) ℝ} (hg : g ∈ K)
    {x : Fin 3 → ℝ} (hx : x ∈ K.poles) : (g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x ∈ K.poles := by
  obtain ⟨hx1, h, hh, hh1, hhx⟩ := hx
  have hgo : (g : Matrix (Fin 3) (Fin 3) ℝ) ∈ orthogonalGroup (Fin 3) ℝ :=
    (mem_specialOrthogonalGroup_iff.mp g.2).1
  refine ⟨by rwa [mem_orthogonalGroup_iff_dotProduct_mulVec.mp hgo], g * h * g⁻¹,
    K.mul_mem (K.mul_mem hg hh) (K.inv_mem hg), fun h1 ↦ hh1 ?_, ?_⟩
  · rwa [mul_inv_eq_one, mul_eq_left] at h1
  · have hgg : ((g⁻¹ : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        ((g : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x) = x := by
      rw [mulVec_mulVec, ← Submonoid.coe_mul, inv_mul_cancel, OneMemClass.coe_one, one_mulVec]
    rw [Submonoid.coe_mul, Submonoid.coe_mul, ← mulVec_mulVec, ← mulVec_mulVec, hgg, hhx]

/-- A finite group of rotations has finitely many poles: each of its nonidentity elements
contributes the two ends of its axis. -/
theorem finite_poles [Finite K] : K.poles.Finite := by
  have h : K.poles ⊆ ⋃ g : K, {x | x ⬝ᵥ x = 1 ∧ (g : specialOrthogonalGroup (Fin 3) ℝ) ≠ 1 ∧
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x = x} :=
    fun x ⟨hx1, g, hg, hg1, hgx⟩ ↦ Set.mem_iUnion.mpr ⟨⟨g, hg⟩, hx1, hg1, hgx⟩
  refine (Set.finite_iUnion fun g ↦ ?_).subset h
  by_cases hg1 : (g : specialOrthogonalGroup (Fin 3) ℝ) = 1
  · simp [hg1]
  · obtain ⟨p, -, -, hp⟩ := exists_setOf_mulVec_eq_self_eq_pair
      (g : specialOrthogonalGroup (Fin 3) ℝ).2 fun h ↦ hg1 (Subtype.ext h)
    refine (Set.toFinite {p, -p}).subset fun x ⟨hx1, _, hx⟩ ↦ ?_
    rw [← hp]
    exact ⟨hx1, hx⟩

instance [Finite K] : Finite K.poles := K.finite_poles.to_subtype

/-- A group of rotations acts on its poles. -/
instance instMulActionPoles : MulAction K K.poles where
  smul g x := ⟨((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x,
    mulVec_mem_poles g.2 x.2⟩
  one_smul x := Subtype.ext (one_mulVec (x : Fin 3 → ℝ))
  mul_smul _ _ x := Subtype.ext (mulVec_mulVec (x : Fin 3 → ℝ) _ _).symm

@[simp]
theorem coe_smul_poles (g : K) (x : K.poles) :
    ((g • x : K.poles) : Fin 3 → ℝ) =
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x :=
  rfl

/-- Every nonidentity element of a group of rotations fixes exactly two of its poles, the two
ends of its axis. -/
theorem card_fixedBy_poles {g : K} (hg : g ≠ 1) : Nat.card (fixedBy K.poles g) = 2 := by
  have hg1 : (g : specialOrthogonalGroup (Fin 3) ℝ) ≠ 1 := fun h ↦ hg (Subtype.ext h)
  obtain ⟨p, hp1, -, hp⟩ := exists_setOf_mulVec_eq_self_eq_pair
    (g : specialOrthogonalGroup (Fin 3) ℝ).2 fun h ↦ hg1 (Subtype.ext h)
  have hpp : p ≠ -p := by
    intro h
    have h1 : (1 : ℝ) = -1 := by
      rw [← hp1]
      nth_rewrite 1 [h]
      rw [neg_dotProduct]
    norm_num at h1
  let e : fixedBy K.poles g ≃ {x : Fin 3 → ℝ | x ⬝ᵥ x = 1 ∧
      ((g : specialOrthogonalGroup (Fin 3) ℝ) : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x = x} :=
    { toFun x := ⟨x.1.1, x.1.2.1, by rw [← coe_smul_poles, mem_fixedBy.mp x.2]⟩
      invFun x := ⟨⟨x.1, setOf_mulVec_eq_self_subset_poles g.2 hg1 x.2⟩,
        mem_fixedBy.mpr (Subtype.ext (by rw [coe_smul_poles]; exact x.2.2))⟩
      left_inv _ := rfl
      right_inv _ := rfl }
  rw [Nat.card_congr e, hp, Nat.card_coe_set_eq, Set.ncard_pair hpp]

/-- **The orbit equation of a finite group of rotations.** If `m₁, …, mₛ` are the orders of the
stabilizers of the orbits of a finite group `K` of rotations on its poles, then
`∑ⱼ (1 - 1 / mⱼ) = 2 - 2 / |K|`. -/
theorem sum_one_sub_one_div_card_stabilizer_poles [Finite K]
    [Fintype (orbitRel.Quotient K K.poles)] :
    ∑ ω : orbitRel.Quotient K K.poles, (1 - 1 / (Nat.card (stabilizer K ω.out) : ℚ)) =
      2 - 2 / Nat.card K := by
  rw [TauCeti.sum_one_sub_one_div_card_stabilizer_eq fun g hg ↦ card_fixedBy_poles hg]
  push_cast
  ring

/-- A group of rotations has no poles exactly when it is trivial. -/
theorem poles_eq_empty_iff : K.poles = ∅ ↔ K = ⊥ := by
  refine ⟨fun h ↦ (eq_bot_iff_forall K).mpr fun g hg ↦ ?_, fun h ↦ ?_⟩
  · by_contra hg1
    obtain ⟨p, hp1, hp, -⟩ := exists_setOf_mulVec_eq_self_eq_pair g.2
      fun h ↦ hg1 (Subtype.ext h)
    exact (Set.eq_empty_iff_forall_notMem.mp h) p ⟨hp1, g, hg, hg1, hp⟩
  · subst h
    exact Set.eq_empty_iff_forall_notMem.mpr fun x ⟨_, g, hg, hg1, _⟩ ↦ hg1 (mem_bot.mp hg)

/-- The stabilizer of a pole of a finite group of rotations is nontrivial. -/
theorem one_lt_card_stabilizer_poles [Finite K] (x : K.poles) :
    1 < Nat.card (stabilizer K x) := by
  obtain ⟨-, g, hg, hg1, hgx⟩ := x.2
  have hmem : (⟨g, hg⟩ : K) ∈ stabilizer K x :=
    mem_stabilizer_iff.mpr (Subtype.ext (by rw [coe_smul_poles]; exact hgx))
  refine (one_lt_card_iff_ne_bot _).mpr fun h ↦ hg1 ?_
  rw [h, mem_bot] at hmem
  exact congrArg Subtype.val hmem

/-- **A nontrivial finite group of rotations has two or three orbits of poles.** In the orbit
equation every term `1 - 1 / mⱼ` lies in `[1/2, 1)`, while `2 - 2 / |K|` lies in `[1, 2)`. -/
theorem card_orbitRel_quotient_poles_eq_two_or_three [Finite K] (hK : K ≠ ⊥) :
    Nat.card (orbitRel.Quotient K K.poles) = 2 ∨ Nat.card (orbitRel.Quotient K K.poles) = 3 := by
  classical
  have := Fintype.ofFinite (orbitRel.Quotient K K.poles)
  have hsum := sum_one_sub_one_div_card_stabilizer_poles (K := K)
  have hN : (2 : ℚ) ≤ Nat.card K := by exact_mod_cast (one_lt_card_iff_ne_bot K).mpr hK
  have hlow (ω : orbitRel.Quotient K K.poles) :
      1 / 2 ≤ 1 - 1 / (Nat.card (stabilizer K ω.out) : ℚ) := by
    have h : (2 : ℚ) ≤ Nat.card (stabilizer K ω.out) := by
      exact_mod_cast one_lt_card_stabilizer_poles ω.out
    have : 1 / (Nat.card (stabilizer K ω.out) : ℚ) ≤ 1 / 2 :=
      one_div_le_one_div_of_le two_pos h
    linarith
  have hup (ω : orbitRel.Quotient K K.poles) :
      1 - 1 / (Nat.card (stabilizer K ω.out) : ℚ) < 1 := by
    have : (0 : ℚ) < Nat.card (stabilizer K ω.out) := by exact_mod_cast Nat.card_pos
    have : 0 < 1 / (Nat.card (stabilizer K ω.out) : ℚ) := one_div_pos.mpr this
    linarith
  have hne : (Finset.univ : Finset (orbitRel.Quotient K K.poles)).Nonempty := by
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr (poles_eq_empty_iff.not.mpr hK)
    exact ⟨Quotient.mk _ ⟨x, hx⟩, Finset.mem_univ _⟩
  -- Bound the orbit equation below by `s / 2` and above by `s`, for `s` the number of orbits.
  have h1 := Finset.card_nsmul_le_sum Finset.univ
    (fun ω : orbitRel.Quotient K K.poles ↦ 1 - 1 / (Nat.card (stabilizer K ω.out) : ℚ)) (1 / 2)
    fun ω _ ↦ hlow ω
  have h2 := Finset.sum_lt_sum_of_nonempty hne fun ω _ ↦ hup ω
  rw [hsum, Finset.card_univ, nsmul_eq_mul] at h1
  rw [hsum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h2
  have h3 : 2 / (Nat.card K : ℚ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hN
  have h4 : 0 < 2 / (Nat.card K : ℚ) := div_pos two_pos (by linarith)
  have hlt : Fintype.card (orbitRel.Quotient K K.poles) < 4 := by
    have : (Fintype.card (orbitRel.Quotient K K.poles) : ℚ) < 4 := by linarith
    exact_mod_cast this
  have hgt : 1 < Fintype.card (orbitRel.Quotient K K.poles) := by
    have : (1 : ℚ) < Fintype.card (orbitRel.Quotient K K.poles) := by linarith
    exact_mod_cast this
  rw [Nat.card_eq_fintype_card]
  omega

end Subgroup
