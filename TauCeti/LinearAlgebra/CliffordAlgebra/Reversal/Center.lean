/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Center
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic

import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# Reversal on the centre of the even Clifford algebra

For a regular quadratic space of even positive dimension `n` over a field of characteristic
different from two, the centre of the even Clifford algebra is `K ⊕ Kω`. Reversal fixes scalars
and sends the volume element `ω` to `(-1) ^ (n.choose 2) • ω`. Thus it fixes the whole centre
when `n.choose 2` is even; otherwise its fixed elements in the centre are exactly the scalars.

The dimension-four and dimension-six specializations distinguish the two kinds of canonical
involution: in dimension four reversal fixes the discriminant algebra pointwise, while in
dimension six it acts by its nontrivial conjugation. These statements hold whether the
discriminant algebra is a quadratic field or a split quadratic algebra. They determine the
base over which the canonical involution is linear in the low-dimensional unitary groups.

The centre and uniqueness of its scalar/volume coordinates are supplied by
`CliffordAlgebra.mem_center_even_iff_exists_eq_add_smul_volume` and
`CliffordAlgebra.add_smul_volume_injective_of_even_length`; the reversal sign is supplied by
`CliffordAlgebra.reverse_prod_map_ι_of_pairwise_isOrtho`.

## References

* M.-A. Knus, *Quadratic and Hermitian Forms over Rings* (1991), Chapter IV, §3.
* M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

namespace TauCeti

open _root_.CliffordAlgebra Module

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [NeZero (2 : K)] {Q : QuadraticForm K V}

/-- For an even anisotropic orthogonal volume element whose reversal sign is negative, reversal
fixes `a + b • ω` exactly when its volume coordinate `b` vanishes. -/
private theorem reverse_fixed_volume_coordinates {l : List V} (hl : l.Pairwise Q.IsOrtho)
    (hlen : Even l.length) (hne : l ≠ []) (hQl : ∀ v ∈ l, Q v ≠ 0)
    (hsign : Odd (l.length.choose 2)) (a b : K) :
    reverse (algebraMap K (CliffordAlgebra Q) a + b • (l.map (ι Q)).prod) =
      algebraMap K (CliffordAlgebra Q) a + b • (l.map (ι Q)).prod ↔ b = 0 := by
  simp only [map_add, map_smul, reverse.commutes, reverse_prod_map_ι_of_pairwise_isOrtho hl,
    hsign.neg_one_pow, smul_neg, neg_one_smul]
  constructor
  · intro h
    have hcoord : (a, -b) = (a, b) :=
      add_smul_volume_injective_of_even_length hl hlen hne hQl (by simpa using h)
    have htwo : (2 : K) * b = 0 := by
      have := congrArg Prod.snd hcoord
      linear_combination -this
    exact (mul_eq_zero.mp htwo).resolve_left (NeZero.ne (2 : K))
  · rintro rfl
    simp

variable [FiniteDimensional K V]

/-- In the centre of a regular even-dimensional Clifford algebra, an element is fixed by
reversal exactly when the volume sign is positive or the element is a scalar. -/
theorem reverseEven_eq_self_iff_of_mem_center (hQ : Q.Nondegenerate)
    (heven : Even (finrank K V)) (hpos : 0 < finrank K V) {x : even Q}
    (hx : x ∈ Subalgebra.center K (even Q)) :
    reverseEven Q x = x ↔
      Even ((finrank K V).choose 2) ∨ ∃ a : K, x = algebraMap K (even Q) a := by
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  obtain ⟨l, hl, hlen, hspan, hQl⟩ := hQ.exists_list_pairwise_isOrtho
  have hle : Even l.length := hlen ▸ heven
  have hne : l ≠ [] := List.length_pos_iff.mp (hlen ▸ hpos)
  obtain ⟨a, b, hab⟩ :=
    (mem_center_even_iff_exists_eq_add_smul_volume hl hle hne hspan hQl).mp hx
  by_cases hsign : Even ((finrank K V).choose 2)
  · have hfix : reverseEven Q x = x := by
      apply Subtype.ext
      simp [hab, reverse_prod_map_ι_of_pairwise_isOrtho hl, hlen, hsign.neg_one_pow]
    exact iff_of_true hfix (Or.inl hsign)
  · have hodd : Odd (l.length.choose 2) := by
      rw [hlen, ← Nat.not_even_iff_odd]
      exact hsign
    simp only [hsign, false_or]
    constructor
    · intro hfix
      have hrev := congrArg (fun y : even Q => (y : CliffordAlgebra Q)) hfix
      rw [coe_reverseEven_apply, hab] at hrev
      have hb := (reverse_fixed_volume_coordinates hl hle hne hQl hodd a b).mp hrev
      refine ⟨a, Subtype.ext ?_⟩
      simpa [hb] using hab
    · rintro ⟨a, rfl⟩
      simp

/-- Reversal fixes the centre of a regular even-dimensional even Clifford algebra pointwise
exactly when the sign of reversal on a volume element is positive. -/
theorem forall_reverseEven_eq_self_on_center_iff (hQ : Q.Nondegenerate)
    (heven : Even (finrank K V)) (hpos : 0 < finrank K V) :
    (∀ x : even Q, x ∈ Subalgebra.center K (even Q) → reverseEven Q x = x) ↔
      Even ((finrank K V).choose 2) := by
  constructor
  · intro hfix
    let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
    obtain ⟨l, hl, hlen, hspan, hQl⟩ := hQ.exists_list_pairwise_isOrtho
    have hle : Even l.length := hlen ▸ heven
    have hne : l ≠ [] := List.length_pos_iff.mp (hlen ▸ hpos)
    let ω : even Q := ⟨(l.map (ι Q)).prod, prod_map_ι_mem_even_of_even_length hle⟩
    have hω : ω ∈ Subalgebra.center K (even Q) :=
      prod_map_ι_mem_center_even_of_even_length hl hle hspan
    rcases (reverseEven_eq_self_iff_of_mem_center hQ heven hpos hω).mp (hfix ω hω) with
      hsign | ⟨a, ha⟩
    · exact hsign
    · exact False.elim (prod_map_ι_ne_algebraMap_of_even_length hl hle hne hQl a
        (congrArg (fun y : even Q => (y : CliffordAlgebra Q)) ha))
  · intro hsign x hx
    exact (reverseEven_eq_self_iff_of_mem_center hQ heven hpos hx).mpr (Or.inl hsign)

/-- In dimension four, the canonical reversal fixes every element of the discriminant algebra,
the centre of the even Clifford algebra. -/
@[simp]
theorem reverseEven_eq_self_of_mem_center_of_finrank_eq_four (hQ : Q.Nondegenerate)
    (hV : finrank K V = 4) {x : even Q} (hx : x ∈ Subalgebra.center K (even Q)) :
    reverseEven Q x = x := by
  apply (reverseEven_eq_self_iff_of_mem_center hQ (by simp [hV, Nat.even_iff]) (by omega) hx).mpr
  exact Or.inl (by simp [hV, Nat.choose_two_right, Nat.even_iff])

/-- In dimension six, the fixed elements of the discriminant algebra under canonical reversal
are exactly the scalars. Thus reversal is conjugation on that quadratic algebra. -/
theorem reverseEven_eq_self_iff_of_mem_center_of_finrank_eq_six (hQ : Q.Nondegenerate)
    (hV : finrank K V = 6) {x : even Q} (hx : x ∈ Subalgebra.center K (even Q)) :
    reverseEven Q x = x ↔ ∃ a : K, x = algebraMap K (even Q) a := by
  simpa [hV, Nat.choose_two_right, Nat.even_iff] using
    reverseEven_eq_self_iff_of_mem_center hQ (by simp [hV, Nat.even_iff]) (by omega) hx

/-- In dimension six, reversal acts nontrivially on the centre of the even Clifford algebra.
This includes both split and nonsplit discriminant algebras. -/
theorem exists_mem_center_reverseEven_ne_of_finrank_eq_six (hQ : Q.Nondegenerate)
    (hV : finrank K V = 6) :
    ∃ x : even Q, x ∈ Subalgebra.center K (even Q) ∧ reverseEven Q x ≠ x := by
  have hnot : ¬ ∀ x : even Q, x ∈ Subalgebra.center K (even Q) → reverseEven Q x = x := by
    rw [forall_reverseEven_eq_self_on_center_iff hQ (by simp [hV, Nat.even_iff]) (by omega)]
    simp [hV, Nat.choose_two_right, Nat.even_iff]
  push Not at hnot
  exact hnot

end TauCeti
