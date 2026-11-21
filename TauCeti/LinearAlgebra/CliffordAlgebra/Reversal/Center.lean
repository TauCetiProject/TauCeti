/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Center
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic

import TauCeti.LinearAlgebra.CliffordAlgebra.CentralSimple.Even
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

/-!
# Reversal on the centre of the even Clifford algebra

Over any commutative ring, reversal fixes the scalar coordinate of `a + b • ω` and multiplies
its orthogonal volume coordinate by `(-1) ^ (n.choose 2)`.

For a regular quadratic space of even positive dimension `n` over a field of characteristic
different from two, the centre of the even Clifford algebra is `K ⊕ Kω`. Reversal fixes scalars
and sends the volume element `ω` to `(-1) ^ (n.choose 2) • ω`. Thus it fixes the whole centre
when `n.choose 2` is even; otherwise its fixed elements in the centre are exactly the scalars.

The dimension-four and dimension-six specializations distinguish the two kinds of canonical
involution: in dimension four reversal fixes the discriminant algebra pointwise, while in
dimension six its central fixed elements are exactly the scalars. These statements hold whether the
discriminant algebra is a quadratic field or a split quadratic algebra. They determine the
base over which the canonical involution is linear in the low-dimensional unitary groups.

The centre is supplied by `CliffordAlgebra.mem_center_even_iff_exists_eq_add_smul_volume` and, in
odd dimension, `TauCeti.CliffordAlgebra.isCentral_even_of_odd_finrank`; the invertibility of the
volume element is supplied by `CliffordAlgebra.isUnit_prod_map_ι` and the reversal sign by
`CliffordAlgebra.reverse_prod_map_ι_of_pairwise_isOrtho`.

## Main results

* `TauCeti.CliffordAlgebra.reverse_add_smul_volume` and
  `TauCeti.CliffordAlgebra.reverseEven_add_smul_volume`: reversal on scalar/volume coordinates
  over any commutative ring.
* `TauCeti.CliffordAlgebra.reverseEven_prod_map_ι_of_pairwise_isOrtho`: reversal on an even
  orthogonal volume element.
* `TauCeti.CliffordAlgebra.reverse_add_smul_volume_eq_self_iff`: the fixed-point criterion for an
  anisotropic orthogonal volume element over a field with `2 ≠ 0`.
* `TauCeti.CliffordAlgebra.reverseEven_eq_self_iff_of_mem_center`: the central fixed-point criterion
  for a regular finite-dimensional quadratic space over a field with `2 ≠ 0`; in odd dimension
  the central elements of the even Clifford algebra are scalars, so the criterion is trivial.
* `TauCeti.CliffordAlgebra.forall_mem_center_reverseEven_eq_self_iff`: the criterion for reversal
  to fix the whole centre pointwise.
* `TauCeti.CliffordAlgebra.reverseEven_eq_self_of_mem_center_of_finrank_eq_four`: pointwise
  fixedness in dimension four.
* `TauCeti.CliffordAlgebra.reverseEven_eq_self_iff_of_mem_center_of_finrank_eq_six` and
  `TauCeti.CliffordAlgebra.exists_mem_center_reverseEven_ne_self_of_finrank_eq_six`: scalar fixed
  elements and nontrivial central action in dimension six.

## References

* M.-A. Knus, *Quadratic and Hermitian Forms over Rings* (1991), Chapter IV, §3.
* M.-A. Knus, A. Merkurjev, M. Rost, J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

namespace TauCeti.CliffordAlgebra

open _root_.CliffordAlgebra Module

universe u v

section CommRing

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {Q : QuadraticForm R M}

/-- Reversal multiplies the volume coordinate of an orthogonal list by its reversal sign,
while fixing the scalar coordinate. -/
theorem reverse_add_smul_volume {l : List M} (hl : l.Pairwise Q.IsOrtho) (a b : R) :
    reverse (algebraMap R (CliffordAlgebra Q) a + b • (l.map (ι Q)).prod) =
      algebraMap R (CliffordAlgebra Q) a +
        (((-1 : R) ^ l.length.choose 2) * b) • (l.map (ι Q)).prod := by
  simp [reverse_prod_map_ι_of_pairwise_isOrtho hl, smul_smul, mul_comm]

/-- Restricted reversal multiplies an even orthogonal volume element by its reversal sign. -/
@[simp] theorem reverseEven_prod_map_ι_of_pairwise_isOrtho {l : List M}
    (hl : l.Pairwise Q.IsOrtho) (hlen : Even l.length) :
    reverseEven Q ⟨(l.map (ι Q)).prod, prod_map_ι_mem_even_of_even_length hlen⟩ =
      ((-1 : R) ^ l.length.choose 2) •
        (⟨(l.map (ι Q)).prod, prod_map_ι_mem_even_of_even_length hlen⟩ : even Q) := by
  apply Subtype.ext
  simpa using reverse_prod_map_ι_of_pairwise_isOrtho hl

/-- Restricted reversal fixes the scalar coordinate and multiplies an even orthogonal volume
coordinate by its reversal sign. -/
theorem reverseEven_add_smul_volume {l : List M}
    (hl : l.Pairwise Q.IsOrtho) (hlen : Even l.length) (a b : R) :
    reverseEven Q (algebraMap R (even Q) a +
        b • ⟨(l.map (ι Q)).prod, prod_map_ι_mem_even_of_even_length hlen⟩) =
      algebraMap R (even Q) a +
        (((-1 : R) ^ l.length.choose 2) * b) •
          ⟨(l.map (ι Q)).prod, prod_map_ι_mem_even_of_even_length hlen⟩ := by
  simp only [map_add, map_smul, reverseEven_algebraMap,
    reverseEven_prod_map_ι_of_pairwise_isOrtho hl hlen, smul_smul, mul_comm]

end CommRing

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [NeZero (2 : K)] {Q : QuadraticForm K V}

/-- For an anisotropic orthogonal volume element, reversal fixes `a + b • ω` exactly when
its reversal sign is positive or its volume coordinate `b` vanishes. -/
theorem reverse_add_smul_volume_eq_self_iff
    {l : List V} (hl : l.Pairwise Q.IsOrtho)
    (hQl : ∀ v ∈ l, Q v ≠ 0)
    (a b : K) :
    reverse (algebraMap K (CliffordAlgebra Q) a + b • (l.map (ι Q)).prod) =
      algebraMap K (CliffordAlgebra Q) a + b • (l.map (ι Q)).prod ↔
        Even (l.length.choose 2) ∨ b = 0 := by
  rw [reverse_add_smul_volume hl]
  by_cases hsign : Even (l.length.choose 2)
  · simp [hsign, hsign.neg_one_pow]
  have hodd : Odd (l.length.choose 2) := Nat.not_even_iff_odd.mp hsign
  simp only [hsign, false_or, hodd.neg_one_pow, neg_one_mul, neg_smul]
  constructor
  · intro h
    -- cancelling the scalar summand leaves `2 b ω = 0`, and the volume element `ω` is a unit
    have hunit : IsUnit (l.map (ι Q)).prod :=
      isUnit_prod_map_ι (List.prod_ne_zero (by simpa using fun v hv h => hQl v hv h)).isUnit
    have h2 : (2 * b) • (l.map (ι Q)).prod = 0 := by
      rw [two_mul, add_smul]
      nth_rewrite 1 [← add_left_cancel h]
      exact neg_add_cancel _
    let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
    simpa [NeZero.ne (2 : K), hunit.ne_zero] using h2
  · rintro rfl
    simp

/-- In the centre of the even Clifford algebra of a regular finite-dimensional quadratic space, an
element is fixed by reversal exactly when `(finrank K V).choose 2` is even (the sign by which
reversal multiplies the volume element is positive) or it is a scalar. In odd dimension the centre
consists of scalars, so both sides hold. -/
theorem reverseEven_eq_self_iff_of_mem_center [FiniteDimensional K V] (hQ : Q.Nondegenerate)
    {x : even Q}
    (hx : x ∈ Subalgebra.center K (even Q)) :
    reverseEven Q x = x ↔
      Even ((finrank K V).choose 2) ∨ ∃ a : K, x = algebraMap K (even Q) a := by
  by_cases heven : Even (finrank K V)
  swap
  · obtain ⟨a, ha⟩ := Algebra.mem_bot.mp
      ((isCentral_even_of_odd_finrank hQ (Nat.not_even_iff_odd.mp heven)).out hx)
    exact iff_of_true (by rw [← ha]; exact reverseEven_algebraMap a) (Or.inr ⟨a, ha.symm⟩)
  let _ : Invertible (2 : K) := invertibleOfNonzero (NeZero.ne (2 : K))
  obtain ⟨l, hl, hlen, hspan, hQl⟩ := hQ.exists_list_pairwise_isOrtho
  have hle : Even l.length := hlen ▸ heven
  obtain ⟨a, b, hab⟩ :=
    (mem_center_even_iff_exists_eq_add_smul_volume hl hle hspan hQl).mp hx
  by_cases hsign : Even ((finrank K V).choose 2)
  · have hfix : reverseEven Q x = x := by
      have hxcoord : x = algebraMap K (even Q) a +
          b • ⟨(l.map (ι Q)).prod, prod_map_ι_mem_even_of_even_length hle⟩ :=
        Subtype.ext (by simpa using hab)
      rw [hxcoord, reverseEven_add_smul_volume hl hle, hlen, hsign.neg_one_pow, one_mul]
    exact iff_of_true hfix (Or.inl hsign)
  · simp only [hsign, false_or]
    constructor
    · intro hfix
      have hrev := congrArg (fun y : even Q => (y : CliffordAlgebra Q)) hfix
      rw [coe_reverseEven_apply, hab] at hrev
      have hb :=
        ((reverse_add_smul_volume_eq_self_iff hl hQl a b).mp hrev).resolve_left
          (by simpa only [hlen] using hsign)
      refine ⟨a, Subtype.ext ?_⟩
      simpa [hb] using hab
    · rintro ⟨a, rfl⟩
      simp

/-- Reversal fixes the centre of a regular even-dimensional even Clifford algebra pointwise
exactly when the sign of reversal on a volume element is positive. -/
theorem forall_mem_center_reverseEven_eq_self_iff (hQ : Q.Nondegenerate)
    (heven : Even (finrank K V)) (hpos : 0 < finrank K V) :
    (∀ x : even Q, x ∈ Subalgebra.center K (even Q) → reverseEven Q x = x) ↔
      Even ((finrank K V).choose 2) := by
  have : FiniteDimensional K V := .of_finrank_pos hpos
  constructor
  · intro hfix
    obtain ⟨ω, hω, hω_scalar⟩ := exists_mem_center_even_forall_ne_algebraMap hQ heven hpos
    rcases (reverseEven_eq_self_iff_of_mem_center hQ hω).mp (hfix ω hω) with
      hsign | ⟨a, ha⟩
    · exact hsign
    · exact False.elim (hω_scalar a ha)
  · intro hsign x hx
    exact (reverseEven_eq_self_iff_of_mem_center hQ hx).mpr (Or.inl hsign)

/-- In dimension four, the canonical reversal fixes every element of the discriminant algebra,
the centre of the even Clifford algebra. -/
theorem reverseEven_eq_self_of_mem_center_of_finrank_eq_four (hQ : Q.Nondegenerate)
    (hV : finrank K V = 4) {x : even Q} (hx : x ∈ Subalgebra.center K (even Q)) :
    reverseEven Q x = x := by
  have : FiniteDimensional K V := .of_finrank_pos (by omega)
  apply (reverseEven_eq_self_iff_of_mem_center hQ hx).mpr
  exact Or.inl (by simp [hV, Nat.choose_two_right, Nat.even_iff])

/-- In dimension six, the fixed elements of the discriminant algebra under canonical reversal
are exactly the scalars. -/
@[simp] theorem reverseEven_eq_self_iff_of_mem_center_of_finrank_eq_six (hQ : Q.Nondegenerate)
    (hV : finrank K V = 6) {x : even Q} (hx : x ∈ Subalgebra.center K (even Q)) :
    reverseEven Q x = x ↔ ∃ a : K, x = algebraMap K (even Q) a := by
  have : FiniteDimensional K V := .of_finrank_pos (by omega)
  simpa [hV, Nat.choose_two_right, Nat.even_iff] using
    reverseEven_eq_self_iff_of_mem_center hQ hx

/-- In dimension six, reversal acts nontrivially on the centre of the even Clifford algebra.
This includes both split and nonsplit discriminant algebras. -/
theorem exists_mem_center_reverseEven_ne_self_of_finrank_eq_six (hQ : Q.Nondegenerate)
    (hV : finrank K V = 6) :
    ∃ x : even Q, x ∈ Subalgebra.center K (even Q) ∧ reverseEven Q x ≠ x := by
  have hnot : ¬ ∀ x : even Q, x ∈ Subalgebra.center K (even Q) → reverseEven Q x = x := by
    rw [forall_mem_center_reverseEven_eq_self_iff hQ (by simp [hV, Nat.even_iff]) (by omega)]
    simp [hV, Nat.choose_two_right, Nat.even_iff]
  push Not at hnot
  exact hnot

end TauCeti.CliffordAlgebra
