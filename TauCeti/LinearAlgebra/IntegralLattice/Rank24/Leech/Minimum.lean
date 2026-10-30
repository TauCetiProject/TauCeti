/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Rank24.Leech.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minimum

/-!
# The congruence model of the Leech lattice and its minimum

The Leech lattice `Λ ⊆ ℚ^(Fin 24)`, glued from the Golay Construction B lattice `K` along the odd
shift `s = (-3/2, 1/2, …, 1/2)`, has the following integral description. A vector `x` lies in `Λ`
exactly when `x = a / 2` for an integer vector `a = 2b + m 𝟙` with `m ∈ {0, 1}`, the reduction of
`b` modulo two a Golay codeword, and `∑ aᵢ ≡ 4m (mod 8)`. The case `m = 0` is the half-lattice `K`
itself; the case `m = 1` is the coset `s + K`, since `a / 2 - s` is the integer vector `b + 2 e₀`.

In these coordinates the norm, the dot product halved, is `B(x, x) = ∑ aᵢ² / 8`. The four-case
bound `∑ aᵢ² ≥ 32` for nonzero admissible `a`, which uses only the minimum distance `8` and the
divisibility by four of the Golay weights, then shows that every nonzero vector of `Λ` has norm
at least `4`. The shift `s` has norm exactly `4`, so the minimum of the Leech lattice is `4`. In
particular the Leech lattice has no roots: it has no vector of norm `2`, and its root sublattice
is zero. No theta series, sphere-packing bound, or uniqueness theorem is used.

## Main declarations

* `TauCeti.mem_leechLattice_carrier_iff_exists`: the congruence model of the Leech lattice.
* `TauCeti.leechLattice_norm_intCast_div_two`: the norm `∑ aᵢ² / 8` in congruence coordinates.
* `TauCeti.four_le_norm_leechLattice`: every nonzero vector of the Leech lattice has norm `≥ 4`.
* `TauCeti.minimum_leechLattice`: the minimum of the Leech lattice is `4`.
* `TauCeti.vectorsOfNorm_two_leechLattice` and `TauCeti.span_vectorsOfNorm_two_leechLattice`:
  the Leech lattice has no roots, and its root sublattice is zero.

## References

* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 4, §11, and
  Chapter 10, §1.
* R. A. Wilson, *The Finite Simple Groups*, §5.4.
-/

public section

namespace TauCeti

open BinaryGolay IntegralLattice

/-- A vector `b` of the even congruence class: `2b / 2 = b` lies in the Golay Construction B
lattice exactly when `b` reduces to a Golay codeword and `∑ 2bᵢ ≡ 0 (mod 8)`. -/
private theorem even_mem_constructionBLattice_carrier_iff (b : Fin 24 → ℤ) :
    (fun i ↦ ((2 * b i + 0 : ℤ) : ℚ) / 2) ∈ constructionBLattice.carrier ↔
      (fun i ↦ (b i : ZMod 2)) ∈ code ∧ ∑ i, (2 * b i + 0) ≡ 4 * 0 [ZMOD 8] := by
  have hx : (fun i ↦ ((2 * b i + 0 : ℤ) : ℚ) / 2) = fun i ↦ (b i : ℚ) := by
    funext i
    push_cast
    ring
  rw [hx, constructionBLattice_carrier, ConstructionB.intCast_mem_lattice]
  refine and_congr Iff.rfl ?_
  simp only [add_zero, mul_zero, ← Finset.mul_sum, Int.ModEq]
  omega

/-- A vector `b` of the odd congruence class: `(2b + 𝟙) / 2` differs from the Leech shift by an
element of the Golay Construction B lattice exactly when `b` reduces to a Golay codeword and
`∑ (2bᵢ + 1) ≡ 4 (mod 8)`. The difference is the integer vector `b + 2 e₀`. -/
private theorem odd_sub_leechShift_mem_constructionBLattice_carrier_iff (b : Fin 24 → ℤ) :
    (fun i ↦ ((2 * b i + 1 : ℤ) : ℚ) / 2) - leechShift ∈ constructionBLattice.carrier ↔
      (fun i ↦ (b i : ZMod 2)) ∈ code ∧ ∑ i, (2 * b i + 1) ≡ 4 * 1 [ZMOD 8] := by
  have hx : (fun i ↦ ((2 * b i + 1 : ℤ) : ℚ) / 2) - leechShift =
      fun i ↦ ((b i + if i = 0 then 2 else 0 : ℤ) : ℚ) := by
    funext i
    by_cases hi : i = 0
    · subst hi
      simp only [Pi.sub_apply, leechShift_zero, ite_true]
      push_cast
      ring
    · simp only [Pi.sub_apply, leechShift_of_ne_zero hi, hi, ite_false]
      push_cast
      ring
  have hred : (fun i ↦ ((b i + if i = 0 then 2 else 0 : ℤ) : ZMod 2)) =
      fun i ↦ (b i : ZMod 2) := by
    funext i
    split_ifs
    · simp [CharTwo.two_eq_zero]
    · simp
  rw [hx, constructionBLattice_carrier, ConstructionB.intCast_mem_lattice, hred]
  refine and_congr Iff.rfl ?_
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Int.ModEq]
  omega

/-- **The congruence model of the Leech lattice.** A vector `x` lies in the Leech lattice exactly
when `x = a / 2` for an integer vector `a = 2b + m 𝟙` with `m ∈ {0, 1}`, `b` reducing to a Golay
codeword modulo two, and `∑ aᵢ ≡ 4m (mod 8)`. -/
theorem mem_leechLattice_carrier_iff_exists (x : Fin 24 → ℚ) :
    x ∈ leechLattice.carrier ↔
      ∃ m : ℤ, (m = 0 ∨ m = 1) ∧ ∃ b : Fin 24 → ℤ, (fun i ↦ (b i : ZMod 2)) ∈ code ∧
        ∑ i, (2 * b i + m) ≡ 4 * m [ZMOD 8] ∧ x = fun i ↦ ((2 * b i + m : ℤ) : ℚ) / 2 := by
  constructor
  · rw [mem_leechLattice_carrier_iff]
    rintro (hx | hx)
    · -- The half-lattice: `x` is an integer vector `b`, and `m = 0`.
      obtain ⟨b, -, rfl⟩ := (ConstructionA.mem_lattice 2).mp
        (ConstructionB.lattice_le code (constructionBLattice_carrier ▸ hx))
      have hb : (fun i ↦ (b i : ℚ)) = fun i ↦ ((2 * b i + 0 : ℤ) : ℚ) / 2 := by
        funext i
        push_cast
        ring
      rw [hb] at hx ⊢
      obtain ⟨hb, hsum⟩ := (even_mem_constructionBLattice_carrier_iff b).mp hx
      exact ⟨0, Or.inl rfl, b, hb, hsum, rfl⟩
    · -- The odd coset: `x - s` is an integer vector `y`, and `x = (2b + 𝟙) / 2` with
      -- `b = y - 2 e₀`.
      obtain ⟨y, -, hy⟩ := (ConstructionA.mem_lattice 2).mp
        (ConstructionB.lattice_le code (constructionBLattice_carrier ▸ hx))
      set b : Fin 24 → ℤ := fun i ↦ y i - if i = 0 then 2 else 0
      have hxb : x = fun i ↦ ((2 * b i + 1 : ℤ) : ℚ) / 2 := by
        funext i
        have hi := congrFun hy i
        simp only [Pi.sub_apply] at hi
        by_cases h0 : i = 0
        · subst h0
          simp only [b, ite_true, leechShift_zero] at hi ⊢
          push_cast
          linarith
        · simp only [b, h0, ite_false, leechShift_of_ne_zero h0] at hi ⊢
          push_cast
          linarith
      rw [hxb] at hx
      obtain ⟨hb, hsum⟩ := (odd_sub_leechShift_mem_constructionBLattice_carrier_iff b).mp hx
      exact ⟨1, Or.inr rfl, b, hb, hsum, hxb⟩
  · rintro ⟨m, hm | hm, b, hb, hsum, rfl⟩ <;> subst hm <;> rw [mem_leechLattice_carrier_iff]
    · exact Or.inl ((even_mem_constructionBLattice_carrier_iff b).mpr ⟨hb, hsum⟩)
    · exact Or.inr ((odd_sub_leechShift_mem_constructionBLattice_carrier_iff b).mpr ⟨hb, hsum⟩)

/-- **The norm in congruence coordinates**: the Leech lattice norm of `a / 2` is `∑ aᵢ² / 8`. -/
theorem leechLattice_norm_intCast_div_two (a : Fin 24 → ℤ) :
    leechLattice.norm (fun i ↦ (a i : ℚ) / 2) = ((∑ i, a i ^ 2 : ℤ) : ℚ) / 8 := by
  rw [norm_apply, leechLattice_form, ConstructionA.form_apply, dotProduct]
  push_cast
  rw [Finset.sum_div, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  ring

/-- **Every nonzero vector of the Leech lattice has norm at least four.** In congruence
coordinates `x = a / 2` this is the four-case bound `∑ aᵢ² ≥ 32`. -/
theorem four_le_norm_leechLattice {x : Fin 24 → ℚ} (hx : x ∈ leechLattice.carrier)
    (hne : x ≠ 0) : 4 ≤ leechLattice.norm x := by
  obtain ⟨m, hm, b, hb, hsum, rfl⟩ := (mem_leechLattice_carrier_iff_exists x).mp hx
  have ha : (fun i ↦ 2 * b i + m) ≠ 0 := by
    intro h
    refine hne (funext fun i ↦ ?_)
    have hi : 2 * b i + m = 0 := congrFun h i
    simp [hi]
  have h32 : ((32 : ℤ) : ℚ) ≤ ((∑ i, (2 * b i + m) ^ 2 : ℤ) : ℚ) := by
    exact_mod_cast thirtyTwo_le_sum_sq hm hb hsum ha
  rw [leechLattice_norm_intCast_div_two (fun i ↦ 2 * b i + m)]
  push_cast at h32 ⊢
  linarith

/-- The Leech lattice is nontrivial: it contains the nonzero odd shift. -/
instance instNontrivialLeechLattice : Nontrivial leechLattice :=
  nontrivial_of_ne ⟨leechShift, leechShift_mem_leechLattice_carrier⟩ 0
    fun h ↦ leechShift_ne_zero (congrArg Subtype.val h)

/-- **The minimum of the Leech lattice is four**: every nonzero vector has norm at least `4`, and
the odd shift has norm exactly `4`. -/
@[simp]
theorem minimum_leechLattice : leechLattice.minimum = 4 := by
  have hleast :
      IsLeast {k : ℤ | ∃ x : leechLattice, x ≠ 0 ∧ leechLattice.integralNorm x = k} 4 := by
    refine ⟨⟨⟨leechShift, leechShift_mem_leechLattice_carrier⟩,
      fun h ↦ leechShift_ne_zero (congrArg Subtype.val h), ?_⟩, ?_⟩
    · have h := leechLattice.integralNorm_cast ⟨leechShift, leechShift_mem_leechLattice_carrier⟩
      rw [norm_apply, leechLattice_form_leechShift_leechShift] at h
      exact_mod_cast h
    · rintro k ⟨x, hx, rfl⟩
      have h := four_le_norm_leechLattice x.2 fun h ↦ hx (Subtype.ext h)
      rw [← leechLattice.integralNorm_cast x] at h
      exact_mod_cast h
  exact_mod_cast isPosDef_leechLattice.isPosSemidef.isLeast_minimum.unique hleast

/-- **The Leech lattice has no roots**: it has no vector of norm `2`. -/
@[simp]
theorem vectorsOfNorm_two_leechLattice : leechLattice.vectorsOfNorm 2 = ∅ :=
  isPosDef_leechLattice.isPosSemidef.vectorsOfNorm_eq_empty_of_lt_minimum two_ne_zero
    (by rw [minimum_leechLattice]; norm_num)

/-- **The root sublattice of the Leech lattice is zero**: the span of its norm-`2` vectors in the
ambient space is trivial. -/
theorem span_vectorsOfNorm_two_leechLattice :
    Submodule.span ℤ
      ((fun x : leechLattice ↦ (x : Fin 24 → ℚ)) '' leechLattice.vectorsOfNorm 2) = ⊥ := by
  rw [vectorsOfNorm_two_leechLattice, Set.image_empty, Submodule.span_empty]

end TauCeti
