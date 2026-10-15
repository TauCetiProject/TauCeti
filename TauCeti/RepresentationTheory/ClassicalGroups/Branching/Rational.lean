/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.ClassicalGroups.Branching.Character
public import TauCeti.RepresentationTheory.ClassicalGroups.GelfandTsetlin.Count
public import TauCeti.RepresentationTheory.ClassicalGroups.WeylModule.Laurent

/-!
# Branching of rational Weyl-module characters

The rational Weyl module `V_λ = TauCeti.rationalWeylRep k (n + 1) λ` of a dominant weight `λ` of
`GL (n + 1)` has, on the diagonal torus `(kˣ)ⁿ × kˣ`, the character

`χ_λ(diag(t, z)) = ∑_{μ ≺ λ} z ^ (|λ| - |μ|) * χ_μ(diag t)`,

where `μ` runs over the dominant weights of `GL n` interlacing `λ`
(`λᵢ ≥ μᵢ ≥ λᵢ₊₁`, `TauCeti.interlacingWeights`) and `|λ| = ∑ᵢ λᵢ`.  The exponent is an integer
and may be negative: for `n = 0` and `λ = (-1)` the module is `det⁻¹` and the identity reads
`z⁻¹ = z⁻¹`.  Setting `z = 1` gives the character identity for the upper-left block inclusion
`GL n → GL (n + 1)`, each interlacing weight occurring once, and evaluating at the identity gives
the dimension recursion `dim V_λ = ∑_{μ ≺ λ} dim V_μ`.

This is the rational, `DominantWeight`-indexed form of the partition-indexed branching rule
`TauCeti.char_weylRepOfShape_diagonal_snoc`.  The interlacing now runs over integer sequences
rather than Young diagrams, and the two are matched by the determinant twist: writing
`λ = ν₀ + c·(1, …, 1)` with `c = λₙ` and `ν₀` the polynomial part of `λ`, the shapes interlacing
`ν₀` with at most `n` rows correspond to the weights interlacing `λ` by `ν ↦ ν + c·(1, …, 1)`,
and the twist `det ^ c` on `GL (n + 1)` restricts to `det ^ c` on `GL n` times `z ^ c`.

As for the partition form, these are identities of characters on the diagonal torus, not
isomorphisms of restricted representations.

## Main results

* `TauCeti.char_rationalWeylRep_diagonal_snoc` and its bundled form
  `TauCeti.char_rationalWeylFDRep_diagonal_snoc`: **the branching rule for rational Weyl
  characters** on the diagonal torus.
* `TauCeti.char_rationalWeylRep_glBlockSucc_diagGL` and its bundled form
  `TauCeti.char_rationalWeylFDRep_glBlockSucc_diagGL`: the character identity for restriction
  along the block inclusion.
* `TauCeti.finrank_rationalWeylFDRep_succ`: the dimension of `V_λ` is the sum of the dimensions
  of the `V_μ` with `μ` interlacing `λ`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course* (1991), Lecture 15, where the
  rational representations of `GL n` are the determinant twists of the polynomial ones.
* R. Goodman and N. R. Wallach, *Symmetry, Representations, and Invariants* (2009), Section 8.1:
  the branching law from `GL n` to `GL (n - 1)`.
-/

public section

open Module

namespace TauCeti

universe u

variable (k : Type u) [Field k] [CharZero k] (n : ℕ)

/-! ### Interlacing shapes and interlacing weights -/

section Reindex

variable {n}

/-- A Young diagram interlacing the polynomial part of a dominant weight `l` of `GL (n + 1)`,
with at most `n` rows, becomes a dominant weight interlacing `l` once shifted back by `lₙ`. -/
private theorem shift_weightOfShape_mem_interlacingWeights (l : DominantWeight (n + 1))
    {ν : YoungDiagram} (hν : ν ∈ YoungDiagram.interlacingShapes n l.detShiftShape) :
    (weightOfShape n ν).shift l.detShift ∈ interlacingWeights l := by
  obtain ⟨hint, -⟩ := YoungDiagram.mem_interlacingShapes.mp hν
  refine mem_interlacingWeights.mpr (interlaces_iff.mpr fun i => ?_)
  have hcast := l.natCast_rowLen_detShiftShape_add_detShift i.castSucc
  have hsucc := l.natCast_rowLen_detShiftShape_add_detShift i.succ
  have h₁ := hint.rowLen_succ_le i
  have h₂ := hint.rowLen_le i
  simp only [Fin.val_castSucc, Fin.val_succ] at hcast hsucc
  simp only [DominantWeight.shift_apply, weightOfShape_apply]
  omega

/-- The Young diagram of a dominant weight interlacing `l`, shifted down by `lₙ`, interlaces the
polynomial part of `l` and has at most `n` rows. -/
private theorem shape_shift_mem_interlacingShapes (l : DominantWeight (n + 1))
    {m : DominantWeight n} (hm : m ∈ interlacingWeights l) :
    (m.shift (-l.detShift)).shape ∈ YoungDiagram.interlacingShapes n l.detShiftShape := by
  have hint := interlaces_iff.mp (mem_interlacingWeights.mp hm)
  refine YoungDiagram.mem_interlacingShapes.mpr
    ⟨YoungDiagram.interlacedBy_iff.mpr fun i => ?_, DominantWeight.colLen_zero_shape_le _⟩
  rcases lt_or_ge i n with hi | hi
  · have h := hint ⟨i, hi⟩
    have hsucc := l.rowLen_detShiftShape ⟨i + 1, by omega⟩
    have hcast := l.rowLen_detShiftShape ⟨i, by omega⟩
    have hrow := (m.shift (-l.detShift)).rowLen_shape ⟨i, hi⟩
    simp only [Fin.castSucc_mk, Fin.succ_mk] at h
    simp only [DominantWeight.shift_apply] at hrow
    simp only at hsucc hcast hrow
    omega
  · rw [l.rowLen_detShiftShape_eq_zero_of_le (by omega : n + 1 ≤ i + 1),
      DominantWeight.rowLen_shape_eq_zero_of_le _ hi]
    exact ⟨le_rfl, Nat.zero_le _⟩

/-- A dominant weight interlacing `l` is at least `lₙ` everywhere, so subtracting `lₙ` leaves a
polynomial weight, which is recovered from its Young diagram. -/
private theorem weightOfShape_shape_shift_neg_detShift (l : DominantWeight (n + 1))
    {m : DominantWeight n} (hm : m ∈ interlacingWeights l) :
    weightOfShape n (m.shift (-l.detShift)).shape = m.shift (-l.detShift) := by
  ext i
  have h := ((interlaces_iff.mp (mem_interlacingWeights.mp hm)) i).2
  have hle := l.detShift_le i.succ
  rw [weightOfShape_apply, DominantWeight.rowLen_shape, DominantWeight.shift_apply]
  omega

end Reindex

/-! ### The branching rule -/

/-- The determinant twist matches the two exponents of `z`: for a shape `ν` with at most `n` rows
interlacing the polynomial part of `l`, the weight `ν + lₙ·(1, …, 1)` of `GL n` falls short of
`l` by `|ν₀| - |ν| + lₙ`, where `ν₀` is the polynomial part of `l`. -/
private theorem sum_sub_sum_shift_weightOfShape (l : DominantWeight (n + 1)) {ν : YoungDiagram}
    (hν : ν ∈ YoungDiagram.interlacingShapes n l.detShiftShape) :
    ∑ i, l.1 i - ∑ i, ((weightOfShape n ν).shift l.detShift).1 i =
      ((l.detShiftShape.card - ν.card : ℕ) : ℤ) + l.detShift := by
  obtain ⟨hint, hrows⟩ := YoungDiagram.mem_interlacingShapes.mp hν
  have hcard {N : ℕ} {μ : YoungDiagram} (hμ : μ.colLen 0 ≤ N) :
      (μ.card : ℤ) = ∑ i, (weightOfShape N μ).1 i := by
    conv_lhs => rw [← shape_weightOfShape hμ]
    exact DominantWeight.natCast_card_shape (isPolynomial_weightOfShape N μ)
  rw [Nat.cast_sub (Finset.card_le_card (YoungDiagram.cells_subset_iff.mpr hint.le)),
    hcard l.colLen_zero_detShiftShape_le, hcard hrows, DominantWeight.weightOfShape_detShiftShape]
  simp only [DominantWeight.shift_apply, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

/-- **The branching rule for rational Weyl characters.**  On diagonal matrices `diag(t, z)` of
`GL (n + 1)`, the character of the rational Weyl module of a dominant weight `l` is the sum, over
the dominant weights `m` of `GL n` interlacing `l`, of `z ^ (|l| - |m|)` times the character of the
rational Weyl module of `m` at `diag t`.  Each interlacing weight occurs once, and the exponent of
`z` is an integer that may be negative. -/
theorem char_rationalWeylRep_diagonal_snoc (l : DominantWeight (n + 1)) (t : Fin n → kˣ)
    (z : kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k (n + 1) l.detShiftShape).toSubmodule)
        (rationalWeylRep k (n + 1) l) (diagGL (Fin.snoc t z)) =
      ∑ m ∈ interlacingWeights l,
        (((z ^ (∑ i, l.1 i - ∑ i, m.1 i)) : kˣ) : k) *
          Representation.character (V := ↥(weylModuleOfShape k n m.detShiftShape).toSubmodule)
            (rationalWeylRep k n m) (diagGL t) := by
  rw [char_rationalWeylRep, det_diagGL, char_weylRepOfShape_diagonal_snoc, Finset.mul_sum]
  refine Finset.sum_nbij' (fun ν => (weightOfShape n ν).shift l.detShift)
    (fun m => (m.shift (-l.detShift)).shape)
    (fun ν hν => shift_weightOfShape_mem_interlacingWeights l hν)
    (fun m hm => shape_shift_mem_interlacingShapes l hm) (fun ν hν => ?_) (fun m hm => ?_)
    (fun ν hν => ?_)
  · rw [DominantWeight.shift_shift, add_neg_cancel, DominantWeight.shift_zero,
      shape_weightOfShape (YoungDiagram.mem_interlacingShapes.mp hν).2]
  · rw [weightOfShape_shape_shift_neg_detShift l hm, DominantWeight.shift_shift, neg_add_cancel,
      DominantWeight.shift_zero]
  · rw [char_rationalWeylRep_shift_diagonal,
      char_rationalWeylRep_weightOfShape_diagonal k n
        (YoungDiagram.mem_interlacingShapes.mp hν).2,
      sum_sub_sum_shift_weightOfShape n l hν, zpow_add, zpow_natCast, Fin.prod_snoc, mul_zpow]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring

/-- The branching rule for rational Weyl characters, for the bundled rational Weyl module. -/
theorem char_rationalWeylFDRep_diagonal_snoc (l : DominantWeight (n + 1)) (t : Fin n → kˣ)
    (z : kˣ) :
    (rationalWeylFDRep k (n + 1) l).character (diagGL (Fin.snoc t z)) =
      ∑ m ∈ interlacingWeights l,
        (((z ^ (∑ i, l.1 i - ∑ i, m.1 i)) : kˣ) : k) *
          (rationalWeylFDRep k n m).character (diagGL t) :=
  char_rationalWeylRep_diagonal_snoc k n l t z

/-- **Restriction of a rational Weyl character along the block inclusion.**  On the diagonal
torus of `GL n`, restricting the character of the rational Weyl module of `l` along
`GL n ↪ GL (n + 1)` gives the sum of the characters of the rational Weyl modules of the dominant
weights interlacing `l`, each occurring once. -/
theorem char_rationalWeylRep_glBlockSucc_diagGL (l : DominantWeight (n + 1)) (t : Fin n → kˣ) :
    Representation.character (V := ↥(weylModuleOfShape k (n + 1) l.detShiftShape).toSubmodule)
        (rationalWeylRep k (n + 1) l) (glBlockSucc k n (diagGL t)) =
      ∑ m ∈ interlacingWeights l,
        Representation.character (V := ↥(weylModuleOfShape k n m.detShiftShape).toSubmodule)
          (rationalWeylRep k n m) (diagGL t) := by
  rw [glBlockSucc_diagGL, char_rationalWeylRep_diagonal_snoc]
  simp

/-- Restriction of a rational Weyl character along the block inclusion, for the bundled rational
Weyl module. -/
theorem char_rationalWeylFDRep_glBlockSucc_diagGL (l : DominantWeight (n + 1))
    (t : Fin n → kˣ) :
    (rationalWeylFDRep k (n + 1) l).character (glBlockSucc k n (diagGL t)) =
      ∑ m ∈ interlacingWeights l, (rationalWeylFDRep k n m).character (diagGL t) :=
  char_rationalWeylRep_glBlockSucc_diagGL k n l t

/-- **The dimension recursion of branching**: the rational Weyl module of a dominant weight `l` of
`GL (n + 1)` has dimension the sum of the dimensions of the rational Weyl modules of the dominant
weights of `GL n` interlacing `l`.  This is the branching rule evaluated at the identity. -/
theorem finrank_rationalWeylFDRep_succ (l : DominantWeight (n + 1)) :
    finrank k (rationalWeylFDRep k (n + 1) l) =
      ∑ m ∈ interlacingWeights l, finrank k (rationalWeylFDRep k n m) := by
  have h := char_rationalWeylFDRep_glBlockSucc_diagGL k n l 1
  simp only [map_one, FDRep.char_one] at h
  exact_mod_cast h

end TauCeti
