/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.LinearAlgebra.Matrix.FixedDetMatrices
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule

/-!
# The upper-triangular representatives of `Γ \ ℳₙ`

For a nonzero integer `n`, every orbit of `Γ = SL(2, ℤ)` on the projective determinant-`n`
matrix module `ℳₙ` contains exactly one class of an upper-triangular matrix `(a b; 0 d)` with
`ad = n`, `0 < a` and `0 ≤ b < |d|`. Popa and Zagier write `ℳₙ^∞` for this set of
representatives and `Tₙ^∞` for its formal sum. The matrices themselves are Mathlib's
`FixedDetMatrices.reps n`, so this file takes their projective classes and proves that they
form a transversal of the orbits. With the count `FixedDetMatrices.card_reps` of those
matrices this gives `|Γ \ ℳₙ| = σ₁(|n|)`.

## Main definitions

* `TauCeti.TraceFormulaMatrixModule.upperTriangularReps n`: the set `ℳₙ^∞` of projective classes
  of the matrices in `FixedDetMatrices.reps n`.
* `TauCeti.TraceFormulaMatrixModule.upperTriangularRepsEquiv`: for `n ≠ 0`, `ℳₙ^∞` is in
  bijection with the orbit space `Γ \ ℳₙ`.

## Main results

* `TauCeti.TraceFormulaMatrixModule.exists_smul_mem_upperTriangularReps`: for `n ≠ 0`, every
  `SL(2, ℤ)`-orbit of `ℳₙ` meets `ℳₙ^∞`.
* `TauCeti.TraceFormulaMatrixModule.smul_eq_self_of_mem_upperTriangularReps`: an element of
  `SL(2, ℤ)` that moves one element of `ℳₙ^∞` into `ℳₙ^∞` fixes it.
* `TauCeti.TraceFormulaMatrixModule.card_orbitRel_quotient`: `|Γ \ ℳₙ| = σ₁(|n|)`.

## References

* A. Popa and D. Zagier, *An elementary proof of the Eichler--Selberg trace formula*,
  J. Reine Angew. Math. 762 (2020), 105--122, arXiv:1711.00327, Section 2.
-/

public section

open Matrix
open scoped MatrixGroups

namespace TauCeti

/-! ### The representative set `ℳₙ^∞` -/

namespace TraceFormulaMatrixModule

variable {n : ℤ}

/-- Popa--Zagier's set `ℳₙ^∞` of upper-triangular representatives of `Γ \ ℳₙ`: the projective
classes of the matrices `(a b; 0 d)` with `ad = n`, `0 < a` and `0 ≤ b < |d|`. -/
def upperTriangularReps (n : ℤ) : Set (TraceFormulaMatrixModule n) :=
  mk '' FixedDetMatrices.reps n

/-- An element of `ℳₙ^∞` is the class of a matrix in `FixedDetMatrices.reps n`. -/
theorem mem_upperTriangularReps {x : TraceFormulaMatrixModule n} :
    x ∈ upperTriangularReps n ↔ ∃ A ∈ FixedDetMatrices.reps n, mk A = x :=
  Iff.rfl

/-- The class of `A` lies in `ℳₙ^∞` exactly when `A` or `-A` is an upper-triangular
representative. -/
theorem mk_mem_upperTriangularReps {A : TraceFormulaMatrix n} :
    mk A ∈ upperTriangularReps n ↔
      A ∈ FixedDetMatrices.reps n ∨ -A ∈ FixedDetMatrices.reps n := by
  simp only [mem_upperTriangularReps, mk_eq_iff]
  constructor
  · rintro ⟨B, hB, rfl | rfl⟩
    · exact Or.inl hB
    · exact Or.inr hB
  · rintro (h | h)
    · exact ⟨A, h, Or.inl rfl⟩
    · exact ⟨-A, h, Or.inr rfl⟩

/-- Distinct upper-triangular representatives have distinct projective classes: the sign is
fixed by the positivity of the upper-left entry. -/
theorem injOn_mk_reps : Set.InjOn (mk (n := n)) (FixedDetMatrices.reps n) := by
  intro A hA B hB h
  refine (mk_eq_iff.mp h).resolve_right fun hAB ↦ ?_
  have hA₀₀ := hA.2.1
  rw [hAB, TraceFormulaMatrix.val_neg, Matrix.neg_apply, neg_pos] at hA₀₀
  exact hA₀₀.not_gt hB.2.1

/-- `ℳₙ^∞` is finite, since `FixedDetMatrices.reps n` is. -/
instance (n : ℤ) : Finite (upperTriangularReps n) :=
  Finite.Set.finite_image _ _

/-- `ℳₙ^∞` has as many elements as `FixedDetMatrices.reps n`. -/
theorem card_upperTriangularReps (n : ℤ) :
    Nat.card (upperTriangularReps n) = Nat.card (FixedDetMatrices.reps n) :=
  Nat.card_image_of_injOn injOn_mk_reps

/-- **Existence of upper-triangular representatives**: for `n ≠ 0`, every element of `ℳₙ` can
be moved into `ℳₙ^∞` by `SL(2, ℤ)`. -/
theorem exists_smul_mem_upperTriangularReps (hn : n ≠ 0) (x : TraceFormulaMatrixModule n) :
    ∃ g : SL(2, ℤ), g • x ∈ upperTriangularReps n := by
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  obtain ⟨g, hg⟩ := FixedDetMatrices.exists_smul_mem_reps hn A
  exact ⟨g, g • A, hg, (smul_mk g A).symm⟩

/-- **Uniqueness of upper-triangular representatives**: if `g : SL(2, ℤ)` moves an element of
`ℳₙ^∞` into `ℳₙ^∞`, then it fixes that element. -/
theorem smul_eq_self_of_mem_upperTriangularReps {x : TraceFormulaMatrixModule n} {g : SL(2, ℤ)}
    (hx : x ∈ upperTriangularReps n) (hgx : g • x ∈ upperTriangularReps n) : g • x = x := by
  obtain ⟨A, hA, rfl⟩ := hx
  obtain ⟨B, hB, hBA⟩ := hgx
  rw [smul_mk, mk_eq_iff] at hBA
  rcases hBA with hBA | hBA
  · rw [smul_mk, ← hBA, FixedDetMatrices.eq_of_smul_eq_of_mem_reps hA hB hBA.symm]
  · have hneg : (-g) • A = B := by
      rw [hBA]
      apply FixedDetMatrices.ext'
      simp [FixedDetMatrices.smul_coe]
    have hAB := FixedDetMatrices.eq_of_smul_eq_of_mem_reps hA hB hneg
    rw [smul_mk, mk_eq_iff]
    exact Or.inr (neg_eq_iff_eq_neg.mpr (hAB.trans hBA)).symm

/-- Two elements of `ℳₙ^∞` in the same `SL(2, ℤ)`-orbit are equal. -/
theorem eq_of_mem_orbit_of_mem_upperTriangularReps {x y : TraceFormulaMatrixModule n}
    (hx : x ∈ upperTriangularReps n) (hy : y ∈ upperTriangularReps n)
    (h : y ∈ MulAction.orbit SL(2, ℤ) x) : x = y := by
  obtain ⟨g, rfl⟩ := h
  exact (smul_eq_self_of_mem_upperTriangularReps hx hy).symm

/-- For `n ≠ 0`, `ℳₙ^∞` is a transversal of the `SL(2, ℤ)`-orbits of `ℳₙ` (Popa--Zagier,
Section 2): sending a representative to its orbit is a bijection onto `Γ \ ℳₙ`. -/
noncomputable def upperTriangularRepsEquiv (hn : n ≠ 0) :
    upperTriangularReps n ≃ MulAction.orbitRel.Quotient SL(2, ℤ) (TraceFormulaMatrixModule n) :=
  Equiv.ofBijective (fun x ↦ Quotient.mk'' x.1) ⟨fun x y h ↦ Subtype.ext <|
    (eq_of_mem_orbit_of_mem_upperTriangularReps y.2 x.2 (Quotient.exact h)).symm,
    fun q ↦ q.inductionOn' fun x ↦ by
      obtain ⟨g, hg⟩ := exists_smul_mem_upperTriangularReps hn x
      exact ⟨⟨g • x, hg⟩, MulAction.orbitRel.Quotient.quotient_smul_eq⟩⟩

/-- The transversal bijection sends a representative to its orbit. -/
@[simp]
theorem upperTriangularRepsEquiv_apply (hn : n ≠ 0) (x : upperTriangularReps n) :
    upperTriangularRepsEquiv hn x = Quotient.mk'' (x : TraceFormulaMatrixModule n) :=
  (rfl)

/-- The inverse of the transversal bijection picks the representative in the given orbit. -/
theorem upperTriangularRepsEquiv_symm_mk_mem_orbit (hn : n ≠ 0)
    (x : TraceFormulaMatrixModule n) :
    ((upperTriangularRepsEquiv hn).symm (Quotient.mk'' x) : TraceFormulaMatrixModule n) ∈
      MulAction.orbit SL(2, ℤ) x := by
  have h := (upperTriangularRepsEquiv hn).apply_symm_apply (Quotient.mk'' x)
  rw [upperTriangularRepsEquiv_apply] at h
  exact Quotient.exact h

/-- The inverse of the transversal bijection sends the orbit of a representative back to it. -/
@[simp]
theorem upperTriangularRepsEquiv_symm_mk (hn : n ≠ 0) (x : upperTriangularReps n) :
    (upperTriangularRepsEquiv hn).symm (Quotient.mk'' (x : TraceFormulaMatrixModule n)) = x :=
  (upperTriangularRepsEquiv hn).symm_apply_apply x

/-- For `n ≠ 0`, the orbit space `Γ \ ℳₙ` is finite. -/
theorem finite_orbitRel_quotient (hn : n ≠ 0) :
    Finite (MulAction.orbitRel.Quotient SL(2, ℤ) (TraceFormulaMatrixModule n)) :=
  .of_equiv _ (upperTriangularRepsEquiv hn)

/-- **The number of orbits** (Popa--Zagier, Section 2): for `n ≠ 0`, `Γ \ ℳₙ` has `σ₁(|n|)`
elements. -/
theorem card_orbitRel_quotient (hn : n ≠ 0) :
    Nat.card (MulAction.orbitRel.Quotient SL(2, ℤ) (TraceFormulaMatrixModule n)) =
      ArithmeticFunction.sigma 1 n.natAbs := by
  rw [← Nat.card_congr (upperTriangularRepsEquiv hn), card_upperTriangularReps,
    FixedDetMatrices.card_reps hn]

end TraceFormulaMatrixModule

end TauCeti
