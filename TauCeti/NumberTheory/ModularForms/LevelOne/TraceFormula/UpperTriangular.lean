/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.LinearAlgebra.Matrix.FixedDetMatrices
public import TauCeti.NumberTheory.ModularForms.LevelOne.TraceFormula.MatrixModule

/-!
# The upper-triangular representatives of `Γ \ ℳₙ`

For a nonzero integer `n`, every orbit of `SL(2, ℤ)` on the projective determinant-`n` matrix
module `ℳₙ` contains exactly one class of an upper-triangular matrix `(a b; 0 d)` with
`ad = n`, `0 < a` and `0 ≤ b < |d|`. Popa and Zagier write `ℳₙ^∞` for this set of
representatives and `Tₙ^∞` for its formal sum. The matrices themselves are Mathlib's
`FixedDetMatrices.reps n`, which `TauCeti.LinearAlgebra.Matrix.FixedDetMatrices` shows to be a
transversal of the `SL(2, ℤ)`-orbits of determinant-`n` matrices and counts
(`FixedDetMatrices.ncard_reps`). This file takes their projective classes, proves that they form a
transversal of the orbits of `ℳₙ`, and deduces `|Γ \ ℳₙ| = σ₁(|n|)`.

Popa and Zagier take `Γ = PSL(2, ℤ)`. Since `-1` acts trivially on `ℳₙ`, the `PSL(2, ℤ)`-orbits
are the `SL(2, ℤ)`-orbits, and this file works with the latter throughout: `Γ \ ℳₙ` denotes
`MulAction.orbitRel.Quotient SL(2, ℤ) ℳₙ`.

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
* `TauCeti.TraceFormulaMatrixModule.ncard_upperTriangularReps`: `|ℳₙ^∞| = σ₁(|n|)`.
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

/-- The elements of `ℳₙ^∞` are exactly the classes of the matrices in `FixedDetMatrices.reps n`. -/
theorem mem_upperTriangularReps {x : TraceFormulaMatrixModule n} :
    x ∈ upperTriangularReps n ↔ ∃ A ∈ FixedDetMatrices.reps n, mk A = x :=
  Iff.rfl

/-- The class of `A` lies in `ℳₙ^∞` exactly when `A` or `-A` is an upper-triangular
representative. -/
@[simp]
theorem mk_mem_upperTriangularReps {A : TraceFormulaMatrix n} :
    mk A ∈ upperTriangularReps n ↔ A ∈ FixedDetMatrices.reps n ∨ -A ∈ FixedDetMatrices.reps n := by
  simp [mem_upperTriangularReps, and_or_left, exists_or]

/-- Distinct upper-triangular representatives have distinct projective classes. -/
theorem mk_injOn_reps : Set.InjOn (mk (n := n)) (FixedDetMatrices.reps n) := by
  intro A hA B hB h
  -- the sign is fixed by the positivity of the upper-left entry
  refine (mk_eq_iff.mp h).resolve_right fun hAB ↦ hB.2.1.not_gt ?_
  simpa [hAB] using hA.2.1

/-- `ℳₙ^∞` is finite. -/
instance (n : ℤ) : Finite (upperTriangularReps n) :=
  Finite.Set.finite_image _ _

/-- `ℳₙ^∞` has `σ₁(|n|)` elements, as many as `FixedDetMatrices.reps n`. -/
@[simp]
theorem ncard_upperTriangularReps (n : ℤ) :
    (upperTriangularReps n).ncard = ArithmeticFunction.sigma 1 n.natAbs :=
  mk_injOn_reps.ncard_image.trans (FixedDetMatrices.ncard_reps n)

/-- **Existence of upper-triangular representatives**: for `n ≠ 0`, every element of `ℳₙ` can
be moved into `ℳₙ^∞` by `SL(2, ℤ)`. -/
theorem exists_smul_mem_upperTriangularReps (hn : n ≠ 0) (x : TraceFormulaMatrixModule n) :
    ∃ g : SL(2, ℤ), g • x ∈ upperTriangularReps n := by
  induction x using TraceFormulaMatrixModule.induction with | h A => ?_
  exact (FixedDetMatrices.exists_smul_mem_reps hn A).imp fun g hg ↦ ⟨g • A, hg, (smul_mk g A).symm⟩

/-- **Uniqueness of upper-triangular representatives**: if `g : SL(2, ℤ)` moves an element of
`ℳₙ^∞` into `ℳₙ^∞`, then it fixes that element. -/
theorem smul_eq_self_of_mem_upperTriangularReps {x : TraceFormulaMatrixModule n} {g : SL(2, ℤ)}
    (hx : x ∈ upperTriangularReps n) (hgx : g • x ∈ upperTriangularReps n) : g • x = x := by
  obtain ⟨A, hA, rfl⟩ := hx
  obtain ⟨B, hB, hBA⟩ := hgx
  -- `B = ±(g • A)`, and a sign is absorbed into the group element: `-(g • A) = (-g) • A`
  obtain ⟨g', hg'⟩ : ∃ g' : SL(2, ℤ), g' • A = B := (mk_eq_iff.mp (hBA.trans (smul_mk g A))).elim
    (⟨g, ·.symm⟩) fun h ↦ ⟨-g, Subtype.ext <| by simp [h, FixedDetMatrices.smul_coe]⟩
  rw [← hBA, FixedDetMatrices.eq_of_smul_eq_of_mem_reps hA hB hg']

/-- For `n ≠ 0`, `ℳₙ^∞` is a transversal of the `SL(2, ℤ)`-orbits of `ℳₙ` (Popa--Zagier,
Section 2): sending a representative to its orbit is a bijection onto `Γ \ ℳₙ`. -/
noncomputable def upperTriangularRepsEquiv (hn : n ≠ 0) :
    upperTriangularReps n ≃ MulAction.orbitRel.Quotient SL(2, ℤ) (TraceFormulaMatrixModule n) :=
  MulAction.transversalEquivOrbitRelQuotient (exists_smul_mem_upperTriangularReps hn)
    fun _ hx _ ↦ smul_eq_self_of_mem_upperTriangularReps hx

/-- The transversal bijection sends a representative to its orbit. -/
@[simp]
theorem upperTriangularRepsEquiv_apply (hn : n ≠ 0) (x : upperTriangularReps n) :
    upperTriangularRepsEquiv hn x = Quotient.mk'' (x : TraceFormulaMatrixModule n) :=
  MulAction.transversalEquivOrbitRelQuotient_apply _ _ x

/-- The inverse of the transversal bijection picks the representative in the given orbit. -/
theorem upperTriangularRepsEquiv_symm_mk_mem_orbit (hn : n ≠ 0) (x : TraceFormulaMatrixModule n) :
    ((upperTriangularRepsEquiv hn).symm (Quotient.mk'' x) : TraceFormulaMatrixModule n) ∈
      MulAction.orbit SL(2, ℤ) x :=
  MulAction.transversalEquivOrbitRelQuotient_symm_mk_mem_orbit _ _ x

/-- The inverse of the transversal bijection sends the orbit of a representative back to it. -/
@[simp]
theorem upperTriangularRepsEquiv_symm_mk (hn : n ≠ 0) (x : upperTriangularReps n) :
    (upperTriangularRepsEquiv hn).symm (Quotient.mk'' (x : TraceFormulaMatrixModule n)) = x :=
  MulAction.transversalEquivOrbitRelQuotient_symm_mk _ _ x

/-- For `n ≠ 0`, the orbit space `Γ \ ℳₙ` is finite. -/
theorem finite_orbitRel_quotient (hn : n ≠ 0) :
    Finite (MulAction.orbitRel.Quotient SL(2, ℤ) (TraceFormulaMatrixModule n)) :=
  .of_equiv _ (upperTriangularRepsEquiv hn)

/-- **The number of orbits** (Popa--Zagier, Section 2): for `n ≠ 0`, `Γ \ ℳₙ` has `σ₁(|n|)`
elements. -/
@[simp]
theorem card_orbitRel_quotient (hn : n ≠ 0) :
    Nat.card (MulAction.orbitRel.Quotient SL(2, ℤ) (TraceFormulaMatrixModule n)) =
      ArithmeticFunction.sigma 1 n.natAbs := by
  rw [← Nat.card_congr (upperTriangularRepsEquiv hn), Nat.card_coe_set_eq,
    ncard_upperTriangularReps]

end TraceFormulaMatrixModule

end TauCeti
