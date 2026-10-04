/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.LinearAlgebra.StdBasis
public import TauCeti.Combinatorics.Brauer.TwoStrands
import Mathlib.Algebra.Algebra.Operations
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# The Brauer algebra on two strands

The Brauer algebra `B_k(δ)` is the free module on the Brauer diagrams of
`TauCeti/Combinatorics/Brauer/Diagram.lean`, with the **loop-weighted stacking**
`D₁ * D₂ = δ ^ middleLoopCount D₁ D₂ • composeDiagram D₁ D₂` as its multiplication.  This file
builds it on **two** strands, where the three diagrams

`1` (two through strands), `s` (the crossing), and `e` (the bottom cap with the top cup)

are all of them (`TauCeti.BrauerDiagram.univ_two`) and the loop count is known exactly
(`TauCeti.middleLoopCount_two`): a loop closes up in the middle only in the product `e * e`, where
exactly one does.  So the multiplication table of `B₂(δ)` is

`s * s = 1`,  `s * e = e = e * s`,  `e * e = δ • e`,

and `TauCeti.BrauerAlgebraTwo` is the `R`-algebra those relations present, free of rank
`(2 * 2 - 1)‼ = 3` on the diagram basis.

## From the presentation to the diagram basis

The algebra is built as a quotient of the free algebra by the relations, as
`TauCeti.TemperleyLieb` is, so the universal property `TauCeti.BrauerAlgebraTwo.lift` comes with
it: an assignment of `s` and `e` satisfying the four relations extends uniquely to an algebra map
out of `B₂(δ)`.  The presentation is then tied back to the diagrams in two steps.

* `TauCeti.BrauerAlgebraTwo.diagram` sends each of the three Brauer diagrams on two strands to the
  corresponding element, and `TauCeti.BrauerAlgebraTwo.diagram_mul_diagram` says that the
  multiplication of `B₂(δ)` **is** the loop-weighted stacking of diagrams.  This is the statement
  the relations exist for, and the only place the diagram combinatorics is used.
* `TauCeti.BrauerAlgebraTwo.basis` is the diagram basis.  Spanning holds because the span of the
  three elements is already a subalgebra, and independence is read off the left-regular
  representation `TauCeti.BrauerAlgebraTwo.regularRep` on `3 × 3` matrices, whose matrices for `s`
  and `e` have the entries that separate `1`, `s` and `e`.  The presentation alone cannot see
  independence -- it is what rules out a collapse of the presented algebra -- so the matrices are
  genuinely needed.

## Two strands, not `k`

Only the two-strand algebra is built here, because for general `k` the loop-weighted stacking is
not yet known to be associative.  Associativity needs the stacking law
`TauCeti.composeDiagram_assoc`, which is available, *together with* the matching loop-count
identity `middleLoopCount (composeDiagram D₁ D₂) D₃ + middleLoopCount D₁ D₂ =
middleLoopCount D₁ (composeDiagram D₂ D₃) + middleLoopCount D₂ D₃`, which is not: it is the
"`compose_assoc` with matching loop-count bookkeeping" that Layer 9 of the Schur--Weyl roadmap
lists as its own build item, and only its special cases are proved so far (in
`TauCeti/Combinatorics/Brauer/Generator.lean` and
`TauCeti/Combinatorics/Brauer/Relations.lean`).  On two strands no such identity is needed: the
four relations above are a presentation, and `TauCeti.middleLoopCount_two` computes every loop
count outright.

## Main definitions

* `TauCeti.BrauerAlgebraTwo.Rel`: the four defining relations, as a relation on the free algebra.
* `TauCeti.BrauerAlgebraTwo`: the Brauer algebra on two strands with loop value `δ`.
* `TauCeti.BrauerAlgebraTwo.s` and `TauCeti.BrauerAlgebraTwo.e`: the crossing and the cap-cup
  generator.
* `TauCeti.BrauerAlgebraTwo.lift`: the universal property of the presentation.
* `TauCeti.BrauerAlgebraTwo.diagram`: the element of `B₂(δ)` attached to a Brauer diagram.
* `TauCeti.BrauerAlgebraTwo.regularRep`: the left-regular representation on `3 × 3` matrices.
* `TauCeti.BrauerAlgebraTwo.basis`: the diagram basis of `B₂(δ)`.

## Main results

* `TauCeti.BrauerAlgebraTwo.s_mul_self`, `TauCeti.BrauerAlgebraTwo.e_mul_self`,
  `TauCeti.BrauerAlgebraTwo.s_mul_e`, `TauCeti.BrauerAlgebraTwo.e_mul_s`: the multiplication
  table.
* `TauCeti.BrauerAlgebraTwo.diagram_mul_diagram`: **the multiplication is the loop-weighted
  stacking of Brauer diagrams**, with `TauCeti.BrauerAlgebraTwo.diagram_permToBrauer_mul` the
  corollary that the permutation diagrams multiply as their permutations do.
* `TauCeti.BrauerAlgebraTwo.basis`, `TauCeti.BrauerAlgebraTwo.finrank_eq_three`: `B₂(δ)` is free
  of rank `(2 * 2 - 1)‼ = 3` on the Brauer diagrams on two strands.
* `TauCeti.BrauerAlgebraTwo.algebraMap_injective`: the base ring embeds, so the presentation does
  not collapse.

## References

* [R. Brauer, *On algebras which are connected with the semisimple continuous groups*][brauer1937],
  Annals of Mathematics 38 (1937), 857-872.
* [Schur--Weyl roadmap](https://github.com/TauCetiProject/TauCetiRoadmap/blob/main/TauCetiRoadmap/RepresentationTheory/SchurWeyl/README.md),
  Layer 9, and its `O(3)` acceptance criterion on `(ℂ³)^{⊗2}`, whose algebra side is the
  three-dimensional `B₂(δ)` built here.
-/

public section

open scoped Nat

namespace TauCeti

variable (R : Type*) (δ : R)

namespace BrauerAlgebraTwo

/-- The defining relations of the Brauer algebra on two strands with loop value `δ`, as a relation
on the free algebra over two generators: the generator `0` is the crossing `s` and the generator
`1` the cap-cup diagram `e`.  The crossing is an involution, the cap-cup diagram is idempotent up
to the loop value, and the crossing is absorbed by the cap-cup diagram from either side. -/
inductive Rel [CommSemiring R] : FreeAlgebra R (Fin 2) → FreeAlgebra R (Fin 2) → Prop
  | s_mul_self : Rel (FreeAlgebra.ι R 0 * FreeAlgebra.ι R 0) 1
  | e_mul_self : Rel (FreeAlgebra.ι R 1 * FreeAlgebra.ι R 1) (δ • FreeAlgebra.ι R 1)
  | s_mul_e : Rel (FreeAlgebra.ι R 0 * FreeAlgebra.ι R 1) (FreeAlgebra.ι R 1)
  | e_mul_s : Rel (FreeAlgebra.ι R 1 * FreeAlgebra.ι R 0) (FreeAlgebra.ι R 1)

end BrauerAlgebraTwo

/-- The **Brauer algebra on two strands** over `R` with loop value `δ`: the free `R`-algebra on the
crossing and the cap-cup diagram, modulo `TauCeti.BrauerAlgebraTwo.Rel`. -/
@[expose] def BrauerAlgebraTwo [CommSemiring R] : Type _ := RingQuot (BrauerAlgebraTwo.Rel R δ)

instance [CommSemiring R] : Semiring (BrauerAlgebraTwo R δ) :=
  inferInstanceAs (Semiring (RingQuot (BrauerAlgebraTwo.Rel R δ)))

instance {S : Type*} [CommRing S] (ε : S) : Ring (BrauerAlgebraTwo S ε) :=
  inferInstanceAs (Ring (RingQuot (BrauerAlgebraTwo.Rel S ε)))

instance [CommSemiring R] : Algebra R (BrauerAlgebraTwo R δ) :=
  inferInstanceAs (Algebra R (RingQuot (BrauerAlgebraTwo.Rel R δ)))

namespace BrauerAlgebraTwo

variable [CommSemiring R]

/-- The quotient map from the free algebra to the Brauer algebra on two strands. -/
def mkAlgHom : FreeAlgebra R (Fin 2) →ₐ[R] BrauerAlgebraTwo R δ :=
  RingQuot.mkAlgHom R (Rel R δ)

variable {R}

/-- The **crossing** `s`, the Brauer diagram on two strands whose two through strands cross. -/
def s : BrauerAlgebraTwo R δ := mkAlgHom R δ (FreeAlgebra.ι R 0)

/-- The **cap-cup diagram** `e`, the Brauer diagram on two strands with a cap joining its two
bottom points and a cup joining its two top points. -/
def e : BrauerAlgebraTwo R δ := mkAlgHom R δ (FreeAlgebra.ι R 1)

variable {δ}

@[simp]
theorem mkAlgHom_ι_zero : mkAlgHom R δ (FreeAlgebra.ι R 0) = s δ := (rfl)

@[simp]
theorem mkAlgHom_ι_one : mkAlgHom R δ (FreeAlgebra.ι R 1) = e δ := (rfl)

/-- Every element of the Brauer algebra on two strands is represented by a free-algebra
element. -/
theorem mkAlgHom_surjective : Function.Surjective (mkAlgHom R δ) :=
  RingQuot.mkAlgHom_surjective _ _

/-- Related elements of the free algebra have the same image in the Brauer algebra. -/
theorem mkAlgHom_rel {x y : FreeAlgebra R (Fin 2)} (h : Rel R δ x y) :
    mkAlgHom R δ x = mkAlgHom R δ y :=
  RingQuot.mkAlgHom_rel R h

/-- The crossing is an involution. -/
@[simp]
theorem s_mul_self : s δ * s δ = 1 := by
  simpa only [map_mul, map_one, mkAlgHom_ι_zero] using
    mkAlgHom_rel (Rel.s_mul_self (R := R) (δ := δ))

/-- The cap-cup diagram is idempotent up to the loop value: closing a loop multiplies by `δ`. -/
@[simp]
theorem e_mul_self : e δ * e δ = δ • e δ := by
  simpa only [map_mul, map_smul, mkAlgHom_ι_one] using
    mkAlgHom_rel (Rel.e_mul_self (R := R) (δ := δ))

/-- The cap-cup diagram absorbs the crossing from the left. -/
@[simp]
theorem s_mul_e : s δ * e δ = e δ := by
  simpa only [map_mul, mkAlgHom_ι_zero, mkAlgHom_ι_one] using
    mkAlgHom_rel (Rel.s_mul_e (R := R) (δ := δ))

/-- The cap-cup diagram absorbs the crossing from the right. -/
@[simp]
theorem e_mul_s : e δ * s δ = e δ := by
  simpa only [map_mul, mkAlgHom_ι_zero, mkAlgHom_ι_one] using
    mkAlgHom_rel (Rel.e_mul_s (R := R) (δ := δ))

section Lift

variable {A : Type*} [Semiring A] [Algebra R A]

/-- The universal property of the presentation of `B₂(δ)`: a crossing and a cap-cup element of an
`R`-algebra satisfying the four defining relations extend to an algebra map out of
`BrauerAlgebraTwo R δ`. -/
def lift (x y : A) (hx : x * x = 1) (hy : y * y = δ • y) (hxy : x * y = y) (hyx : y * x = y) :
    BrauerAlgebraTwo R δ →ₐ[R] A :=
  RingQuot.liftAlgHom R ⟨FreeAlgebra.lift R ![x, y], by
    rintro u v (_ | _ | _ | _)
    · simpa only [map_mul, map_one, FreeAlgebra.lift_ι_apply, Matrix.cons_val_zero] using hx
    · simpa only [map_mul, map_smul, FreeAlgebra.lift_ι_apply, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using hy
    · simpa only [map_mul, FreeAlgebra.lift_ι_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using hxy
    · simpa only [map_mul, FreeAlgebra.lift_ι_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val_fin_one] using hyx⟩

@[simp]
theorem lift_s (x y : A) (hx) (hy) (hxy) (hyx) : lift (δ := δ) x y hx hy hxy hyx (s δ) = x :=
  (RingQuot.liftAlgHom_mkAlgHom_apply R _ _ _).trans (by simp)

@[simp]
theorem lift_e (x y : A) (hx) (hy) (hxy) (hyx) : lift (δ := δ) x y hx hy hxy hyx (e δ) = y :=
  (RingQuot.liftAlgHom_mkAlgHom_apply R _ _ _).trans (by simp)

/-- Two algebra maps out of `B₂(δ)` agreeing on the two generators are equal. -/
@[ext high]
theorem hom_ext {F G : BrauerAlgebraTwo R δ →ₐ[R] A} (hs : F (s δ) = G (s δ))
    (he : F (e δ) = G (e δ)) : F = G :=
  RingQuot.ringQuot_ext' R F G <| FreeAlgebra.hom_ext <| funext fun i => by
    fin_cases i
    · exact hs
    · exact he

end Lift

/-- The two generators generate. -/
theorem adjoin_pair_s_e : Algebra.adjoin R {s δ, e δ} = ⊤ := by
  have hrange : ({s δ, e δ} : Set (BrauerAlgebraTwo R δ))
      = mkAlgHom R δ '' Set.range (FreeAlgebra.ι R (X := Fin 2)) := by
    rw [← Set.image_univ, ← Set.image_comp]
    refine Set.Subset.antisymm ?_ ?_
    · rintro x (rfl | rfl)
      · exact ⟨0, Set.mem_univ _, rfl⟩
      · exact ⟨1, Set.mem_univ _, rfl⟩
    · rintro x ⟨i, -, rfl⟩
      fin_cases i
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ rfl
  rw [hrange, ← AlgHom.map_adjoin, FreeAlgebra.adjoin_range_ι, Algebra.map_top]
  exact (AlgHom.range_eq_top _).2 mkAlgHom_surjective

/-! ### The diagram basis -/

section Diagram

variable (δ)

/-- The element of `B₂(δ)` attached to a Brauer diagram on two strands: the cap-cup diagram goes
to `e`, the crossing to `s`, and the identity diagram to `1`.  These are the only three diagrams
(`TauCeti.BrauerDiagram.univ_two`), so this is a complete assignment. -/
noncomputable def diagram (D : BrauerDiagram 2) : BrauerAlgebraTwo R δ :=
  if D = capCup 0 1 then e δ else if D = permToBrauer (Equiv.swap 0 1) then s δ else 1

variable {δ}

/-- The identity diagram and the cap-cup diagram on two strands are different. -/
theorem permToBrauer_one_ne_capCup :
    permToBrauer (1 : Equiv.Perm (Fin 2)) ≠ capCup 0 1 :=
  (capCup_ne_permToBrauer (by decide) 1).symm

/-- The crossing and the cap-cup diagram on two strands are different. -/
theorem permToBrauer_swap_ne_capCup :
    permToBrauer (Equiv.swap (0 : Fin 2) 1) ≠ capCup 0 1 :=
  (capCup_ne_permToBrauer (by decide) _).symm

/-- The identity diagram and the crossing are different. -/
theorem permToBrauer_one_ne_permToBrauer_swap :
    permToBrauer (1 : Equiv.Perm (Fin 2)) ≠ permToBrauer (Equiv.swap 0 1) := fun h =>
  absurd (permToBrauer_injective 2 h) (by decide)

@[simp]
theorem diagram_capCup : diagram δ (capCup 0 1) = e δ := by
  simp [diagram]

@[simp]
theorem diagram_permToBrauer_swap : diagram δ (permToBrauer (Equiv.swap 0 1)) = s δ := by
  simp [diagram, permToBrauer_swap_ne_capCup]

@[simp]
theorem diagram_permToBrauer_one : diagram δ (permToBrauer 1) = 1 := by
  simp [diagram, permToBrauer_one_ne_capCup, permToBrauer_one_ne_permToBrauer_swap]

/-- The three diagram elements are the identity, the crossing and the cap-cup generator. -/
theorem range_diagram : Set.range (diagram δ) = {1, s δ, e δ} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro x ⟨D, rfl⟩
    rcases D.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl <;>
      simp
  · rintro x (rfl | rfl | rfl)
    · exact ⟨permToBrauer 1, diagram_permToBrauer_one⟩
    · exact ⟨permToBrauer (Equiv.swap 0 1), diagram_permToBrauer_swap⟩
    · exact ⟨capCup 0 1, diagram_capCup⟩

/-- **The multiplication of `B₂(δ)` is the loop-weighted stacking of Brauer diagrams**: the
product of the elements of two diagrams is `δ` raised to the number of loops that close up in the
middle of their stack, times the element of the stacked diagram.  This is the loop rule of the
Brauer algebra, and it is what the four defining relations encode. -/
theorem diagram_mul_diagram (D₁ D₂ : BrauerDiagram 2) :
    diagram δ D₁ * diagram δ D₂
      = δ ^ middleLoopCount D₁ D₂ • diagram δ (composeDiagram D₁ D₂) := by
  rcases D₁.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl <;>
    rcases D₂.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl <;>
    simp [permToBrauer_one_ne_capCup, permToBrauer_swap_ne_capCup]

/-- **The symmetric group sits inside `B₂(δ)`**: the elements of permutation diagrams multiply as
their permutations do, no loop ever closing up in the middle, so the group algebra of `S₂` maps
into `B₂(δ)` along `TauCeti.permToBrauer`. -/
theorem diagram_permToBrauer_mul (σ τ : Equiv.Perm (Fin 2)) :
    diagram δ (permToBrauer σ) * diagram δ (permToBrauer τ)
      = diagram δ (permToBrauer (σ * τ)) := by
  rw [diagram_mul_diagram, composeDiagram_permToBrauer, middleLoopCount_permToBrauer_left,
    pow_zero, one_smul]

end Diagram

/-! ### The left-regular representation -/

section Regular

variable (R δ)

/-- The matrix of left multiplication by the crossing on `B₂(δ)`, read in the diagram basis
`(1, s, e)`: the crossing exchanges `1` and `s` and fixes `e`. -/
def crossingMatrix : Matrix (Fin 3) (Fin 3) R := !![0, 1, 0; 1, 0, 0; 0, 0, 1]

/-- The matrix of left multiplication by the cap-cup diagram on `B₂(δ)`, read in the diagram basis
`(1, s, e)`: the cap-cup diagram carries `1` and `s` to `e` and `e` to `δ • e`. -/
def capCupMatrix : Matrix (Fin 3) (Fin 3) R := !![0, 0, 0; 0, 0, 0; 1, 1, δ]

variable {R δ}

theorem crossingMatrix_mul_self : crossingMatrix R * crossingMatrix R = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossingMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem capCupMatrix_mul_self : capCupMatrix R δ * capCupMatrix R δ = δ • capCupMatrix R δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [capCupMatrix, Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem crossingMatrix_mul_capCupMatrix :
    crossingMatrix R * capCupMatrix R δ = capCupMatrix R δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossingMatrix, capCupMatrix, Matrix.mul_apply, Fin.sum_univ_three]

theorem capCupMatrix_mul_crossingMatrix :
    capCupMatrix R δ * crossingMatrix R = capCupMatrix R δ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [crossingMatrix, capCupMatrix, Matrix.mul_apply, Fin.sum_univ_three]

/-- **The left-regular representation of `B₂(δ)`**, read in the diagram basis `(1, s, e)`: the
algebra map to `3 × 3` matrices sending the crossing and the cap-cup diagram to the matrices of
left multiplication by them.  It is what separates the three diagram elements, so it is what rules
out a collapse of the presentation. -/
noncomputable def regularRep : BrauerAlgebraTwo R δ →ₐ[R] Matrix (Fin 3) (Fin 3) R :=
  lift (δ := δ) (crossingMatrix R) (capCupMatrix R δ) crossingMatrix_mul_self
    capCupMatrix_mul_self crossingMatrix_mul_capCupMatrix capCupMatrix_mul_crossingMatrix

@[simp]
theorem regularRep_s : regularRep (s δ) = crossingMatrix R := lift_s _ _ _ _ _ _

@[simp]
theorem regularRep_e : regularRep (e δ) = capCupMatrix R δ := lift_e _ _ _ _ _ _

/-- **The base ring embeds in `B₂(δ)`**: the presentation does not collapse.  The scalar is read
off the top-left entry of its left-regular matrix. -/
theorem algebraMap_injective : Function.Injective (algebraMap R (BrauerAlgebraTwo R δ)) := by
  intro a b hab
  have h : (regularRep (algebraMap R (BrauerAlgebraTwo R δ) a)) 0 0
      = (regularRep (algebraMap R (BrauerAlgebraTwo R δ) b)) 0 0 := by rw [hab]
  simpa [AlgHom.commutes, Matrix.algebraMap_matrix_apply] using h

instance [Nontrivial R] : Nontrivial (BrauerAlgebraTwo R δ) :=
  algebraMap_injective.nontrivial

end Regular

/-! ### Freeness on the diagram basis -/

section Basis

/-- The position of a Brauer diagram on two strands in the ordered basis `(1, s, e)`. -/
private noncomputable def diagramIndex (D : BrauerDiagram 2) : Fin 3 :=
  if D = capCup 0 1 then 2 else if D = permToBrauer (Equiv.swap 0 1) then 1 else 0

private theorem diagramIndex_capCup : diagramIndex (capCup 0 1) = 2 := by
  simp [diagramIndex]

private theorem diagramIndex_permToBrauer_swap :
    diagramIndex (permToBrauer (Equiv.swap 0 1)) = 1 := by
  simp [diagramIndex, permToBrauer_swap_ne_capCup]

private theorem diagramIndex_permToBrauer_one : diagramIndex (permToBrauer 1) = 0 := by
  simp [diagramIndex, permToBrauer_one_ne_capCup, permToBrauer_one_ne_permToBrauer_swap]

private theorem diagramIndex_injective : Function.Injective diagramIndex := by
  intro D₁ D₂ h
  rcases D₁.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl <;>
    rcases D₂.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl <;>
      simp_all [diagramIndex_permToBrauer_one, diagramIndex_permToBrauer_swap,
        diagramIndex_capCup]

variable (R δ)

/-- The three matrix entries that separate the left-regular matrices of `1`, `s` and `e`. -/
private def separatingEntries : Matrix (Fin 3) (Fin 3) R →ₗ[R] (Fin 3 → R) where
  toFun M := ![M 0 0, M 0 1, M 2 0]
  map_add' M N := by ext i; fin_cases i <;> simp
  map_smul' c M := by ext i; fin_cases i <;> simp

variable {R δ}

private theorem separatingEntries_regularRep_diagram (D : BrauerDiagram 2) :
    separatingEntries R (regularRep (diagram δ D)) = Pi.single (diagramIndex D) 1 := by
  rcases D.eq_permToBrauer_one_or_eq_permToBrauer_swap_or_eq_capCup with rfl | rfl | rfl <;>
    ext i <;> fin_cases i <;>
    simp [separatingEntries, diagramIndex_permToBrauer_one, diagramIndex_permToBrauer_swap,
      diagramIndex_capCup, crossingMatrix, capCupMatrix]

/-- **The three diagram elements of `B₂(δ)` are linearly independent.** -/
theorem linearIndependent_diagram : LinearIndependent R (diagram δ) := by
  have hsingle : LinearIndependent R fun D : BrauerDiagram 2 =>
      (Pi.single (diagramIndex D) 1 : Fin 3 → R) := by
    simpa only [Function.comp_def, Pi.basisFun_apply] using
      (Pi.basisFun R (Fin 3)).linearIndependent.comp diagramIndex diagramIndex_injective
  refine LinearIndependent.of_comp ((regularRep (R := R) (δ := δ)).toLinearMap) ?_
  refine LinearIndependent.of_comp (separatingEntries R) ?_
  simpa only [Function.comp_def, AlgHom.toLinearMap_apply,
    separatingEntries_regularRep_diagram] using hsingle

/-- **The three diagram elements of `B₂(δ)` span it.** Their span is already a subalgebra, by the
multiplication table, and the two generators generate. -/
theorem span_range_diagram : Submodule.span R (Set.range (diagram δ)) = ⊤ := by
  have hgen : ∀ x ∈ ({1, s δ, e δ} : Set (BrauerAlgebraTwo R δ)),
      x ∈ Submodule.span R (Set.range (diagram δ)) := fun x hx =>
    Submodule.subset_span (by rw [range_diagram]; exact hx)
  have hone : (1 : BrauerAlgebraTwo R δ) ∈ Submodule.span R (Set.range (diagram δ)) :=
    hgen 1 (by simp)
  have hs : s δ ∈ Submodule.span R (Set.range (diagram δ)) := hgen _ (by simp)
  have he : e δ ∈ Submodule.span R (Set.range (diagram δ)) := hgen _ (by simp)
  have hmulle : Submodule.span R (Set.range (diagram δ)) *
      Submodule.span R (Set.range (diagram δ)) ≤ Submodule.span R (Set.range (diagram δ)) := by
    rw [Submodule.span_mul_span, Submodule.span_le]
    rintro z ⟨a, ha, b, hb, rfl⟩
    rw [range_diagram] at ha hb
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    simp only [SetLike.mem_coe]
    rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl <;>
      simp only [one_mul, mul_one, s_mul_self, s_mul_e, e_mul_s, e_mul_self] <;>
      first
        | exact hone
        | exact hs
        | exact he
        | exact Submodule.smul_mem _ _ he
  have hmul : ∀ x y : BrauerAlgebraTwo R δ,
      x ∈ Submodule.span R (Set.range (diagram δ)) →
      y ∈ Submodule.span R (Set.range (diagram δ)) →
      x * y ∈ Submodule.span R (Set.range (diagram δ)) := fun x y hx hy =>
    hmulle (Submodule.mul_mem_mul hx hy)
  have htop : Algebra.adjoin R ({s δ, e δ} : Set (BrauerAlgebraTwo R δ))
      ≤ (Submodule.span R (Set.range (diagram δ))).toSubalgebra hone hmul :=
    Algebra.adjoin_le (by rintro x (rfl | rfl) <;> assumption)
  refine eq_top_iff.2 fun x _ => ?_
  exact htop ((adjoin_pair_s_e (R := R) (δ := δ)).ge Algebra.mem_top)

/-- **The diagram basis of `B₂(δ)`**: the Brauer algebra on two strands is free on the Brauer
diagrams on two strands. -/
noncomputable def basis : Module.Basis (BrauerDiagram 2) R (BrauerAlgebraTwo R δ) :=
  Module.Basis.mk linearIndependent_diagram (by rw [span_range_diagram])

@[simp]
theorem coe_basis : (basis (R := R) (δ := δ) : BrauerDiagram 2 → BrauerAlgebraTwo R δ)
    = diagram δ :=
  Module.Basis.coe_mk _ _

instance : Module.Free R (BrauerAlgebraTwo R δ) :=
  Module.Free.of_basis basis

end Basis

section Finrank

variable {R : Type*} [CommRing R] [StrongRankCondition R] {δ : R}

/-- **`B₂(δ)` has dimension `(2 * 2 - 1)‼ = 3`**, the number of Brauer diagrams on two
strands. -/
theorem finrank_eq_three : Module.finrank R (BrauerAlgebraTwo R δ) = 3 := by
  rw [Module.finrank_eq_card_basis (basis (R := R) (δ := δ)), card_brauerDiagram]
  decide

end Finrank

end BrauerAlgebraTwo

end TauCeti
