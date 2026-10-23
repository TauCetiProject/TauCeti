/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Grid.Homology.KnotAlexander

/-!
# Non-torsion classes in unblocked grid homology from rectangle parity

The `X`-marking state `G.X` of a grid diagram, the grid state whose point in each column is the
lower-left corner of the `X`-marked square, is a cycle of the unblocked grid complex `GC⁻`
(`GridDiagram.unblockedDifferential_single_X`). This file studies when its class `XMarkingClass`
in `GH⁻` is not torsion.

The tool is the evaluation of the coefficient ring `R[V₀, …, V_{n-1}]` at `V₀ = ⋯ = V_{n-1} = 1`.
It sends the weight `V^{O(r)}` of every rectangle to `1`, hence sends each matrix coefficient of
`∂⁻` to the number of rectangles it counts (`eval_one_unblockedCoefficient`). If every grid state
has an even number of counted rectangles ending at a state `z`, then in characteristic two the
`z`-coefficient of every boundary evaluates to zero
(`eval_one_unblockedDifferential_apply_eq_zero`), so `p • z` is a boundary only when
`p(1, …, 1) = 0` (`eval_one_eq_zero_of_smul_single_mem_range`), and no monomial multiple of `z` is
a boundary. Applied to `z = G.X`, no power of `U` kills `XMarkingClass`
(`X_pow_smul_XMarkingClass_ne_zero`).

For a knot grid the class is homogeneous of Alexander degree `A(G.X)`
(`IsKnot.XMarkingClass_mem_alexanderUnblockedHomologyGrading_piece`), so over a field of
characteristic two the parity hypothesis makes `A(G.X)` a non-torsion degree of the `R[U]`-module
`GH⁻` (`IsKnot.alexanderℤ_X_mem_nonTorsionDegrees`); in particular `GH⁻` is not a torsion module.
A degree bound on the grid states bounds the non-torsion degrees
(`IsKnot.nonTorsionDegrees_subset_Iic`), so when `G.X` has the largest Alexander grading among
the grid states, `A(G.X)` is the maximal non-torsion degree
(`IsKnot.supNonTorsionDegree_alexanderUnblockedHomologyGrading_eq`). The standard torus knot
grids satisfy both hypotheses; they are treated in `TorusLink/Homology.lean`.

## Main definitions

* `TauCeti.GridDiagram.XMarkingCycle`: the `X`-marking state as a cycle of `GC⁻`.
* `TauCeti.GridDiagram.XMarkingClass`: its class in `GH⁻`.

## Main results

* `TauCeti.GridDiagram.eval_one_eq_zero_of_smul_single_mem_range`: if every state has an even
  number of counted rectangles into `z`, a multiple `p • z` is a boundary only when
  `p(1, …, 1) = 0`.
* `TauCeti.GridDiagram.X_pow_smul_XMarkingClass_ne_zero` and
  `TauCeti.GridDiagram.IsKnot.X_pow_smul_XMarkingClass_ne_zero`: under that parity hypothesis at
  `G.X`, no power of a grid variable, or of `U` on a knot grid, kills `XMarkingClass`.
* `TauCeti.GridDiagram.IsKnot.alexanderℤ_X_mem_nonTorsionDegrees` and
  `TauCeti.GridDiagram.IsKnot.supNonTorsionDegree_alexanderUnblockedHomologyGrading_eq`: the
  Alexander grading of `G.X` is a non-torsion degree, and the maximal one when `G.X` has maximal
  Alexander grading among the grid states.

## References

The class of the `X`-marking state is the canonical generator used by Ozsváth--Stipsicz--Szabó,
*Grid Homology for Knots and Links*, Chapter 6, to compute `τ` of torus knots; the argument
through the evaluation at `1` is the observation that torsion in `GH⁻` is invisible to the count
of `X`-avoiding rectangles.
-/

public section

open MvPolynomial

namespace TauCeti

namespace GridDiagram

variable {n : ℕ} (G : GridDiagram n)

section Chain

variable (R : Type*) [CommSemiring R]

/-! ### Evaluating the grid variables at one -/

/-- Setting every grid variable to `1` sends the weight of a rectangle to `1`. -/
@[simp]
theorem eval_one_OMonomial (r : GridRectangle n) :
    eval (fun _ : Fin n => (1 : R)) (G.OMonomial R r) = 1 := by
  rw [OMonomial_eq_monomial, eval_monomial]
  simp

/-- Setting every grid variable to `1` sends a matrix coefficient of `∂⁻` to the number of
rectangles it counts. -/
@[simp]
theorem eval_one_unblockedCoefficient (x y : GridState n) :
    eval (fun _ : Fin n => (1 : R)) (G.unblockedCoefficient R x y) =
      ((G.unblockedRectangles x y).card : R) := by
  rw [unblockedCoefficient_def, map_sum]
  simp

/-- Setting every grid variable to `1` in the `z`-coefficient of `∂⁻ c` gives the sum, over the
support of `c`, of the evaluated coefficients weighted by the numbers of counted rectangles. -/
theorem eval_one_unblockedDifferential_apply (c : GridChainMinus R n) (z : GridState n) :
    eval (fun _ : Fin n => (1 : R)) (G.unblockedDifferential R c z) =
      c.sum fun x a =>
        eval (fun _ : Fin n => (1 : R)) a * ((G.unblockedRectangles x z).card : R) := by
  rw [unblockedDifferential_apply_apply, map_finsuppSum]
  exact Finsupp.sum_congr fun x _ => by rw [map_mul, eval_one_unblockedCoefficient]

section Parity

variable [CharP R 2] {z : GridState n}
  (hz : ∀ x : GridState n, Even (G.unblockedRectangles x z).card)
include hz

/-- If every grid state has an even number of counted rectangles into `z`, then in characteristic
two the `z`-coefficient of every boundary vanishes once the grid variables are set to `1`. -/
theorem eval_one_unblockedDifferential_apply_eq_zero (c : GridChainMinus R n) :
    eval (fun _ : Fin n => (1 : R)) (G.unblockedDifferential R c z) = 0 := by
  rw [eval_one_unblockedDifferential_apply]
  refine Finset.sum_eq_zero fun x _ => ?_
  dsimp only
  rw [(CharP.cast_eq_zero_iff R 2 _).mpr (even_iff_two_dvd.mp (hz x)), mul_zero]

/-- If every grid state has an even number of counted rectangles into `z`, then a multiple
`p • z` of the generator `z` is a boundary only when `p(1, …, 1) = 0`. -/
theorem eval_one_eq_zero_of_smul_single_mem_range {p : MvPolynomial (Fin n) R}
    (hp : p • (Finsupp.single z 1 : GridChainMinus R n) ∈
      LinearMap.range (G.unblockedDifferential R)) :
    eval (fun _ : Fin n => (1 : R)) p = 0 := by
  obtain ⟨c, hc⟩ := hp
  have h := congrArg (fun f : GridChainMinus R n => eval (fun _ : Fin n => (1 : R)) (f z)) hc
  simp only [Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one] at h
  rw [← h, G.eval_one_unblockedDifferential_apply_eq_zero R hz]

/-- If every grid state has an even number of counted rectangles into `z`, then no monomial
multiple of the generator `z` is a boundary. -/
theorem monomial_smul_single_notMem_range [Nontrivial R] (e : Fin n →₀ ℕ) :
    (monomial e (1 : R)) • (Finsupp.single z 1 : GridChainMinus R n) ∉
      LinearMap.range (G.unblockedDifferential R) := by
  intro h
  have h1 := G.eval_one_eq_zero_of_smul_single_mem_range R hz h
  rw [eval_monomial] at h1
  simp at h1

end Parity

/-! ### The `X`-marking state as a cycle -/

/-- The `X`-marking state, as a cycle of the unblocked grid complex `GC⁻`. -/
noncomputable def XMarkingCycle : LinearMap.ker (G.unblockedDifferential R) :=
  ⟨Finsupp.single G.X 1, LinearMap.mem_ker.mpr (G.unblockedDifferential_single_X R)⟩

/-- The cycle `XMarkingCycle` is the generator of `GC⁻` at the `X`-marking state. -/
@[simp]
theorem coe_XMarkingCycle :
    (G.XMarkingCycle R : GridChainMinus R n) = Finsupp.single G.X 1 :=
  (rfl)

end Chain

section Homology

variable (R : Type*) [CommRing R] [CharP R 2]

/-- The class of the `X`-marking state in the unblocked grid homology `GH⁻`. -/
noncomputable def XMarkingClass : G.unblockedHomology R :=
  G.unblockedHomologyClass R (G.XMarkingCycle R)

/-- The class of the `X`-marking state is the class of its cycle. -/
theorem XMarkingClass_def : G.XMarkingClass R = G.unblockedHomologyClass R (G.XMarkingCycle R) :=
  (rfl)

/-- If every grid state has an even number of counted rectangles into the `X`-marking state, then
no monomial in the grid variables kills its class in `GH⁻`. -/
theorem monomial_smul_XMarkingClass_ne_zero [Nontrivial R]
    (hX : ∀ x : GridState n, Even (G.unblockedRectangles x G.X).card) (e : Fin n →₀ ℕ) :
    (monomial e (1 : R)) • G.XMarkingClass R ≠ 0 := by
  intro h
  rw [XMarkingClass_def, ← map_smul, unblockedHomologyClass_eq_zero_iff, Submodule.coe_smul,
    coe_XMarkingCycle] at h
  exact G.monomial_smul_single_notMem_range R hX e h

/-- If every grid state has an even number of counted rectangles into the `X`-marking state, then
no power of a grid variable kills its class in `GH⁻`. -/
theorem X_pow_smul_XMarkingClass_ne_zero [Nontrivial R]
    (hX : ∀ x : GridState n, Even (G.unblockedRectangles x G.X).card) (i : Fin n) (k : ℕ) :
    (MvPolynomial.X i ^ k : MvPolynomial (Fin n) R) • G.XMarkingClass R ≠ 0 := by
  have h := G.monomial_smul_XMarkingClass_ne_zero R hX (Finsupp.single i k)
  rwa [← X_pow_eq_monomial] at h

/-! ### Knot grids -/

namespace IsKnot

variable {G R} (hG : G.IsKnot)
include hG

/-- On a knot grid whose `X`-marking state receives an even number of counted rectangles from
every grid state, no power of `U` kills the class of the `X`-marking state in `GH⁻`. -/
theorem X_pow_smul_XMarkingClass_ne_zero [Nontrivial R]
    (hX : ∀ x : GridState n, Even (G.unblockedRectangles x G.X).card) (k : ℕ) :
    letI := hG.unblockedHomologyModule R
    (Polynomial.X ^ k : Polynomial R) • G.XMarkingClass R ≠ 0 := by
  let _ := hG.unblockedHomologyModule R
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero hG.ne_zero⟩
  have h := hG.aeval_smul_unblockedHomology (R := R) (MvPolynomial.X i ^ k) (G.XMarkingClass R)
  rw [map_pow, aeval_X] at h
  rw [h]
  exact G.X_pow_smul_XMarkingClass_ne_zero R hX i k

/-- On a knot grid the class of the `X`-marking state is homogeneous of Alexander degree
`A(G.X)`. -/
theorem XMarkingClass_mem_alexanderUnblockedHomologyGrading_piece :
    G.XMarkingClass R ∈ (hG.alexanderUnblockedHomologyGrading R).piece
      (hG.toOddComponentGridDiagram.alexanderℤ G.X) := by
  rw [hG.mem_alexanderUnblockedHomologyGrading_piece_iff, XMarkingClass_def,
    unblockedHomologyIso_hom_unblockedHomologyClass,
    OddComponentGridDiagram.mem_alexanderHomologyGrading_piece_iff]
  refine ⟨G.XMarkingCycle R, ?_, rfl⟩
  rw [coe_XMarkingCycle]
  have h := OddComponentGridDiagram.single_one_mem_bigradedChainMinusPiece
    hG.toOddComponentGridDiagram R G.X
  have hle := OddComponentGridDiagram.bigradedChainMinusPiece_le_alexanderChainMinusPiece
    hG.toOddComponentGridDiagram R (hG.toOddComponentGridDiagram.bidegree G.X).1
    (hG.toOddComponentGridDiagram.bidegree G.X).2
  have hmem := hle (by rw [Prod.mk.eta]; exact h)
  rwa [OddComponentGridDiagram.bidegree_snd] at hmem

omit [CharP R 2] in
/-- A homogeneous nonzero chain of `GC⁻` has Alexander degree at most the Alexander grading of
some grid state, so at most any common upper bound of the Alexander gradings of the grid
states. -/
theorem le_of_mem_alexanderChainMinusPiece_of_ne_zero {a₀ : ℤ}
    (h : ∀ x : GridState n, hG.toOddComponentGridDiagram.alexanderℤ x ≤ a₀) {a : ℤ}
    {c : GridChainMinus R n}
    (hc : c ∈ hG.toOddComponentGridDiagram.alexanderChainMinusPiece R a) (hc0 : c ≠ 0) :
    a ≤ a₀ := by
  rw [OddComponentGridDiagram.mem_alexanderChainMinusPiece] at hc
  obtain ⟨x, hx⟩ := Finsupp.ne_iff.mp hc0
  obtain ⟨e, he⟩ := (support_nonempty (p := c x)).mpr (by simpa using hx)
  rw [← hc x e he]
  have := h x
  omega

/-- On a knot grid, an upper bound for the Alexander gradings of the grid states bounds the
non-torsion degrees of `GH⁻`. -/
theorem nonTorsionDegrees_subset_Iic {a₀ : ℤ}
    (h : ∀ x : GridState n, hG.toOddComponentGridDiagram.alexanderℤ x ≤ a₀) :
    letI := hG.unblockedHomologyModule R
    (hG.alexanderUnblockedHomologyGrading R).nonTorsionDegrees ⊆ Set.Iic a₀ := by
  let _ := hG.unblockedHomologyModule R
  intro a ha
  obtain ⟨y, hy, hyt⟩ := InternalGrading.mem_nonTorsionDegrees.mp ha
  have hy0 : y ≠ 0 := fun hy0 => hyt (hy0 ▸ Submodule.zero_mem _)
  rw [hG.mem_alexanderUnblockedHomologyGrading_piece_iff,
    OddComponentGridDiagram.mem_alexanderHomologyGrading_piece_iff] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  refine hG.le_of_mem_alexanderChainMinusPiece_of_ne_zero h hz fun hz0 => hy0 ?_
  have hzero : z = 0 := Subtype.ext hz0
  rw [hzero, map_zero] at hzy
  exact (ModuleCat.mono_iff_injective (G.unblockedHomologyIso R).hom).mp inferInstance
    (hzy.symm.trans (map_zero _).symm)

end IsKnot

end Homology

section Field

variable {K : Type*} [Field K] [CharP K 2] {G : GridDiagram n} (hG : G.IsKnot)
  (hX : ∀ x : GridState n, Even (G.unblockedRectangles x G.X).card)
include hG hX

namespace IsKnot

/-- On a knot grid whose `X`-marking state receives an even number of counted rectangles from
every grid state, the Alexander grading of the `X`-marking state is a non-torsion degree of the
`K[U]`-module `GH⁻`: the class of that state is homogeneous and not torsion. -/
theorem alexanderℤ_X_mem_nonTorsionDegrees :
    letI := hG.unblockedHomologyModule K
    hG.toOddComponentGridDiagram.alexanderℤ G.X ∈
      (hG.alexanderUnblockedHomologyGrading K).nonTorsionDegrees := by
  let _ := hG.unblockedHomologyModule K
  have := hG.isScalarTower_unblockedHomology (R := K)
  rw [InternalGrading.mem_nonTorsionDegrees_iff_forall_X_pow_smul_ne_zero (d := 1) one_ne_zero
    (fun p y hy => by simpa using hG.X_smul_mem_alexanderUnblockedHomologyGrading_piece K hy)]
  exact ⟨G.XMarkingClass K, hG.XMarkingClass_mem_alexanderUnblockedHomologyGrading_piece,
    fun k => hG.X_pow_smul_XMarkingClass_ne_zero hX k⟩

/-- On a knot grid whose `X`-marking state receives an even number of counted rectangles from
every grid state, `GH⁻` is not a torsion `K[U]`-module. -/
theorem not_isTorsion_unblockedHomology :
    letI := hG.unblockedHomologyModule K
    ¬Module.IsTorsion (Polynomial K) (G.unblockedHomology K) := by
  let _ := hG.unblockedHomologyModule K
  exact (InternalGrading.nonTorsionDegrees_nonempty_iff _).mp
    ⟨_, hG.alexanderℤ_X_mem_nonTorsionDegrees hX⟩

/-- On a knot grid whose `X`-marking state receives an even number of counted rectangles from
every grid state and has the largest Alexander grading among the grid states, that grading is the
maximal non-torsion degree of the `K[U]`-module `GH⁻`. -/
theorem supNonTorsionDegree_alexanderUnblockedHomologyGrading_eq
    (h : ∀ x : GridState n, hG.toOddComponentGridDiagram.alexanderℤ x ≤
      hG.toOddComponentGridDiagram.alexanderℤ G.X) :
    letI := hG.unblockedHomologyModule K
    (hG.alexanderUnblockedHomologyGrading K).supNonTorsionDegree =
      hG.toOddComponentGridDiagram.alexanderℤ G.X := by
  let _ := hG.unblockedHomologyModule K
  rw [InternalGrading.supNonTorsionDegree_def]
  exact IsGreatest.csSup_eq ⟨hG.alexanderℤ_X_mem_nonTorsionDegrees hX,
    fun a ha => hG.nonTorsionDegrees_subset_Iic (R := K) h ha⟩

end IsKnot

end Field

end GridDiagram

end TauCeti
