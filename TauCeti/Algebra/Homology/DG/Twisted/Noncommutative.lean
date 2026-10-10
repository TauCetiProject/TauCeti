/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Complex
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.Derivation
public import Mathlib.Combinatorics.Quiver.SingleObj

/-!
# Twisted complexes: a noncommutative regression test

The twisted differential of `TauCeti.Algebra.Homology.DG.Twisted.Complex` multiplies the
coefficients of a twisting cocycle through the right action of the algebra.  Over a commutative
algebra the order of the factors is invisible; this file checks the construction on the smallest
noncommutative example in which it matters.

The algebra is the path algebra `ℚ⟨a, b, c⟩` of the quiver with one vertex and three loops, graded
by `|a| = |b| = 0` and `|c| = -1` (cohomologically), with the differential `∂a = ∂b = 0` and
`∂c = -ab`, extended as a graded derivation.  Three generators `x, z, y` of indices `2, 1, 0`
carry the coefficients `m x z = a`, `m z y = b` and `m x y = c`.  The twisting equation reads
`∂c = -ab` and holds; the matrix is one-sided.

On the regular module `A` with its right action, the twisted differential sends `1 ⊗ x` to
`a ⊗ z + c ⊗ y`, then `a ⊗ z` to `ab ⊗ y` and `c ⊗ y` to `-ab ⊗ y`, so `D² (1 ⊗ x) = 0` on the
nose (`twistedDifferential_twistedDifferential_single_x`).  The cancellation is between `ab`,
produced by the right action of `b` on `a`, and `∂c = -ab`; the products `ab` and `ba` are distinct
basis paths (`gen_a_mul_gen_b_ne`), so it depends on the order in which the construction
multiplies the coefficients.  The literal right-free reading of the same coefficients,
`d e_x = Σ_y e_y m x y`, in which the twisting coefficient multiplies the coordinate `f x` on the
left, is recorded as
`rightFreeDifferential`: it gives `d² e_x = e_y (ba - ab) ≠ 0`
(`rightFreeDifferential_rightFreeDifferential_single_x_ne_zero`), which is the reason for the
variance convention of the twisted complex.

## Main definitions and results

* `TauCeti.TwistedExamples.threeDegree`, `TauCeti.TwistedExamples.threeRelator`: the degrees of the
  three arrows and the values of the differential on them;
  `TauCeti.TwistedExamples.isDGAlgebra_threeDifferential` makes `ℚ⟨a, b, c⟩` a differential graded
  algebra.
* `TauCeti.TwistedExamples.threeCocycle`: the twisting cocycle `m x z = a`, `m z y = b`,
  `m x y = c`, with its entries `threeCocycle_m_apply`.
* `TauCeti.TwistedExamples.twistedDifferential_single_x`: `D (1 ⊗ x) = a ⊗ z + c ⊗ y`.
* `TauCeti.TwistedExamples.twistedDifferential_twistedDifferential_single_x`: `D² (1 ⊗ x) = 0`,
  computed term by term.
* `TauCeti.TwistedExamples.gen_a_mul_gen_b_ne`: `ab ≠ ba` in the path algebra.
* `TauCeti.TwistedExamples.rightFreeDifferential`: the literal right-free reading of the
  coefficients, with `rightFreeDifferential_rightFreeDifferential_single_x_ne_zero`: its square
  does not vanish on `e_x`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4.
-/

public section

namespace TauCeti

open MulOpposite _root_.Quiver PathAlgebra

namespace TwistedExamples

/-- The three loops `a`, `b`, `c` of the one-vertex quiver. -/
inductive ThreeArrow : Type
  /-- The loop `a`, of degree `0`. -/
  | a
  /-- The loop `b`, of degree `0`. -/
  | b
  /-- The loop `c`, of degree `-1`, with `∂c = -ab`. -/
  | c
  deriving DecidableEq

/-- The cohomological degrees of the three loops: `|a| = |b| = 0` and `|c| = -1`. -/
def threeDegree : ∀ {i j : SingleObj ThreeArrow}, (i ⟶ j) → ℤ
  | _, _, .a => 0
  | _, _, .b => 0
  | _, _, .c => -1

/-- The path-algebra element of one of the three loops.  A definition rather than an abbreviation,
so that `simp` does not rewrite the generators to basis paths. -/
noncomputable def gen (e : ThreeArrow) : pathAlgebra ℚ (SingleObj ThreeArrow) :=
  ofArrow (SingleObj.toHom e)

/-- A generator is homogeneous of its own degree. -/
theorem gen_mem_gradeBy (e : ThreeArrow) :
    gen e ∈ gradeBy ℚ threeDegree (threeDegree (SingleObj.toHom e)) :=
  ofArrow_mem_gradeBy threeDegree _

/-- The values of the differential on the three loops: `∂a = ∂b = 0` and `∂c = -ab`. -/
noncomputable def threeRelator :
    ∀ {i j : SingleObj ThreeArrow}, (i ⟶ j) → pathAlgebra ℚ (SingleObj ThreeArrow)
  | _, _, .a => 0
  | _, _, .b => 0
  | _, _, .c => -(gen .a * gen .b)

/-- The differential of `ℚ⟨a, b, c⟩`: the graded derivation with `∂a = ∂b = 0` and `∂c = -ab`. -/
noncomputable def threeDifferential :
    pathAlgebra ℚ (SingleObj ThreeArrow) →ₗ[ℚ] pathAlgebra ℚ (SingleObj ThreeArrow) :=
  liftDerivation ℚ threeDegree threeRelator

/-- With one vertex, the vertex idempotent is the unit. -/
private theorem vertexIdempotent_eq_one (v : SingleObj ThreeArrow) :
    vertexIdempotent ℚ v = (1 : pathAlgebra ℚ (SingleObj ThreeArrow)) := by
  rw [one_def, Fintype.sum_unique, Unique.eq_default v]

private theorem vertexIdempotent_mul_threeRelator {i j : SingleObj ThreeArrow} (e : i ⟶ j) :
    vertexIdempotent ℚ j * threeRelator e = threeRelator e := by
  rw [vertexIdempotent_eq_one, one_mul]

private theorem threeRelator_mul_vertexIdempotent {i j : SingleObj ThreeArrow} (e : i ⟶ j) :
    threeRelator e * vertexIdempotent ℚ i = threeRelator e := by
  rw [vertexIdempotent_eq_one, mul_one]

/-- The differential on the three loops is the prescribed one. -/
theorem threeDifferential_gen (e : ThreeArrow) :
    threeDifferential (gen e) = threeRelator (SingleObj.toHom e) := by
  rw [threeDifferential, gen]
  exact liftDerivation_ofArrow ℚ _ _ threeRelator_mul_vertexIdempotent _

/-- The Leibniz rule against a generator. -/
theorem threeDifferential_gen_mul (e : ThreeArrow) (z : pathAlgebra ℚ (SingleObj ThreeArrow)) :
    threeDifferential (gen e * z) = threeRelator (SingleObj.toHom e) * z +
      (threeDegree (SingleObj.toHom e)).negOnePow • (gen e * threeDifferential z) := by
  rw [threeDifferential, gen]
  exact liftDerivation_ofArrow_mul ℚ _ _ vertexIdempotent_mul_threeRelator
    threeRelator_mul_vertexIdempotent _ z

@[simp]
theorem threeDifferential_gen_a : threeDifferential (gen .a) = 0 :=
  threeDifferential_gen .a

@[simp]
theorem threeDifferential_gen_b : threeDifferential (gen .b) = 0 :=
  threeDifferential_gen .b

/-- The defining equation `∂c = -ab`. -/
@[simp]
theorem threeDifferential_gen_c : threeDifferential (gen .c) = -(gen .a * gen .b) :=
  threeDifferential_gen .c

private theorem threeRelator_mem_gradeBy {i j : SingleObj ThreeArrow} (e : i ⟶ j) :
    threeRelator e ∈ gradeBy ℚ threeDegree (threeDegree e + 1) := by
  cases e with
  | a => exact zero_mem _
  | b => exact zero_mem _
  | c =>
    refine neg_mem ?_
    simpa [threeDegree] using SetLike.mul_mem_graded (gen_mem_gradeBy .a) (gen_mem_gradeBy .b)

private theorem threeDifferential_threeRelator {i j : SingleObj ThreeArrow} (e : i ⟶ j) :
    threeDifferential (threeRelator e) = 0 := by
  cases e with
  | a => simp [threeRelator]
  | b => simp [threeRelator]
  | c =>
    rw [threeRelator, map_neg, threeDifferential_gen_mul, threeDifferential_gen_b]
    simp [threeRelator]

/-- **`ℚ⟨a, b, c⟩` is a differential graded algebra**, graded by `|a| = |b| = 0`, `|c| = -1`, with
`∂a = ∂b = 0` and `∂c = -ab`. -/
theorem isDGAlgebra_threeDifferential : IsDGAlgebra (gradeBy ℚ threeDegree) threeDifferential := by
  rw [threeDifferential]
  exact isDGAlgebra_liftDerivation ℚ _ _ vertexIdempotent_mul_threeRelator
    threeRelator_mul_vertexIdempotent threeRelator_mem_gradeBy threeDifferential_threeRelator

/-- The generators: `x = 0` of index `2`, `z = 1` of index `1` and `y = 2` of index `0`. -/
def threeInd : Fin 3 → ℤ := ![2, 1, 0]

/-- The coefficient matrix: `m x z = a`, `m z y = b`, `m x y = c`, every other entry zero. -/
noncomputable def threeMatrix : Fin 3 → Fin 3 → pathAlgebra ℚ (SingleObj ThreeArrow) :=
  ![![0, gen .a, gen .c], ![0, 0, gen .b], ![0, 0, 0]]

/-- The twisting cocycle `m x z = a`, `m z y = b`, `m x y = c` over `ℚ⟨a, b, c⟩`. -/
noncomputable def threeCocycle :
    TwistingCocycle (gradeBy ℚ threeDegree) threeDifferential (Fin 3) threeInd where
  m := threeMatrix
  mem_graded i j := by
    fin_cases i <;> fin_cases j <;>
      first
      | exact zero_mem _
      | exact gen_mem_gradeBy .a
      | exact gen_mem_gradeBy .b
      | exact gen_mem_gradeBy .c
  twisting i j := by
    fin_cases i <;> fin_cases j <;> simp [threeMatrix, threeInd, Fin.sum_univ_three]
  one_sided i j := by
    fin_cases i <;> fin_cases j <;> simp [threeMatrix, threeInd]

/-- The entries of the cocycle. -/
@[simp]
theorem threeCocycle_m_apply (i j : Fin 3) : threeCocycle.m i j = threeMatrix i j := by
  rw [threeCocycle]

/-- **`D (1 ⊗ x) = a ⊗ z + c ⊗ y`** on the regular module. -/
theorem twistedDifferential_single_x :
    twistedDifferential threeCocycle.m (gradeBy ℚ threeDegree) threeDifferential (Pi.single 0 1) =
      Pi.single 1 (gen .a) + Pi.single 2 (gen .c) := by
  rw [twistedDifferential_single threeCocycle.m threeDifferential 0 (q := 0)
    (SetLike.one_mem_graded _), isDGAlgebra_threeDifferential.map_one_eq_zero, Pi.single_zero,
    zero_add]
  simp [Fin.sum_univ_three, threeMatrix]

/-- **`D (a ⊗ z) = ab ⊗ y`**: the coefficient `b` multiplies `a` on the right. -/
theorem twistedDifferential_single_z :
    twistedDifferential threeCocycle.m (gradeBy ℚ threeDegree) threeDifferential
      (Pi.single 1 (gen .a)) = Pi.single 2 (gen .a * gen .b) := by
  rw [twistedDifferential_single threeCocycle.m threeDifferential 1 (q := 0) (gen_mem_gradeBy .a),
    threeDifferential_gen_a, Pi.single_zero, zero_add]
  simp [Fin.sum_univ_three, threeMatrix]

/-- **`D (c ⊗ y) = ∂c ⊗ y = -ab ⊗ y`**. -/
theorem twistedDifferential_single_y :
    twistedDifferential threeCocycle.m (gradeBy ℚ threeDegree) threeDifferential
      (Pi.single 2 (gen .c)) = Pi.single 2 (-(gen .a * gen .b)) := by
  rw [twistedDifferential_single threeCocycle.m threeDifferential 2 (q := -1)
    (gen_mem_gradeBy .c), threeDifferential_gen_c]
  simp [Fin.sum_univ_three, threeMatrix]

/-- **`D² (1 ⊗ x) = (ab + ∂c) ⊗ y = 0`**, computed term by term. -/
theorem twistedDifferential_twistedDifferential_single_x :
    twistedDifferential threeCocycle.m (gradeBy ℚ threeDegree) threeDifferential
      (twistedDifferential threeCocycle.m (gradeBy ℚ threeDegree) threeDifferential
        (Pi.single 0 1)) = 0 := by
  rw [twistedDifferential_single_x, map_add, twistedDifferential_single_z,
    twistedDifferential_single_y, ← Pi.single_add, add_neg_cancel, Pi.single_zero]

/-- **`ab ≠ ba`** in `ℚ⟨a, b, c⟩`: the two products are distinct basis paths. -/
theorem gen_a_mul_gen_b_ne : gen .a * gen .b ≠ gen .b * gen .a := by
  unfold gen
  rw [ofArrow_eq_ofPath, ofArrow_eq_ofPath, ofPath_mul_ofPath_of_comp,
    ofPath_mul_ofPath_of_comp, ofPath_eq_single, ofPath_eq_single]
  intro h
  have := congrArg (fun f ↦ (pathAlgebraBasis ℚ (SingleObj ThreeArrow)).repr f
    ⟨SingleObj.star ThreeArrow, SingleObj.star ThreeArrow,
      (SingleObj.toHom ThreeArrow.b).toPath.comp (SingleObj.toHom ThreeArrow.a).toPath⟩) h
  simp [pathAlgebraBasis_repr_single, Quiver.Hom.toPath, Quiver.Path.comp] at this

/-! ### The literal right-free reading

Reading the coefficients as a differential on a free right module, `d e_x = Σ_y e_y m x y`, puts
the twisting coefficient between the basis vector and its coordinate: on `Fin 3 → ℚ⟨a, b, c⟩`,
`(d f) y = ∂ (f y) + Σ_x m x y * f x`, so `m x y` multiplies the coordinate `f x` on the left.  Its
square does not vanish. -/

/-- The literal right-free reading of the coefficients of `threeCocycle`:
`(d f) y = ∂ (f y) + Σ_x m x y * f x`, the twisting coefficient multiplying the coordinate `f x` on
the left.  Recorded for comparison with `twistedDifferential`, where it multiplies on the right. -/
noncomputable def rightFreeDifferential :
    (Fin 3 → pathAlgebra ℚ (SingleObj ThreeArrow)) →ₗ[ℚ]
      (Fin 3 → pathAlgebra ℚ (SingleObj ThreeArrow)) :=
  LinearMap.pi fun y ↦ threeDifferential ∘ₗ LinearMap.proj y +
    ∑ x, LinearMap.mulLeft ℚ (threeMatrix x y) ∘ₗ LinearMap.proj x

/-- The components of the right-free reading. -/
theorem rightFreeDifferential_apply (f : Fin 3 → pathAlgebra ℚ (SingleObj ThreeArrow)) (y : Fin 3) :
    rightFreeDifferential f y = threeDifferential (f y) + ∑ x, threeMatrix x y * f x := by
  simp [rightFreeDifferential, LinearMap.pi_apply, LinearMap.sum_apply]

/-- In the right-free reading, `d e_x = e_z a + e_y c`. -/
theorem rightFreeDifferential_single_x :
    rightFreeDifferential (Pi.single 0 1) = Pi.single 1 (gen .a) + Pi.single 2 (gen .c) := by
  funext y
  fin_cases y <;> simp [rightFreeDifferential_apply, Fin.sum_univ_three, threeMatrix,
    isDGAlgebra_threeDifferential.map_one_eq_zero]

/-- In the right-free reading, `d² e_x = e_y (ba - ab)`. -/
theorem rightFreeDifferential_rightFreeDifferential_single_x :
    rightFreeDifferential (rightFreeDifferential (Pi.single 0 1)) =
      Pi.single 2 (gen .b * gen .a - gen .a * gen .b) := by
  rw [rightFreeDifferential_single_x]
  funext y
  fin_cases y <;> simp [rightFreeDifferential_apply, Fin.sum_univ_three, threeMatrix,
    sub_eq_neg_add, add_comm]

/-- **The right-free reading is not a complex**: `d² e_x = e_y (ba - ab) ≠ 0`. -/
theorem rightFreeDifferential_rightFreeDifferential_single_x_ne_zero :
    rightFreeDifferential (rightFreeDifferential (Pi.single 0 1)) ≠ 0 := by
  rw [rightFreeDifferential_rightFreeDifferential_single_x]
  intro h
  have := congrFun h 2
  rw [Pi.single_eq_same, Pi.zero_apply, sub_eq_zero] at this
  exact gen_a_mul_gen_b_ne this.symm

end TwistedExamples

end TauCeti
