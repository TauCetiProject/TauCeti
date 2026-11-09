/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Generators
public import TauCeti.Algebra.Lie.E6.DoubledMinuscule.IntegralMatrix
public import TauCeti.Algebra.Lie.E6.Minuscule.CubicForm
public import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Scheme.ToralClosure.ConstantMultiplication
public import TauCeti.LinearAlgebra.Matrix.PartialMap

/-!
# The cross product on the doubled type-E6 minuscule module

The invariant cubic form `TauCeti.E6Minuscule.cubicForm` on `V = V(ϖ₁)` defines a bilinear map
`V × V → Vˣ`, and the same coefficients read on the dual define `Vˣ × Vˣ → V`. Together they form a
commutative bilinear product on the doubled module `V(ϖ₁) ⊕ V(ϖ₆) = V ⊕ Vˣ`, in the basis of the
doubled carrier: with `eᵢ` the basis of `V` and `fᵢ` that of `Vˣ`,

```text
e_k * e_j = ∑ᵢ c(k, j, i) fᵢ,    f_k * f_j = ∑ᵢ c(k, j, i) eᵢ,    e_k * f_j = 0,
```

where `c` is the cubic form. The product is homogeneous for the doubled weights, and every
structure constant is `-1`, `0` or `1`.

The main result is that the doubled carrier `TauCeti.E6DoubledMinuscule.groupScheme` preserves
this product, as a group scheme: every matrix-valued point over every commutative ring is
multiplicative for it. It suffices to check the generators. A numbered root subgroup has points
`1 + uX` with `X` a signed raising or lowering matrix; on `V` it is the minuscule raising or
lowering matrix and on `Vˣ` the negative transpose, so `X` is a derivation of the product exactly
because both are derivations of the cubic form, and the second-order terms vanish for weight
reasons. A weight-torus point is diagonal, and the product is homogeneous for the weights.

The product is a tool for controlling the carrier's points: a diagonal carrier point is forced to
be multiplicative along every nonzero structure constant, which pins it to the weight torus.

## Main declarations

* `TauCeti.E6DoubledMinuscule.crossProductCoefficient`: the structure constants on the block
  indices of `V ⊕ Vˣ`.
* `TauCeti.E6DoubledMinuscule.crossProductMatrix`: the structure matrices in the fifty-four
  matrix coordinates of the carrier.
* `TauCeti.E6DoubledMinuscule.crossProductMatrix_apply_eq_zero_of_weight_ne`: the product is
  homogeneous for the weights.
* `TauCeti.E6DoubledMinuscule.eq_of_eq_mul_of_crossProductMatrix_ne_zero`: a function
  multiplicative along the product is determined by its values at six basis indices of `V(ϖ₁)`.
* `TauCeti.E6DoubledMinuscule.preserves_crossProductMatrix_rootSubgroupPoints` and
  `TauCeti.E6DoubledMinuscule.preserves_crossProductMatrix_weightTorusPoints`: the generators
  preserve the product.
* `TauCeti.E6DoubledMinuscule.constantMultiplicationDefiningHopfIdeal_le_definingIdeal`: the
  carrier is a closed subgroup scheme of the stabilizer of the product.
* `TauCeti.E6DoubledMinuscule.preserves_crossProductMatrix_of_mem_points`: every carrier point
  preserves the product.

## References

* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Chapter 5, for the cross product of the exceptional Jordan algebra and its dual.
* The structure of the argument follows the triality product of the tripled type-`D₄` carrier in
  `TauCeti.Algebra.Lie.D4.Tripled.Triality.Product`.
-/

public section

open scoped Matrix

namespace TauCeti.E6DoubledMinuscule

open TauCeti.DynkinType

universe v

/-! ## The product -/

/-- **The structure constants of the cross product on `V(ϖ₁) ⊕ V(ϖ₆)`**, on the block indices:
the coefficient of the basis vector at `i` in the product of the basis vectors at `k` and `j`.
Two vectors of `V(ϖ₁)` multiply into `V(ϖ₆)` and two vectors of `V(ϖ₆)` into `V(ϖ₁)`, both through
the invariant cubic form; a vector of one block times a vector of the other is zero. -/
def crossProductCoefficient : Fin 27 ⊕ Fin 27 → Fin 27 ⊕ Fin 27 → Fin 27 ⊕ Fin 27 → ℤ
  | .inl k, .inr i, .inl j => E6Minuscule.cubicForm k j i
  | .inr k, .inl i, .inr j => E6Minuscule.cubicForm k j i
  | _, _, _ => 0

/-- Two vectors of `V(ϖ₁)` multiply into `V(ϖ₆)` through the cubic form. -/
@[simp]
theorem crossProductCoefficient_inl_inr_inl (k i j : Fin 27) :
    crossProductCoefficient (.inl k) (.inr i) (.inl j) = E6Minuscule.cubicForm k j i :=
  (rfl)

/-- Two vectors of `V(ϖ₆)` multiply into `V(ϖ₁)` through the cubic form. -/
@[simp]
theorem crossProductCoefficient_inr_inl_inr (k i j : Fin 27) :
    crossProductCoefficient (.inr k) (.inl i) (.inr j) = E6Minuscule.cubicForm k j i :=
  (rfl)

/-- Two vectors of `V(ϖ₁)` have no component in `V(ϖ₁)`. -/
@[simp]
theorem crossProductCoefficient_inl_inl_inl (k i j : Fin 27) :
    crossProductCoefficient (.inl k) (.inl i) (.inl j) = 0 :=
  (rfl)

/-- A vector of `V(ϖ₁)` times a vector of `V(ϖ₆)` has no component in `V(ϖ₁)`. -/
@[simp]
theorem crossProductCoefficient_inl_inl_inr (k i j : Fin 27) :
    crossProductCoefficient (.inl k) (.inl i) (.inr j) = 0 :=
  (rfl)

/-- A vector of `V(ϖ₁)` times a vector of `V(ϖ₆)` has no component in `V(ϖ₆)`. -/
@[simp]
theorem crossProductCoefficient_inl_inr_inr (k i j : Fin 27) :
    crossProductCoefficient (.inl k) (.inr i) (.inr j) = 0 :=
  (rfl)

/-- A vector of `V(ϖ₆)` times a vector of `V(ϖ₁)` has no component in `V(ϖ₁)`. -/
@[simp]
theorem crossProductCoefficient_inr_inl_inl (k i j : Fin 27) :
    crossProductCoefficient (.inr k) (.inl i) (.inl j) = 0 :=
  (rfl)

/-- A vector of `V(ϖ₆)` times a vector of `V(ϖ₁)` has no component in `V(ϖ₆)`. -/
@[simp]
theorem crossProductCoefficient_inr_inr_inl (k i j : Fin 27) :
    crossProductCoefficient (.inr k) (.inr i) (.inl j) = 0 :=
  (rfl)

/-- Two vectors of `V(ϖ₆)` have no component in `V(ϖ₆)`. -/
@[simp]
theorem crossProductCoefficient_inr_inr_inr (k i j : Fin 27) :
    crossProductCoefficient (.inr k) (.inr i) (.inr j) = 0 :=
  (rfl)

/-- **The structure matrices of the cross product** in the fifty-four matrix coordinates of the
doubled carrier. The entry `(i, j)` of the matrix at `k` is the coefficient of `eᵢ` in
`e_k * e_j`. -/
def crossProductMatrix (k : Fin 54) : Matrix (Fin 54) (Fin 54) ℤ :=
  Matrix.of fun i j =>
    crossProductCoefficient (matrixIndexEquiv.symm k) (matrixIndexEquiv.symm i)
      (matrixIndexEquiv.symm j)

/-- The entries of the cross product's structure matrices are its block structure constants. -/
@[simp]
theorem crossProductMatrix_apply (k i j : Fin 54) :
    crossProductMatrix k i j =
      crossProductCoefficient (matrixIndexEquiv.symm k) (matrixIndexEquiv.symm i)
        (matrixIndexEquiv.symm j) :=
  (rfl)

/-- The cross product is commutative. -/
theorem crossProductMatrix_apply_comm (k i j : Fin 54) :
    crossProductMatrix k i j = crossProductMatrix j i k := by
  simp only [crossProductMatrix_apply]
  rcases matrixIndexEquiv.symm k with k | k <;> rcases matrixIndexEquiv.symm i with i | i <;>
    rcases matrixIndexEquiv.symm j with j | j <;>
    simp [crossProductCoefficient, E6Minuscule.cubicForm_swap_left]

/-- Every nonzero structure constant is homogeneous for the doubled weights. -/
private theorem e6DoubledMinusculeWeight_eq_add_of_crossProductCoefficient_ne_zero
    {k i j : Fin 27 ⊕ Fin 27} (h : crossProductCoefficient k i j ≠ 0) :
    e6DoubledMinusculeWeight i = e6DoubledMinusculeWeight k + e6DoubledMinusculeWeight j := by
  rcases k with k | k <;> rcases i with i | i <;> rcases j with j | j <;>
    simp only [crossProductCoefficient, ne_eq, not_true_eq_false] at h <;>
    have hw := (E6Minuscule.cubicForm_ne_zero_iff _ _ _).mp h <;>
    simp only [e6DoubledMinusculeWeight_inl, e6DoubledMinusculeWeight_inr]
  · linear_combination -hw
  · linear_combination hw

/-- **The cross product is homogeneous for the weights**: the coefficient of `eᵢ` in `e_k * e_j`
vanishes unless the weight of `i` is the sum of the weights of `k` and `j`. -/
theorem crossProductMatrix_apply_eq_zero_of_weight_ne {k i j : Fin 54}
    (h : matrixWeight i ≠ matrixWeight k + matrixWeight j) :
    crossProductMatrix k i j = 0 :=
  not_not.mp fun hne => h <| by
    simpa only [matrixWeight_apply] using
      e6DoubledMinusculeWeight_eq_add_of_crossProductCoefficient_ne_zero hne

/-- Every structure constant of the cross product is `-1`, `0` or `1`. -/
theorem crossProductMatrix_apply_eq_neg_one_or_eq_zero_or_eq_one (k i j : Fin 54) :
    crossProductMatrix k i j = -1 ∨ crossProductMatrix k i j = 0 ∨
      crossProductMatrix k i j = 1 := by
  rw [crossProductMatrix_apply]
  rcases matrixIndexEquiv.symm k with k | k <;> rcases matrixIndexEquiv.symm i with i | i <;>
    rcases matrixIndexEquiv.symm j with j | j <;>
    simp [crossProductCoefficient, E6Minuscule.cubicForm_eq_neg_one_or_eq_zero_or_eq_one]

/-! ## Functions multiplicative along the product

A function `t` on the basis indices is multiplicative along the product when `tᵢ = tₖ tⱼ` whenever
`eᵢ` occurs in `e_k * e_j`. Starting from the six indices `0`, `1`, `2`, `4`, `5`, `11` of
`V(ϖ₁)`, whose weights form a basis of the weight lattice, every other index is reached in four
rounds, each new index occurring in a nonzero structure constant together with two indices already
reached. The rounds are computed on the block indices. -/

/-- The basis indices of `V(ϖ₁)` from which multiplicativity along the product propagates. -/
private def seedIndices : Finset (Fin 27 ⊕ Fin 27) :=
  {.inl 0, .inl 1, .inl 2, .inl 4, .inl 5, .inl 11}

/-- The block indices reached from `seedIndices` in one round. -/
private def firstIndices : Finset (Fin 27 ⊕ Fin 27) :=
  {.inl 0, .inl 1, .inl 2, .inl 4, .inl 5, .inl 11, .inr 23, .inr 25, .inr 26}

/-- The block indices reached in two rounds. -/
private def secondIndices : Finset (Fin 27 ⊕ Fin 27) :=
  {.inl 0, .inl 1, .inl 2, .inl 4, .inl 5, .inl 7, .inl 8, .inl 10, .inl 11, .inl 12, .inl 13,
    .inl 15, .inl 18, .inl 19, .inr 2, .inr 4, .inr 5, .inr 7, .inr 8, .inr 10, .inr 11, .inr 12,
    .inr 13, .inr 15, .inr 18, .inr 19, .inr 23, .inr 25, .inr 26}

/-- The block indices reached in three rounds: all but `3`, `22` and `24` of each block. -/
private def thirdIndices : Finset (Fin 27 ⊕ Fin 27) :=
  Finset.univ.filter fun x => Sum.elim id id x ∉ ({3, 22, 24} : Finset (Fin 27))

/-- One round of propagation: an index occurring in a nonzero structure constant together with
two indices of `S` is reached from `S`. -/
private def Reached (S : Finset (Fin 27 ⊕ Fin 27)) (x : Fin 27 ⊕ Fin 27) : Prop :=
  x ∈ S ∨ ∃ k ∈ S, ∃ j ∈ S, crossProductCoefficient k x j ≠ 0 ∨
    crossProductCoefficient x k j ≠ 0 ∨ crossProductCoefficient k j x ≠ 0

private instance (S : Finset (Fin 27 ⊕ Fin 27)) : DecidablePred (Reached S) := fun _ => by
  unfold Reached
  infer_instance

private theorem firstIndices_reached : ∀ x ∈ firstIndices, Reached seedIndices x := by
  decide +kernel

private theorem secondIndices_reached : ∀ x ∈ secondIndices, Reached firstIndices x := by
  decide +kernel

private theorem thirdIndices_reached : ∀ x ∈ thirdIndices, Reached secondIndices x := by
  decide +kernel

private theorem all_reached : ∀ x, Reached thirdIndices x := by
  decide +kernel

/-- A function multiplicative along the block structure constants and trivial on `S` is trivial
on every index reached from `S`. -/
private theorem eq_one_of_reached {G : Type*} [CommGroup G] {f : Fin 27 ⊕ Fin 27 → G}
    (hf : ∀ k i j, crossProductCoefficient k i j ≠ 0 → f i = f k * f j)
    {S : Finset (Fin 27 ⊕ Fin 27)} (hS : ∀ a ∈ S, f a = 1) {x : Fin 27 ⊕ Fin 27}
    (hx : Reached S x) : f x = 1 :=
  hx.elim (hS x) (ConstantMultiplication.eq_one_of_eq_mul_of_ne_zero (T := S) hf hS)

/-- **A function multiplicative along the cross product is determined by its values at the
indices `0`, `1`, `2`, `4`, `5` and `11` of `V(ϖ₁)`.** Here `t` and `u` take values in a
commutative group and satisfy `tᵢ = tₖ tⱼ` and `uᵢ = uₖ uⱼ` whenever the coefficient of `eᵢ` in
`e_k * e_j` is nonzero. -/
theorem eq_of_eq_mul_of_crossProductMatrix_ne_zero {G : Type*} [CommGroup G]
    {t u : Fin 54 → G}
    (ht : ∀ k i j, crossProductMatrix k i j ≠ 0 → t i = t k * t j)
    (hu : ∀ k i j, crossProductMatrix k i j ≠ 0 → u i = u k * u j)
    (hseed : ∀ a ∈ ({0, 1, 2, 4, 5, 11} : Finset (Fin 27)),
      t (matrixIndexEquiv (.inl a)) = u (matrixIndexEquiv (.inl a))) : t = u := by
  -- The quotient `t / u`, read on the block indices, is multiplicative along the product and
  -- trivial at the seeds.
  let f : Fin 27 ⊕ Fin 27 → G := fun x => t (matrixIndexEquiv x) / u (matrixIndexEquiv x)
  have hf : ∀ k i j, crossProductCoefficient k i j ≠ 0 → f i = f k * f j := fun k i j h => by
    have h' : crossProductMatrix (matrixIndexEquiv k) (matrixIndexEquiv i)
        (matrixIndexEquiv j) ≠ 0 := by
      simpa only [crossProductMatrix_apply, Equiv.symm_apply_apply] using h
    simp only [f, ht _ _ _ h', hu _ _ _ h', div_mul_div_comm]
  have hseeds : ∀ a ∈ seedIndices, f a = 1 := by
    simp only [seedIndices, Finset.mem_insert, Finset.mem_singleton]
    rintro a (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      exact div_eq_one.mpr (hseed _ (by decide))
  have hfirst : ∀ a ∈ firstIndices, f a = 1 := fun a ha =>
    eq_one_of_reached hf hseeds (firstIndices_reached a ha)
  have hsecond : ∀ a ∈ secondIndices, f a = 1 := fun a ha =>
    eq_one_of_reached hf hfirst (secondIndices_reached a ha)
  have hthird : ∀ a ∈ thirdIndices, f a = 1 := fun a ha =>
    eq_one_of_reached hf hsecond (thirdIndices_reached a ha)
  funext a
  have ha := eq_one_of_reached hf hthird (all_reached (matrixIndexEquiv.symm a))
  simpa only [f, Equiv.apply_symm_apply, div_eq_one] using ha

/-! ## Products with a root-operator matrix -/

/-- The simple reflection of a numbered root operator on the matrix coordinates. -/
private def rootReflection (k : Fin 6 ⊕ Fin 6) (a : Fin 54) : Fin 54 :=
  matrixIndexEquiv (reflection (Sum.elim id id k) (matrixIndexEquiv.symm a))

private theorem rootReflection_involutive (k : Fin 6 ⊕ Fin 6) :
    Function.Involutive (rootReflection k) := fun a => by
  simp [rootReflection]

/-- A root-operator matrix is the signed matrix of the partial map given by its simple
reflection, defined where the weight permits the move. -/
private theorem rootIntMatrix_apply_eq_ite (k : Fin 6 ⊕ Fin 6) (a b : Fin 54) :
    rootIntMatrix k a b =
      if matrixWeight b (Sum.elim id id k) = Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) k ∧
          a = rootReflection k b
        then summandSign (matrixIndexEquiv.symm b) else 0 := by
  rw [rootIntMatrix_apply, rootReflection]
  split_ifs <;> simp_all

/-- The block form of the derivation equation for a numbered root operator. On the pattern
`V(ϖ₁) × V(ϖ₁) → V(ϖ₆)` it is the invariance of the cubic form under the operator itself, and on
`V(ϖ₆) × V(ϖ₆) → V(ϖ₁)` its invariance under the opposite operator. -/
private theorem crossProductCoefficient_derivation (k : Fin 6 ⊕ Fin 6)
    (z x y : Fin 27 ⊕ Fin 27) :
    (if e6DoubledMinusculeWeight (reflection (Sum.elim id id k) x) (Sum.elim id id k) =
          Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) k then
        summandSign (reflection (Sum.elim id id k) x) *
          crossProductCoefficient z (reflection (Sum.elim id id k) x) y
      else 0) =
      (if e6DoubledMinusculeWeight z (Sum.elim id id k) =
            Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) k then
          summandSign z * crossProductCoefficient (reflection (Sum.elim id id k) z) x y
        else 0) +
        if e6DoubledMinusculeWeight y (Sum.elim id id k) =
            Sum.elim (fun _ ↦ -1) (fun _ ↦ 1) k then
          crossProductCoefficient z x (reflection (Sum.elim id id k) y) * summandSign y
        else 0 := by
  rcases k with r | r <;> rcases z with z | z <;> rcases x with x | x <;> rcases y with y | y <;>
    simp only [Sum.elim_inl, Sum.elim_inr, id, reflection_inl, reflection_inr,
      crossProductCoefficient, e6DoubledMinusculeWeight_inl, e6DoubledMinusculeWeight_inr,
      summandSign_inl, summandSign_inr, Pi.neg_apply,
      TauCeti.E6Minuscule.e6MinusculeWeight_reflection_apply_self, neg_neg, neg_inj, mul_zero,
      zero_mul, ite_self, add_zero]
  -- Four cases survive, a raising or lowering operator on either nonzero block pattern; each is
  -- the coordinate form of the invariance of the cubic form under one of the two operators.
  · have h := E6Minuscule.cubicForm_raising_invariant r z y x
    split_ifs at h ⊢ <;> omega
  · have h := E6Minuscule.cubicForm_lowering_invariant r z y x
    split_ifs at h ⊢ <;> omega
  · have h := E6Minuscule.cubicForm_lowering_invariant r z y x
    split_ifs at h ⊢ <;> omega
  · have h := E6Minuscule.cubicForm_raising_invariant r z y x
    split_ifs at h ⊢ <;> omega

/-- Every numbered root-operator matrix is a derivation of the cross product. -/
private theorem rootIntMatrix_mul_crossProductMatrix (k : Fin 6 ⊕ Fin 6) (c : Fin 54) :
    rootIntMatrix k * crossProductMatrix c =
      ∑ d, rootIntMatrix k d c • crossProductMatrix d + crossProductMatrix c * rootIntMatrix k := by
  ext a b
  rw [Matrix.add_apply,
    Matrix.mul_apply_of_apply_eq_ite_weight_left (rootReflection_involutive k)
      (rootIntMatrix_apply_eq_ite k),
    Matrix.sum_smul_apply_of_apply_eq_ite_weight (rootIntMatrix_apply_eq_ite k),
    Matrix.mul_apply_of_apply_eq_ite_weight_right (rootIntMatrix_apply_eq_ite k)]
  -- Read the three matrix coordinates as block indices.
  simpa [rootReflection] using crossProductCoefficient_derivation k (matrixIndexEquiv.symm c)
    (matrixIndexEquiv.symm a) (matrixIndexEquiv.symm b)

/-- The second-order terms of a numbered root-operator matrix on the cross product vanish: two
moves by the same simple root would raise a weight coordinate to `±2`. -/
private theorem sum_smul_crossProductMatrix_mul_rootIntMatrix (k : Fin 6 ⊕ Fin 6) (c : Fin 54) :
    (∑ d, rootIntMatrix k d c • crossProductMatrix d) * rootIntMatrix k = 0 := by
  ext a b
  rw [Matrix.mul_apply_of_apply_eq_ite_weight_right (rootIntMatrix_apply_eq_ite k),
    Matrix.sum_smul_apply_of_apply_eq_ite_weight (rootIntMatrix_apply_eq_ite k),
    Matrix.zero_apply]
  split_ifs with hb hc
  · rw [crossProductMatrix_apply_eq_zero_of_weight_ne, mul_zero, zero_mul]
    intro h
    have hr := congrFun h (Sum.elim id id k)
    simp only [rootReflection, matrixWeight_apply, Equiv.symm_apply_apply, Pi.add_apply,
      e6DoubledMinusculeWeight_reflection_apply_self] at hr hb hc
    rcases e6DoubledMinusculeWeight_apply_eq_neg_one_or_eq_zero_or_eq_one
      (matrixIndexEquiv.symm a) (Sum.elim id id k) with ha | ha | ha <;>
      rcases k with r | r <;> simp_all
  · rw [zero_mul]
  · rfl

/-! ## Invariance under the generators -/

/-- **A numbered root-subgroup point preserves the cross product.** -/
theorem preserves_crossProductMatrix_rootSubgroupPoints (k : Fin 6 ⊕ Fin 6) (A : Type v)
    [CommRing A] (u : Multiplicative A) :
    ConstantMultiplication.Preserves ℤ 54 crossProductMatrix
      ((rootSubgroupPoints k A u : Matrix.GeneralLinearGroup (Fin 54) A) :
        Matrix (Fin 54) (Fin 54) A) := by
  have hmap : (rootIntMatrix k).map (Int.cast : ℤ → A) =
      (rootIntMatrix k).map (algebraMap ℤ A) := by
    ext a b
    simp
  rw [coe_rootSubgroupPoints_eq_one_add_smul, hmap]
  exact ConstantMultiplication.preserves_one_add_smul crossProductMatrix
    (rootIntMatrix_mul_crossProductMatrix k) (sum_smul_crossProductMatrix_mul_rootIntMatrix k) _

/-- **A weight-torus point preserves the cross product**, because the product is homogeneous for
the weights. -/
theorem preserves_crossProductMatrix_weightTorusPoints (A : Type v) [CommRing A]
    (s : Fin 6 → Aˣ) :
    ConstantMultiplication.Preserves ℤ 54 crossProductMatrix
      ((weightTorusPoints A s : Matrix.GeneralLinearGroup (Fin 54) A) :
        Matrix (Fin 54) (Fin 54) A) := by
  rw [coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe,
    ConstantMultiplication.preserves_diagonal_iff]
  intro k i j
  by_cases h : matrixWeight i = matrixWeight k + matrixWeight j
  · rw [h, torusCharacter_add, Units.val_mul]
    ring
  · rw [crossProductMatrix_apply_eq_zero_of_weight_ne h, map_zero, mul_zero, mul_zero, zero_mul]

/-- The generic root-subgroup matrices of the carrier preserve the cross product, in the form
required by the generic toral-closure criterion. -/
private theorem preserves_crossProductMatrix_kostantRootSubgroupMatrix (k : Fin 6 ⊕ Fin 6)
    (A : Type) [CommRing A] (q : WithConv (AdditiveGroup.coordinateHopfAlgebra ℤ →ₐ[ℤ] A)) :
    ConstantMultiplication.Preserves ℤ 54 crossProductMatrix
      ((UniversalEnvelopingAlgebra.kostantRootSubgroupMatrix
        (TauCeti.serreRootGenerator (CartanMatrix.E 6)ᵀ) (TauCeti.serreH ℚ (CartanMatrix.E 6)ᵀ)
        rep lattice.toAddSubgroup rep_kostantForm_mem_lattice k
        (isNilpotent_rep_serreRootGenerator k) matrixBasis q :
          Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) := by
  have h := coe_rootSubgroupPoints k A (AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A) q)
  rw [MulEquiv.symm_apply_apply] at h
  rw [← h]
  exact preserves_crossProductMatrix_rootSubgroupPoints k A _

/-- The generic weight-torus matrices of the carrier preserve the cross product, in the form
required by the generic toral-closure criterion. -/
private theorem preserves_crossProductMatrix_kostantTorusMatrix :
    letI := Fintype.ofFinite (Fin 6)
    ∀ (A : Type) [CommRing A] (s : Fin 6 → Aˣ),
      ConstantMultiplication.Preserves ℤ 54 crossProductMatrix
        ((UniversalEnvelopingAlgebra.kostantTorusMatrix lattice.toAddSubgroup matrixBasis
          matrixWeight s : Matrix.GeneralLinearGroup (Fin 54) A) : Matrix (Fin 54) (Fin 54) A) := by
  intro A _ s
  -- The generic criterion states the torus matrix with the `Fintype` instance obtained from
  -- `Finite`; `convert` identifies it with the standard instance on `Fin 6`.
  convert preserves_crossProductMatrix_weightTorusPoints A s using 2
  rw [coe_weightTorusPoints]
  congr
  exact Subsingleton.elim _ _

/-- **The doubled carrier is a closed subgroup scheme of the stabilizer of the cross product.**
The Hopf ideal cutting out the subgroup scheme of `GL₅₄` preserving the product is contained in
the defining ideal of the carrier. -/
theorem constantMultiplicationDefiningHopfIdeal_le_definingIdeal :
    ConstantMultiplication.definingHopfIdeal ℤ 54 crossProductMatrix ≤ definingIdeal := by
  rw [definingIdeal_def]
  open TauCeti.UniversalEnvelopingAlgebra in
  exact constantMultiplicationDefiningHopfIdeal_le_kostantToralDefiningIdeal_of_generators
    _ _ _ _ _ _ _ _ _ preserves_crossProductMatrix_kostantRootSubgroupMatrix
    preserves_crossProductMatrix_kostantTorusMatrix

/-- **Every point of the doubled carrier preserves the cross product**, over every commutative
ring, including nonreduced ones. -/
theorem preserves_crossProductMatrix_of_mem_points {A : Type v} [CommRing A]
    {g : Matrix.GeneralLinearGroup (Fin 54) A} (hg : g ∈ points A) :
    ConstantMultiplication.Preserves ℤ 54 crossProductMatrix
      (g : Matrix (Fin 54) (Fin 54) A) := by
  rw [points_def, definingIdeal_def,
    ← UniversalEnvelopingAlgebra.kostantToralPointsSubgroup_def] at hg
  exact UniversalEnvelopingAlgebra.preserves_of_mem_kostantToralPointsSubgroup_of_generators
    _ _ _ _ _ _ _ _ _ preserves_crossProductMatrix_kostantRootSubgroupMatrix
    preserves_crossProductMatrix_kostantTorusMatrix A hg

end TauCeti.E6DoubledMinuscule
