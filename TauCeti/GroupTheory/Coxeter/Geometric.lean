/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.GroupTheory.Coxeter.Basic
public import Mathlib.LinearAlgebra.BilinearForm.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RepresentationTheory.Basic

/-!
# The standard geometric representation of a Coxeter system

Let `cs : CoxeterSystem M W` be a Coxeter system with Coxeter matrix `M : CoxeterMatrix B`. This
file builds the representation of `W` that Jacques Tits used to analyse Coxeter groups: the free
real vector space `B →₀ ℝ` on the index set, with the `i`-th basis vector read as the `i`-th
*simple root* `αᵢ`, carries the symmetric bilinear form

```text
B(αᵢ, αᵢ') = -cos (π / M i i'),
```

and `W` acts with the `i`-th simple reflection acting as the orthogonal reflection
`v ↦ v - 2 B(αᵢ, v) αᵢ` in the hyperplane `B(αᵢ, ·) = 0`. Mathlib's convention that an entry
`M i i' = 0` stands for `∞` is exactly right here: `π / 0` is `0` in Lean, so such a pair
contributes `-cos 0 = -1`, the degenerate Gram matrix of a pair of parallel walls. The diagonal
entries are `-cos π = 1`, so every simple root is a unit vector.

## What this file is for

The Coxeter relations hold in this representation, which is what makes the action exist; but the
point of building it is the *converse* divisibility that comes out of it. The defining relations
of a Coxeter group give only `orderOf (s i * s i') ∣ M i i'`
(`CoxeterSystem.simple_mul_simple_pow`), and a presentation can a priori collapse. Restricting
the action to the plane spanned by two simple roots computes the order on the nose: that plane is
Euclidean as soon as `M i i'` is finite and at least two, the two reflections compose to the
rotation through `2 π / M i i'`, and a rotation through `2 π / m` has order exactly `m`. When
`M i i' = 0` the plane is degenerate and the composite is a shear, of infinite order. So

```text
orderOf (cs.simple i * cs.simple i') = M i i'
```

uniformly in `i` and `i'`, with `0` read as `∞`
(`CoxeterSystem.orderOf_simple_mul_simple`). Three further collapses are ruled out at the same
time: a simple reflection is never the identity, it has order exactly two, and distinct indices
give distinct simple reflections.

Exactness, not just divisibility, is what a braid move needs. The braid move at `(i, i')` rewrites
the alternating word `s i s i' s i ⋯` of length `M i i'` into the alternating word of the same
length that starts with `s i'`, and the induction step of **Matsumoto's theorem** needs those words
to be reduced. Were `orderOf (s i * s i')` a proper divisor `d` of `M i i'`, the alternating word of
length `2 * d` would already be trivial and the length-`M i i'` one would not be reduced.

## The route

Everything rests on one two-dimensional computation. In the
coordinates `αᵢ, αᵢ'` the composite `σᵢ σᵢ'` of the two simple reflections has matrix
`!![4 c ^ 2 - 1, -(2 c); 2 c, -1]` with `c = cos (π / M i i')`, of determinant one and trace
`2 cos (2 π / M i i')`; an induction on the exponent, whose step is the pair of addition formulas
for `cos` and `sin`, turns its `k`-th power into the rotation matrix through `2 k π / M i i'`
written in those coordinates. Two consequences are read off. At `k = M i i'` the angle is `2 π`
and both simple roots are fixed; since the Gram matrix of the two simple roots is invertible, the
plane splits off its orthogonal complement -- on which the composite is the identity, both
reflections fixing it -- so the braid relation holds on the whole space. And `σᵢ σᵢ'` can fix the
first simple root only if the angle `2 k π / M i i'` is a multiple of `2 π`, which pins the order
down.

The second simple root is handled without a second induction: `σᵢ' σᵢ` is the inverse of
`σᵢ σᵢ'`, and the two commute, so the first computation with the indices exchanged transfers.

## Main results

* `CoxeterMatrix.geometricForm`: **the canonical bilinear form** of a Coxeter matrix, with
  `CoxeterMatrix.geometricForm_single_single` its Gram matrix and
  `CoxeterMatrix.geometricForm_comm` its symmetry.
* `CoxeterMatrix.geometricReflection`: **the simple reflections**, with
  `CoxeterMatrix.geometricReflection_mul_self` saying that they are involutions,
  `CoxeterMatrix.geometricReflection_apply_single_self` that the `i`-th one negates the `i`-th
  simple root, and `CoxeterMatrix.geometricForm_geometricReflection` that they are orthogonal for
  the canonical form.
* `CoxeterMatrix.isLiftable_geometricReflection`: **the simple reflections satisfy the Coxeter
  relations**, so they lift along `CoxeterSystem.lift`.
* `CoxeterSystem.geometricRepresentation`: **the standard geometric representation**, with
  `CoxeterSystem.geometricRepresentation_simple` its values on the simple reflections and
  `CoxeterSystem.geometricForm_geometricRepresentation` its orthogonality.
* `CoxeterSystem.simple_mul_simple_pow_eq_one_iff` and
  `CoxeterSystem.orderOf_simple_mul_simple`: **the entry `M i i'` is the exact order of
  `s i * s i'`**, not merely a multiple of it.
* `CoxeterSystem.simple_ne_one`, `CoxeterSystem.orderOf_simple` and
  `CoxeterSystem.simple_injective`: **a simple reflection has order exactly two, and distinct
  indices give distinct simple reflections**.

## What is not proved here

Tits' theorem proper -- that the geometric representation is *faithful*, so that a Coxeter group
is a reflection group -- is a strictly stronger statement, proved by the "root bookkeeping"
argument that tracks which simple roots a reduced word makes negative. It is not proved here, and
none of the results above needs it: the exact order of a product of two simple reflections only
needs the representation to be nontrivial on a single rank-two plane.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Springer (2002), Ch. V, Section 4.3.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 5.3.
-/

public section

open Real

namespace CoxeterMatrix

variable {B : Type*} (M : CoxeterMatrix B)

/-! ### The canonical bilinear form -/

/-- **The canonical bilinear form of a Coxeter matrix** on the free real vector space on the
index set: the symmetric form whose Gram matrix in the basis of simple roots has entries
`-cos (π / M i i')`. The diagonal entries are `-cos π = 1`, and a pair of indices with no
relation between them (`M i i' = 0`, read as `∞`) contributes `-cos 0 = -1`. -/
noncomputable def geometricForm : LinearMap.BilinForm ℝ (B →₀ ℝ) :=
  Finsupp.linearCombination ℝ fun i ↦
    Finsupp.linearCombination ℝ fun i' ↦ -cos (π / M i i')

/-- **The Gram matrix of the canonical form** in the basis of simple roots. -/
@[simp]
theorem geometricForm_single_single (i i' : B) (a b : ℝ) :
    M.geometricForm (Finsupp.single i a) (Finsupp.single i' b) =
      a * b * -cos (π / M i i') := by
  simp only [geometricForm, Finsupp.linearCombination_single, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- The diagonal entries of the canonical form are `1`, the Coxeter matrix having `1` on its
diagonal and `-cos π` being `1`. -/
theorem geometricForm_single_self (i : B) :
    M.geometricForm (Finsupp.single i 1) (Finsupp.single i 1) = 1 := by
  simp

/-- **The canonical form is symmetric**, the Coxeter matrix being symmetric. -/
theorem geometricForm_comm (u v : B →₀ ℝ) : M.geometricForm u v = M.geometricForm v u := by
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add u₁ u₂ h₁ h₂ => simp [h₁, h₂]
  | single i a =>
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add v₁ v₂ h₁ h₂ => simp [h₁, h₂]
    | single i' b =>
      rw [geometricForm_single_single, geometricForm_single_single, M.symmetric i i']
      ring

/-! ### The simple reflections -/

/-- **The simple reflection of the geometric representation** attached to an index `i`: the
reflection `v ↦ v - 2 B(αᵢ, v) αᵢ` of the free real vector space on the index set in the
hyperplane orthogonal to the `i`-th simple root `αᵢ`, for the canonical form `B`. -/
noncomputable def geometricReflection (i : B) : Module.End ℝ (B →₀ ℝ) :=
  LinearMap.id -
    (LinearMap.toSpanSingleton ℝ (B →₀ ℝ) (Finsupp.single i 1)).comp
      ((2 : ℝ) • M.geometricForm (Finsupp.single i 1))

/-- **The reflection formula** `v ↦ v - 2 B(αᵢ, v) αᵢ`. -/
@[simp]
theorem geometricReflection_apply (i : B) (v : B →₀ ℝ) :
    M.geometricReflection i v =
      v - (2 * M.geometricForm (Finsupp.single i 1) v) • Finsupp.single i 1 := by
  simp [geometricReflection, LinearMap.toSpanSingleton_apply]

/-- **The `i`-th simple reflection negates the `i`-th simple root.** -/
theorem geometricReflection_apply_single_self (i : B) :
    M.geometricReflection i (Finsupp.single i 1) = -Finsupp.single i (1 : ℝ) := by
  rw [geometricReflection_apply, geometricForm_single_self]
  module

/-- A vector orthogonal to the `i`-th simple root is fixed by the `i`-th simple reflection. -/
theorem geometricReflection_apply_of_eq_zero {i : B} {v : B →₀ ℝ}
    (h : M.geometricForm (Finsupp.single i 1) v = 0) : M.geometricReflection i v = v := by
  simp [h]

/-- **The simple reflections are involutions.** -/
theorem geometricReflection_mul_self (i : B) :
    M.geometricReflection i * M.geometricReflection i = 1 := by
  refine LinearMap.ext fun v ↦ ?_
  simp only [Module.End.mul_apply, Module.End.one_apply, geometricReflection_apply, map_sub,
    map_smul, geometricForm_single_self]
  module

/-- **The simple reflections preserve the canonical form**, so the geometric representation is
orthogonal for it. -/
theorem geometricForm_geometricReflection (i : B) (u v : B →₀ ℝ) :
    M.geometricForm (M.geometricReflection i u) (M.geometricReflection i v) =
      M.geometricForm u v := by
  simp only [geometricReflection_apply, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul, geometricForm_single_self,
    M.geometricForm_comm (Finsupp.single i 1) u]
  ring

/-! ### The rank-two computation -/

section RankTwo

variable (i i' : B)

/-- **One step of the rotation.** On the plane spanned by the two simple roots `αᵢ` and `αᵢ'`,
the composite of the two simple reflections acts by the matrix
`!![4 c ^ 2 - 1, -(2 c); 2 c, -1]` of determinant one, where `c = cos (π / M i i')`. For the
degenerate instance `i = i'` the two coordinates coincide and the formula still holds, both
sides then being the identity. -/
private theorem geometricReflection_mul_apply (x y : ℝ) :
    (M.geometricReflection i * M.geometricReflection i')
        (x • Finsupp.single i (1 : ℝ) + y • Finsupp.single i' (1 : ℝ)) =
      ((4 * cos (π / M i i') ^ 2 - 1) * x - 2 * cos (π / M i i') * y) •
          Finsupp.single i (1 : ℝ) +
        (2 * cos (π / M i i') * x - y) • Finsupp.single i' (1 : ℝ) := by
  simp only [Module.End.mul_apply, geometricReflection_apply, map_add, map_sub, map_smul,
    geometricForm_single_single, CoxeterMatrix.diagonal, Nat.cast_one, div_one, Real.cos_pi,
    M.symmetric i' i]
  module

/-- The composite of the two simple reflections in the other order is its inverse. -/
private theorem geometricReflection_mul_mul_geometricReflection_mul :
    (M.geometricReflection i * M.geometricReflection i') *
        (M.geometricReflection i' * M.geometricReflection i) = 1 := by
  rw [mul_assoc, ← mul_assoc (M.geometricReflection i'), M.geometricReflection_mul_self i',
    one_mul, M.geometricReflection_mul_self i]

/-- A vector orthogonal to both simple roots is fixed by every power of the rotation. -/
private theorem pow_apply_eq_self {v : B →₀ ℝ}
    (h : M.geometricForm (Finsupp.single i 1) v = 0)
    (h' : M.geometricForm (Finsupp.single i' 1) v = 0) (k : ℕ) :
    ((M.geometricReflection i * M.geometricReflection i') ^ k) v = v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, Module.End.mul_apply,
      M.geometricReflection_apply_of_eq_zero h', M.geometricReflection_apply_of_eq_zero h]

/-- The `cos` half of the induction step of `pow_geometricReflection_mul_apply_single`, as an
identity of real numbers: the Pythagorean relation between `s` and `c` is what makes it hold. -/
private theorem cos_rotation_step {u w c s : ℝ} (hs : s ≠ 0) (hsc : s ^ 2 = 1 - c ^ 2) :
    (4 * c ^ 2 - 1) * (u + c * (w / s)) - 2 * c * (w / s) =
      u * (2 * c ^ 2 - 1) - w * (2 * s * c) +
        c * ((w * (2 * c ^ 2 - 1) + u * (2 * s * c)) / s) := by
  field_simp
  linear_combination (2 * c * w) * hsc

/-- The `sin` half of the induction step of `pow_geometricReflection_mul_apply_single`. -/
private theorem sin_rotation_step {u w c s : ℝ} (hs : s ≠ 0) :
    2 * c * (u + c * (w / s)) - w / s = (w * (2 * c ^ 2 - 1) + u * (2 * s * c)) / s := by
  field_simp
  ring

/-- **The rotation formula.** Writing `θ = π / M i i'`, the `k`-th power of the composite of the
two simple reflections acts on the first simple root as the rotation through the angle `2 k θ`
of the plane the two simple roots span, the plane being Euclidean for the canonical form as soon
as `sin θ ≠ 0`. -/
private theorem pow_geometricReflection_mul_apply_single
    (hs : sin (π / M i i') ≠ 0) (k : ℕ) :
    ((M.geometricReflection i * M.geometricReflection i') ^ k) (Finsupp.single i 1) =
      (cos (2 * k * (π / M i i')) +
            cos (π / M i i') * (sin (2 * k * (π / M i i')) / sin (π / M i i'))) •
          Finsupp.single i (1 : ℝ) +
        (sin (2 * k * (π / M i i')) / sin (π / M i i')) • Finsupp.single i' (1 : ℝ) := by
  have hsc : sin (π / M i i') ^ 2 = 1 - cos (π / M i i') ^ 2 := by
    have := Real.sin_sq_add_cos_sq (π / M i i')
    linarith
  induction k with
  | zero => simp
  | succ k ih =>
    have hangle : 2 * ((k : ℝ) + 1) * (π / M i i') =
        2 * k * (π / M i i') + 2 * (π / M i i') := by ring
    rw [pow_succ', Module.End.mul_apply, ih, M.geometricReflection_mul_apply i i']
    push_cast
    rw [hangle, Real.cos_add, Real.sin_add, Real.cos_two_mul, Real.sin_two_mul,
      cos_rotation_step hs hsc, sin_rotation_step hs]

/-- At `k = M i i'` the angle `2 k θ` is `2 π`, so the rotation returns the first simple root. -/
private theorem pow_geometricReflection_mul_apply_single_left
    (hs : sin (π / M i i') ≠ 0) (hm : (M i i' : ℝ) ≠ 0) :
    ((M.geometricReflection i * M.geometricReflection i') ^ M i i') (Finsupp.single i 1) =
      Finsupp.single i (1 : ℝ) := by
  have hangle : 2 * (M i i' : ℝ) * (π / M i i') = 2 * π := by field_simp
  rw [M.pow_geometricReflection_mul_apply_single i i' hs, hangle, Real.cos_two_pi,
    Real.sin_two_pi]
  simp

/-- The same for the second simple root, by the inverse rotation with the indices exchanged. -/
private theorem pow_geometricReflection_mul_apply_single_right
    (hs : sin (π / M i i') ≠ 0) (hm : (M i i' : ℝ) ≠ 0) :
    ((M.geometricReflection i * M.geometricReflection i') ^ M i i') (Finsupp.single i' 1) =
      Finsupp.single i' (1 : ℝ) := by
  have h1 := M.geometricReflection_mul_mul_geometricReflection_mul i i'
  have h2 := M.geometricReflection_mul_mul_geometricReflection_mul i' i
  have hcomm : Commute (M.geometricReflection i * M.geometricReflection i')
      (M.geometricReflection i' * M.geometricReflection i) := h1.trans h2.symm
  have hsym : M i' i = M i i' := M.symmetric i' i
  have hswap := M.pow_geometricReflection_mul_apply_single_left i' i (by rwa [hsym]) (by rwa [hsym])
  rw [hsym] at hswap
  have hinv : (M.geometricReflection i * M.geometricReflection i') ^ M i i' *
      (M.geometricReflection i' * M.geometricReflection i) ^ M i i' = 1 := by
    rw [← hcomm.mul_pow, h1, one_pow]
  calc ((M.geometricReflection i * M.geometricReflection i') ^ M i i') (Finsupp.single i' 1)
      = ((M.geometricReflection i * M.geometricReflection i') ^ M i i')
          (((M.geometricReflection i' * M.geometricReflection i) ^ M i i') (Finsupp.single i' 1)) :=
        by rw [hswap]
    _ = Finsupp.single i' (1 : ℝ) := by
        rw [← Module.End.mul_apply, hinv, Module.End.one_apply]

/-- **The braid relation in the geometric representation**, for a finite Coxeter-matrix entry at
least two: the rotation through `2 π / M i i'` has order dividing `M i i'`. The plane spanned by
the two simple roots is Euclidean, so it splits off its orthogonal complement, on which the
rotation is the identity. -/
private theorem geometricReflection_mul_pow_eq_one (hm : 2 ≤ M i i') :
    (M.geometricReflection i * M.geometricReflection i') ^ M i i' = 1 := by
  have hm0 : (M i i' : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hpos : 0 < π / (M i i' : ℝ) := by
    have : (0 : ℝ) < M i i' := by positivity
    positivity
  have hlt : π / (M i i' : ℝ) < π := by
    refine div_lt_self Real.pi_pos ?_
    have : (2 : ℝ) ≤ M i i' := by exact_mod_cast hm
    linarith
  have hs : sin (π / M i i') ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt)
  have hden : (1 : ℝ) - cos (π / M i i') ^ 2 ≠ 0 := by
    have hsq := Real.sin_sq_add_cos_sq (π / (M i i' : ℝ))
    have : sin (π / (M i i' : ℝ)) ^ 2 ≠ 0 := pow_ne_zero 2 hs
    intro hcon
    apply this
    linarith
  refine LinearMap.ext fun v ↦ ?_
  rw [Module.End.one_apply]
  obtain ⟨x, y, hx, hy⟩ :
      ∃ x y : ℝ,
        M.geometricForm (Finsupp.single i 1)
            (x • Finsupp.single i (1 : ℝ) + y • Finsupp.single i' (1 : ℝ)) =
          M.geometricForm (Finsupp.single i 1) v ∧
        M.geometricForm (Finsupp.single i' 1)
            (x • Finsupp.single i (1 : ℝ) + y • Finsupp.single i' (1 : ℝ)) =
          M.geometricForm (Finsupp.single i' 1) v := by
    refine ⟨(M.geometricForm (Finsupp.single i 1) v +
        cos (π / M i i') * M.geometricForm (Finsupp.single i' 1) v) /
          (1 - cos (π / M i i') ^ 2),
      (M.geometricForm (Finsupp.single i' 1) v +
        cos (π / M i i') * M.geometricForm (Finsupp.single i 1) v) /
          (1 - cos (π / M i i') ^ 2), ?_, ?_⟩ <;>
    · simp only [map_add, map_smul, smul_eq_mul, geometricForm_single_single,
        CoxeterMatrix.diagonal, Nat.cast_one, div_one, Real.cos_pi, M.symmetric i' i]
      field_simp
      ring
  have h1 : M.geometricForm (Finsupp.single i 1)
      (v - (x • Finsupp.single i (1 : ℝ) + y • Finsupp.single i' (1 : ℝ))) = 0 := by
    rw [map_sub, hx, sub_self]
  have h2 : M.geometricForm (Finsupp.single i' 1)
      (v - (x • Finsupp.single i (1 : ℝ) + y • Finsupp.single i' (1 : ℝ))) = 0 := by
    rw [map_sub, hy, sub_self]
  have hfix := M.pow_apply_eq_self i i' h1 h2 (M i i')
  have hplane : ((M.geometricReflection i * M.geometricReflection i') ^ M i i')
      (x • Finsupp.single i (1 : ℝ) + y • Finsupp.single i' (1 : ℝ)) =
      x • Finsupp.single i (1 : ℝ) + y • Finsupp.single i' (1 : ℝ) := by
    rw [map_add, map_smul, map_smul,
      M.pow_geometricReflection_mul_apply_single_left i i' hs hm0,
      M.pow_geometricReflection_mul_apply_single_right i i' hs hm0]
  calc ((M.geometricReflection i * M.geometricReflection i') ^ M i i') v
      = ((M.geometricReflection i * M.geometricReflection i') ^ M i i')
          ((v - (x • Finsupp.single i (1 : ℝ) + y • Finsupp.single i' (1 : ℝ))) +
            (x • Finsupp.single i (1 : ℝ) + y • Finsupp.single i' (1 : ℝ))) := by
        rw [sub_add_cancel]
    _ = v := by rw [map_add, hfix, hplane, sub_add_cancel]

/-- **The parabolic rotation formula.** When `M i i' = 0`, read as `∞`, the plane spanned by the
two simple roots carries a degenerate form and the rotation is a shear: it moves the first simple
root by `2 k` times the sum of the two roots. In particular it has infinite order. -/
private theorem pow_geometricReflection_mul_apply_single_of_eq_zero (h : M i i' = 0) (k : ℕ) :
    ((M.geometricReflection i * M.geometricReflection i') ^ k) (Finsupp.single i 1) =
      (2 * k + 1 : ℝ) • Finsupp.single i (1 : ℝ) + (2 * k : ℝ) • Finsupp.single i' (1 : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, ih, M.geometricReflection_mul_apply i i']
    simp only [h, Nat.cast_zero, div_zero, Real.cos_zero]
    push_cast
    module

/-- **The Coxeter-matrix entry is the exact order of the rotation** in the geometric
representation: the composite of two simple reflections is killed by an exponent exactly when
that exponent is a multiple of the corresponding entry. The divisibility that the defining
relations of a Coxeter group give is only one half of this. -/
private theorem pow_geometricReflection_mul_eq_one_iff (n : ℕ) :
    (M.geometricReflection i * M.geometricReflection i') ^ n = 1 ↔ M i i' ∣ n := by
  refine ⟨fun hR ↦ ?_, fun hdvd ↦ ?_⟩
  · rcases eq_or_ne i i' with rfl | hne
    · rw [M.diagonal i]
      exact one_dvd n
    -- distinct simple roots are linearly independent, so coordinates can be read off
    have hpair := (LinearIndepOn.pair_iff (fun b : B ↦ Finsupp.single b (1 : ℝ)) hne).1
      ((Finsupp.linearIndependent_single_one (ι := B) (R := ℝ)).linearIndepOn {i, i'})
    rcases Nat.lt_or_ge (M i i') 2 with hlt | hge
    · have hzero : M i i' = 0 := by
        have := M.off_diagonal i i' hne
        omega
      have key := M.pow_geometricReflection_mul_apply_single_of_eq_zero i i' hzero n
      rw [hR, Module.End.one_apply] at key
      obtain ⟨-, h2⟩ := hpair (2 * n) (2 * n) (by linear_combination (norm := module) -key)
      have : (n : ℝ) = 0 := by linarith
      have : n = 0 := by exact_mod_cast this
      simp [hzero, this]
    · have hm0 : (M i i' : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
      have hpos : 0 < π / (M i i' : ℝ) := by
        have : (0 : ℝ) < M i i' := by positivity
        positivity
      have hlt' : π / (M i i' : ℝ) < π := by
        refine div_lt_self Real.pi_pos ?_
        have : (2 : ℝ) ≤ M i i' := by exact_mod_cast hge
        linarith
      have hs : sin (π / M i i') ≠ 0 := ne_of_gt (Real.sin_pos_of_pos_of_lt_pi hpos hlt')
      have key := M.pow_geometricReflection_mul_apply_single i i' hs n
      rw [hR, Module.End.one_apply] at key
      obtain ⟨hc, hsi⟩ := hpair
        (cos (2 * (n : ℝ) * (π / M i i')) +
            cos (π / M i i') * (sin (2 * (n : ℝ) * (π / M i i')) / sin (π / M i i')) - 1)
        (sin (2 * (n : ℝ) * (π / M i i')) / sin (π / M i i'))
        (by linear_combination (norm := module) -key)
      have hsin : sin (2 * (n : ℝ) * (π / M i i')) = 0 := by
        rcases div_eq_zero_iff.1 hsi with h | h
        · exact h
        · exact absurd h hs
      have hcos : cos (2 * (n : ℝ) * (π / M i i')) = 1 := by
        rw [hsi] at hc
        linarith
      obtain ⟨j, hj⟩ := (Real.cos_eq_one_iff _).1 hcos
      have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
      have hmul : (j : ℝ) * (2 * π) * (M i i' : ℝ) = 2 * (n : ℝ) * π := by
        rw [hj]
        field_simp
      have hcancel : (j : ℝ) * (M i i' : ℝ) = (n : ℝ) :=
        mul_right_cancel₀ h2pi (by linear_combination hmul)
      have hint : (M i i' : ℤ) ∣ (n : ℤ) := ⟨j, by
        have : (n : ℤ) = j * (M i i' : ℤ) := by exact_mod_cast hcancel.symm
        linarith⟩
      exact Int.ofNat_dvd.1 (by simpa using hint)
  · obtain ⟨k, rfl⟩ := hdvd
    rcases eq_or_ne i i' with rfl | hne
    · rw [M.diagonal i, one_mul, M.geometricReflection_mul_self, one_pow]
    rcases Nat.lt_or_ge (M i i') 2 with hlt | hge
    · have hzero : M i i' = 0 := by
        have := M.off_diagonal i i' hne
        omega
      rw [hzero, zero_mul, pow_zero]
    · rw [pow_mul, M.geometricReflection_mul_pow_eq_one i i' hge, one_pow]

end RankTwo

/-- **The simple reflections of the geometric representation satisfy the Coxeter relations.** -/
theorem isLiftable_geometricReflection : M.IsLiftable M.geometricReflection := fun i i' ↦
  (M.pow_geometricReflection_mul_eq_one_iff i i' (M i i')).2 dvd_rfl

end CoxeterMatrix

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- **The standard geometric representation of a Coxeter system**: the representation of `W` on
the free real vector space on the index set in which the `i`-th simple reflection acts as the
reflection `v ↦ v - 2 B(αᵢ, v) αᵢ` in the hyperplane orthogonal to the `i`-th simple root, for
the canonical bilinear form `B = CoxeterMatrix.geometricForm M`.

The Coxeter relations hold, but for three different reasons. At `i = i'` the entry is `1` and the
relation says that a reflection is an involution. For `i ≠ i'` with `M i i'` nonzero, hence at least
two (an off-diagonal entry is never `1`), the plane spanned by the two simple roots is Euclidean and
the two reflections compose to the rotation through `2 π / M i i'`, whose `M i i'`-th power is the
identity. For `i ≠ i'` with
`M i i' = 0`, read as `∞`, that plane is instead degenerate and the composite is a shear, of
infinite order; there the relation to be checked is the vacuous `(σᵢ σᵢ')^0 = 1`. -/
noncomputable def geometricRepresentation : Representation ℝ W (B →₀ ℝ) :=
  cs.lift ⟨M.geometricReflection, M.isLiftable_geometricReflection⟩

/-- **Each simple reflection of a Coxeter system acts by its geometric reflection**, the
reflection in the hyperplane orthogonal to the corresponding simple root. -/
@[simp]
theorem geometricRepresentation_simple (i : B) :
    cs.geometricRepresentation (cs.simple i) = M.geometricReflection i :=
  cs.lift_apply_simple M.isLiftable_geometricReflection i

/-- **The geometric representation is orthogonal** for the canonical bilinear form. -/
theorem geometricForm_geometricRepresentation (w : W) (u v : B →₀ ℝ) :
    M.geometricForm (cs.geometricRepresentation w u) (cs.geometricRepresentation w v) =
      M.geometricForm u v := by
  suffices h : ∀ w : W, ∀ u v : B →₀ ℝ,
      M.geometricForm (cs.geometricRepresentation w u) (cs.geometricRepresentation w v) =
        M.geometricForm u v from h w u v
  intro w
  induction w using cs.simple_induction with
  | simple i =>
    intro u v
    rw [cs.geometricRepresentation_simple, M.geometricForm_geometricReflection]
  | one => intro u v; simp
  | mul w w' hw hw' =>
    intro u v
    rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, hw, hw']

/-- **The exact relation satisfied by two simple reflections**: the product of two simple
reflections is killed by an exponent exactly when that exponent is a multiple of the
corresponding entry of the Coxeter matrix. One half of this is the defining relation
`CoxeterSystem.simple_mul_simple_pow`; the other half is Tits' theorem on the geometric
representation. -/
theorem simple_mul_simple_pow_eq_one_iff (i i' : B) (n : ℕ) :
    (cs.simple i * cs.simple i') ^ n = 1 ↔ M i i' ∣ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hrep := congrArg cs.geometricRepresentation h
    rw [map_pow, map_mul, geometricRepresentation_simple, geometricRepresentation_simple,
      map_one] at hrep
    exact (M.pow_geometricReflection_mul_eq_one_iff i i' n).1 hrep
  · obtain ⟨k, rfl⟩ := h
    rw [pow_mul, cs.simple_mul_simple_pow, one_pow]

/-- **The entries of the Coxeter matrix are the exact orders of the products of pairs of simple
reflections.** The defining relations give only the divisibility
`orderOf (s i * s i') ∣ M i i'`; the reverse divisibility is Tits' theorem on the geometric
representation. An entry `M i i' = 0`, read as `∞`, says that the product has infinite order. -/
theorem orderOf_simple_mul_simple (i i' : B) :
    orderOf (cs.simple i * cs.simple i') = M i i' :=
  Nat.dvd_antisymm (orderOf_dvd_of_pow_eq_one (cs.simple_mul_simple_pow i i'))
    ((cs.simple_mul_simple_pow_eq_one_iff i i' _).1 (pow_orderOf_eq_one _))

/-- **The simple reflections are pairwise distinct.** -/
theorem simple_injective : Function.Injective cs.simple := by
  intro i i' h
  by_contra hne
  have hdvd : M i i' ∣ 1 := by
    refine (cs.simple_mul_simple_pow_eq_one_iff i i' 1).1 ?_
    rw [pow_one, ← h, cs.simple_mul_simple_self]
  exact M.off_diagonal i i' hne (Nat.dvd_one.mp hdvd)

/-- **A simple reflection is not the identity**: it negates its own simple root. -/
theorem simple_ne_one (i : B) : cs.simple i ≠ 1 := by
  intro h
  have hrep : M.geometricReflection i = 1 := by
    rw [← cs.geometricRepresentation_simple i, h, map_one]
  have hneg := M.geometricReflection_apply_single_self i
  rw [hrep, Module.End.one_apply] at hneg
  have : (Finsupp.single i (1 : ℝ)) i = 0 := by
    have := congrArg (fun f : B →₀ ℝ ↦ f i) hneg
    simp only [Finsupp.neg_apply, Finsupp.single_eq_same] at this
    linarith
  simp at this

/-- **Each simple reflection has order exactly two.** -/
theorem orderOf_simple (i : B) : orderOf (cs.simple i) = 2 :=
  orderOf_eq_prime (by rw [pow_two, cs.simple_mul_simple_self]) (cs.simple_ne_one i)

end CoxeterSystem
