/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CubicDiscriminant
public import Mathlib.GroupTheory.Index
public import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.LinearAlgebra.Determinant.Basic
import TauCeti.LinearAlgebra.FreeModule.Int
import TauCeti.RingTheory.Adjoin.Polynomial.Basic

/-!
# The index form of a based cubic ring

Let `A` be a commutative `R`-algebra with a basis `b = ⟨b 0, b 1, b 2⟩` over `R`; for a cubic
ring, `b 0 = 1`. For `u, v ∈ A` write `D_b(u, v)` for the determinant `b.det ![1, u, v]` of the
coordinate columns of `1, u, v` in `b`. The *index form* of `b` is the binary cubic form
`I_b(x, y) = D_b(ξ, ξ ^ 2)` for `ξ = x • b 1 + y • b 2`, that is
`1 ∧ ξ ∧ ξ ^ 2 = I_b(x, y) • (b 0 ∧ b 1 ∧ b 2)` in the top exterior power. Expanding the
trilinear expression gives its coefficients
`(D(b₁, b₁²), D(b₂, b₁²) + 2 D(b₁, b₁b₂), 2 D(b₂, b₁b₂) + D(b₁, b₂²), D(b₂, b₂²))`, which we
record as a Mathlib `Cubic R`, read as `a x³ + b x² y + c x y² + d y³`.

This is the form through which a cubic ring with a chosen basis determines a binary cubic form.
When `b 0 = 1`:

* `I_b` depends only on the images of `b 1, b 2` in `A / R • 1`: translating them by scalars
  does not change it (`Module.Basis.indexForm_eq_of_sub_mem_range`), and `D_b(u, u ^ 2)` is the
  value of `I_b` at the coordinates of `u` along `b 1, b 2`
  (`Module.Basis.det_one_sq_eq_indexForm`);
* if `b'` is another basis with `b' 0 = 1` whose vectors `b' 1, b' 2` are congruent modulo
  scalars to the rows of `γ • (b 1, b 2)` for a matrix `γ`, then `det γ = b.det b'`
  (`Module.Basis.det_eq_of_apply_zero_eq_one`) and
  `det γ • I_{b'}(x, y) = I_b((x, y) γ)` (`Module.Basis.det_mul_indexForm_eq_indexForm`), so
  `I_{b'}` is the twisted transform `(det γ)⁻¹ I_b((x, y) γ)` of `I_b`;
* over `ℤ`, the subring `ℤ[u]` has index `|I_b(x, y)|` in `A`, where `x, y` are the coordinates
  of `u` along `b 1, b 2` (`Module.Basis.index_closure_eq_natAbs_indexForm`). When `I_b(x, y) = 0`
  both sides vanish: the subring then has infinite index.

The evaluation identity `D_b(ξ, ξ ^ 2) = I_b(x, y)` holds for every basis
(`Module.Basis.det_one_smul_add_smul_sq`).

## Main definitions

* `Module.Basis.indexForm`: the index form of a basis indexed by `Fin 3`.

## References

* B. H. Gross and M. Lucianovic, *On cubic rings and quaternion rings*, J. Number Theory 129
  (2009), 1468–1478, proof of Proposition 2.1 and its footnote.
* M. Bhargava, A. Shankar and J. Tsimerman, *On the Davenport–Heilbronn theorems and second
  order terms*, Invent. Math. 193 (2013), 439–499, proof of Theorem 9.
* W. T. Gan, B. H. Gross and G. Savin, *Fourier coefficients of modular forms on G₂*, Duke
  Math. J. 115 (2002), 105–169, Lemma 5.3: the index of `ℤ[ξ]` is the value of the index form.
-/

public section

open Matrix

namespace Module.Basis

section Ring

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (b : Basis (Fin 3) R A)

/-- In a basis whose first vector is `1`, the determinant of `1, u, v` is the `2 × 2` minor of the
coordinates of `u` and `v` along `b 1` and `b 2`. -/
theorem det_vecCons_one (hb : b 0 = 1) (u v : A) :
    b.det ![1, u, v] = b.repr u 1 * b.repr v 2 - b.repr u 2 * b.repr v 1 := by
  rw [det_apply, det_fin_three, ← hb]
  simp only [toMatrix_apply, cons_val_zero, cons_val_one, cons_val, repr_self,
    Finsupp.single_eq_same, Finsupp.single_eq_of_ne, ne_eq, one_ne_zero, Fin.reduceEq,
    not_false_eq_true, one_mul, mul_zero, zero_mul, add_zero, sub_zero]
  ring

/-- Translating `u` by a scalar does not change the determinant of `1, u, u ^ 2` in any basis. -/
theorem det_one_add_algebraMap_sq (u : A) (c : R) :
    b.det ![1, u + algebraMap R A c, (u + algebraMap R A c) ^ 2] = b.det ![1, u, u ^ 2] := by
  have hsq : (u + algebraMap R A c) ^ 2 = u ^ 2 + (2 * c) • u + c ^ 2 • 1 := by
    simp only [Algebra.algebraMap_eq_smul_one, sq, add_mul, mul_add, mul_one, one_mul,
      mul_smul_comm, smul_mul_assoc]
    module
  rw [hsq]
  simp only [det_apply, det_fin_three, toMatrix_apply, Algebra.algebraMap_eq_smul_one,
    map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, cons_val_zero,
    cons_val_one, cons_val_two, tail_cons, head_cons]
  ring

/-- In a basis whose first vector is `1`, the determinant of another such basis `b'` is the
determinant of the matrix `γ = (b.repr (b' i) j)_{i, j ∈ {1, 2}}` expressing `b' 1, b' 2` in
terms of `b 1, b 2` modulo scalars. -/
theorem det_eq_of_apply_zero_eq_one (hb : b 0 = 1) {b' : Basis (Fin 3) R A} (hb' : b' 0 = 1) :
    b.det b' = b.repr (b' 1) 1 * b.repr (b' 2) 2 - b.repr (b' 1) 2 * b.repr (b' 2) 1 := by
  rw [← b.det_vecCons_one hb, ← hb']
  congr 1
  ext i
  fin_cases i <;> simp

end Ring

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-- The **index form** of a basis `b = ⟨b 0, b 1, b 2⟩` of an `R`-algebra `A`: the binary cubic
form `I_b(x, y) = det_b(1, ξ, ξ ^ 2)` for `ξ = x • b 1 + y • b 2`, recorded by its coefficients
`a x³ + b x² y + c x y² + d y³` (see `Module.Basis.det_one_smul_add_smul_sq`). -/
noncomputable def indexForm (b : Basis (Fin 3) R A) : Cubic R where
  a := b.det ![1, b 1, b 1 ^ 2]
  b := b.det ![1, b 2, b 1 ^ 2] + 2 * b.det ![1, b 1, b 1 * b 2]
  c := 2 * b.det ![1, b 2, b 1 * b 2] + b.det ![1, b 1, b 2 ^ 2]
  d := b.det ![1, b 2, b 2 ^ 2]

variable (b : Basis (Fin 3) R A)

@[simp]
theorem indexForm_a : b.indexForm.a = b.det ![1, b 1, b 1 ^ 2] := (rfl)

@[simp]
theorem indexForm_b :
    b.indexForm.b = b.det ![1, b 2, b 1 ^ 2] + 2 * b.det ![1, b 1, b 1 * b 2] := (rfl)

@[simp]
theorem indexForm_c :
    b.indexForm.c = 2 * b.det ![1, b 2, b 1 * b 2] + b.det ![1, b 1, b 2 ^ 2] := (rfl)

@[simp]
theorem indexForm_d : b.indexForm.d = b.det ![1, b 2, b 2 ^ 2] := (rfl)

/-- **Evaluation of the index form.** For `ξ = x • b 1 + y • b 2`, the determinant of
`1, ξ, ξ ^ 2` in `b` is the value `I_b(x, y)` of the index form of `b`. -/
theorem det_one_smul_add_smul_sq (x y : R) :
    b.det ![1, x • b 1 + y • b 2, (x • b 1 + y • b 2) ^ 2] =
      b.indexForm.a * x ^ 3 + b.indexForm.b * x ^ 2 * y + b.indexForm.c * x * y ^ 2 +
        b.indexForm.d * y ^ 3 := by
  have hsq : (x • b 1 + y • b 2) ^ 2 =
      x ^ 2 • b 1 ^ 2 + (2 * x * y) • (b 1 * b 2) + y ^ 2 • b 2 ^ 2 := by
    simp only [sq, add_mul, mul_add, smul_mul_smul_comm, mul_comm (b 2) (b 1)]
    module
  rw [hsq]
  simp only [indexForm_a, indexForm_b, indexForm_c, indexForm_d, det_apply, det_fin_three,
    toMatrix_apply, map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    cons_val_zero, cons_val_one, cons_val_two, tail_cons, head_cons]
  ring

/-- In a basis whose first vector is `1`, the determinant of `1, u, u ^ 2` is the value of the
index form at the coordinates of `u` along `b 1` and `b 2`. -/
theorem det_one_sq_eq_indexForm (hb : b 0 = 1) (u : A) :
    b.det ![1, u, u ^ 2] =
      b.indexForm.a * b.repr u 1 ^ 3 + b.indexForm.b * b.repr u 1 ^ 2 * b.repr u 2 +
        b.indexForm.c * b.repr u 1 * b.repr u 2 ^ 2 + b.indexForm.d * b.repr u 2 ^ 3 := by
  have hu : u = (b.repr u 1 • b 1 + b.repr u 2 • b 2) + algebraMap R A (b.repr u 0) := by
    conv_lhs => rw [← b.sum_repr u]
    rw [Fin.sum_univ_three, hb, Algebra.algebraMap_eq_smul_one]
    abel
  conv_lhs => rw [hu]
  rw [det_one_add_algebraMap_sq, det_one_smul_add_smul_sq]

/-- **Change of basis for the index form.** Let `b` and `b'` be bases with `b 0 = 1`, and let
`γ = (b.repr (b' i) j)_{i, j ∈ {1, 2}}`, so that `b' 1, b' 2` are the rows of `γ • (b 1, b 2)`
modulo scalars. Then `b.det b' • I_{b'}(x, y) = I_b((x, y) γ)`. When also `b' 0 = 1`,
`b.det b' = det γ` (`Module.Basis.det_eq_of_apply_zero_eq_one`), so `I_{b'}` is the twisted
transform `(det γ)⁻¹ I_b((x, y) γ)` of `I_b`. -/
theorem det_mul_indexForm_eq_indexForm (hb : b 0 = 1) (b' : Basis (Fin 3) R A) (x y : R) :
    b.det b' * (b'.indexForm.a * x ^ 3 + b'.indexForm.b * x ^ 2 * y +
        b'.indexForm.c * x * y ^ 2 + b'.indexForm.d * y ^ 3) =
      b.indexForm.a * (x * b.repr (b' 1) 1 + y * b.repr (b' 2) 1) ^ 3 +
        b.indexForm.b * (x * b.repr (b' 1) 1 + y * b.repr (b' 2) 1) ^ 2 *
          (x * b.repr (b' 1) 2 + y * b.repr (b' 2) 2) +
        b.indexForm.c * (x * b.repr (b' 1) 1 + y * b.repr (b' 2) 1) *
          (x * b.repr (b' 1) 2 + y * b.repr (b' 2) 2) ^ 2 +
        b.indexForm.d * (x * b.repr (b' 1) 2 + y * b.repr (b' 2) 2) ^ 3 := by
  rw [← det_one_smul_add_smul_sq, ← smul_eq_mul, ← smul_apply,
    ← AlternatingMap.eq_smul_basis_det, det_one_sq_eq_indexForm b hb]
  simp

/-- **The index form is invariant under translation by scalars.** If `b` and `b'` both have first
vector `1` and `b' 1 - b 1`, `b' 2 - b 2` are scalars, then `b` and `b'` have the same index
form. -/
theorem indexForm_eq_of_sub_mem_range (hb : b 0 = 1) {b' : Basis (Fin 3) R A} (hb' : b' 0 = 1)
    (h₁ : b' 1 - b 1 ∈ (algebraMap R A).range) (h₂ : b' 2 - b 2 ∈ (algebraMap R A).range) :
    b'.indexForm = b.indexForm := by
  obtain ⟨r, hr⟩ := h₁
  obtain ⟨s, hs⟩ := h₂
  rw [eq_sub_iff_add_eq, add_comm] at hr hs
  -- `b'.det = b.det` since the change of basis is unitriangular
  have hdet : b'.det = b.det := det_eq_det_of_det_eq_one <| by
    rw [b.det_eq_of_apply_zero_eq_one hb hb', ← hr, ← hs]
    simp [Algebra.algebraMap_eq_smul_one, ← hb]
  have h1 : b.repr 1 = Finsupp.single 0 1 := by rw [← hb, repr_self]
  ext <;> simp [hdet, b.det_vecCons_one hb, ← hr, ← hs, Algebra.algebraMap_eq_smul_one, sq,
    add_mul, mul_add, h1] <;> ring

/-- **The index of `ℤ[u]` is the value of the index form.** Let `b` be a `ℤ`-basis of a
commutative ring `A` with `b 0 = 1`, and let `u ∈ A` have coordinates `x, y` along `b 1, b 2`.
Then the subring `ℤ[u]` has index `|I_b(x, y)|` in `A`. When `I_b(x, y) = 0` the subring has
infinite index, which `AddSubgroup.index` records as `0`. -/
theorem index_closure_eq_natAbs_indexForm (b : Basis (Fin 3) ℤ A) (hb : b 0 = 1) (u : A) :
    (Subring.closure {u}).toAddSubgroup.index =
      (b.indexForm.a * b.repr u 1 ^ 3 + b.indexForm.b * b.repr u 1 ^ 2 * b.repr u 2 +
        b.indexForm.c * b.repr u 1 * b.repr u 2 ^ 2 + b.indexForm.d * b.repr u 2 ^ 3).natAbs := by
  have := Module.Free.of_basis b
  have := Module.Finite.of_basis b
  have hspan : Subalgebra.toSubmodule (Algebra.adjoin ℤ {u}) =
      LinearMap.range (b.constr ℤ ![1, u, u ^ 2]) := by
    rw [TauCeti.Algebra.toSubmodule_adjoin_singleton_eq_span_range_pow, constr_range,
      finrank_eq_card_basis b, Fintype.card_fin]
    congr
    funext i
    fin_cases i <;> simp [sq]
  -- `ℤ[u]` is both the subring generated by `u` and the `ℤ`-subalgebra generated by `u`
  have hclosure : (Subring.closure {u}).toAddSubgroup =
      (LinearMap.range (b.constr ℤ ![1, u, u ^ 2])).toAddSubgroup := by
    refine SetLike.ext' ?_
    rw [Submodule.coe_toAddSubgroup, ← hspan, Subalgebra.coe_toSubmodule, Algebra.adjoin_int]
    exact Set.ext fun _ ↦ mem_subalgebraOfSubring.symm
  have hmat : LinearMap.toMatrix b b (b.constr ℤ ![1, u, u ^ 2]) = b.toMatrix ![1, u, u ^ 2] := by
    ext
    rw [LinearMap.toMatrix_apply, toMatrix_apply, constr_basis]
  rw [hclosure, LinearMap.index_range_eq_natAbs_det_toMatrix b b, hmat, ← det_apply,
    det_one_sq_eq_indexForm b hb]

end Module.Basis
