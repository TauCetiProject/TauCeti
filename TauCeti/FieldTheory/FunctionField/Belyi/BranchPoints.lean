/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Equiv
public import TauCeti.FieldTheory.RatFunc.Mobius
import Mathlib.LinearAlgebra.Matrix.Notation
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.GroupTheory.Perm.FinThree.Basic

/-!
# Permuting the branch points of an algebraic Belyi pair

The six linear fractional transformations

| `ρ`                | `0, 1, ∞` go to | `m(t)`         |
| ------------------ | --------------- | -------------- |
| `1`                | `0, 1, ∞`       | `t`            |
| `swap 0 1`         | `1, 0, ∞`       | `1 - t`        |
| `swap 1 2`         | `0, ∞, 1`       | `t / (t - 1)`  |
| `swap 0 2`         | `∞, 1, 0`       | `1 / t`        |
| `finRotate 3`      | `∞, 0, 1`       | `(t - 1) / t`  |
| `(finRotate 3)⁻¹`  | `1, ∞, 0`       | `1 / (1 - t)`  |

are the Möbius transformations permuting `0, 1, ∞`, defined over the prime field. Numbering
`0, 1, ∞` as `0, 1, 2 : Fin 3`, the transformation `m` attached to `ρ` sends the point numbered
`ρ i` to the point numbered `i`. Its substitution `t ↦ m(t)` is the automorphism
`RatFunc.branchPointAut ρ` of `k(t)`, and `ρ ↦ RatFunc.branchPointAut ρ` is a group
homomorphism from the symmetric group on the three branch points.

Postcomposing a Belyi map `β` with `m` gives the Belyi map `m ∘ β` on the same curve. Its fibre
over the point numbered `i` is the fibre of `β` over the point numbered `ρ i`, so `m ∘ β` is the
reordering of the branch points of `β` along `ρ`, in the indexing convention of
`TauCeti.PermutationTriple.reindexBranchPoints`, whose component over `i` comes from the old
component over `ρ i`. The inversion is visible on the two three-cycles: the reordering
`finRotate 3`, which is `0 → 1 → ∞ → 0`, is realised by `(t - 1) / t`, whose own permutation of
the points is `0 → ∞ → 1 → 0`.

On function fields, `m ∘ β` replaces the embedding `φ : k(t) → F` by `φ ∘ m`. This file states
this along an isomorphism `e : F ≃ₐ[k] F'` with `e (φ (m x)) = φ' x`, so that `F'` may be `F`
itself with the new algebra structure, or any other model of it.

## Main definitions

* `RatFunc.branchPointAut`: the homomorphism `Perm (Fin 3) →* Aut(k(t)/k)`, with its values
  at `X` on the five nonidentity permutations (`RatFunc.branchPointAut_swap_zero_one_X` and its
  siblings).

## Main results

* `TauCeti.Place.map_branchPointAut_markedPlace`: `RatFunc.branchPointAut ρ` carries the marked
  place numbered `i` to the marked place numbered `ρ i`.
* `TauCeti.IsAlgebraicBelyiPair.of_branchPointAut`: reordering the branch points of an algebraic
  Belyi pair gives an algebraic Belyi pair.
* `TauCeti.finrank_eq_of_branchPointAut`: of the same degree.
* `TauCeti.Place.restrict_map_eq_markedPlace_iff_of_branchPointAut` and
  `TauCeti.Place.ramificationIdx_map_of_branchPointAut`: the places over the
  branch point numbered `i` of the new pair are those over the branch point numbered `ρ i` of the
  old one, with the same ramification indices.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, §4.4.
* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer, 2004, §1.5.
-/

public section

open Equiv

namespace RatFunc

variable {K : Type*} [Field K]

/-- The integer coefficient matrices `!![a, b; c, d]` of the six transformations
`(a t + b) / (c t + d)` permuting `0, 1, ∞`, normalized so that they form a subgroup of
`GL₂(ℤ)` isomorphic to the symmetric group. A permutation of `Fin 3` is determined by its values
at `0` and `1`. -/
private def branchPointMatrix (ρ : Perm (Fin 3)) : Matrix (Fin 2) (Fin 2) ℤ :=
  match ρ 0, ρ 1 with
  | 1, 0 => !![-1, 1; 0, 1]
  | 0, 2 => !![1, 0; 1, -1]
  | 2, 1 => !![0, -1; -1, 0]
  | 1, 2 => !![-1, 1; -1, 0]
  | 2, 0 => !![0, -1; 1, -1]
  | _, _ => 1

/-- Substitution composes the matrices in the opposite order. -/
private theorem branchPointMatrix_mul (ρ ρ' : Perm (Fin 3)) :
    branchPointMatrix (ρ * ρ') = branchPointMatrix ρ' * branchPointMatrix ρ := by
  revert ρ ρ'
  decide

/-- The six coefficient matrices have determinant `±1`, so they are invertible over any field. -/
private theorem det_branchPointMatrix_ne_zero (ρ : Perm (Fin 3)) :
    ((branchPointMatrix ρ 0 0 : ℤ) : K) * (branchPointMatrix ρ 1 1 : ℤ) -
      (branchPointMatrix ρ 0 1 : ℤ) * (branchPointMatrix ρ 1 0 : ℤ) ≠ 0 := by
  have h : ∀ ρ : Perm (Fin 3), branchPointMatrix ρ 0 0 * branchPointMatrix ρ 1 1 -
      branchPointMatrix ρ 0 1 * branchPointMatrix ρ 1 0 = 1 ∨
    branchPointMatrix ρ 0 0 * branchPointMatrix ρ 1 1 -
      branchPointMatrix ρ 0 1 * branchPointMatrix ρ 1 0 = -1 := by decide
  rw [← Int.cast_mul, ← Int.cast_mul, ← Int.cast_sub]
  rcases h ρ with h | h <;> simp [h]

/-- The substitution attached to `ρ`, before it is bundled as a homomorphism. -/
private noncomputable def branchPointAutFun (ρ : Perm (Fin 3)) : RatFunc K ≃ₐ[K] RatFunc K :=
  mobiusAutOf (det_branchPointMatrix_ne_zero ρ)

/-- The defining value of the substitution attached to `ρ`. -/
private theorem branchPointAutFun_X (ρ : Perm (Fin 3)) :
    branchPointAutFun ρ X = mobiusOf ((branchPointMatrix ρ 0 0 : ℤ) : K)
      (branchPointMatrix ρ 0 1 : ℤ) (branchPointMatrix ρ 1 0 : ℤ) (branchPointMatrix ρ 1 1 : ℤ) :=
  mobiusAutOf_X _

variable (K) in
/-- **The automorphisms of `k(t)` permuting the branch points `0, 1, ∞`**: for
`ρ : Perm (Fin 3)`, the substitution `t ↦ m(t)` by the linear fractional transformation `m` that
sends the point numbered `ρ i` to the point numbered `i`, where `0, 1, 2` number `0, 1, ∞`. The
five nonidentity substitutions are `1 - t`, `t / (t - 1)`, `1 / t`, `(t - 1) / t` and
`1 / (1 - t)` (`RatFunc.branchPointAut_swap_zero_one_X` and its siblings, the last one for
the inverse of `finRotate 3`), and they act on the
marked places through `ρ` (`TauCeti.Place.map_branchPointAut_markedPlace`). -/
noncomputable def branchPointAut : Perm (Fin 3) →* (RatFunc K ≃ₐ[K] RatFunc K) where
  toFun := branchPointAutFun
  map_one' := algEquiv_ext (by
    rw [branchPointAutFun_X, AlgEquiv.one_apply]
    simp [branchPointMatrix, mobiusOf_def])
  map_mul' ρ ρ' := algEquiv_ext (by
    rw [AlgEquiv.mul_apply, branchPointAutFun_X, branchPointAutFun_X, branchPointAutFun,
      mobiusAutOf_mobiusOf, branchPointMatrix_mul]
    simp [Matrix.mul_apply, Fin.sum_univ_two])

/-- The value of `RatFunc.branchPointAut ρ` at `X`, read off the coefficient matrix. -/
private theorem branchPointAut_X (ρ : Perm (Fin 3)) :
    branchPointAut K ρ X = mobiusOf ((branchPointMatrix ρ 0 0 : ℤ) : K)
      (branchPointMatrix ρ 0 1 : ℤ) (branchPointMatrix ρ 1 0 : ℤ) (branchPointMatrix ρ 1 1 : ℤ) :=
  branchPointAutFun_X ρ

/-- The substitution exchanging `0` and `1` is `t ↦ 1 - t`. -/
@[simp]
theorem branchPointAut_swap_zero_one_X : branchPointAut K (swap 0 1) X = 1 - X := by
  rw [branchPointAut_X, show branchPointMatrix (swap 0 1) = !![-1, 1; 0, 1] by decide]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one, Int.cast_zero, mobiusOf_def, map_neg,
    map_one, map_zero, zero_mul, zero_add, div_one]
  ring

/-- The substitution exchanging `1` and `∞` is `t ↦ t / (t - 1)`. -/
@[simp]
theorem branchPointAut_swap_one_two_X : branchPointAut K (swap 1 2) X = X / (X - 1) := by
  rw [branchPointAut_X, show branchPointMatrix (swap 1 2) = !![1, 0; 1, -1] by decide]
  simp [mobiusOf_def, sub_eq_add_neg]

/-- The substitution exchanging `0` and `∞` is `t ↦ 1 / t`. -/
@[simp]
theorem branchPointAut_swap_zero_two_X : branchPointAut K (swap 0 2) X = X⁻¹ := by
  rw [branchPointAut_X, show branchPointMatrix (swap 0 2) = !![0, -1; -1, 0] by decide]
  simp [mobiusOf_def]

/-- The substitution reordering the branch points along `0 → 1 → ∞ → 0` is
`t ↦ (t - 1) / t`. -/
@[simp]
theorem branchPointAut_finRotate_X : branchPointAut K (finRotate 3) X = (X - 1) / X := by
  rw [branchPointAut_X, show branchPointMatrix (finRotate 3) = !![-1, 1; -1, 0] by decide]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one, Int.cast_zero, mobiusOf_def, map_neg,
    map_one, map_zero, add_zero]
  ring

/-- The substitution reordering the branch points along `0 → ∞ → 1 → 0`, the inverse of
`RatFunc.branchPointAut (finRotate 3)`, is `t ↦ 1 / (1 - t)`. It is stated for the inverse
automorphism, the simp-normal form of `branchPointAut K (finRotate 3)⁻¹`. -/
@[simp]
theorem branchPointAut_finRotate_symm_X : (branchPointAut K (finRotate 3)).symm X = (1 - X)⁻¹ := by
  rw [← AlgEquiv.aut_inv, ← map_inv, branchPointAut_X,
    show branchPointMatrix (finRotate 3)⁻¹ = !![0, -1; 1, -1] by decide]
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one, Int.cast_neg, Int.cast_one, Int.cast_zero, mobiusOf_def, map_neg,
    map_one, map_zero, zero_mul, zero_add, one_mul]
  rw [neg_div, one_div, ← inv_neg]
  ring

end RatFunc

open RatFunc

namespace TauCeti

namespace Place

variable {k : Type*} [Field k]

/-- The order of a monomial `c X ^ a (X - 1) ^ b` at the marked places `0`, `1` and `∞`. -/
private theorem ord_markedPlace_monomial (i : Fin 3) {c : k} (hc : c ≠ 0) (a b : ℤ) :
    (markedPlace k i).ord (algebraMap k (RatFunc k) c * X ^ a * (X - 1) ^ b) =
      ![a, b, -(a + b)] i := by
  fin_cases i
  · simpa using ord_adicOfIrreducible_X_algebraMap_mul_X_zpow_mul_X_sub_one_zpow hc a b
  · simpa using ord_adicOfIrreducible_X_sub_one_algebraMap_mul_X_zpow_mul_X_sub_one_zpow hc a b
  · simpa using ord_infty_algebraMap_mul_X_zpow_mul_X_sub_one_zpow hc a b

/-- The two generating transpositions move the marked places as they move their numbers. -/
private theorem map_branchPointAut_markedPlace_of_mem {ρ : Perm (Fin 3)}
    (hρ : ρ = swap 0 1 ∨ ρ = swap 1 2) (i : Fin 3) :
    (markedPlace k i).map (branchPointAut k ρ) = markedPlace k (ρ i) := by
  have h0 {P : Place k (RatFunc k)} (h : 0 < P.ord X) : P = markedPlace k 0 := by
    rw [markedPlace_zero]
    exact ord_X_pos_iff.mp h
  have h1 {P : Place k (RatFunc k)} (h : 0 < P.ord (X - 1)) : P = markedPlace k 1 := by
    rw [markedPlace_one]
    exact (ord_X_sub_C_pos_iff (a := (1 : k))).mp (by rwa [map_one])
  have h2 {P : Place k (RatFunc k)} (h : P.ord X < 0) : P = markedPlace k 2 := by
    rw [markedPlace_two]
    exact X_notMem_integers_iff_eq_infty.mp (by rwa [mem_integers_iff_ord_nonneg, not_le])
  have hX1 : (X - 1 : RatFunc k) ≠ 0 := by simpa using RatFunc.X_sub_C_ne_zero (1 : k)
  -- Each case evaluates the order of `X` or of `X - 1` at the transported place, which is the
  -- order of a monomial `c X ^ a (X - 1) ^ b` at a marked place.
  rcases hρ with rfl | rfl <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, swap_apply_left, swap_apply_right,
      swap_apply_of_ne_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true]
  · refine h1 ?_
    rw [ord_map, ← AlgEquiv.aut_inv, ← map_inv, swap_inv, map_sub, map_one,
      branchPointAut_swap_zero_one_X,
      show (1 - X - 1 : RatFunc k) = algebraMap k _ (-1) * X ^ (1 : ℤ) * (X - 1) ^ (0 : ℤ) by
        simp, ord_markedPlace_monomial 0 (neg_ne_zero.mpr one_ne_zero)]
    simp
  · refine h0 ?_
    rw [ord_map, ← AlgEquiv.aut_inv, ← map_inv, swap_inv, branchPointAut_swap_zero_one_X,
      show (1 - X : RatFunc k) = algebraMap k _ (-1) * X ^ (0 : ℤ) * (X - 1) ^ (1 : ℤ) by
        simp, ord_markedPlace_monomial 1 (neg_ne_zero.mpr one_ne_zero)]
    simp
  · refine h2 ?_
    rw [ord_map, ← AlgEquiv.aut_inv, ← map_inv, swap_inv, branchPointAut_swap_zero_one_X,
      show (1 - X : RatFunc k) = algebraMap k _ (-1) * X ^ (0 : ℤ) * (X - 1) ^ (1 : ℤ) by
        simp, ord_markedPlace_monomial 2 (neg_ne_zero.mpr one_ne_zero)]
    simp
  · refine h0 ?_
    rw [ord_map, ← AlgEquiv.aut_inv, ← map_inv, swap_inv, branchPointAut_swap_one_two_X,
      show (X / (X - 1) : RatFunc k) = algebraMap k _ 1 * X ^ (1 : ℤ) * (X - 1) ^ (-1 : ℤ) by
        simp [div_eq_mul_inv], ord_markedPlace_monomial 0 one_ne_zero]
    simp
  · refine h2 ?_
    rw [ord_map, ← AlgEquiv.aut_inv, ← map_inv, swap_inv, branchPointAut_swap_one_two_X,
      show (X / (X - 1) : RatFunc k) = algebraMap k _ 1 * X ^ (1 : ℤ) * (X - 1) ^ (-1 : ℤ) by
        simp [div_eq_mul_inv], ord_markedPlace_monomial 1 one_ne_zero]
    simp
  · refine h1 ?_
    rw [ord_map, ← AlgEquiv.aut_inv, ← map_inv, swap_inv, map_sub, map_one,
      branchPointAut_swap_one_two_X,
      show (X / (X - 1) - 1 : RatFunc k) =
          algebraMap k _ 1 * X ^ (0 : ℤ) * (X - 1) ^ (-1 : ℤ) by
        field_simp
        simp, ord_markedPlace_monomial 2 one_ne_zero]
    simp

/-- **The branch-point substitutions permute the marked places**: `RatFunc.branchPointAut ρ`
carries the marked place numbered `i` to the marked place numbered `ρ i`. -/
@[simp]
theorem map_branchPointAut_markedPlace (ρ : Perm (Fin 3)) (i : Fin 3) :
    (markedPlace k i).map (branchPointAut k ρ) = markedPlace k (ρ i) := by
  have hgen : Submonoid.closure {swap (0 : Fin 3) 1, swap 1 2} = ⊤ := by
    rw [← Perm.mclosure_swap_castSucc_succ 2]
    congr 1
    ext σ
    simp [Fin.exists_fin_two, eq_comm]
  refine Submonoid.closure_induction
    (motive := fun ρ _ ↦ ∀ i, (markedPlace k i).map (branchPointAut k ρ) = markedPlace k (ρ i))
    (fun ρ hρ ↦ map_branchPointAut_markedPlace_of_mem hρ) (fun i ↦ ?_)
    (fun ρ ρ' _ _ h h' i ↦ ?_) (hgen ▸ Submonoid.mem_top ρ) i
  · rw [map_one, AlgEquiv.aut_one, map_refl, Perm.one_apply]
  · rw [map_mul, AlgEquiv.aut_mul, ← map_map, h', h, Perm.mul_apply]

/-- The branch-point substitutions carry the three marked places into themselves. -/
theorem mapsTo_branchPointAut_zeroOneInfty (ρ : Perm (Fin 3)) :
    Set.MapsTo (Place.map (branchPointAut k ρ)) (zeroOneInfty k) (zeroOneInfty k) := by
  intro P hP
  rw [← range_markedPlace] at hP ⊢
  obtain ⟨i, rfl⟩ := hP
  exact ⟨ρ i, (map_branchPointAut_markedPlace ρ i).symm⟩

section Reorder

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra (RatFunc k) F] [Algebra (RatFunc k) F'] (ρ : Perm (Fin 3)) (e : F ≃ₐ[k] F')
  (he : ∀ x, e (algebraMap (RatFunc k) F (branchPointAut k ρ x)) = algebraMap (RatFunc k) F' x)
include he

/-- If `e` sends `m(t)` in `F` to the Belyi function `t` of `F'`, then it carries the image of
`k(t)` in `F` onto that in `F'` along the inverse substitution. -/
private theorem commute_branchPointAut_inv (x : RatFunc k) :
    e (algebraMap (RatFunc k) F x) = algebraMap (RatFunc k) F' (branchPointAut k ρ⁻¹ x) := by
  rw [← he, ← AlgEquiv.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, AlgEquiv.one_apply]

/-- **Reordering the branch points keeps the places above them**: when `e : F ≃ₐ[k] F'`
replaces the Belyi function `t` of `F` by `m(t)`, a place of `F` lies over the branch point
numbered `ρ i` exactly when its transport to `F'` lies over the branch point numbered `i`. -/
theorem restrict_map_eq_markedPlace_iff_of_branchPointAut [IsScalarTower k (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F'] [Algebra.IsIntegral (RatFunc k) F]
    [Algebra.IsIntegral (RatFunc k) F'] {P : Place k F} {i : Fin 3} :
    (P.map e).restrict k (RatFunc k) = markedPlace k i ↔
      P.restrict k (RatFunc k) = markedPlace k (ρ i) := by
  rw [restrict_map e (branchPointAut k ρ⁻¹) (commute_branchPointAut_inv ρ e he), ← mapEquiv_apply,
    ← Equiv.eq_symm_apply, mapEquiv_symm_apply, ← AlgEquiv.aut_inv, ← map_inv, inv_inv,
    map_branchPointAut_markedPlace]

/-- **Reordering the branch points keeps the ramification indices**: when `e : F ≃ₐ[k] F'`
replaces the Belyi function `t` of `F` by `m(t)`, a place of `F` and its transport to `F'`
have the same ramification index over `k(t)`. -/
theorem ramificationIdx_map_of_branchPointAut (P : Place k F) :
    ramificationIdx (RatFunc k) (P.map e) = ramificationIdx (RatFunc k) P :=
  ramificationIdx_map e (branchPointAut k ρ⁻¹).toRingEquiv (commute_branchPointAut_inv ρ e he) P

end Reorder

end Place

section Reorder

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra (RatFunc k) F] [Algebra (RatFunc k) F'] (ρ : Perm (Fin 3)) (e : F ≃ₐ[k] F')
  (he : ∀ x, e (algebraMap (RatFunc k) F (branchPointAut k ρ x)) = algebraMap (RatFunc k) F' x)
include he

/-- **Reordering the branch points keeps the degree**: when `e : F ≃ₐ[k] F'` replaces the
Belyi function `t` of `F` by `m(t)`, the degrees of `F` and `F'` over `k(t)` agree. -/
theorem finrank_eq_of_branchPointAut :
    Module.finrank (RatFunc k) F' = Module.finrank (RatFunc k) F :=
  (Algebra.finrank_eq_of_equiv_equiv (branchPointAut k ρ⁻¹).toRingEquiv e.toRingEquiv
    (RingHom.ext fun x ↦ (Place.commute_branchPointAut_inv ρ e he x).symm)).symm

/-- **Reordering the branch points of an algebraic Belyi pair**: if `F` is an algebraic Belyi
pair with Belyi function `t`, and `e : F ≃ₐ[k] F'` sends `m(t)` to the Belyi function of `F'`,
where `m` is the substitution `RatFunc.branchPointAut ρ`, then `F'` is an algebraic Belyi pair.

Taking `F' = F` with the algebra structure `φ ∘ m`, this is the postcomposition `m ∘ β` of the
Belyi map `β`. Its fibres over the marked places are those of `β` reordered along `ρ`
(`TauCeti.Place.restrict_map_eq_markedPlace_iff_of_branchPointAut`). -/
theorem IsAlgebraicBelyiPair.of_branchPointAut [CharZero k] [IsScalarTower k (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F'] [FiniteDimensional (RatFunc k) F]
    [FiniteDimensional (RatFunc k) F'] (h : IsAlgebraicBelyiPair k F) :
    IsAlgebraicBelyiPair k F' :=
  h.of_equiv_equiv (branchPointAut k ρ⁻¹) (Place.mapsTo_branchPointAut_zeroOneInfty ρ⁻¹) e
    (Place.commute_branchPointAut_inv ρ e he)

end Reorder

end TauCeti
