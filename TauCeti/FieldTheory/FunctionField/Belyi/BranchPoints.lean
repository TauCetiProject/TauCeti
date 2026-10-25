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
homomorphism from the symmetric group on the three branch points; it is constructed with the
other linear fractional transformations in `TauCeti.FieldTheory.RatFunc.Mobius`.

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

/-- The order at a marked place transported along an involutive substitution `τ` is the order of
the image under `τ`, read off a monomial form `c X ^ a (X - 1) ^ b` of that image. -/
private theorem ord_map_branchPointAut_markedPlace {τ : Perm (Fin 3)} (hτ : τ⁻¹ = τ) (i : Fin 3)
    {f : RatFunc k} {c : k} (hc : c ≠ 0) {a b : ℤ}
    (hf : branchPointAut k τ f = algebraMap k (RatFunc k) c * X ^ a * (X - 1) ^ b) :
    ((markedPlace k i).map (branchPointAut k τ)).ord f = ![a, b, -(a + b)] i := by
  rw [ord_map, ← AlgEquiv.aut_inv, ← map_inv, hτ, hf, ord_markedPlace_monomial i hc]

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
  have hm : (-1 : k) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  -- The images of `X` and `X - 1` under the two generators, as monomials `c X ^ a (X - 1) ^ b`.
  have h01X : branchPointAut k (swap 0 1) X =
      algebraMap k (RatFunc k) (-1) * X ^ (0 : ℤ) * (X - 1) ^ (1 : ℤ) := by simp
  have h01X1 : branchPointAut k (swap 0 1) (X - 1) =
      algebraMap k (RatFunc k) (-1) * X ^ (1 : ℤ) * (X - 1) ^ (0 : ℤ) := by simp
  have h12X : branchPointAut k (swap 1 2) X =
      algebraMap k (RatFunc k) 1 * X ^ (1 : ℤ) * (X - 1) ^ (-1 : ℤ) := by
    simp [div_eq_mul_inv]
  have h12X1 : branchPointAut k (swap 1 2) (X - 1) =
      algebraMap k (RatFunc k) 1 * X ^ (0 : ℤ) * (X - 1) ^ (-1 : ℤ) := by
    simp only [map_sub, map_one, branchPointAut_swap_one_two_X]
    field_simp
    simp
  rcases hρ with rfl | rfl <;> fin_cases i <;>
    simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, swap_apply_left, swap_apply_right,
      swap_apply_of_ne_of_ne, ne_eq, Fin.reduceEq, not_false_eq_true]
  · exact h1 (by rw [ord_map_branchPointAut_markedPlace (swap_inv _ _) _ hm h01X1]; simp)
  · exact h0 (by rw [ord_map_branchPointAut_markedPlace (swap_inv _ _) _ hm h01X]; simp)
  · exact h2 (by rw [ord_map_branchPointAut_markedPlace (swap_inv _ _) _ hm h01X]; simp)
  · exact h0 (by rw [ord_map_branchPointAut_markedPlace (swap_inv _ _) _ one_ne_zero h12X]; simp)
  · exact h2 (by rw [ord_map_branchPointAut_markedPlace (swap_inv _ _) _ one_ne_zero h12X]; simp)
  · exact h1 (by rw [ord_map_branchPointAut_markedPlace (swap_inv _ _) _ one_ne_zero h12X1]; simp)

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
