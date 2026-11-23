/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.BilinearMap.Multilinear
import Mathlib.Data.Fin.Tuple.Reflection

/-!
# Recognizing a second exterior power

An alternating bilinear map `ω : M → M → N` induces, by the universal property of the exterior
power, a linear map `⋀²M → N` sending `x ∧ y` to `ω x y`. This file records when that map is an
isomorphism: if `M` has a basis `b` indexed by a linearly ordered type and the values
`ω (b i) (b j)` for `i < j` form a basis of `N`, then `⋀²M ≃ N`.

This is how a module presented by a basis of "brackets" of basis vectors, such as the degree-one
piece of the graded Lie algebra of a free group, is identified with an exterior square without
comparing the index set `{(i, j) | i < j}` with Mathlib's index set of two-element subsets.

## Main definitions

* `LinearMap.IsAlt.exteriorSquareEquiv`: the isomorphism `⋀²M ≃ N` induced by an alternating
  bilinear map carrying the ordered pairs of a basis of `M` to a basis of `N`.

## Main results

* `LinearMap.IsAlt.exteriorSquareEquiv_ιMulti`: the isomorphism sends `x ∧ y` to `ω x y`.
* `LinearMap.IsAlt.exteriorSquareEquiv_symm_apply`: its inverse sends the basis vector indexed by
  `i < j` to `b i ∧ b j`.
* `exteriorPower.ιMulti_two_add_left`, `exteriorPower.ιMulti_two_add_right`,
  `exteriorPower.ιMulti_two_smul_left`, `exteriorPower.ιMulti_two_smul_right`,
  `exteriorPower.ιMulti_two_neg_right`, `exteriorPower.ιMulti_two_sub_right`,
  `exteriorPower.ιMulti_two_swap`, and `exteriorPower.ιMulti_two_self`: the wedge `u ∧ w` of two
  vectors is bilinear and alternating.
* `exteriorPower.ιMulti_two_swap_of_lt` and `exteriorPower.ιMulti_two_comp`: wedges of two
  vectors of a family, normalized to increasing order and written as vectors of length two.
* `exteriorPower.linearMap_ext_ιMulti_two`: linear maps out of `⋀²M` are determined on pure wedges
  `u ∧ v`.
-/

public section

namespace exteriorPower

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- The wedge `u ∧ w` is additive in `u`. -/
theorem ιMulti_two_add_left (u u' w : M) :
    ιMulti R 2 ![u + u', w] = ιMulti R 2 ![u, w] + ιMulti R 2 ![u', w] :=
  Subtype.ext <| by simp [ExteriorAlgebra.ιMulti_apply, Matrix.vecTail, add_mul]

/-- The wedge `u ∧ w` is additive in `w`. -/
theorem ιMulti_two_add_right (u w w' : M) :
    ιMulti R 2 ![u, w + w'] = ιMulti R 2 ![u, w] + ιMulti R 2 ![u, w'] := by
  apply Subtype.ext
  simp [ExteriorAlgebra.ιMulti_apply, Matrix.vecTail, mul_add]

/-- The wedge `u ∧ w` is homogeneous in `w`. -/
theorem ιMulti_two_smul_right (u w : M) (c : R) :
    ιMulti R 2 ![u, c • w] = c • ιMulti R 2 ![u, w] := by
  apply Subtype.ext
  simp [ExteriorAlgebra.ιMulti_apply, Matrix.vecTail]

/-- The wedge `u ∧ w` is homogeneous in `u`. -/
theorem ιMulti_two_smul_left (u w : M) (c : R) :
    ιMulti R 2 ![c • u, w] = c • ιMulti R 2 ![u, w] := by
  apply Subtype.ext
  simp [ExteriorAlgebra.ιMulti_apply, Matrix.vecTail]

/-- The wedge `u ∧ w` changes sign when `w` is negated. -/
theorem ιMulti_two_neg_right (u w : M) :
    ιMulti R 2 ![u, -w] = -ιMulti R 2 ![u, w] := by
  apply Subtype.ext
  simp [ExteriorAlgebra.ιMulti_apply, Matrix.vecTail]

/-- The wedge `u ∧ w` is subtractive in `w`. -/
theorem ιMulti_two_sub_right (u w w' : M) :
    ιMulti R 2 ![u, w - w'] = ιMulti R 2 ![u, w] - ιMulti R 2 ![u, w'] := by
  rw [sub_eq_add_neg w, ιMulti_two_add_right, ιMulti_two_neg_right, sub_eq_add_neg]

/-- The wedge `u ∧ w` is antisymmetric: `w ∧ u = -(u ∧ w)`. -/
theorem ιMulti_two_swap (u w : M) :
    ιMulti R 2 ![w, u] = -ιMulti R 2 ![u, w] := by
  simpa using (ιMulti R 2).map_swap ![u, w] (i := 0) (j := 1) Fin.zero_ne_one

/-- Wedges of two vectors of a family indexed by a linear order are normalized to increasing
order. The order hypothesis lets `simp` use this rule only in that direction. -/
theorem ιMulti_two_swap_of_lt {ι : Type*} [LinearOrder ι] (v : ι → M) {i j : ι} (_ : j < i) :
    ιMulti R 2 ![v i, v j] = -ιMulti R 2 ![v j, v i] :=
  ιMulti_two_swap _ _

/-- The wedge of the vectors `v (p 0)` and `v (p 1)` of a family `v`, indexed through
`p : Fin 2 → ι`, written as a vector of length two. -/
theorem ιMulti_two_comp {ι : Type*} (v : ι → M) (p : Fin 2 → ι) :
    ιMulti R 2 (fun j ↦ v (p j)) = ιMulti R 2 ![v (p 0), v (p 1)] := by
  congr 1
  ext j : 1
  fin_cases j <;> rfl

/-- The wedge `u ∧ u` of a vector with itself vanishes. -/
@[simp]
theorem ιMulti_two_self (u : M) : ιMulti R 2 ![u, u] = 0 :=
  (ιMulti R 2).map_eq_zero_of_eq ![u, u] (i := 0) (j := 1) rfl zero_ne_one

/-- Two linear maps out of `⋀[R]^2 M` agree if they agree on all pure wedges `u ∧ v`. -/
theorem linearMap_ext_ιMulti_two {N : Type*} [AddCommGroup N] [Module R N]
    {f g : ⋀[R]^2 M →ₗ[R] N}
    (h : ∀ u v : M, f (ιMulti R 2 ![u, v]) = g (ιMulti R 2 ![u, v])) : f = g :=
  linearMap_ext <| AlternatingMap.ext fun v ↦ by rw [← FinVec.etaExpand_eq v]; exact h (v 0) (v 1)

end exteriorPower

namespace LinearMap.IsAlt

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [LinearOrder ι] {ω : M →ₗ[R] M →ₗ[R] N}

/-- **Recognizing an exterior square.** Let `ω` be an alternating bilinear map, `b` a basis of `M`
indexed by a linearly ordered type, and `c` a basis of `N` indexed by the pairs `i < j` with
`c (i, j) = ω (b i) (b j)`. Then the linear map `⋀²M → N` induced by `ω`, which sends `x ∧ y` to
`ω x y` (`LinearMap.IsAlt.exteriorSquareEquiv_ιMulti`), is an isomorphism. -/
noncomputable def exteriorSquareEquiv (hω : ω.IsAlt) (b : Module.Basis ι R M)
    (c : Module.Basis {ij : ι × ι // ij.1 < ij.2} R N)
    (hc : ∀ ij, ω (b ij.val.1) (b ij.val.2) = c ij) : ⋀[R]^2 M ≃ₗ[R] N :=
  LinearEquiv.ofLinearMap (exteriorPower.alternatingMapLinearEquiv hω.toAlternatingMap)
    (c.constr R fun ij ↦ exteriorPower.ιMulti R 2 ![b ij.val.1, b ij.val.2])
    (c.ext fun ij ↦ by
      simp [Module.Basis.constr_basis, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, hc])
    (exteriorPower.linearMap_ext <| b.ext_alternating fun v hv ↦ by
      have hv01 : v 0 ≠ v 1 := hv.ne (by decide)
      have hbv : (fun i ↦ b (v i)) = ![b (v 0), b (v 1)] := by
        ext i
        fin_cases i <;> rfl
      simp only [hbv, LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti, toAlternatingMap_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one, LinearMap.id_apply]
      rcases hv01.lt_or_gt with h | h
      · rw [hc ⟨(v 0, v 1), h⟩, Module.Basis.constr_basis]
      · -- The pair is out of order: swap it, at the cost of a sign on both sides.
        have hswap : ![b (v 0), b (v 1)] = ![b (v 1), b (v 0)] ∘ Equiv.swap 0 1 := by
          ext i
          fin_cases i <;> rfl
        rw [← hω.neg, hc ⟨(v 1, v 0), h⟩, map_neg, Module.Basis.constr_basis, hswap,
          AlternatingMap.map_swap _ _ (by decide)])

/-- The isomorphism induced by `ω` sends `x ∧ y` to `ω x y`. -/
@[simp]
theorem exteriorSquareEquiv_ιMulti (hω : ω.IsAlt) (b : Module.Basis ι R M)
    (c : Module.Basis {ij : ι × ι // ij.1 < ij.2} R N)
    (hc : ∀ ij, ω (b ij.val.1) (b ij.val.2) = c ij) (v : Fin 2 → M) :
    hω.exteriorSquareEquiv b c hc (exteriorPower.ιMulti R 2 v) = ω (v 0) (v 1) := by
  simp [exteriorSquareEquiv, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

/-- The inverse isomorphism sends the basis vector of `N` indexed by `i < j` to `b i ∧ b j`. -/
@[simp]
theorem exteriorSquareEquiv_symm_apply (hω : ω.IsAlt) (b : Module.Basis ι R M)
    (c : Module.Basis {ij : ι × ι // ij.1 < ij.2} R N)
    (hc : ∀ ij, ω (b ij.val.1) (b ij.val.2) = c ij) (ij : {ij : ι × ι // ij.1 < ij.2}) :
    (hω.exteriorSquareEquiv b c hc).symm (c ij) =
      exteriorPower.ιMulti R 2 ![b ij.val.1, b ij.val.2] := by
  simp [exteriorSquareEquiv, Module.Basis.constr_basis]

end LinearMap.IsAlt
