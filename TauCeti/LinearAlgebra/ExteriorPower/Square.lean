/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import TauCeti.LinearAlgebra.BilinearForm.Multilinear

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
-/

public section

namespace LinearMap.IsAlt

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [LinearOrder ι] {ω : M →ₗ[R] M →ₗ[R] N}

/-- **Recognizing an exterior square.** Let `ω` be an alternating bilinear map, `b` a basis of `M`
indexed by a linearly ordered type, and `c` a basis of `N` indexed by the pairs `i < j` with
`c (i, j) = ω (b i) (b j)`. Then the linear map `⋀²M → N` induced by `ω`, which sends `x ∧ y` to
`ω x y` (`LinearMap.IsAlt.exteriorSquareEquiv_ιMulti`), is an isomorphism. -/
noncomputable def exteriorSquareEquiv (hω : ω.IsAlt) (b : Module.Basis ι R M)
    (c : Module.Basis {ij : ι × ι // ij.1 < ij.2} R N)
    (hc : ∀ ij, ω (b ij.1.1) (b ij.1.2) = c ij) : ⋀[R]^2 M ≃ₗ[R] N :=
  LinearEquiv.ofLinearMap (exteriorPower.alternatingMapLinearEquiv hω.toAlternatingMap)
    (c.constr R fun ij ↦ exteriorPower.ιMulti R 2 ![b ij.1.1, b ij.1.2])
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
    (hc : ∀ ij, ω (b ij.1.1) (b ij.1.2) = c ij) (v : Fin 2 → M) :
    hω.exteriorSquareEquiv b c hc (exteriorPower.ιMulti R 2 v) = ω (v 0) (v 1) := by
  simp [exteriorSquareEquiv, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]

/-- The inverse isomorphism sends the basis vector of `N` indexed by `i < j` to `b i ∧ b j`. -/
@[simp]
theorem exteriorSquareEquiv_symm_apply (hω : ω.IsAlt) (b : Module.Basis ι R M)
    (c : Module.Basis {ij : ι × ι // ij.1 < ij.2} R N)
    (hc : ∀ ij, ω (b ij.1.1) (b ij.1.2) = c ij) (ij : {ij : ι × ι // ij.1 < ij.2}) :
    (hω.exteriorSquareEquiv b c hc).symm (c ij) =
      exteriorPower.ιMulti R 2 ![b ij.1.1, b ij.1.2] := by
  simp [exteriorSquareEquiv, Module.Basis.constr_basis]

end LinearMap.IsAlt
