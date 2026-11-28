/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Basic
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.LinearAlgebra.Dimension.Constructions
import TauCeti.LinearAlgebra.Charpoly.Quotient

/-!
# Determinant character and twisting endomorphisms on the Hall algebra

For a multiplicative character `χ : MulChar k ℂ` of a field `k`, the determinant character
`TauCeti.HallAlgebra.detChar χ` sends a similarity class `c` to
`χ ((-1) ^ c.dim * c.charpoly.coeff 0)` (which equals `χ g.det` at `ofEnd g`). Because the
determinant is multiplicative along invariant subspaces and quotients, pointwise multiplication by
`detChar χ` defines a `ℂ`-algebra endomorphism `TauCeti.HallAlgebra.detTwist χ` of
`TauCeti.HallAlgebra k` when `k` is finite.

* `TauCeti.HallAlgebra.detChar`: the class function `c ↦ χ ((-1) ^ c.dim * c.charpoly.coeff 0)`.
* `TauCeti.HallAlgebra.detChar_ofEnd`: `detChar χ (ofEnd g) = χ g.det`.
* `TauCeti.HallAlgebra.detChar_eq_one_of_dim_eq_zero`: `detChar χ o = 1` when `o.dim = 0`.
* `TauCeti.HallAlgebra.detChar_ofEnd_eq_mul`: multiplicativity of `detChar χ` along an invariant
  subspace and its quotient.
* `TauCeti.HallAlgebra.detTwist`: the `ℂ`-algebra endomorphism `F ↦ fun c ↦ detChar χ c * F c`
  of `HallAlgebra k` for finite `k`.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.

## Provenance

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
  PBC), files `src/Lib/LocalGL/Green/TauFunctions.lean` (`New.detChar`) and
  `src/Lib/LocalGL/Green/LabelCharacters.lean` (`New.evalGL_labelChar_mul_det`).
-/

public section

namespace TauCeti.HallAlgebra

open SimilarityClass

section Field

variable {k : Type*} [Field k]

/-- The determinant character `χ ∘ det` as an element of `HallAlgebra k`, defined on a
similarity class `c` via the constant term of its characteristic polynomial. -/
noncomputable def detChar (χ : MulChar k ℂ) : HallAlgebra k :=
  fun c ↦ χ ((-1) ^ c.dim * c.charpoly.coeff 0)

/-- At the similarity class of an endomorphism `g`, `detChar χ` evaluates to `χ g.det`. -/
@[simp]
theorem detChar_ofEnd (χ : MulChar k ℂ) {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (g : Module.End k V) :
    detChar χ (ofEnd g) = χ (LinearMap.det g) := by
  let b := Module.finBasis k V
  rw [detChar, dim_ofEnd, charpoly_ofEnd, ← LinearMap.det_toMatrix b,
    ← LinearMap.charpoly_toMatrix g b, Matrix.det_eq_sign_charpoly_coeff, Fintype.card_fin]

/-- On a dimension-zero similarity class, `detChar χ` takes the value `1`. -/
@[simp]
theorem detChar_eq_one_of_dim_eq_zero (χ : MulChar k ℂ) {o : SimilarityClass k} (h : o.dim = 0) :
    detChar χ o = 1 := by
  have hsub : Subsingleton (Fin o.dim → k) := by rw [h]; infer_instance
  have hrep : o.rep = LinearMap.id := LinearMap.ext fun _ ↦ hsub.elim _ _
  rw [← ofEnd_rep o, detChar_ofEnd, hrep, LinearMap.det_id, map_one]

/-- The determinant character is multiplicative along an invariant subspace and its quotient. -/
theorem detChar_ofEnd_eq_mul (χ : MulChar k ℂ) {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {g : Module.End k V} {U : Submodule k V} (hU : U ∈ g.invtSubmodule) :
    detChar χ (ofEnd g) =
      detChar χ (ofEnd (g.invtRestrict hU)) * detChar χ (ofEnd (g.invtQuot hU)) := by
  have hchar := (Module.End.charpoly_invtRestrict_mul_charpoly_invtQuot hU).symm
  have hdim : Module.finrank k V = Module.finrank k U + Module.finrank k (V ⧸ U) := by
    rw [add_comm, Submodule.finrank_quotient_add_finrank U]
  simp only [detChar, dim_ofEnd, charpoly_ofEnd, hchar, Polynomial.mul_coeff_zero, hdim, pow_add,
    ← map_mul]
  congr 1
  ring

end Field

section Finite

variable {k : Type*} [Field k] [Finite k]

/-- Pointwise multiplication by `detChar χ` defines a `ℂ`-algebra endomorphism of
`HallAlgebra k`. -/
noncomputable def detTwist (χ : MulChar k ℂ) : HallAlgebra k →ₐ[ℂ] HallAlgebra k where
  toFun F c := detChar χ c * F c
  map_one' := by
    ext c
    by_cases h : c.dim = 0
    · simp [one_apply, h, detChar_eq_one_of_dim_eq_zero]
    · simp [one_apply, h]
  map_mul' F H := by
    refine ext_ofEnd fun n g ↦ ?_
    have := Fintype.ofFinite g.invtSubmodule
    simp only [mul_ofEnd_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun U _ ↦ ?_
    rw [detChar_ofEnd_eq_mul χ U.property]
    ring
  map_zero' := by ext c; simp [zero_apply]
  map_add' F H := by ext c; simp [add_apply, mul_add]
  commutes' a := by
    ext c
    by_cases h : c.dim = 0
    · simp [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply, h,
        detChar_eq_one_of_dim_eq_zero]
    · simp [Algebra.algebraMap_eq_smul_one, smul_apply, one_apply, h]

@[simp]
theorem detTwist_apply (χ : MulChar k ℂ) (F : HallAlgebra k) (c : SimilarityClass k) :
    detTwist χ F c = detChar χ c * F c := by
  rfl

end Finite

end TauCeti.HallAlgebra
