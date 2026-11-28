/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.MulChar.Basic
public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Basic

import Mathlib.LinearAlgebra.Charpoly.BaseChange
import TauCeti.LinearAlgebra.Charpoly.Quotient

/-!
# Determinant character and twisting endomorphisms on the Hall algebra

For a multiplicative character `χ : MulChar k ℂ` of a field `k`, the determinant character
`χ.detChar` sends a similarity class `c` to `χ ((-1) ^ c.dim * c.charpoly.coeff 0)` (which equals
`χ g.det` at `ofEnd g`). Because the determinant is multiplicative along invariant subspaces and
quotients (`Module.End.det_eq_det_invtRestrict_mul_det_invtQuot`), pointwise multiplication by
`χ.detChar` defines a `ℂ`-algebra endomorphism `χ.detTwist` of `TauCeti.HallAlgebra k` when `k` is
finite. Restricting `χ.detTwist F` to `GL_n(k)` via `TauCeti.HallAlgebra.toClassFunction` gives
the restriction of `F` multiplied pointwise by `χ ∘ det`.

* `Module.End.det_eq_det_invtRestrict_mul_det_invtQuot`: `g.det = (g.invtRestrict hU).det *
  (g.invtQuot hU).det` for an invariant subspace `U ∈ g.invtSubmodule`.
* `MulChar.detChar`: the class function `c ↦ χ ((-1) ^ c.dim * c.charpoly.coeff 0)`.
* `MulChar.detChar_apply`: explicit coefficient formula for `χ.detChar c`.
* `MulChar.detChar_ofEnd`: `χ.detChar (ofEnd g) = χ g.det`.
* `MulChar.detChar_eq_one_of_dim_eq_zero`: `χ.detChar o = 1` when `o.dim = 0`.
* `MulChar.detChar_ofEnd_eq_mul`: multiplicativity of `χ.detChar` along an invariant subspace and
  its quotient.
* `MulChar.detTwist`: the `ℂ`-algebra endomorphism `F ↦ fun c ↦ χ.detChar c * F c` of
  `HallAlgebra k` for finite `k`.
* `MulChar.detTwist_apply`: evaluation rule `(χ.detTwist F) c = χ.detChar c * F c`.
* `MulChar.detTwist_rankPart`: `χ.detTwist` commutes with `TauCeti.HallAlgebra.rankPart`.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.

## Provenance

* Adapted from grh-lean (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic,
  PBC), files `src/Lib/LocalGL/Green/TauFunctions.lean` (`New.detChar`) and
  `src/Lib/LocalGL/Green/LabelCharacters.lean` (`New.evalGL_labelChar_mul_det`).
-/

public section

open TauCeti TauCeti.HallAlgebra TauCeti.SimilarityClass

/-- The determinant of an endomorphism of a finite-dimensional vector space factors as the product
of the determinants of its restriction to an invariant subspace and the induced endomorphism on the
quotient. -/
theorem Module.End.det_eq_det_invtRestrict_mul_det_invtQuot {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] {g : Module.End k V} {U : Submodule k V}
    (hU : U ∈ g.invtSubmodule) :
    LinearMap.det g =
      LinearMap.det (g.invtRestrict hU) * LinearMap.det (g.invtQuot hU) := by
  rw [Module.End.invtRestrict_def, Module.End.invtQuot_def]
  exact LinearMap.det_eq_det_mul_det U g ((Module.End.mem_invtSubmodule g).1 hU)

namespace MulChar

section Field

variable {k : Type*} [Field k]

/-- The determinant character `χ ∘ det` as an element of `HallAlgebra k`, defined on a
similarity class `c` via the constant term of its characteristic polynomial. -/
noncomputable def detChar (χ : MulChar k ℂ) : HallAlgebra k :=
  fun c ↦ χ ((-1) ^ c.dim * c.charpoly.coeff 0)

/-- Coefficient formula for the determinant character `χ.detChar` on an arbitrary similarity
class. -/
theorem detChar_apply (χ : MulChar k ℂ) (c : SimilarityClass k) :
    χ.detChar c = χ ((-1) ^ c.dim * c.charpoly.coeff 0) := by
  rfl

/-- At the similarity class of an endomorphism `g`, `χ.detChar` evaluates to `χ g.det`. -/
@[simp]
theorem detChar_ofEnd (χ : MulChar k ℂ) {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (g : Module.End k V) :
    χ.detChar (ofEnd g) = χ (LinearMap.det g) := by
  rw [detChar, dim_ofEnd, charpoly_ofEnd, LinearMap.det_eq_sign_charpoly_coeff]

/-- On a dimension-zero similarity class, `χ.detChar` takes the value `1`. -/
@[simp]
theorem detChar_eq_one_of_dim_eq_zero (χ : MulChar k ℂ) {o : SimilarityClass k} (h : o.dim = 0) :
    χ.detChar o = 1 := by
  have : Subsingleton (Fin o.dim → k) := by rw [h]; infer_instance
  rw [← ofEnd_rep o, detChar_ofEnd, LinearMap.det_eq_one_of_subsingleton, map_one]

/-- The determinant character is multiplicative along an invariant subspace and its quotient. -/
theorem detChar_ofEnd_eq_mul (χ : MulChar k ℂ) {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] {g : Module.End k V} {U : Submodule k V} (hU : U ∈ g.invtSubmodule) :
    χ.detChar (ofEnd g) =
      χ.detChar (ofEnd (g.invtRestrict hU)) * χ.detChar (ofEnd (g.invtQuot hU)) := by
  rw [detChar_ofEnd, detChar_ofEnd, detChar_ofEnd, ← map_mul,
    g.det_eq_det_invtRestrict_mul_det_invtQuot hU]

end Field

section Finite

variable {k : Type*} [Field k] [Finite k]

/-- Pointwise multiplication by `χ.detChar` defines a `ℂ`-algebra endomorphism of
`HallAlgebra k`. -/
noncomputable def detTwist (χ : MulChar k ℂ) : HallAlgebra k →ₐ[ℂ] HallAlgebra k :=
  let f : HallAlgebra k →ₗ[ℂ] HallAlgebra k :=
    LinearMap.piMap fun c : SimilarityClass k ↦ LinearMap.mulLeft ℂ (χ.detChar c)
  have hf (F : HallAlgebra k) (c : SimilarityClass k) : f F c = χ.detChar c * F c := rfl
  AlgHom.ofLinearMap f
    (by
      ext c
      rw [hf]
      by_cases h : c.dim = 0
      · simp [h, detChar_eq_one_of_dim_eq_zero]
      · simp [h])
    (by
      intro F H
      refine ext_ofEnd fun n g ↦ ?_
      simp only [hf, HallAlgebra.mul_ofEnd, mul_finsum]
      refine finsum_congr fun U ↦ ?_
      rw [detChar_ofEnd_eq_mul χ U.property]
      ring)

/-- Evaluating `χ.detTwist F` at a similarity class `c` multiplies `F c` by `χ.detChar c`. -/
@[simp]
theorem detTwist_apply (χ : MulChar k ℂ) (F : HallAlgebra k) (c : SimilarityClass k) :
    χ.detTwist F c = χ.detChar c * F c := by
  rfl

/-- Twisting by `χ.detChar` commutes with restriction to similarity classes of a given rank. -/
@[simp]
theorem detTwist_rankPart (χ : MulChar k ℂ) (n : ℕ) (F : HallAlgebra k) :
    χ.detTwist (rankPart n F) = rankPart n (χ.detTwist F) := by
  ext c
  by_cases h : c.dim = n <;> simp [rankPart_apply, h]

end Finite

end MulChar
