/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.IwasawaBruhat
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transvection

/-!
# Transposition-transvection factorisation for the Iwahori quadratic relation

Let `K` be a field and `m` a finite index type. For distinct indices `a ≠ b` and a unit `u : Kˣ`,
the product of the transposition matrix `permutationGL (Equiv.swap a b)` with the transvection
`1 + u E_{ab}` factors as `x_{ab}(u⁻¹) * diag(-u⁻¹, u) * x_{ba}(u⁻¹)`
(`TauCeti.permutationGL_swap_mul_transvectionUnit`).

Over a valuation subring `A` of `K`, when `u` has valuation `1`, every entry of the diagonal factor
has valuation `1` (`TauCeti.valuation_mulSingle_neg_inv_mul_mulSingle_eq_one`), so it normalises
the pro-`p` Iwahori subgroup `I₁`. Together these identities form the matrix core of the
Iwahori–Hecke quadratic relation.

## Main results

* `TauCeti.permutationGL_swap_mul_transvectionUnit`:
  `s * x_{ab}(u) = x_{ab}(u⁻¹) * diag(-u⁻¹, u) * x_{ba}(u⁻¹)`.
* `TauCeti.valuation_mulSingle_neg_inv_mul_mulSingle_eq_one`: if `A.valuation u = 1`, every entry
  of `Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b u` has valuation `1`.

## References

* T. J. Haines, R. E. Kottwitz and A. Prasad, *Iwahori–Hecke algebras*, J. Ramanujan Math. Soc.
  25 (2010), §1.
* Adapted from `src/Lib/LocalGL/Iwahori/QuadraticRelation.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.swap_mul_transvectionGL` and `New.v_mulSingle_neg_inv_mul_mulSingle_eq_one`.
-/

public section

open Matrix

namespace TauCeti

variable {K : Type*} [Field K] {m : Type*} [DecidableEq m]

/-- The matrix factorisation
`s * x_{ab}(u) = x_{ab}(u⁻¹) * diag(-u⁻¹, u) * x_{ba}(u⁻¹)` for the transposition `s = swap a b`,
distinct indices `a ≠ b`, and a unit `u : Kˣ`. -/
theorem permutationGL_swap_mul_transvectionUnit [Fintype m] {a b : m} (h : a ≠ b) (u : Kˣ) :
    permutationGL (Equiv.swap a b) * transvectionUnit h (u : K) =
      transvectionUnit h ((u⁻¹ : Kˣ) : K) *
        diagGL (Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b u) *
        transvectionUnit h.symm ((u⁻¹ : Kˣ) : K) := by
  ext i j
  simp [Units.val_mul, permutationGL_coe, PEquiv.toMatrix_mul_apply,
    coe_transvectionUnit_eq_one_add_single, diagGL_coe, mul_add, add_mul, Matrix.single_apply,
    Matrix.one_apply, Matrix.diagonal_apply, apply_ite Units.val, Pi.mulSingle_apply]
  grind

/-- If `u : Kˣ` has valuation `1`, then every entry of the diagonal torus element with `-u⁻¹` at
`a`, `u` at `b`, and `1` elsewhere has valuation `1`. -/
theorem valuation_mulSingle_neg_inv_mul_mulSingle_eq_one (A : ValuationSubring K) (a b : m)
    {u : Kˣ} (hu : A.valuation (u : K) = 1) (i : m) :
    A.valuation ((Pi.mulSingle a (-u⁻¹) * Pi.mulSingle b u : m → Kˣ) i : K) = 1 := by
  simp only [Pi.mul_apply, Units.val_mul, map_mul, Pi.mulSingle_apply]
  split_ifs <;> simp [Units.val_inv_eq_inv_val, hu]

end TauCeti
