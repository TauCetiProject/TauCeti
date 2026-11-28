/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import TauCeti.Algebra.MvPolynomial.Taylor
import TauCeti.RingTheory.MvPolynomial.Ideal.Basic

/-!
# Point evaluation ideals and the Taylor shift

This file bridges Mathlib's `idealOfVars` and `TauCeti.Algebra.MvPolynomial.Taylor` by identifying
the evaluation ideal `RingHom.ker (eval a)` and its powers as pullbacks of the ideal of variables
`MvPolynomial.idealOfVars σ R` and its powers along the Taylor shift `MvPolynomial.taylor a`.

## Main results

* `MvPolynomial.ker_eval_eq_comap_taylor`: the kernel of `eval a` is the pullback of
  `idealOfVars σ R` along `taylor a`.
* `MvPolynomial.pow_ker_eval_eq_comap_taylor`: over a commutative ring, the `k`-th power of
  `RingHom.ker (eval a)` is the pullback of `idealOfVars σ R ^ k` along `taylor a`.
* `MvPolynomial.mem_pow_ker_eval_iff`: a polynomial lies in `RingHom.ker (eval a) ^ k` if and only
  if `taylor a p ∈ idealOfVars σ R ^ k`.
-/

public section

namespace MvPolynomial

variable {σ : Type*}

section CommSemiring

variable {R : Type*} [CommSemiring R]

/-- The evaluation ideal `RingHom.ker (eval a)` is the pullback of the ideal of variables along
the Taylor shift `taylor a`. -/
theorem ker_eval_eq_comap_taylor (a : σ → R) :
    RingHom.ker (eval a) = (idealOfVars σ R).comap (taylor a).toRingHom := by
  rw [← ker_constantCoeff, RingHom.comap_ker]
  congr 1
  exact RingHom.ext fun p ↦ (constantCoeff_taylor a p).symm

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

private theorem comap_taylor_eq_map_taylor_neg (a : σ → R) (I : Ideal (MvPolynomial σ R)) :
    I.comap (taylor a).toRingHom = I.map (taylor (-a)).toRingHom := by
  refine le_antisymm ?_ ?_
  · intro p hp
    rw [← taylor_neg_taylor a p]
    exact Ideal.mem_map_of_mem _ hp
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [Ideal.mem_comap, Ideal.mem_comap]
    simpa [taylor_taylor] using hp

/-- Over a commutative ring, the `k`-th power of the evaluation ideal at `a` is the pullback of
the `k`-th power of the ideal of variables along the Taylor shift `taylor a`. -/
theorem pow_ker_eval_eq_comap_taylor (a : σ → R) (k : ℕ) :
    RingHom.ker (eval a) ^ k = (idealOfVars σ R ^ k).comap (taylor a).toRingHom := by
  rw [ker_eval_eq_comap_taylor a, comap_taylor_eq_map_taylor_neg, ← Ideal.map_pow,
    ← comap_taylor_eq_map_taylor_neg]

/-- A polynomial lies in the `k`-th power of the evaluation ideal at `a` if and only if its Taylor
shift at `a` lies in the `k`-th power of the ideal of variables. -/
theorem mem_pow_ker_eval_iff (a : σ → R) (k : ℕ) {p : MvPolynomial σ R} :
    p ∈ RingHom.ker (eval a) ^ k ↔ taylor a p ∈ idealOfVars σ R ^ k := by
  simp [pow_ker_eval_eq_comap_taylor]

end CommRing

end MvPolynomial
