/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPolynomial.Ideal
public import TauCeti.Algebra.MvPolynomial.Taylor

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
  ext p
  rw [RingHom.mem_ker, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    ← pow_one (idealOfVars σ R), mem_pow_idealOfVars_iff', ← constantCoeff_taylor,
    constantCoeff_eq]
  simp [Finsupp.degree_eq_zero_iff]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R]

/-- Over a commutative ring, the `k`-th power of the evaluation ideal at `a` is the pullback of
the `k`-th power of the ideal of variables along the Taylor shift `taylor a`. -/
theorem pow_ker_eval_eq_comap_taylor (a : σ → R) (k : ℕ) :
    RingHom.ker (eval a) ^ k = (idealOfVars σ R ^ k).comap (taylor a).toRingHom := by
  have hhom : (taylor a : MvPolynomial σ R →+* MvPolynomial σ R) =
      ((taylorEquiv a).toRingEquiv : MvPolynomial σ R →+* MvPolynomial σ R) :=
    RingHom.ext fun p ↦ (taylorEquiv_apply a p).symm
  have hcoe (I : Ideal (MvPolynomial σ R)) :
      I.comap (taylor a).toRingHom = I.comap (taylorEquiv a).toRingEquiv := by
    rw [AlgHom.toRingHom_eq_coe, hhom, Ideal.comap_coe]
  rw [ker_eval_eq_comap_taylor a, hcoe, ← Ideal.map_symm, ← Ideal.map_pow, Ideal.map_symm, ← hcoe]

/-- A polynomial lies in the `k`-th power of the evaluation ideal at `a` if and only if its Taylor
shift at `a` lies in the `k`-th power of the ideal of variables. -/
theorem mem_pow_ker_eval_iff (a : σ → R) (k : ℕ) {p : MvPolynomial σ R} :
    p ∈ RingHom.ker (eval a) ^ k ↔ taylor a p ∈ idealOfVars σ R ^ k := by
  simp [pow_ker_eval_eq_comap_taylor]

end CommRing

end MvPolynomial
