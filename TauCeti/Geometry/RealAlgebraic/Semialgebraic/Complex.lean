/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Complex.BigOperators
public import TauCeti.Analysis.Complex.Euclidean.Space
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function

/-!
# Complex polynomial equations in real coordinates

A complex polynomial equation in complex coordinates `z` and their conjugates `star z` becomes two
real polynomial equations, its real and imaginary parts, in the real coordinates `Re z` and `Im z`.
So the subsets of complex coordinate spaces cut out by such equations are semialgebraic once
complex coordinates are split into their real and imaginary parts. This is how complex algebraic
sets, and sets such as the Hermitian matrices that also involve conjugation, enter real algebraic
geometry.

The real coordinates of `z : κ → ℂ` are indexed by `κ ⊕ κ`: `Sum.inl k` is the real part and
`Sum.inr k` the imaginary part of `z k`, as in `TauCeti.complexToRealEuclidean`.

## Main results

* `TauCeti.isSemialgebraic_setOf_eval_ofReal_eq_zero`: the real points of a complex polynomial
  equation form a semialgebraic set.
* `TauCeti.isSemialgebraic_setOf_eval_sumElim_star_eq_zero`: the zero set of a polynomial in
  complex coordinates and their conjugates is semialgebraic in the real coordinates.
* `TauCeti.isSemialgebraicOn_complexToRealPi_of_forall_eq_iff`: a map between complex coordinate
  spaces whose graph is cut out by such equations is semialgebraic in the real coordinates.
-/

public section

open MvPolynomial Complex

namespace TauCeti

variable {σ κ : Type*}

/-- The real points `a : σ → ℝ` of a complex polynomial equation `r(a) = 0` form a semialgebraic
set: it is cut out by the real polynomials whose coefficients are the real and the imaginary parts
of the coefficients of `r`. -/
theorem isSemialgebraic_setOf_eval_ofReal_eq_zero (r : MvPolynomial σ ℂ) :
    IsSemialgebraic {a : σ → ℝ | eval (fun s ↦ (a s : ℂ)) r = 0} := by
  -- At a real point every monomial is real, so the real and imaginary parts of `r(a)` are the
  -- values of the coefficientwise real and imaginary parts of `r`.
  have hmon (a : σ → ℝ) (d : σ →₀ ℕ) :
      ∏ s ∈ d.support, (a s : ℂ) ^ d s = ((∏ s ∈ d.support, a s ^ d s : ℝ) : ℂ) := by
    push_cast
    rfl
  have hre (a : σ → ℝ) : (eval (fun s ↦ (a s : ℂ)) r).re =
      eval a (∑ d ∈ r.support, monomial d (r.coeff d).re) := by
    rw [eval_eq]
    simp only [hmon, re_sum, re_mul_ofReal, map_sum, eval_monomial, Finsupp.prod]
  have him (a : σ → ℝ) : (eval (fun s ↦ (a s : ℂ)) r).im =
      eval a (∑ d ∈ r.support, monomial d (r.coeff d).im) := by
    rw [eval_eq]
    simp only [hmon, im_sum, im_mul_ofReal, map_sum, eval_monomial, Finsupp.prod]
  have h : {a : σ → ℝ | eval (fun s ↦ (a s : ℂ)) r = 0} =
      {a | eval a (∑ d ∈ r.support, monomial d (r.coeff d).re) = 0} ∩
        {a | eval a (∑ d ∈ r.support, monomial d (r.coeff d).im) = 0} := by
    ext a
    simp [Complex.ext_iff, hre, him]
  rw [h]
  exact (isSemialgebraic_eval_eq_zero _).inter (isSemialgebraic_eval_eq_zero _)

/-- The zero set of a polynomial `q(z, star z)` in complex coordinates `z : κ → ℂ` and their
conjugates is semialgebraic in the real coordinates `a : κ ⊕ κ → ℝ`, where
`z k = a (Sum.inl k) + a (Sum.inr k) * I`. -/
theorem isSemialgebraic_setOf_eval_sumElim_star_eq_zero (q : MvPolynomial (κ ⊕ κ) ℂ) :
    IsSemialgebraic {a : κ ⊕ κ → ℝ |
      eval (Sum.elim (fun k ↦ (a (.inl k) : ℂ) + a (.inr k) * I)
        (fun k ↦ star ((a (.inl k) : ℂ) + a (.inr k) * I))) q = 0} := by
  -- Substitute `z = x + y I` and `star z = x - y I` to obtain a complex polynomial in real
  -- variables.
  let L : κ ⊕ κ → MvPolynomial (κ ⊕ κ) ℂ :=
    Sum.elim (fun k ↦ X (.inl k) + X (.inr k) * C I) (fun k ↦ X (.inl k) - X (.inr k) * C I)
  have h (a : κ ⊕ κ → ℝ) :
      eval (Sum.elim (fun k ↦ (a (.inl k) : ℂ) + a (.inr k) * I)
        (fun k ↦ star ((a (.inl k) : ℂ) + a (.inr k) * I))) q =
        eval (fun s ↦ (a s : ℂ)) (bind₁ L q) := by
    have hL : (fun t ↦ eval (fun s ↦ (a s : ℂ)) (L t)) =
        Sum.elim (fun k ↦ (a (.inl k) : ℂ) + a (.inr k) * I)
          (fun k ↦ star ((a (.inl k) : ℂ) + a (.inr k) * I)) := by
      funext t
      cases t <;> simp [L, sub_eq_add_neg]
    rw [← hL]
    simp only [← coe_aeval_eq_eval]
    exact (aeval_bind₁ _ L q).symm
  simp only [h]
  exact isSemialgebraic_setOf_eval_ofReal_eq_zero _

/-- A map `g` between complex coordinate spaces, read in the real coordinates given by
`TauCeti.complexToRealPi`, is semialgebraic on a semialgebraic domain `s` when its graph over `s`
is cut out by finitely many polynomial equations in the input and output coordinates and their
conjugates: for `z ∈ s`, `g z = w` exactly when every `R k` vanishes at `(z, w)`. -/
theorem isSemialgebraicOn_complexToRealPi_of_forall_eq_iff {σ τ ι : Type*} [Fintype σ]
    [Fintype τ] [Finite ι] {g : (σ → ℂ) → (τ → ℂ)} {s : Set (σ → ℂ)}
    (hs : IsSemialgebraic ((complexToRealPi σ).symm ⁻¹' s))
    (R : ι → MvPolynomial ((σ ⊕ τ) ⊕ (σ ⊕ τ)) ℂ)
    (hR : ∀ z ∈ s, ∀ w, g z = w ↔
      ∀ k, eval (Sum.elim (Sum.elim z w) fun t ↦ star (Sum.elim z w t)) (R k) = 0) :
    IsSemialgebraicOn (fun a ↦ complexToRealPi τ (g ((complexToRealPi σ).symm a)))
      ((complexToRealPi σ).symm ⁻¹' s) := by
  refine isSemialgebraicOn_def.2 ⟨hs, ?_⟩
  -- Regroup the real coordinates of the graph, input then output, into real then imaginary parts.
  let f : (σ ⊕ τ) ⊕ (σ ⊕ τ) → (σ ⊕ σ) ⊕ (τ ⊕ τ) := Sum.elim (Sum.map .inl .inl) (Sum.map .inr .inr)
  convert (hs.preimage_comp Sum.inl).inter (IsSemialgebraic.iInter fun k ↦
    (isSemialgebraic_setOf_eval_sumElim_star_eq_zero (R k)).preimage_comp f) using 1
  ext v
  rw [mem_preimage_sumArrowEquivProdArrow_graphOn]
  simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_ofPred_eq]
  refine and_congr_right fun hv ↦ ?_
  rw [← ContinuousLinearEquiv.eq_symm_apply, hR _ hv]
  refine forall_congr' fun k ↦ Eq.congr_left (congr_arg (eval · (R k)) ?_)
  funext t
  rcases t with (t | t) | (t | t) <;> simp [f]

end TauCeti
