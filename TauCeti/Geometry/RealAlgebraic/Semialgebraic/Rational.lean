/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.Ring.Defs
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Function

/-!
# Semialgebraic preimages and graphs of rational maps

Let `K` be a linearly ordered field and `r x j = eval x (f j) / eval x (g j)` be a map whose
coordinates are quotients of polynomials. On any semialgebraic domain `u` where none of the
denominators `g j` vanish:

* when the output coordinate index `τ` is finite, `r` is semialgebraic on `u`
  (`TauCeti.isSemialgebraicOn_eval_div`), because its graph over `u` is cut out by the polynomial
  equations `g_j(x) y_j - f_j(x) = 0`;
* when `K` is a strict ordered ring (`[IsStrictOrderedRing K]`), the preimage `u ∩ r ⁻¹' s` of any
  semialgebraic set `s ⊆ τ → K` is semialgebraic
  (`TauCeti.IsSemialgebraic.inter_preimage_eval_div`), without assuming projection closure
  (`TauCeti.HasSemialgebraicProjections K`) or finiteness of `τ`: clearing denominators by
  positive squares turns every polynomial sign condition in `r x` into a polynomial sign condition
  in `x`.

## References

* J. Bochnak, M. Coste, and M.-F. Roy, *Real Algebraic Geometry*, Ergebnisse der Mathematik
  und ihrer Grenzgebiete 36, Springer (1998), Section 2.1.
-/

public section

open MvPolynomial Set

namespace TauCeti

section Graph

variable {σ τ K : Type*} [Field K] [LinearOrder K]

/-- A map with finitely many output coordinates given by quotients of polynomials is semialgebraic
on any semialgebraic domain where none of its denominators vanish. -/
theorem isSemialgebraicOn_eval_div [Finite τ] (f g : τ → MvPolynomial σ K)
    {s : Set (σ → K)} (hs : IsSemialgebraic s) (hg : ∀ x ∈ s, ∀ j, eval x (g j) ≠ 0) :
    IsSemialgebraicOn (fun x j ↦ eval x (f j) / eval x (g j)) s := by
  refine isSemialgebraicOn_of_forall_eq_iff hs
    (fun j ↦ rename Sum.inl (g j) * X (Sum.inr j) - rename Sum.inl (f j)) fun x hx y ↦ ?_
  simp only [funext_iff, map_sub, map_mul, eval_rename, eval_X, Sum.elim_comp_inl, Sum.elim_inr]
  refine forall_congr' fun j ↦ ?_
  rw [div_eq_iff (hg x hx j), sub_eq_zero, mul_comm, eq_comm]

/-- A map with finitely many output coordinates given by quotients of nowhere-vanishing polynomials
is a semialgebraic map. -/
theorem isSemialgebraicMap_eval_div [Finite τ] (f g : τ → MvPolynomial σ K)
    (hg : ∀ x j, eval x (g j) ≠ 0) :
    IsSemialgebraicMap (fun x j ↦ eval x (f j) / eval x (g j)) :=
  isSemialgebraicOn_univ.1 <|
    isSemialgebraicOn_eval_div f g isSemialgebraic_univ fun x _ ↦ hg x

end Graph

section Preimage

variable {σ τ K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Clearing denominators of a polynomial evaluated on quotients `f j / g j` with strictly positive
even-power denominators over a set where no `g j` vanishes. -/
private theorem exists_eval_div_mul_eq_eval {u : Set (σ → K)}
    (f g : τ → MvPolynomial σ K) (hg : ∀ x ∈ u, ∀ j, eval x (g j) ≠ 0)
    (p : MvPolynomial τ K) :
    ∃ num denom : MvPolynomial σ K, (∀ x ∈ u, 0 < eval x denom) ∧
      ∀ x ∈ u, eval (fun j ↦ eval x (f j) / eval x (g j)) p * eval x denom = eval x num := by
  refine MvPolynomial.induction_on
    (motive := fun p ↦ ∃ num denom : MvPolynomial σ K, (∀ x ∈ u, 0 < eval x denom) ∧
      ∀ x ∈ u, eval (fun j ↦ eval x (f j) / eval x (g j)) p * eval x denom = eval x num) p
    (fun a ↦ ⟨C a, 1, fun _ _ ↦ by simp, fun _ _ ↦ by simp⟩)
    (fun p q ⟨np, dp, hdp, hp⟩ ⟨nq, dq, hdq, hq⟩ ↦
      ⟨np * dq + nq * dp, dp * dq, fun x hx ↦ ?_, fun x hx ↦ ?_⟩)
    (fun p j ⟨np, dp, hdp, hp⟩ ↦
      ⟨np * f j * g j, dp * g j ^ 2, fun x hx ↦ ?_, fun x hx ↦ ?_⟩)
  · simpa only [map_mul] using mul_pos (hdp x hx) (hdq x hx)
  · simp only [map_add, map_mul]
    have hp' := hp x hx
    have hq' := hq x hx
    grind
  · simpa only [map_mul, map_pow] using mul_pos (hdp x hx) (sq_pos_of_ne_zero (hg x hx j))
  · have hgj : eval x (f j) / eval x (g j) * eval x (g j) = eval x (f j) :=
      div_mul_cancel₀ _ (hg x hx j)
    have hp' := hp x hx
    simp only [map_mul, eval_X, sq]
    grind

/-- **Rational preimages.** On a semialgebraic domain `u` where none of the denominators `g j`
vanish, the preimage of a semialgebraic set under `x ↦ fun j ↦ eval x (f j) / eval x (g j)` is
semialgebraic. Neither projection closure nor finiteness of `τ` is required. -/
theorem IsSemialgebraic.inter_preimage_eval_div {s : Set (τ → K)} (hs : IsSemialgebraic s)
    {u : Set (σ → K)} (hu : IsSemialgebraic u) (f g : τ → MvPolynomial σ K)
    (hg : ∀ x ∈ u, ∀ j, eval x (g j) ≠ 0) :
    IsSemialgebraic (u ∩ (fun x j ↦ eval x (f j) / eval x (g j)) ⁻¹' s) := by
  refine hs.induction
    (motive := fun t ↦ IsSemialgebraic (u ∩ (fun x j ↦ eval x (f j) / eval x (g j)) ⁻¹' t))
    (fun p ↦ ?_) (fun p ↦ ?_) (fun t _ iht ↦ ?_) (fun t w _ _ iht ihw ↦ ?_)
  · obtain ⟨num, denom, hpos, hmul⟩ := exists_eval_div_mul_eq_eval f g hg p
    convert hu.inter (isSemialgebraic_eval_eq_zero num) using 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    refine and_congr_right fun hx ↦ ?_
    rw [← hmul x hx, mul_eq_zero, or_iff_left (hpos x hx).ne']
  · obtain ⟨num, denom, hpos, hmul⟩ := exists_eval_div_mul_eq_eval f g hg p
    convert hu.inter (isSemialgebraic_eval_pos num) using 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
    refine and_congr_right fun hx ↦ ?_
    rw [← hmul x hx, mul_pos_iff_of_pos_right (hpos x hx)]
  · convert hu.sdiff iht using 1
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_sdiff]
    tauto
  · rw [preimage_union, inter_union_distrib_left]
    exact iht.union ihw

/-- The preimage of a semialgebraic set under a rational map with nowhere-vanishing denominators
is semialgebraic. -/
theorem IsSemialgebraic.preimage_eval_div {s : Set (τ → K)} (hs : IsSemialgebraic s)
    (f g : τ → MvPolynomial σ K) (hg : ∀ x j, eval x (g j) ≠ 0) :
    IsSemialgebraic ((fun x j ↦ eval x (f j) / eval x (g j)) ⁻¹' s) := by
  simpa using hs.inter_preimage_eval_div isSemialgebraic_univ f g fun x _ ↦ hg x

end Preimage

end TauCeti
