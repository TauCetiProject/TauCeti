/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Jimbo.Trace

/-!
# Adding an uncrossed strand in the Jimbo representation

Appending a fixed colour to every word intertwines the Jimbo actions on `n + 1` and
`n + 2` strands along `BraidGroup.strandIncl`. Thus the added strand retains its colour,
and the action on the old strands is unchanged. This is the tensor-power compatibility
needed when taking a partial trace over the added strand in a Markov stabilization.

The weighted trace of the included braid is its old weighted trace multiplied by the
quantum dimension. We work over arbitrary commutative rings and allow any number of
colours, including zero.

## References

* V. G. Turaev, *The Yang-Baxter equation and invariants of links*, Invent. Math.
  92 (1988), 527–553 (enhanced braid representations and their Markov traces).
* V. F. R. Jones, *Hecke algebra representations of braid groups and link polynomials*,
  Ann. of Math. 126 (1987), 335–388.

The word inclusion uses Mathlib's `Finsupp.lmapDomain` and `Fin.snoc`; no separate
tensor-space inclusion is introduced.
-/

public section

open Function Finsupp
open scoped BigOperators

namespace TauCeti.KnotTheory

variable {R : Type*} [CommRing R] {ι : Type*} [LinearOrder ι] {n : ℕ}

/-- Appending a colour intertwines a Jimbo generator with the generator on the same
two old strands of the larger word space. -/
theorem jimboGenerator_comp_lmapDomain_snoc (q : Rˣ) (j k : Fin n) (a : ι) :
    (jimboGenerator q j.castSucc k.castSucc).comp
        (lmapDomain R R (fun w : Fin n → ι ↦ Fin.snoc w a)) =
      (lmapDomain R R (fun w : Fin n → ι ↦ Fin.snoc w a)).comp
        (jimboGenerator q j k) := by
  classical
  ext w : 2
  have hswap : Fin.snoc w a ∘ Equiv.swap j.castSucc k.castSucc =
      Fin.snoc (w ∘ Equiv.swap j k) a := by
    funext i
    refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simp [Equiv.swap_apply_of_ne_of_ne, (Fin.castSucc_lt_last j).ne.symm,
        (Fin.castSucc_lt_last k).ne.symm]
    · rw [comp_apply, ← (Fin.castSucc_injective n).map_swap j k i]
      simp
  simp only [LinearMap.comp_apply, lsingle_apply]
  rw [lmapDomain_apply, mapDomain_single, jimboGenerator_single_one,
    jimboGenerator_single_one]
  simp only [Fin.snoc_castSucc, hswap]
  split_ifs <;> simp only [map_add, map_smul, lmapDomain_apply, mapDomain_single]

/-- The action of a braid after adding an uncrossed strand is its original action with
the last colour held fixed. This intertwining identity applies to arbitrary vectors. -/
@[simp↓]
theorem jimbo_strandIncl_lmapDomain_snoc (q : Rˣ) (b : BraidGroup (n + 1)) (a : ι)
    (v : (Fin (n + 1) → ι) →₀ R) :
    (jimbo ι q (BraidGroup.strandIncl b) : Module.End R ((Fin (n + 2) → ι) →₀ R))
        (lmapDomain R R (fun w ↦ Fin.snoc w a) v) =
      lmapDomain R R (fun w ↦ Fin.snoc w a)
        ((jimbo ι q b : Module.End R ((Fin (n + 1) → ι) →₀ R)) v) := by
  induction b using BraidGroup.sigma_induction_on generalizing v with
  | sigma i =>
    have hj : BraidGroup.strand i.castSucc = (BraidGroup.strand i).castSucc :=
      Fin.ext (by simp)
    have hk : BraidGroup.strandSucc i.castSucc = (BraidGroup.strandSucc i).castSucc :=
      Fin.ext (by simp)
    simp only [BraidGroup.strandIncl_sigma, jimbo_sigma, jimboUnit_val, hj, hk]
    exact DFunLike.congr_fun (jimboGenerator_comp_lmapDomain_snoc q _ _ a) v
  | one => simp
  | mul b c hb hc =>
    simp only [map_mul, Units.val_mul, Module.End.mul_apply, hc, hb]
  | inv b hb =>
    have h := congrArg
      (fun x ↦ (((jimbo ι q (BraidGroup.strandIncl b))⁻¹ :
        (Module.End R ((Fin (n + 2) → ι) →₀ R))ˣ) :
          Module.End R ((Fin (n + 2) → ι) →₀ R)) x)
      (hb ((((jimbo ι q b)⁻¹ : (Module.End R ((Fin (n + 1) → ι) →₀ R))ˣ) :
        Module.End R ((Fin (n + 1) → ι) →₀ R)) v))
    simpa only [map_inv, ← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel,
      mul_inv_cancel, Units.val_one, Module.End.one_apply] using h.symm

/-- Basis-vector form of compatibility with adding an uncrossed strand. -/
@[simp]
theorem jimbo_strandIncl_single_snoc (q : Rˣ) (b : BraidGroup (n + 1))
    (w : Fin (n + 1) → ι) (a : ι) (c : R) :
    (jimbo ι q (BraidGroup.strandIncl b) : Module.End R ((Fin (n + 2) → ι) →₀ R))
        (single (Fin.snoc w a) c) =
      mapDomain (fun u ↦ Fin.snoc u a)
        ((jimbo ι q b : Module.End R ((Fin (n + 1) → ι) →₀ R)) (single w c)) := by
  simpa only [lmapDomain_apply, mapDomain_single] using
    jimbo_strandIncl_lmapDomain_snoc q b a (single w c)

/-- Inclusion preserves coefficients on each fixed-last-colour block and has zero
coefficients between blocks with different last colours. -/
@[simp↓]
theorem jimbo_strandIncl_single_snoc_apply_snoc (q : Rˣ) (b : BraidGroup (n + 1))
    (w u : Fin (n + 1) → ι) (a d : ι) (c : R) :
    (jimbo ι q (BraidGroup.strandIncl b) : Module.End R ((Fin (n + 2) → ι) →₀ R))
        (single (Fin.snoc w a) c) (Fin.snoc u d) =
      if a = d then
        (jimbo ι q b : Module.End R ((Fin (n + 1) → ι) →₀ R)) (single w c) u
      else 0 := by
  classical
  rw [jimbo_strandIncl_single_snoc]
  by_cases h : a = d
  · subst d
    simp only [ite_true]
    exact mapDomain_apply_of_injective (@Fin.snoc_left_injective _ (fun _ ↦ ι) a) _ _
  · rw [ite_eq_right h]
    apply mapDomain_of_notMem_range
    rintro ⟨v, hv⟩
    apply h
    simpa using congrArg (fun z : Fin (n + 2) → ι ↦ z (Fin.last (n + 1))) hv

/-- An uncrossed strand multiplies the weighted braid trace by the quantum dimension. -/
@[simp]
theorem jimboWeightedTrace_strandIncl {N : ℕ} (q : Rˣ) (b : BraidGroup (n + 1)) :
    jimboWeightedTrace (N := N) q (BraidGroup.strandIncl b) =
      jimboWeightedTrace (N := N) q b * ∑ a : Fin N, jimboWeight q a := by
  classical
  rw [jimboWeightedTrace_eq_sum, ← (Fin.snocEquiv (fun _ : Fin (n + 2) ↦ Fin N)).sum_comp]
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fintype.sum_prod_type,
    jimbo_strandIncl_single_snoc_apply_snoc, ite_true]
  have hweight (w : Fin (n + 1) → Fin N) (a : Fin N) :
      (∏ i : Fin (n + 2), jimboWeight q ((Fin.snoc w a : Fin (n + 2) → Fin N) i)) =
        (∏ i, jimboWeight q (w i)) * jimboWeight q a := by
    rw [Fin.prod_univ_castSucc]
    simp
  simp only [hweight]
  rw [jimboWeightedTrace_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro w _
  ring

end TauCeti.KnotTheory
