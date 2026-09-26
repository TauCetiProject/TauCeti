/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.RingTheory.Trace.Defs
import Mathlib.RingTheory.MatrixPolynomialAlgebra

/-!
# Hensel's lemma for the norm

Let `R` be a Henselian local ring with maximal ideal `𝔪` and `S` a finite free `R`-algebra
containing a unit `w` whose trace is a unit of `R`. Then every unit `v` of `R` that is a norm
modulo `𝔪` is a norm: if `N_{S/R}(a) ≡ v (mod 𝔪)` then `N_{S/R}(y) = v` for some `y ≡ a`
(mod `𝔪S`).

So a norm equation over `R` with a unit right-hand side is solvable as soon as it is solvable
modulo `𝔪`. This is the step that makes the norm surjective on units in an unramified extension
of local fields, where the residue norm is surjective and the residue trace is nonzero.

## Main results

* `TauCeti.Algebra.exists_norm_eq_of_norm_sub_mem_maximalIdeal`: a unit that is a norm modulo
  `𝔪` is a norm.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti

variable {R S : Type*} [CommRing R] [HenselianLocalRing R] [CommRing S] [Algebra R S]
  [Module.Free R S] [Module.Finite R S]

/-- **Hensel's lemma for the norm.** Let `S` be a finite free algebra over a Henselian local ring
`R`, containing a unit `w` whose trace is a unit. If a unit `v` of `R` is congruent to the norm of
`a` modulo the maximal ideal, then `v` is the norm of some `y` congruent to `a` modulo `𝔪S`. -/
theorem Algebra.exists_norm_eq_of_norm_sub_mem_maximalIdeal {w : S} (hw : IsUnit w)
    (htr : IsUnit (Algebra.trace R S w)) {a : S} {v : R} (hv : IsUnit v)
    (hav : Algebra.norm R a - v ∈ maximalIdeal R) :
    ∃ y : S, Algebra.norm R y = v ∧ y - a ∈ (maximalIdeal R).map (algebraMap R S) := by
  -- We look for `y` on the line `t ↦ a (1 - t w)`. Along it the norm is `N(a) · det (1 - t M)`,
  -- where `M` is the matrix of multiplication by `w`, and `det (1 - X M)` is the reversed
  -- characteristic polynomial of `M`. Because `M` is invertible this is a unit multiple of the
  -- monic characteristic polynomial of `M⁻¹`, its value at `0` is `1` and its derivative at `0`
  -- is `-tr M`, a unit. So `t = 0` is a simple approximate root of `N(a) · det (1 - t M) = v`,
  -- which Hensel's lemma lifts to a root in `𝔪`.
  classical
  let b := Module.Free.chooseBasis R S
  let n := Fintype.card (Module.Free.ChooseBasisIndex R S)
  -- `M` is the matrix of multiplication by `w`; along the line `t ↦ 1 - t w` the norm is the
  -- reversed characteristic polynomial `P = det (1 - X M)` of `M`.
  let M := Algebra.leftMulMatrix b w
  have hM : IsUnit M := hw.map (Algebra.leftMulMatrix b)
  have htrM : Algebra.trace R S w = M.trace := Algebra.trace_eq_matrix_trace b w
  have hPeval (t : R) : M.charpolyRev.eval t = Algebra.norm R (1 - t • w) := by
    rw [Algebra.norm_eq_matrix_det b, map_sub, map_one, map_smul, Matrix.charpolyRev,
      ← coe_evalRingHom, RingHom.map_det]
    congr 1
    ext i j
    by_cases hij : i = j <;> simp [hij, M] <;> ring
  -- Since `M` is invertible, `Q = charpoly (M⁻¹)` is the unit `κ = (-1)ⁿ (det M)⁻¹` times `P`,
  -- so `Q` is a monic polynomial with `Q(0) = κ` and `Q'(0) = -κ tr M`.
  obtain ⟨κ, hκ⟩ : IsUnit ((-1) ^ n * Ring.inverse M.det) :=
    (isUnit_neg_one.pow n).mul (isUnit_ringInverse.2 ((Matrix.isUnit_iff_isUnit_det M).1 hM))
  set Q := M⁻¹.charpoly with hQ
  have hQP : Q = C (κ : R) * M.charpolyRev := by
    rw [hQ, Matrix.charpoly_inv M hM, hκ]
    simp [n]
  have hQ0 : Q.eval 0 = κ := by rw [hQP, eval_mul, eval_C, Matrix.eval_charpolyRev, mul_one]
  have hQ1 : Q.coeff 1 = κ * -M.trace := by
    rw [hQP, coeff_C_mul, Matrix.coeff_charpolyRev_eq_neg_trace]
  obtain ⟨ν, hν⟩ : IsUnit (Algebra.norm R a) := by
    by_contra h
    have := Ideal.sub_mem _ ((mem_maximalIdeal _).2 h) hav
    rw [sub_sub_cancel] at this
    exact notMem_maximalIdeal.2 hv this
  -- Solve the monic equation `Q(t) = κ v N(a)⁻¹` by Hensel's lemma at the approximate root `0`.
  let f := Q - C (κ * (v * (ν⁻¹ : Rˣ)))
  have hf : f.Monic := (Matrix.charpoly_monic _).sub_of_left <| degree_C_le.trans_lt <| by
    rw [Matrix.charpoly_degree_eq_dim]
    refine WithBot.coe_pos.2 (Fintype.card_pos_iff.2 ?_)
    -- The basis is nonempty, since the trace of `w` is a unit.
    rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex R S) with h | h
    · simp [htrM, Matrix.trace] at htr
    · exact h
  obtain ⟨t, ht, ht𝔪⟩ := HenselianLocalRing.is_henselian f hf 0
    (by
      have : f.eval 0 = κ * (ν⁻¹ : Rˣ) * (Algebra.norm R a - v) := by
        simp only [f, eval_sub, eval_C, hQ0, ← hν]
        linear_combination (-(κ : R)) * ν.inv_mul
      rw [this]
      exact Ideal.mul_mem_left _ _ hav)
    (by
      simp only [f, derivative_sub, derivative_C, sub_zero, ← coeff_zero_eq_eval_zero,
        coeff_derivative, zero_add, Nat.cast_zero, mul_one, hQ1]
      exact κ.isUnit.mul (htrM ▸ htr).neg)
  refine ⟨a * (1 - t • w), ?_, ?_⟩
  · have hroot : κ * Algebra.norm R (1 - t • w) = κ * (v * (ν⁻¹ : Rˣ)) := by
      rw [← hPeval, ← eval_C_mul (a := (κ : R)), ← hQP]
      simpa [f, sub_eq_zero] using ht
    rw [map_mul, κ.mul_right_inj.1 hroot, ← hν, mul_comm, Units.inv_mul_cancel_right]
  · have ht' : t ∈ maximalIdeal R := by simpa using ht𝔪
    rw [mul_sub, mul_one, sub_sub_cancel_left, Algebra.smul_def]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ht')))

end TauCeti
