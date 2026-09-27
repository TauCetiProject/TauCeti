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

Let `R` be a ring Henselian at an ideal `I`, and `S` a finite free `R`-algebra containing a unit
`w` whose trace is a unit of `R`. Then every unit `v` of `R` that is a norm modulo `I` is a norm:
if `N_{S/R}(a) ≡ v (mod I)` then `N_{S/R}(y) = v` for some `y ≡ a` (mod `IS`).

So a norm equation over `R` with a unit right-hand side is solvable as soon as it is solvable
modulo `I`, with a solution as close to the approximate one as the approximation was good. At the
maximal ideal of a Henselian local ring this makes the norm surjective on units in an unramified
extension of local fields, where the residue norm is surjective and the residue trace is nonzero.
At a power `𝔪 ^ i` of the maximal ideal of a complete local ring, applied to the approximate
solution `a = 1`, it makes the norm surjective on the depth-`i` step of the unit filtration.

## Main results

* `TauCeti.Algebra.exists_norm_eq_of_norm_sub_mem`: a unit that is a norm modulo `I` is the norm
  of an element congruent to the approximate solution modulo `IS`.

## References

* J.-P. Serre, *Local Fields*, Chapter V, §2.
-/

public section

open IsLocalRing Polynomial

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S] [Module.Finite R S]

/-- **Hensel's lemma for the norm.** Let `S` be a finite free algebra over a ring `R` Henselian at
an ideal `I`, containing a unit `w` whose trace is a unit. If a unit `v` of `R` is congruent to the
norm of `a` modulo `I`, then `v` is the norm of some `y` congruent to `a` modulo `IS`. -/
theorem Algebra.exists_norm_eq_of_norm_sub_mem {I : Ideal R} [HenselianRing R I] {w : S}
    (hw : IsUnit w) (htr : IsUnit (Algebra.trace R S w)) {a : S} {v : R} (hv : IsUnit v)
    (hav : Algebra.norm R a - v ∈ I) :
    ∃ y : S, Algebra.norm R y = v ∧ y - a ∈ I.map (algebraMap R S) := by
  -- We look for `y` on the line `t ↦ a (1 - t w)`. Along it the norm is `N(a) · det (1 - t M)`,
  -- where `M` is the matrix of multiplication by `w`, and `det (1 - X M)` is the reversed
  -- characteristic polynomial of `M`. Because `M` is invertible this is a unit multiple of the
  -- monic characteristic polynomial of `M⁻¹`, its value at `0` is `1` and its derivative at `0`
  -- is `-tr M`, a unit. So `t = 0` is a simple approximate root of `N(a) · det (1 - t M) = v`,
  -- which Hensel's lemma lifts to a root in `I`.
  rcases subsingleton_or_nontrivial R with _ | _
  · exact ⟨a, Subsingleton.elim _ _, by simp⟩
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
  -- `N(a)` is a unit: it differs from the unit `v` by an element of `I`, which lies in the
  -- Jacobson radical.
  obtain ⟨ν, hν⟩ : IsUnit (Algebra.norm R a) := by
    obtain ⟨u, rfl⟩ := hv
    have h : Algebra.norm R a = u * (↑u⁻¹ * (Algebra.norm R a - u) + 1) := by
      rw [mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]
    rw [h]
    refine u.isUnit.mul (Ideal.isUnit_of_sub_one_mem_jacobson_bot _ ?_)
    rw [add_sub_cancel_right]
    exact HenselianRing.jac (I.mul_mem_left _ hav)
  -- Solve the monic equation `Q(t) = κ v N(a)⁻¹` by Hensel's lemma at the approximate root `0`.
  let f := Q - C (κ * (v * (ν⁻¹ : Rˣ)))
  have hf : f.Monic := (Matrix.charpoly_monic _).sub_of_left <| degree_C_le.trans_lt <| by
    rw [Matrix.charpoly_degree_eq_dim]
    refine WithBot.coe_pos.2 (Fintype.card_pos_iff.2 ?_)
    -- The basis is nonempty, since the trace of `w` is a unit.
    rcases isEmpty_or_nonempty (Module.Free.ChooseBasisIndex R S) with h | h
    · simp [htrM, Matrix.trace] at htr
    · exact h
  obtain ⟨t, ht, htI⟩ := HenselianRing.is_henselian f hf 0
    (by
      have : f.eval 0 = κ * (ν⁻¹ : Rˣ) * (Algebra.norm R a - v) := by
        simp only [f, eval_sub, eval_C, hQ0, ← hν]
        linear_combination (-(κ : R)) * ν.inv_mul
      rw [this]
      exact Ideal.mul_mem_left _ _ hav)
    (by
      simp only [f, derivative_sub, derivative_C, sub_zero, ← coeff_zero_eq_eval_zero,
        coeff_derivative, zero_add, Nat.cast_zero, mul_one, hQ1]
      exact (κ.isUnit.mul (htrM ▸ htr).neg).map (Ideal.Quotient.mk I))
  refine ⟨a * (1 - t • w), ?_, ?_⟩
  · have hroot : κ * Algebra.norm R (1 - t • w) = κ * (v * (ν⁻¹ : Rˣ)) := by
      rw [← hPeval, ← eval_C_mul (a := (κ : R)), ← hQP]
      simpa [f, sub_eq_zero] using ht
    rw [map_mul, κ.mul_right_inj.1 hroot, ← hν, mul_comm, Units.inv_mul_cancel_right]
  · have ht' : t ∈ I := by simpa using htI
    rw [mul_sub, mul_one, sub_sub_cancel_left, Algebra.smul_def]
    exact neg_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ ht')))

end TauCeti
