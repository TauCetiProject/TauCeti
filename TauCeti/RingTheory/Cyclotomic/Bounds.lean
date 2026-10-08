/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Cyclotomic.Basic

/-!
# Coefficient bounds for sums of roots of unity

`Cyclotomic.rootCoeffBound e` is the largest absolute power-basis coefficient of any of
`1, ζ, …, ζ^(e-1)` in the exact coefficient-vector ring. It is computable from the cyclotomic
polynomial, and bounds each coefficient of a sum of `n` such roots by `n * rootCoeffBound e`.
This converts the eigenvalue description of a character into a quantitative bound suitable for
reconstruction from modular residues. Reduction modulo the cyclotomic polynomial can increase
coefficients, so the bound retains this dependence on the exponent.

The coefficient maps reuse Mathlib's linear remainder map `AdjoinRoot.modByMonicHom`.
-/

public section

namespace TauCeti.Cyclotomic

variable {e : ℕ}

/-- The maximum absolute coefficient of the `e` powers of the distinguished root of unity,
computed in the canonical power basis. -/
def rootCoeffBound (e : ℕ) : ℕ :=
  (Finset.range e).sup fun k ↦
    (Finset.range e.totient).sup fun j ↦ ((zeta e ^ k).coeff j).natAbs

/-- The defining finite maximum for the root coefficient bound. -/
theorem rootCoeffBound_def (e : ℕ) : rootCoeffBound e =
    (Finset.range e).sup (fun k ↦
      (Finset.range e.totient).sup fun j ↦ ((zeta e ^ k).coeff j).natAbs) := (rfl)

/-- Every coefficient of a power with exponent below `e` satisfies the root coefficient bound. -/
theorem coeff_pow_natAbs_le_rootCoeffBound {k : ℕ} (hk : k < e) (j : ℕ) :
    ((zeta e ^ k).coeff j).natAbs ≤ rootCoeffBound e := by
  by_cases hj : j < e.totient
  · exact (Finset.le_sup (f := fun j ↦ ((zeta e ^ k).coeff j).natAbs)
      (Finset.mem_range.mpr hj)).trans
        (Finset.le_sup (f := fun k ↦ (Finset.range e.totient).sup
          fun j ↦ ((zeta e ^ k).coeff j).natAbs) (Finset.mem_range.mpr hk))
  · simp [coeff_eq_zero_of_totient_le _ (Nat.le_of_not_gt hj)]

/-- A sum of `e`-th roots of unity has an exact cyclotomic representative whose coefficients
are bounded by the number of summands times `rootCoeffBound e`. Multiplicities are retained. -/
theorem exists_complexEmbedding_eq_sum_and_coeff_natAbs_le [NeZero e] (s : Multiset ℂ)
    (hs : ∀ μ ∈ s, μ ^ e = 1) :
    ∃ x : Cyclotomic e, complexEmbedding x = s.sum ∧
      ∀ j, (x.coeff j).natAbs ≤ s.card * rootCoeffBound e := by
  induction s using Multiset.induction_on with
  | empty => exact ⟨0, by simp, fun j ↦ by simp⟩
  | @cons μ s ih =>
    obtain ⟨k, hk, hμ⟩ := isPrimitiveRoot_complexRoot.eq_pow_of_pow_eq_one
      (hs μ (Multiset.mem_cons_self _ _))
    obtain ⟨x, hx, hbound⟩ := ih fun ν hν ↦ hs ν (Multiset.mem_cons_of_mem hν)
    refine ⟨zeta e ^ k + x, ?_, fun j ↦ ?_⟩
    · simp [complexEmbedding_zeta, hμ, hx]
    · rw [coeff_add]
      calc
        _ ≤ ((zeta e ^ k).coeff j).natAbs + (x.coeff j).natAbs := Int.natAbs_add_le _ _
        _ ≤ rootCoeffBound e + s.card * rootCoeffBound e :=
          Nat.add_le_add (coeff_pow_natAbs_le_rootCoeffBound hk j) (hbound j)
        _ = (μ ::ₘ s).card * rootCoeffBound e := by simp [Nat.add_mul, Nat.add_comm]

end TauCeti.Cyclotomic
