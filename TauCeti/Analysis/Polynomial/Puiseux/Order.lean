/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.GenericLine
public import TauCeti.Analysis.Analytic.Order

/-!
# Ambient order from Puiseux root contacts

If a plane polynomial splits after `y = a 0 + t ^ N` into analytic roots `r i t`, with
a nonvanishing analytic leading factor, its ambient order at a specified point is computed
by their contact orders with the second coordinate of that point:

`N * order(p, a) = ∑ i, min N (analyticOrderAt (r i · - a 1) 0)`.

The formula includes repeated roots and branches identically zero. It differs from
the multiplicity in the vertical fiber: for `z² - y`, the fiber has multiplicity two
at zero but the ambient order is one. Generic lines avoid cancellation at roots
whose contact order equals the ramification exponent. This is the transverse-slice
calculation used to recover ambient order on root sections from ramified splittings.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Filter Topology MvPolynomial

namespace MvPolynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [Fintype ι]

/-- An analytic Puiseux splitting computes the ambient order of a plane polynomial
from the contact orders of all root labels with the second coordinate of the point.
The leading factor is a unit; root labels may repeat or vanish identically. -/
theorem orderAt_mul_eq_sum_min_of_puiseux (p : MvPolynomial (Fin 2) 𝕜) (a : Fin 2 → 𝕜)
    {N : ℕ} (hN : 0 < N) {r : ι → 𝕜 → 𝕜} {u : 𝕜 → 𝕜}
    (hr : ∀ i, AnalyticAt 𝕜 (r i) 0) (hu : AnalyticAt 𝕜 u 0) (hu0 : u 0 ≠ 0)
    (hsplit : ∀ᶠ t in 𝓝 (0 : 𝕜), ∀ z : 𝕜,
      eval ![a 0 + t ^ N, z] p = u t * ∏ i, (z - r i t)) :
    p.orderAt a * N = ∑ i, min (N : ℕ∞) (analyticOrderAt (fun t ↦ r i t - a 1) 0) := by
  classical
  have hp : p ≠ 0 := by
    obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset
      (Finset.univ.image fun i ↦ r i 0)
    have hprod : ∏ i, (z - r i 0) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ by
      apply sub_ne_zero.2
      intro heq
      exact hz (Finset.mem_image.2 ⟨i, Finset.mem_univ _, heq.symm⟩)
    intro hp
    have := hsplit.self_of_nhds z
    simp only [hp, map_zero, zero_pow hN.ne'] at this
    exact mul_ne_zero hu0 hprod this.symm
  choose b hb using fun i ↦
    ((hr i).sub analyticAt_const).exists_analyticOrderAt_monomial_sub_eq_min N
  obtain ⟨c, hc, horder⟩ := p.exists_analyticOrderAt_eval_finTwo_eq hp a
    (insert 0 (Finset.univ.image b))
  have hc0 : c ≠ 0 := fun h ↦ hc (by simp [h])
  have hcb (i : ι) : c ≠ b i := fun h ↦ hc (by simp [h])
  have hline : AnalyticAt 𝕜 (fun t : 𝕜 ↦ eval ![a 0 + t, a 1 + c * t] p) 0 := by
    have hcoord (i : Fin 2) : AnalyticAt 𝕜 (fun t : 𝕜 ↦ ![a 0 + t, a 1 + c * t] i) 0 := by
      fin_cases i
      · exact analyticAt_const.add analyticAt_id
      · exact analyticAt_const.add (analyticAt_const.mul analyticAt_id)
    simpa only [aeval_eq_eval] using AnalyticAt.aeval_mvPolynomial hcoord p
  have hram := TauCeti.analyticOrderAt_comp_pow_zero hline hN
  have hfactor : analyticOrderAt (fun t : 𝕜 ↦ eval ![a 0 + t ^ N, a 1 + c * t ^ N] p) 0 =
      ∑ i, min (N : ℕ∞) (analyticOrderAt (fun t ↦ r i t - a 1) 0) := by
    have heq : (fun t : 𝕜 ↦ eval ![a 0 + t ^ N, a 1 + c * t ^ N] p) =ᶠ[𝓝 0]
        (fun t ↦ u t * ∏ i, (c * t ^ N - (r i t - a 1))) :=
      hsplit.mono fun t ht ↦ by
        simpa only [sub_sub_eq_add_sub, add_comm] using ht (a 1 + c * t ^ N)
    have hprodA : AnalyticAt 𝕜 (fun t : 𝕜 ↦ ∏ i, (c * t ^ N - (r i t - a 1))) 0 := by
      simpa only [Finset.prod_fn, Pi.sub_def, Pi.mul_def, Pi.pow_def, id_eq] using
        Finset.analyticAt_prod Finset.univ (fun i _ ↦
          (analyticAt_const.mul (analyticAt_id.pow N)).sub ((hr i).sub analyticAt_const))
    have hmul := analyticOrderAt_mul hu hprodA
    simp only [Pi.mul_def] at hmul
    rw [analyticOrderAt_congr heq, hmul, hu.analyticOrderAt_eq_zero.2 hu0, zero_add]
    have hprod := TauCeti.analyticOrderAt_prod
      (s := Finset.univ) (F := fun i t ↦ c * t ^ N - (r i t - a 1))
      (fun i _ ↦ (analyticAt_const.mul (analyticAt_id.pow N)).sub ((hr i).sub analyticAt_const))
    simp only [Finset.prod_fn] at hprod
    rw [hprod]
    exact Finset.sum_congr rfl fun i _ ↦ hb i c hc0 (hcb i)
  rw [horder] at hram
  exact hram.symm.trans hfactor

end MvPolynomial
