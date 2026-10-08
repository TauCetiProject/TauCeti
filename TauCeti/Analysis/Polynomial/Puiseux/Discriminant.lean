/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.MvPolynomial.Complexification
public import TauCeti.Analysis.Polynomial.Puiseux.Monic
import Mathlib.Analysis.Convex.Contractible

/-!
# Ramified splittings from constant real discriminant order

A monic polynomial with real polynomial coefficients, restricted along a real analytic
parametrization, admits a local analytic complex splitting after a ramified transverse
substitution when its discriminant has constant finite ambient order along the parametrization.
The complexification, transverse direction, branches and discriminant unit are constructed
from the real data. Neither a prepared discriminant nor a splitting is assumed.

The branches retain repeated labels on the exceptional hyperplane. Their restrictions there
give complex roots, even when the central fiber has multiple roots. The real branches are
subsequently selected to construct real root sections in
`TauCeti.Geometry.RealAlgebraic.Stack.Discriminant`. This result does not assert constancy of
the ambient order of the original polynomial on those sections.

## References

* S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
  in *Quantifier Elimination and Cylindrical Algebraic Decomposition*, Springer (1998).
* S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
  construction*, Journal of Symbolic Computation 92 (2019), Section 4.
-/

public section

open Filter Function Metric Polynomial Set Topology

namespace TauCeti

variable {σ ι : Type*} [Fintype σ] [Fintype ι]

/-- Constant finite ambient order of the formal discriminant along a real analytic
parametrization produces a complex analytic splitting after a transverse power substitution.
The ramification exponent is the factorial of the formal degree. The constructed discriminant
unit is nonzero at the center; root labels may collide on the exceptional hyperplane. -/
theorem _root_.Polynomial.exists_analyticAt_prod_X_sub_C_of_orderAt_discr_eq
    (p : Polynomial (MvPolynomial σ ℝ)) (hp : p.Monic)
    {φ : (ι → ℝ) → σ → ℝ} {a : ι → ℝ} {m : ℕ}
    (hφ : AnalyticAt ℝ φ a) (hm : ∀ᶠ x in 𝓝 a, p.discr.orderAt (φ x) = m) :
    ∃ Φ : (ι → ℂ) → σ → ℂ, ∃ v : σ → ℝ,
      ∃ r : Fin p.natDegree → (ι → ℂ) × ℂ → ℂ, ∃ u : (ι → ℂ) × ℂ → ℂ,
        AnalyticAt ℂ Φ (fun j ↦ (a j : ℂ)) ∧
        (∀ᶠ x in 𝓝 a, Φ (fun j ↦ (x j : ℂ)) = fun i ↦ (φ x i : ℂ)) ∧
        (∀ i, AnalyticAt ℂ (r i) ((fun j ↦ (a j : ℂ)), 0)) ∧
        AnalyticAt ℂ u ((fun j ↦ (a j : ℂ)), 0) ∧
        u ((fun j ↦ (a j : ℂ)), 0) ≠ 0 ∧
        ∀ᶠ z in 𝓝 ((fun j ↦ (a j : ℂ)), (0 : ℂ)),
          p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
            (Φ z.1 + z.2 ^ p.natDegree.factorial • (fun i ↦ (v i : ℂ)))) =
              ∏ i, (X - C (r i z)) ∧
          (p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
            (Φ z.1 + z.2 ^ p.natDegree.factorial • (fun i ↦ (v i : ℂ))))).discr =
              z.2 ^ (p.natDegree.factorial * m) * u z := by
  -- Prepare the discriminant on one complex polydisc directly from its real ambient order.
  obtain ⟨ρ₀, hρ₀, Φ, V, -, hV, hΦ₀, hreal₀, -, hdir⟩ :=
    p.discr.exists_complexification_dense_open_directions_eval_add_smul_eq_pow_mul hφ hm
  obtain ⟨v, hv⟩ := hV.nonempty
  obtain ⟨ρ, hρ, hρle, u, hu, hunit⟩ := hdir v hv
  have hΦ := hΦ₀.mono (ball_subset_ball hρle)
  have hreal := fun x hx ↦ hreal₀ x (ball_subset_ball hρle hx)
  let ac : ι → ℂ := fun j ↦ (a j : ℂ)
  let U := ball ac ρ
  let F : (ι → ℂ) × ℂ → ℂ[X] := fun z ↦
    p.map (MvPolynomial.eval₂Hom Complex.ofRealHom
      (Φ z.1 + z.2 • (fun i ↦ (v i : ℂ))))
  have hU : IsOpen U := isOpen_ball
  have hac : ac ∈ U := mem_ball_self hρ
  let : ContractibleSpace U := (convex_ball ac ρ).contractibleSpace ⟨ac, hac⟩
  let : SimplyConnectedSpace U := SimplyConnectedSpace.ofContractible U
  have hcoeff (i : ℕ) : AnalyticOnNhd ℂ (fun z ↦ (F z).coeff i) (U ×ˢ ball 0 ρ) := by
    intro z hz
    have hcoord (j : σ) : AnalyticAt ℂ
        (fun z : (ι → ℂ) × ℂ ↦ (Φ z.1 + z.2 • (fun i ↦ (v i : ℂ))) j) z := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact ((analyticAt_pi_iff.1 (hΦ z.1 hz.1) j).comp analyticAt_fst).add
        (analyticAt_snd.mul analyticAt_const)
    simpa only [F, coeff_map, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq_eval_map,
      MvPolynomial.aeval_eq_eval] using
      AnalyticAt.aeval_mvPolynomial hcoord ((p.coeff i).map Complex.ofRealHom)
  have hmonic (z) : (F z).Monic := hp.map _
  have hdeg (z) : (F z).natDegree = p.natDegree := hp.natDegree_map _
  have hdiscr (z) (hz : z ∈ U ×ˢ ball 0 ρ) : (F z).discr = z.2 ^ m * u z := by
    rw [hp.discr_map]
    simpa only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval_map] using (hunit z hz).2
  -- Monicity keeps the formal degree unchanged throughout the transverse family.
  obtain ⟨R, hR, hfit, r, hr, hsplit, -, -⟩ :=
    Polynomial.exists_analyticOnNhd_prod_X_sub_C_of_discr_eq_pow_mul hU hρ
      (fun i _ ↦ hcoeff i) (fun z _ ↦ hmonic z) (fun z _ ↦ hdeg z)
      hu (fun z hz ↦ (hunit z hz).1) hdiscr
  let Q : (ι → ℂ) × ℂ → (ι → ℂ) × ℂ := fun z ↦ (z.1, z.2 ^ p.natDegree.factorial)
  have hQ : AnalyticAt ℂ Q (ac, 0) := analyticAt_fst.prod (analyticAt_snd.pow _)
  have hzero : Q (ac, 0) = (ac, 0) := by simp [Q, p.natDegree.factorial_ne_zero]
  have hQmem (z) (hz : z ∈ U ×ˢ ball 0 R) : Q z ∈ U ×ˢ ball 0 ρ := by
    refine ⟨hz.1, ?_⟩
    rw [mem_ball_zero_iff, norm_pow]
    exact (pow_lt_pow_left₀ (mem_ball_zero_iff.1 hz.2) (norm_nonneg _)
      p.natDegree.factorial_ne_zero).trans_le hfit
  refine ⟨Φ, v, r, fun z ↦ u (Q z), hΦ ac hac,
    Filter.Eventually.mono (ball_mem_nhds a hρ) hreal,
    fun i ↦ hr i (ac, 0) ⟨hac, mem_ball_self hR⟩,
    (hu (ac, 0) ⟨hac, mem_ball_self hρ⟩).comp_of_eq hQ hzero,
    by simpa only [ac, Q, zero_pow p.natDegree.factorial_ne_zero] using
      (hunit (ac, 0) ⟨hac, mem_ball_self hρ⟩).1, ?_⟩
  filter_upwards [(hU.prod isOpen_ball).mem_nhds ⟨hac, mem_ball_self hR⟩] with z hz
  exact ⟨hsplit z hz, by simpa only [Q, ← pow_mul] using hdiscr (Q z) (hQmem z hz)⟩

end TauCeti
