/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping
public import TauCeti.Geometry.Symplectic.Floer.Pullback
public import TauCeti.Analysis.Complex.ThricePuncturedSphere.Exchange
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import Mathlib.MeasureTheory.Group.LIntegral

/-!
# The input-exchange family of pair-of-pants perturbation data

Graded commutativity of the pair-of-pants product compares the product of `a` and `b` with the
product of `b` and `a`. Geometrically the comparison is the holomorphic involution
`σ(w) = 1 - w` of the thrice-punctured sphere `S = ℂ ∖ {0, 1}`, which exchanges the two input
punctures and fixes the output puncture `∞`. If `u` solves the Floer equation for the
pair-of-pants datum `K'` whose input Hamiltonians are exchanged, then `u ∘ σ` solves it for the
pulled-back datum `σ^*K'` and the pulled-back almost complex structures. On the input ends this
pullback is the original pair-of-pants datum `K = TauCeti.Floer.pairOfPantsPerturbation H`,
because `σ` exchanges the end lifts of `0` and `1` exactly. On the output end it is not: the end
lift `φ_∞(z) = 2 exp (-2πz)` is centred at `0`, and `σ` carries it to the end lift centred at `1`,
rotated by half a period. Graded commutativity therefore needs a one-parameter family of
perturbation data joining `K` to `σ^*K'` whose output end moves from the centre `0` to the
centre `1`.

This file constructs that family. For `c ∈ ℝ` the datum
`TauCeti.Floer.exchangePerturbation H c` is the input part of the pair-of-pants datum (its
Hamiltonians on the ends at `0` and `1`) plus the negative plane datum of the output
Hamiltonian `H_∞` (`TauCeti.Floer.negativePlanePerturbation`) translated by `c`. Thus its output
end has the end lift `z ↦ c + φ_∞(z)`, whose asymptotic marker points in the same direction for
every `c`. The output Hamiltonian of the exchanged datum is rotated by half a period,
`H'_∞(t) = H_∞(t + 1/2)` (`TauCeti.Floer.exchangeHamiltonians`), which matches the half-period
rotation of the end at `∞` under `σ`. The main results are:

* `TauCeti.Floer.exchangePerturbation_zero`: at `c = 0` the family is the pair-of-pants datum.
* `TauCeti.Floer.exchangePerturbation_one`: at `c = 1` it is the pullback along `σ` of the
  pair-of-pants datum with exchanged inputs, `σ^*K'(w) = -K'(1 - w)`, since `dσ = -1`;
  `TauCeti.Floer.perturbationPullback_pairOfPantsPerturbation_exchangeHamiltonians` states this
  for the components in real coordinates, the form used by
  `TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_perturbationPullback`.
* `TauCeti.Floer.exchangePerturbation_cylindricalEndLift` and
  `TauCeti.Floer.exchangePerturbation_add_cylindricalEndLift_inf`: for `0 ≤ c ≤ 1` every member
  is `H_q(t) dt` far out on the input end `q`, in the end lift `φ_q`, and `H_∞(t) dt` far out on
  the output end, in the end lift `c + φ_∞`.
* `TauCeti.Floer.contMDiffAt_exchangePerturbation`: the family is jointly smooth in the parameter
  `c`, the domain point of `S` and the target point.
* `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_exchangePerturbation_le`: for
  Hamiltonians on a manifold with a smooth two-form, such as a closed symplectic manifold, the
  integrated curvature `∫ |R_K|` of every member with `0 ≤ c ≤ 1` is at most `B₀ + B₁ + B_∞`
  along any map, where `|H_q| ≤ B_q`; the bound does not depend on `c`. The symplectic vector
  space case (`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_exchangePerturbation_le`)
  is the case of the constant form `TauCeti.SymplecticForm.constSmooth`.

The input part is supported in two small discs about `0` and `1`, and the translated plane datum
vanishes on the disc of radius `2 exp (2π)` about `c`, so for `0 ≤ c ≤ 1` the two parts have
disjoint supports and the curvature splits into the curvatures of the two parts.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the graded commutativity of the pair-of-pants product.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on
  perturbation data on punctured surfaces whose ends are related by automorphisms.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*} {H : Puncture → ℝ → M → ℝ}

/-! ### The exchanged Hamiltonians -/

/-- The end Hamiltonians of the pair of pants with exchanged inputs: the Hamiltonian of the end at
`0` is `H₁`, that of the end at `1` is `H₀`, and the output Hamiltonian is rotated by half a
period, `t ↦ H_∞(t + 1/2)`, matching the half-period rotation of the end at `∞` under
`w ↦ 1 - w`. -/
def exchangeHamiltonians (H : Puncture → ℝ → M → ℝ) : Puncture → ℝ → M → ℝ
  | .zero => H one
  | .one => H zero
  | .inf => fun t => H inf (t + 1 / 2)

@[simp]
theorem exchangeHamiltonians_zero (H : Puncture → ℝ → M → ℝ) :
    exchangeHamiltonians H zero = H one :=
  (rfl)

@[simp]
theorem exchangeHamiltonians_one (H : Puncture → ℝ → M → ℝ) :
    exchangeHamiltonians H one = H zero :=
  (rfl)

@[simp]
theorem exchangeHamiltonians_inf (H : Puncture → ℝ → M → ℝ) :
    exchangeHamiltonians H inf = fun t => H inf (t + 1 / 2) :=
  (rfl)

/-- The exchanged Hamiltonians of period-one Hamiltonians have period one. -/
theorem periodic_exchangeHamiltonians (hH : ∀ q, Periodic (H q) 1) (q : Puncture) :
    Periodic (exchangeHamiltonians H q) 1 := by
  cases q
  · simpa using hH one
  · simpa using hH zero
  · simpa using (hH inf).add_const (1 / 2)

/-! ### The family -/

/-- **The input-exchange family of perturbation data.** For `c ∈ ℝ` this is the input part of the
pair-of-pants datum of `H`, given by its Hamiltonians on the ends at `0` and `1`, plus the
negative plane datum of the output Hamiltonian `H_∞` translated by `c`. Its output end is
therefore the end at `∞` recentred at `c`, with end lift `z ↦ c + 2 exp (-2πz)`. At `c = 0` it
is the pair-of-pants datum (`TauCeti.Floer.exchangePerturbation_zero`), and at `c = 1` it is the
pullback of the pair-of-pants datum with exchanged inputs along `w ↦ 1 - w`
(`TauCeti.Floer.exchangePerturbation_one`). -/
def exchangePerturbation (H : Puncture → ℝ → M → ℝ) (c : ℝ) (w : ℂ) (x : M) : ℂ →L[ℝ] ℝ :=
  pairOfPantsPerturbation (update H inf 0) w x + negativePlanePerturbation (H inf) (w - c) x

theorem exchangePerturbation_def (H : Puncture → ℝ → M → ℝ) (c : ℝ) (w : ℂ) (x : M) :
    exchangePerturbation H c w x =
      pairOfPantsPerturbation (update H inf 0) w x + negativePlanePerturbation (H inf) (w - c) x :=
  (rfl)

/-- **The start of the family is the pair-of-pants datum.** -/
@[simp]
theorem exchangePerturbation_zero (H : Puncture → ℝ → M → ℝ) :
    exchangePerturbation H 0 = pairOfPantsPerturbation H := by
  funext w x
  simp [exchangePerturbation_def,
    ← pairOfPantsPerturbation_eq_update_inf_add_negativePlanePerturbation]

/-- The input part of the pair-of-pants datum is exchanged by `w ↦ 1 - w`: since `dσ = -1`, the
pullback of the input part with exchanged Hamiltonians is the input part. -/
private theorem pairOfPantsPerturbation_update_exchangeHamiltonians_one_sub (w : ℂ) (x : M) :
    pairOfPantsPerturbation (update (exchangeHamiltonians H) inf 0) (1 - w) x =
      -pairOfPantsPerturbation (update H inf 0) w x := by
  simp [pairOfPantsPerturbation_def, Puncture.sum_univ, endCoord_zero_one_sub,
    endCoord_one_one_sub, endAngularForm_zero_one_sub, endAngularForm_one_one_sub, add_comm]

/-- **The end of the family is the exchanged pair-of-pants datum.** At `c = 1` the family is the
pullback of the pair-of-pants datum `K'` with exchanged Hamiltonians
(`TauCeti.Floer.exchangeHamiltonians`) along the exchange `σ(w) = 1 - w` of the two inputs. Since
`dσ = -1`, this pullback is `w ↦ -K'(1 - w)`. -/
theorem exchangePerturbation_one (hH : Periodic (H inf) 1) (w : ℂ) (x : M) :
    exchangePerturbation H 1 w x =
      -pairOfPantsPerturbation (exchangeHamiltonians H) (1 - w) x := by
  have hplane := negativePlanePerturbation_neg hH (w - 1) x
  rw [neg_sub] at hplane
  rw [pairOfPantsPerturbation_eq_update_inf_add_negativePlanePerturbation,
    pairOfPantsPerturbation_update_exchangeHamiltonians_one_sub, exchangeHamiltonians_inf,
    hplane, exchangePerturbation_def, Complex.ofReal_one]
  abel

/-- **The end of the family in real coordinates.** In the real coordinates `ℝ × ℝ ≃ ℂ`, the
exchange is `σ(s, t) = (1 - s, -t)`, and the pullback along `σ` of the components of the
pair-of-pants datum with exchanged Hamiltonians (`TauCeti.Floer.perturbationPullback`) is the end
`c = 1` of the family. Since `σ` is holomorphic,
`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_perturbationPullback` turns solutions of
the Floer equation for the exchanged datum, composed with `σ`, into solutions for this end. -/
theorem perturbationPullback_pairOfPantsPerturbation_exchangeHamiltonians
    (hH : Periodic (H inf) 1) (v z : ℝ × ℝ) (x : M) :
    perturbationPullback (fun z => (1, 0) - z)
        (fun z x => pairOfPantsPerturbation (exchangeHamiltonians H)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x => pairOfPantsPerturbation (exchangeHamiltonians H)
          (Complex.equivRealProdCLM.symm z) x Complex.I) v z x =
      exchangePerturbation H 1 (Complex.equivRealProdCLM.symm z) x
        (Complex.equivRealProdCLM.symm v) := by
  have hσ : Complex.equivRealProdCLM.symm ((1, 0) - z) = 1 - Complex.equivRealProdCLM.symm z := by
    apply Complex.ext <;> simp
  have hv : Complex.equivRealProdCLM.symm v = v.1 • (1 : ℂ) + v.2 • Complex.I := by
    apply Complex.ext <;> simp
  rw [perturbationPullback_apply, fderiv_const_sub, fderiv_fun_id, exchangePerturbation_one hH, hσ,
    hv]
  simp only [neg_apply, ContinuousLinearMap.id_apply, Prod.fst_neg, Prod.snd_neg, map_add,
    map_smul, smul_eq_mul]
  ring

/-! ### The ends of the family -/

/-- The real part of the exponent of the end lifts. -/
private theorem re_neg_two_pi_mul (z : ℂ) : (-(2 * (π : ℂ)) * z).re = -(2 * π) * z.re := by
  rw [show -(2 * (π : ℂ)) * z = ((-(2 * π) : ℝ) : ℂ) * z by push_cast; ring,
    Complex.re_ofReal_mul]

/-- Every `c ∈ [0, 1]` lies within distance `1` of `1`. -/
private theorem norm_ofReal_sub_one_le {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) :
    ‖(c : ℂ) - 1‖ ≤ 1 := by
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_of_nonpos (by linarith)]
  linarith

/-- On the part `s > 0` of an input end `q`, the end lift stays within distance `1` of `0` or
`1`, hence within distance `2` of every `c ∈ [0, 1]`. -/
private theorem norm_cylindricalEndLift_sub_le {q : Puncture} (hq : q ≠ inf) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : 0 < z.re) :
    ‖q.cylindricalEndLift z - c‖ ≤ 2 := by
  have hφ : ‖q.cylindricalEndLift z - q.endCenter‖ ≤ 1 := by
    rw [cylindricalEndLift_eq, add_sub_cancel_left, norm_mul, norm_endScale hq,
      Complex.norm_exp]
    have : Real.exp (-(2 * (π : ℂ)) * z).re ≤ 1 := by
      rw [Real.exp_le_one_iff, re_neg_two_pi_mul]
      nlinarith [Real.pi_pos]
    linarith
  have hc : ‖q.endCenter - (c : ℂ)‖ ≤ 1 := by
    rcases q.endCenter_eq_zero_or_eq_one with h | h <;> rw [h]
    · rw [zero_sub, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc₀]
      exact hc₁
    · rw [norm_sub_rev]
      exact norm_ofReal_sub_one_le hc₀ hc₁
  calc ‖q.cylindricalEndLift z - c‖
      = ‖(q.cylindricalEndLift z - q.endCenter) + (q.endCenter - c)‖ := by ring_nf
    _ ≤ 1 + 1 := (norm_add_le _ _).trans (add_le_add hφ hc)
    _ = 2 := by norm_num

/-- The translated plane datum vanishes within distance `2` of `c`. -/
private theorem negativePlanePerturbation_sub_eq_zero {H : ℝ → M → ℝ} {c : ℝ} {w : ℂ}
    (hw : ‖w - c‖ ≤ 2) (x : M) : negativePlanePerturbation H (w - c) x = 0 :=
  negativePlanePerturbation_eq_zero_of_norm_le
    (hw.trans (by nlinarith [Real.one_le_exp (by positivity : 0 ≤ 2 * π)])) x

/-- The input part of the pair-of-pants datum vanishes at distance at least `1/2` from both `0` and
`1`. -/
private theorem pairOfPantsPerturbation_update_inf_eq_zero {w : ℂ} (h₀ : 1 / 2 ≤ ‖w‖)
    (h₁ : 1 / 2 ≤ ‖w - 1‖) (x : M) : pairOfPantsPerturbation (update H inf 0) w x = 0 := by
  -- On each input end the longitudinal coordinate is nonpositive at such points.
  have hre {q : Puncture} (hq : q ≠ inf) : (q.endCoord w).re ≤ 0 := by
    have hn : 1 ≤ ‖(w - q.endCenter) / q.endScale‖ := by
      rw [norm_div, norm_endScale hq, le_div_iff₀ (by norm_num), one_mul]
      rcases q.endCenter_eq_zero_or_eq_one with h | h <;> rw [h]
      · rwa [sub_zero]
      · exact h₁
    rw [re_endCoord, neg_div, neg_nonpos]
    exact div_nonneg (Real.log_nonneg hn) (by positivity)
  have hcut {q : Puncture} (hq : q ≠ inf) :
      smoothTransition ((q.endCoord w).re - 1) = 0 :=
    smoothTransition.zero_of_nonpos (by linarith [hre hq])
  simp [pairOfPantsPerturbation_def, Puncture.sum_univ, hcut (q := zero) (by decide),
    hcut (q := one) (by decide)]

/-- The input part of the pair-of-pants datum vanishes at distance at least `3/2` from a point
`c ∈ [0, 1]`. -/
private theorem pairOfPantsPerturbation_update_inf_eq_zero_of_le_norm_sub {c : ℝ} (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {w : ℂ} (hw : 3 / 2 ≤ ‖w - c‖) (x : M) :
    pairOfPantsPerturbation (update H inf 0) w x = 0 := by
  refine pairOfPantsPerturbation_update_inf_eq_zero ?_ ?_ x
  · have := norm_sub_le w (c : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg hc₀] at this
    linarith
  · have := norm_sub_le (w - 1) ((c : ℂ) - 1)
    rw [sub_sub_sub_cancel_right] at this
    linarith [norm_ofReal_sub_one_le hc₀ hc₁]

/-- **The family on an input end.** For `0 ≤ c ≤ 1`, on the part `s > 0` of an input end `q`, the
pullback of every member of the family along the end lift `φ_q` is the continuation datum
`β(s - 1) H_q(t) dt` of the pair of pants: it sends a tangent vector `v` of the cylinder to
`Im v · β(Re z - 1) H_q(Im z)`. -/
theorem exchangePerturbation_cylindricalEndLift_of_pos {q : Puncture} (hq : q ≠ inf)
    (hH : Periodic (H q) 1) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : 0 < z.re) (x : M)
    (v : ℂ) :
    exchangePerturbation H c (q.cylindricalEndLift z) x (deriv q.cylindricalEndLift z * v) =
      v.im * (smoothTransition (z.re - 1) * H q z.im x) := by
  rw [exchangePerturbation_def, negativePlanePerturbation_sub_eq_zero
    (norm_cylindricalEndLift_sub_le hq hc₀ hc₁ hz), add_zero,
    pairOfPantsPerturbation_cylindricalEndLift_of_pos (by simpa [update_of_ne hq] using hH)
      (by rwa [endSign_eq_one hq, one_mul])]
  simp [update_of_ne hq, endSign_eq_one hq]

/-- **The family is `H_q(t) dt` far out on an input end.** For `0 ≤ c ≤ 1`, on the part `s ≥ 2`
of an input end `q`, the pullback of every member of the family along the end lift `φ_q` sends a
tangent vector `v` of the cylinder to `Im v · H_q(Im z)`. -/
theorem exchangePerturbation_cylindricalEndLift {q : Puncture} (hq : q ≠ inf)
    (hH : Periodic (H q) 1) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : 2 ≤ z.re) (x : M)
    (v : ℂ) :
    exchangePerturbation H c (q.cylindricalEndLift z) x (deriv q.cylindricalEndLift z * v) =
      v.im * H q z.im x := by
  rw [exchangePerturbation_cylindricalEndLift_of_pos hq hH hc₀ hc₁ (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

/-- **The family on the output end.** For `0 ≤ c ≤ 1`, on the part `s < 0` of the output end
recentred at `c`, with end lift `z ↦ c + φ_∞(z)`, the pullback of the member `c` of the family is
the continuation datum `β(-s - 1) H_∞(t) dt`: it sends a tangent vector `v` of the cylinder to
`Im v · β(-Re z - 1) H_∞(Im z)`. -/
theorem exchangePerturbation_add_cylindricalEndLift_inf_of_neg (hH : Periodic (H inf) 1) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : z.re < 0) (x : M) (v : ℂ) :
    exchangePerturbation H c (c + inf.cylindricalEndLift z) x
        (deriv inf.cylindricalEndLift z * v) =
      v.im * (smoothTransition (-z.re - 1) * H inf z.im x) := by
  -- The end lift at `∞` stays at distance more than `2` from `0` on the part `s < 0`.
  have hφ : 2 ≤ ‖inf.cylindricalEndLift z‖ := by
    rw [cylindricalEndLift_inf, norm_mul, Complex.norm_ofNat, Complex.norm_exp]
    have : 1 ≤ Real.exp (-(2 * (π : ℂ)) * z).re := by
      rw [Real.one_le_exp_iff, re_neg_two_pi_mul]
      nlinarith [Real.pi_pos]
    linarith
  have hw : 3 / 2 ≤ ‖(c : ℂ) + inf.cylindricalEndLift z - c‖ := by
    rw [add_sub_cancel_left]
    linarith
  rw [exchangePerturbation_def,
    pairOfPantsPerturbation_update_inf_eq_zero_of_le_norm_sub hc₀ hc₁ hw, zero_add,
    add_sub_cancel_left, negativePlanePerturbation_cylindricalEndLift_of_neg hH hz]

/-- **The family is `H_∞(t) dt` far out on the output end.** For `0 ≤ c ≤ 1`, on the part
`s ≤ -2` of the output end recentred at `c`, the pullback of the member `c` of the family along the
end lift `z ↦ c + φ_∞(z)` sends a tangent vector `v` of the cylinder to `Im v · H_∞(Im z)`. -/
theorem exchangePerturbation_add_cylindricalEndLift_inf (hH : Periodic (H inf) 1) {c : ℝ}
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : z.re ≤ -2) (x : M) (v : ℂ) :
    exchangePerturbation H c (c + inf.cylindricalEndLift z) x
        (deriv inf.cylindricalEndLift z * v) =
      v.im * H inf z.im x := by
  rw [exchangePerturbation_add_cylindricalEndLift_inf_of_neg hH hc₀ hc₁ (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

/-! ### Smoothness of the family -/

/-- The input Hamiltonians, with the output Hamiltonian replaced by zero, inherit any property
shared by the Hamiltonians `H q` and `0`. -/
private theorem forall_update_inf {P : (ℝ → M → ℝ) → Prop} (h₀ : P 0) (hH : ∀ q, P (H q))
    (q : Puncture) : P (update H inf 0 q) := by
  rcases eq_or_ne q inf with rfl | hq
  · simpa using h₀
  · simpa [update_of_ne hq] using hH q

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The family is smooth.** For period-one Hamiltonians of class `C^n` on `ℝ × M`, the family
is `C^n` jointly in the parameter `c ∈ ℝ`, the domain point of the thrice-punctured sphere
`S = ℂ ∖ {0, 1}` and the target point. -/
theorem contMDiffAt_exchangePerturbation {n : ℕ∞} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H q))) (c : ℝ)
    (w : ThricePuncturedSphere) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℝ × (ℂ × M) => exchangePerturbation H p.1 p.2.1 p.2.2) (c, ((w : ℂ), x)) := by
  -- The input part does not depend on the parameter.
  have hin : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℝ × (ℂ × M) => pairOfPantsPerturbation (update H inf 0) p.2.1 p.2.2)
      (c, ((w : ℂ), x)) :=
    (contMDiffAt_pairOfPantsPerturbation (forall_update_inf (P := fun f => Periodic f 1)
      (fun _ => rfl) hH) (forall_update_inf
        (P := fun f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f)) contMDiff_const hHs)
      w x).comp (c, ((w : ℂ), x)) contMDiffAt_snd
  -- The plane part is the smooth plane datum composed with the translation by the parameter.
  have hsub : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
      (fun p : ℝ × (ℂ × M) => p.2.1 - (p.1 : ℂ)) (c, ((w : ℂ), x)) :=
    (contMDiffAt_fst.comp _ contMDiffAt_snd).sub
      (Complex.ofRealCLM.contDiff.contMDiff.contMDiffAt.comp _ contMDiffAt_fst)
  have hpl : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℝ × (ℂ × M) => negativePlanePerturbation (H inf) (p.2.1 - p.1) p.2.2)
      (c, ((w : ℂ), x)) :=
    (contMDiff_negativePlanePerturbation (hH inf) (hHs inf)).contMDiffAt.comp
      (f := fun p : ℝ × (ℂ × M) => (p.2.1 - (p.1 : ℂ), p.2.2)) _
      (hsub.prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))
  exact hin.add hpl

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer MeasureTheory

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {H : Puncture → ℝ → M → ℝ}

/-- **The integrated curvature of the input-exchange family is bounded uniformly.** Let `K` be the
member `c ∈ [0, 1]` of the input-exchange family of period-one `C¹` Hamiltonians `H_q` on a
manifold `M` with a two-form `ω`, with `|H_q| ≤ B_q`, and write its components in the global
coordinate `z = s + i t` of `ℂ` as `K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Then for every map
`u` into `M`, the integral of `|R_K(z, u(z))|` over the plane is at most `B₀ + B₁ + B_∞`, which
does not depend on `c`. -/
theorem lintegral_enorm_hamiltonianCurvature_exchangePerturbation_le (ω : SmoothTwoForm I M)
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ q, ENNReal.ofReal (B q) := by
  set e := Complex.equivRealProdCLM.symm
  -- The two parts of the datum, as components in real coordinates.
  set Ki : ℂ → ℝ × ℝ → M → ℝ := fun v z x ↦ pairOfPantsPerturbation (update H inf 0) (e z) x v
  set Kp : ℂ → ℝ × ℝ → M → ℝ := fun v z x ↦ negativePlanePerturbation (H inf) (e z) x v
  set a : ℝ × ℝ := ((c : ℝ), (0 : ℝ))
  have he (z : ℝ × ℝ) : e z - c = e (z + -a) := by
    simp only [e, a, map_add, map_neg]
    apply Complex.ext <;> simp [sub_eq_add_neg]
  -- Near the disc `‖w - c‖ < 2 exp (2π)` the datum is its input part; outside the disc it is the
  -- translated plane datum.
  set A : Set (ℝ × ℝ) := {z | ‖e z - c‖ < 2 * Real.exp (2 * π)}
  have hcont : Continuous fun z : ℝ × ℝ => ‖e z - c‖ := (e.continuous.sub continuous_const).norm
  have hA : IsOpen A := isOpen_lt hcont continuous_const
  have hexp : 3 < 2 * Real.exp (2 * π) := by
    nlinarith [Real.add_one_le_exp (2 * π), Real.two_le_pi]
  have hin (v : ℂ) {z : ℝ × ℝ} (hz : z ∈ A) :
      (fun z x ↦ exchangePerturbation H c (e z) x v) =ᶠ[𝓝 z] Ki v := by
    filter_upwards [hA.mem_nhds hz] with z' hz'
    funext x
    rw [exchangePerturbation_def, add_apply,
      negativePlanePerturbation_eq_zero_of_norm_le hz'.le, zero_apply, add_zero]
  have hout (v : ℂ) {z : ℝ × ℝ} (hz : z ∉ A) :
      (fun z x ↦ exchangePerturbation H c (e z) x v) =ᶠ[𝓝 z] fun z ↦ Kp v (z + -a) := by
    have h3 : 3 < ‖e z - c‖ := hexp.trans_le (not_lt.1 hz)
    filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds h3] with z' hz'
    funext x
    have hw : 3 / 2 ≤ ‖e z' - c‖ := by linarith
    simp only [Kp, exchangePerturbation_def,
      pairOfPantsPerturbation_update_inf_eq_zero_of_le_norm_sub hc₀ hc₁ hw, zero_add, he]
  -- Hence the curvature is that of one of the two parts at every point.
  have hRin {z : ℝ × ℝ} (hz : z ∈ A) :
      ω.hamiltonianCurvature (fun z x ↦ exchangePerturbation H c (e z) x 1)
        (fun z x ↦ exchangePerturbation H c (e z) x Complex.I) z =
      ω.hamiltonianCurvature (Ki 1) (Ki Complex.I) z :=
    ω.hamiltonianCurvature_congr_of_eventuallyEq (hin 1 hz) (hin Complex.I hz)
  have hRout {z : ℝ × ℝ} (hz : z ∈ Aᶜ) :
      ω.hamiltonianCurvature (fun z x ↦ exchangePerturbation H c (e z) x 1)
        (fun z x ↦ exchangePerturbation H c (e z) x Complex.I) z =
      ω.hamiltonianCurvature (fun w ↦ Kp 1 (w + -a)) (fun w ↦ Kp Complex.I (w + -a)) z :=
    ω.hamiltonianCurvature_congr_of_eventuallyEq (hout 1 hz) (hout Complex.I hz)
  -- The two bounds: the input part with bounds `B₀`, `B₁`, `0` and the plane part with `B_∞`.
  have hBin := ω.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le
    (forall_update_inf (P := fun f => Periodic f 1) (fun _ => rfl) hH)
    (forall_update_inf (P := fun f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry f))
      contMDiff_const hHs)
    (B := update B inf 0) (fun q t x => by
      rcases eq_or_ne q inf with rfl | hq
      · simp
      · simpa [update_of_ne hq] using hB q t x) u
  have hBpl : ∫⁻ z, ‖ω.hamiltonianCurvature (fun w ↦ Kp 1 (w + -a))
      (fun w ↦ Kp Complex.I (w + -a)) z (u z)‖ₑ ≤ ENNReal.ofReal (B inf) := by
    have h := ω.lintegral_enorm_hamiltonianCurvature_comp_add_right (Kp 1) (Kp Complex.I)
      (fun z ↦ u (z - -a)) (-a)
    simp only [add_sub_cancel_right] at h
    rw [h]
    exact ω.lintegral_enorm_hamiltonianCurvature_negativePlanePerturbation_le (hH inf) (hHs inf)
      (hB inf) (fun z ↦ u (z - -a))
  calc _ = (∫⁻ z in A, ‖ω.hamiltonianCurvature (fun z x ↦ exchangePerturbation H c (e z) x 1)
            (fun z x ↦ exchangePerturbation H c (e z) x Complex.I) z (u z)‖ₑ) +
          ∫⁻ z in Aᶜ, ‖ω.hamiltonianCurvature (fun z x ↦ exchangePerturbation H c (e z) x 1)
            (fun z x ↦ exchangePerturbation H c (e z) x Complex.I) z (u z)‖ₑ :=
        (lintegral_add_compl _ hA.measurableSet).symm
    _ = (∫⁻ z in A, ‖ω.hamiltonianCurvature (Ki 1) (Ki Complex.I) z (u z)‖ₑ) +
          ∫⁻ z in Aᶜ, ‖ω.hamiltonianCurvature (fun w ↦ Kp 1 (w + -a))
            (fun w ↦ Kp Complex.I (w + -a)) z (u z)‖ₑ := by
        congr 1
        · exact setLIntegral_congr_fun hA.measurableSet fun z hz => by rw [hRin hz]
        · exact setLIntegral_congr_fun hA.measurableSet.compl fun z hz => by rw [hRout hz]
    _ ≤ (∫⁻ z, ‖ω.hamiltonianCurvature (Ki 1) (Ki Complex.I) z (u z)‖ₑ) +
          ∫⁻ z, ‖ω.hamiltonianCurvature (fun w ↦ Kp 1 (w + -a))
            (fun w ↦ Kp Complex.I (w + -a)) z (u z)‖ₑ :=
        add_le_add (setLIntegral_le_lintegral _ _) (setLIntegral_le_lintegral _ _)
    _ ≤ (∑ q, ENNReal.ofReal (update B inf 0 q)) + ENNReal.ofReal (B inf) := add_le_add hBin hBpl
    _ = ∑ q, ENNReal.ofReal (B q) := by
        simp [Puncture.sum_univ]

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

open Floer MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **The integrated curvature of the input-exchange family is bounded uniformly.** This is the
vector-space case of
`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_exchangePerturbation_le`: for the
member `c ∈ [0, 1]` of the input-exchange family of period-one `C¹` Hamiltonians `H_q` on a
symplectic vector space with `|H_q| ≤ B_q`, and every map `u` into it, the integral of
`|R_K(z, u(z))|` over the plane is at most `B₀ + B₁ + B_∞`. -/
theorem lintegral_enorm_hamiltonianCurvature_exchangePerturbation_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ exchangePerturbation H c (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ q, ENNReal.ofReal (B q) := by
  simpa using ω.constSmooth.lintegral_enorm_hamiltonianCurvature_exchangePerturbation_le hH
    (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hB hc₀ hc₁ u

end TauCeti.SymplecticForm
