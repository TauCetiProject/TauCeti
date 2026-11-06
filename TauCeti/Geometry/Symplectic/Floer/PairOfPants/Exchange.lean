/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.ThricePuncturedSphere.Exchange
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Unique

/-!
# Exchanging the inputs of the pair of pants

The graded commutativity of the pair-of-pants product compares the counts for the input order
`(H₀, H₁)` with those for `(H₁, H₀)`. The comparison is induced by the reflection `σ(w) = 1 - w` of
the thrice-punctured sphere `S = ℂ ∖ {0, 1}`, which exchanges the input punctures `0` and `1` and
fixes the output puncture `∞`. This file constructs the perturbation data of this comparison.

The reflection exchanges the two input ends exactly, markers included
(`TauCeti.ThricePuncturedSphere.Puncture.one_sub_cylindricalEndLift`), but it is not a symmetry
of the output end coordinate `w = 2 exp (-2πz)` centred at `0`. It is the point reflection about
`1/2`, so it rotates by half a turn the output end coordinate `w = 1/2 + 2 exp (-2πz)` centred at
`1/2`. The data therefore move the centre of the output end:

* `TauCeti.Floer.centeredPairOfPantsPerturbation c H` is the pair-of-pants perturbation of the
  input Hamiltonians `H₀`, `H₁` plus the negative plane perturbation of the output Hamiltonian `H_∞`
  translated by `c`. For `c = 0` it is the pair-of-pants perturbation
  (`centeredPairOfPantsPerturbation_zero`). For `‖c‖ ≤ 1/2` it is `H_q(t) dt` far out on each
  input end in the standard end coordinates
  (`centeredPairOfPantsPerturbation_cylindricalEndLift`) and `H_∞(t) dt` far out on the output
  end in the end coordinates centred at `c`
  (`centeredPairOfPantsPerturbation_add_cylindricalEndLift`). It is smooth jointly in `c`, the point
  of `S` and the target point (`contMDiffAt_centeredPairOfPantsPerturbation`), and its integrated
  curvature is at most `B₀ + B₁ + B_∞` for `|H_q| ≤ B_q`, uniformly in `c`
  (`SymplecticForm.lintegral_enorm_hamiltonianCurvature_centeredPairOfPantsPerturbation_le`). The
  segment `c ∈ [0, 1/2]` thus deforms the pair-of-pants datum with fixed end Hamiltonians and
  bounded curvature.
* At `c = 1/2` the reflection pulls the datum back to the datum of the exchanged Hamiltonians
  `TauCeti.Floer.exchangeHamiltonians H = (H₁, H₀, H_∞(· + 1/2))`
  (`centeredPairOfPantsPerturbation_one_sub`). The output Hamiltonian is shifted by half a period
  because the reflection rotates the output end by half a turn
  (`negativePlanePerturbation_neg`).

For a symplectic vector space target, `u ↦ u ∘ σ` is therefore a bijection between the solutions of
the Floer equation for the two data at `c = 1/2`
(`SymplecticForm.isComplexLinearMap_perturbedFDeriv_exchange_iff`), which preserves the energy
density (`SymplecticForm.floerEnergyDensity_exchange`) and the energy
(`SymplecticForm.integral_floerEnergyDensity_exchange`). The curvature of the exchanged datum is
the reflected curvature (`SymplecticForm.hamiltonianCurvature_exchange`). In the global real
coordinate `z = s + i t` of `ℂ` the reflection is `z ↦ (1, 0) - z`. Identifying the orbits of
`H_∞(· + 1/2)` with those of `H_∞` by the rotation `x ↦ x(· + 1/2)` of loops, the orientations and
the resulting counts are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the commutativity of the pair-of-pants product.
* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200.
-/

public noncomputable section

open Set Real Manifold Topology Function MeasureTheory
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*}

/-! ### The exchanged Hamiltonians -/

/-- The end Hamiltonians after exchanging the inputs: the two input Hamiltonians trade places, and
the output Hamiltonian is shifted in time by half a period, since the exchange `w ↦ 1 - w` rotates
the output end by half a turn. -/
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

variable {H : Puncture → ℝ → M → ℝ}

/-- On an input, the exchanged Hamiltonian is the Hamiltonian of the other input. -/
theorem exchangeHamiltonians_of_ne_inf {q : Puncture} (hq : q ≠ inf) :
    exchangeHamiltonians H q = H (Equiv.swap zero one q) := by
  cases q <;> simp_all

/-- Exchanging the inputs twice gives back the end Hamiltonians, for a period-one output
Hamiltonian. -/
theorem exchangeHamiltonians_exchangeHamiltonians (hH : Periodic (H inf) 1) :
    exchangeHamiltonians (exchangeHamiltonians H) = H := by
  funext q
  cases q
  · rfl
  · rfl
  · funext t
    simp only [exchangeHamiltonians_inf, add_assoc]
    norm_num
    exact hH t

/-- A property of time-dependent Hamiltonians that is preserved by the half-period time shift
passes from the end Hamiltonians to the exchanged ones, for instance periodicity or smoothness. -/
theorem forall_exchangeHamiltonians {P : (ℝ → M → ℝ) → Prop}
    (hP : ∀ f, P f → P fun t => f (t + 1 / 2)) (h : ∀ q, P (H q)) (q : Puncture) :
    P (exchangeHamiltonians H q) := by
  cases q
  exacts [h one, h zero, hP _ (h inf)]

/-! ### The pair-of-pants perturbation with a translated output end -/

/-- **The pair-of-pants perturbation with output end centred at `c`.** It is the pair-of-pants
perturbation of the two input Hamiltonians `H 0` and `H 1`, plus the negative plane perturbation
of the output Hamiltonian `H ∞` translated by `c`. For `‖c‖ ≤ 1/2` and a period-one `H ∞`, in the
end coordinates `w = c + 2 exp (-2πz)` of the translated end at `∞` it is `β(-s - 1) H_∞(t) dt`
on the part `s < 0` (`centeredPairOfPantsPerturbation_add_cylindricalEndLift_of_neg`). For
`c = 0` it is the pair-of-pants perturbation (`centeredPairOfPantsPerturbation_zero`). -/
def centeredPairOfPantsPerturbation (c : ℂ) (H : Puncture → ℝ → M → ℝ) (w : ℂ) (x : M) :
    ℂ →L[ℝ] ℝ :=
  pairOfPantsPerturbation (update H inf 0) w x + negativePlanePerturbation (H inf) (w - c) x

theorem centeredPairOfPantsPerturbation_def (c : ℂ) (H : Puncture → ℝ → M → ℝ) (w : ℂ)
    (x : M) :
    centeredPairOfPantsPerturbation c H w x =
      pairOfPantsPerturbation (update H inf 0) w x + negativePlanePerturbation (H inf) (w - c) x :=
  (rfl)

/-- With the output end centred at `0`, the perturbation is the pair-of-pants perturbation. -/
@[simp]
theorem centeredPairOfPantsPerturbation_zero (H : Puncture → ℝ → M → ℝ) :
    centeredPairOfPantsPerturbation 0 H = pairOfPantsPerturbation H := by
  have hH : H = update H inf 0 + Pi.single inf (H inf) := by
    funext q
    rcases eq_or_ne q inf with rfl | hq
    · simp
    · simp [hq]
  funext w x
  conv_rhs => rw [hH]
  rw [pairOfPantsPerturbation_add, pairOfPantsPerturbation_single_inf,
    centeredPairOfPantsPerturbation_def, sub_zero, Pi.add_apply, Pi.add_apply]

/-- The input part of the perturbation vanishes off the disc of radius `3/2`, which contains the
parts `s > 0` of both input ends. -/
private theorem pairOfPantsPerturbation_update_inf_zero_eq_zero {w : ℂ} (hw : 3 / 2 ≤ ‖w‖)
    (x : M) : pairOfPantsPerturbation (update H inf 0) w x = 0 := by
  rw [pairOfPantsPerturbation_def]
  refine Finset.sum_eq_zero fun q _ => ?_
  rcases eq_or_ne q inf with rfl | hq
  · simp
  · have hc : ‖q.endCenter‖ ≤ 1 := by
      rcases q.endCenter_eq_zero_or_eq_one with h | h <;> simp [h]
    have h₁ : 1 ≤ ‖(w - q.endCenter) / q.endScale‖ := by
      rw [norm_div, norm_endScale hq, le_div_iff₀ (by norm_num)]
      linarith [norm_sub_norm_le w q.endCenter]
    have h₂ : q.endSign * (q.endCoord w).re ≤ 0 := by
      rw [endSign_eq_one hq, one_mul, re_endCoord, neg_div]
      exact neg_nonpos.2 (div_nonneg (Real.log_nonneg h₁) (by positivity))
    rw [smoothTransition.zero_of_nonpos (by linarith), zero_mul, zero_smul]

/-- **The perturbation on an input end.** If `‖c‖ ≤ 1/2`, then on the part `s > 0` of the input
end `q` the pullback of the perturbation along the end lift is the continuation datum
`β(s - 1) H_q(t) dt`: the translated output datum vanishes there. -/
theorem centeredPairOfPantsPerturbation_cylindricalEndLift_of_pos {q : Puncture} (hq : q ≠ inf)
    {c : ℂ} (hc : ‖c‖ ≤ 1 / 2) (hH : Periodic (H q) 1) {z : ℂ} (hz : 0 < z.re) (x : M)
    (v : ℂ) :
    centeredPairOfPantsPerturbation c H (q.cylindricalEndLift z) x
        (deriv q.cylindricalEndLift z * v) =
      v.im * (smoothTransition (z.re - 1) * H q z.im x) := by
  have hw : ‖q.cylindricalEndLift z - c‖ ≤ 2 * Real.exp (2 * π) := by
    have hc' : ‖q.endCenter‖ ≤ 1 := by
      rcases q.endCenter_eq_zero_or_eq_one with h | h <;> simp [h]
    have he : Real.exp (-(2 * π * z.re)) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    have h1 := norm_cylindricalEndLift_sub_endCenter q z
    rw [norm_endScale hq] at h1
    have h2 : ‖q.cylindricalEndLift z - c‖ ≤
        ‖q.cylindricalEndLift z - q.endCenter‖ + ‖q.endCenter‖ + ‖c‖ := by
      calc ‖q.cylindricalEndLift z - c‖
          = ‖(q.cylindricalEndLift z - q.endCenter) + q.endCenter - c‖ := by ring_nf
        _ ≤ ‖(q.cylindricalEndLift z - q.endCenter) + q.endCenter‖ + ‖c‖ := norm_sub_le _ _
        _ ≤ _ := by gcongr; exact norm_add_le _ _
    nlinarith [Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * π)]
  rw [centeredPairOfPantsPerturbation_def, negativePlanePerturbation_eq_zero_of_norm_le hw,
    add_zero]
  have h := pairOfPantsPerturbation_cylindricalEndLift_of_pos (H := update H inf 0) (q := q)
    (by simpa [update_of_ne hq] using hH) (z := z) (by rwa [endSign_eq_one hq, one_mul]) x v
  simpa [update_of_ne hq, endSign_eq_one hq] using h

/-- **The perturbation is `H_q(t) dt` far out on each input end**, for `‖c‖ ≤ 1/2`. -/
theorem centeredPairOfPantsPerturbation_cylindricalEndLift {q : Puncture} (hq : q ≠ inf)
    {c : ℂ} (hc : ‖c‖ ≤ 1 / 2) (hH : Periodic (H q) 1) {z : ℂ} (hz : 2 ≤ z.re) (x : M)
    (v : ℂ) :
    centeredPairOfPantsPerturbation c H (q.cylindricalEndLift z) x
        (deriv q.cylindricalEndLift z * v) =
      v.im * H q z.im x := by
  rw [centeredPairOfPantsPerturbation_cylindricalEndLift_of_pos hq hc hH (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

/-- **The perturbation on the translated output end.** If `‖c‖ ≤ 1/2`, then on the part `s < 0`
of the output end, in the end coordinates `w = c + 2 exp (-2πz)` centred at `c`, the pullback of
the perturbation is the continuation datum `β(-s - 1) H_∞(t) dt`: the input part vanishes there. -/
theorem centeredPairOfPantsPerturbation_add_cylindricalEndLift_of_neg {c : ℂ}
    (hc : ‖c‖ ≤ 1 / 2) (hH : Periodic (H inf) 1) {z : ℂ} (hz : z.re < 0) (x : M) (v : ℂ) :
    centeredPairOfPantsPerturbation c H (c + inf.cylindricalEndLift z) x
        (deriv inf.cylindricalEndLift z * v) =
      v.im * (smoothTransition (-z.re - 1) * H inf z.im x) := by
  have hw : 3 / 2 ≤ ‖c + inf.cylindricalEndLift z‖ := by
    have h1 := norm_cylindricalEndLift_sub_endCenter inf z
    simp only [endCenter_inf, sub_zero, endScale_inf, Complex.norm_ofNat] at h1
    have he : 1 ≤ Real.exp (-(2 * π * z.re)) :=
      Real.one_le_exp (by nlinarith [Real.pi_pos])
    have h2 := norm_sub_norm_le (inf.cylindricalEndLift z) (-c)
    rw [sub_neg_eq_add, add_comm, norm_neg] at h2
    linarith
  rw [centeredPairOfPantsPerturbation_def, pairOfPantsPerturbation_update_inf_zero_eq_zero hw,
    zero_add, add_sub_cancel_left]
  exact negativePlanePerturbation_cylindricalEndLift_of_neg hH hz x v

/-- **The perturbation is `H_∞(t) dt` far out on the translated output end**, for `‖c‖ ≤ 1/2`. -/
theorem centeredPairOfPantsPerturbation_add_cylindricalEndLift {c : ℂ} (hc : ‖c‖ ≤ 1 / 2)
    (hH : Periodic (H inf) 1) {z : ℂ} (hz : z.re ≤ -2) (x : M) (v : ℂ) :
    centeredPairOfPantsPerturbation c H (c + inf.cylindricalEndLift z) x
        (deriv inf.cylindricalEndLift z * v) =
      v.im * H inf z.im x := by
  rw [centeredPairOfPantsPerturbation_add_cylindricalEndLift_of_neg hc hH (by linarith),
    smoothTransition.one_of_one_le (by linarith), one_mul]

/-! ### The input exchange -/

/-- **The half-turn of the negative plane.** The point reflection `w ↦ -w` pulls the negative
plane perturbation of a period-one Hamiltonian `H` back to the negative plane perturbation of
`H(· + 1/2)`; the derivative `-1` of the reflection accounts for the sign. -/
theorem negativePlanePerturbation_neg {H : ℝ → M → ℝ} (hH : Periodic H 1) (w : ℂ) (x : M) :
    negativePlanePerturbation H (-w) x =
      -negativePlanePerturbation (fun t => H (t + 1 / 2)) w x := by
  rcases eq_or_ne w 0 with rfl | hw
  · have h : ‖(0 : ℂ)‖ ≤ 2 * Real.exp (2 * π) := by rw [norm_zero]; positivity
    rw [neg_zero, negativePlanePerturbation_eq_zero_of_norm_le h,
      negativePlanePerturbation_eq_zero_of_norm_le h, neg_zero]
  obtain ⟨k, hk⟩ := exists_im_endCoord_inf_neg_eq hw
  have hp : H ((inf.endCoord w).im + 1 / 2 + k) x = H ((inf.endCoord w).im + 1 / 2) x := by
    simpa using congrFun (hH.int_mul k ((inf.endCoord w).im + 1 / 2)) x
  rw [negativePlanePerturbation_def, negativePlanePerturbation_def, re_endCoord_inf_neg, hk, hp,
    endAngularForm_inf_neg, smul_neg]

/-- **The input exchange.** With the output end centred at `1/2`, the reflection `w ↦ 1 - w` pulls
the perturbation of the end Hamiltonians `H` back to the perturbation of the exchanged
Hamiltonians `(H₁, H₀, H_∞(· + 1/2))`: the value at `1 - w` is minus the exchanged value at `w`,
the sign being the derivative of the reflection. -/
theorem centeredPairOfPantsPerturbation_one_sub (hH : Periodic (H inf) 1) (w : ℂ) (x : M) :
    centeredPairOfPantsPerturbation (1 / 2) H (1 - w) x =
      -centeredPairOfPantsPerturbation (1 / 2) (exchangeHamiltonians H) w x := by
  have hout : negativePlanePerturbation (H inf) (1 - w - 1 / 2) x =
      -negativePlanePerturbation (exchangeHamiltonians H inf) (w - 1 / 2) x := by
    rw [show 1 - w - 1 / 2 = -(w - 1 / 2) by ring, negativePlanePerturbation_neg hH,
      exchangeHamiltonians_inf]
  have e₀ : zero.endCoord (1 - w) = one.endCoord w := by
    simpa using endCoord_swap_one_sub (q := one) (by decide) w
  have e₁ : one.endCoord (1 - w) = zero.endCoord w := by
    simpa using endCoord_swap_one_sub (q := zero) (by decide) w
  have a₀ : zero.endAngularForm (1 - w) = -one.endAngularForm w := by
    simpa using endAngularForm_swap_one_sub (q := one) (by decide) w
  have a₁ : one.endAngularForm (1 - w) = -zero.endAngularForm w := by
    simpa using endAngularForm_swap_one_sub (q := zero) (by decide) w
  have hin : pairOfPantsPerturbation (update H inf 0) (1 - w) x =
      -pairOfPantsPerturbation (update (exchangeHamiltonians H) inf 0) w x := by
    simp only [pairOfPantsPerturbation_def, Puncture.sum_univ, e₀, e₁, a₀, a₁, update_self,
      update_of_ne (show zero ≠ inf by decide), update_of_ne (show one ≠ inf by decide),
      exchangeHamiltonians_zero, exchangeHamiltonians_one, endSign_zero, endSign_one,
      Pi.zero_apply, mul_zero, zero_smul, add_zero, smul_neg, neg_add]
    abel
  rw [centeredPairOfPantsPerturbation_def, centeredPairOfPantsPerturbation_def, hin, hout,
    neg_add]

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The family is smooth.** For Hamiltonians of period one which are `C^n` on `ℝ × M`, the
perturbation is `C^n` jointly in the centre `c ∈ ℂ` of the output end, the point of the
thrice-punctured sphere and the target point. -/
theorem contMDiffAt_centeredPairOfPantsPerturbation {n : ℕ∞} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H q))) (c : ℂ)
    (w : ThricePuncturedSphere) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × ℂ × M => centeredPairOfPantsPerturbation p.1 H p.2.1 p.2.2) (c, (w : ℂ), x) := by
  have hin := contMDiffAt_pairOfPantsPerturbation (H := update H inf 0) (n := n)
    ((forall_update_iff H fun _ f => Periodic f 1).2 ⟨fun _ => rfl, fun q _ => hH q⟩)
    ((forall_update_iff H fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f)).2
      ⟨contMDiff_const, fun q _ => hHs q⟩) w x
  have hout := (contMDiff_negativePlanePerturbation (hH inf) (hHs inf)).contMDiffAt
    (x := ((w : ℂ) - c, x))
  have h₁ : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
      (fun p : ℂ × ℂ × M => p.2.1) (c, (w : ℂ), x) :=
    contMDiffAt_fst.comp _ contMDiffAt_snd
  have h₀ : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
      (fun p : ℂ × ℂ × M => p.1) (c, (w : ℂ), x) :=
    contMDiffAt_fst
  have hsub : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℂ).prod I)) (𝓘(ℝ, ℂ).prod I) n
      (fun p : ℂ × ℂ × M => (p.2.1 - p.1, p.2.2)) (c, (w : ℂ), x) :=
    (h₁.sub h₀).prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd)
  have hin' : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × ℂ × M => pairOfPantsPerturbation (update H inf 0) p.2.1 p.2.2)
      (c, (w : ℂ), x) :=
    hin.comp (c, (w : ℂ), x) contMDiffAt_snd
  have hout' : ContMDiffAt (𝓘(ℝ, ℂ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × ℂ × M => negativePlanePerturbation (H inf) (p.2.1 - p.1) p.2.2)
      (c, (w : ℂ), x) :=
    hout.comp (c, (w : ℂ), x) hsub
  exact hin'.add hout'

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

omit [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
/-- In real coordinates the exchange `w ↦ 1 - w` is the point reflection `z ↦ (1, 0) - z`, and
each component of the exchanged datum is the pullback `z ↦ -K(1 - z)` of the datum. -/
private theorem centeredPairOfPantsPerturbation_exchange_apply (hH : Periodic (H inf) 1)
    (v : ℂ) :
    (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) (exchangeHamiltonians H)
        (Complex.equivRealProdCLM.symm z) x v) =
      fun z ↦ -fun x ↦ centeredPairOfPantsPerturbation (1 / 2) H
        (Complex.equivRealProdCLM.symm ((1, 0) - z)) x v := by
  funext z x
  have h : Complex.equivRealProdCLM.symm ((1, 0) - z) = 1 - Complex.equivRealProdCLM.symm z := by
    apply Complex.ext <;> simp
  rw [Pi.neg_apply, h, centeredPairOfPantsPerturbation_one_sub hH, neg_apply, neg_neg]

/-- **The exchange of the inputs preserves the Floer equation.** With the output end centred at
`1/2`, the reflected map `z ↦ u((1, 0) - z)` solves the Floer equation at `z` for the datum of the
exchanged Hamiltonians exactly when `u` solves it at `(1, 0) - z` for the datum of `H`. -/
theorem isComplexLinearMap_perturbedFDeriv_exchange_iff (ω : SymplecticForm V)
    (J : AlmostComplexStructure V) (hH : Periodic (H inf) 1) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv
          (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) (exchangeHamiltonians H)
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) (exchangeHamiltonians H)
            (Complex.equivRealProdCLM.symm z) x Complex.I)
          (fun w ↦ u ((1, 0) - w)) z : ℝ × ℝ →ₗ[ℝ] V) ↔
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedFDeriv
          (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H
            (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H
            (Complex.equivRealProdCLM.symm z) x Complex.I)
          u ((1, 0) - z) : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [centeredPairOfPantsPerturbation_exchange_apply hH,
    centeredPairOfPantsPerturbation_exchange_apply hH]
  exact ω.isComplexLinearMap_perturbedFDeriv_neg_comp_const_sub_iff J
    (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H (Complex.equivRealProdCLM.symm z) x
      Complex.I) u (1, 0) z

/-- **The exchange of the inputs preserves the energy density.** -/
theorem floerEnergyDensity_exchange (ω : SymplecticForm V) (hH : Periodic (H inf) 1)
    (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.floerEnergyDensity
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) (exchangeHamiltonians H)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) (exchangeHamiltonians H)
          (Complex.equivRealProdCLM.symm z) x Complex.I)
        (fun w ↦ u ((1, 0) - w)) z =
      ω.floerEnergyDensity
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H
          (Complex.equivRealProdCLM.symm z) x Complex.I)
        u ((1, 0) - z) := by
  rw [centeredPairOfPantsPerturbation_exchange_apply hH,
    centeredPairOfPantsPerturbation_exchange_apply hH]
  exact ω.floerEnergyDensity_neg_comp_const_sub
    (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H (Complex.equivRealProdCLM.symm z) x
      Complex.I) u (1, 0) z

/-- **The exchange of the inputs preserves the energy**: the energy of the reflected map for the
exchanged datum is the energy of the map. -/
theorem integral_floerEnergyDensity_exchange (ω : SymplecticForm V) (hH : Periodic (H inf) 1)
    (u : ℝ × ℝ → V) :
    ∫ z, ω.floerEnergyDensity
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) (exchangeHamiltonians H)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) (exchangeHamiltonians H)
          (Complex.equivRealProdCLM.symm z) x Complex.I)
        (fun w ↦ u ((1, 0) - w)) z =
      ∫ z, ω.floerEnergyDensity
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H
          (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z := by
  simp_rw [ω.floerEnergyDensity_exchange hH u]
  rw [Measure.volume_eq_prod]
  exact integral_sub_left_eq_self _ _ _

/-- **The curvature of the exchanged datum** is the curvature of the datum at the reflected
point. -/
theorem hamiltonianCurvature_exchange (ω : SymplecticForm V) (hH : Periodic (H inf) 1)
    (z : ℝ × ℝ) (x : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) (exchangeHamiltonians H)
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) (exchangeHamiltonians H)
          (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H
          (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H
          (Complex.equivRealProdCLM.symm z) x Complex.I) ((1, 0) - z) x := by
  rw [centeredPairOfPantsPerturbation_exchange_apply hH,
    centeredPairOfPantsPerturbation_exchange_apply hH]
  exact ω.hamiltonianCurvature_neg_comp_const_sub
    (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H (Complex.equivRealProdCLM.symm z) x 1)
    (fun z x ↦ centeredPairOfPantsPerturbation (1 / 2) H (Complex.equivRealProdCLM.symm z) x
      Complex.I) (1, 0) z x

/-- **The integrated curvature of the family.** Let `|H_q| ≤ B_q` for period-one `C¹`
Hamiltonians. For every centre `c` of the output end with `‖c‖ ≤ 1/2` and every map `u` into the
target, the integral of the curvature `|R_K(z, u(z))|` of the perturbation with output end centred
at `c` is at most `B₀ + B₁ + B_∞`. On the disc `‖w‖ < 2` the perturbation is its input part, and
off the disc `‖w‖ ≤ 3/2` it is the translated plane perturbation, whose curvature integral does not
depend on the translation. -/
theorem lintegral_enorm_hamiltonianCurvature_centeredPairOfPantsPerturbation_le
    (ω : SymplecticForm V) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) {B : Puncture → ℝ}
    (hB : ∀ q t x, |H q t x| ≤ B q) {c : ℂ} (hc : ‖c‖ ≤ 1 / 2) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ centeredPairOfPantsPerturbation c H (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ centeredPairOfPantsPerturbation c H (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        z (u z)‖ₑ ≤ ∑ q, ENNReal.ofReal (B q) := by
  set e := Complex.equivRealProdCLM
  set c' : ℝ × ℝ := e c
  set A : Set (ℝ × ℝ) := {z | ‖e.symm z‖ < 2}
  have hA : IsOpen A := isOpen_lt (e.symm.continuous.norm) continuous_const
  -- The curvature of the input part, and that of the untranslated plane perturbation.
  set Rin : ℝ × ℝ → V → ℝ := ω.hamiltonianCurvature
    (fun z x ↦ pairOfPantsPerturbation (update H inf 0) (e.symm z) x 1)
    (fun z x ↦ pairOfPantsPerturbation (update H inf 0) (e.symm z) x Complex.I)
  set Rout : ℝ × ℝ → V → ℝ := ω.hamiltonianCurvature
    (fun z x ↦ negativePlanePerturbation (H inf) (e.symm z) x 1)
    (fun z x ↦ negativePlanePerturbation (H inf) (e.symm z) x Complex.I)
  -- On `A` the translated plane perturbation vanishes near every point.
  have hinA : ∀ z ∈ A, ω.hamiltonianCurvature
      (fun z x ↦ centeredPairOfPantsPerturbation c H (e.symm z) x 1)
      (fun z x ↦ centeredPairOfPantsPerturbation c H (e.symm z) x Complex.I) z = Rin z := by
    intro z hz
    have h : ∀ᶠ z' in 𝓝 z, ∀ x : V,
        centeredPairOfPantsPerturbation c H (e.symm z') x =
          pairOfPantsPerturbation (update H inf 0) (e.symm z') x := by
      filter_upwards [hA.mem_nhds hz] with z' hz' x
      have hle : ‖e.symm z' - c‖ ≤ 2 * Real.exp (2 * π) := by
        have := norm_sub_le (e.symm z') c
        have : 2 * π + 1 ≤ Real.exp (2 * π) := Real.add_one_le_exp _
        have := Real.two_le_pi
        simp only [A, mem_ofPred_eq] at hz'
        linarith
      rw [centeredPairOfPantsPerturbation_def, negativePlanePerturbation_eq_zero_of_norm_le hle,
        add_zero]
    exact ω.hamiltonianCurvature_congr_of_eventuallyEq
      (h.mono fun z' hz' => funext fun x => by simp only [hz' x])
      (h.mono fun z' hz' => funext fun x => by simp only [hz' x])
  -- Off `A` the input part vanishes near every point.
  have houtA : ∀ z ∈ Aᶜ, ω.hamiltonianCurvature
      (fun z x ↦ centeredPairOfPantsPerturbation c H (e.symm z) x 1)
      (fun z x ↦ centeredPairOfPantsPerturbation c H (e.symm z) x Complex.I) z =
        Rout (z - c') := by
    intro z hz
    have hB' : IsOpen {z : ℝ × ℝ | 3 / 2 < ‖e.symm z‖} :=
      isOpen_lt continuous_const e.symm.continuous.norm
    have hz' : 3 / 2 < ‖e.symm z‖ := by
      simp only [A, mem_compl_iff, mem_ofPred_eq, not_lt] at hz
      linarith
    have h : ∀ᶠ z' in 𝓝 z, ∀ x : V,
        centeredPairOfPantsPerturbation c H (e.symm z') x =
          negativePlanePerturbation (H inf) (e.symm (z' + -c')) x := by
      filter_upwards [hB'.mem_nhds hz'] with z' hz' x
      rw [centeredPairOfPantsPerturbation_def,
        pairOfPantsPerturbation_update_inf_zero_eq_zero hz'.le, zero_add, map_add, map_neg,
        ContinuousLinearEquiv.symm_apply_apply, ← sub_eq_add_neg]
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq
      (Ks' := fun z' x ↦ negativePlanePerturbation (H inf) (e.symm (z' + -c')) x 1)
      (Kt' := fun z' x ↦ negativePlanePerturbation (H inf) (e.symm (z' + -c')) x Complex.I)
      (h.mono fun z' hz' => funext fun x => by simp only [hz' x])
      (h.mono fun z' hz' => funext fun x => by simp only [hz' x])]
    funext x
    exact (ω.hamiltonianCurvature_comp_add_right
      (fun z x ↦ negativePlanePerturbation (H inf) (e.symm z) x 1)
      (fun z x ↦ negativePlanePerturbation (H inf) (e.symm z) x Complex.I) (-c') z x).trans
        (by rw [← sub_eq_add_neg])
  -- The two pieces are bounded by the existing curvature bounds.
  have hBin : ∫⁻ z, ‖Rin z (u z)‖ₑ ≤ ENNReal.ofReal (B zero) + ENNReal.ofReal (B one) := by
    have h := ω.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le
      (H := update H inf 0) (B := update B inf 0)
      ((forall_update_iff H fun _ f => Periodic f 1).2 ⟨fun _ => rfl, fun q _ => hH q⟩)
      ((forall_update_iff H fun _ f => ContDiff ℝ 1 (uncurry f)).2
        ⟨contDiff_const, fun q _ => hHs q⟩)
      (fun q t x => by
        rcases eq_or_ne q inf with rfl | hq
        · simp
        · simpa [update_of_ne hq] using hB q t x) u
    simpa [Puncture.sum_univ, update_of_ne (show zero ≠ inf by decide),
      update_of_ne (show one ≠ inf by decide)] using h
  have hBout : ∫⁻ z, ‖Rout (z - c') (u z)‖ₑ ≤ ENNReal.ofReal (B inf) := by
    rw [Measure.volume_eq_prod,
      ← lintegral_add_right_eq_self (fun z ↦ ‖Rout (z - c') (u z)‖ₑ) c', ← Measure.volume_eq_prod]
    simpa only [add_sub_cancel_right] using
      ω.lintegral_enorm_hamiltonianCurvature_negativePlanePerturbation_le (hH inf) (hHs inf)
        (hB inf) (fun z ↦ u (z + c'))
  calc _ = (∫⁻ z in A, ‖ω.hamiltonianCurvature
          (fun z x ↦ centeredPairOfPantsPerturbation c H (e.symm z) x 1)
          (fun z x ↦ centeredPairOfPantsPerturbation c H (e.symm z) x Complex.I) z (u z)‖ₑ) +
        ∫⁻ z in Aᶜ, ‖ω.hamiltonianCurvature
          (fun z x ↦ centeredPairOfPantsPerturbation c H (e.symm z) x 1)
          (fun z x ↦ centeredPairOfPantsPerturbation c H (e.symm z) x Complex.I) z (u z)‖ₑ :=
        (lintegral_add_compl _ hA.measurableSet).symm
    _ = (∫⁻ z in A, ‖Rin z (u z)‖ₑ) + ∫⁻ z in Aᶜ, ‖Rout (z - c') (u z)‖ₑ := by
        rw [setLIntegral_congr_fun hA.measurableSet fun z hz => by rw [hinA z hz],
          setLIntegral_congr_fun hA.measurableSet.compl fun z hz => by rw [houtA z hz]]
    _ ≤ (∫⁻ z, ‖Rin z (u z)‖ₑ) + ∫⁻ z, ‖Rout (z - c') (u z)‖ₑ :=
        add_le_add (setLIntegral_le_lintegral _ _) (setLIntegral_le_lintegral _ _)
    _ ≤ ENNReal.ofReal (B zero) + ENNReal.ofReal (B one) + ENNReal.ofReal (B inf) :=
        add_le_add hBin hBout
    _ = ∑ q, ENNReal.ofReal (B q) := (Puncture.sum_univ fun q ↦ ENNReal.ofReal (B q)).symm

end TauCeti.SymplecticForm
