/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Exchange

/-!
# Capping the input at `0` along the input-exchange family

The unit of the pair-of-pants product is the count of negative PSS planes, and it is a unit on
either side: gluing a negative plane into the input at `1` or into the input at `0` of the pair of
pants `ℂ ∖ {0, 1}` gives a cylinder, whose counts compare with continuation maps. The capping
family at `1` is a datum on the standard cylinder in the end coordinates of the remaining input `0`
(`TauCeti.Floer.cappedCylinderComponent`), because the output end at `∞` is centred at `0` too,
so the two end coordinates differ by a translation. Capping the input at `0` instead leaves
`ℂ ∖ {1}`, whose remaining input end is centred at `1` while the output end is still centred at
`0`, and the two end coordinates differ by more than a translation.

This file joins the capping family at `0` to a Floer cylinder by moving the output end. For
`c ∈ ℝ`, the datum `TauCeti.Floer.cappedExchangePerturbation H L c` plumbs the negative plane with
Hamiltonian `H_0` into the end at `0` of the input-exchange family
`TauCeti.Floer.exchangePerturbation H c`, whose output end has the end lift `z ↦ c + φ_∞(z)`.
Since the translated output datum vanishes near the inputs, this is the capping datum at `0` plus
the output datum translated by `c`. For `0 ≤ c ≤ 1`:

* near the capped puncture `0` it is the capping datum at `0`
  (`TauCeti.Floer.cappedExchangePerturbation_of_lt_re_endCoord`), and it vanishes on the image of
  the pole disc of the plane (`TauCeti.Floer.cappedExchangePerturbation_eq_zero`); elsewhere it is
  the input-exchange datum (`TauCeti.Floer.cappedExchangePerturbation_of_re_endCoord_le`). The
  translated output datum and the capped part have disjoint supports: the datum is the capped part
  near `c` (`TauCeti.Floer.cappedExchangePerturbation_of_norm_sub_le`) and the translated output
  datum away from it (`TauCeti.Floer.cappedExchangePerturbation_of_le_norm_sub`);
* it is `H_1(t) dt` far out on the input end at `1`
  (`TauCeti.Floer.cappedExchangePerturbation_cylindricalEndLift`) and `H_∞(t) dt` far out on the
  output end recentred at `c`
  (`TauCeti.Floer.cappedExchangePerturbation_add_cylindricalEndLift_inf`);
* it is jointly `C^n` in `c`, the point of the capped domain `ℂ ∖ {1}` and the target point
  (`TauCeti.Floer.contMDiffAt_cappedExchangePerturbation`);
* for a symplectic vector space target and `|H_q| ≤ B_q`, its integrated curvature along any map
  is at most `B_0 + (B_0 + B_1 + B_∞)`, uniformly in `c` and in the neck length
  (`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_cappedExchangePerturbation_le`).

At `c = 0` it is the capping family at `0`
(`TauCeti.Floer.cappedExchangePerturbation_zero`). At `c = 1` it is the pullback along the
exchange `σ(w) = 1 - w` of the capping family at `1` of the pair of pants with exchanged inputs
(`TauCeti.Floer.cappedExchangePerturbation_one`), since `σ` carries the plumbing at `0` to the
plumbing at `1`. As `σ` carries the end lift of `1` to the end lift of `0`, in the cylinder
coordinates of the end lift `φ_1` the datum at `c = 1` is the capped cylinder datum of the
exchanged Hamiltonians (`TauCeti.Floer.cappedCylinderComponent_exchangeHamiltonians`). It is
therefore `H_1(t) dt` for `s ≥ 2` and `H_∞(t + 1/2) dt` for `s ≤ -3`, like a continuation datum on
the standard cylinder, and the energy identity and action bounds of
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.CappedCylinder` apply to it.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants and on the input exchange.
-/

public noncomputable section

open Set Real Manifold Topology Function MeasureTheory Filter
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M : Type*} {H : Puncture → ℝ → M → ℝ} {L c : ℝ}

/-- **The input-exchange family capped at `0`.** For a neck length `L` and `c ∈ ℝ`, the datum
obtained by plumbing the negative plane with Hamiltonian `H 0` into the input end at `0` of the
pair of pants whose output datum is the negative plane datum of `H ∞` translated by `c`, as in the
input-exchange family `TauCeti.Floer.exchangePerturbation`. -/
def cappedExchangePerturbation (H : Puncture → ℝ → M → ℝ) (L c : ℝ) (w : ℂ) (x : M) :
    ℂ →L[ℝ] ℝ :=
  plumbedPerturbation (Pi.single inf (H zero)) (update H inf 0) zero L w x +
    negativePlanePerturbation (H inf) (w - c) x

theorem cappedExchangePerturbation_def (H : Puncture → ℝ → M → ℝ) (L c : ℝ) (w : ℂ) (x : M) :
    cappedExchangePerturbation H L c w x =
      plumbedPerturbation (Pi.single inf (H zero)) (update H inf 0) zero L w x +
        negativePlanePerturbation (H inf) (w - c) x :=
  (rfl)

/-- For `L ≥ 2`, at distance at least `1/2` from `0` the longitudinal coordinate of the end at `0`
is at most `L / 2`, so the plumbing at `0` leaves the receiving datum unchanged there. -/
private theorem re_endCoord_zero_le_half (hL : 2 ≤ L) {w : ℂ} (hw : 1 / 2 ≤ ‖w‖) :
    (zero.endCoord w).re ≤ L / 2 := by
  have h : Real.exp (-(2 * π)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [Real.pi_pos])
  linarith [re_endCoord_zero_le_one (w := w) (by linarith)]

/-- The translated output datum vanishes within distance `1/2` of `0`, for `0 ≤ c ≤ 1`. -/
private theorem negativePlanePerturbation_sub_eq_zero_of_norm_le {H : ℝ → M → ℝ} (hc₀ : 0 ≤ c)
    (hc₁ : c ≤ 1) {w : ℂ} (hw : ‖w‖ ≤ 1 / 2) (x : M) :
    negativePlanePerturbation H (w - c) x = 0 := by
  refine negativePlanePerturbation_sub_eq_zero ((norm_sub_le _ _).trans ?_) x
  rw [Complex.norm_real, Real.norm_of_nonneg hc₀]
  linarith

/-- **Away from the capped disc the family is the input-exchange family.** Where the longitudinal
coordinate of the end at `0` is at most `L / 2`, the capped datum is the member `c` of the
input-exchange family. -/
theorem cappedExchangePerturbation_of_re_endCoord_le {w : ℂ} (hw : (zero.endCoord w).re ≤ L / 2)
    (x : M) : cappedExchangePerturbation H L c w x = exchangePerturbation H c w x := by
  rw [cappedExchangePerturbation_def, plumbedPerturbation_def, ite_eq_right (not_lt.2 hw),
    exchangePerturbation_def]

/-- **Near the capped puncture the family is the capping family at `0`.** For `L ≥ 2` and
`0 ≤ c ≤ 1`, where the longitudinal coordinate of the end at `0` exceeds `L / 2`, the capped datum
is the datum obtained by plumbing the negative plane with Hamiltonian `H 0` into the end at `0` of
the pair of pants with Hamiltonians `H`. -/
theorem cappedExchangePerturbation_of_lt_re_endCoord (hL : 2 ≤ L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {w : ℂ} (hw : L / 2 < (zero.endCoord w).re) (x : M) :
    cappedExchangePerturbation H L c w x =
      plumbedPerturbation (Pi.single inf (H zero)) H zero L w x := by
  have hn : ‖w‖ ≤ 1 / 2 := by
    by_contra! h
    linarith [re_endCoord_zero_le_half hL h.le]
  rw [cappedExchangePerturbation_def, negativePlanePerturbation_sub_eq_zero_of_norm_le hc₀ hc₁ hn,
    add_zero, plumbedPerturbation_def, plumbedPerturbation_def, ite_eq_left hw, ite_eq_left hw]

/-- **The start of the family is the capping family at `0`.** -/
theorem cappedExchangePerturbation_zero (hL : 2 ≤ L) :
    cappedExchangePerturbation H L 0 = plumbedPerturbation (Pi.single inf (H zero)) H zero L := by
  funext w x
  rcases le_or_gt (zero.endCoord w).re (L / 2) with hw | hw
  · rw [cappedExchangePerturbation_of_re_endCoord_le hw, exchangePerturbation_zero,
      plumbedPerturbation_def, ite_eq_right (not_lt.2 hw)]
  · exact cappedExchangePerturbation_of_lt_re_endCoord hL le_rfl zero_le_one hw x

/-- **The end of the family is the exchanged capping family at `1`.** At `c = 1` the capped datum
is the pullback along the exchange `σ(w) = 1 - w` of the datum obtained by plumbing the negative
plane with Hamiltonian `H 0` into the end at `1` of the pair of pants with exchanged Hamiltonians
(`TauCeti.Floer.exchangeHamiltonians`). Since `dσ = -1`, this pullback is `w ↦ -K'(1 - w)`. -/
theorem cappedExchangePerturbation_one (hH : Periodic (H inf) 1) (hL : 2 ≤ L) (w : ℂ) (x : M) :
    cappedExchangePerturbation H L 1 w x =
      -plumbedPerturbation (Pi.single inf (H zero)) (exchangeHamiltonians H) one L (1 - w) x := by
  have hre : (one.endCoord (1 - w)).re = (zero.endCoord w).re := by rw [endCoord_one_one_sub]
  rcases le_or_gt (zero.endCoord w).re (L / 2) with hw | hw
  · rw [cappedExchangePerturbation_of_re_endCoord_le hw, exchangePerturbation_one hH,
      plumbedPerturbation_def, ite_eq_right (by rw [hre]; exact not_lt.2 hw)]
  · -- In plumbing coordinates the exchange is the identity, while it reverses tangent vectors.
    have hpt : (1 - w - one.endCenter) / one.plumbingFactor L =
        (w - zero.endCenter) / zero.plumbingFactor L := by
      rw [plumbingFactor_one, endCenter_one, endCenter_zero, div_neg, ← neg_div]
      ring_nf
    rw [cappedExchangePerturbation_of_lt_re_endCoord hL zero_le_one le_rfl hw,
      plumbedPerturbation_def, plumbedPerturbation_def, ite_eq_left hw,
      ite_eq_left (by rwa [hre]), hpt, plumbingFactor_one, inv_neg]
    ext v
    simp

/-- **The end of the family on the standard cylinder.** In the cylinder coordinates of the end
lift `φ_1` of the end at `1`, the capped datum at `c = 1` is the capped cylinder datum
`TauCeti.Floer.cappedCylinderComponent` of the exchanged Hamiltonians. -/
theorem cappedCylinderComponent_exchangeHamiltonians (hH : Periodic (H inf) 1) (hL : 2 ≤ L)
    (v : ℂ) (z : ℝ × ℝ) (x : M) :
    cappedCylinderComponent (exchangeHamiltonians H) L v z x =
      cappedExchangePerturbation H L 1 (one.cylindricalEndLift (Complex.equivRealProdCLM.symm z)) x
        (deriv one.cylindricalEndLift (Complex.equivRealProdCLM.symm z) * v) := by
  have hd (w : ℂ) : deriv one.cylindricalEndLift w = -deriv zero.cylindricalEndLift w := by
    rw [deriv_cylindricalEndLift, deriv_cylindricalEndLift, ← one_sub_cylindricalEndLift_zero,
      endCenter_one, endCenter_zero]
    ring
  rw [cappedExchangePerturbation_one hH hL, one_sub_cylindricalEndLift_one, hd,
    cappedCylinderComponent_def, exchangeHamiltonians_one, neg_apply, neg_mul, map_neg, neg_neg]

/-- **The family on the remaining input end.** For `L ≥ 0` and `0 ≤ c ≤ 1`, on the part `s ≥ 2`
of the input end at `1`, the pullback of the capped datum along the end lift `φ_1` sends a tangent
vector `v` of the cylinder to `Im v · H_1(Im z)`. -/
theorem cappedExchangePerturbation_cylindricalEndLift (hH : Periodic (H one) 1) (hL : 0 ≤ L)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : 2 ≤ z.re) (x : M) (v : ℂ) :
    cappedExchangePerturbation H L c (one.cylindricalEndLift z) x
        (deriv one.cylindricalEndLift z * v) =
      v.im * H one z.im x := by
  have hw : (zero.endCoord (one.cylindricalEndLift z)).re ≤ L / 2 := by
    have h := endSign_mul_re_endCoord_nonpos (q := one) (r := zero) (by decide)
      (w := one.cylindricalEndLift z)
      (by rw [endSign_eq_one (by decide), one_mul, re_endCoord_cylindricalEndLift]; linarith)
    rw [endSign_eq_one (by decide), one_mul] at h
    linarith
  rw [cappedExchangePerturbation_of_re_endCoord_le hw,
    exchangePerturbation_cylindricalEndLift (by decide) hH hc₀ hc₁ hz]

/-- **The family on the output end.** For `L ≥ 2` and `0 ≤ c ≤ 1`, on the part `s ≤ -2` of the
output end recentred at `c`, the pullback of the capped datum along the end lift `z ↦ c + φ_∞(z)`
sends a tangent vector `v` of the cylinder to `Im v · H_∞(Im z)`. -/
theorem cappedExchangePerturbation_add_cylindricalEndLift_inf (hH : Periodic (H inf) 1)
    (hL : 2 ≤ L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {z : ℂ} (hz : z.re ≤ -2) (x : M) (v : ℂ) :
    cappedExchangePerturbation H L c (c + inf.cylindricalEndLift z) x
        (deriv inf.cylindricalEndLift z * v) =
      v.im * H inf z.im x := by
  -- The end lift at `∞` stays at distance at least `2` from `0` on the part `s ≤ 0`.
  have hφ : 2 ≤ ‖inf.cylindricalEndLift z‖ := by
    rw [cylindricalEndLift_inf, norm_mul, Complex.norm_ofNat, Complex.norm_exp]
    have : 1 ≤ Real.exp (-(2 * (π : ℂ)) * z).re := by
      rw [Real.one_le_exp_iff,
        show -(2 * (π : ℂ)) * z = ((-(2 * π) : ℝ) : ℂ) * z by push_cast; ring,
        Complex.re_ofReal_mul]
      nlinarith [Real.pi_pos]
    linarith
  have hn : 1 / 2 ≤ ‖(c : ℂ) + inf.cylindricalEndLift z‖ := by
    have h := norm_sub_norm_le (inf.cylindricalEndLift z) (-(c : ℂ))
    rw [sub_neg_eq_add, norm_neg, Complex.norm_real, Real.norm_of_nonneg hc₀, add_comm] at h
    linarith
  rw [cappedExchangePerturbation_of_re_endCoord_le (re_endCoord_zero_le_half hL hn),
    exchangePerturbation_add_cylindricalEndLift_inf hH hc₀ hc₁ hz]

/-- **The family near the inputs.** Within distance `2 exp (2π)` of `c`, the translated output
datum vanishes, and the capped datum is the plumbing of the negative plane into the input part of
the pair-of-pants datum. -/
theorem cappedExchangePerturbation_of_norm_sub_le {w : ℂ} (hw : ‖w - c‖ ≤ 2 * Real.exp (2 * π))
    (x : M) :
    cappedExchangePerturbation H L c w x =
      plumbedPerturbation (Pi.single inf (H zero)) (update H inf 0) zero L w x := by
  rw [cappedExchangePerturbation_def, negativePlanePerturbation_eq_zero_of_norm_le hw, add_zero]

/-- **The family near the output.** For `L ≥ 2` and `0 ≤ c ≤ 1`, at distance at least `3/2` from
`c` the capped part vanishes, and the capped datum is the negative plane datum translated by `c`. -/
theorem cappedExchangePerturbation_of_le_norm_sub (hL : 2 ≤ L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    {w : ℂ} (hw : 3 / 2 ≤ ‖w - c‖) (x : M) :
    cappedExchangePerturbation H L c w x = negativePlanePerturbation (H inf) (w - c) x := by
  have hn : 1 / 2 ≤ ‖w‖ := by
    have h := norm_sub_le w (c : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg hc₀] at h
    linarith
  rw [cappedExchangePerturbation_of_re_endCoord_le (re_endCoord_zero_le_half hL hn),
    exchangePerturbation_def, pairOfPantsPerturbation_update_inf_eq_zero_of_le_norm_sub hc₀ hc₁ hw,
    zero_add]

/-- **The capped disc.** For `L > 2` and `0 ≤ c ≤ 1`, the capped datum vanishes on the disc of
radius `exp (-2π(L - 1)) / 2` about the capped puncture `0`, the image under the plumbing map of
the pole disc of the plane. -/
theorem cappedExchangePerturbation_eq_zero (hL : 2 < L) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1) {w : ℂ}
    (hw : ‖w‖ ≤ Real.exp (-(2 * π * (L - 1))) / 2) (x : M) :
    cappedExchangePerturbation H L c w x = 0 := by
  have hn : ‖w‖ ≤ 1 / 2 := hw.trans <| by
    have : Real.exp (-(2 * π * (L - 1))) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [Real.pi_pos])
    linarith
  rw [cappedExchangePerturbation_def,
    plumbedPerturbation_single_inf_eq_zero (by decide) hL (by simpa using hw),
    negativePlanePerturbation_sub_eq_zero_of_norm_le hc₀ hc₁ hn, add_zero]

/-- The inserted Hamiltonian of the capped part is the value at `0` of its receiving Hamiltonians
`update H inf 0`, the form used by the capping-family API. -/
private theorem update_inf_zero : update H inf 0 zero = H zero :=
  update_of_ne (by decide) _ _

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The family is smooth.** For period-one Hamiltonians of class `C^n` on `ℝ × M` and neck length
`L > 4`, the capped datum is `C^n` jointly in the parameter `c ∈ ℝ`, the point of the capped domain
`ℂ ∖ {1}` and the target point. -/
theorem contMDiffAt_cappedExchangePerturbation {n : ℕ∞} (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (H q))) (hL : 4 < L) (c : ℝ)
    {w : ℂ} (hw : w ≠ 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℝ × (ℂ × M) => cappedExchangePerturbation H L p.1 p.2.1 p.2.2) (c, (w, x)) := by
  -- The capped part does not depend on the parameter.
  have hw' : w = zero.endCenter ∨ w ≠ 0 ∧ w ≠ 1 := by
    rcases eq_or_ne w 0 with rfl | h₀
    · exact Or.inl endCenter_zero.symm
    · exact Or.inr ⟨h₀, hw⟩
  have hcap := contMDiffAt_plumbedPerturbation_single_inf (Hb := update H inf 0) (by decide)
    ((forall_update_iff H fun _ f => Periodic f 1).2 ⟨fun _ => rfl, fun q _ => hH q⟩)
    ((forall_update_iff H fun _ f => ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry f)).2
      ⟨contMDiff_const, fun q _ => hHs q⟩) hL hw' x
  rw [update_inf_zero] at hcap
  have hin : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℝ × (ℂ × M) =>
        plumbedPerturbation (Pi.single inf (H zero)) (update H inf 0) zero L p.2.1 p.2.2)
      (c, (w, x)) :=
    hcap.comp (c, (w, x)) contMDiffAt_snd
  -- The plane part is the smooth plane datum composed with the translation by the parameter.
  have hsub : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
      (fun p : ℝ × (ℂ × M) => p.2.1 - (p.1 : ℂ)) (c, (w, x)) :=
    (contMDiffAt_fst.comp _ contMDiffAt_snd).sub
      (Complex.ofRealCLM.contDiff.contMDiff.contMDiffAt.comp _ contMDiffAt_fst)
  have hpl : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℝ × (ℂ × M) => negativePlanePerturbation (H inf) (p.2.1 - p.1) p.2.2)
      (c, (w, x)) :=
    (contMDiff_negativePlanePerturbation (hH inf) (hHs inf)).contMDiffAt.comp
      (f := fun p : ℝ × (ℂ × M) => (p.2.1 - (p.1 : ℂ), p.2.2)) _
      (hsub.prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))
  exact hin.add hpl

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {L : ℝ}

/-- **The integrated curvature of the capped input-exchange family is bounded uniformly.** Let `K`
be the member `c ∈ [0, 1]` of the input-exchange family capped at `0` along a neck of length
`L > 4`, for period-one `C¹` Hamiltonians `H_q` with `|H_q| ≤ B_q`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)` in the global coordinate `z = s + i t` of `ℂ`. Then for
every map `u` into the target, the integral of `|R_K(z, u(z))|` over the plane is at most
`B_0 + ∑ q, B_q`, which depends neither on `c` nor on `L`. -/
theorem lintegral_enorm_hamiltonianCurvature_cappedExchangePerturbation_le (ω : SymplecticForm V)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q))) (hL : 4 < L)
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {c : ℝ} (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        z (u z)‖ₑ ≤ ENNReal.ofReal (B zero) + ∑ q, ENNReal.ofReal (B q) := by
  set e := Complex.equivRealProdCLM.symm
  -- The two parts of the datum, as components in real coordinates.
  set Ki : ℂ → ℝ × ℝ → V → ℝ := fun v z x ↦
    plumbedPerturbation (Pi.single inf (H zero)) (update H inf 0) zero L (e z) x v
  set Kp : ℂ → ℝ × ℝ → V → ℝ := fun v z x ↦ negativePlanePerturbation (H inf) (e z) x v
  set a : ℝ × ℝ := ((c : ℝ), (0 : ℝ))
  have he (z : ℝ × ℝ) : e z - c = e (z + -a) := by
    simp only [e, a, map_add, map_neg]
    apply Complex.ext <;> simp [sub_eq_add_neg]
  -- Near the disc `‖w - c‖ < 2 exp (2π)` the datum is its capped part; outside the disc it is the
  -- translated plane datum.
  set A : Set (ℝ × ℝ) := {z | ‖e z - c‖ < 2 * Real.exp (2 * π)}
  have hcont : Continuous fun z : ℝ × ℝ => ‖e z - c‖ := (e.continuous.sub continuous_const).norm
  have hA : IsOpen A := isOpen_lt hcont continuous_const
  have hexp : 3 < 2 * Real.exp (2 * π) := by
    nlinarith [Real.add_one_le_exp (2 * π), Real.two_le_pi]
  have hin (v : ℂ) {z : ℝ × ℝ} (hz : z ∈ A) :
      (fun z x ↦ cappedExchangePerturbation H L c (e z) x v) =ᶠ[𝓝 z] Ki v := by
    filter_upwards [hA.mem_nhds hz] with z' hz'
    funext x
    rw [cappedExchangePerturbation_of_norm_sub_le hz'.le]
  have hout (v : ℂ) {z : ℝ × ℝ} (hz : z ∉ A) :
      (fun z x ↦ cappedExchangePerturbation H L c (e z) x v) =ᶠ[𝓝 z] fun z ↦ Kp v (z + -a) := by
    have h3 : 3 < ‖e z - c‖ := hexp.trans_le (not_lt.1 hz)
    filter_upwards [(isOpen_lt continuous_const hcont).mem_nhds h3] with z' hz'
    funext x
    rw [cappedExchangePerturbation_of_le_norm_sub (by linarith) hc₀ hc₁ (by linarith), he]
  -- Hence the curvature is that of one of the two parts at every point.
  have hRin {z : ℝ × ℝ} (hz : z ∈ A) :
      ω.hamiltonianCurvature (fun z x ↦ cappedExchangePerturbation H L c (e z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (e z) x Complex.I) z =
      ω.hamiltonianCurvature (Ki 1) (Ki Complex.I) z :=
    ω.hamiltonianCurvature_congr_of_eventuallyEq (hin 1 hz) (hin Complex.I hz)
  have hRout {z : ℝ × ℝ} (hz : z ∈ Aᶜ) :
      ω.hamiltonianCurvature (fun z x ↦ cappedExchangePerturbation H L c (e z) x 1)
        (fun z x ↦ cappedExchangePerturbation H L c (e z) x Complex.I) z =
      ω.hamiltonianCurvature (fun w ↦ Kp 1 (w + -a)) (fun w ↦ Kp Complex.I (w + -a)) z :=
    ω.hamiltonianCurvature_congr_of_eventuallyEq (hout 1 hz) (hout Complex.I hz)
  -- The two bounds: the capped part with bounds `B₀`, `B₁`, `0` and the plane part with `B_∞`.
  have hBin : ∫⁻ z, ‖ω.hamiltonianCurvature (Ki 1) (Ki Complex.I) z (u z)‖ₑ ≤
      ENNReal.ofReal (B zero) + ∑ q, ENNReal.ofReal (update B inf 0 q) := by
    have h := ω.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_single_inf_le
      (q := zero) (Hb := update H inf 0) (by decide)
      ((forall_update_iff H fun _ f => Periodic f 1).2 ⟨fun _ => rfl, fun q _ => hH q⟩)
      ((forall_update_iff H fun _ f => ContDiff ℝ 1 (uncurry f)).2
        ⟨contDiff_const, fun q _ => hHs q⟩) hL
      (Bb := update B inf 0) (fun q t x => by
        rcases eq_or_ne q inf with rfl | hq
        · simp
        · simpa [update_of_ne hq] using hB q t x) u
    simpa only [update_inf_zero, update_of_ne (show zero ≠ inf by decide)] using h
  have hBpl : ∫⁻ z, ‖ω.hamiltonianCurvature (fun w ↦ Kp 1 (w + -a))
      (fun w ↦ Kp Complex.I (w + -a)) z (u z)‖ₑ ≤ ENNReal.ofReal (B inf) := by
    have h := ω.lintegral_enorm_hamiltonianCurvature_comp_add_right (Kp 1) (Kp Complex.I)
      (fun z ↦ u (z - -a)) (-a)
    simp only [add_sub_cancel_right] at h
    rw [h]
    exact ω.lintegral_enorm_hamiltonianCurvature_negativePlanePerturbation_le (hH inf) (hHs inf)
      (hB inf) (fun z ↦ u (z - -a))
  calc _ = (∫⁻ z in A, ‖ω.hamiltonianCurvature
            (fun z x ↦ cappedExchangePerturbation H L c (e z) x 1)
            (fun z x ↦ cappedExchangePerturbation H L c (e z) x Complex.I) z (u z)‖ₑ) +
          ∫⁻ z in Aᶜ, ‖ω.hamiltonianCurvature
            (fun z x ↦ cappedExchangePerturbation H L c (e z) x 1)
            (fun z x ↦ cappedExchangePerturbation H L c (e z) x Complex.I) z (u z)‖ₑ :=
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
    _ ≤ (ENNReal.ofReal (B zero) + ∑ q, ENNReal.ofReal (update B inf 0 q)) +
          ENNReal.ofReal (B inf) := add_le_add hBin hBpl
    _ = ENNReal.ofReal (B zero) + ∑ q, ENNReal.ofReal (B q) := by
        simp [Puncture.sum_univ, add_assoc]

end TauCeti.SymplecticForm
