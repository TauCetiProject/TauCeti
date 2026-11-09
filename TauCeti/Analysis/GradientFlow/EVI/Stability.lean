/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.EVI.Basic
public import TauCeti.Topology.Semicontinuity.GammaConvergence

/-!
# Stability of evolution variational inequalities

The endpoint energy regularization characterization
`TauCeti.isEVISolution_iff_apply_le` involves only distances and endpoint energies, rather
than derivatives, and is therefore suited to passing to limits.

For energies with a common EVI parameter on a fixed metric carrier, Γ-convergence and
pointwise convergence of the solution curves to a continuous curve imply that the limit
is an EVI solution, assuming a nonempty effective domain and no negative-infinite energy
along the limit curve at positive times. No convergence of energies along the curves is assumed: the
Γ-liminf inequality and recovery sequences for the comparison points suffice. Compactness
of trajectories is a separate input, not a consequence of Γ-convergence.

## Main results

* `TauCeti.TendstoGamma.isEVISolution_of_tendsto`: stability under Γ-convergence.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 4.
* M. Muratori, G. Savaré, *Gradient flows and evolution variational inequalities in metric
  spaces. I: Structural properties*, J. Funct. Anal. 278 (2020), Sections 3 and 4.
-/

public section

open Filter Set Topology Real MeasureTheory

namespace TauCeti

variable {X : Type*} [PseudoMetricSpace X] {lam : ℝ} {φ : X → EReal} {u : ℝ → X}

/-- Γ-convergence preserves the endpoint regularization estimate of EVI solutions, using
recovery sequences for the comparison point and the Γ-liminf inequality along the curves. -/
private theorem TendstoGamma.apply_le_of_isEVISolution
    {F : ℕ → X → EReal} {U : ℕ → ℝ → X} (hΓ : TendstoGamma F φ)
    (hF : ∀ n, LowerSemicontinuous (F n)) (hU : ∀ n, IsEVISolution lam (F n) (U n))
    (hlim : ∀ t ≥ 0, Tendsto (fun n ↦ U n t) atTop (𝓝 (u t)))
    {y : X} (hy : φ y ≠ ⊤) {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    φ (u t) ≤ φ y + (((dist (u s) y ^ 2 - exp (lam * (t - s)) * dist (u t) y ^ 2) /
      (2 * ∫ r in 0..(t - s), exp (lam * r)) : ℝ) : EReal) := by
  obtain ⟨v, hv, hrec⟩ := hΓ.exists_tendsto_limsup_le y
  let C : X → X → X → ℝ := fun x z w ↦
    (dist x w ^ 2 - exp (lam * (t - s)) * dist z w ^ 2) /
      (2 * ∫ r in 0..(t - s), exp (lam * r))
  have hC : Tendsto (fun n ↦ ((C (U n s) (U n t) (v n) : ℝ) : EReal)) atTop
      (𝓝 ((C (u s) (u t) y : ℝ) : EReal)) := by
    apply (continuous_coe_real_ereal.tendsto _).comp
    dsimp [C]
    exact (((hlim s hs).dist hv).pow 2 |>.sub
      (tendsto_const_nhds.mul (((hlim t (hs.trans hst.le)).dist hv).pow 2))).div_const _
  have hfinite : ∀ᶠ n in atTop, F n (v n) ≠ ⊤ :=
    (eventually_lt_of_limsup_lt (hrec.trans_lt (lt_top_iff_ne_top.2 hy))).mono
      fun _ hn ↦ hn.ne
  have hreg : ∀ᶠ n in atTop, F n (U n t) ≤ F n (v n) +
      ((C (U n s) (U n t) (v n) : ℝ) : EReal) := by
    filter_upwards [hfinite] with n hn
    exact (hU n).apply_le_of_nonneg (hF n) hn hs hst
  calc φ (u t)
      ≤ liminf (fun n ↦ F n (U n t)) atTop := hΓ.le_liminf (hlim t (hs.trans hst.le))
    _ ≤ limsup (fun n ↦ F n (v n) + ((C (U n s) (U n t) (v n) : ℝ) : EReal)) atTop :=
      (liminf_le_liminf hreg).trans liminf_le_limsup
    _ ≤ limsup (fun n ↦ F n (v n)) atTop +
        limsup (fun n ↦ ((C (U n s) (U n t) (v n) : ℝ) : EReal)) atTop :=
      EReal.limsup_add_le
        (.inr (by rw [hC.limsup_eq]; exact EReal.coe_ne_top _))
        (.inr (by rw [hC.limsup_eq]; exact EReal.coe_ne_bot _))
    _ ≤ _ := by rw [hC.limsup_eq]; exact add_le_add hrec le_rfl

/-- **Stability of EVI flows under Γ-convergence on a fixed carrier.** Suppose the energies
`F n` are lower semicontinuous and Γ-converge to `φ`, and their `EVI_lam` solutions converge
pointwise at nonnegative times to a continuous curve `u`. If `φ` is not identically `⊤` and
never takes the value `⊥` along `u` at positive times, then `u` is an `EVI_lam` solution.
In particular, neither energy convergence along the curves nor trajectory compactness is
hidden in Γ-convergence; convergence to a continuous trajectory is an explicit hypothesis. -/
theorem TendstoGamma.isEVISolution_of_tendsto
    {F : ℕ → X → EReal} {U : ℕ → ℝ → X} (hΓ : TendstoGamma F φ)
    (hF : ∀ n, LowerSemicontinuous (F n)) (hU : ∀ n, IsEVISolution lam (F n) (U n))
    (hlim : ∀ t ≥ 0, Tendsto (fun n ↦ U n t) atTop (𝓝 (u t)))
    (hu : ContinuousOn u (Ici 0)) (hdom : ∃ y, φ y ≠ ⊤)
    (hbot : ∀ t > 0, φ (u t) ≠ ⊥) : IsEVISolution lam φ u := by
  have hreg := fun y hy s t hs hst ↦ hΓ.apply_le_of_isEVISolution hF hU hlim
    (y := y) hy (s := s) (t := t) hs hst
  have htop : ∀ t > 0, φ (u t) ≠ ⊤ := by
    obtain ⟨y, hy⟩ := hdom
    intro t ht
    exact ne_top_of_le_ne_top (EReal.add_ne_top hy (EReal.coe_ne_top _))
      (hreg y hy 0 t le_rfl ht)
  exact (isEVISolution_iff_apply_le hΓ.lowerSemicontinuous).2 ⟨hu, htop, hbot, hreg⟩

end TauCeti
