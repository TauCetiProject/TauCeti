/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.GradientFlow.MaximalSlope.Basic
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Limits of curves of maximal slope

The Sandier–Serfaty argument passes the energy-dissipation inequality to a limit using
well-prepared initial energies and lower bounds for the energy, action and upper gradients.
Here all curves take values in one pseudometric space and converge pointwise on a compact
time interval. Lower semicontinuity of the action supplies the action bound, and its finite
lower limit implies absolute continuity of the limiting curve for every exponent `p > 1`.
Fatou's lemma supplies the upper-gradient integral bound from an almost-everywhere slope
bound. If the limiting upper gradient is strong, the endpoint dissipation inequality
implies that the limit is a curve of maximal slope on the whole interval.

Once the limiting energy identity holds, both the terminal energies and the total
dissipations converge: no energy or dissipation is lost in the limit.

No compactness or recovery-sequence assumption is built into the theorem: it applies after
a convergent family of trajectories has been obtained. The initial energy convergence and
the energy and slope lower bounds are separate hypotheses.

## References

* S. Serfaty, *Gamma-convergence of gradient flows on Hilbert and metric spaces and
  applications*, Discrete Contin. Dyn. Syst. 31 (2011), 1427–1451, Theorem 2.
* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Section 2.3.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal Interval

namespace TauCeti

variable {X ι : Type*} [PseudoMetricSpace X] {l : Filter ι}
  [l.NeBot] [l.IsCountablyGenerated] {p q a b : ℝ}
  {u : ℝ → X} {us : ι → ℝ → X} {g : X → ℝ≥0∞} {gs : ι → X → ℝ≥0∞}

/-- **Lower semicontinuity of dissipation.** Pointwise convergence of curves, eventually
absolutely continuous, and an almost-everywhere lower bound on the upper gradients give a
lower bound on the limiting dissipation. No absolute continuity of the limit is assumed. -/
theorem dissipation_le_liminf (hp : 1 < p) (hq : 0 < q)
    (hus : ∀ᶠ i in l, AbsolutelyContinuousOnInterval (us i) a b)
    (hu : ∀ t ∈ uIcc a b, Tendsto (fun i ↦ us i t) l (𝓝 (u t)))
    (hgs : ∀ᶠ i in l, AEMeasurable (fun t ↦ gs i (us i t)) (volume.restrict (Ι a b)))
    (hg : ∀ᵐ t ∂volume.restrict (Ι a b), g (u t) ≤ liminf (fun i ↦ gs i (us i t)) l) :
    dissipation p q g u a b ≤ liminf (fun i ↦ dissipation p q (gs i) (us i) a b) l := by
  classical
  have hA := curveAction_le_liminf_of_one_lt hp hus hu
  -- Replace the exceptional, possibly nonmeasurable integrands by zero for Fatou.
  let fs : ι → ℝ → ℝ≥0∞ := fun i ↦
    if AEMeasurable (fun t ↦ gs i (us i t)) (volume.restrict (Ι a b)) then
      fun t ↦ gs i (us i t) ^ q else 0
  have hfs : ∀ᶠ i in l, fs i = fun t ↦ gs i (us i t) ^ q :=
    hgs.mono fun i hi ↦ by simp [fs, hi]
  have hmeas i : AEMeasurable (fs i) (volume.restrict (Ι a b)) := by
    dsimp [fs]
    split_ifs with hi
    · exact hi.pow_const q
    · exact aemeasurable_const
  have hFatou : (∫⁻ t in Ι a b, liminf (fun i ↦ gs i (us i t) ^ q) l) ≤
      liminf (fun i ↦ ∫⁻ t in Ι a b, gs i (us i t) ^ q) l := by
    calc
      _ = ∫⁻ t in Ι a b, liminf (fun i ↦ fs i t) l :=
        lintegral_congr fun t ↦ liminf_congr (hfs.mono fun i hi ↦ congrFun hi.symm t)
      _ ≤ liminf (fun i ↦ ∫⁻ t in Ι a b, fs i t) l := lintegral_liminf_le' hmeas
      _ = _ := liminf_congr (hfs.mono fun i hi ↦ by rw [hi])
  have hG : (∫⁻ t in Ι a b, g (u t) ^ q) ≤
      liminf (fun i ↦ ∫⁻ t in Ι a b, gs i (us i t) ^ q) l := by
    refine (lintegral_mono_ae (hg.mono fun t ht ↦ ?_)).trans hFatou
    exact (ENNReal.rpow_le_rpow ht hq.le).trans_eq
      ((ENNReal.monotone_rpow_of_nonneg hq.le).map_liminf_of_continuousAt (F := l)
        (fun i ↦ gs i (us i t)) ENNReal.continuous_rpow_const.continuousAt)
  have hdiv (c : ℝ) (hc : 0 < c) (v : ι → ℝ≥0∞) :
      liminf v l / ENNReal.ofReal c = liminf (fun i ↦ v i / ENNReal.ofReal c) l := by
    have hmono : Monotone fun x : ℝ≥0∞ ↦ x / ENNReal.ofReal c :=
      fun _ _ h ↦ ENNReal.div_le_div_right h _
    exact hmono.map_liminf_of_continuousAt (F := l) v
      (ENNReal.continuous_div_const _ (ENNReal.ofReal_pos.2 hc).ne').continuousAt
  simp only [dissipation_def]
  calc
    _ ≤ liminf (fun i ↦ curveAction p (us i) a b) l / ENNReal.ofReal p +
        liminf (fun i ↦ ∫⁻ t in Ι a b, gs i (us i t) ^ q) l / ENNReal.ofReal q :=
      add_le_add (ENNReal.div_le_div_right hA _) (ENNReal.div_le_div_right hG _)
    _ = _ := by rw [hdiv p (zero_lt_one.trans hp), hdiv q hq]
    _ ≤ _ := by
      -- `EReal.le_liminf_add` applies to nonnegative extended reals after the continuous
      -- order embedding; the generic ordered-group lemma does not apply to `ENNReal`.
      have hcast (v : ι → ℝ≥0∞) :
          (↑(liminf v l) : EReal) = liminf (fun i ↦ (v i : EReal)) l :=
        EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt _
          continuous_coe_ennreal_ereal.continuousAt
      apply EReal.coe_ennreal_le_coe_ennreal_iff.1
      rw [EReal.coe_ennreal_add, hcast, hcast, hcast]
      simpa only [Function.comp_apply, EReal.coe_ennreal_add, Pi.add_def] using
        (EReal.le_liminf_add (f := l)
          (u := fun i ↦ (↑(curveAction p (us i) a b / ENNReal.ofReal p) : EReal))
          (v := fun i ↦ (↑((∫⁻ t in Ι a b, gs i (us i t) ^ q) / ENNReal.ofReal q) : EReal)))

/-- **The Sandier–Serfaty limit argument on a fixed carrier.** Let the approximating curves
eventually be curves of maximal slope and converge pointwise on `[a,b]`, with initial
energies converging to the limiting initial energy, a lower bound on the terminal energy,
and an almost-everywhere lower bound on the upper gradients. If the limiting upper gradient
is strong, the limit is a curve of maximal slope. Absolute continuity of the limit follows
from the dissipation bound. -/
theorem isCurveOfMaximalSlope_of_tendsto {φ : X → EReal} {φs : ι → X → EReal}
    (hpq : p.HolderConjugate q) (hab : a ≤ b)
    (hus : ∀ᶠ i in l, IsCurveOfMaximalSlope p q (φs i) (gs i) (us i) (Icc a b))
    (hu : ∀ t ∈ Icc a b, Tendsto (fun i ↦ us i t) l (𝓝 (u t)))
    (hinit : Tendsto (fun i ↦ φs i (us i a)) l (𝓝 (φ (u a))))
    (ha : φ (u a) ≠ ⊤) (hb : φ (u b) ≠ ⊥)
    (henergy : φ (u b) ≤ liminf (fun i ↦ φs i (us i b)) l)
    (hgs : ∀ᶠ i in l, AEMeasurable (fun t ↦ gs i (us i t)) (volume.restrict (Ι a b)))
    (hslope : ∀ᵐ t ∂volume.restrict (Ι a b),
      g (u t) ≤ liminf (fun i ↦ gs i (us i t)) l)
    (hg : IsStrongUpperGradient φ g) : IsCurveOfMaximalSlope p q φ g u (Icc a b) := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hAC := hus.mono fun i hi ↦ hi.absolutelyContinuousOnInterval haI hbI
  have hlim : ∀ t ∈ uIcc a b, Tendsto (fun i ↦ us i t) l (𝓝 (u t)) := by
    simpa only [uIcc_of_le hab] using hu
  set D := liminf (fun i ↦ dissipation p q (gs i) (us i) a b) l
  have hcoe : (D : EReal) =
      liminf (fun i ↦ (dissipation p q (gs i) (us i) a b : EReal)) l :=
    EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt _
      continuous_coe_ennreal_ereal.continuousAt
  have hbound : φ (u b) + D ≤ φ (u a) := by
    calc
      _ ≤ liminf (fun i ↦ φs i (us i b)) l + D := by gcongr
      _ ≤ liminf (fun i ↦ φs i (us i b) + dissipation p q (gs i) (us i) a b) l := by
        rw [hcoe]
        exact EReal.le_liminf_add
      _ ≤ liminf (fun i ↦ φs i (us i a)) l :=
        liminf_le_liminf (hus.mono fun i hi ↦ hi.apply_add_dissipation_le haI hbI hab)
      _ = _ := hinit.liminf_eq
  have hD : D ≠ ∞ := by
    intro h
    rw [h, EReal.coe_ennreal_top, EReal.add_top_of_ne_bot hb, top_le_iff] at hbound
    exact ha hbound
  have haction : liminf (fun i ↦ curveAction p (us i) a b) l ≠ ∞ := by
    have hle : liminf (fun i ↦ curveAction p (us i) a b / ENNReal.ofReal p) l ≤ D :=
      liminf_le_liminf (.of_forall fun i ↦ by
        rw [dissipation_def]
        exact le_self_add)
    have hmono : Monotone fun x : ℝ≥0∞ ↦ x / ENNReal.ofReal p :=
      fun _ _ h ↦ ENNReal.div_le_div_right h _
    have hmap : liminf (fun i ↦ curveAction p (us i) a b) l / ENNReal.ofReal p =
        liminf (fun i ↦ curveAction p (us i) a b / ENNReal.ofReal p) l :=
      hmono.map_liminf_of_continuousAt (F := l)
        (fun i ↦ curveAction p (us i) a b)
        (ENNReal.continuous_div_const _ (ENNReal.ofReal_pos.2 hpq.pos).ne').continuousAt
    rw [← hmap] at hle
    intro h
    rw [h, ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top, top_le_iff] at hle
    exact hD hle
  have hACu := absolutelyContinuousOnInterval_of_tendsto_of_liminf_ne_top hpq.lt
    hAC hlim haction
  refine (isCurveOfMaximalSlope_Icc_iff hg hpq hab hACu).2 ⟨ha, hb, ?_⟩
  refine le_trans ?_ hbound
  gcongr
  exact EReal.coe_ennreal_le_coe_ennreal_iff.2
    (dissipation_le_liminf hpq.lt hpq.symm.pos hAC hlim hgs hslope)

omit [l.IsCountablyGenerated] in
/-- **Convergence of energy and dissipation.** For a limiting curve of maximal slope with
a strong upper gradient, well-prepared initial energies and lower bounds on the terminal
energy and dissipation force convergence of both quantities, provided the approximating
curves are eventually curves of maximal slope. This applies to any interval on which the
limit argument has identified the limiting curve. -/
theorem IsCurveOfMaximalSlope.tendsto_apply_and_dissipation
    {φ : X → EReal} {φs : ι → X → EReal}
    (h : IsCurveOfMaximalSlope p q φ g u (Icc a b))
    (hg : IsStrongUpperGradient φ g) (hpq : p.HolderConjugate q) (hab : a ≤ b)
    (hus : ∀ᶠ i in l, IsCurveOfMaximalSlope p q (φs i) (gs i) (us i) (Icc a b))
    (hinit : Tendsto (fun i ↦ φs i (us i a)) l (𝓝 (φ (u a))))
    (henergy : φ (u b) ≤ liminf (fun i ↦ φs i (us i b)) l)
    (hdiss : dissipation p q g u a b ≤
      liminf (fun i ↦ dissipation p q (gs i) (us i) a b) l) :
    Tendsto (fun i ↦ φs i (us i b)) l (𝓝 (φ (u b))) ∧
      Tendsto (fun i ↦ dissipation p q (gs i) (us i) a b) l
        (𝓝 (dissipation p q g u a b)) := by
  have haI : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hbI : b ∈ Icc a b := ⟨hab, le_rfl⟩
  set D := dissipation p q g u a b
  have heq : φ (u a) = φ (u b) + D := h.apply_eq_add_dissipation hg hpq haI hbI hab
  have hD : D ≠ ∞ := by
    intro htop
    rw [htop, EReal.coe_ennreal_top, EReal.add_top_of_ne_bot (h.apply_ne_bot hbI)] at heq
    exact h.apply_ne_top haI heq
  have hcast : (↑(liminf (fun i ↦ dissipation p q (gs i) (us i) a b) l) : EReal) =
      liminf (fun i ↦ (dissipation p q (gs i) (us i) a b : EReal)) l :=
    EReal.coe_ennreal_strictMono.monotone.map_liminf_of_continuousAt _
      continuous_coe_ennreal_ereal.continuousAt
  have hlower : (D : EReal) ≤
      liminf (fun i ↦ (dissipation p q (gs i) (us i) a b : EReal)) l := by
    rw [← hcast]
    exact EReal.coe_ennreal_le_coe_ennreal_iff.2 hdiss
  -- The lower dissipation bound and the approximating inequalities bound the terminal
  -- energy from above. The limiting energy identity makes this the matching upper bound.
  have hupper : limsup (fun i ↦ φs i (us i b)) l + D ≤ φ (u a) := by
    calc
      _ ≤ limsup (fun i ↦ φs i (us i b)) l +
          liminf (fun i ↦ (dissipation p q (gs i) (us i) a b : EReal)) l := by gcongr
      _ ≤ limsup (fun i ↦ φs i (us i b) + dissipation p q (gs i) (us i) a b) l :=
        EReal.le_limsup_add
      _ ≤ limsup (fun i ↦ φs i (us i a)) l :=
        limsup_le_limsup (hus.mono fun i hi ↦ hi.apply_add_dissipation_le haI hbI hab)
      _ = _ := hinit.limsup_eq
  have hEtendsto : Tendsto (fun i ↦ φs i (us i b)) l (𝓝 (φ (u b))) := by
    rw [heq, ← EReal.coe_ennreal_toReal hD] at hupper
    exact tendsto_of_le_liminf_of_limsup_le henergy
      ((EReal.addLECancellable_coe D.toReal).add_le_add_iff_right.1 hupper)
  refine ⟨hEtendsto, EReal.tendsto_coe_ennreal.1 ?_⟩
  -- With terminal energy convergence established, the same argument bounds dissipation
  -- from above. Its assumed lower bound then gives convergence as well.
  have hupperD : (D : EReal) ≥
      limsup (fun i ↦ (dissipation p q (gs i) (us i) a b : EReal)) l := by
    have hsum : limsup (fun i ↦ (dissipation p q (gs i) (us i) a b : EReal)) l +
        φ (u b) ≤ φ (u a) := by
      calc
        _ = limsup (fun i ↦ (dissipation p q (gs i) (us i) a b : EReal)) l +
            liminf (fun i ↦ φs i (us i b)) l := by rw [hEtendsto.liminf_eq]
        _ ≤ limsup (fun i ↦ (dissipation p q (gs i) (us i) a b : EReal) +
            φs i (us i b)) l := EReal.le_limsup_add
        _ ≤ limsup (fun i ↦ φs i (us i a)) l := by
          exact limsup_le_limsup (hus.mono fun i hi ↦ by
            simpa only [add_comm] using hi.apply_add_dissipation_le haI hbI hab)
        _ = _ := hinit.limsup_eq
    rw [heq, add_comm (φ (u b))] at hsum
    lift φ (u b) to ℝ using ⟨h.apply_ne_top hbI, h.apply_ne_bot hbI⟩ with eb
    exact (EReal.addLECancellable_coe eb).add_le_add_iff_right.1 hsum
  exact tendsto_of_le_liminf_of_limsup_le hlower hupperD

end TauCeti
