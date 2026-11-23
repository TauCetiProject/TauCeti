/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Geometry.Manifold.MFDeriv.Parametric.Basic
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Fixed-curve calculus for a varying Riemannian metric

Joint regularity of a metric family gives joint regularity of a fixed curve's squared speed.
For a regular curve, differentiating its speed integral divides the diagonal metric derivative
by twice the speed. The normalized derivative `-2 * r` therefore gives `-r / speed`.
These statements use no curvature, completeness or compactness of the ambient manifold.

The squared-speed argument follows the Chow–Liao–Qin formalization
`pathLength_timeDeriv_of_ricciFlow` (Apache-2.0), whose original notice is:

DifferentialGeometry
Copyright 2026 The DifferentialGeometry contributors

## References

* https://github.com/frenzymath/lean-eval-submissions
* https://github.com/frenzymath/PoincareConjecture
-/

public noncomputable section

open Bundle Filter MeasureTheory Set TauCeti.Manifold
open scoped ContDiff Manifold Topology

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {γ : ℝ → M}
  {g : ℝ → ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}

/-- Joint `C¹` metric regularity and a `C²` curve give joint `C¹` regularity of its
squared speed in metric time and curve parameter. -/
theorem _root_.ContMDiffAt.contDiffAt_metric_speed_sq
    {t u : ℝ} (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I 2 γ u)
    (hg : ContMDiffAt (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 1
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        p.2 ((g p.1).inner p.2)) (t, γ u)) :
    ContDiffAt ℝ 1 (fun p : ℝ × ℝ ↦ (g p.1).inner (γ p.2)
      (curveVelocity I γ p.2) (curveVelocity I γ p.2)) (t, u) := by
  have hbase : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod I) 1
      (fun p : ℝ × ℝ ↦ (p.1, γ p.2)) (t, u) :=
    contMDiffAt_fst.prodMk ((hγ.of_le (by norm_num : (1 : ℕ∞ω) ≤ 2)).comp
      (t, u) contMDiffAt_snd)
  have hcurve : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 2
      (fun p : ℝ × ℝ ↦ γ p.2) (t, u) := by
    simpa +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod,
      Function.comp_def] using hγ.comp (t, u)
        (contMDiffAt_snd : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) 2 Prod.snd (t, u))
  have hv : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) I.tangent 1
      (fun p : ℝ × ℝ ↦ TotalSpace.mk' E (γ p.2) (curveVelocity I γ p.2)) (t, u) := by
    simpa +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] using
      (hcurve.contMDiffAt_curveVelocity_snd (f := fun _ s ↦ γ s) (m := 1) (by norm_num))
  have h := (hg.comp (t, u) hbase).clm_bundle_apply₂
    (F₃ := ℝ) (E₃ := fun _ : M ↦ ℝ) hv hv
  have hh := (contMDiffAt_totalSpace_iff.mp h).2
  simp +instances only [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at hh
  simpa using hh.contDiffAt

/-- A metric family with diagonal derivative `-2 * r` differentiates the speed integral
to the integral of `-r / speed`, along a fixed curve with nonzero velocity. -/
theorem hasDerivAt_integral_speed
    {a b t : ℝ} {r : ℝ → ℝ}
    (hG : ∀ u ∈ uIcc a b, ContDiffAt ℝ 1 (fun p : ℝ × ℝ ↦
      (g p.1).inner (γ p.2) (curveVelocity I γ p.2) (curveVelocity I γ p.2)) (t, u))
    (hvel : ∀ u ∈ uIcc a b, curveVelocity I γ u ≠ 0)
    (hd : ∀ u ∈ uIcc a b, HasDerivAt (fun τ ↦ (g τ).inner (γ u)
      (curveVelocity I γ u) (curveVelocity I γ u)) (-2 * r u) t) :
    HasDerivAt (fun τ ↦ ∫ u in a..b,
      Real.sqrt ((g τ).inner (γ u) (curveVelocity I γ u) (curveVelocity I γ u)))
      (∫ u in a..b, -r u /
        Real.sqrt ((g t).inner (γ u) (curveVelocity I γ u) (curveVelocity I γ u))) t := by
  let G : ℝ × ℝ → ℝ := fun p ↦
    (g p.1).inner (γ p.2) (curveVelocity I γ p.2) (curveVelocity I γ p.2)
  obtain ⟨U, V, hUo, hVo, htU, hV, hGU⟩ :=
    TauCeti.exists_isOpen_prod_contMDiffOn (I' := 𝓘(ℝ, ℝ × ℝ)) (J := 𝓘(ℝ, ℝ))
      isCompact_uIcc (by simp) (fun u hu ↦ (hG u hu).contMDiffAt)
  have hGc : ContDiffOn ℝ 1 G (U ×ˢ V) := hGU.contDiffOn
  let W := (U ×ˢ V) ∩ G ⁻¹' Ioi 0
  have hWo : IsOpen W := hGc.continuousOn.isOpen_inter_preimage (hUo.prod hVo) isOpen_Ioi
  have hL : ContDiffOn ℝ 1 (fun p ↦ Real.sqrt (G p)) W :=
    (hGc.mono inter_subset_left).sqrt fun _ hp ↦ ne_of_gt hp.2
  have hsub : {t} ×ˢ uIcc a b ⊆ W := by
    rintro ⟨τ, u⟩ ⟨hτ, hu⟩
    have hτ : τ = t := mem_singleton_iff.mp hτ
    subst τ
    exact ⟨⟨htU, hV hu⟩, (g t).pos (γ u) _ (hvel u hu)⟩
  obtain ⟨_, hD⟩ := TauCeti.hasDerivAt_intervalIntegral_of_contDiffOn hWo hL hsub
  apply hD.congr_deriv
  apply intervalIntegral.integral_congr
  intro u hu
  have hp : HasDerivAt (fun τ : ℝ ↦ (τ, u)) ((1 : ℝ), (0 : ℝ)) t :=
    (hasDerivAt_id' (x := t)).prodMk (hasDerivAt_const t u)
  have hl := ((hL.differentiableOn one_ne_zero (t, u) (hsub ⟨rfl, hu⟩)).differentiableAt
    (hWo.mem_nhds (hsub ⟨rfl, hu⟩))).hasFDerivAt.comp_hasDerivAt t hp
  have hs := (hd u hu).sqrt (ne_of_gt ((g t).pos (γ u) _ (hvel u hu)))
  dsimp only
  rw [hl.unique hs]
  ring

end Bundle.ContMDiffRiemannianMetric
