/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Defs

/-!
# Smooth Hamiltonian data along a plumbing family

The Hamiltonian perturbation on a plumbed four-punctured sphere varies smoothly with the
neck length, not merely on each fixed domain. More precisely, it is jointly `C^n` in length,
domain point and target point on the total space with `L > 4` and with the moving punctures
removed. The target can be an arbitrary manifold, including a product carrying external
parameters. This gives the coefficient regularity needed to differentiate a family of
inhomogeneous Cauchy–Riemann equations before selecting regular perturbations.

The apparent discontinuity in the definition at the moving half-neck is harmless: the two
formulas agree on an open cylindrical overlap. The inserted formula contains both the inverse
plumbing coordinate and the inverse plumbing scale acting on covectors; both vary smoothly at
every finite length. No smooth extension to the broken domain at infinite length is asserted.

The open-overlap argument is the Hamiltonian counterpart of
`TauCeti.Floer.contMDiffAt_plumbedAlmostComplex`. The underlying plumbing and perturbation
conventions follow McDuff–Salamon, *J-holomorphic curves and symplectic topology*, Section 10.9,
and Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 9.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture

namespace TauCeti.Floer

variable {M E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-- The plumbed Hamiltonian one-form is jointly `C^n` in neck length, domain point and target
point, including across the moving half-neck. The four punctures are excluded at the given
length; no compactness, nondegeneracy or symplectic structure on the target is needed. -/
theorem contMDiffAt_plumbedPerturbation_family {n : ℕ∞} (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℂ}
    (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℝ × (ℂ × M) => plumbedPerturbation Ha Hb q p.1 p.2.1 p.2.2)
      (L, (w, x)) := by
  have hc : w ≠ q.endCenter := ne_endCenter hw.1 q
  have hcont : ContinuousAt (fun p : ℝ × (ℂ × M) => (q.endCoord p.2.1).re) (L, (w, x)) :=
    ContinuousAt.comp (g := fun w => (q.endCoord w).re) (f := fun p : ℝ × (ℂ × M) => p.2.1)
      (q.contDiffAt_re_endCoord hc (n := 0)).continuousAt
      (continuousAt_fst.comp continuousAt_snd)
  -- For L > 4 these two open regions cover the seam as well as both pieces.
  rcases lt_or_ge (q.endCoord w).re (L - 2) with hlt | hge
  · refine ((contMDiffAt_pairOfPantsPerturbation hHb hHbs ⟨w, hw.1⟩ x).comp
      (L, (w, x)) contMDiffAt_snd).congr_of_eventuallyEq ?_
    have hdiff : ContinuousAt (fun p : ℝ × (ℂ × M) =>
        p.1 - 2 - (q.endCoord p.2.1).re) (L, (w, x)) :=
      (continuousAt_fst.sub continuousAt_const).sub hcont
    filter_upwards [hdiff.eventually (lt_mem_nhds (by linarith : 0 < L - 2 - (q.endCoord w).re))]
      with p hp
    exact plumbedPerturbation_of_re_endCoord_le hq hab (by linarith) p.2.2
  · have h2 : 2 < (q.endCoord w).re := by linarith
    set w' := (w - q.endCenter) / q.plumbingFactor L
    have hw'0 : w' ≠ 0 := q.sub_endCenter_div_plumbingFactor_ne_zero L hc
    have hw'1 : w' ≠ 1 := fun h => hw.2
      ((q.plumbingMap_sub_endCenter_div L w).symm.trans (congrArg (q.plumbingMap L) h))
    have hcoord : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ) n
        (fun p : ℝ × (ℂ × M) => (p.2.1 - q.endCenter) / q.plumbingFactor p.1) (L, (w, x)) :=
      (q.contDiff_inverse_plumbingMap (n := n)).contDiffAt.contMDiffAt.comp
        (f := fun p : ℝ × (ℂ × M) => (p.1, p.2.1)) (L, (w, x))
        (contMDiffAt_fst.prodMk_space (contMDiffAt_fst.comp _ contMDiffAt_snd))
    -- A covector is pushed forward by composition with multiplication by the inverse scale.
    have hscale : ContDiff ℝ n (fun l : ℝ => (q.plumbingFactor l)⁻¹) :=
      q.contDiff_plumbingFactor.inv (fun l => q.plumbingFactor_ne_zero l)
    have hmul : ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓘(ℝ, ℂ).prod I)) 𝓘(ℝ, ℂ →L[ℝ] ℂ) n
        (fun p : ℝ × (ℂ × M) => ContinuousLinearMap.mul ℝ ℂ (q.plumbingFactor p.1)⁻¹)
        (L, (w, x)) :=
      (((ContinuousLinearMap.mul ℝ ℂ).contDiff.comp hscale).contMDiff.contMDiffAt).comp
        (L, (w, x)) contMDiffAt_fst
    have hK := ((contMDiffAt_pairOfPantsPerturbation hHa hHas ⟨w', hw'0, hw'1⟩ x).comp
      (L, (w, x)) (hcoord.prodMk (contMDiffAt_snd.comp _ contMDiffAt_snd))).clm_comp hmul
    refine hK.congr_of_eventuallyEq ?_
    filter_upwards [hcont.eventually (lt_mem_nhds h2)] with p hp
    exact plumbedPerturbation_eq_comp hq hab hp p.2.2

end TauCeti.Floer
