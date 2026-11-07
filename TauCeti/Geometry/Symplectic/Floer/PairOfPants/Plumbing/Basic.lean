/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Family
public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Action
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action
import TauCeti.Geometry.Symplectic.Floer.Pullback
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Plumbing pair-of-pants perturbation data along a neck

Composing two pair-of-pants products plugs the output of one pair of pants `S'` into an input
`q ∈ {0, 1}` of another `S`. On the domain this is the plumbing map
`ψ = TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L` of neck length `L`, which glues the
part `Re z > -L` of `S'`, in the end coordinate at `∞`, to the part `Re z < L` of `S`, in the end
coordinate of `q`, into the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`
(`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap_image_union`).

This file glues the Hamiltonian perturbations of the two pairs of pants
(`TauCeti.Floer.pairOfPantsPerturbation`) along the same neck. If the Hamiltonian `Ha ∞` on the
output end of `S'` is the Hamiltonian `Hb q` on the input end of `S`, then on the part of the
neck where both perturbations are cylindrical, the pushforward of the perturbation of `S'` along
`ψ` is the perturbation of `S`: both are `H(t) dt`, and `ψ` is the translation `z ↦ z + L` in end
coordinates (`TauCeti.Floer.pairOfPantsPerturbation_plumbingMap`). The glued datum
`TauCeti.Floer.plumbedPerturbation` uses the pushforward on the half `Re z > L/2` of the end `q`
and the perturbation of `S` elsewhere. It restricts to each of the two given perturbations away
from a collar of width `2` at the end of each piece. For `L > 4`, when these two regions overlap
in an open neck, and for period-one Hamiltonians of class `C^n` (smooth ones, taking `n = ∞`), it
is of class `C^n` on the four-punctured sphere. Its four ends therefore carry
the two input Hamiltonians of `S'` at `c_q` and `ψ(1)`, and the remaining input and output
Hamiltonians of `S`.

The energy identity turns a bound on the integrated curvature `∫ |R_K|` of the perturbation into
an energy bound, so the curvature of the plumbed datum must stay bounded as the neck grows. For
Hamiltonians on any manifold with a two-form, such as a closed symplectic manifold, it does. Off
the half `Re z > L/2` of the end `q` the plumbed datum is the perturbation of `S`, and on that half
its pullback along the affine map `ψ` is the perturbation of `S'`. Since the absolute curvature
integral is invariant under changes of coordinates
(`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_image`), the integrated curvature of
the plumbed datum is at most the sum of the bounds for `S` and `S'` given by
`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`, which
does not depend on `L`. The curvature of the neck itself vanishes, as the datum is `H(t) dt` there.

The energy identity itself holds on the truncation `Σ_R` of the plumbed sphere
(`TauCeti.ThricePuncturedSphere.Puncture.plumbedTruncation`), for `R ≥ L/2`: the part
`Re z ≤ L/2` of the end `q` of the truncation `S_R`, together with the image under `ψ` of the
part `Re z ≥ -L/2` of the end at `∞` of the truncation `S'_R`. The energy over each part is
given by the energy identity of a truncated pair of pants with one end cut short,
`SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_inter_eq_sum_hamiltonianAction`
in the coordinates of `S` and of `S'` respectively, the second after the change of variables
along `ψ`. The two cut loops along the middle of the neck are the same loop, by the
gluing law of the end lifts, and they carry the same Hamiltonian `Hb q = Ha ∞`, with opposite
signs: an input of `S` and the output of `S'`. So their actions cancel, and the energy over `Σ_R`
is the signed sum of the actions of the four boundary loops of `Σ_R` minus the integrated
curvature. With the curvature bound, the energy differs from this sum by at most the six end
bounds, uniformly in `L` and `R`, and for solutions of the Floer equation the action of the output
loop is at most the sum of the actions of the three input loops plus that constant.

## Main definitions

* `TauCeti.Floer.plumbedPerturbation Ha Hb q L`: the perturbation on the plumbed four-punctured
  sphere.

## Main results

* `TauCeti.Floer.pairOfPantsPerturbation_plumbingMap`: the two perturbations match on the neck.
* `TauCeti.Floer.plumbedPerturbation_of_re_endCoord_le`: off the collar `Re z > L - 2` of the end
  `q`, the glued datum is the perturbation of the receiving pair of pants.
* `TauCeti.Floer.plumbedPerturbation_plumbingMap`: off the collar `Re z < 2 - L` of the end at
  `∞`, the pullback of the glued datum along `ψ` is the perturbation of the inserted pair of pants.
* `TauCeti.Floer.contMDiffAt_plumbedPerturbation`: for `L > 4` and period-one Hamiltonians of
  class `C^n`, the glued datum is of class `C^n` on the four-punctured sphere; smooth Hamiltonians
  give a smooth datum.
* `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le`: for
  `L > 4`, the integrated curvature of the glued datum along any map into a manifold is at most
  the sum of bounds for the six end Hamiltonians of the two pairs of pants, uniformly in `L`;
  `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le` is the
  case of a symplectic vector space.
* `TauCeti.SymplecticForm.integral_floerEnergyDensity_plumbedPerturbation_eq_sum_hamiltonianAction`:
  the energy identity on the truncation `Σ_R` of the plumbed sphere, for a symplectic vector space
  target.
* `TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_sum_le`: the
  energy over `Σ_R` differs from the signed sum of the actions of its boundary loops by at most
  the sum of the six end bounds.
* `TauCeti.SymplecticForm.hamiltonianAction_le_sum_add_sum_add_sum_add_sum`: for solutions of the
  Floer equation, the action bound for the output loop of `Σ_R`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on gluing perturbation data for compositions of pair-of-pants products.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on gluing
  perturbation data along strip-like ends.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart realChart_apply contDiff_realChart hasFDerivAt_realChart)

namespace TauCeti.Floer

variable {M : Type*} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]

/-- **The plumbed perturbation is smooth.** For Hamiltonians of period one which are `C^n` on
`ℝ × M`, with matching Hamiltonians on the glued ends and neck length `L > 4`, the plumbed
perturbation is `C^n` on `S₄ × M`, where `S₄ = ℂ ∖ {0, 1, ψ(1)}` is the plumbed four-punctured
sphere. -/
theorem contMDiffAt_plumbedPerturbation {n : ℕ∞} (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1)
    (x : M) :
    ContMDiffAt (𝓘(ℝ, ℂ).prod I) 𝓘(ℝ, ℂ →L[ℝ] ℝ) n
      (fun p : ℂ × M => plumbedPerturbation Ha Hb q L p.1 p.2) (w, x) := by
  exact (contMDiffAt_plumbedPerturbation_family hq hHa hHb hHas hHbs hab hL hw x).comp
    (w, x) (contMDiffAt_const.prodMk contMDiffAt_id)

omit [TopologicalSpace M] [ChartedSpace G M] in
/-- Near a point off the collar `Re z ≥ L - 2` of the end `q`, the plumbed perturbation is the
perturbation of the receiving pair of pants. -/
private theorem eventually_plumbedPerturbation_eq (hq : q ≠ inf) (hab : Hb q = Ha inf) {w : ℂ}
    (hw : w ≠ q.endCenter) (h : (q.endCoord w).re < L - 2) :
    ∀ᶠ w' in 𝓝 w, plumbedPerturbation Ha Hb q L w' = pairOfPantsPerturbation Hb w' := by
  filter_upwards [((q.contDiffAt_re_endCoord hw (n := 0)).continuousAt).eventually
    (gt_mem_nhds h)] with w' hw'
  exact funext fun x => plumbedPerturbation_of_re_endCoord_le hq hab hw'.le x

omit [TopologicalSpace M] [ChartedSpace G M] in
/-- Near a point off the collar `Re z ≤ 2 - L` of the end at `∞` of the inserted pair of pants,
the pullback of the plumbed perturbation along the plumbing map is the perturbation of the
inserted pair of pants. -/
private theorem eventually_plumbedPerturbation_plumbingMap (hq : q ≠ inf) (hab : Hb q = Ha inf)
    {w : ℂ} (hw : w ≠ 0) (h : 2 - L < (inf.endCoord w).re) :
    ∀ᶠ w' in 𝓝 w, ∀ x v, plumbedPerturbation Ha Hb q L (q.plumbingMap L w') x
      (q.plumbingFactor L * v) = pairOfPantsPerturbation Ha w' x v := by
  have hc : ContinuousAt (fun w => (inf.endCoord w).re) w :=
    (inf.contDiffAt_re_endCoord (by simpa using hw) (n := 0)).continuousAt
  filter_upwards [eventually_ne_nhds hw, hc.eventually (lt_mem_nhds h)] with w' hw' h' x v
  exact plumbedPerturbation_plumbingMap hq hab hw' h'.le x v

private theorem contDiff_realChart_plumbingMap (q : Puncture) (L : ℝ) {n : WithTop ℕ∞} :
    ContDiff ℝ n (realChart (q.plumbingMap L)) := by
  have hψ : q.plumbingMap L = fun w => q.endCenter + q.plumbingFactor L * w :=
    funext (plumbingMap_apply q L)
  exact contDiff_realChart (by rw [hψ]; fun_prop)

private theorem injective_realChart_plumbingMap (q : Puncture) (L : ℝ) :
    Injective (realChart (q.plumbingMap L)) := fun a b h ↦ by
  rw [realChart_apply, realChart_apply] at h
  exact Complex.equivRealProdCLM.symm.injective
    (q.plumbingMap_injective L (Complex.equivRealProdCLM.injective h))

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer MeasureTheory

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-- At points other than the four punctures, the components of the plumbed perturbation of `C¹`
Hamiltonians are differentiable in the domain point. -/
private theorem differentiableAt_plumbedPerturbation_domain (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {z : ℝ × ℝ}
    (hz : (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) (x : M) (v : ℂ) :
    DifferentiableAt ℝ
      (fun z' ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z') x v) z := by
  have hK : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1 (fun w ↦ plumbedPerturbation Ha Hb q L w x)
      (Complex.equivRealProdCLM.symm z) :=
    (contMDiffAt_plumbedPerturbation hq hHa hHb hHas hHbs hab hL hz x).comp
      (f := fun w : ℂ ↦ (w, x)) _ (contMDiffAt_id.prodMk contMDiffAt_const)
  exact ((hK.contDiffAt.differentiableAt one_ne_zero).comp z
    Complex.equivRealProdCLM.symm.differentiableAt).clm_apply (differentiableAt_const v)

/-- At points other than the four punctures, the components of the plumbed perturbation of `C¹`
Hamiltonians are differentiable in the target point. -/
private theorem mdifferentiableAt_plumbedPerturbation_target (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1)
    (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ plumbedPerturbation Ha Hb q L w y v) x :=
  (((contMDiffAt_plumbedPerturbation hq hHa hHb hHas hHbs hab hL hw x).comp
    (f := fun y : M ↦ (w, y)) x (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply
    contMDiffAt_const).mdifferentiableAt one_ne_zero

variable [IsManifold I ⊤ M]

/-- Off the collar `Re z ≥ L/2` of the end `q`, the curvature of the plumbed perturbation is the
curvature of the perturbation of the receiving pair of pants. -/
private theorem hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_le (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hab : Hb q = Ha inf) (hL : 4 < L) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter)
    (hre : (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2) :
    ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        z := by
  have hP := (Complex.equivRealProdCLM.symm.continuous.tendsto z).eventually
    (eventually_plumbedPerturbation_eq (L := L) hq hab hz (by linarith))
  exact ω.hamiltonianCurvature_congr_of_eventuallyEq
    (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])
    (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])

/-- Off the collar `Re z ≤ -L/2` of the end at `∞` of the inserted pair of pants, the curvature of
the pullback of the plumbed perturbation along the plumbing chart is the curvature of the
perturbation of the inserted pair of pants. -/
private theorem hamiltonianCurvature_perturbationPullback_plumbedPerturbation
    (ω : SmoothTwoForm I M) (hq : q ≠ inf) (hab : Hb q = Ha inf) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0)
    (hre : 2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    ω.hamiltonianCurvature
        (perturbationPullback (realChart (q.plumbingMap L))
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
            Complex.I) stdComplexLineReal)
        (perturbationPullback (realChart (q.plumbingMap L))
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
            Complex.I) stdComplexLineImag) z =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        z := by
  have hP := (Complex.equivRealProdCLM.symm.continuous.tendsto z).eventually
    (eventually_plumbedPerturbation_plumbingMap (L := L) hq hab hz hre)
  have h₁ : Complex.equivRealProdCLM.symm stdComplexLineReal = 1 := by
    apply Complex.ext <;> simp [stdComplexLineReal_eq]
  have hI : Complex.equivRealProdCLM.symm stdComplexLineImag = Complex.I := by
    apply Complex.ext <;> simp [stdComplexLineImag_eq]
  exact ω.hamiltonianCurvature_congr_of_eventuallyEq
    (hP.mono fun z' hz' ↦ funext fun x ↦ by
      rw [perturbationPullback_realChart _ (q.hasDerivAt_plumbingMap L _), h₁, hz'])
    (hP.mono fun z' hz' ↦ funext fun x ↦ by
      rw [perturbationPullback_realChart _ (q.hasDerivAt_plumbingMap L _), hI, hz'])

/-- On the part `A` of the plane off the collar `Re z > L/2` of the end `q`, the integrated
curvature of the plumbed perturbation is that of the receiving pair of pants, and so is at most
the sum of bounds for its end Hamiltonians. -/
private theorem setLIntegral_enorm_hamiltonianCurvature_plumbedPerturbation_le_receiving
    (ω : SmoothTwoForm I M) (hq : q ≠ inf) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L)
    {Bb : Puncture → ℝ} (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → M) :
    ∫⁻ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ q.endCenter ∧
        (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2},
      ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ r, ENNReal.ofReal (Bb r) := by
  have hAm : MeasurableSet {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ q.endCenter ∧
      (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2} :=
    ((measurableSet_singleton q.endCenter).compl.preimage
      Complex.equivRealProdCLM.symm.continuous.measurable).inter
      (measurableSet_le (measurable_re_endCoord q) measurable_const)
  calc _ ≤ ∫⁻ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ q.endCenter ∧
          (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2},
        ‖ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z)‖ₑ :=
        setLIntegral_mono' hAm fun z hz ↦ by
          rw [hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_le ω hq hab hL hz.1 hz.2]
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hHb hHbs hBb u

/-- On the image under the plumbing chart of the part `S` of the inserted pair of pants off the
collar `Re z < -L/2` of its end at `∞`, the integrated curvature of the plumbed perturbation is
that of the inserted pair of pants, and so is at most the sum of bounds for its end
Hamiltonians. -/
private theorem setLIntegral_enorm_hamiltonianCurvature_plumbedPerturbation_le_inserted
    (ω : SmoothTwoForm I M) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L)
    {Ba : Puncture → ℝ} (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (u : ℝ × ℝ → M) :
    ∫⁻ z in realChart (q.plumbingMap L) '' {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1 ∧
        -(L / 2) < (inf.endCoord (Complex.equivRealProdCLM.symm z)).re},
      ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ r, ENNReal.ofReal (Ba r) := by
  set S := {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1 ∧
    -(L / 2) < (inf.endCoord (Complex.equivRealProdCLM.symm z)).re}
  have hSm : MeasurableSet S :=
    ((measurableSet_singleton 0).compl.preimage
      Complex.equivRealProdCLM.symm.continuous.measurable).inter
      (((measurableSet_singleton 1).compl.preimage
        Complex.equivRealProdCLM.symm.continuous.measurable).inter
        (measurableSet_lt measurable_const (measurable_re_endCoord inf)))
  -- The plumbing chart maps `S` into the plumbed four-punctured sphere, where the plumbed
  -- perturbation is differentiable.
  have hS₄ {w : ℝ × ℝ} (hw : w ∈ S) :
      (Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ 0 ∧
        Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ 1) ∧
      Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ q.plumbingMap L 1 := by
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨q.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos ?_,
      fun h ↦ hw.2.1 (q.plumbingMap_injective L h)⟩
    rw [endSign_eq_one hq, one_mul, re_endCoord_plumbingMap q L hw.1]
    linarith [hw.2.2]
  have hdom {w : ℝ × ℝ} (hw : w ∈ S) (y : M) (v : ℂ) :=
    differentiableAt_plumbedPerturbation_domain hq hHa hHb hHas hHbs hab hL (hS₄ hw) y v
  have htgt {w : ℝ × ℝ} (hw : w ∈ S) (y : M) (v : ℂ) :=
    mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL (hS₄ hw) y v
  rw [ω.lintegral_enorm_hamiltonianCurvature_image hSm (injective_realChart_plumbingMap q L).injOn
    (fun w _ ↦ (contDiff_realChart_plumbingMap q L).contDiffAt)
    (fun w hw ↦ hdom hw _ 1) (fun w hw ↦ hdom hw _ Complex.I)
    (fun w hw ↦ htgt hw _ 1) (fun w hw ↦ htgt hw _ Complex.I)]
  calc _ = ∫⁻ w in S, ‖ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
          w ((u ∘ realChart (q.plumbingMap L)) w)‖ₑ :=
        setLIntegral_congr_fun hSm fun w hw ↦ by
          rw [hamiltonianCurvature_perturbationPullback_plumbedPerturbation ω hq hab hw.1
            (by linarith [hw.2.2]), comp_apply]
    _ ≤ _ := setLIntegral_le_lintegral _ _
    _ ≤ _ := lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le ω hHa hHas hBa _

/-- **The integrated curvature of the plumbed perturbation is bounded uniformly in the neck
length.** Plumb the output end of a pair of pants with period-one `C¹` Hamiltonians `Ha` into the
input end `q` of one with period-one `C¹` Hamiltonians `Hb`, along a neck of length `L > 4`,
where `Hb q = Ha ∞`, and write the components of the plumbed perturbation
`TauCeti.Floer.plumbedPerturbation` in the global coordinate `z = s + i t` of `ℂ` as
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. If `|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, then for every
map `u` into the target the integral of `|R_K(z, u(z))|` over the plane is at most
`∑ r, Ba r + ∑ r, Bb r`. The bound does not depend on `L`. -/
theorem lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → M) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ r, ENNReal.ofReal (Ba r) + ∑ r, ENNReal.ofReal (Bb r) := by
  -- The plane is covered, up to two points, by the part `A` where the plumbed datum is the
  -- datum of the receiving pair of pants, and the image under the plumbing chart of a part `S`
  -- of the inserted pair of pants where its pullback is the datum of the inserted one.
  set A := {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ q.endCenter ∧
    (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}
  set S := {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1 ∧
    -(L / 2) < (inf.endCoord (Complex.equivRealProdCLM.symm z)).re}
  set N : Set (ℝ × ℝ) :=
    {Complex.equivRealProdCLM q.endCenter, Complex.equivRealProdCLM (q.plumbingMap L 1)}
  have hcover : univ ⊆ (A ∪ realChart (q.plumbingMap L) '' S) ∪ N := by
    intro z _
    by_cases h₀ : Complex.equivRealProdCLM.symm z = q.endCenter
    · exact Or.inr (by simp [N, ← h₀])
    by_cases h₁ : Complex.equivRealProdCLM.symm z = q.plumbingMap L 1
    · exact Or.inr (by simp [N, ← h₁])
    by_cases hle : (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2
    · exact Or.inl (Or.inl ⟨h₀, hle⟩)
    refine Or.inl (Or.inr ⟨Complex.equivRealProdCLM
      ((Complex.equivRealProdCLM.symm z - q.endCenter) / q.plumbingFactor L), ?_, ?_⟩)
    · refine ⟨?_, ?_, ?_⟩ <;> rw [ContinuousLinearEquiv.symm_apply_apply]
      · exact q.sub_endCenter_div_plumbingFactor_ne_zero L h₀
      · intro h
        exact h₁ (by rw [← h, plumbingMap_sub_endCenter_div])
      · rw [re_endCoord_inf_sub_endCenter_div q L h₀]
        linarith
    · rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply,
        plumbingMap_sub_endCenter_div, ContinuousLinearEquiv.apply_symm_apply]
  have hN : volume N = 0 := by
    rw [Measure.volume_eq_prod]
    exact (Set.toFinite N).measure_zero _
  calc _ = ∫⁻ z in univ, ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ := (setLIntegral_univ _).symm
    _ ≤ _ := lintegral_mono_set hcover
    _ ≤ _ := lintegral_union_le _ _ _
    _ = _ := by rw [setLIntegral_measure_zero _ _ hN, add_zero]
    _ ≤ _ := lintegral_union_le _ _ _
    _ ≤ ∑ r, ENNReal.ofReal (Bb r) + ∑ r, ENNReal.ofReal (Ba r) :=
        add_le_add
          (setLIntegral_enorm_hamiltonianCurvature_plumbedPerturbation_le_receiving ω hq hHb hHbs
            hab hL hBb u)
          (setLIntegral_enorm_hamiltonianCurvature_plumbedPerturbation_le_inserted ω hq hHa hHb
            hHas hHbs hab hL hBa u)
    _ = _ := add_comm _ _

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

open Floer MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ha Hb : Puncture → ℝ → V → ℝ} {q : Puncture} {L : ℝ}

/-- **The integrated curvature of the plumbed perturbation is bounded uniformly in the neck
length.** This is the vector-space case of
`TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le`: for
period-one `C¹` Hamiltonians on a symplectic vector space with `|Ha r| ≤ Ba r` and
`|Hb r| ≤ Bb r`, and every map `u` into it, the integral of `|R_K(z, u(z))|` over the plane is at
most `∑ r, Ba r + ∑ r, Bb r`, for every neck length `L > 4`. -/
theorem lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → V) :
    ∫⁻ z, ‖ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)‖ₑ ≤ ∑ r, ENNReal.ofReal (Ba r) + ∑ r, ENNReal.ofReal (Bb r) := by
  simpa using ω.constSmooth.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHas r).contMDiff)
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hab hL hBa hBb u


omit [FiniteDimensional ℝ V] in
/-- At points other than the four punctures, the plumbed perturbation of `C¹` Hamiltonians is
`C¹` jointly in the domain and target points. -/
private theorem contDiffAt_plumbedPerturbation_prod (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1)
    (x : V) :
    ContDiffAt ℝ 1 (fun p : ℂ × V ↦ plumbedPerturbation Ha Hb q L p.1 p.2) (w, x) := by
  have hmfd {H : Puncture → ℝ → V → ℝ} (hH : ∀ r, ContDiff ℝ 1 (uncurry (H r))) (r : Puncture) :
      ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ, ℝ) 1 (uncurry (H r)) := by
    have h := (hH r).contMDiff
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have h := contMDiffAt_plumbedPerturbation (n := 1) hq hHa hHb (hmfd hHas) (hmfd hHbs) hab hL
    hw x
  have h' : ContMDiffAt 𝓘(ℝ, ℂ × V) 𝓘(ℝ, ℂ →L[ℝ] ℝ) 1
      (fun p : ℂ × V ↦ plumbedPerturbation Ha Hb q L p.1 p.2) (w, x) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact h
  exact h'.contDiffAt

/-! ### The energy identity on the plumbed four-punctured sphere -/

/-- The plumbing chart preserves orientation: its derivative is multiplication by the complex
number `ψ'`, whose real determinant is `|ψ'|²`. -/
private theorem det_fderiv_realChart_plumbingMap_nonneg (q : Puncture) (L : ℝ) (z : ℝ × ℝ) :
    0 ≤ (fderiv ℝ (realChart (q.plumbingMap L)) z).det := by
  rw [(hasFDerivAt_realChart (q.hasDerivAt_plumbingMap L _)).fderiv]
  -- The determinant is invariant under the conjugation by `ℂ ≃ ℝ × ℝ`.
  have hconj := LinearMap.det_conj
    (((ContinuousLinearMap.toSpanSingleton ℂ (q.plumbingFactor L)).restrictScalars ℝ :
      ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) Complex.equivRealProdCLM.toLinearEquiv
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_comp,
    ContinuousLinearMap.toLinearMap_comp]
  -- The linear maps underlying `ℂ ≃L[ℝ] ℝ × ℝ` as a continuous linear map and as a linear
  -- equivalence agree only definitionally, so `rw` does not see `hconj` in the goal.
  erw [hconj]
  simp [LinearMap.det_restrictScalars, Algebra.norm_complex_apply, Complex.normSq_nonneg]

omit [FiniteDimensional ℝ V] in
/-- In the real coordinates, the plumbed perturbation of `C¹` Hamiltonians is `C¹` at the points
of the four-punctured sphere. -/
private theorem contDiffAt_uncurry_plumbedPerturbation (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {z : ℝ × ℝ}
    (hz : (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) (x : V) (v : ℂ) :
    ContDiffAt ℝ 1
      (uncurry fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v)
      (z, x) :=
  ((contDiffAt_plumbedPerturbation_prod hq hHa hHb hHas hHbs hab hL hz x).comp
    (f := fun p : (ℝ × ℝ) × V ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x)
    ((Complex.equivRealProdCLM.symm.contDiff.comp contDiff_fst).prodMk
      contDiff_snd).contDiffAt).clm_apply contDiffAt_const

/-- The truncated plumbed sphere, in the real coordinates, is the part of the truncation of the
receiving pair of pants inside the circle `Re z = L/2` of the end `q`, together with the image
under the plumbing chart of the part of the truncation of the inserted pair of pants outside the
circle `Re z = -L/2` of its end at `∞`. -/
private theorem preimage_plumbedTruncation (hq : q ≠ inf) (L R : ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R =
      (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}) ∪
      realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}) := by
  ext z
  simp only [plumbedTruncation_def, mem_preimage, mem_union, mem_inter_iff, mem_ofPred_eq,
    mem_image, endSign_eq_one hq, one_mul, endSign_inf, neg_one_mul, neg_le]
  constructor
  · rintro (h | ⟨w, hw, hwz⟩)
    · exact Or.inl h
    · refine Or.inr ⟨Complex.equivRealProdCLM w, by
        rw [ContinuousLinearEquiv.symm_apply_apply]; exact hw, ?_⟩
      rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, hwz,
        ContinuousLinearEquiv.apply_symm_apply]
  · rintro (h | ⟨w, hw, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨Complex.equivRealProdCLM.symm w, hw, ?_⟩
      rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The two parts of the truncated plumbed sphere meet in the circle `Re z = L/2` of the end `q`,
which is a null set. -/
private theorem volume_inter_image_realChart_plumbingMap (hq : q ≠ inf) {L : ℝ} (hL : 0 < L)
    (R : ℝ) :
    volume ((Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}) ∩
      realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2})) =
      0 := by
  refine measure_mono_null (t := endChart q '' ({L / 2} ×ˢ Ico 0 1)) ?_ ?_
  · rintro z ⟨hzA, w, hwB, rfl⟩
    have hw0 : Complex.equivRealProdCLM.symm w ≠ 0 := (mem_truncation.1 hwB.1).1
    have h₁ : q.endSign *
        (q.endCoord (Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w))).re ≤ L / 2 :=
      hzA.2
    have h₂ : inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm w)).re ≤ L / 2 :=
      hwB.2
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply,
      re_endCoord_plumbingMap q L hw0, endSign_eq_one hq, one_mul] at h₁
    rw [endSign_inf] at h₂
    rw [image_endChart_prod_Ico fun s hs ↦ by
      rw [mem_singleton_iff.1 hs, endSign_eq_one hq]; linarith]
    refine ⟨⟨(mem_truncation.1 hzA.1).1, (mem_truncation.1 hzA.1).2.1⟩, ?_⟩
    rw [mem_singleton_iff, realChart_apply, ContinuousLinearEquiv.symm_apply_apply,
      re_endCoord_plumbingMap q L hw0]
    linarith
  · rw [Measure.volume_eq_prod]
    have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _
      (fun w _ ↦ (hasFDerivAt_endChart q w).differentiableAt.differentiableWithinAt) ?_
    rw [Measure.prod_prod]
    simp

/-- **The energy on the receiving part of the truncated plumbed sphere.** Inside the circle
`Re z = L/2` of the end `q` the plumbed datum is the datum of the receiving pair of pants, so the
energy there is given by the energy identity of that pair of pants with the end `q` cut short. -/
private theorem integral_floerEnergyDensity_plumbedPerturbation_receiving (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : ℝ} (hR : L / 2 ≤ R) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2},
        ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      (∑ r ∈ Finset.univ.erase q, r.endSign * ω.hamiltonianAction (Hb r)
          (fun t ↦ u (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) +
        ω.hamiltonianAction (Hb q) (fun t ↦ u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
            {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2},
          ω.hamiltonianCurvature
            (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
              Complex.I) z (u z) := by
  set A : Set (ℝ × ℝ) := Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
    {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2} with hA
  have hAm : MeasurableSet A :=
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_truncation R)).isClosed.measurableSet.inter
      (measurableSet_le ((measurable_re_endCoord q).const_mul _) measurable_const)
  have hAre {z : ℝ × ℝ} (hz : z ∈ A) :
      (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2 := by
    have h : q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2 := hz.2
    rwa [endSign_eq_one hq, one_mul] at h
  have h := integral_floerEnergyDensity_pairOfPantsPerturbation_inter_eq_sum_hamiltonianAction
    ω hHb hHbs q (c := L / 2) (by linarith) hR (u := u) (hu.mono fun z hz ↦ ⟨⟨hz.1, hz.2.1⟩,
      fun h ↦ by
        have h' := hz.2.2
        rw [h, re_endCoord_plumbingMap q L one_ne_zero, endSign_eq_one hq, one_mul] at h'
        linarith [re_endCoord_inf_one_pos]⟩)
  rw [← hA, endSign_eq_one hq, one_mul, one_mul] at h
  have hAE : ∫ z in A, ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z = ∫ z in A, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z :=
    setIntegral_congr_fun hAm fun z hz ↦ ω.floerEnergyDensity_congr_perturbation u
      (funext fun x ↦ by
        rw [plumbedPerturbation_of_re_endCoord_le hq hab (by linarith [hAre hz]) x])
      (funext fun x ↦ by
        rw [plumbedPerturbation_of_re_endCoord_le hq hab (by linarith [hAre hz]) x])
  have hAR : ∫ z in A, ω.hamiltonianCurvature
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) = ∫ z in A, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) :=
    setIntegral_congr_fun hAm fun z hz ↦ by
      rw [← hamiltonianCurvature_constSmooth, ← hamiltonianCurvature_constSmooth,
        ω.constSmooth.hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_le hq hab hL
          (ne_endCenter ⟨(mem_truncation.1 hz.1).1, (mem_truncation.1 hz.1).2.1⟩ q) (hAre hz)]
  rw [hAE, hAR, h]

/-- **The energy on the inserted part of the truncated plumbed sphere.** Outside the circle
`Re z = -L/2` of the end at `∞` of the inserted pair of pants, the pullback of the plumbed datum
along the plumbing chart is the datum of the inserted pair of pants, so the energy over the image
of that part is given by the energy identity of the inserted pair of pants with its end at `∞`
cut short. Its loop along the cut is the loop along the circle `Re z = L/2` of the end `q`. -/
private theorem integral_floerEnergyDensity_plumbedPerturbation_inserted (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : ℝ} (hR : L / 2 ≤ R) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}),
        ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      (∑ r ∈ Finset.univ.erase inf, ω.hamiltonianAction (Ha r)
          (fun t ↦ u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) -
        ω.hamiltonianAction (Hb q) (fun t ↦ u (Complex.equivRealProdCLM
          (q.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))) -
        ∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
            {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}),
          ω.hamiltonianCurvature
            (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
              Complex.I) z (u z) := by
  set B : Set (ℝ × ℝ) := Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
    {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2} with hB
  have hBm : MeasurableSet B :=
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_truncation R)).isClosed.measurableSet.inter
      (measurableSet_le ((measurable_re_endCoord inf).const_mul _) measurable_const)
  have hB0 {w : ℝ × ℝ} (hw : w ∈ B) : Complex.equivRealProdCLM.symm w ≠ 0 :=
    (mem_truncation.1 hw.1).1
  have hBre {w : ℝ × ℝ} (hw : w ∈ B) :
      -(L / 2) ≤ (inf.endCoord (Complex.equivRealProdCLM.symm w)).re := by
    have h : inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm w)).re ≤ L / 2 := hw.2
    rw [endSign_inf] at h
    linarith
  -- The plumbing chart maps `B` into the four-punctured sphere, where `u` and the plumbed datum
  -- are differentiable.
  have hBψ {w : ℝ × ℝ} (hw : w ∈ B) :
      (Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ 0 ∧
      Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ 1) ∧
      Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ q.plumbingMap L 1 :=
    plumbedTruncation_subset hq (by linarith) R
      (by rw [preimage_plumbedTruncation hq] at *; exact Or.inr (mem_image_of_mem _ hw) :
        realChart (q.plumbingMap L) w ∈ Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R)
  have hS₄o : IsOpen {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} :=
    ((isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).inter
      (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const)).inter
      (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const)
  have hK {w : ℝ × ℝ} (hw : w ∈ B) (y : V) (v : ℂ) := (contDiffAt_uncurry_plumbedPerturbation
    hq hHa hHb hHas hHbs hab hL (hBψ hw) y v).differentiableAt one_ne_zero
  have htgt {w : ℝ × ℝ} (hw : w ∈ B) (y : V) (v : ℂ) : DifferentiableAt ℝ
      (fun y ↦ plumbedPerturbation Ha Hb q L
        (Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w)) y v) y :=
    (hK hw y v).comp _ ((differentiableAt_const _).prodMk differentiableAt_id)
  have hdom {w : ℝ × ℝ} (hw : w ∈ B) (y : V) (v : ℂ) : DifferentiableAt ℝ
      (fun z ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) y v)
      (realChart (q.plumbingMap L) w) :=
    (hK hw y v).comp (f := fun z : ℝ × ℝ ↦ (z, y)) (realChart (q.plumbingMap L) w)
      (differentiableAt_id.prodMk (differentiableAt_const y))
  have hpull {w : ℝ × ℝ} (hw : w ∈ B) (v : ℂ) (x : V) :
      plumbedPerturbation Ha Hb q L (q.plumbingMap L (Complex.equivRealProdCLM.symm w)) x
        (q.plumbingFactor L * v) =
        pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm w) x v :=
    plumbedPerturbation_plumbingMap hq hab (hB0 hw) (by linarith [hBre hw]) x v
  -- Change variables along the plumbing chart, in both integrals.
  have hBE : ∫ z in realChart (q.plumbingMap L) '' B, ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z = ∫ w in B, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.plumbingMap L)) w := by
    rw [ω.integral_floerEnergyDensity_image hBm (injective_realChart_plumbingMap q L).injOn
      (fun w _ ↦ (contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero w)
      (fun w _ ↦ det_fderiv_realChart_plumbingMap_nonneg q L w)
      (fun w hw ↦ (hu.differentiableOn two_ne_zero _ (hBψ hw)).differentiableAt
        (hS₄o.mem_nhds (hBψ hw)))
      (fun w hw ↦ htgt hw _ 1) (fun w hw ↦ htgt hw _ Complex.I)]
    refine setIntegral_congr_fun hBm fun w hw ↦ ω.floerEnergyDensity_congr_perturbation _
      (funext fun x ↦ ?_) (funext fun x ↦ ?_)
    · rw [perturbationPullback_realChart _ (q.hasDerivAt_plumbingMap L _),
        equivRealProdCLM_symm_stdComplexLineReal, hpull hw]
    · rw [perturbationPullback_realChart _ (q.hasDerivAt_plumbingMap L _),
        equivRealProdCLM_symm_stdComplexLineImag, hpull hw]
  have hBR : ∫ z in realChart (q.plumbingMap L) '' B, ω.hamiltonianCurvature
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z) = ∫ w in B, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w ((u ∘ realChart (q.plumbingMap L)) w) := by
    rw [ω.integral_hamiltonianCurvature_image hBm (injective_realChart_plumbingMap q L).injOn
      (fun w _ ↦ (contDiff_realChart_plumbingMap q L).contDiffAt)
      (fun w _ ↦ det_fderiv_realChart_plumbingMap_nonneg q L w)
      (fun w hw ↦ hdom hw _ 1) (fun w hw ↦ hdom hw _ Complex.I)
      (fun w hw ↦ htgt hw _ 1) (fun w hw ↦ htgt hw _ Complex.I)]
    exact setIntegral_congr_fun hBm fun w hw ↦ by
      rw [← hamiltonianCurvature_constSmooth, ← hamiltonianCurvature_constSmooth,
        ω.constSmooth.hamiltonianCurvature_perturbationPullback_plumbedPerturbation hq hab
          (hB0 hw) (by linarith [hBre hw]), comp_apply]
  rw [hBE, hBR]
  -- The energy identity of the inserted pair of pants with its end at `∞` cut short.
  have h := integral_floerEnergyDensity_pairOfPantsPerturbation_inter_eq_sum_hamiltonianAction
    ω hHa hHas inf (c := L / 2) (by linarith) hR (u := u ∘ realChart (q.plumbingMap L))
    (hu.comp (contDiff_realChart_plumbingMap q L).contDiffOn fun z hz ↦ by
      have hre : -(inf.endCoord (Complex.equivRealProdCLM.symm z)).re < L / 2 + 1 := by
        simpa [endSign_inf] using hz.2.2
      refine ⟨q.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos ?_, fun h ↦ hz.2.1 ?_⟩
      · rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply, endSign_eq_one hq,
          one_mul, re_endCoord_plumbingMap q L hz.1]
        linarith
      · rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply] at h
        exact q.plumbingMap_injective L h)
  -- The loop along the cut is the loop along the circle `Re z = L/2` of the end `q`, and the
  -- loops along the input ends are the images under the plumbing map.
  have hneck : (fun t : ℝ ↦ (u ∘ realChart (q.plumbingMap L)) (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(inf.endSign * (L / 2)) + ↑t * Complex.I)))) =
      fun t : ℝ ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I))) := by
    funext t
    rw [comp_apply, realChart_apply, ContinuousLinearEquiv.symm_apply_apply,
      ← cylindricalEndLift_add_ofReal, endSign_inf]
    congr 3
    push_cast
    ring
  have hsum : ∑ r ∈ Finset.univ.erase inf, r.endSign * ω.hamiltonianAction (Ha r)
      (fun t ↦ (u ∘ realChart (q.plumbingMap L)) (Complex.equivRealProdCLM
        (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) =
      ∑ r ∈ Finset.univ.erase inf, ω.hamiltonianAction (Ha r)
        (fun t ↦ u (Complex.equivRealProdCLM
          (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) :=
    Finset.sum_congr rfl fun r hr ↦ by
      simp only [endSign_eq_one (Finset.ne_of_mem_erase hr), one_mul, comp_apply,
        realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
  rw [← hB, hneck, hsum, ← hab, endSign_inf, neg_one_mul] at h
  linarith

/-- **The energy identity on the truncated plumbed four-punctured sphere.** Plumb the output end
of a pair of pants with period-one `C¹` Hamiltonians `Ha` into the input end `q` of one with
period-one `C¹` Hamiltonians `Hb`, along a neck of length `L > 4`, where `Hb q = Ha ∞`, and let
`K` be the plumbed perturbation `TauCeti.Floer.plumbedPerturbation`, with components
`K_s(z) = K(z)(1)` and `K_t(z) = K(z)(i)`. Let `u` be a map which is `C²` on the four-punctured
sphere `ℂ ∖ {0, 1, ψ(1)}`. For `R ≥ L / 2` the Floer energy of `u` over the truncated plumbed
sphere `Σ_R = q.plumbedTruncation L R` is the signed sum of the Hamiltonian actions of its four
boundary loops, minus the integrated curvature:

`∫_{Σ_R} E = ∑_{r ≠ q} ±A_{Hb r}(ℓ_r) + ∑_{r ≠ ∞} A_{Ha r}(ψ ∘ ℓ'_r) - ∫_{Σ_R} R_K(u)`.

Here `ℓ_r(t) = u(φ_r(±R + i t))` are the loops along the circles `±s = R` of the two remaining ends
of the receiving pair of pants, and `(ψ ∘ ℓ'_r)(t) = u(ψ(φ_r(R + i t)))` are the images under the
plumbing map `ψ` of the loops along the circles `s = R` of the two input ends of the inserted
one. The loops along the middle of the neck cancel. -/
theorem integral_floerEnergyDensity_plumbedPerturbation_eq_sum_hamiltonianAction
    (ω : SymplecticForm V) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hab : Hb q = Ha inf) (hL : 4 < L) {R : ℝ}
    (hR : L / 2 ≤ R) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∑ r ∈ Finset.univ.erase q, r.endSign * ω.hamiltonianAction (Hb r)
          (fun t ↦ u (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) +
        (∑ r ∈ Finset.univ.erase inf, ω.hamiltonianAction (Ha r)
          (fun t ↦ u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set S₄ : Set (ℝ × ℝ) := {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}
  -- Both integrands are continuous on the four-punctured sphere, which contains the compact set
  -- `Σ_R`, so they are integrable over it.
  have hS₄o : IsOpen S₄ :=
    ((isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const).inter
      (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const)).inter
      (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const)
  have hPS₄ : Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R ⊆ S₄ := fun z hz ↦
    plumbedTruncation_subset hq (by linarith) R hz
  have hPc : IsCompact (Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_plumbedTruncation q L R)
  have hK (v : ℂ) : ContDiffOn ℝ 1
      (uncurry fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v)
      (S₄ ×ˢ univ) := fun p hp ↦
    (contDiffAt_uncurry_plumbedPerturbation hq hHa hHb hHas hHbs hab hL hp.1 p.2
      v).contDiffWithinAt
  have hEint := ((ω.continuousOn_floerEnergyDensity hS₄o (hu.of_le one_le_two) (hK 1)
    (hK Complex.I)).mono hPS₄).integrableOn_compact (μ := volume) hPc
  have hRint := ((ω.continuousOn_hamiltonianCurvature_comp hS₄o hu.continuousOn (hK 1)
    (hK Complex.I)).mono hPS₄).integrableOn_compact (μ := volume) hPc
  -- Split `Σ_R` into its receiving and inserted parts, which meet in a null set.
  have hψBm : MeasurableSet (realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹'
      truncation R ∩
        {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2})) :=
    measurable_image_of_fderivWithin
      ((Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
        (isCompact_truncation R)).isClosed.measurableSet.inter
        (measurableSet_le ((measurable_re_endCoord inf).const_mul _) measurable_const))
      (fun w _ ↦ ((contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero
        w).hasFDerivAt.hasFDerivWithinAt) (injective_realChart_plumbingMap q L).injOn
  have hsplit (f : ℝ × ℝ → ℝ)
      (hf : IntegrableOn f (Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R)) :=
    setIntegral_union₀ (volume_inter_image_realChart_plumbingMap hq (by linarith) R)
      hψBm.nullMeasurableSet
      ((preimage_plumbedTruncation hq L R ▸ hf).mono_set subset_union_left)
      ((preimage_plumbedTruncation hq L R ▸ hf).mono_set subset_union_right)
  rw [preimage_plumbedTruncation hq L R, hsplit _ hEint, hsplit _ hRint,
    integral_floerEnergyDensity_plumbedPerturbation_receiving ω hq hHb hHbs hab hL hR hu,
    integral_floerEnergyDensity_plumbedPerturbation_inserted ω hq hHa hHb hHas hHbs hab hL hR hu]
  ring

/-- **The energy and the actions on a truncated plumbed sphere.** Under the hypotheses of
`SymplecticForm.integral_floerEnergyDensity_plumbedPerturbation_eq_sum_hamiltonianAction`, if
moreover the end Hamiltonians are bounded, `|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, then the Floer
energy over `Σ_R` differs from the signed sum of the actions of its four boundary loops by at most
`∑ r, Ba r + ∑ r, Bb r`, uniformly in the neck length `L` and in `R`. -/
theorem abs_integral_floerEnergyDensity_plumbedPerturbation_sub_sum_le
    (ω : SymplecticForm V) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hab : Hb q = Ha inf) (hL : 4 < L)
    {Ba Bb : Puncture → ℝ} (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r)
    {R : ℝ} (hR : L / 2 ≤ R) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      ((∑ r ∈ Finset.univ.erase q, r.endSign * ω.hamiltonianAction (Hb r)
          (fun t ↦ u (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) +
        ∑ r ∈ Finset.univ.erase inf, ω.hamiltonianAction (Ha r)
          (fun t ↦ u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))))| ≤
      ∑ r, Ba r + ∑ r, Bb r := by
  rw [integral_floerEnergyDensity_plumbedPerturbation_eq_sum_hamiltonianAction ω hq hHa hHb hHas
    hHbs hab hL hR hu, sub_sub_cancel_left, abs_neg]
  have hBa₀ : 0 ≤ ∑ r, Ba r := Finset.sum_nonneg fun r _ ↦ (abs_nonneg _).trans (hBa r 0 0)
  have hBb₀ : 0 ≤ ∑ r, Bb r := Finset.sum_nonneg fun r _ ↦ (abs_nonneg _).trans (hBb r 0 0)
  rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg hBa₀ hBb₀), ← Real.enorm_eq_ofReal_abs,
    ENNReal.ofReal_add hBa₀ hBb₀,
    ENNReal.ofReal_sum_of_nonneg fun r _ ↦ (abs_nonneg _).trans (hBa r 0 0),
    ENNReal.ofReal_sum_of_nonneg fun r _ ↦ (abs_nonneg _).trans (hBb r 0 0)]
  exact (enorm_integral_le_lintegral_enorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le ω hq hHa hHb hHas hHbs hab hL
      hBa hBb u))

/-- **The action bound on a truncated plumbed sphere.** Under the hypotheses of
`SymplecticForm.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_sum_le`, let `u` solve the
Floer equation `(du - X_K)^{0,1} = 0` on `Σ_R` for almost complex structures `J(z)` tamed by `ω`.
Then the action of the output loop `ℓ_∞(t) = u(φ_∞(-R + i t))` is at most the sum of the actions
of the three input loops, the loop `ℓ_r(t) = u(φ_r(R + i t))` of the remaining input end `r` of the
receiving pair of pants and the loops `u(ψ(φ_r(R + i t)))` of the two input ends of the inserted
one, plus `∑ r, Ba r + ∑ r, Bb r`. The bound does not depend on the neck length `L`. -/
theorem hamiltonianAction_le_sum_add_sum_add_sum_add_sum (ω : SymplecticForm V) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {R : ℝ}
    (hR : L / 2 ≤ R) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z) (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (Hb inf) (fun t ↦ u (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(-R) + ↑t * Complex.I)))) ≤
      (∑ r ∈ (Finset.univ.erase q).erase inf, ω.hamiltonianAction (Hb r)
          (fun t ↦ u (Complex.equivRealProdCLM (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) +
        (∑ r ∈ Finset.univ.erase inf, ω.hamiltonianAction (Ha r)
          (fun t ↦ u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) +
        (∑ r, Ba r + ∑ r, Bb r) := by
  -- The energy over `Σ_R` is nonnegative.
  have hPm : MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R) :=
    (Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
      (isCompact_plumbedTruncation q L R)).isClosed.measurableSet
  have hE := setIntegral_nonneg (μ := volume) hPm fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (abs_integral_floerEnergyDensity_plumbedPerturbation_sub_sum_le ω hq hHa
    hHb hHas hHbs hab hL hBa hBb hR hu)).2
  -- Split the output end off the remaining ends of the receiving pair of pants.
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨fun h ↦ hq h.symm, Finset.mem_univ inf⟩),
    Finset.sum_congr rfl fun r hr ↦ by
      rw [endSign_eq_one (Finset.ne_of_mem_erase hr), one_mul, one_mul],
    endSign_inf, neg_one_mul, neg_one_mul] at h
  linarith

end TauCeti.SymplecticForm
