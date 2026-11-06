/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Family
public import TauCeti.Geometry.Symplectic.Floer.Energy
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature
import TauCeti.Geometry.Symplectic.Floer.Pullback

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
an energy bound, so the curvature of the plumbed datum must stay bounded as the neck grows. For a
symplectic vector space target it does. Off the half `Re z > L/2` of the end `q` the plumbed datum
is the perturbation of `S`, and on that half its pullback along the affine map `ψ` is the
perturbation of `S'`. Since the absolute curvature integral is invariant under changes of
coordinates (`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_image`), the integrated
curvature of the plumbed datum is at most the sum of the bounds for `S` and `S'` given by
`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_pairOfPantsPerturbation_le`, which
does not depend on `L`. The curvature of the neck itself vanishes, as the datum is `H(t) dt` there.

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
* `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le`: for
  `L > 4`, the integrated curvature of the glued datum along any map into a symplectic vector
  space is at most the sum of bounds for the six end Hamiltonians of the two pairs of pants,
  uniformly in `L`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on gluing perturbation data for compositions of pair-of-pants products.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on gluing
  perturbation data along strip-like ends.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart realChart_apply contDiff_realChart)

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

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ha Hb : Puncture → ℝ → V → ℝ} {q : Puncture} {L : ℝ}

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

/-- At points other than the four punctures, the plumbed perturbation of `C¹` Hamiltonians is
differentiable jointly in the domain and target points. -/
private theorem differentiableAt_plumbedPerturbation (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1)
    (x : V) :
    DifferentiableAt ℝ (fun p : ℂ × V ↦ plumbedPerturbation Ha Hb q L p.1 p.2) (w, x) := by
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
  exact h'.contDiffAt.differentiableAt one_ne_zero

/-- The longitudinal coordinate of an end, in the real coordinates, is measurable. -/
private theorem measurable_re_endCoord (r : Puncture) :
    Measurable fun z : ℝ × ℝ ↦ (r.endCoord (Complex.equivRealProdCLM.symm z)).re := by
  simp_rw [re_endCoord]
  exact (Real.measurable_log.comp (by fun_prop : Continuous fun z : ℝ × ℝ ↦
    ‖(Complex.equivRealProdCLM.symm z - r.endCenter) / r.endScale‖).measurable).neg.div_const _

variable [FiniteDimensional ℝ V]

/-- Off the collar `Re z ≥ L/2` of the end `q`, the curvature of the plumbed perturbation is the
curvature of the perturbation of the receiving pair of pants. -/
private theorem hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_le (ω : SymplecticForm V)
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
    (ω : SymplecticForm V) (hq : q ≠ inf) (hab : Hb q = Ha inf) (hL : 4 < L) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0)
    (hre : -(L / 2) < (inf.endCoord (Complex.equivRealProdCLM.symm z)).re) :
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
    (eventually_plumbedPerturbation_plumbingMap (L := L) hq hab hz (by linarith))
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
    (ω : SymplecticForm V) (hq : q ≠ inf) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hab : Hb q = Ha inf) (hL : 4 < L)
    {Bb : Puncture → ℝ} (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → V) :
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
    (ω : SymplecticForm V) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hab : Hb q = Ha inf) (hL : 4 < L)
    {Ba : Puncture → ℝ} (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (u : ℝ × ℝ → V) :
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
  have hdiff {w : ℝ × ℝ} (hw : w ∈ S) (y : V) :
      DifferentiableAt ℝ (fun p : ℂ × V ↦ plumbedPerturbation Ha Hb q L p.1 p.2)
        (Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w), y) := by
    refine differentiableAt_plumbedPerturbation hq hHa hHb hHas hHbs hab hL ?_ y
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
    refine ⟨q.ne_zero_and_ne_one_of_endSign_mul_re_endCoord_pos ?_,
      fun h ↦ hw.2.1 (q.plumbingMap_injective L h)⟩
    rw [endSign_eq_one hq, one_mul, re_endCoord_plumbingMap q L hw.1]
    linarith [hw.2.2]
  have hdom {w : ℝ × ℝ} (hw : w ∈ S) (y : V) (v : ℂ) : DifferentiableAt ℝ
      (fun z ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) y v)
      (realChart (q.plumbingMap L) w) :=
    ((hdiff hw y).comp (f := fun z ↦ (Complex.equivRealProdCLM.symm z, y))
      (realChart (q.plumbingMap L) w) (Complex.equivRealProdCLM.symm.differentiableAt.prodMk
        (differentiableAt_const y))).clm_apply (differentiableAt_const v)
  have htgt {w : ℝ × ℝ} (hw : w ∈ S) (y : V) (v : ℂ) : DifferentiableAt ℝ
      (fun y ↦ plumbedPerturbation Ha Hb q L
        (Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w)) y v) y :=
    ((hdiff hw y).comp
      (f := fun y ↦ (Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w), y))
      y ((differentiableAt_const _).prodMk differentiableAt_id)).clm_apply
      (differentiableAt_const v)
  rw [ω.lintegral_enorm_hamiltonianCurvature_image hSm (injective_realChart_plumbingMap q L).injOn
    (fun w _ ↦ (contDiff_realChart_plumbingMap q L).contDiffAt)
    (fun w hw ↦ hdom hw _ 1) (fun w hw ↦ hdom hw _ Complex.I)
    (fun w hw ↦ htgt hw _ 1) (fun w hw ↦ htgt hw _ Complex.I)]
  calc _ = ∫⁻ w in S, ‖ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
          w ((u ∘ realChart (q.plumbingMap L)) w)‖ₑ :=
        setLIntegral_congr_fun hSm fun w hw ↦ by
          rw [hamiltonianCurvature_perturbationPullback_plumbedPerturbation ω hq hab hL hw.1
            hw.2.2, comp_apply]
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
theorem lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → V) :
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

end TauCeti.SymplecticForm
