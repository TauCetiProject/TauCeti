/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Family
public import TauCeti.Geometry.Symplectic.Floer.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Pullback
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Curvature

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

The same comparison along the plumbing chart computes the energy and the integrated curvature of
the plumbed datum over the image of a region of `S'` as those of the perturbation of `S'` along the
pulled-back map, for any manifold target. These are the change-of-variables steps of the energy
identity on the plumbed sphere, which is assembled from the energy identities of the two pairs of
pants in `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Manifold`.

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
* `TauCeti.SmoothTwoForm.hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_lt`,
  `TauCeti.SmoothTwoForm.hamiltonianCurvature_perturbationPullback_plumbedPerturbation`: away
  from the collars where the two data are glued, the curvature of the glued datum, or of its
  pullback along the plumbing chart, is the curvature of the corresponding pair-of-pants datum.
* `TauCeti.SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le`: for
  `L > 4`, the integrated curvature of the glued datum along any map into a manifold is at most
  the sum of bounds for the six end Hamiltonians of the two pairs of pants, uniformly in `L`;
  `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le` is the
  case of a symplectic vector space.
* `TauCeti.SmoothTwoForm.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le`,
  `TauCeti.SymplecticForm.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le`: the same
  bound for the integral of the curvature over any region.
* `TauCeti.Floer.differentiableAt_plumbedPerturbation_domain`,
  `TauCeti.Floer.mdifferentiableAt_plumbedPerturbation_target`: for `C¹` Hamiltonians, the
  components of the glued datum are differentiable in the domain point and in the target point
  at the points of the four-punctured sphere.
* `TauCeti.SmoothTwoForm.floerEnergyDensity_perturbationPullback_plumbedPerturbation`: off the
  collar of the end at `∞` of the inserted pair of pants, the energy density for the pullback of
  the glued datum along the plumbing chart is the energy density for the inserted datum.
* `TauCeti.SmoothTwoForm.integral_floerEnergyDensity_image_plumbingMap`,
  `TauCeti.SmoothTwoForm.integral_hamiltonianCurvature_image_plumbingMap`,
  `TauCeti.SmoothTwoForm.integrableOn_floerEnergyDensity_image_plumbingMap_iff`,
  `TauCeti.SmoothTwoForm.integrableOn_hamiltonianCurvature_image_plumbingMap_iff`: the energy and
  the integrated curvature of the glued datum over the image of a region under the plumbing chart
  are those of the inserted datum along the pulled-back map, and integrability transfers.
* `TauCeti.Floer.mapsTo_realChart_plumbingMap`,
  `TauCeti.Floer.volume_inter_image_realChart_plumbingMap`: in real coordinates the plumbing chart
  maps the part `Re z > -L` of the inserted pair of pants into the four-punctured sphere, and the
  receiving and inserted parts of a truncated plumbed sphere meet in a null set.
* `TauCeti.Floer.setOf_endSign_mul_re_endCoord_lt_subset_plumbedSphere`,
  `TauCeti.Floer.mapsTo_realChart_plumbingMap_setOf_endSign_mul_re_endCoord_lt`,
  `TauCeti.Floer.preimage_truncation_inter_subset_setOf_lt_re_endCoord_inf`: the parts of the two
  pairs of pants inside the circle `±s = L/2 + 1` of their glued ends lie in, or map into, the
  four-punctured sphere, and the inserted part `±s ≤ L/2` of a truncation lies where the pullback
  of the glued datum is the inserted datum.
* `TauCeti.SmoothTwoForm.floerEnergyDensity_plumbedPerturbation_of_re_endCoord_le`: inside the
  circle `Re z = L - 2` of the end `q`, the energy density for the glued datum is the energy
  density for the receiving datum.
* `TauCeti.Floer.contDiffAt_plumbedPerturbation_prod`,
  `TauCeti.Floer.contDiffAt_uncurry_plumbedPerturbation`: for a vector space target, `L > 4` and
  period-one Hamiltonians of class `C^n`, the glued datum is `C^n` jointly in the domain and
  target points, also in the real coordinates.
* `TauCeti.Floer.perturbationPullback_plumbedPerturbation_of_mem_truncation`: for `L ≥ R + 2`,
  the pullback of the glued datum along `ψ` on the truncation `S_R` of the inserted pair of pants
  is its pair-of-pants datum.
* `TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_realChart_plumbingMap`: for
  `L > 4` and `L > R + 2`, if `u` solves the Floer equation of the glued datum at `ψ(w)` with
  `w ∈ S_R`, then `u ∘ ψ` solves the Floer equation of the inserted pair of pants at `w`.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on gluing perturbation data for compositions of pair-of-pants products.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on gluing
  perturbation data along strip-like ends.
-/

public noncomputable section

open Set Real Manifold Topology Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart realChart_apply contDiff_realChart realChart_injective
  det_fderiv_realChart_nonneg equivRealProdCLM_symm_realChart)

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

/-- At points other than the four punctures, the components of the plumbed perturbation of `C¹`
Hamiltonians are differentiable in the domain point. -/
theorem differentiableAt_plumbedPerturbation_domain (hq : q ≠ inf)
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
theorem mdifferentiableAt_plumbedPerturbation_target (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1)
    (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ) (fun y ↦ plumbedPerturbation Ha Hb q L w y v) x :=
  (((contMDiffAt_plumbedPerturbation hq hHa hHb hHas hHbs hab hL hw x).comp
    (f := fun y : M ↦ (w, y)) x (contMDiffAt_const.prodMk contMDiffAt_id)).clm_apply
    contMDiffAt_const).mdifferentiableAt one_ne_zero

/-- In the real coordinates, the components of the plumbed perturbation of Hamiltonians of class
`C^n` are `C^n` on the plumbed four-punctured sphere times the target manifold. -/
theorem contMDiffOn_uncurry_plumbedPerturbation {n : ℕ∞} (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) n (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) (v : ℂ) :
    ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) n
      (uncurry fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v)
      ({z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  have hφ : ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (𝓘(ℝ, ℂ).prod I) n
      (fun p : (ℝ × ℝ) × M ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x) :=
    (Complex.equivRealProdCLM.symm.contDiff.contMDiff.contMDiffAt.comp _ contMDiffAt_fst).prodMk
      contMDiffAt_snd
  exact (((contMDiffAt_plumbedPerturbation hq hHa hHb hHas hHbs hab hL hz x).comp (z, x)
    hφ).clm_apply contMDiffAt_const).contMDiffWithinAt

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

/-- In real coordinates, the plumbing chart maps the part `Re z > -L` of the inserted
thrice-punctured sphere, measured in the end coordinate at `∞`, into the four-punctured
sphere. -/
theorem mapsTo_realChart_plumbingMap (hq : q ≠ inf) (hL : 0 < L) :
    MapsTo (realChart (q.plumbingMap L))
      {w : ℝ × ℝ | (Complex.equivRealProdCLM.symm w ≠ 0 ∧ Complex.equivRealProdCLM.symm w ≠ 1) ∧
        -L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re}
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := fun w hw ↦ by
  rw [mem_ofPred_eq, realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
  exact mapsTo_plumbingMap hq hL hw

/-- In real coordinates, the part `±s < L/2 + 1` of the end `q` of the receiving thrice-punctured
sphere lies in the four-punctured sphere: the puncture `ψ(1)` lies beyond `±s = L`. -/
theorem setOf_endSign_mul_re_endCoord_lt_subset_plumbedSphere (hq : q ≠ inf) (hL : 4 < L) :
    {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1 ∧
      q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re < L / 2 + 1} ⊆
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := fun z hz ↦ by
  refine ⟨⟨hz.1, hz.2.1⟩, fun h ↦ ?_⟩
  have h' := hz.2.2
  rw [h, re_endCoord_plumbingMap q L one_ne_zero, endSign_eq_one hq, one_mul] at h'
  linarith [re_endCoord_inf_one_pos]

/-- In real coordinates, the plumbing chart maps the part `±s < L/2 + 1` of the end at `∞` of the
inserted thrice-punctured sphere into the four-punctured sphere. -/
theorem mapsTo_realChart_plumbingMap_setOf_endSign_mul_re_endCoord_lt (hq : q ≠ inf)
    (hL : 4 < L) :
    MapsTo (realChart (q.plumbingMap L))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1 ∧
        inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re < L / 2 + 1}
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := fun z hz ↦ by
  have hre : -(inf.endCoord (Complex.equivRealProdCLM.symm z)).re < L / 2 + 1 := by
    simpa [endSign_inf] using hz.2.2
  exact mapsTo_realChart_plumbingMap hq (by linarith) ⟨⟨hz.1, hz.2.1⟩, by linarith⟩

/-- The part `±s ≤ L/2` of the end at `∞` of a truncation of the inserted thrice-punctured sphere
lies in the part `Re z > 2 - L` of that end, where the pullback of the plumbed datum along the
plumbing chart is the datum of the inserted pair of pants. -/
theorem preimage_truncation_inter_subset_setOf_lt_re_endCoord_inf (hL : 4 < L) (R : ℝ) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
        {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2} ⊆
      {w | (Complex.equivRealProdCLM.symm w ≠ 0 ∧ Complex.equivRealProdCLM.symm w ≠ 1) ∧
        2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re} := fun w hw ↦ by
  have h : inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm w)).re ≤ L / 2 := hw.2
  rw [endSign_inf] at h
  exact ⟨truncation_subset _ hw.1, by linarith⟩

open MeasureTheory in
/-- The two parts of the truncated plumbed sphere meet in the circle `Re z = L/2` of the end `q`,
which is a null set. -/
theorem volume_inter_image_realChart_plumbingMap (hq : q ≠ inf) (hL : 0 < L) (R : ℝ) :
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
    rw [equivRealProdCLM_symm_realChart, re_endCoord_plumbingMap q L hw0, endSign_eq_one hq,
      one_mul] at h₁
    rw [endSign_inf] at h₂
    rw [image_endChart_prod_Ico fun s hs ↦ by
      rw [mem_singleton_iff.1 hs, endSign_eq_one hq]; linarith]
    refine ⟨truncation_subset _ hzA.1, ?_⟩
    rw [mem_singleton_iff, equivRealProdCLM_symm_realChart, re_endCoord_plumbingMap q L hw0]
    linarith
  · rw [Measure.volume_eq_prod]
    have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
    refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero _
      (fun w _ ↦ (hasFDerivAt_endChart q w).differentiableAt.differentiableWithinAt) ?_
    rw [Measure.prod_prod]
    simp

omit [TopologicalSpace M] [ChartedSpace G M] in
/-- **The plumbed datum on the inserted truncation.** For neck length `L ≥ R + 2`, the pullback of
the plumbed perturbation along the plumbing map `ψ_L`, at a point of the truncation `S_R` of the
inserted pair of pants and in the real coordinates, is its pair-of-pants perturbation. -/
theorem perturbationPullback_plumbedPerturbation_of_mem_truncation (hq : q ≠ inf)
    (hab : Hb q = Ha inf) {R : ℝ} (hRL : R + 2 ≤ L) {w : ℝ × ℝ}
    (hw : Complex.equivRealProdCLM.symm w ∈ truncation R) (v : ℝ × ℝ) (x : M) :
    perturbationPullback (realChart (q.plumbingMap L))
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        v w x =
      pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm w) x
        (Complex.equivRealProdCLM.symm v) := by
  have h := (mem_truncation.1 hw).2.2 inf
  rw [endSign_inf, neg_one_mul] at h
  rw [perturbationPullback_realChart _ (q.hasDerivAt_plumbingMap L _),
    plumbedPerturbation_plumbingMap hq hab (mem_truncation.1 hw).1 (by linarith)]

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer MeasureTheory

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

variable [IsManifold I ⊤ M]

/-- Off the collar `Re z ≥ L - 2` of the end `q`, the curvature of the plumbed perturbation is
the curvature of the perturbation of the receiving pair of pants. -/
theorem hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_lt (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hab : Hb q = Ha inf) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ q.endCenter)
    (hre : (q.endCoord (Complex.equivRealProdCLM.symm z)).re < L - 2) :
    ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        z := by
  have hP := (Complex.equivRealProdCLM.symm.continuous.tendsto z).eventually
    (eventually_plumbedPerturbation_eq (L := L) hq hab hz hre)
  exact ω.hamiltonianCurvature_congr_of_eventuallyEq
    (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])
    (hP.mono fun z' hz' ↦ funext fun x ↦ by simp only [hz'])

/-- Inside the circle `Re z = L - 2` of the end `q`, the energy density of a map for the plumbed
perturbation is its energy density for the perturbation of the receiving pair of pants. -/
theorem floerEnergyDensity_plumbedPerturbation_of_re_endCoord_le (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hab : Hb q = Ha inf) (u : ℝ × ℝ → M) {z : ℝ × ℝ}
    (hre : (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L - 2) :
    ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z := by
  refine ω.floerEnergyDensity_congr_perturbation u (funext fun x ↦ ?_) (funext fun x ↦ ?_) <;>
    rw [plumbedPerturbation_of_re_endCoord_le hq hab hre x]

/-- Off the collar `Re z ≤ 2 - L` of the end at `∞` of the inserted pair of pants, the curvature of
the pullback of the plumbed perturbation along the plumbing chart is the curvature of the
perturbation of the inserted pair of pants. -/
theorem hamiltonianCurvature_perturbationPullback_plumbedPerturbation
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

/-- Off the collar `Re z ≤ 2 - L` of the end at `∞` of the inserted pair of pants, the energy
density of a map for the pullback of the plumbed perturbation along the plumbing chart is its
energy density for the perturbation of the inserted pair of pants. -/
theorem floerEnergyDensity_perturbationPullback_plumbedPerturbation (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hab : Hb q = Ha inf) (u : ℝ × ℝ → M) {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ 0)
    (hre : 2 - L ≤ (inf.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    ω.floerEnergyDensity
        (perturbationPullback (realChart (q.plumbingMap L))
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
            Complex.I) stdComplexLineReal)
        (perturbationPullback (realChart (q.plumbingMap L))
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
            Complex.I) stdComplexLineImag) u z =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z := by
  refine ω.floerEnergyDensity_congr_perturbation u (funext fun x ↦ ?_) (funext fun x ↦ ?_) <;>
    rw [perturbationPullback_realChart _ (q.hasDerivAt_plumbingMap L _)]
  · rw [equivRealProdCLM_symm_stdComplexLineReal, plumbedPerturbation_plumbingMap hq hab hz hre]
  · rw [equivRealProdCLM_symm_stdComplexLineImag, plumbedPerturbation_plumbingMap hq hab hz hre]

/-- On the part `Re z > 2 - L` of the inserted thrice-punctured sphere, measured in the end
coordinate at `∞`, the energy density of the plumbed perturbation at the image of a point `w`
under the plumbing chart `ψ`, multiplied by the Jacobian of `ψ`, is the energy density of `u ∘ ψ`
for the perturbation of the inserted pair of pants at `w`. -/
private theorem abs_det_mul_floerEnergyDensity_plumbedPerturbation_realChart
    (ω : SmoothTwoForm I M) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → M} {w : ℝ × ℝ}
    (hw : (Complex.equivRealProdCLM.symm w ≠ 0 ∧ Complex.equivRealProdCLM.symm w ≠ 1) ∧
      2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re)
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    |(fderiv ℝ (realChart (q.plumbingMap L)) w).det| * ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x
            Complex.I) u (realChart (q.plumbingMap L) w) =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.plumbingMap L)) w := by
  have hψ := mapsTo_realChart_plumbingMap (L := L) hq (by linarith) ⟨hw.1, by linarith [hw.2]⟩
  rw [abs_of_nonneg (det_fderiv_realChart_nonneg (q.hasDerivAt_plumbingMap L _)),
    ← ω.floerEnergyDensity_perturbationPullback
      ((contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero w)
      (hu.mdifferentiableAt ((isOpen_plumbedSphere q L).mem_nhds hψ))
      (mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL hψ _ 1)
      (mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL hψ _ _),
    ω.floerEnergyDensity_perturbationPullback_plumbedPerturbation hq hab _ hw.1.1 hw.2.le]

/-- **The energy along the plumbing chart, for a manifold target.** On a measurable set `B` in
the part `Re z > 2 - L` of the inserted thrice-punctured sphere, measured in the end coordinate at
`∞`, the pullback of the plumbed perturbation along the plumbing chart `ψ` is the perturbation of
the inserted pair of pants. So the energy of a map `u`, differentiable on the four-punctured
sphere, over `ψ(B)` for the plumbed perturbation is the energy of `u ∘ ψ` over `B` for the
pair-of-pants perturbation of `Ha`. -/
theorem integral_floerEnergyDensity_image_plumbingMap (ω : SmoothTwoForm I M) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {B : Set (ℝ × ℝ)} (hBm : MeasurableSet B)
    (hB : B ⊆ {w | (Complex.equivRealProdCLM.symm w ≠ 0 ∧
      Complex.equivRealProdCLM.symm w ≠ 1) ∧
      2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re}) {u : ℝ × ℝ → M}
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    (∫ z in realChart (q.plumbingMap L) '' B, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) =
      ∫ w in B, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.plumbingMap L)) w := by
  refine integral_image_eq_integral_of_eq_abs_det_smul hBm
    (realChart_injective (q.plumbingMap_injective L)).injOn
    (fun w _ ↦ (contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero w)
    fun w hw ↦ ?_
  rw [smul_eq_mul, abs_det_mul_floerEnergyDensity_plumbedPerturbation_realChart ω hq hHa hHb hHas
    hHbs hab hL (hB hw) hu]

/-- The energy density of the plumbed perturbation is integrable over the image `ψ(B)` of a
measurable set `B` in the part `Re z > 2 - L` of the inserted thrice-punctured sphere under the
plumbing chart `ψ` exactly when the energy density of `u ∘ ψ` for the perturbation of the inserted
pair of pants is integrable over `B`. -/
theorem integrableOn_floerEnergyDensity_image_plumbingMap_iff (ω : SmoothTwoForm I M) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {B : Set (ℝ × ℝ)} (hBm : MeasurableSet B)
    (hB : B ⊆ {w | (Complex.equivRealProdCLM.symm w ≠ 0 ∧
      Complex.equivRealProdCLM.symm w ≠ 1) ∧
      2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re}) {u : ℝ × ℝ → M}
    (hu : MDifferentiableOn 𝓘(ℝ, ℝ × ℝ) I u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        (realChart (q.plumbingMap L) '' B) ↔
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.plumbingMap L))) B := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hBm
    (fun w _ ↦ ((contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero
      w).hasFDerivAt.hasFDerivWithinAt) (realChart_injective (q.plumbingMap_injective L)).injOn]
  refine integrableOn_congr_fun (fun w hw ↦ ?_) hBm
  rw [smul_eq_mul, abs_det_mul_floerEnergyDensity_plumbedPerturbation_realChart ω hq hHa hHb hHas
    hHbs hab hL (hB hw) hu]

/-- On the part `Re z > 2 - L` of the inserted thrice-punctured sphere, measured in the end
coordinate at `∞`, the curvature of the plumbed perturbation at the image of a point `w` under
the plumbing chart `ψ`, multiplied by the Jacobian of `ψ`, is the curvature of the perturbation of
the inserted pair of pants at `w`. -/
private theorem abs_det_mul_hamiltonianCurvature_plumbedPerturbation_realChart
    (ω : SmoothTwoForm I M) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℝ × ℝ}
    (hw : (Complex.equivRealProdCLM.symm w ≠ 0 ∧ Complex.equivRealProdCLM.symm w ≠ 1) ∧
      2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re) (x : M) :
    |(fderiv ℝ (realChart (q.plumbingMap L)) w).det| * ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        (realChart (q.plumbingMap L) w) x =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w x := by
  have hψ := mapsTo_realChart_plumbingMap (L := L) hq (by linarith) ⟨hw.1, by linarith [hw.2]⟩
  rw [abs_of_nonneg (det_fderiv_realChart_nonneg (q.hasDerivAt_plumbingMap L _)),
    ← ω.hamiltonianCurvature_perturbationPullback (contDiff_realChart_plumbingMap q L).contDiffAt
      (differentiableAt_plumbedPerturbation_domain hq hHa hHb hHas hHbs hab hL hψ x 1)
      (differentiableAt_plumbedPerturbation_domain hq hHa hHb hHas hHbs hab hL hψ x _)
      (mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL hψ x 1)
      (mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL hψ x _),
    ω.hamiltonianCurvature_perturbationPullback_plumbedPerturbation hq hab hw.1.1 hw.2]

/-- **The integrated curvature along the plumbing chart, for a manifold target.** On a measurable
set `B` in the part `Re z > 2 - L` of the inserted thrice-punctured sphere, measured in the end
coordinate at `∞`, the integral over `ψ(B)` of the curvature of the plumbed perturbation along any
map `u` is the integral over `B` of the curvature of the pair-of-pants perturbation of `Ha` along
`u ∘ ψ`, where `ψ` is the plumbing chart. -/
theorem integral_hamiltonianCurvature_image_plumbingMap (ω : SmoothTwoForm I M) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {B : Set (ℝ × ℝ)} (hBm : MeasurableSet B)
    (hB : B ⊆ {w | (Complex.equivRealProdCLM.symm w ≠ 0 ∧
      Complex.equivRealProdCLM.symm w ≠ 1) ∧
      2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re}) (u : ℝ × ℝ → M) :
    ∫ z in realChart (q.plumbingMap L) '' B, ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      ∫ w in B, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w ((u ∘ realChart (q.plumbingMap L)) w) :=
  integral_image_eq_integral_of_eq_abs_det_smul hBm
    (realChart_injective (q.plumbingMap_injective L)).injOn
    (fun w _ ↦ (contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero w)
    fun w hw ↦ by
      rw [smul_eq_mul, abs_det_mul_hamiltonianCurvature_plumbedPerturbation_realChart ω hq hHa hHb
        hHas hHbs hab hL (hB hw), comp_apply]

/-- The curvature of the plumbed perturbation along `u` is integrable over the image `ψ(B)` of a
measurable set `B` in the part `Re z > 2 - L` of the inserted thrice-punctured sphere under the
plumbing chart `ψ` exactly when the curvature of the perturbation of the inserted pair of pants
along `u ∘ ψ` is integrable over `B`. -/
theorem integrableOn_hamiltonianCurvature_image_plumbingMap_iff (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {B : Set (ℝ × ℝ)} (hBm : MeasurableSet B)
    (hB : B ⊆ {w | (Complex.equivRealProdCLM.symm w ≠ 0 ∧
      Complex.equivRealProdCLM.symm w ≠ 1) ∧
      2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re}) (u : ℝ × ℝ → M) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) (realChart (q.plumbingMap L) '' B) ↔
      IntegrableOn (fun w ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w ((u ∘ realChart (q.plumbingMap L)) w)) B := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hBm
    (fun w _ ↦ ((contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero
      w).hasFDerivAt.hasFDerivWithinAt) (realChart_injective (q.plumbingMap_injective L)).injOn]
  exact integrableOn_congr_fun (fun w hw ↦ by
    rw [smul_eq_mul, abs_det_mul_hamiltonianCurvature_plumbedPerturbation_realChart ω hq hHa hHb
      hHas hHbs hab hL (hB hw), comp_apply]) hBm

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
          rw [hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_lt ω hq hab hz.1
            (by linarith [hz.2])]
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
  rw [ω.lintegral_enorm_hamiltonianCurvature_image hSm
    (realChart_injective (q.plumbingMap_injective L)).injOn
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

/-- **The integrated curvature of the plumbed perturbation over any region.** For period-one `C¹`
Hamiltonians on a manifold with `|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, every map `u` into it and
every set `s` of the plane, the integral of the curvature `R_K(z, u(z))` of the plumbed
perturbation over `s` is at most `∑ r, Ba r + ∑ r, Bb r` in absolute value, for every neck length
`L > 4`. -/
theorem abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → M)
    (s : Set (ℝ × ℝ)) :
    |∫ z in s, ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)| ≤ ∑ r, Ba r + ∑ r, Bb r := by
  have hBa₀ (r : Puncture) : 0 ≤ Ba r := (abs_nonneg _).trans (hBa r 0 (u 0))
  have hBb₀ (r : Puncture) : 0 ≤ Bb r := (abs_nonneg _).trans (hBb r 0 (u 0))
  rw [← ENNReal.ofReal_le_ofReal_iff (add_nonneg (Finset.sum_nonneg fun r _ ↦ hBa₀ r)
      (Finset.sum_nonneg fun r _ ↦ hBb₀ r)), ← Real.eNorm_eq_ofReal_abs,
    ENNReal.ofReal_add (Finset.sum_nonneg fun r _ ↦ hBa₀ r) (Finset.sum_nonneg fun r _ ↦ hBb₀ r),
    ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hBa₀ r, ENNReal.ofReal_sum_of_nonneg fun r _ ↦ hBb₀ r]
  exact (eNorm_integral_le_lintegral_eNorm _).trans ((setLIntegral_le_lintegral _ _).trans
    (ω.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb hHas hHbs hab hL hBa
      hBb u))

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

/-- **The integrated curvature of the plumbed perturbation over any region.** This is the
vector-space case of
`TauCeti.SmoothTwoForm.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le`: for
period-one `C¹` Hamiltonians on a symplectic vector space with `|Ha r| ≤ Ba r` and
`|Hb r| ≤ Bb r`, every map `u` into it and every set `s` of the plane, the integral of the
curvature `R_K(z, u(z))` of the plumbed perturbation over `s` is at most `∑ r, Ba r + ∑ r, Bb r`
in absolute value, for every neck length `L > 4`. -/
theorem abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) (u : ℝ × ℝ → V)
    (s : Set (ℝ × ℝ)) :
    |∫ z in s, ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)| ≤ ∑ r, Ba r + ∑ r, Bb r := by
  simpa using ω.constSmooth.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHas r).contMDiff)
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hab hL hBa hBb u s

end TauCeti.SymplecticForm

namespace TauCeti.Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Ha Hb : Puncture → ℝ → V → ℝ}
  {q : Puncture} {L : ℝ}

/-- At points other than the four punctures, the plumbed perturbation of Hamiltonians of class
`C^n` is `C^n` jointly in the domain and target points. -/
theorem contDiffAt_plumbedPerturbation_prod {n : ℕ∞} (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ n (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ n (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℂ} (hw : (w ≠ 0 ∧ w ≠ 1) ∧ w ≠ q.plumbingMap L 1)
    (x : V) :
    ContDiffAt ℝ n (fun p : ℂ × V ↦ plumbedPerturbation Ha Hb q L p.1 p.2) (w, x) :=
  (contMDiffAt_prod_modelWithCornersSelf_iff.1 (contMDiffAt_plumbedPerturbation (n := n) hq hHa
    hHb (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHas r).contMDiff)
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hab hL hw x)).contDiffAt

/-- In the real coordinates, the plumbed perturbation of Hamiltonians of class `C^n` is `C^n` at
the points of the four-punctured sphere. -/
theorem contDiffAt_uncurry_plumbedPerturbation {n : ℕ∞} (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ n (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ n (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {z : ℝ × ℝ}
    (hz : (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1) (x : V) (v : ℂ) :
    ContDiffAt ℝ n
      (uncurry fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v)
      (z, x) :=
  ((contDiffAt_plumbedPerturbation_prod hq hHa hHb hHas hHbs hab hL hz x).comp
    (f := fun p : (ℝ × ℝ) × V ↦ (Complex.equivRealProdCLM.symm p.1, p.2)) (z, x)
    ((Complex.equivRealProdCLM.symm.contDiff.comp contDiff_fst).prodMk
      contDiff_snd).contDiffAt).clm_apply contDiffAt_const

/-- The plumbing chart maps the part `Re z > 2 - L` of the inserted thrice-punctured sphere into
the four-punctured sphere, where the plumbed datum is `C¹`. -/
theorem differentiableAt_uncurry_plumbedPerturbation_realChart_plumbingMap
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℝ × ℝ}
    (hw : (Complex.equivRealProdCLM.symm w ≠ 0 ∧ Complex.equivRealProdCLM.symm w ≠ 1) ∧
      2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re) (y : V) (v : ℂ) :
    DifferentiableAt ℝ
      (uncurry fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v)
      (realChart (q.plumbingMap L) w, y) :=
  (contDiffAt_uncurry_plumbedPerturbation hq hHa hHb hHas hHbs hab hL
    (by
      rw [equivRealProdCLM_symm_realChart]
      exact mapsTo_plumbingMap hq (by linarith) ⟨hw.1, by linarith [hw.2]⟩) y v).differentiableAt
    one_ne_zero

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ha Hb : Puncture → ℝ → V → ℝ} {q : Puncture} {R L : ℝ}

/-- **The inserted pair of pants solves its Floer equation.** Let `u` solve the Floer equation
`(du - X_K)^{0,1} = 0` of the plumbed perturbation `K` at the image `ψ_L(w)` of a point `w` of the
truncation `S_R` of the inserted pair of pants, with neck length `L > 4` and `L > R + 2`. Then
`u ∘ ψ_L` solves the Floer equation of the inserted pair-of-pants perturbation at `w`, for the same
almost complex structure, because the plumbing map is holomorphic. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_realChart_plumbingMap (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) (hRL : R + 2 < L) {w : ℝ × ℝ}
    (hw : Complex.equivRealProdCLM.symm w ∈ truncation R) {u : ℝ × ℝ → V}
    (hu : DifferentiableAt ℝ u (realChart (q.plumbingMap L) w)) {J : AlmostComplexStructure V}
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u (realChart (q.plumbingMap L) w) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
      (u ∘ realChart (q.plumbingMap L)) w : ℝ × ℝ →ₗ[ℝ] V) := by
  have h₂ := (mem_truncation.1 hw).2.2 inf
  rw [endSign_inf, neg_one_mul] at h₂
  have hw' : (Complex.equivRealProdCLM.symm w ≠ 0 ∧ Complex.equivRealProdCLM.symm w ≠ 1) ∧
      2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re :=
    ⟨⟨(mem_truncation.1 hw).1, (mem_truncation.1 hw).2.1⟩, by linarith⟩
  have htgt (v : ℂ) :=
    (differentiableAt_uncurry_plumbedPerturbation_realChart_plumbingMap hq hHa hHb hHas hHbs hab
      hL hw' (u (realChart (q.plumbingMap L) w)) v).comp
      (f := fun y : V ↦ (realChart (q.plumbingMap L) w, y)) _
      ((differentiableAt_const _).prodMk differentiableAt_id)
  have h' := ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback
    ((contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero w) hu (htgt 1)
    (htgt Complex.I) (isComplexLinearMap_fderiv_realChart (q.hasDerivAt_plumbingMap L _)) h
  -- The pulled-back datum is the datum of the inserted pair of pants.
  have hs : perturbationPullback (realChart (q.plumbingMap L))
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      stdComplexLineReal w =
        fun x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm w) x 1 :=
    funext fun x ↦ by
      rw [perturbationPullback_plumbedPerturbation_of_mem_truncation hq hab hRL.le hw,
        equivRealProdCLM_symm_stdComplexLineReal]
  have ht : perturbationPullback (realChart (q.plumbingMap L))
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      stdComplexLineImag w =
        fun x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm w) x Complex.I :=
    funext fun x ↦ by
      rw [perturbationPullback_plumbedPerturbation_of_mem_truncation hq hab hRL.le hw,
        equivRealProdCLM_symm_stdComplexLineImag]
  rwa [ω.perturbedFDeriv_congr (Ks' := fun z x ↦
      pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
    (Kt' := fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I) _
    hs ht] at h'

end TauCeti.SymplecticForm
