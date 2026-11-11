/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Basic
import TauCeti.Analysis.Calculus.ContDiff.Cutoff
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Local
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Floer.Pullback

/-!
# The energy identity on the plumbed four-punctured sphere

Plumbing the output end at `∞` of a pair of pants `S'`, with Hamiltonians `Ha`, into the input end
`q ∈ {0, 1}` of a pair of pants `S`, with Hamiltonians `Hb`, along a neck of length `L` gives the
four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, where `ψ` is the plumbing map
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L`, with the plumbed perturbation `K`
(`TauCeti.Floer.plumbedPerturbation`). Its four ends carry the two inputs `Ha 0` and `Ha 1` of
`S'`, at `ψ(0) = c_q` and `ψ(1)`, the remaining input of `S` and the output `Hb ∞` of `S`. Families
of such domains connect the two ways of composing two pair-of-pants products, which is how the
product is shown to be associative.

The *plumbed truncation* `S_{L/2} ∪ ψ(S_{L/2})` is the union of the truncation `S_{L/2}` of the
receiving pair of pants `S` and the image under `ψ` of the truncation `S_{L/2}` of the inserted
pair of pants `S'`. The two pieces meet along the middle circle `s_q = L/2` of the neck, and the
four boundary circles of the union are the circles `±s = L/2` of the four outer ends. For a map
`u` into a symplectic vector space `(V, ω)` which is `C²` on the four-punctured sphere, the Floer
energy of `u` over the plumbed truncation is

`∫ E(u) = A_{Ha 0}(ℓ'_0) + A_{Ha 1}(ℓ'_1) + A_{Hb q'}(ℓ_{q'}) - A_{Hb ∞}(ℓ_∞) - ∫ R_K(u)`

(`SymplecticForm.integral_floerEnergyDensity_plumbedPerturbation_eq_sum_hamiltonianAction`). Here
`q'` is the input of `S` other than `q`, the loops `ℓ'_r(t) = u(ψ(φ_r(L/2 + i t)))` and
`ℓ_r(t) = u(φ_r(±L/2 + i t))` run along the outer boundary circles, `A_H` is the Hamiltonian
action `TauCeti.SymplecticForm.hamiltonianAction`, and the curvature is integrated over the plumbed
truncation. The neck does not contribute: the loop along its middle circle is both the output
loop of `S'` and the input loop `q` of `S`, with the same Hamiltonian `Ha ∞ = Hb q`, so its two
actions cancel.

The integrated curvature of the plumbed perturbation is bounded independently of `L`
(`TauCeti.SymplecticForm.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le`), so the
energy over the plumbed truncation differs from the signed sum of the four outer actions by at
most `∑ r, Ba r + ∑ r, Bb r` when `|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, for every `L > 4`
(`SymplecticForm.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_sum_le`). For a solution
of the Floer equation with tame almost complex structures the energy density is nonnegative, which
bounds the action of the output loop by the actions of the three input loops plus that constant
(`SymplecticForm.hamiltonianAction_le_sum_add_sum_add_of_plumbedPerturbation`).

The proof applies the energy identity of the truncated pair of pants
`integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction`
to each piece. On `S_{L/2}` the plumbed perturbation is the perturbation of `S`. On `ψ(S_{L/2})` its
pullback along `ψ` is the perturbation of `S'`, and energy and curvature are invariant under the
holomorphic change of coordinates `ψ` (`TauCeti.SymplecticForm.integral_floerEnergyDensity_image`,
`TauCeti.SymplecticForm.integral_hamiltonianCurvature_image`). The map `u` need not extend across
the puncture `ψ(1)`, which lies on the end `q` of `S`, nor across the remaining puncture of `S`,
whose preimage under `ψ` lies on the end at `∞` of `S'`. So each piece first multiplies `u` by a
cutoff which is `1` up to the circle at height `L/2 + 1` of that end and `0` beyond height
`L/2 + 2`; this cut-off map is `C²` on the thrice-punctured sphere and agrees with `u` near the
truncation.

For a target that is a finite-dimensional manifold `M` with a nondegenerate two-form `ω`, such as
a closed symplectic manifold, the loops have no action, and the identity is stated with the
symplectic area and the Hamiltonian terms of the boundary loops, as for the pair of pants
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation`).
For a map `u` which is `C¹` on the four-punctured sphere,

`∫ E(u) = ∫ u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, ℓ'_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, ℓ_r(t)) dt -
  ∫ R_K(u)`

over the plumbed truncation
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`), with the
uniform bound
(`SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le`) and
the resulting lower bound for Floer solutions
(`SmoothTwoForm.IsNondegenerate.neg_sum_le_integral_add_sum_of_plumbedPerturbation`). Again the
Hamiltonian terms of the middle circle of the neck cancel. A map into a manifold cannot be cut
off; instead the pair-of-pants identity applies on each piece in the form for maps which are `C¹`
near the truncation only, in `TauCeti.SmoothTwoForm`:
(`IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_of_subset`).

All four outer ends are truncated at the same height `L/2` as the neck. Truncations of the outer
ends at heights independent of `L`, and the energy identity over the whole four-punctured sphere,
are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the energy estimates for compositions of pair-of-pants products.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 10.9, on
  gluing punctured Riemann surfaces along cylindrical ends.
-/

public section

open Set Real Function MeasureTheory Filter TauCeti.ThricePuncturedSphere
  TauCeti.ThricePuncturedSphere.Puncture
open scoped Topology Manifold
open TauCeti.Complex (realChart realChart_apply realChart_injective)

namespace TauCeti.Floer

variable {M : Type*} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-- On the receiving truncation `S_{L/2}`, the plumbed perturbation is the perturbation of the
receiving pair of pants. -/
private theorem plumbedPerturbation_of_mem_truncation (hq : q ≠ inf) (hab : Hb q = Ha inf)
    (hL : 4 < L) {z : ℝ × ℝ} (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2))
    (x : M) (v : ℂ) :
    plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v =
      pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x v := by
  have h := (mem_truncation.1 hz).2.2 q
  rw [endSign_eq_one hq, one_mul] at h
  rw [plumbedPerturbation_of_re_endCoord_le hq hab (by linarith) x]

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-! ### The inserted piece, for a manifold target -/

/-- Over the image `ψ(S_{L/2})` of the inserted truncation, the integrated curvature of the
plumbed perturbation along `u` is the integrated curvature over `S_{L/2}` of the perturbation of
the inserted pair of pants along `u ∘ ψ`, and the integrability of the two agrees. -/
private theorem setIntegral_hamiltonianCurvature_inserted (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) (u : ℝ × ℝ → M) :
    (∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)),
        ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) =
      ∫ w in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w ((u ∘ realChart (q.plumbingMap L)) w)) ∧
    (IntegrableOn (fun z ↦ ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z))
        (realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2))) ↔
      IntegrableOn (fun w ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w ((u ∘ realChart (q.plumbingMap L)) w))
        (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2))) := by
  have hT := measurableSet_preimage_truncation (L / 2)
  have hinj := (realChart_injective (q.plumbingMap_injective L)).injOn
    (s := Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2))
  have hP {w : ℝ × ℝ} (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :=
    realChart_plumbingMap_image_subset hq hL ⟨w, hw, rfl⟩
  have hK {w : ℝ × ℝ} (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) (v : ℂ) :=
    And.intro (differentiableAt_plumbedPerturbation_domain hq hHa hHb hHas hHbs hab hL (hP hw)
      (u (realChart (q.plumbingMap L) w)) v)
      (mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL (hP hw)
        (u (realChart (q.plumbingMap L) w)) v)
  -- In the coordinates of the inserted pair of pants, the curvature times the Jacobian of `ψ` is
  -- the curvature of the inserted perturbation.
  have hpt {w : ℝ × ℝ} (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :
      (fderiv ℝ (realChart (q.plumbingMap L)) w).det * ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          (realChart (q.plumbingMap L) w) (u (realChart (q.plumbingMap L) w)) =
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
          w ((u ∘ realChart (q.plumbingMap L)) w) := by
    have hw' := mem_truncation.1 hw
    have hre : 2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re := by
      have h := hw'.2.2 inf
      rw [endSign_inf, neg_one_mul] at h
      linarith
    rw [← ω.hamiltonianCurvature_perturbationPullback
      (contDiff_realChart_plumbingMap q L).contDiffAt (hK hw 1).1 (hK hw Complex.I).1
      (hK hw 1).2 (hK hw Complex.I).2]
    exact congrFun (ω.hamiltonianCurvature_perturbationPullback_plumbedPerturbation hq hab hw'.1
      hre) _
  refine ⟨?_, ?_⟩
  · rw [ω.integral_hamiltonianCurvature_image hT hinj
      (fun w _ ↦ (contDiff_realChart_plumbingMap q L).contDiffAt)
      (fun w _ ↦ det_fderiv_realChart_plumbingMap_nonneg q L w)
      (fun w hw ↦ (hK hw 1).1) (fun w hw ↦ (hK hw Complex.I).1)
      (fun w hw ↦ (hK hw 1).2) (fun w hw ↦ (hK hw Complex.I).2)]
    refine setIntegral_congr_fun hT fun w hw ↦ ?_
    rw [← hpt hw, ω.hamiltonianCurvature_perturbationPullback
      (contDiff_realChart_plumbingMap q L).contDiffAt (hK hw 1).1 (hK hw Complex.I).1
      (hK hw 1).2 (hK hw Complex.I).2]
  · have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
    rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hT
      (fun w _ ↦ ((contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero
        w).hasFDerivAt.hasFDerivWithinAt) hinj]
    refine integrableOn_congr_fun (fun w hw ↦ ?_) hT
    rw [smul_eq_mul, abs_of_nonneg (det_fderiv_realChart_plumbingMap_nonneg q L w), hpt hw]

/-- Over the image `ψ(S_{L/2})` of the inserted truncation, the Floer energy of `u` for the
plumbed perturbation is the energy of `u ∘ ψ` over `S_{L/2}` for the perturbation of the inserted
pair of pants, and the symplectic area of `u` is the area of `u ∘ ψ`. -/
private theorem setIntegral_floerEnergyDensity_inserted (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    (∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)),
        ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      ∫ w in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.plumbingMap L)) w) ∧
    (∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)),
        (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) =
      ∫ w in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2),
        (SmoothBundleForm.eval₂ ω ((u ∘ realChart (q.plumbingMap L)) w)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart (q.plumbingMap L)) w stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart (q.plumbingMap L)) w stdComplexLineImag) : ℝ) := by
  have hT := measurableSet_preimage_truncation (L / 2)
  have hinj := (realChart_injective (q.plumbingMap_injective L)).injOn
    (s := Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2))
  have hφ (w : ℝ × ℝ) : DifferentiableAt ℝ (realChart (q.plumbingMap L)) w :=
    (contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero w
  have hP {w : ℝ × ℝ} (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :=
    realChart_plumbingMap_image_subset hq hL ⟨w, hw, rfl⟩
  have hud {w : ℝ × ℝ} (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :
      MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (realChart (q.plumbingMap L) w) :=
    (hu.contMDiffAt ((isOpen_plumbedSphere q L).mem_nhds (hP hw))).mdifferentiableAt one_ne_zero
  have hK {w : ℝ × ℝ} (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) (v : ℂ) :=
    mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL (hP hw)
      (u (realChart (q.plumbingMap L) w)) v
  refine ⟨?_, ?_⟩
  · rw [ω.integral_floerEnergyDensity_image hT hinj (fun w _ ↦ hφ w)
      (fun w _ ↦ det_fderiv_realChart_plumbingMap_nonneg q L w) (fun w hw ↦ hud hw)
      (fun w hw ↦ hK hw 1) (fun w hw ↦ hK hw Complex.I)]
    refine setIntegral_congr_fun hT fun w hw ↦ ?_
    have hpR := funext (perturbationPullback_plumbedPerturbation_of_mem_truncation (Ha := Ha)
      (Hb := Hb) (L := L) (R := L / 2) hq hab (by linarith) hw stdComplexLineReal)
    have hpI := funext (perturbationPullback_plumbedPerturbation_of_mem_truncation (Ha := Ha)
      (Hb := Hb) (L := L) (R := L / 2) hq hab (by linarith) hw stdComplexLineImag)
    rw [equivRealProdCLM_symm_stdComplexLineReal] at hpR
    rw [equivRealProdCLM_symm_stdComplexLineImag] at hpI
    simp only [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineReal,
      perturbedMFDeriv_apply_stdComplexLineImag, hpR, hpI]
  · have h := ω.integral_floerEnergyDensity_image (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0) hT hinj
      (fun w _ ↦ hφ w) (fun w _ ↦ det_fderiv_realChart_plumbingMap_nonneg q L w)
      (fun w hw ↦ hud hw) (fun _ _ ↦ mdifferentiableAt_const) (fun _ _ ↦ mdifferentiableAt_const)
    simpa only [perturbationPullback_zero, floerEnergyDensity_zero] using h

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ha Hb : Puncture → ℝ → V → ℝ} {q : Puncture} {L : ℝ}

/-! ### Cutting a map off along an end -/

/-- The cutoff `1 - β(±s_r - R)` along the end `r`, in real coordinates: it is `1` where the signed
longitudinal coordinate `±s_r` is at most `R` and `0` where it is at least `R + 1`. -/
private noncomputable def endCutoff (r : Puncture) (R : ℝ) (z : ℝ × ℝ) : ℝ :=
  1 - smoothTransition (r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re - R)

private theorem continuousAt_endHeight {r : Puncture} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ r.endCenter) :
    ContinuousAt (fun z : ℝ × ℝ ↦ r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re)
      z :=
  continuousAt_const.mul ((r.contDiffAt_re_endCoord hz (n := 0)).continuousAt.comp
    Complex.equivRealProdCLM.symm.continuous.continuousAt)

private theorem contDiffAt_endCutoff {r : Puncture} {R : ℝ} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ r.endCenter) {n : ℕ∞} :
    ContDiffAt ℝ n (endCutoff r R) z :=
  contDiffAt_const.sub (smoothTransition.contDiffAt.comp z
    ((contDiffAt_const.mul ((r.contDiffAt_re_endCoord hz).comp z
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt)).sub contDiffAt_const))

/-- Near a point at which `±s_r < R`, the cutoff is `1`. -/
private theorem endCutoff_eventuallyEq_one {r : Puncture} {R : ℝ} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ r.endCenter)
    (h : r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re < R) :
    endCutoff r R =ᶠ[𝓝 z] fun _ ↦ 1 := by
  filter_upwards [(continuousAt_endHeight hz).eventually (gt_mem_nhds h)] with z' hz'
  rw [endCutoff, smoothTransition.zero_of_nonpos (by linarith), sub_zero]

/-- Near a point at which `±s_r > R + 1`, the cutoff is `0`. -/
private theorem endCutoff_eventuallyEq_zero {r : Puncture} {R : ℝ} {z : ℝ × ℝ}
    (hz : Complex.equivRealProdCLM.symm z ≠ r.endCenter)
    (h : R + 1 < r.endSign * (r.endCoord (Complex.equivRealProdCLM.symm z)).re) :
    endCutoff r R =ᶠ[𝓝 z] fun _ ↦ 0 := by
  filter_upwards [(continuousAt_endHeight hz).eventually (lt_mem_nhds h)] with z' hz'
  rw [endCutoff, smoothTransition.one_of_one_le (by linarith), sub_self]

/-- The cutoffs at height `L/2 + 1` are `1` on the boundary circles `±s = L/2` of the ends. -/
private theorem endCutoff_cylindricalEndLift (hL : 0 < L) (r r' : Puncture) (t : ℝ) :
    endCutoff r' (L / 2 + 1) (Complex.equivRealProdCLM
      (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I))) = 1 := by
  have h := (mem_truncation.1
    (cylindricalEndLift_mem_truncation r (R := L / 2) (by linarith) t)).2.2 r'
  rw [endCutoff, ContinuousLinearEquiv.symm_apply_apply,
    smoothTransition.zero_of_nonpos (by linarith), sub_zero]

/-! ### The receiving and inserted pieces of a map -/

/-- The components of the plumbed perturbation are `C¹` on the plumbed four-punctured sphere times
the target. -/
private theorem contDiffOn_uncurry_plumbedPerturbation (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) (v : ℂ) :
    ContDiffOn ℝ 1
      (uncurry fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v)
      ({z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  exact (contDiffAt_uncurry_plumbedPerturbation (n := 1) hq hHa hHb hHas hHbs hab hL hz x
    v).contDiffWithinAt

/-- The receiving piece `(1 - β(s_q - L/2 - 1)) u` of a map `u` that is `C²` on the plumbed
four-punctured sphere vanishes near the puncture `ψ(1)`, and so is `C²` on `S`. -/
private theorem contDiffOn_receivingPiece (hq : q ≠ inf) (hL : 4 < L) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ContDiffOn ℝ 2 (fun z ↦ endCutoff q (L / 2 + 1) z • u z)
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1} := by
  refine contDiffOn_smul_of_eventuallyEq_zero (isOpen_plumbedSphere q L)
    (fun z hz ↦ contDiffAt_endCutoff (ne_endCenter hz q)) hu fun z hz hzP ↦ ?_
  have h₁ : Complex.equivRealProdCLM.symm z = q.plumbingMap L 1 := by
    by_contra h
    exact hzP ⟨hz, h⟩
  refine endCutoff_eventuallyEq_zero (ne_endCenter hz q) ?_
  rw [h₁, endSign_eq_one hq, one_mul, re_endCoord_plumbingMap q L one_ne_zero]
  linarith [re_endCoord_inf_one_pos]

/-- The inserted piece `(1 - β(-s_∞ - L/2 - 1)) (u ∘ ψ)` of a map `u` that is `C²` on the plumbed
four-punctured sphere vanishes near the preimage under `ψ` of the remaining finite puncture, and
so is `C²` on `S`. -/
private theorem contDiffOn_insertedPiece (hq : q ≠ inf) (hL : 4 < L) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ContDiffOn ℝ 2 (fun w ↦ endCutoff inf (L / 2 + 1) w • u (realChart (q.plumbingMap L) w))
      {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1} := by
  have hψ := hu.comp (contDiff_realChart_plumbingMap q L).contDiffOn (mapsTo_preimage _ _)
  refine contDiffOn_smul_of_eventuallyEq_zero
    ((isOpen_plumbedSphere q L).preimage (contDiff_realChart_plumbingMap q L (n := 0)).continuous)
    (fun w hw ↦ contDiffAt_endCutoff (by simpa using hw.1)) hψ fun w hw hwP ↦ ?_
  have hψw : Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) =
      q.plumbingMap L (Complex.equivRealProdCLM.symm w) := by
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hvq : q.plumbingMap L (Complex.equivRealProdCLM.symm w) ≠ q.endCenter := by
    rw [plumbingMap_apply]
    intro h
    have h' : q.plumbingFactor L * Complex.equivRealProdCLM.symm w = 0 := by
      linear_combination h
    exact hw.1 ((mul_eq_zero.1 h').resolve_left (q.plumbingFactor_ne_zero L))
  have hv : q.plumbingMap L (Complex.equivRealProdCLM.symm w) = 0 ∨
      q.plumbingMap L (Complex.equivRealProdCLM.symm w) = 1 := by
    by_contra! h
    exact hwP (by
      rw [mem_preimage, mem_ofPred_eq, hψw]
      exact ⟨h, fun h' ↦ hw.2 (q.plumbingMap_injective L h')⟩)
  refine endCutoff_eventuallyEq_zero (by simpa using hw.1) ?_
  have h := re_endCoord_lt_zero hq hv hvq
  rw [re_endCoord_plumbingMap q L hw.1] at h
  rw [endSign_inf]
  linarith

/-- On the receiving truncation `S_{L/2}`, the receiving piece agrees with the map near every
point. -/
private theorem receivingPiece_eventuallyEq (u : ℝ × ℝ → V) {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :
    (fun z ↦ endCutoff q (L / 2 + 1) z • u z) =ᶠ[𝓝 z] u := by
  have hz' := mem_truncation.1 hz
  filter_upwards [endCutoff_eventuallyEq_one (ne_endCenter ⟨hz'.1, hz'.2.1⟩ q)
    (by linarith [hz'.2.2 q] : q.endSign * (q.endCoord _).re < L / 2 + 1)] with z' hz''
  rw [hz'', one_smul]

/-- On the inserted truncation `S_{L/2}`, the inserted piece agrees with `u ∘ ψ` near every
point. -/
private theorem insertedPiece_eventuallyEq (u : ℝ × ℝ → V) {w : ℝ × ℝ}
    (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :
    (fun w ↦ endCutoff inf (L / 2 + 1) w • u (realChart (q.plumbingMap L) w)) =ᶠ[𝓝 w]
      fun w ↦ u (realChart (q.plumbingMap L) w) := by
  have hw' := mem_truncation.1 hw
  filter_upwards [endCutoff_eventuallyEq_one (ne_endCenter ⟨hw'.1, hw'.2.1⟩ inf)
    (by linarith [hw'.2.2 inf] : inf.endSign * (inf.endCoord _).re < L / 2 + 1)] with w' hw''
  rw [hw'', one_smul]

/-! ### The energy and curvature of the two pieces -/

variable [FiniteDimensional ℝ V]

/-- Over the receiving truncation `S_{L/2}`, the Floer energy of `u` for the plumbed perturbation
is that of the receiving piece of `u` for the perturbation of the receiving pair of pants. -/
private theorem setIntegral_floerEnergyDensity_receiving (ω : SymplecticForm V) (hq : q ≠ inf)
    (hab : Hb q = Ha inf) (hL : 4 < L) (u : ℝ × ℝ → V) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        (fun z ↦ endCutoff q (L / 2 + 1) z • u z) z := by
  refine setIntegral_congr_fun ((isCompact_truncation _).isClosed.preimage
    Complex.equivRealProdCLM.symm.continuous).measurableSet fun z hz ↦ ?_
  rw [ω.floerEnergyDensity_congr_of_eventuallyEq _ _ (receivingPiece_eventuallyEq u hz)]
  simp only [floerEnergyDensity_def, perturbedFDeriv_apply_stdComplexLineReal,
    perturbedFDeriv_apply_stdComplexLineImag, plumbedPerturbation_of_mem_truncation (Ha := Ha) hq
      hab hL hz]

/-- Over the image under the plumbing map of the inserted truncation `S_{L/2}`, the Floer energy
of `u` for the plumbed perturbation is that of the inserted piece of `u` over `S_{L/2}` for the
perturbation of the inserted pair of pants. -/
private theorem setIntegral_floerEnergyDensity_inserted (ω : SymplecticForm V) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)),
        ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z =
      ∫ w in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        (fun w ↦ endCutoff inf (L / 2 + 1) w • u (realChart (q.plumbingMap L) w)) w := by
  have h := (SmoothTwoForm.setIntegral_floerEnergyDensity_inserted (ω := ω.constSmooth) hq hHa
    hHb (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHas r).contMDiff)
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hab hL
    (contMDiffOn_iff_contDiffOn.2 (hu.of_le one_le_two))).1
  simp only [floerEnergyDensity_constSmooth] at h
  rw [h]
  refine setIntegral_congr_fun (measurableSet_preimage_truncation _) fun w hw ↦ ?_
  rw [ω.floerEnergyDensity_congr_of_eventuallyEq _ _ (insertedPiece_eventuallyEq u hw),
    Function.comp_def]

/-- Over the receiving truncation `S_{L/2}`, the integrated curvature of the plumbed perturbation
along `u` is the integrated curvature over `S` of the receiving perturbation along the receiving
piece of `u`. -/
private theorem setIntegral_hamiltonianCurvature_receiving (ω : SymplecticForm V) (hq : q ≠ inf)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) (u : ℝ × ℝ → V) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      ∫ z in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (endCutoff q (L / 2 + 1) z • u z) := by
  rw [setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_eq_truncation ω hHb hHbs _
    (by linarith : (2 : ℝ) ≤ L / 2)]
  refine setIntegral_congr_fun ((isCompact_truncation _).isClosed.preimage
    Complex.equivRealProdCLM.symm.continuous).measurableSet fun z hz ↦ ?_
  have hz' := mem_truncation.1 hz
  have hre : (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2 := by
    have h := hz'.2.2 q
    rwa [endSign_eq_one hq, one_mul] at h
  have hu : endCutoff q (L / 2 + 1) z • u z = u z := (receivingPiece_eventuallyEq u hz).eq_of_nhds
  rw [hu, ← hamiltonianCurvature_constSmooth, ← hamiltonianCurvature_constSmooth]
  exact congrFun (SmoothTwoForm.hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_lt
    ω.constSmooth hq hab (ne_endCenter ⟨hz'.1, hz'.2.1⟩ q) (by linarith)) (u z)

/-- Over the image under the plumbing map of the inserted truncation `S_{L/2}`, the integrated
curvature of the plumbed perturbation along `u` is the integrated curvature over `S` of the
inserted perturbation along the inserted piece of `u`. -/
private theorem setIntegral_hamiltonianCurvature_inserted (ω : SymplecticForm V) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) (u : ℝ × ℝ → V) :
    ∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)),
        ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) =
      ∫ w in {z : ℝ × ℝ | Complex.equivRealProdCLM.symm z ≠ 0 ∧
          Complex.equivRealProdCLM.symm z ≠ 1}, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w (endCutoff inf (L / 2 + 1) w • u (realChart (q.plumbingMap L) w)) := by
  have h := (SmoothTwoForm.setIntegral_hamiltonianCurvature_inserted (ω := ω.constSmooth) hq hHa
    hHb (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHas r).contMDiff)
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hab hL u).1
  simp only [hamiltonianCurvature_constSmooth] at h
  rw [h, setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_eq_truncation ω hHa hHas _
    (by linarith : (2 : ℝ) ≤ L / 2)]
  refine setIntegral_congr_fun (measurableSet_preimage_truncation _) fun w hw ↦ ?_
  have hu : endCutoff inf (L / 2 + 1) w • u (realChart (q.plumbingMap L) w) =
      u (realChart (q.plumbingMap L) w) := (insertedPiece_eventuallyEq u hw).eq_of_nhds
  rw [hu, Function.comp_apply]

omit [FiniteDimensional ℝ V] in
/-- A function continuous on the plumbed four-punctured sphere integrates over the plumbed
truncation `S_{L/2} ∪ ψ(S_{L/2})` as the sum of its integrals over the two pieces. -/
private theorem setIntegral_plumbedTruncation (hq : q ≠ inf) (hL : 4 < L) {f : ℝ × ℝ → ℝ}
    (hf : ContinuousOn f {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), f z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), f z) +
        ∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹'
          truncation (L / 2)), f z := by
  have hT : IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation _)
  have hA := hT.image (contDiff_realChart_plumbingMap q L (n := 0)).continuous
  exact setIntegral_truncation_union_image_of_integrableOn hq
    ((hf.mono fun z hz ↦ mem_plumbedSphere_of_mem_truncation hq hL hz).integrableOn_compact hT)
    ((hf.mono (realChart_plumbingMap_image_subset hq hL)).integrableOn_compact hA)

/-! ### The energy identity -/

/-- **The energy identity on the plumbed four-punctured sphere.** Plumb the output end of a pair
of pants with period-one `C¹` Hamiltonians `Ha` into the input end `q ≠ ∞` of one with period-one
`C¹` Hamiltonians `Hb`, with `Hb q = Ha ∞`, along a neck of length `L > 4`, and let `u` be `C²` on
the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, in real coordinates. Over the plumbed truncation
`S_{L/2} ∪ ψ(S_{L/2})`, the Floer energy of `u` for the plumbed perturbation `K` is

`∑_{r ≠ ∞} A_{Ha r}(ℓ'_r) + ∑_{r ≠ q} ±A_{Hb r}(ℓ_r) - ∫ R_K(u)`,

the actions of the loops `ℓ'_r(t) = u(ψ(φ_r(L/2 + i t)))` along the input circles of the inserted
pair of pants, plus the signed actions of the loops `ℓ_r(t) = u(φ_r(±L/2 + i t))` along the
remaining input and output circles of the receiving one, minus the integrated curvature. -/
theorem integral_floerEnergyDensity_plumbedPerturbation_eq_sum_hamiltonianAction
    (ω : SymplecticForm V) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r))) (hab : Hb q = Ha inf) (hL : 4 < L)
    {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∑ r ∈ Finset.univ.erase inf, ω.hamiltonianAction (Ha r) (fun t ↦ u
          (Complex.equivRealProdCLM (q.plumbingMap L
            (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))))) +
        (∑ r ∈ Finset.univ.erase q, r.endSign * ω.hamiltonianAction (Hb r) (fun t ↦ u
          (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
            (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have hKs := contDiffOn_uncurry_plumbedPerturbation hq hHa hHb hHas hHbs hab hL
  have hR : (2 : ℝ) ≤ L / 2 := by linarith
  rw [setIntegral_plumbedTruncation hq hL (ω.continuousOn_floerEnergyDensity
      (isOpen_plumbedSphere q L) (hu.of_le one_le_two) (hKs 1) (hKs Complex.I)),
    setIntegral_plumbedTruncation hq hL (ω.continuousOn_hamiltonianCurvature_comp
      (isOpen_plumbedSphere q L) hu.continuousOn (hKs 1) (hKs Complex.I)),
    setIntegral_floerEnergyDensity_receiving ω hq hab hL u,
    setIntegral_floerEnergyDensity_inserted ω hq hHa hHb hHas hHbs hab hL hu,
    setIntegral_hamiltonianCurvature_receiving ω hq hHb hHbs hab hL u,
    setIntegral_hamiltonianCurvature_inserted ω hq hHa hHb hHas hHbs hab hL u,
    integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction ω hHb
      hHbs (contDiffOn_receivingPiece hq hL hu) hR,
    integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_eq_sum_hamiltonianAction ω hHa
      hHas (contDiffOn_insertedPiece hq hL hu) hR,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ q),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ inf)]
  have hchart (w : ℂ) : realChart (q.plumbingMap L) (Complex.equivRealProdCLM w) =
      Complex.equivRealProdCLM (q.plumbingMap L w) := by
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
  -- The inputs of the inserted pair of pants have sign `+`.
  have hinputs : ∑ r ∈ Finset.univ.erase inf, r.endSign * ω.hamiltonianAction (Ha r) (fun t ↦
      u (Complex.equivRealProdCLM (q.plumbingMap L
        (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I))))) =
      ∑ r ∈ Finset.univ.erase inf, ω.hamiltonianAction (Ha r) (fun t ↦
        u (Complex.equivRealProdCLM (q.plumbingMap L
          (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I))))) :=
    Finset.sum_congr rfl fun r hr ↦ by
      rw [endSign_eq_one (Finset.ne_of_mem_erase hr), one_mul, one_mul]
  -- The cutoffs are `1` on the boundary circles, and the output loop of the inserted pair of
  -- pants is the input loop `q` of the receiving one, so their actions cancel.
  simp only [endCutoff_cylindricalEndLift (by linarith : 0 < L), one_smul, hchart,
    plumbingMap_cylindricalEndLift_inf hq, ← hab, hinputs]
  rw [endSign_inf, endSign_eq_one hq]
  ring

/-- **The energy bound on the plumbed four-punctured sphere.** Under the hypotheses of
`SymplecticForm.integral_floerEnergyDensity_plumbedPerturbation_eq_sum_hamiltonianAction`, if
`|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, then the Floer energy over the plumbed truncation differs from
the signed sum of the actions of its four boundary loops by at most `∑ r, Ba r + ∑ r, Bb r`,
uniformly in the neck length `L > 4`. -/
theorem abs_integral_floerEnergyDensity_plumbedPerturbation_sub_sum_le (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      ((∑ r ∈ Finset.univ.erase inf, ω.hamiltonianAction (Ha r) (fun t ↦ u
          (Complex.equivRealProdCLM (q.plumbingMap L
            (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))))) +
        ∑ r ∈ Finset.univ.erase q, r.endSign * ω.hamiltonianAction (Hb r) (fun t ↦ u
          (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I)))))| ≤
      ∑ r, Ba r + ∑ r, Bb r := by
  rw [integral_floerEnergyDensity_plumbedPerturbation_eq_sum_hamiltonianAction ω hq hHa hHb hHas
    hHbs hab hL hu, sub_sub_cancel_left, abs_neg]
  exact ω.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb hHas hHbs hab hL
    hBa hBb u _

/-- **The action bound on the plumbed four-punctured sphere.** Under the hypotheses of
`SymplecticForm.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_sum_le`, if `u` solves the
Floer equation `(du - X_K)^{0,1} = 0` on the plumbed truncation for almost complex structures
`J(z)` tamed by `ω`, then the action of its output loop is at most the sum of the actions of its
three input loops plus `∑ r, Ba r + ∑ r, Bb r`:

`A_{Hb ∞}(ℓ_∞) ≤ A_{Ha 0}(ℓ'_0) + A_{Ha 1}(ℓ'_1) + A_{Hb q'}(ℓ_{q'}) + ∑ r, Ba r + ∑ r, Bb r`,

where `q'` is the input of the receiving pair of pants other than `q`. The bound does not depend on
the neck length `L > 4`. -/
theorem hamiltonianAction_le_sum_add_sum_add_of_plumbedPerturbation (ω : SymplecticForm V)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 1 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → V}
    (hu : ContDiffOn ℝ 2 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ℝ × ℝ → AlmostComplexStructure V}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹'
      (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹'
      (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) :
    ω.hamiltonianAction (Hb inf) (fun t ↦ u (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(-(L / 2)) + ↑t * Complex.I)))) ≤
      (∑ r ∈ Finset.univ.erase inf, ω.hamiltonianAction (Ha r) (fun t ↦ u
          (Complex.equivRealProdCLM (q.plumbingMap L
            (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))))) +
        (∑ r ∈ (Finset.univ.erase q).erase inf, ω.hamiltonianAction (Hb r) (fun t ↦ u
          (Complex.equivRealProdCLM (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I))))) +
        (∑ r, Ba r + ∑ r, Bb r) := by
  have hE := setIntegral_nonneg (μ := volume) (measurableSet_preimage_truncation_union_image q L _)
    fun z hz ↦ ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (abs_integral_floerEnergyDensity_plumbedPerturbation_sub_sum_le ω hq hHa hHb
    hHas hHbs hab hL hBa hBb hu)).2
  -- The remaining input of the receiving pair of pants has sign `+`.
  have hother : ∑ r ∈ (Finset.univ.erase q).erase inf, r.endSign * ω.hamiltonianAction (Hb r)
      (fun t ↦ u (Complex.equivRealProdCLM
        (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I)))) =
      ∑ r ∈ (Finset.univ.erase q).erase inf, ω.hamiltonianAction (Hb r) (fun t ↦ u
        (Complex.equivRealProdCLM (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))) :=
    Finset.sum_congr rfl fun r hr ↦ by
      rw [endSign_eq_one (Finset.ne_of_mem_erase hr), one_mul, one_mul]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_erase.2 ⟨Ne.symm hq, Finset.mem_univ inf⟩), hother,
    endSign_inf, neg_one_mul, neg_one_mul] at h
  linarith

end TauCeti.SymplecticForm

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I ⊤ M] {ω : SmoothTwoForm I M} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture}
  {L : ℝ}

/-! ### The energy identity for a manifold target -/

omit [FiniteDimensional ℝ E] in
/-- Over the receiving truncation `S_{L/2}`, the Floer energy density and the curvature of the
plumbed perturbation along `u` are those of the perturbation of the receiving pair of pants. -/
private theorem floerEnergyDensity_and_hamiltonianCurvature_receiving (hq : q ≠ inf)
    (hab : Hb q = Ha inf) (hL : 4 < L) (u : ℝ × ℝ → M) {z : ℝ × ℝ}
    (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :
    ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z ∧
    ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) := by
  have hz' := mem_truncation.1 hz
  have hre : (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2 := by
    have h := hz'.2.2 q
    rwa [endSign_eq_one hq, one_mul] at h
  refine ⟨?_, congrFun (hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_lt ω hq hab
    (ne_endCenter ⟨hz'.1, hz'.2.1⟩ q) (by linarith)) (u z)⟩
  simp only [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag,
    plumbedPerturbation_of_mem_truncation (Ha := Ha) hq hab hL hz]

/-- Over the plumbed truncation `S_{L/2} ∪ ψ(S_{L/2})`, the Floer energy, the symplectic area and
the integrated curvature of `u` for the plumbed perturbation are the sums of those of `u` over the
receiving truncation `S_{L/2}`, for the perturbation of the receiving pair of pants, and of
`u ∘ ψ` over the inserted truncation `S_{L/2}`, for the perturbation of the inserted one. -/
private theorem IsNondegenerate.setIntegral_plumbedTruncation_eq_add
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    (∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) +
      ∫ w in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.plumbingMap L)) w) ∧
    (∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
        (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2),
        (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
      ∫ w in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2),
        (SmoothBundleForm.eval₂ ω ((u ∘ realChart (q.plumbingMap L)) w)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart (q.plumbingMap L)) w stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ realChart (q.plumbingMap L)) w stdComplexLineImag) : ℝ)) ∧
    (∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) +
      ∫ w in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w ((u ∘ realChart (q.plumbingMap L)) w)) := by
  have hT := measurableSet_preimage_truncation (L / 2)
  have hTc : IsCompact (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :=
    Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2 (isCompact_truncation _)
  have hAc := hTc.image (contDiff_realChart_plumbingMap q L (n := 0)).continuous
  have hPo := isOpen_plumbedSphere q L
  have hTP : Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2) ⊆
      {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} :=
    fun z hz ↦ mem_plumbedSphere_of_mem_truncation hq hL hz
  have hAP := realChart_plumbingMap_image_subset hq hL
  have hKs := contMDiffOn_plumbedPerturbation hq hHa hHb hHas hHbs hab hL 1
  have hKt := contMDiffOn_plumbedPerturbation hq hHa hHb hHas hHbs hab hL Complex.I
  have hrec {z : ℝ × ℝ} (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :=
    floerEnergyDensity_and_hamiltonianCurvature_receiving (ω := ω) (Ha := Ha) hq hab hL u hz
  have hins := setIntegral_hamiltonianCurvature_inserted (ω := ω) hq hHa hHb hHas hHbs hab hL u
  -- The curvature, the area density and the energy density are integrable over both pieces.
  have hRT : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)) :=
    (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation ω hHb hHbs
      (by linarith) hPo hTP hu.continuousOn).congr_fun (fun z hz ↦ (hrec hz).2.symm) hT
  have hRA := hins.2.2 (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncation ω
    hHa hHas (by linarith) (hPo.preimage (contDiff_realChart_plumbingMap q L (n := 0)).continuous)
    (fun w hw ↦ hAP ⟨w, hw, rfl⟩)
    ((hu.comp (contDiff_realChart_plumbingMap q L).contMDiff.contMDiffOn
      (mapsTo_preimage _ _)).continuousOn))
  have harea := (ω.isSmoothForm.of_le (by simp)).continuousOn_apply_mfderiv hPo hu
    stdComplexLineReal stdComplexLineImag
  simp only [← SmoothBundleForm.eval₂_apply] at harea
  obtain ⟨hEins, hAins⟩ := setIntegral_floerEnergyDensity_inserted (ω := ω) hq hHa hHb hHas hHbs
    hab hL hu
  rw [setIntegral_truncation_union_image_of_integrableOn hq
      (hω.integrableOn_floerEnergyDensity hPo hu hKs hKt hTc hTP hRT)
      (hω.integrableOn_floerEnergyDensity hPo hu hKs hKt hAc hAP hRA),
    setIntegral_truncation_union_image_of_integrableOn hq
      ((harea.mono hTP).integrableOn_compact hTc) ((harea.mono hAP).integrableOn_compact hAc),
    setIntegral_truncation_union_image_of_integrableOn hq hRT hRA,
    setIntegral_congr_fun hT fun z hz ↦ (hrec hz).1,
    setIntegral_congr_fun hT fun z hz ↦ (hrec hz).2, hEins, hAins, hins.1]
  exact ⟨rfl, rfl, rfl⟩

/-- **The energy identity on the plumbed four-punctured sphere, for a manifold target.** Plumb
the output end of a pair of pants with period-one `C¹` Hamiltonians `Ha` into the input end
`q ≠ ∞` of one with period-one `C¹` Hamiltonians `Hb`, with `Hb q = Ha ∞`, along a neck of length
`L > 4`, for Hamiltonians on a finite-dimensional manifold with a nondegenerate two-form. Let `u`
be `C¹` on the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, in real coordinates. Over the plumbed
truncation `S_{L/2} ∪ ψ(S_{L/2})`, the Floer energy of `u` for the plumbed perturbation `K` is

`∫ u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, ℓ'_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, ℓ_r(t)) dt - ∫ R_K(u)`,

the symplectic area, plus the Hamiltonian terms of the loops `ℓ'_r(t) = u(ψ(φ_r(L/2 + i t)))`
along the input circles of the inserted pair of pants and of the loops
`ℓ_r(t) = u(φ_r(±L/2 + i t))` along the remaining input and output circles of the receiving one,
with the sign `-` on the output, minus the integrated curvature. The terms of the circle in the
middle of the neck cancel: it is both the output circle of the inserted pair of pants and the
input circle `q` of the receiving one, with the same Hamiltonian. -/
theorem IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
          (q.plumbingMap L (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))))) +
        (∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (u
          (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
            (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  have hR : (1 : ℝ) ≤ L / 2 := by linarith
  have hPo := isOpen_plumbedSphere q L
  have hAP := realChart_plumbingMap_image_subset hq hL
  obtain ⟨hE, hA, hRK⟩ := hω.setIntegral_plumbedTruncation_eq_add hq hHa hHb hHas hHbs hab hL hu
  rw [hE, hA, hRK,
    hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_of_subset hHb hHbs hR hPo
      (fun z hz ↦ mem_plumbedSphere_of_mem_truncation hq hL hz) hu,
    -- The map `u ∘ ψ` on the inserted pair of pants is `C¹` near its truncation `S_{L/2}`.
    hω.integral_floerEnergyDensity_pairOfPantsPerturbation_truncation_of_subset hHa hHas hR
      (hPo.preimage (contDiff_realChart_plumbingMap q L (n := 0)).continuous)
      (fun w hw ↦ hAP ⟨w, hw, rfl⟩)
      (hu.comp (contDiff_realChart_plumbingMap q L).contMDiff.contMDiffOn (mapsTo_preimage _ _)),
    smoothTransition.one_of_one_le (by linarith), one_mul, one_mul,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ q),
    ← Finset.add_sum_erase _ _ (Finset.mem_univ inf)]
  -- The inputs of the inserted pair of pants have sign `+`, and its output circle is the input
  -- circle `q` of the receiving one, with the same Hamiltonian, so their terms cancel.
  have hchart (w : ℂ) : (u ∘ realChart (q.plumbingMap L)) (Complex.equivRealProdCLM w) =
      u (Complex.equivRealProdCLM (q.plumbingMap L w)) := by
    rw [comp_apply, realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
  have hinputs : ∑ r ∈ Finset.univ.erase inf, r.endSign * ∫ t in (0 : ℝ)..1, Ha r t
      ((u ∘ realChart (q.plumbingMap L)) (Complex.equivRealProdCLM
        (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I)))) =
      ∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
        (q.plumbingMap L (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I))))) :=
    Finset.sum_congr rfl fun r hr ↦ by
      simp only [hchart, endSign_eq_one (Finset.ne_of_mem_erase hr), one_mul]
  rw [hinputs]
  simp only [hchart, plumbingMap_cylindricalEndLift_inf hq, ← hab]
  rw [endSign_inf, endSign_eq_one hq]
  ring

/-- **The energy bound on the plumbed four-punctured sphere, for a manifold target.** Under the
hypotheses of `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedPerturbation`, if
`|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, then the Floer energy over the plumbed truncation differs from
the symplectic area plus the Hamiltonian terms of its four boundary loops by at most
`∑ r, Ba r + ∑ r, Bb r`, uniformly in the neck length `L > 4`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      ((∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
          (q.plumbingMap L (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))))) +
        ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (u
          (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I)))))| ≤
      ∑ r, Ba r + ∑ r, Bb r := by
  rw [hω.integral_floerEnergyDensity_plumbedPerturbation hq hHa hHb hHas hHbs hab hL hu,
    sub_sub_cancel_left, abs_neg]
  exact ω.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb hHas hHbs hab hL
    hBa hBb u _

/-- **The topological energy of a solution on the plumbed four-punctured sphere is bounded below,
for a manifold target.** Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le`, let `u`
solve the Floer equation `(du - X_K)^{0,1} = 0` on the plumbed truncation for almost complex
structures `J z` on the tangent spaces `T_{u(z)} M` tamed by the two-form. Since its energy is
nonnegative, its symplectic area plus the Hamiltonian terms of its four boundary loops is at least
`-(∑ r, Ba r + ∑ r, Bb r)`, whatever the neck length `L > 4`. -/
theorem IsNondegenerate.neg_sum_le_integral_add_sum_of_plumbedPerturbation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹'
      (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹'
      (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -(∑ r, Ba r + ∑ r, Bb r) ≤
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹'
          (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)),
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        (∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
          (q.plumbingMap L (r.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I)))))) +
        ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (u
          (Complex.equivRealProdCLM
            (r.cylindricalEndLift (↑(r.endSign * (L / 2)) + ↑t * Complex.I)))) := by
  have hE := setIntegral_nonneg (μ := volume) (measurableSet_preimage_truncation_union_image q L _)
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (hω.abs_integral_floerEnergyDensity_plumbedPerturbation_sub_le hq hHa hHb
    hHas hHbs hab hL hBa hBb hu)).2
  linarith

end TauCeti.SmoothTwoForm
