/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Basic
import TauCeti.Analysis.Calculus.ContDiff.Cutoff
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

**Manifold targets.** For a finite-dimensional manifold `M` with a nondegenerate two-form `ω`,
such as a closed symplectic manifold, and a map `u` which is `C¹` on the four-punctured sphere,
the loops along the boundary circles bound no canonical discs, and the identity is stated with the
symplectic area. The outer ends may be truncated at any height `R ≥ L/2`, independent of the neck:
over the truncated plumbed sphere `Σ_R = q.plumbedTruncation L R`, the part `s_q ≤ L/2` of the
truncation `S_R` of `S` together with the image under `ψ` of the part `-s_∞ ≤ L/2` of the
truncation `S_R` of `S'`,

`∫_{Σ_R} E(u) = ∫_{Σ_R} u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, ℓ'_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, ℓ_r(t)) dt
  - ∫_{Σ_R} R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedTruncation`), where now
`ℓ'_r(t) = u(ψ(φ_r(R + i t)))` and `ℓ_r(t) = u(φ_r(±R + i t))` run along the four outer circles at
height `R`, again with the terms of the middle circle of the neck cancelling. With the same
curvature bound, the energy differs from the symplectic area plus the Hamiltonian terms by at most
`∑ r, Ba r + ∑ r, Bb r` (`SmoothTwoForm`'s
`IsNondegenerate.abs_integral_floerEnergyDensity_plumbedTruncation_sub_le`), and for a solution of
the Floer equation with tame almost complex structures this topological part is at least
`-(∑ r, Ba r + ∑ r, Bb r)`, uniformly in `L > 4` and `R ≥ L/2` (`SmoothTwoForm`'s
`IsNondegenerate.neg_sum_add_sum_le_integral_add_sum_add_sum_of_plumbedTruncation`). For `R = L/2`,
`Σ_R` is the plumbed truncation `S_{L/2} ∪ ψ(S_{L/2})`
(`TauCeti.ThricePuncturedSphere.Puncture.plumbedTruncation_div_two`), so rewriting along it
specializes these statements to that set. On a target which is not symplectically aspherical the
area term depends on the homotopy class of `u`; caps of the four boundary loops turn it into capped
actions and the area of a sphere, which is not done here.

No cutoff is needed on a manifold. Each half of `Σ_R` is a truncated pair of pants with one end cut
short along the middle circle of the neck, and its energy identity
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsPerturbation_inter`) only
requires its map to be `C¹` near that half, which `u` and `u ∘ ψ` are. The integrals over the
inserted half are transported along `ψ` by the change of variables formula
(`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_image`,
`TauCeti.SmoothTwoForm.integral_eval₂_mfderiv_stdComplexLine_image`), and the two halves meet in
the null circle `s_q = L/2`
(`TauCeti.ThricePuncturedSphere.Puncture.aedisjoint_truncation_inter_image`). The energy identity
over the whole four-punctured sphere, as `R → ∞`, is not treated here.

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

variable {X : Type*} {Ha Hb : Puncture → ℝ → X → ℝ} {q : Puncture} {L : ℝ}

/-- A function integrable over the receiving truncation `S_{L/2}` and over the image `ψ(S_{L/2})`
of the inserted one integrates over the plumbed truncation `S_{L/2} ∪ ψ(S_{L/2})` as the sum of
its integrals over the two pieces, which meet in a null set. -/
private theorem setIntegral_plumbedTruncation_of_integrableOn (hq : q ≠ inf) {f : ℝ × ℝ → ℝ}
    (hfT : IntegrableOn f (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)))
    (hfA : IntegrableOn f (realChart (q.plumbingMap L) ''
      (Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2)))) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹'
        (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2)), f z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' truncation (L / 2), f z) +
        ∫ z in realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹'
          truncation (L / 2)), f z := by
  have hA := (isCompact_preimage_truncation (L / 2)).image
    (contDiff_realChart_plumbingMap q L (n := 0)).continuous
  have hd := (aedisjoint_truncation_inter_image (L := L) hq (L / 2)).mono
    (fun z hz ↦ ⟨hz, (mem_truncation.1 hz).2.2 q⟩)
    (image_mono fun w hw ↦ ⟨hw, (mem_truncation.1 hw).2.2 inf⟩)
  rw [preimage_union, preimage_image_plumbingMap]
  exact setIntegral_union₀ hd hA.isClosed.measurableSet.nullMeasurableSet hfT hfA

/-- The plumbing chart maps a point of the inserted pair of pants outside the circle `s_∞ = -L/2`
into the plumbed four-punctured sphere. -/
private theorem realChart_plumbingMap_mem_plumbedSphere (hq : q ≠ inf) (hL : 0 < L)
    {w : ℝ × ℝ} (hw : w ∈ thricePuncturedSphereReal)
    (hwL : inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm w)).re ≤ L / 2) :
    (Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ 0 ∧
      Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ 1) ∧
      Complex.equivRealProdCLM.symm (realChart (q.plumbingMap L) w) ≠ q.plumbingMap L 1 := by
  rw [TauCeti.Complex.equivRealProdCLM_symm_realChart]
  exact plumbingMap_mem_plumbedSphere_of_endSign_mul_re_endCoord_le hq hL
    (mem_thricePuncturedSphereReal_iff.1 hw) hwL

/-- Outside the circle `s_∞ = -L/2` of the inserted pair of pants, the pullback of the plumbed
perturbation along the plumbing chart is the perturbation of the inserted pair of pants. -/
private theorem perturbationPullback_realChart_plumbedPerturbation (hq : q ≠ inf)
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℝ × ℝ} (hw₀ : Complex.equivRealProdCLM.symm w ≠ 0)
    (hwL : inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm w)).re ≤ L / 2) (x : X)
    (v : ℝ × ℝ) :
    perturbationPullback (realChart (q.plumbingMap L))
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      v w x =
        pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm w) x
          (Complex.equivRealProdCLM.symm v) := by
  rw [perturbationPullback_realChart _ (q.hasDerivAt_plumbingMap L _)]
  refine plumbedPerturbation_plumbingMap hq hab hw₀ ?_ x _
  rw [endSign_inf, neg_one_mul] at hwL
  linarith

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-! ### The curvature and energy of the two pieces, for a manifold target -/

/-- Inside the circle `s_q = L/2` of the receiving pair of pants, the curvature of the plumbed
perturbation along `u` is that of the receiving pair of pants. -/
private theorem hamiltonianCurvature_plumbedPerturbation_receiving (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hab : Hb q = Ha inf) (hL : 4 < L) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal)
    (hzL : q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z x =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        z x := by
  rw [endSign_eq_one hq, one_mul] at hzL
  exact congrFun (hamiltonianCurvature_plumbedPerturbation_of_re_endCoord_lt ω hq hab
    (ne_endCenter (mem_thricePuncturedSphereReal_iff.1 hz) q) (by linarith)) x

/-- Inside the circle `s_q = L/2` of the receiving pair of pants, the Floer energy density of `u`
for the plumbed perturbation is that for the perturbation of the receiving pair of pants. -/
private theorem floerEnergyDensity_plumbedPerturbation_receiving (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hab : Hb q = Ha inf) (hL : 4 < L) (u : ℝ × ℝ → M) {z : ℝ × ℝ}
    (hzL : q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2) :
    ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z := by
  rw [endSign_eq_one hq, one_mul] at hzL
  have hK (x : M) : plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x =
      pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x :=
    plumbedPerturbation_of_re_endCoord_le hq hab (by linarith) x
  simp only [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag, hK]

/-- Outside the circle `s_∞ = -L/2` of the inserted pair of pants, the curvature of its
perturbation is the Jacobian of the plumbing chart times the curvature of the plumbed perturbation
at the image point. -/
private theorem hamiltonianCurvature_pairOfPantsPerturbation_inserted (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {w : ℝ × ℝ} (hw : w ∈ thricePuncturedSphereReal)
    (hwL : inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm w)).re ≤ L / 2) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w x =
      (fderiv ℝ (realChart (q.plumbingMap L)) w).det * ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        (realChart (q.plumbingMap L) w) x := by
  have hP := realChart_plumbingMap_mem_plumbedSphere hq (by linarith) hw hwL
  rw [endSign_inf, neg_one_mul] at hwL
  rw [← ω.hamiltonianCurvature_perturbationPullback
      (contDiff_realChart_plumbingMap q L).contDiffAt
      (differentiableAt_plumbedPerturbation_domain hq hHa hHb hHas hHbs hab hL hP _ 1)
      (differentiableAt_plumbedPerturbation_domain hq hHa hHb hHas hHbs hab hL hP _ Complex.I)
      (mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL hP _ 1)
      (mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL hP _ Complex.I),
    hamiltonianCurvature_perturbationPullback_plumbedPerturbation ω hq hab
      (mem_thricePuncturedSphereReal_iff.1 hw).1 (by linarith)]

/-- Over the image under the plumbing chart of a measurable set `B` outside the circle
`s_∞ = -L/2` of the inserted pair of pants, the integrated curvature of the plumbed perturbation
along `u` is that of the inserted pair of pants along `u ∘ ψ` over `B`. -/
private theorem integral_hamiltonianCurvature_plumbedPerturbation_inserted
    (ω : SmoothTwoForm I M) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) (u : ℝ × ℝ → M) {B : Set (ℝ × ℝ)} (hBm : MeasurableSet B)
    (hB : ∀ w ∈ B, w ∈ thricePuncturedSphereReal ∧
      inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm w)).re ≤ L / 2) :
    ∫ z in realChart (q.plumbingMap L) '' B, ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      ∫ w in B, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        w ((u ∘ realChart (q.plumbingMap L)) w) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hBm
    (fun w _ ↦ ((contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero
      w).hasFDerivAt.hasFDerivWithinAt)
    (realChart_injective (q.plumbingMap_injective L)).injOn]
  refine setIntegral_congr_fun hBm fun w hw ↦ ?_
  rw [abs_of_nonneg (det_fderiv_realChart_plumbingMap_nonneg q L w), smul_eq_mul, comp_apply,
    hamiltonianCurvature_pairOfPantsPerturbation_inserted ω hq hHa hHb hHas hHbs hab hL
      (hB w hw).1 (hB w hw).2]

/-- Over the image under the plumbing chart of a measurable set `B` outside the circle
`s_∞ = -L/2` of the inserted pair of pants, the Floer energy of `u` for the plumbed perturbation
is that of `u ∘ ψ` over `B` for the perturbation of the inserted pair of pants. -/
private theorem integral_floerEnergyDensity_plumbedPerturbation_inserted (ω : SmoothTwoForm I M)
    (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) {B : Set (ℝ × ℝ)}
    (hBm : MeasurableSet B)
    (hB : ∀ w ∈ B, w ∈ thricePuncturedSphereReal ∧
      inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm w)).re ≤ L / 2) :
    ∫ z in realChart (q.plumbingMap L) '' B, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      ∫ w in B, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.plumbingMap L)) w := by
  have hP {w : ℝ × ℝ} (hw : w ∈ B) :=
    realChart_plumbingMap_mem_plumbedSphere hq (by linarith) (hB w hw).1 (hB w hw).2
  rw [ω.integral_floerEnergyDensity_image hBm
    (realChart_injective (q.plumbingMap_injective L)).injOn
    (fun w _ ↦ (contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero w)
    (fun w _ ↦ det_fderiv_realChart_plumbingMap_nonneg q L w)
    (fun w hw ↦ (hu.contMDiffAt ((isOpen_plumbedSphere q L).mem_nhds (hP hw))).mdifferentiableAt
      one_ne_zero)
    (fun w hw ↦ mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL (hP hw)
      _ 1)
    (fun w hw ↦ mdifferentiableAt_plumbedPerturbation_target hq hHa hHb hHas hHbs hab hL (hP hw)
      _ Complex.I)]
  refine setIntegral_congr_fun hBm fun w hw ↦ ?_
  have hpull (v : ℝ × ℝ) : perturbationPullback (realChart (q.plumbingMap L))
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      v w = fun x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm w) x
        (Complex.equivRealProdCLM.symm v) :=
    funext fun x ↦ perturbationPullback_realChart_plumbedPerturbation hq hab hL
      (mem_thricePuncturedSphereReal_iff.1 (hB w hw).1).1 (hB w hw).2 x v
  simp only [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag, hpull, equivRealProdCLM_symm_stdComplexLineReal,
    equivRealProdCLM_symm_stdComplexLineImag]

/-- Along a map continuous on the plumbed four-punctured sphere, the curvature of the plumbed
perturbation is integrable over a truncation of the receiving pair of pants at nonnegative heights
`R` with `R q ≤ L/2`. -/
private theorem integrableOn_hamiltonianCurvature_plumbedPerturbation_receiving
    (ω : SmoothTwoForm I M) (hq : q ≠ inf) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : Puncture → ℝ} (hR : ∀ r, 0 ≤ R r) (hRq : R q ≤ L / 2)
    {u : ℝ × ℝ → M}
    (hu : ContinuousOn u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) (Complex.equivRealProdCLM.symm ⁻¹' truncationAt R) := by
  have hT {z : ℝ × ℝ} (hz : z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncationAt R) :
      z ∈ thricePuncturedSphereReal ∧
        q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2 :=
    ⟨preimage_truncationAt_subset_thricePuncturedSphereReal R hz,
      ((mem_truncationAt.1 hz).2.2 q).trans hRq⟩
  exact (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncationAt ω hHb hHbs hR
    (hu.mono fun _ hz ↦ mem_plumbedSphere_of_endSign_mul_re_endCoord_le hq (by linarith)
      (mem_thricePuncturedSphereReal_iff.1 (hT hz).1) (hT hz).2)).congr_fun
    (fun _ hz ↦ (hamiltonianCurvature_plumbedPerturbation_receiving ω hq hab hL (hT hz).1
      (hT hz).2 _).symm)
    (isCompact_preimage_truncationAt R).isClosed.measurableSet

/-- Along a map continuous on the plumbed four-punctured sphere, the curvature of the plumbed
perturbation is integrable over the image under the plumbing chart of a truncation of the inserted
pair of pants at nonnegative heights `R` with `R ∞ ≤ L/2`. -/
private theorem integrableOn_hamiltonianCurvature_plumbedPerturbation_inserted
    (ω : SmoothTwoForm I M) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : Puncture → ℝ} (hR : ∀ r, 0 ≤ R r)
    (hRi : R inf ≤ L / 2) {u : ℝ × ℝ → M}
    (hu : ContinuousOn u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z))
      (realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹' truncationAt R)) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  have hTm := (isCompact_preimage_truncationAt R).isClosed.measurableSet
  have hT {w : ℝ × ℝ} (hw : w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncationAt R) :
      w ∈ thricePuncturedSphereReal ∧
        inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm w)).re ≤ L / 2 :=
    ⟨preimage_truncationAt_subset_thricePuncturedSphereReal R hw,
      ((mem_truncationAt.1 hw).2.2 inf).trans hRi⟩
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hTm
    (fun w _ ↦ ((contDiff_realChart_plumbingMap q L (n := 1)).differentiable one_ne_zero
      w).hasFDerivAt.hasFDerivWithinAt)
    (realChart_injective (q.plumbingMap_injective L)).injOn]
  refine (integrableOn_hamiltonianCurvature_pairOfPantsPerturbation_truncationAt ω hHa hHas hR
    (hu.comp (contDiff_realChart_plumbingMap q L (n := 0)).continuous.continuousOn
      fun _ hw ↦ realChart_plumbingMap_mem_plumbedSphere hq (by linarith) (hT hw).1
        (hT hw).2)).congr_fun (fun w hw ↦ ?_) hTm
  rw [abs_of_nonneg (det_fderiv_realChart_plumbingMap_nonneg q L w), smul_eq_mul]
  exact hamiltonianCurvature_pairOfPantsPerturbation_inserted ω hq hHa hHb hHas hHbs hab hL
    (hT hw).1 (hT hw).2 _

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
  refine setIntegral_congr_fun (isCompact_preimage_truncation _).isClosed.measurableSet
    fun z hz ↦ ?_
  rw [ω.floerEnergyDensity_congr_of_eventuallyEq _ _ (receivingPiece_eventuallyEq u hz),
    ← floerEnergyDensity_constSmooth, ← floerEnergyDensity_constSmooth]
  exact SmoothTwoForm.floerEnergyDensity_plumbedPerturbation_receiving ω.constSmooth hq hab hL u
    ((mem_truncation.1 hz).2.2 q)

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
  have h := SmoothTwoForm.integral_floerEnergyDensity_plumbedPerturbation_inserted ω.constSmooth
    hq hHa hHb (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHas r).contMDiff)
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hab hL
    (contMDiffOn_iff_contDiffOn.mpr (hu.of_le one_le_two))
    (isCompact_preimage_truncation _).isClosed.measurableSet fun w hw ↦
      ⟨preimage_truncation_subset_thricePuncturedSphereReal _ hw, (mem_truncation.1 hw).2.2 inf⟩
  simp only [floerEnergyDensity_constSmooth] at h
  rw [h]
  exact setIntegral_congr_fun (isCompact_preimage_truncation _).isClosed.measurableSet
    fun w hw ↦ (ω.floerEnergyDensity_congr_of_eventuallyEq _ _
      (insertedPiece_eventuallyEq u hw)).symm

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
  refine setIntegral_congr_fun (isCompact_preimage_truncation _).isClosed.measurableSet
    fun z hz ↦ ?_
  rw [(receivingPiece_eventuallyEq u hz).eq_of_nhds, ← hamiltonianCurvature_constSmooth,
    ← hamiltonianCurvature_constSmooth]
  exact SmoothTwoForm.hamiltonianCurvature_plumbedPerturbation_receiving ω.constSmooth hq hab hL
    (preimage_truncation_subset_thricePuncturedSphereReal _ hz) ((mem_truncation.1 hz).2.2 q) _

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
  have h := SmoothTwoForm.integral_hamiltonianCurvature_plumbedPerturbation_inserted ω.constSmooth
    hq hHa hHb (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHas r).contMDiff)
    (fun r ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHbs r).contMDiff) hab hL u
    (isCompact_preimage_truncation _).isClosed.measurableSet fun w hw ↦
      ⟨preimage_truncation_subset_thricePuncturedSphereReal _ hw, (mem_truncation.1 hw).2.2 inf⟩
  simp only [hamiltonianCurvature_constSmooth] at h
  rw [setIntegral_hamiltonianCurvature_pairOfPantsPerturbation_eq_truncation ω hHa hHas _
    (by linarith : (2 : ℝ) ≤ L / 2), h]
  refine setIntegral_congr_fun (isCompact_preimage_truncation _).isClosed.measurableSet
    fun w hw ↦ ?_
  rw [(insertedPiece_eventuallyEq u hw).eq_of_nhds, comp_apply]

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
  have hT := isCompact_preimage_truncation (L / 2)
  have hA := hT.image (contDiff_realChart_plumbingMap q L (n := 0)).continuous
  have hAP : realChart (q.plumbingMap L) '' (Complex.equivRealProdCLM.symm ⁻¹'
      truncation (L / 2)) ⊆ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
    rintro _ ⟨w, hw, rfl⟩
    exact realChart_plumbingMap_mem_plumbedSphere hq (by linarith)
      (preimage_truncation_subset_thricePuncturedSphereReal _ hw) ((mem_truncation.1 hw).2.2 inf)
  exact setIntegral_plumbedTruncation_of_integrableOn hq
    ((hf.mono fun z hz ↦ mem_plumbedSphere_of_mem_truncation hq hL hz).integrableOn_compact hT)
    ((hf.mono hAP).integrableOn_compact hA)

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
  have hψ : Continuous (q.plumbingMap L) := by
    have h : q.plumbingMap L = fun w => q.endCenter + q.plumbingFactor L * w :=
      funext (plumbingMap_apply q L)
    rw [h]
    fun_prop
  have hDm : MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹'
      (truncation (L / 2) ∪ q.plumbingMap L '' truncation (L / 2))) :=
    (((isCompact_truncation _).union ((isCompact_truncation _).image hψ)).isClosed.preimage
      Complex.equivRealProdCLM.symm.continuous).measurableSet
  have hE := setIntegral_nonneg (μ := volume) hDm fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJ z hz) (hfloer z hz)
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

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M] [IsManifold I ⊤ M]
  {ω : SmoothTwoForm I M} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture} {L : ℝ}

/-! ### The energy identity for a manifold target -/

variable [FiniteDimensional ℝ E]

/-- **The energy identity on the truncated plumbed four-punctured sphere, for a manifold target.**
Plumb the output end of a pair of pants with period-one `C¹` Hamiltonians `Ha` into the input end
`q ≠ ∞` of one with period-one `C¹` Hamiltonians `Hb`, with `Hb q = Ha ∞`, along a neck of length
`L > 4`, for Hamiltonians on a finite-dimensional manifold with a nondegenerate two-form, such as a
closed symplectic manifold. Let `u` be `C¹` on the four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}`, in
real coordinates. For `R ≥ L/2`, over the truncated plumbed sphere
`Σ_R = q.plumbedTruncation L R`, the Floer energy of `u` for the plumbed perturbation `K` is the
symplectic area, plus the Hamiltonian terms of the four boundary circles, minus the integrated
curvature:

`∫_{Σ_R} E = ∫_{Σ_R} u^*ω + ∑_{r ≠ ∞} ∫₀¹ Ha_r(t, ℓ'_r(t)) dt + ∑_{r ≠ q} ±∫₀¹ Hb_r(t, ℓ_r(t)) dt
  - ∫_{Σ_R} R_K(u)`.

Here `ℓ'_r(t) = u(ψ(φ_r(R + i t)))` runs along the images of the circles `s = R` of the input
ends of the inserted pair of pants and `ℓ_r(t) = u(φ_r(±R + i t))` along the circles `±s = R` of
the remaining input and output ends of the receiving one, with the sign `+` on inputs and `-` on
the output. The circle in the middle of the neck does not contribute: it is both the output circle
of the inserted pair of pants and the input circle `q` of the receiving one, with the same
Hamiltonian `Ha ∞ = Hb q`, so its two terms cancel. For a symplectic vector space target the area
and the Hamiltonian terms combine into the actions of the four loops, in
`SymplecticForm.integral_floerEnergyDensity_plumbedTruncation_eq_sum_hamiltonianAction`. -/
theorem IsNondegenerate.integral_floerEnergyDensity_plumbedTruncation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : ℝ} (hR : L / 2 ≤ R) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    ∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z =
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (u
            (Complex.equivRealProdCLM
              (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) -
        ∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, ω.hamiltonianCurvature
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          z (u z) := by
  set P := {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}
  -- The receiving piece `A` and the inserted piece `B` are truncations at given heights.
  set A := Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
    {z | q.endSign * (q.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}
  set B := Complex.equivRealProdCLM.symm ⁻¹' truncation R ∩
    {z | inf.endSign * (inf.endCoord (Complex.equivRealProdCLM.symm z)).re ≤ L / 2}
  have hL2 : (1 : ℝ) ≤ L / 2 := by linarith
  have hR₀ (r r' : Puncture) : 0 ≤ Function.update (fun _ ↦ R) r (L / 2) r' :=
    le_update_iff (x := fun _ ↦ (0 : ℝ)).2 ⟨by linarith, fun _ _ ↦ by linarith⟩ r'
  have hAeq : A = _ := preimage_truncation_inter_eq_preimage_truncationAt q hR
  have hBeq : B = _ := preimage_truncation_inter_eq_preimage_truncationAt inf hR
  have hAc : IsCompact A := by rw [hAeq]; exact isCompact_preimage_truncationAt _
  have hBc : IsCompact B := by rw [hBeq]; exact isCompact_preimage_truncationAt _
  have hAm := hAc.isClosed.measurableSet
  have hBm := hBc.isClosed.measurableSet
  have hAP : A ⊆ P := fun z hz ↦ mem_plumbedSphere_of_endSign_mul_re_endCoord_le hq (by linarith)
    ⟨(mem_truncation.1 hz.1).1, (mem_truncation.1 hz.1).2.1⟩ hz.2
  have hBS (w : ℝ × ℝ) (hw : w ∈ B) := And.intro
    (preimage_truncation_subset_thricePuncturedSphereReal R hw.1) hw.2
  have hψBP : realChart (q.plumbingMap L) '' B ⊆ P := by
    rintro _ ⟨w, hw, rfl⟩
    exact realChart_plumbingMap_mem_plumbedSphere hq (by linarith) (hBS w hw).1 (hBS w hw).2
  have hψBc := hBc.image (contDiff_realChart_plumbingMap q L (n := 0)).continuous
  have hPo : IsOpen P := isOpen_plumbedSphere q L
  have hKp := contMDiffOn_uncurry_plumbedPerturbation hq hHa hHb hHas hHbs hab hL
  have hRA : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) A := by
    rw [hAeq]
    exact integrableOn_hamiltonianCurvature_plumbedPerturbation_receiving ω hq hHb hHbs hab hL
      (hR₀ q) (by simp) hu.continuousOn
  have hRB : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      z (u z)) (realChart (q.plumbingMap L) '' B) := by
    rw [hBeq]
    exact integrableOn_hamiltonianCurvature_plumbedPerturbation_inserted ω hq hHa hHb hHas hHbs
      hab hL (hR₀ inf) (by simp) hu.continuousOn
  have harea := (ω.isSmoothForm.of_le (by simp)).continuousOn_apply_mfderiv hPo hu
    stdComplexLineReal stdComplexLineImag
  simp only [← SmoothBundleForm.eval₂_apply] at harea
  -- The map `u ∘ ψ` is `C¹` near the inserted piece.
  have hψ := contDiff_realChart_plumbingMap q L (n := 1)
  have hv : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 (u ∘ realChart (q.plumbingMap L))
      (realChart (q.plumbingMap L) ⁻¹' P) :=
    hu.comp hψ.contMDiff.contMDiffOn (mapsTo_preimage _ _)
  have hmd {w : ℝ × ℝ} (hw : w ∈ B) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u
      (realChart (q.plumbingMap L) w) :=
    (hu.contMDiffAt (hPo.mem_nhds (hψBP ⟨w, hw, rfl⟩))).mdifferentiableAt one_ne_zero
  -- `Σ_R` is the union of the two pieces, which meet in a null set.
  have hsplit (f : ℝ × ℝ → ℝ) (hfA : IntegrableOn f A)
      (hfB : IntegrableOn f (realChart (q.plumbingMap L) '' B)) :
      ∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, f z =
        (∫ z in A, f z) + ∫ z in realChart (q.plumbingMap L) '' B, f z := by
    rw [preimage_plumbedTruncation hq L R]
    exact setIntegral_union₀ (aedisjoint_truncation_inter_image hq R)
      hψBc.isClosed.measurableSet.nullMeasurableSet hfA hfB
  -- Compute each piece with the energy identity of its pair of pants with one end cut short.
  rw [hsplit _ (hω.integrableOn_floerEnergyDensity hPo hu (hKp 1) (hKp Complex.I) hAc hAP hRA)
      (hω.integrableOn_floerEnergyDensity hPo hu (hKp 1) (hKp Complex.I) hψBc hψBP hRB),
    hsplit _ ((harea.mono hAP).integrableOn_compact hAc)
      ((harea.mono hψBP).integrableOn_compact hψBc),
    hsplit _ hRA hRB,
    setIntegral_congr_fun hAm fun z hz ↦
      floerEnergyDensity_plumbedPerturbation_receiving ω hq hab hL u hz.2,
    setIntegral_congr_fun hAm fun z hz ↦ hamiltonianCurvature_plumbedPerturbation_receiving ω hq
      hab hL (preimage_truncation_subset_thricePuncturedSphereReal R hz.1) hz.2 (u z),
    integral_floerEnergyDensity_plumbedPerturbation_inserted ω hq hHa hHb hHas hHbs hab hL hu hBm
      hBS,
    ω.integral_eval₂_mfderiv_stdComplexLine_image hBm
      (realChart_injective (q.plumbingMap_injective L)).injOn
      (fun w _ ↦ hψ.differentiable one_ne_zero w)
      (fun w _ ↦ det_fderiv_realChart_plumbingMap_nonneg q L w) fun w hw ↦ hmd hw,
    integral_hamiltonianCurvature_plumbedPerturbation_inserted ω hq hHa hHb hHas hHbs hab hL u hBm
      hBS,
    hω.integral_floerEnergyDensity_pairOfPantsPerturbation_inter hHb hHbs q hL2 hR hPo hAP hu,
    hω.integral_floerEnergyDensity_pairOfPantsPerturbation_inter hHa hHas inf hL2 hR
      (hPo.preimage hψ.continuous) (fun w hw ↦ hψBP ⟨w, hw, rfl⟩) hv,
    smoothTransition.one_of_one_le (by linarith : 1 ≤ R - 1),
    smoothTransition.one_of_one_le (by linarith : 1 ≤ L / 2 - 1), one_mul, one_mul, one_mul,
    one_mul]
  have hchart (w : ℂ) : realChart (q.plumbingMap L) (Complex.equivRealProdCLM w) =
      Complex.equivRealProdCLM (q.plumbingMap L w) := by
    rw [realChart_apply, ContinuousLinearEquiv.symm_apply_apply]
  -- The inputs of the inserted pair of pants have sign `+`; the output circle of the inserted pair
  -- of pants is the input circle `q` of the receiving one, with the same Hamiltonian, so their
  -- terms cancel.
  have hinputs : ∑ r ∈ Finset.univ.erase inf, r.endSign * ∫ t in (0 : ℝ)..1,
      Ha r t ((u ∘ realChart (q.plumbingMap L)) (Complex.equivRealProdCLM
        (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))) =
      ∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
        (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I))))) :=
    Finset.sum_congr rfl fun r hr ↦ by
      simp only [endSign_eq_one (Finset.ne_of_mem_erase hr), one_mul, comp_apply, hchart]
  have hcancel : inf.endSign * ∫ t in (0 : ℝ)..1,
      Ha inf t ((u ∘ realChart (q.plumbingMap L)) (Complex.equivRealProdCLM
        (inf.cylindricalEndLift (↑(inf.endSign * (L / 2)) + ↑t * Complex.I)))) =
      -(q.endSign * ∫ t in (0 : ℝ)..1, Hb q t (u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(q.endSign * (L / 2)) + ↑t * Complex.I))))) := by
    simp only [comp_apply, hchart, plumbingMap_cylindricalEndLift_inf hq, ← hab]
    rw [endSign_inf, endSign_eq_one hq]
    ring
  rw [hinputs, hcancel]
  ring

/-- **The energy bound on the truncated plumbed four-punctured sphere, for a manifold target.**
Under the hypotheses of
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_plumbedTruncation`, if
`|Ha r| ≤ Ba r` and `|Hb r| ≤ Bb r`, then the Floer energy over `Σ_R` differs from the symplectic
area plus the Hamiltonian terms of its four boundary circles by at most `∑ r, Ba r + ∑ r, Bb r`,
uniformly in the neck length `L > 4` and in `R ≥ L/2`. -/
theorem IsNondegenerate.abs_integral_floerEnergyDensity_plumbedTruncation_sub_le
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : ℝ} (hR : L / 2 ≤ R) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}) :
    |(∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R, ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z) -
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (u
            (Complex.equivRealProdCLM
              (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I)))))| ≤
      ∑ r, Ba r + ∑ r, Bb r := by
  have hsub (a b c : ℝ) : a + b - c - a - b = -c := by ring
  rw [hω.integral_floerEnergyDensity_plumbedTruncation hq hHa hHb hHas hHbs hab hL hR hu, hsub,
    abs_neg]
  exact ω.abs_setIntegral_hamiltonianCurvature_plumbedPerturbation_le hq hHa hHb hHas hHbs hab hL
    hBa hBb u _

/-- **The topological energy of a solution on the truncated plumbed four-punctured sphere is
bounded below, for a manifold target.** Let `u` solve the Floer equation `(du - X_K)^{0,1} = 0` on
`Σ_R` for almost complex structures `J z` on the tangent spaces `T_{u(z)} M` tamed by the
two-form, under the hypotheses of
`IsNondegenerate.abs_integral_floerEnergyDensity_plumbedTruncation_sub_le`. Since its energy is
nonnegative, its symplectic area over `Σ_R` plus the Hamiltonian terms of the four boundary
circles is at least `-(∑ r, Ba r + ∑ r, Bb r)`, whatever the neck length `L > 4` and `R ≥ L/2`. -/
theorem
    IsNondegenerate.neg_sum_add_sum_le_integral_add_sum_add_sum_of_plumbedTruncation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) (hL : 4 < L) {R : ℝ} (hR : L / 2 ≤ R) {Ba Bb : Puncture → ℝ}
    (hBa : ∀ r t x, |Ha r t x| ≤ Ba r) (hBb : ∀ r t x, |Hb r t x| ≤ Bb r) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {J : ∀ z, AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
      (hω.symplecticFormAt (u z)).Tames (J z))
    (hfloer : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z)
        (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) :
    -(∑ r, Ba r + ∑ r, Bb r) ≤
      (∫ z in Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R,
          (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
            (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∑ r ∈ Finset.univ.erase inf, ∫ t in (0 : ℝ)..1, Ha r t (u (Complex.equivRealProdCLM
            (q.plumbingMap L (r.cylindricalEndLift (↑R + ↑t * Complex.I)))))) +
          ∑ r ∈ Finset.univ.erase q, r.endSign * ∫ t in (0 : ℝ)..1, Hb r t (u
            (Complex.equivRealProdCLM
              (r.cylindricalEndLift (↑(r.endSign * R) + ↑t * Complex.I))))) := by
  have hE := setIntegral_nonneg (μ := volume) (measurableSet_preimage_plumbedTruncation q L R)
    fun z hz ↦ floerEnergyDensity_nonneg hω (hJ z hz) (hfloer z hz)
  have h := (abs_le.1 (hω.abs_integral_floerEnergyDensity_plumbedTruncation_sub_le hq hHa hHb hHas
    hHbs hab hL hR hBa hBb hu)).2
  linarith

end TauCeti.SmoothTwoForm
