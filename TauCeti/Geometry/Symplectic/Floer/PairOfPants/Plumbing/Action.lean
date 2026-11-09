/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Basic
public import TauCeti.Geometry.Symplectic.Floer.Action
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Action

/-!
# The energy identity on the plumbed four-punctured sphere

Plumb the output end of a pair of pants `S'` with Hamiltonians `Ha` into the input end `q` of a
pair of pants `S` with Hamiltonians `Hb`, along a neck of length `L > 4`, with `Hb q = Ha ∞`, and
equip the plumbed four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}` with the glued perturbation
`TauCeti.Floer.plumbedPerturbation` (see
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Basic`).

The energy identity holds on the truncation `Σ_R` of the plumbed sphere
(`TauCeti.ThricePuncturedSphere.Puncture.plumbedTruncation`), for `R ≥ L/2`: the part of the
truncation `S_R` inside the circle `Re z = L/2` of the end `q`, together with the image under `ψ`
of the part of the truncation `S'_R` outside the circle `Re z = -L/2` of its end at `∞`. The
energy over each part is given by the energy identity of a truncated pair of pants with one end
cut short,
`SymplecticForm.integral_floerEnergyDensity_pairOfPantsPerturbation_inter_eq_sum_hamiltonianAction`
in the coordinates of `S` and of `S'` respectively, the second after the change of variables
along `ψ`. The two cut loops along the middle of the neck are the same loop, by the
gluing law of the end lifts, and they carry the same Hamiltonian `Hb q = Ha ∞`, with opposite
signs: an input of `S` and the output of `S'`. So their actions cancel, and the energy over `Σ_R`
is the signed sum of the actions of the four boundary loops of `Σ_R` minus the integrated
curvature. With the curvature bound
`TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_plumbedPerturbation_le`, the energy
differs from this sum by at most the six end bounds, uniformly in `L` and `R`, and for solutions of
the Floer equation the action of the output loop is at most the sum of the actions of the three
input loops plus that constant.

## Main results

* `TauCeti.Floer.preimage_plumbedTruncation`: in the real coordinates, the truncation `Σ_R` is
  the union of its receiving part and the image of its inserted part under the plumbing chart.
* `TauCeti.Floer.isCompact_preimage_plumbedTruncation`,
  `TauCeti.Floer.measurableSet_preimage_plumbedTruncation`: in the real coordinates, the
  truncation `Σ_R` is compact and measurable.
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
  ETH Zürich (1995), on energy estimates for compositions of pair-of-pants products.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, EMS (2008), Section 9, on energy
  estimates on glued domains.
* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  energy identity.
-/

public noncomputable section

open Set Real Function
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart det_fderiv_realChart_nonneg equivRealProdCLM_symm_realChart
  realChart_equivRealProdCLM)

namespace TauCeti.Floer

variable {q : Puncture}

/-- The four-punctured sphere `ℂ ∖ {0, 1, ψ(1)}` is open in the real coordinates. -/
private theorem isOpen_plumbedSphereReal (q : Puncture) (L : ℝ) :
    IsOpen {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} :=
  isOpen_thricePuncturedSphereReal.inter
    (isOpen_ne_fun Complex.equivRealProdCLM.symm.continuous continuous_const)

/-- The truncated plumbed sphere, in the real coordinates, is the part of the truncation of the
receiving pair of pants inside the circle `Re z = L/2` of the end `q`, together with the image
under the plumbing chart of the part of the truncation of the inserted pair of pants outside the
circle `Re z = -L/2` of its end at `∞`. -/
theorem preimage_plumbedTruncation (hq : q ≠ inf) (L R : ℝ) :
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
      rw [realChart_equivRealProdCLM, hwz, ContinuousLinearEquiv.apply_symm_apply]
  · rintro (h | ⟨w, hw, rfl⟩)
    · exact Or.inl h
    · refine Or.inr ⟨Complex.equivRealProdCLM.symm w, hw, ?_⟩
      rw [equivRealProdCLM_symm_realChart]

/-- The truncation `Σ_R` of the plumbed sphere is compact in the real coordinates. -/
theorem isCompact_preimage_plumbedTruncation (q : Puncture) (L R : ℝ) :
    IsCompact (Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R) :=
  Complex.equivRealProdCLM.symm.toHomeomorph.isCompact_preimage.2
    (isCompact_plumbedTruncation q L R)

/-- The truncation `Σ_R` of the plumbed sphere is measurable in the real coordinates. -/
theorem measurableSet_preimage_plumbedTruncation (q : Puncture) (L R : ℝ) :
    MeasurableSet (Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R) :=
  (isCompact_preimage_plumbedTruncation q L R).isClosed.measurableSet

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ha Hb : Puncture → ℝ → V → ℝ} {q : Puncture} {L : ℝ}

/-! ### The energy identity on the plumbed four-punctured sphere -/

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
    rw [equivRealProdCLM_symm_realChart, re_endCoord_plumbingMap q L hw0, endSign_eq_one hq,
      one_mul] at h₁
    rw [endSign_inf] at h₂
    rw [image_endChart_prod_Ico fun s hs ↦ by
      rw [mem_singleton_iff.1 hs, endSign_eq_one hq]; linarith]
    refine ⟨⟨(mem_truncation.1 hzA.1).1, (mem_truncation.1 hzA.1).2.1⟩, ?_⟩
    rw [mem_singleton_iff, equivRealProdCLM_symm_realChart, re_endCoord_plumbingMap q L hw0]
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
    measurableSet_preimage_truncation_inter q R _
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
    measurableSet_preimage_truncation_inter inf R _
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
      (by rw [preimage_plumbedTruncation hq]; exact Or.inr (mem_image_of_mem _ hw) :
        realChart (q.plumbingMap L) w ∈ Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R)
  have hS₄o := isOpen_plumbedSphereReal q L
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
      (fun w _ ↦ det_fderiv_realChart_nonneg (q.hasDerivAt_plumbingMap L _))
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
      (fun w _ ↦ det_fderiv_realChart_nonneg (q.hasDerivAt_plumbingMap L _))
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
      · rw [equivRealProdCLM_symm_realChart, endSign_eq_one hq, one_mul,
          re_endCoord_plumbingMap q L hz.1]
        linarith
      · rw [equivRealProdCLM_symm_realChart] at h
        exact q.plumbingMap_injective L h)
  -- The loop along the cut is the loop along the circle `Re z = L/2` of the end `q`, and the
  -- loops along the input ends are the images under the plumbing map.
  have hneck : (fun t : ℝ ↦ (u ∘ realChart (q.plumbingMap L)) (Complex.equivRealProdCLM
      (inf.cylindricalEndLift (↑(inf.endSign * (L / 2)) + ↑t * Complex.I)))) =
      fun t : ℝ ↦ u (Complex.equivRealProdCLM
        (q.cylindricalEndLift (↑(L / 2) + ↑t * Complex.I))) := by
    funext t
    rw [comp_apply, realChart_equivRealProdCLM, ← cylindricalEndLift_add_ofReal, endSign_inf]
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
        realChart_equivRealProdCLM]
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
  have hS₄o : IsOpen S₄ := isOpen_plumbedSphereReal q L
  have hPS₄ : Complex.equivRealProdCLM.symm ⁻¹' q.plumbedTruncation L R ⊆ S₄ := fun z hz ↦
    plumbedTruncation_subset hq (by linarith) R hz
  have hPc := isCompact_preimage_plumbedTruncation q L R
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
    measurable_image_of_fderivWithin (measurableSet_preimage_truncation_inter inf R _)
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
  have hE := setIntegral_nonneg (μ := volume) (measurableSet_preimage_plumbedTruncation q L R)
    fun z hz ↦
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
