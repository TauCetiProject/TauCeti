/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Capped
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.LongNeck
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart

/-!
# Compactness at the long-neck end of the capped comparison family in a closed manifold

The comparison between the pair-of-pants product and the quantum product caps the three ends of
the pair of pants `S = ℂ ∖ {0, 1}` with Piunikhin–Salamon–Schwarz planes, giving a sphere with
three poles `0`, `1` and `∞`, and carries the one-parameter family of Floer data
`K_R = TauCeti.Floer.cappedComparisonPerturbation H R` with the almost complex structures
`J_R = TauCeti.SmoothTwoForm.Compatible.cappedComparisonAlmostComplex h₀ J hJ R` on the tangent
bundle of the target. For `R ≥ 2` there are necks of length `R - 1` along the three ends, and as
`R → ∞` the sphere breaks into the pair of pants and three PSS planes: the long-neck end of the
family, whose broken configurations give the composite of the pair-of-pants product with the PSS
maps. Compactness over compact windows of parameters is in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Capped`; it does not reach this end,
where the parameters are unbounded. The interior part of Gromov–Floer compactness at this end, for
a symplectic vector space target, is
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.LongNeck`. This file proves it for a
closed manifold `M` with a nondegenerate two-form `σ`, such as a closed symplectic manifold, with no
condition on where the solutions take their values, uniformly in `R`.

* **The pair of pants.** On the truncation `S_T` the comparison datum is the pair-of-pants
  perturbation `TauCeti.Floer.pairOfPantsPerturbation H` as soon as `T ≤ R + 1`, and the
  structure is that of neck length `T`
  (`TauCeti.Floer.cappedPerturbation_eq_smul_pairOfPantsPerturbation`,
  `TauCeti.SmoothTwoForm.Compatible.cappedAlmostComplex_eq_pairOfPantsAlmostComplex`). Neither
  depends on `R`.
* **The caps of the PSS planes.** Beyond the neck at the end `q`, the data read through the
  translation `χ = TauCeti.ThricePuncturedSphere.Puncture.endShift q (R - 1)` by the neck length
  are the data `TauCeti.Floer.cappedPerturbation 1 0 H` and
  `TauCeti.SmoothTwoForm.Compatible.cappedAlmostComplex h₀ J hJ 1 0` with no neck
  (`TauCeti.Floer.perturbationPullback_cappedComparisonPerturbation_endShift`,
  `TauCeti.SmoothTwoForm.Compatible.cappedAlmostComplex_endShift`). Since `χ` is holomorphic,
  `u ∘ χ` solves the Floer equation of these fixed data there
  (`TauCeti.SmoothTwoForm.Compatible.isComplexLinearMap_perturbedMFDeriv_comp_realChart_endShift`),
  and its energy over a region `Ω` is the energy of `u` over `χ(Ω)`
  (`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_image_endShift`).
* **The energy bound.** A solution of area at most `A` has Floer energy at most
  `A + 2 (B₀ + B₁ + B_∞)` over every region, for `|H_q| ≤ B_q` and every `R ≥ 0`
  (`IsNondegenerate.setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le` in the
  namespace `TauCeti.SmoothTwoForm`).

So on each of the four pieces the solutions, or their translates, solve the Floer equation of fixed
data with uniformly bounded energy, and compactness for fixed data in a closed manifold
(`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in the
namespace `TauCeti.SmoothTwoForm`) applies on each, with a threshold independent of `R`. The
almost complex structures of the fixed data are `C²` read in the charts of `M` by the smoothness of
the capped structures
(`TauCeti.SmoothTwoForm.Compatible.contMDiff_cappedAlmostComplex`). As in
`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding of a
closed manifold, with the structures uniformly tame with respect to `e` and the pushforwards
through `e` of the Hamiltonian vector fields bounded, on the windows considered.

## Main results

In the namespace `TauCeti.SmoothTwoForm`:

* `Compatible.isComplexLinearMap_perturbedMFDeriv_comp_realChart_endShift`,
  `integral_floerEnergyDensity_image_endShift`: the Floer equation and the energy on the cap of a
  PSS plane piece, read through the translation by the neck length, for a manifold target.

In the namespace `TauCeti.SmoothTwoForm.Compatible`:

* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_truncation`
  : on an open subset of a compact window of the truncation `S_T`, solutions for parameters
  `Rₖ ≥ max 2 (T - 1)` converge off finitely many bubbling points.
* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_endShift_subseq_off_finset_cappedComparison`:
  on an open subset of a compact window of the plane, made of the center of the end `q` and points
  beyond the neck, the translated solutions `uₖ ∘ χ_{q, Rₖ - 1}` converge off finitely many
  bubbling points.
* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_longNeck`:
  a single subsequence along which the solutions converge on the pair of pants and the translated
  solutions converge on the caps of all three PSS planes.

The cylindrical ends of the PSS planes below their caps, the Floer cylinders that break off along
the three necks, the bubbles at the bubbling points and the regularity of the limits are not
treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points), Section 10.9 (gluing and the limits of glued domains) and
  Section 12.1 (the PSS isomorphism).
-/

public section

open Bundle Complex Filter Function MeasureTheory Metric Set Topology
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart equivRealProdCLM_symm_realChart realChart_injective
  det_fderiv_realChart_nonneg)
open scoped Manifold

namespace TauCeti.Floer

/-- On the truncation `S_T`, the comparison datum with parameter `R ≥ 2` and `T ≤ R + 1` is the
pair-of-pants perturbation. -/
private theorem cappedComparisonPerturbation_eq_pairOfPantsPerturbation {M : Type*}
    {H : Puncture → ℝ → M → ℝ} {R T : ℝ} (hR : 2 ≤ R) (hRT : T ≤ R + 1) {w : ℂ}
    (hw : w ∈ truncation T) (x : M) :
    cappedComparisonPerturbation H R w x = pairOfPantsPerturbation H w x := by
  rw [cappedComparisonPerturbation_of_two_le H hR,
    cappedPerturbation_eq_smul_pairOfPantsPerturbation
      fun q ↦ ((mem_truncation.1 hw).2.2 q).trans (by linarith), one_smul]

end TauCeti.Floer

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I (⊤ : ℕ∞) M] {σ : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}
  {J₀ : SmoothAlmostComplexStructure I M} {J : Puncture → ℝ → SmoothAlmostComplexStructure I M}

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] in
/-- Each component of the comparison datum is differentiable in the target point. -/
private theorem mdifferentiableAt_cappedComparisonPerturbation_apply
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (R : ℝ) (z : ℝ × ℝ) (x : M) (v : ℂ) :
    MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y v) x := by
  rw [cappedComparisonPerturbation_def]
  exact (((contMDiff_cappedPerturbation_apply hH hHs (comparisonCutoff R) (comparisonNeckLength R)
    v).comp (contMDiff_const.prodMk contMDiff_id)).mdifferentiable one_ne_zero) x

/-- **The Floer equation on the caps of the PSS plane pieces, in a manifold.** For `R ≥ 2`, let `χ`
be the translation `TauCeti.ThricePuncturedSphere.Puncture.endShift q (R - 1)` by the neck length
along the end `q`. At a point `w` which is the center `c_q` of the end, its pole for an input end,
or has signed longitudinal coordinate at least `2` on it, if `u` solves the Floer equation of the
comparison family at `χ(w)`, then `u ∘ χ` solves the Floer equation of the data
`TauCeti.Floer.cappedPerturbation 1 0 H` and
`TauCeti.SmoothTwoForm.Compatible.cappedAlmostComplex h₀ J hJ 1 0` with no neck at `w`. -/
theorem Compatible.isComplexLinearMap_perturbedMFDeriv_comp_realChart_endShift
    (h₀ : σ.Compatible J₀) {hJ : ∀ q t, σ.Tames (J q t)} {q : Puncture}
    (hJp : Periodic (J q) 1) (hH : ∀ r, Periodic (H r) 1)
    (hHs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H r))) {R : ℝ} (hR : 2 ≤ R)
    {w : ℝ × ℝ} (hw : equivRealProdCLM.symm w = q.endCenter ∨
      2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) {u : ℝ × ℝ → M}
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (realChart (q.endShift (R - 1)) w))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      ((h₀.cappedComparisonAlmostComplex J hJ R
        (equivRealProdCLM.symm (realChart (q.endShift (R - 1)) w))).almostComplexStructureAt
          (u (realChart (q.endShift (R - 1)) w)))
      (σ.perturbedMFDeriv
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x Complex.I)
        u (realChart (q.endShift (R - 1)) w)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      ((h₀.cappedAlmostComplex J hJ 1 0 (equivRealProdCLM.symm w)).almostComplexStructureAt
        ((u ∘ realChart (q.endShift (R - 1))) w))
      (σ.perturbedMFDeriv (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.endShift (R - 1))) w).toLinearMap := by
  rw [equivRealProdCLM_symm_realChart, cappedComparisonAlmostComplex_of_two_le h₀ J hJ hR,
    cappedAlmostComplex_endShift h₀ J hJ hJp 1 (by linarith) hw] at h
  have h' := σ.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    ((q.contDiff_realChart_endShift (R - 1) (n := 1)).differentiable one_ne_zero w) hu
    (mdifferentiableAt_cappedComparisonPerturbation_apply hH hHs R _ _ 1)
    (mdifferentiableAt_cappedComparisonPerturbation_apply hH hHs R _ _ Complex.I)
    (isComplexLinearMap_fderiv_realChart (q.hasDerivAt_endShift _ _)) h
  rwa [σ.perturbedMFDeriv_congr_perturbation
    (Ks' := fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
    (Kt' := fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I) _
    (funext fun x ↦ by rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR hw,
      equivRealProdCLM_symm_stdComplexLineReal])
    (funext fun x ↦ by rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR hw,
      equivRealProdCLM_symm_stdComplexLineImag])] at h'

omit [FiniteDimensional ℝ E] in
/-- **The energy on the caps of the PSS plane pieces, in a manifold.** For `R ≥ 2`, let `χ` be the
translation `TauCeti.ThricePuncturedSphere.Puncture.endShift q (R - 1)` by the neck length along the
end `q`. On a measurable set `Ω` of points which are the center `c_q` of the end, its pole for an
input end, or have signed longitudinal coordinate at least `2` on it, the energy of `u` for the
comparison datum `K_R` over `χ(Ω)` is the energy of `u ∘ χ` for the datum
`TauCeti.Floer.cappedPerturbation 1 0 H` with no neck over `Ω`. -/
theorem integral_floerEnergyDensity_image_endShift (ω : SmoothTwoForm I M)
    (hH : ∀ r, Periodic (H r) 1)
    (hHs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H r))) {q : Puncture}
    {R : ℝ} (hR : 2 ≤ R) {Ω : Set (ℝ × ℝ)} (hΩm : MeasurableSet Ω)
    (hΩ : ∀ w ∈ Ω, equivRealProdCLM.symm w = q.endCenter ∨
      2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) {u : ℝ × ℝ → M}
    (hu : ∀ w ∈ Ω, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (realChart (q.endShift (R - 1)) w)) :
    ∫ z in realChart (q.endShift (R - 1)) '' Ω, ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x Complex.I) u z =
      ∫ w in Ω, ω.floerEnergyDensity
        (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.endShift (R - 1))) w := by
  rw [ω.integral_floerEnergyDensity_image hΩm (realChart_injective (q.endShift_injective _)).injOn
    (fun w _ ↦ (q.contDiff_realChart_endShift (R - 1) (n := 1)).differentiable one_ne_zero w)
    (fun w _ ↦ det_fderiv_realChart_nonneg (q.hasDerivAt_endShift _ _)) hu
    (fun w _ ↦ mdifferentiableAt_cappedComparisonPerturbation_apply hH hHs R _ _ 1)
    (fun w _ ↦ mdifferentiableAt_cappedComparisonPerturbation_apply hH hHs R _ _ Complex.I)]
  refine setIntegral_congr_fun hΩm fun w hw ↦ ω.floerEnergyDensity_congr_perturbation _
    (funext fun x ↦ ?_) (funext fun x ↦ ?_)
  · rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR (hΩ w hw),
      equivRealProdCLM_symm_stdComplexLineReal]
  · rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR (hΩ w hw),
      equivRealProdCLM_symm_stdComplexLineImag]

/-- The capped structures of a fixed cutoff parameter and neck length, read in the plane chart,
are `C²` jointly in the domain point and the target point. -/
private theorem Compatible.contMDiffAt_cappedAlmostComplex_equivRealProdCLM (h₀ : σ.Compatible J₀)
    (hJ : ∀ q t, σ.Tames (J q t)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (r L : ℝ) (z : ℝ × ℝ) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) (2 : ℕ∞)
      (fun p : (ℝ × ℝ) × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) p.2
        ((h₀.cappedAlmostComplex J hJ r L (equivRealProdCLM.symm p.1)).toEndomorphism p.2))
      (z, x) :=
  (h₀.contMDiff_cappedAlmostComplex J hJ (n := 2) hJp hJs contMDiff_const contMDiff_const
    (equivRealProdCLM.symm.contDiff.contMDiff.comp contMDiff_fst) contMDiff_snd).contMDiffAt

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] in
/-- Each component of the pair-of-pants perturbation, read in the plane chart, is `C³` jointly in
the point of `S` and the target point. -/
private theorem contMDiffAt_pairOfPantsPerturbation_apply_equivRealProdCLM
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    (v : ℂ) (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) (x : M) :
    ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1)
      (uncurry fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x v) (z, x) :=
  (((contMDiffAt_pairOfPantsPerturbation hH hHs ⟨equivRealProdCLM.symm z, hz⟩ x).comp (z, x)
    ((equivRealProdCLM.symm.contDiff.contMDiff.comp contMDiff_fst).prodMk
      contMDiff_snd).contMDiffAt).clm_apply contMDiffAt_const).of_le (by norm_num)

/-- On the truncation `S_T`, the structure of the comparison family with parameter `R ≥ 2` and
`T ≤ R + 1` is the capped structure of neck length `T`: both are the pair-of-pants structure. -/
private theorem Compatible.cappedComparisonAlmostComplex_eq_cappedAlmostComplex
    (h₀ : σ.Compatible J₀) (J : Puncture → ℝ → SmoothAlmostComplexStructure I M)
    (hJ : ∀ q t, σ.Tames (J q t)) {R T : ℝ} (hR : 2 ≤ R) (hRT : T ≤ R + 1) {w : ℂ}
    (hw : w ∈ truncation T) :
    h₀.cappedComparisonAlmostComplex J hJ R w = h₀.cappedAlmostComplex J hJ 1 T w := by
  obtain ⟨hw₀, hw₁, hwq⟩ := mem_truncation.1 hw
  rw [cappedComparisonAlmostComplex_of_two_le h₀ J hJ hR]
  exact (h₀.cappedAlmostComplex_eq_pairOfPantsAlmostComplex J hJ (w := ⟨w, hw₀, hw₁⟩) le_rfl
    fun q ↦ (hwq q).trans (by linarith)).trans
      (h₀.cappedAlmostComplex_eq_pairOfPantsAlmostComplex J hJ (w := ⟨w, hw₀, hw₁⟩) le_rfl
        fun q ↦ (hwq q).trans (by linarith)).symm

/-- **The energy on the caps of the PSS plane pieces is bounded along the long necks.** For a
solution `u` of the Floer equation of the comparison family at `R ≥ 2`, with integrable energy
density and curvature term and symplectic area at most `A`, and its translate `u ∘ χ` by the neck
length along the end `q`, the energy of the translate for the datum with no neck over a measurable
set `Ω` of points that are the center of the end or lie beyond the neck is at most
`A + 2 (B₀ + B₁ + B_∞)`. -/
private theorem Compatible.setIntegral_floerEnergyDensity_comp_realChart_endShift_le
    (h₀ : σ.Compatible J₀) (J : Puncture → ℝ → SmoothAlmostComplexStructure I M)
    (hJ : ∀ q t, σ.Tames (J q t)) (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) {q : Puncture} {R A : ℝ} (hR : 2 ≤ R)
    {Ω : Set (ℝ × ℝ)} (hΩm : MeasurableSet Ω)
    (hΩ : ∀ w ∈ Ω, equivRealProdCLM.symm w = q.endCenter ∨
      2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) {u : ℝ × ℝ → M}
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hfl : ∀ z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      ((h₀.cappedComparisonAlmostComplex J hJ R
        (equivRealProdCLM.symm z)).almostComplexStructureAt (u z))
      (σ.perturbedMFDeriv
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap)
    (hint : Integrable (σ.floerEnergyDensity
      (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x Complex.I) u))
    (hcurv : Integrable fun z ↦ σ.hamiltonianCurvature
      (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x Complex.I)
      z (u z))
    (harea : ∫ z, (SmoothBundleForm.eval₂ σ (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) ≤ A) :
    ∫ w in Ω, σ.floerEnergyDensity
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
      (u ∘ realChart (q.endShift (R - 1))) w ≤ A + 2 * ∑ q, B q := by
  rw [← σ.integral_floerEnergyDensity_image_endShift hH hHs hR hΩm hΩ
    fun w _ ↦ hu.mdifferentiableAt one_ne_zero]
  exact h₀.isNondegenerate.setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le hH hHs hB
    (by linarith) hu
    (fun z ↦ h₀.tames_almostComplexStructureAt_cappedComparisonAlmostComplex J hJ _ _ _)
    hfl hint hcurv harea _

section Closed

variable [I.Boundaryless] [CompactSpace M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {e : M → F}

namespace Compatible

/-- **Solutions of the capped comparison family in a closed manifold converge on the pair of pants,
uniformly along the long necks.** Let `σ` be a two-form on a closed manifold `M` compatible with a
smooth almost complex structure `J₀`, let the end structures `J q t` be tamed by `σ`, of period one
in `t` and jointly `C²` on `ℝ × M`, and let `H_q` be period-one `C³` Hamiltonians with
`|H_q| ≤ B_q`. Fix a truncation `S_T` of the pair of pants and a compact window `D ⊆ S_T` (in real
coordinates). Let `e : M → F` be injective and differentiable, with the capped structure of neck
length `T` uniformly tame with respect to `e` over `D`, `c ‖d e v‖² ≤ σ(v, J v)` with `c > 0`, and
the pushforwards through `e` of the Hamiltonian vector fields of the two components of the
pair-of-pants perturbation at most `L` there. There is a threshold `δ > 0` with the following
property. Let `uₖ` be `C³` maps of the plane chart `ℝ × ℝ ≅ ℂ` of the three-pole sphere into `M`
solving the Floer equation `(du - X_{K_{Rₖ}})^{0,1} = 0` for the structures `J_{Rₖ}(z, u)` of the
comparison family, with `Rₖ ≥ 2` and `T ≤ Rₖ + 1`, integrable energy density and curvature term,
and symplectic area `∫ uₖ^* σ ≤ A`, and let `Ω ⊆ D` be open. Then there are a subsequence `φ` and a
finite set `Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)` such that, along `φ`, every disc about a
point of `Z` eventually carries Floer energy at least `δ` for the pair-of-pants perturbation, the
energy densities are uniformly bounded on every compact subset of `Ω \ Z`, and the solutions
converge on `Ω \ Z` to a continuous map `v`, locally uniformly after applying `e` and pointwise in
`M`. The parameters `Rₖ` need not be bounded. -/
theorem
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_truncation
    (h₀ : σ.Compatible J₀) (J : Puncture → ℝ → SmoothAlmostComplexStructure I M)
    (hJ : ∀ q t, σ.Tames (J q t)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (T : ℝ) {D : Set (ℝ × ℝ)}
    (hD : IsCompact D) (hDT : D ⊆ equivRealProdCLM.symm ⁻¹' truncation T)
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      σ.eval₂ x v (h₀.cappedAlmostComplex J hJ 1 T (equivRealProdCLM.symm z) x v))
    (hLs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, 2 ≤ R k) → (∀ k, T ≤ R k + 1) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.cappedComparisonAlmostComplex J hJ (R k)
          (equivRealProdCLM.symm z)).almostComplexStructureAt (u k z))
        (σ.perturbedMFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, Integrable (σ.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        (u k))) →
      (∀ k, Integrable fun z ↦ σ.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        z (u k z)) →
      (∀ k, ∫ z, (SmoothBundleForm.eval₂ σ (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, σ.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L', σ.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  have hω := h₀.isNondegenerate
  have hDS : D ⊆ thricePuncturedSphereReal :=
    hDT.trans (preimage_truncation_subset_thricePuncturedSphereReal T)
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    (Ks := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
    (J := fun z ↦
      (h₀.cappedAlmostComplex J hJ 1 T (equivRealProdCLM.symm z)).almostComplexStructureAt)
    he he_inj isOpen_thricePuncturedSphereReal hD hDS
    (contDiffOn_almostComplexInChartAt_almostComplexStructureAt (n := 2)
      (J := fun z ↦ h₀.cappedAlmostComplex J hJ 1 T (equivRealProdCLM.symm z))
      fun z _ x ↦ contMDiffAt_cappedAlmostComplex_equivRealProdCLM h₀ hJ hJp hJs 1 T z x)
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt
      (contMDiffAt_pairOfPantsPerturbation_apply_equivRealProdCLM hH hHs 1))
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt
      (contMDiffAt_pairOfPantsPerturbation_apply_equivRealProdCLM hH hHs Complex.I))
    (fun z _ x ↦ hω.tames_iff.1 (h₀.tames_cappedAlmostComplex J hJ 1 T _) x) hc
    (fun z hz x v ↦ by
      simpa only [IsNondegenerate.symplecticFormAt_apply,
        SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using hJc z hz x v)
    hLs hLt
  refine ⟨δ, hδ, fun Ω R u A hΩ hΩD hR2 hRT hu hfl hint hcurv harea ↦ ?_⟩
  set KR : ℕ → ℂ → ℝ × ℝ → M → ℝ := fun k v z x ↦
    cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x v
  set Kb : ℂ → ℝ × ℝ → M → ℝ := fun v z x ↦
    pairOfPantsPerturbation H (equivRealProdCLM.symm z) x v
  -- On `Ω` the comparison data are the pair-of-pants datum and the structure of neck length `T`.
  have hKb (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) (v : ℂ) : KR k v z = Kb v z := funext fun x ↦ by
    simp only [KR, Kb]
    rw [cappedComparisonPerturbation_eq_pairOfPantsPerturbation (hR2 k) (hRT k) (hDT (hΩD hz))]
  have hJb (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) :=
    cappedComparisonAlmostComplex_eq_cappedAlmostComplex h₀ J hJ (hR2 k) (hRT k) (hDT (hΩD hz))
  -- The energy over `Ω` is at most the area plus `2 (B₀ + B₁ + B_∞)`.
  have hE (k : ℕ) : ∫ z in Ω, σ.floerEnergyDensity (Kb 1) (Kb Complex.I) (u k) z ≤
      A + 2 * ∑ q, B q := by
    rw [setIntegral_congr_fun hΩ.measurableSet fun z hz ↦
      σ.floerEnergyDensity_congr_perturbation (u k) (hKb k hz 1).symm (hKb k hz Complex.I).symm]
    exact hω.setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB (by linarith [hR2 k])
      ((hu k).of_le (by norm_num))
      (fun z ↦ h₀.tames_almostComplexStructureAt_cappedComparisonAlmostComplex J hJ _ _ _)
      (hfl k) (hint k) (hcurv k) (harea k) Ω
  exact hconv hΩ hΩD (fun k ↦ (hu k).contMDiffOn)
    (fun k z hz ↦ by
      have h := hfl k z
      rwa [hJb k hz, σ.perturbedMFDeriv_congr_perturbation _ (hKb k hz 1)
        (hKb k hz Complex.I)] at h)
    (fun k ↦ (hint k).integrableOn.congr_fun (fun z hz ↦
      σ.floerEnergyDensity_congr_perturbation _ (hKb k hz 1) (hKb k hz Complex.I))
        hΩ.measurableSet)
    hE

/-- **The translated solutions of the capped comparison family in a closed manifold converge on the
caps of the PSS planes, uniformly along the long necks.** Let `σ` be a two-form on a closed manifold
`M` compatible with a smooth almost complex structure `J₀`, let the end structures `J q t` be tamed
by `σ`, of period one in `t` and jointly `C²` on `ℝ × M`, and let `H_q` be period-one `C³`
Hamiltonians with `|H_q| ≤ B_q`. Fix an end `q` and a compact window `D ⊆ ℝ × ℝ` of the plane. Let
`e : M → F` be injective and differentiable, with the capped structure with no neck uniformly tame
with respect to `e` over `D`, `c ‖d e v‖² ≤ σ(v, J v)` with `c > 0`, and the pushforwards through
`e` of the Hamiltonian vector fields of the two components of the capped datum
`TauCeti.Floer.cappedPerturbation 1 0 H` with no neck at most `L` there. There is a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` maps of the plane chart `ℝ × ℝ ≅ ℂ` of the
three-pole sphere into `M` solving the Floer equation `(du - X_{K_{Rₖ}})^{0,1} = 0` for the
structures `J_{Rₖ}(z, u)` of the comparison family, with `Rₖ ≥ 2`, integrable energy density and
curvature term, and symplectic area `∫ uₖ^* σ ≤ A`. Read them beyond the necks of length `Rₖ - 1`
through the translations `χₖ = TauCeti.ThricePuncturedSphere.Puncture.endShift q (Rₖ - 1)` along
the end `q`, and let `Ω ⊆ D` be open, made of points that are the center `c_q` of the end `q`, its
pole for an input end, or have signed longitudinal coordinate at least `2` on it. Then there are a
subsequence `φ` and a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)` such that, along `φ`,
every disc about a point of `Z` eventually carries Floer energy at least `δ` for the datum with no
neck, the energy densities of the translated maps `u_{φ n} ∘ χ_{φ n}` are uniformly bounded on
every compact subset of `Ω \ Z`, and the translated maps converge on `Ω \ Z` to a continuous map
`v`, locally uniformly after applying `e` and pointwise in `M`. The parameters `Rₖ` need not be
bounded. Points of the plane whose signed longitudinal coordinate is less than `2`, on its
cylindrical end below the cap, are not covered. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_endShift_subseq_off_finset_cappedComparison
    (h₀ : σ.Compatible J₀) (J : Puncture → ℝ → SmoothAlmostComplexStructure I M)
    (hJ : ∀ q t, σ.Tames (J q t)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (q : Puncture) {D : Set (ℝ × ℝ)}
    (hD : IsCompact D) (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      σ.eval₂ x v (h₀.cappedAlmostComplex J hJ 1 0 (equivRealProdCLM.symm z) x v))
    (hLs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ w ∈ Ω, equivRealProdCLM.symm w = q.endCenter ∨
        2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) →
      (∀ k, 2 ≤ R k) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.cappedComparisonAlmostComplex J hJ (R k)
          (equivRealProdCLM.symm z)).almostComplexStructureAt (u k z))
        (σ.perturbedMFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, Integrable (σ.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        (u k))) →
      (∀ k, Integrable fun z ↦ σ.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        z (u k z)) →
      (∀ k, ∫ z, (SmoothBundleForm.eval₂ σ (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, σ.floerEnergyDensity
          (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))) y) ∧
        (∀ L', IsCompact L' → L' ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ L', σ.floerEnergyDensity
          (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))))
            (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))) z)
            atTop (𝓝 (v z)) := by
  have hω := h₀.isNondegenerate
  have hHs1 (r : Puncture) : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H r)) :=
    (hHs r).of_le (by norm_num)
  -- The plane pieces carry the fixed data with no neck, which are smooth on the whole plane.
  have hX (v : ℂ) (α : M) := hω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2)
    (U := univ) (K := fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x v)
    (fun z _ x ↦ (contMDiff_cappedPerturbation_apply (n := 2 + 1) hH
      (fun r ↦ (hHs r).of_le (by norm_num)) 1 0 v).contMDiffAt) α
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    (Ks := fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
    (J := fun z ↦
      (h₀.cappedAlmostComplex J hJ 1 0 (equivRealProdCLM.symm z)).almostComplexStructureAt)
    he he_inj isOpen_univ hD (subset_univ D)
    (contDiffOn_almostComplexInChartAt_almostComplexStructureAt (n := 2)
      (J := fun z ↦ h₀.cappedAlmostComplex J hJ 1 0 (equivRealProdCLM.symm z))
      fun z _ x ↦ contMDiffAt_cappedAlmostComplex_equivRealProdCLM h₀ hJ hJp hJs 1 0 z x)
    (hX 1) (hX Complex.I)
    (fun z _ x ↦ hω.tames_iff.1 (h₀.tames_cappedAlmostComplex J hJ 1 0 _) x) hc
    (fun z hz x v ↦ by
      simpa only [IsNondegenerate.symplecticFormAt_apply,
        SmoothAlmostComplexStructure.almostComplexStructureAt_apply] using hJc z hz x v)
    hLs hLt
  refine ⟨δ, hδ, fun Ω R u A hΩ hΩD hΩq hR2 hu hfl hint hcurv harea ↦ ?_⟩
  have hud (k : ℕ) (z : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u k) z :=
    (hu k).mdifferentiableAt (by norm_num)
  have hχ (k : ℕ) : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k ∘ realChart (q.endShift (R k - 1))) :=
    (hu k).comp (q.contDiff_realChart_endShift (R k - 1)).contMDiff
  -- The energy of the translated map over `Ω` is the energy of the solution over `χₖ(Ω)`.
  have hE (k : ℕ) := setIntegral_floerEnergyDensity_comp_realChart_endShift_le h₀ J hJ hH hHs1 hB
    (hR2 k) hΩ.measurableSet hΩq ((hu k).of_le (by norm_num)) (hfl k) (hint k) (hcurv k) (harea k)
  -- The energy density of the translated map is continuous, so integrable on the compact `D`.
  have hint0 (k : ℕ) : IntegrableOn (σ.floerEnergyDensity
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
      (u k ∘ realChart (q.endShift (R k - 1)))) Ω :=
    (((σ.continuousOn_floerEnergyDensity_of_continuousOn_inChartAt isOpen_univ
      ((hχ k).of_le (by norm_num)).contMDiffOn (fun α ↦ (hX 1 α).continuousOn)
      (fun α ↦ (hX Complex.I α).continuousOn)).mono (subset_univ D)).integrableOn_compact
        hD).mono_set hΩD
  exact hconv hΩ hΩD (fun k ↦ (hχ k).contMDiffOn)
    (fun k w hw ↦ h₀.isComplexLinearMap_perturbedMFDeriv_comp_realChart_endShift (hJp q) hH hHs1
      (hR2 k) (hΩq w hw) (hud k _) (hfl k _))
    hint0 hE

/-- **Compactness at the long-neck end of the capped comparison family in a closed manifold.** Let
`σ` be a two-form on a closed manifold `M` compatible with a smooth almost complex structure `J₀`,
let the end structures `J q t` be tamed by `σ`, of period one in `t` and jointly `C²` on `ℝ × M`,
and let `H_q` be period-one `C³` Hamiltonians with `|H_q| ≤ B_q`. Fix a truncation `S_T` of the
pair of pants with a compact window `D ⊆ S_T`, and compact windows `D'_q ⊆ ℝ × ℝ` of the plane for
the three PSS planes. Let `e : M → F` be injective and differentiable, and over these windows let
the structures of neck length `T` (on `D`) and with no neck (on each `D'_q`) be uniformly tame with
respect to `e`, `c ‖d e v‖² ≤ σ(v, J v)` with `c > 0`, and let the pushforwards through `e` of the
Hamiltonian vector fields of the two components of the pair-of-pants perturbation (on `D`) and of
the capped datum with no neck (on each `D'_q`) be at most `L`. There is a threshold `δ > 0` with
the following property. Let `uₖ` be `C³` maps of the plane chart `ℝ × ℝ ≅ ℂ` of the three-pole
sphere into `M` solving the Floer equation of the comparison family at parameters `Rₖ ≥ 2` with
`T ≤ Rₖ + 1`, with integrable energy density and curvature term and symplectic area at most `A`.
Let `Ω ⊆ D` be open, and for each end `q` let `Ω'_q ⊆ D'_q` be open, made of points that are the
center `c_q` of the end `q`, its pole for an input end, or have signed longitudinal coordinate at
least `2` on it. Then along a single subsequence `φ` the maps `u_{φ n}` converge on the pair of
pants `Ω` off a finite set `Z`, and for each end `q` the maps `u_{φ n} ∘ χ_{q, φ n}`, translated by
`χ_{q, k} = TauCeti.ThricePuncturedSphere.Puncture.endShift q (Rₖ - 1)` along the end, converge on
the part `Ω'_q` of the cap of the PSS plane off a finite set `Z'_q`, where `#Z * δ` and every
`#Z'_q * δ` are at most `A + 2 (B₀ + B₁ + B_∞)`. The limits are continuous, and the convergence is
locally uniform after applying `e` and pointwise in `M`. For `Rₖ → ∞` the capped sphere breaks into
the pair of pants and the three PSS planes; on each plane this covers only the cap, not the
cylindrical end below it, where the signed longitudinal coordinate is less than `2`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_longNeck
    (h₀ : σ.Compatible J₀) (J : Puncture → ℝ → SmoothAlmostComplexStructure I M)
    (hJ : ∀ q t, σ.Tames (J q t)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (T : ℝ) {D : Set (ℝ × ℝ)}
    {D' : Puncture → Set (ℝ × ℝ)} (hD : IsCompact D)
    (hDT : D ⊆ equivRealProdCLM.symm ⁻¹' truncation T) (hD' : ∀ q, IsCompact (D' q))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      σ.eval₂ x v (h₀.cappedAlmostComplex J hJ 1 T (equivRealProdCLM.symm z) x v))
    (hLs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L)
    (hJc' : ∀ q, ∀ z ∈ D' q, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤
      σ.eval₂ x v (h₀.cappedAlmostComplex J hJ 1 0 (equivRealProdCLM.symm z) x v))
    (hLs' : ∀ q, ∀ z ∈ D' q, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt' : ∀ q, ∀ z ∈ D' q, ∀ x, ‖mvfderiv I e x (σ.hamiltonianVectorField
      (fun y ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃Ω' : Puncture → Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄
      ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D → (∀ q, IsOpen (Ω' q)) →
      (∀ q, Ω' q ⊆ D' q) →
      (∀ q, ∀ w ∈ Ω' q, equivRealProdCLM.symm w = q.endCenter ∨
        2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) →
      (∀ k, 2 ≤ R k) → (∀ k, T ≤ R k + 1) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.cappedComparisonAlmostComplex J hJ (R k)
          (equivRealProdCLM.symm z)).almostComplexStructureAt (u k z))
        (σ.perturbedMFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, Integrable (σ.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        (u k))) →
      (∀ k, Integrable fun z ↦ σ.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        z (u k z)) →
      (∀ k, ∫ z, (SmoothBundleForm.eval₂ σ (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) ≤ A) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (Z' : Puncture → Finset (ℝ × ℝ)) (v : ℝ × ℝ → M)
        (v' : Puncture → ℝ × ℝ → M), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧ ContinuousOn v (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
        (∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z))) ∧
        ∀ q, ↑(Z' q) ⊆ Ω' q ∧ (Z' q).card * δ ≤ A + 2 * ∑ q, B q ∧
          ContinuousOn (v' q) (Ω' q \ ↑(Z' q)) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))))
            (e ∘ v' q) atTop (Ω' q \ ↑(Z' q)) ∧
          ∀ z ∈ Ω' q \ ↑(Z' q),
            Tendsto (fun n ↦ (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))) z) atTop
              (𝓝 (v' q z)) := by
  obtain ⟨δc, hδc, hcore⟩ :=
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_truncation
      h₀ J hJ hJp hJs hH hHs hB T hD hDT he he_inj hc hJc hLs hLt
  choose δp hδp hplane using fun q ↦
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_endShift_subseq_off_finset_cappedComparison
      h₀ J hJ hJp hJs hH hHs hB q (hD' q) he he_inj hc (hJc' q) (hLs' q) (hLt' q)
  set δ := min δc (min (δp .zero) (min (δp .one) (δp .inf)))
  refine ⟨δ, lt_min hδc (lt_min (hδp _) (lt_min (hδp _) (hδp _))),
    fun Ω Ω' R u A hΩ hΩD hΩ' hΩ'D hΩ'q hR2 hRT hu hfl hint hcurv harea ↦ ?_⟩
  have hcard {δ' : ℝ} (hδ' : δ ≤ δ') {Z₀ : Finset (ℝ × ℝ)} (h : Z₀.card * δ' ≤ A + 2 * ∑ q, B q) :
      Z₀.card * δ ≤ A + 2 * ∑ q, B q :=
    (mul_le_mul_of_nonneg_left hδ' (Nat.cast_nonneg _)).trans h
  -- Locally uniform convergence passes to subsequences.
  have hsub {G : ℕ → ℝ × ℝ → F} {g : ℝ × ℝ → F} {s : Set (ℝ × ℝ)} {ψ : ℕ → ℕ}
      (hψ : Tendsto ψ atTop atTop) (h : TendstoLocallyUniformlyOn G g atTop s) :
      TendstoLocallyUniformlyOn (fun n ↦ G (ψ n)) g atTop s :=
    fun U hU x hx ↦ (h U hU x hx).imp fun _ ht ↦ ⟨ht.1, hψ.eventually ht.2⟩
  -- Compactness on the pair of pants, then on the caps of the three PSS planes along further
  -- subsequences.
  obtain ⟨φ₀, hφ₀, Z, hZ, hZE, -, -, v, hvc, hv, hvp⟩ :=
    hcore hΩ hΩD hR2 hRT hu hfl hint hcurv harea
  obtain ⟨φ₁, hφ₁, Z₀, hZ₀, hZ₀E, -, -, v₀, hv₀c, hv₀, hv₀p⟩ :=
    hplane .zero (hΩ' .zero) (hΩ'D .zero) (hΩ'q .zero) (fun k ↦ hR2 (φ₀ k))
      (fun k ↦ hu (φ₀ k)) (fun k ↦ hfl (φ₀ k)) (fun k ↦ hint (φ₀ k)) (fun k ↦ hcurv (φ₀ k))
      (fun k ↦ harea (φ₀ k))
  obtain ⟨φ₂, hφ₂, Z₁, hZ₁, hZ₁E, -, -, v₁, hv₁c, hv₁, hv₁p⟩ :=
    hplane .one (hΩ' .one) (hΩ'D .one) (hΩ'q .one) (fun k ↦ hR2 (φ₀ (φ₁ k)))
      (fun k ↦ hu (φ₀ (φ₁ k))) (fun k ↦ hfl (φ₀ (φ₁ k))) (fun k ↦ hint (φ₀ (φ₁ k)))
      (fun k ↦ hcurv (φ₀ (φ₁ k))) (fun k ↦ harea (φ₀ (φ₁ k)))
  obtain ⟨φ₃, hφ₃, Z₂, hZ₂, hZ₂E, -, -, v₂, hv₂c, hv₂, hv₂p⟩ :=
    hplane .inf (hΩ' .inf) (hΩ'D .inf) (hΩ'q .inf) (fun k ↦ hR2 (φ₀ (φ₁ (φ₂ k))))
      (fun k ↦ hu (φ₀ (φ₁ (φ₂ k)))) (fun k ↦ hfl (φ₀ (φ₁ (φ₂ k))))
      (fun k ↦ hint (φ₀ (φ₁ (φ₂ k)))) (fun k ↦ hcurv (φ₀ (φ₁ (φ₂ k))))
      (fun k ↦ harea (φ₀ (φ₁ (φ₂ k))))
  have h₁₂₃ := (hφ₁.comp (hφ₂.comp hφ₃)).tendsto_atTop
  refine ⟨φ₀ ∘ φ₁ ∘ φ₂ ∘ φ₃, Z, fun q ↦ match q with | .zero => Z₀ | .one => Z₁ | .inf => Z₂, v,
    fun q ↦ match q with | .zero => v₀ | .one => v₁ | .inf => v₂,
    hφ₀.comp (hφ₁.comp (hφ₂.comp hφ₃)), hZ, hcard (min_le_left _ _) hZE, hvc,
    hsub h₁₂₃ hv, fun z hz ↦ (hvp z hz).comp h₁₂₃, ?_⟩
  rintro (_ | _ | _)
  · have h₂₃ := (hφ₂.comp hφ₃).tendsto_atTop
    exact ⟨hZ₀, hcard ((min_le_right _ _).trans (min_le_left _ _)) hZ₀E, hv₀c,
      hsub h₂₃ hv₀, fun z hz ↦ (hv₀p z hz).comp h₂₃⟩
  · exact ⟨hZ₁, hcard ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      hZ₁E, hv₁c, hsub hφ₃.tendsto_atTop hv₁,
      fun z hz ↦ (hv₁p z hz).comp hφ₃.tendsto_atTop⟩
  · exact ⟨hZ₂, hcard ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
      hZ₂E, hv₂c, hv₂, hv₂p⟩

end Compatible

end Closed

end TauCeti.SmoothTwoForm
