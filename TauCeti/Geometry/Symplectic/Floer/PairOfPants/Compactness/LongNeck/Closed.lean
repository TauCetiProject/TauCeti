/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Manifold.Capped
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.LongNeck
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness at the long-neck end of the capped comparison family in a closed manifold

The comparison between the pair-of-pants product and the quantum product caps the three ends of
the pair of pants `S = ℂ ∖ {0, 1}` with Piunikhin–Salamon–Schwarz planes, giving a sphere with
three poles `0`, `1` and `∞`. Its one-parameter family of Floer data is
`K_R = TauCeti.Floer.cappedComparisonPerturbation H R`, with the almost complex structures
`J_R = TauCeti.SmoothTwoForm.Compatible.cappedComparisonAlmostComplex h₀ J hJ R` on the tangent
bundle of the target. For `R ≥ 2` there are necks of length `R - 1` along the three ends, and as
`R → ∞` the sphere breaks into the pair of pants and three PSS planes: the long-neck end of the
family. For a symplectic vector space target, interior compactness at this end is
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.LongNeck`. This file proves it for a
closed manifold `M` with a nondegenerate two-form `ω`, such as a closed symplectic manifold, with no
condition on where the solutions take their values.

The two pieces are treated as in the vector-space case, but with the compactness theorem in a
closed manifold,
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset`
in the namespace `TauCeti.SmoothTwoForm` (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`),
in place of the compactness theorem in a vector space.

* **The pair of pants.** On the truncation `S_T`, once `T ≤ R + 1`, the datum `K_R` is the
  pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation H` and `J_R` is the capped
  structure with neck length `T`
  (`TauCeti.Floer.cappedPerturbation_eq_smul_pairOfPantsPerturbation`,
  `TauCeti.Floer.cappedAlmostComplex_eq_pairOfPantsAlmostComplex`). These no longer depend on `R`.
* **The caps of the PSS planes.** Let
  `χ = TauCeti.ThricePuncturedSphere.Puncture.endShift q (R - 1)` be the translation by the neck
  length along the end `q`. At the center `c_q` of the end and at
  every point whose signed longitudinal coordinate is at least `2`, the pullback of the data along
  `χ` is the datum `TauCeti.Floer.cappedPerturbation 1 0 H` with no neck
  (`TauCeti.Floer.perturbationPullback_cappedComparisonPerturbation_endShift`), and the structure
  is the one with no neck (`TauCeti.SmoothTwoForm.Compatible.cappedAlmostComplex_endShift`). Since
  `χ` is holomorphic, `u ∘ χ` solves the Floer equation of these fixed data there
  (`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_realChart_endShift`), and its
  energy over a region `Ω` is the energy of `u` over `χ(Ω)`
  (`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_image_endShift`).

The energy identity of the family
(`IsNondegenerate.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le` in the
namespace `TauCeti.SmoothTwoForm`) bounds the Floer energy of a solution of symplectic area at most
`A` by `A + 2 (B₀ + B₁ + B_∞)` for `|H_q| ≤ B_q`, uniformly in `R`, so the energy of each piece is
bounded uniformly in `R`. The structures read in the charts of `M` are `C²` because the end
structures are (`TauCeti.SmoothTwoForm.Compatible.contMDiff_cappedAlmostComplex`,
`TauCeti.Floer.contDiffOn_almostComplexInChartAt_almostComplexStructureAt`). As in
`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding, with
the limit structures uniformly tame with respect to `e` and the pushforwards through `e` of the
Hamiltonian vector fields of the limit data bounded.

## Main results

In the namespace `TauCeti.SmoothTwoForm`:

* `isComplexLinearMap_perturbedMFDeriv_comp_realChart_endShift`,
  `integral_floerEnergyDensity_image_endShift`: the Floer equation and the energy on the cap of a
  PSS plane piece, read through the translation by the neck length.

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_truncation`:
  on an open subset of the truncation `S_T`, solutions for parameters `Rₖ ≥ max 2 (T - 1)`
  converge off finitely many bubbling points.
* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_endShift_subseq_off_finset_cappedComparison`:
  on an open subset of a compact window of the plane, made of the center of the end `q` and points
  beyond the neck, the translated solutions `uₖ ∘ χ_{q, Rₖ - 1}` converge off finitely many
  bubbling points.
* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_longNeck`:
  a single subsequence along which the solutions converge on the pair of pants and the translated
  solutions converge on the caps of all three PSS planes.

In each case the parameters `Rₖ` need not be bounded. The cylindrical ends of the PSS planes below
their caps, the bubbles at the bubbling points, the Floer cylinders that break off along the three
necks and the pole `∞` are not treated here.

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
open scoped Manifold
open TauCeti.Complex (realChart equivRealProdCLM_symm_realChart realChart_injective
  det_fderiv_realChart_nonneg)

namespace TauCeti.SmoothTwoForm

open Floer

variable {E G M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I (⊤ : ℕ∞) M]
  {H : Puncture → ℝ → M → ℝ}

/-- **The Floer equation on the caps of the PSS plane pieces.** For `R ≥ 2`, let `χ` be the
translation `TauCeti.ThricePuncturedSphere.Puncture.endShift q (R - 1)` by the neck length along the
end `q`. At a point `w` which is the center `c_q` of the end, its pole for an input end, or has
signed longitudinal coordinate at least `2` on it, if `u : ℝ × ℝ → M` solves the Floer equation of
the comparison family at `χ(w)`, then `u ∘ χ` solves the Floer equation of the data
`TauCeti.Floer.cappedPerturbation 1 0 H` and
`TauCeti.SmoothTwoForm.Compatible.cappedAlmostComplex h₀ J hJ 1 0` with no neck at `w`. -/
theorem isComplexLinearMap_perturbedMFDeriv_comp_realChart_endShift (ω : SmoothTwoForm I M)
    {J₀ : SmoothAlmostComplexStructure I M} (h₀ : ω.Compatible J₀)
    {J : Puncture → ℝ → SmoothAlmostComplexStructure I M} {hJ : ∀ q t, ω.Tames (J q t)}
    {q : Puncture} (hJp : Periodic (J q) 1) (hH : ∀ r, Periodic (H r) 1)
    (hHs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H r))) {R : ℝ} (hR : 2 ≤ R)
    {w : ℝ × ℝ} (hw : equivRealProdCLM.symm w = q.endCenter ∨
      2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) {u : ℝ × ℝ → M}
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (realChart (q.endShift (R - 1)) w))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      ((h₀.cappedComparisonAlmostComplex J hJ R
        (equivRealProdCLM.symm (realChart (q.endShift (R - 1)) w))).almostComplexStructureAt
          (u (realChart (q.endShift (R - 1)) w)))
      (ω.perturbedMFDeriv
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x Complex.I)
        u (realChart (q.endShift (R - 1)) w)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      ((h₀.cappedAlmostComplex J hJ 1 0 (equivRealProdCLM.symm w)).almostComplexStructureAt
        ((u ∘ realChart (q.endShift (R - 1))) w))
      (ω.perturbedMFDeriv (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.endShift (R - 1))) w).toLinearMap := by
  rw [equivRealProdCLM_symm_realChart, h₀.cappedComparisonAlmostComplex_of_two_le J hJ hR,
    h₀.cappedAlmostComplex_endShift J hJ hJp 1 (by linarith) hw] at h
  have hKd (v : ℂ) : MDifferentiableAt I 𝓘(ℝ) (fun y ↦ cappedComparisonPerturbation H R
      (equivRealProdCLM.symm (realChart (q.endShift (R - 1)) w)) y v)
      (u (realChart (q.endShift (R - 1)) w)) := by
    rw [cappedComparisonPerturbation_of_two_le H hR]
    exact mdifferentiable_cappedPerturbation_target hH hHs 1 (R - 1) _ v _
  have h' := ω.isComplexLinearMap_perturbedMFDeriv_perturbationPullback
    ((q.contDiff_realChart_endShift (R - 1) (n := 1)).differentiable one_ne_zero w) hu (hKd 1)
    (hKd Complex.I) (isComplexLinearMap_fderiv_realChart (q.hasDerivAt_endShift _ _)) h
  rwa [ω.perturbedMFDeriv_congr_perturbation (u ∘ realChart (q.endShift (R - 1)))
    (Ks' := fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
    (Kt' := fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
    (funext fun x ↦ by rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR hw,
      equivRealProdCLM_symm_stdComplexLineReal])
    (funext fun x ↦ by rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR hw,
      equivRealProdCLM_symm_stdComplexLineImag])] at h'

omit [FiniteDimensional ℝ E] in
/-- **The energy on the caps of the PSS plane pieces.** For `R ≥ 2`, let `χ` be the translation
`TauCeti.ThricePuncturedSphere.Puncture.endShift q (R - 1)` by the neck length along the end `q`. On
a measurable set `Ω` of points which are the center `c_q` of the end, its pole for an input end, or
have signed longitudinal coordinate at least `2` on it, the energy of a map `u : ℝ × ℝ → M` for the
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
  have hKd (z : ℝ × ℝ) (x : M) (v : ℂ) : MDifferentiableAt I 𝓘(ℝ)
      (fun y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y v) x := by
    rw [cappedComparisonPerturbation_of_two_le H hR]
    exact mdifferentiable_cappedPerturbation_target hH hHs 1 (R - 1) _ v x
  rw [ω.integral_floerEnergyDensity_image hΩm (realChart_injective (q.endShift_injective _)).injOn
    (fun w _ ↦ (q.contDiff_realChart_endShift (R - 1) (n := 1)).differentiable one_ne_zero w)
    (fun w _ ↦ det_fderiv_realChart_nonneg (q.hasDerivAt_endShift _ _)) hu
    (fun w _ ↦ hKd _ _ 1) (fun w _ ↦ hKd _ _ Complex.I)]
  refine setIntegral_congr_fun hΩm fun w hw ↦ ω.floerEnergyDensity_congr_perturbation _
    (funext fun x ↦ ?_) (funext fun x ↦ ?_)
  · rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR (hΩ w hw),
      equivRealProdCLM_symm_stdComplexLineReal]
  · rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR (hΩ w hw),
      equivRealProdCLM_symm_stdComplexLineImag]

end TauCeti.SmoothTwoForm

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I (⊤ : ℕ∞) M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {H : Puncture → ℝ → M → ℝ}
  {J₀ : SmoothAlmostComplexStructure I M} {J : Puncture → ℝ → SmoothAlmostComplexStructure I M}
  {e : M → F}

omit [I.Boundaryless] [CompactSpace M] in
/-- The capped structures with cutoff parameter `1` and a fixed neck length, read in the chart at
every point of `M`, are `C²` on the whole plane chart `ℝ × ℝ`, for period-one end structures which
are `C²` on `ℝ × M`. -/
private theorem contDiffOn_almostComplexInChartAt_cappedAlmostComplex (h₀ : ω.Compatible J₀)
    (hJ : ∀ q t, ω.Tames (J q t)) (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (L : ℝ) (α : M) :
    ContDiffOn ℝ 2 (almostComplexInChartAt I α fun z ↦
        (h₀.cappedAlmostComplex J hJ 1 L (equivRealProdCLM.symm z)).almostComplexStructureAt)
      (univ ×ˢ (extChartAt I α).target) :=
  contDiffOn_almostComplexInChartAt_almostComplexStructureAt
    (J := fun z ↦ h₀.cappedAlmostComplex J hJ 1 L (equivRealProdCLM.symm z))
    (fun z _ x ↦ (h₀.contMDiff_cappedAlmostComplex J hJ hJp hJs contMDiff_const contMDiff_const
      ((equivRealProdCLM.symm.contDiff.contMDiff).comp contMDiff_fst) contMDiff_snd) (z, x)) α

/-- **Solutions of the comparison family in a closed manifold converge on the pair of pants,
uniformly along the long necks.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, let
`H_q` be period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible, and let
`J_q(t)` be period-one `ω`-tame end structures which are `C²` on `ℝ × M`. Fix a truncation `S_T` of
the pair of pants and an injective differentiable `e : M → F`. On `S_T` let the capped structure
with neck length `T`, which is the pair-of-pants structure there, be uniformly tame with respect to
`e`, `c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`, and let the pushforwards through `e` of the Hamiltonian
vector fields of the two components of the pair-of-pants perturbation be at most `L`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` maps of the plane chart
`ℝ × ℝ ≅ ℂ` of the three-pole sphere into `M` solving the Floer equation
`(du - X_{K_{Rₖ}})^{0,1} = 0` for the structures `J_{Rₖ}(z, u)` of the comparison family, with
`Rₖ ≥ 2` and `T ≤ Rₖ + 1`, integrable energy density and curvature term, and symplectic area
`∫ u^* ω ≤ A`, and let `Ω ⊆ S_T` be open. Then there are a subsequence `φ` and a finite set
`Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)` such that, along `φ`, every disc about a point of `Z`
eventually carries Floer energy at least `δ` for the pair-of-pants perturbation, the energy
densities are uniformly bounded on every compact subset of `Ω \ Z`, and the solutions converge on
`Ω \ Z` to a continuous map `v`, locally uniformly after applying `e` and pointwise in `M`. The
parameters `Rₖ` need not be bounded. -/
theorem
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_truncation
    (hω : ω.IsNondegenerate) (h₀ : ω.Compatible J₀) (hJ : ∀ q t, ω.Tames (J q t))
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (T : ℝ)
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation T, ∀ x v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v
        ((h₀.cappedAlmostComplex J hJ 1 T (equivRealProdCLM.symm z)).almostComplexStructureAt x v))
    (hLs : ∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation T, ∀ x, ‖mvfderiv I e x
      (ω.hamiltonianVectorField (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y 1)
        x)‖ ≤ L)
    (hLt : ∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation T, ∀ x, ‖mvfderiv I e x
      (ω.hamiltonianVectorField
        (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y Complex.I)
        x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω →
      Ω ⊆ equivRealProdCLM.symm ⁻¹' truncation T → (∀ k, 2 ≤ R k) → (∀ k, T ≤ R k + 1) →
      (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.cappedComparisonAlmostComplex J hJ (R k)
          (equivRealProdCLM.symm z)).almostComplexStructureAt (u k z))
        (ω.perturbedMFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        (u k))) →
      (∀ k, Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        z (u k z)) →
      (∀ k, ∫ z, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I) (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ C, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  -- On `S_T` the family is the pair-of-pants datum with the fixed structure of neck length `T`.
  -- Each component `z ↦ K_z(w)` of the pair-of-pants perturbation is `C³` jointly in `z ∈ S` and
  -- the target point, so its Hamiltonian vector field is `C²` in every chart.
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    (Ks := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
    (J := fun z ↦
      (h₀.cappedAlmostComplex J hJ 1 T (equivRealProdCLM.symm z)).almostComplexStructureAt)
    he he_inj isOpen_thricePuncturedSphereReal (isCompact_preimage_truncation T)
    (preimage_truncation_subset_thricePuncturedSphereReal T)
    (fun α ↦ (contDiffOn_almostComplexInChartAt_cappedAlmostComplex h₀ hJ hJp hJs T α).mono
      (prod_mono (subset_univ _) subset_rfl))
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt fun z hz x ↦
      (contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x 1).of_le (by norm_num))
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt fun z hz x ↦
      (contMDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x Complex.I).of_le (by norm_num))
    (fun z _ x ↦ h₀.isNondegenerate.tames_iff.1 (h₀.tames_cappedAlmostComplex J hJ 1 T _) x)
    hc hJc hLs hLt
  refine ⟨δ, hδ, fun Ω R u A hΩ hΩT hR2 hRT hu hfl hint hcurv harea ↦ ?_⟩
  have hKb (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) (v : ℂ) :
      (fun x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x v) =
        fun x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x v := by
    rw [cappedComparisonPerturbation_eq_pairOfPantsPerturbation_of_mem_truncation H (hR2 k)
      (hRT k) (hΩT hz)]
  -- The Floer energy over `Ω` is at most `A + 2 (B₀ + B₁ + B_∞)`.
  have hE (k : ℕ) : ∫ z in Ω, ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I) (u k) z ≤
        A + 2 * ∑ q, B q := by
    rw [setIntegral_congr_fun hΩ.measurableSet fun z hz ↦
      ω.floerEnergyDensity_congr_perturbation (u k)
        (Ks' := fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (Kt' := fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x
          Complex.I) (hKb k hz 1).symm (hKb k hz Complex.I).symm]
    exact hω.setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB (by linarith [hR2 k]) ((hu k).of_le (by norm_num))
      (fun z ↦ h₀.tames_almostComplexStructureAt_cappedComparisonAlmostComplex J hJ _ _ _)
      (hfl k) (hint k) (hcurv k) (harea k) Ω
  exact hconv hΩ hΩT (fun k ↦ (hu k).contMDiffOn)
    (fun k z hz ↦ by
      have h := hfl k z
      rwa [h₀.cappedComparisonAlmostComplex_eq_cappedAlmostComplex_of_mem_truncation J hJ (hR2 k)
          (hRT k) (hΩT hz),
        ω.perturbedMFDeriv_congr_perturbation _
          (Ks' := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (Kt' := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
          (hKb k hz 1) (hKb k hz Complex.I)] at h)
    (fun k ↦ (hint k).integrableOn.congr_fun (fun z hz ↦
      ω.floerEnergyDensity_congr_perturbation _
        (Ks' := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
        (Kt' := fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x Complex.I)
        (hKb k hz 1) (hKb k hz Complex.I)) hΩ.measurableSet)
    hE

/-- **The translated solutions in a closed manifold converge on the caps of the PSS planes,
uniformly along the long necks.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, let
`H_q` be period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible, and let
`J_q(t)` be period-one `ω`-tame end structures which are `C²` on `ℝ × M`. Fix an end `q`, a compact
window `D ⊆ ℝ × ℝ` of the plane and an injective differentiable `e : M → F`. On `D` let the capped
structure with no neck be uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J v)` with
`c > 0`, and let the pushforwards through `e` of the Hamiltonian vector fields of the two components
of the datum `TauCeti.Floer.cappedPerturbation 1 0 H` with no neck be at most `L`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` maps of the plane chart
`ℝ × ℝ ≅ ℂ` of the three-pole sphere into `M` solving the Floer equation
`(du - X_{K_{Rₖ}})^{0,1} = 0` for the structures `J_{Rₖ}(z, u)` of the comparison family, with
`Rₖ ≥ 2`, integrable energy density and curvature term, and symplectic area `∫ u^* ω ≤ A`. Read them
beyond the necks of length `Rₖ - 1` through the translations
`χₖ = TauCeti.ThricePuncturedSphere.Puncture.endShift q (Rₖ - 1)` along the end `q`. Let `Ω ⊆ D` be
open, made of points that are the center `c_q` of the end `q`, its pole for an input end, or have
signed longitudinal coordinate at least `2` on it. Then there are a subsequence `φ` and a finite set
`Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)` such that, along `φ`, every disc about a point of `Z`
eventually carries Floer energy of `u_{φ n} ∘ χ_{φ n}` at least `δ` for the datum with no neck,
these energy densities are uniformly bounded on every compact subset of `Ω \ Z`, and the maps
`u_{φ n} ∘ χ_{φ n}` converge on `Ω \ Z` to a continuous map `v`, locally uniformly after applying
`e` and pointwise in `M`. The parameters `Rₖ` need not be bounded. Points of the plane whose signed
longitudinal coordinate is less than `2`, on its cylindrical end below the cap, are not covered. -/
theorem
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_endShift_subseq_off_finset_cappedComparison
    (hω : ω.IsNondegenerate) (h₀ : ω.Compatible J₀) (hJ : ∀ q t, ω.Tames (J q t))
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (q : Puncture) {D : Set (ℝ × ℝ)}
    (hD : IsCompact D) (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    {c L : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v
      ((h₀.cappedAlmostComplex J hJ 1 0 (equivRealProdCLM.symm z)).almostComplexStructureAt x v))
    (hLs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ w ∈ Ω, equivRealProdCLM.symm w = q.endCenter ∨
        2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) →
      (∀ k, 2 ≤ R k) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.cappedComparisonAlmostComplex J hJ (R k)
          (equivRealProdCLM.symm z)).almostComplexStructureAt (u k z))
        (ω.perturbedMFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        (u k))) →
      (∀ k, Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        z (u k z)) →
      (∀ k, ∫ z, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) ≤ A) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧
        Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ A', ∀ n, ∀ y ∈ C, ω.floerEnergyDensity
          (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))) y ≤ A') ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn
            (fun n ↦ e ∘ (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1)))) (e ∘ v) atTop
            (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z,
            Tendsto (fun n ↦ (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))) z) atTop
              (𝓝 (v z)) := by
  -- The plane pieces carry the fixed data with no neck, which are smooth on the whole plane.
  have hK (w : ℂ) (z : ℝ × ℝ) (_ : z ∈ (univ : Set (ℝ × ℝ))) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1)
        (uncurry fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x w) (z, x) :=
    (contMDiff_cappedPerturbation_apply hH hHs 1 0 w).contMDiffAt
  have hHs1 (r : Puncture) : ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H r)) :=
    (hHs r).of_le (by norm_num)
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    (Ks := fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
    (Kt := fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
    (J := fun z ↦
      (h₀.cappedAlmostComplex J hJ 1 0 (equivRealProdCLM.symm z)).almostComplexStructureAt)
    he he_inj isOpen_univ hD (subset_univ D)
    (contDiffOn_almostComplexInChartAt_cappedAlmostComplex h₀ hJ hJp hJs 0)
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK 1))
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK Complex.I))
    (fun z _ x ↦ h₀.isNondegenerate.tames_iff.1 (h₀.tames_cappedAlmostComplex J hJ 1 0 _) x)
    hc hJc hLs hLt
  refine ⟨δ, hδ, fun Ω R u A hΩ hΩD hΩq hR2 hu hfl hint hcurv harea ↦ ?_⟩
  have hud (k : ℕ) (z : ℝ × ℝ) : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u k) z :=
    ((hu k).mdifferentiable (by norm_num)) z
  have hχ (k : ℕ) : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k ∘ realChart (q.endShift (R k - 1))) :=
    (hu k).comp (q.contDiff_realChart_endShift (R k - 1)).contMDiff
  -- The energy of the translated map over `Ω` is the energy of the solution over `χₖ(Ω)`.
  have hE (k : ℕ) : ∫ w in Ω, ω.floerEnergyDensity
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
      (u k ∘ realChart (q.endShift (R k - 1))) w ≤ A + 2 * ∑ q, B q := by
    rw [← ω.integral_floerEnergyDensity_image_endShift hH hHs1 (hR2 k) hΩ.measurableSet hΩq
      fun w _ ↦ hud k _]
    exact hω.setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le hH hHs1 hB
      (by linarith [hR2 k]) ((hu k).of_le (by norm_num))
      (fun z ↦ h₀.tames_almostComplexStructureAt_cappedComparisonAlmostComplex J hJ _ _ _)
      (hfl k) (hint k) (hcurv k) (harea k) _
  -- The energy density of the translated map is continuous, so integrable on the compact `D`.
  have hint0 (k : ℕ) : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x Complex.I)
      (u k ∘ realChart (q.endShift (R k - 1)))) Ω :=
    (((ω.continuousOn_floerEnergyDensity_of_continuousOn_inChartAt isOpen_univ
      ((hχ k).of_le (by norm_num)).contMDiffOn
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK 1) α).continuousOn)
      (fun α ↦ (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK Complex.I) α).continuousOn)).mono
        (subset_univ D)).integrableOn_compact hD).mono_set hΩD
  exact hconv hΩ hΩD (fun k ↦ (hχ k).contMDiffOn)
    (fun k w hw ↦ ω.isComplexLinearMap_perturbedMFDeriv_comp_realChart_endShift h₀ (hJp q) hH hHs1
      (hR2 k) (hΩq w hw) (hud k _) (hfl k _))
    hint0 hE

/-- **Compactness at the long-neck end of the capped comparison family in a closed manifold.** Let
`ω` be a nondegenerate two-form on a closed manifold `M`, let `H_q` be period-one `C³` Hamiltonians
with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible, and let `J_q(t)` be period-one `ω`-tame end
structures which are `C²` on `ℝ × M`. Fix a truncation `S_T` of the pair of pants, compact windows
`D_q ⊆ ℝ × ℝ` of the plane for the three PSS planes, and an injective differentiable `e : M → F`.
Let the limit structures be uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J v)` with
`c > 0`: the capped structure with neck length `T`, which is the pair-of-pants structure, on `S_T`,
and the capped structure with no neck on each `D_q`. Let the pushforwards through `e` of the
Hamiltonian vector fields of the two components of the limit data be at most `L`: the pair-of-pants
perturbation on `S_T`, and the datum `TauCeti.Floer.cappedPerturbation 1 0 H` with no neck on each
`D_q`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` maps of the plane
chart `ℝ × ℝ ≅ ℂ` of the three-pole sphere into `M` solving the Floer equation of the comparison
family at parameters `Rₖ ≥ 2` with `T ≤ Rₖ + 1`, with integrable energy density and curvature term,
and symplectic area `∫ u^* ω ≤ A`. Let `Ω ⊆ S_T` be open, and for each end `q` let `Ω'_q ⊆ D_q` be
open, made of points that are the center `c_q` of the end `q`, its pole for an input end, or have
signed longitudinal coordinate at least `2` on it. Then along a single subsequence `φ` the maps
`u_{φ n}` converge on the pair of pants `Ω` off a finite set `Z`, and for each end `q` the
translated maps `u_{φ n} ∘ χ_{q, φ n}`, for the translations
`χ_{q,k} = TauCeti.ThricePuncturedSphere.Puncture.endShift q (Rₖ - 1)` along the end, converge
on the part `Ω'_q` of the cap of the PSS plane off a finite set `Z'_q`, where `#Z * δ` and every
`#Z'_q * δ` are at most `A + 2 (B₀ + B₁ + B_∞)`. The limits are continuous, and the
convergence is locally uniform after applying `e` and pointwise in `M`. For `Rₖ → ∞` the capped
sphere breaks into the pair of pants and the three PSS planes; on each plane this covers only the
cap, not the cylindrical end below it. -/
theorem
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_longNeck
    (hω : ω.IsNondegenerate) (h₀ : ω.Compatible J₀) (hJ : ∀ q t, ω.Tames (J q t))
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContMDiff (𝓘(ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x)
        p.2 ((J q p.1).toEndomorphism p.2)))
    (hH : ∀ q, Periodic (H q) 1)
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (T : ℝ) {D : Puncture → Set (ℝ × ℝ)}
    (hD : ∀ q, IsCompact (D q)) (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x)
    (he_inj : Injective e) {c L : ℝ} (hc : 0 < c)
    (hJcT : ∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation T, ∀ x v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v
        ((h₀.cappedAlmostComplex J hJ 1 T (equivRealProdCLM.symm z)).almostComplexStructureAt x v))
    (hLsT : ∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation T, ∀ x, ‖mvfderiv I e x
      (ω.hamiltonianVectorField (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y 1)
        x)‖ ≤ L)
    (hLtT : ∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation T, ∀ x, ‖mvfderiv I e x
      (ω.hamiltonianVectorField
        (fun y ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L)
    (hJc : ∀ q, ∀ z ∈ D q, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v
      ((h₀.cappedAlmostComplex J hJ 1 0 (equivRealProdCLM.symm z)).almostComplexStructureAt x v))
    (hLs : ∀ q, ∀ z ∈ D q, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) y 1) x)‖ ≤ L)
    (hLt : ∀ q, ∀ z ∈ D q, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ L) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃Ω' : Puncture → Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄
      ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ equivRealProdCLM.symm ⁻¹' truncation T →
      (∀ q, IsOpen (Ω' q)) → (∀ q, Ω' q ⊆ D q) →
      (∀ q, ∀ w ∈ Ω' q, equivRealProdCLM.symm w = q.endCenter ∨
        2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) →
      (∀ k, 2 ≤ R k) → (∀ k, T ≤ R k + 1) → (∀ k, ContMDiff 𝓘(ℝ, ℝ × ℝ) I 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        ((h₀.cappedComparisonAlmostComplex J hJ (R k)
          (equivRealProdCLM.symm z)).almostComplexStructureAt (u k z))
        (ω.perturbedMFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        (u k))) →
      (∀ k, Integrable fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x Complex.I)
        z (u k z)) →
      (∀ k, ∫ z, (SmoothBundleForm.eval₂ ω (u k z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u k) z stdComplexLineImag) : ℝ) ≤ A) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (Z' : Puncture → Finset (ℝ × ℝ)) (v : ℝ × ℝ → M)
        (v' : Puncture → ℝ × ℝ → M), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧ ContinuousOn v (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
        (∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z))) ∧
        ∀ q, ↑(Z' q) ⊆ Ω' q ∧ (Z' q).card * δ ≤ A + 2 * ∑ q, B q ∧
          ContinuousOn (v' q) (Ω' q \ ↑(Z' q)) ∧
          TendstoLocallyUniformlyOn
            (fun n ↦ e ∘ (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1)))) (e ∘ v' q) atTop
            (Ω' q \ ↑(Z' q)) ∧
          ∀ z ∈ Ω' q \ ↑(Z' q),
            Tendsto (fun n ↦ (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))) z) atTop
              (𝓝 (v' q z)) := by
  obtain ⟨δc, hδc, hcore⟩ :=
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_cappedComparison_truncation
      hω h₀ hJ hJp hJs hH hHs hB T he he_inj hc hJcT hLsT hLtT
  choose δp hδp hplane using fun q ↦
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_endShift_subseq_off_finset_cappedComparison
      hω h₀ hJ hJp hJs hH hHs hB q (hD q) he he_inj hc (hJc q) (hLs q) (hLt q)
  set δ := min δc (min (δp .zero) (min (δp .one) (δp .inf)))
  refine ⟨δ, lt_min hδc (lt_min (hδp _) (lt_min (hδp _) (hδp _))),
    fun Ω Ω' R u A hΩ hΩT hΩ' hΩ'D hΩ'q hR2 hRT hu hfl hint hcurv harea ↦ ?_⟩
  have hcard {δ' : ℝ} (hδ' : δ ≤ δ') {Z₀ : Finset (ℝ × ℝ)} (h : Z₀.card * δ' ≤ A + 2 * ∑ q, B q) :
      Z₀.card * δ ≤ A + 2 * ∑ q, B q :=
    (mul_le_mul_of_nonneg_left hδ' (Nat.cast_nonneg _)).trans h
  -- Compactness on the pair of pants, then on the caps of the three PSS planes along further
  -- subsequences.
  obtain ⟨φ₀, hφ₀, Z, hZ, hZE, -, -, v, hvc, hv, hvp⟩ :=
    hcore hΩ hΩT hR2 hRT hu hfl hint hcurv harea
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
  have h₂₃ := (hφ₂.comp hφ₃).tendsto_atTop
  refine ⟨φ₀ ∘ φ₁ ∘ φ₂ ∘ φ₃, Z, fun q ↦ match q with | .zero => Z₀ | .one => Z₁ | .inf => Z₂, v,
    fun q ↦ match q with | .zero => v₀ | .one => v₁ | .inf => v₂,
    hφ₀.comp (hφ₁.comp (hφ₂.comp hφ₃)), hZ, hcard (min_le_left _ _) hZE, hvc,
    (hv.comp_tendsto h₁₂₃ :), fun z hz ↦ (hvp z hz).comp h₁₂₃, ?_⟩
  rintro (_ | _ | _)
  · exact ⟨hZ₀, hcard ((min_le_right _ _).trans (min_le_left _ _)) hZ₀E, hv₀c,
      (hv₀.comp_tendsto h₂₃ :), fun z hz ↦ (hv₀p z hz).comp h₂₃⟩
  · exact ⟨hZ₁, hcard ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      hZ₁E, hv₁c, (hv₁.comp_tendsto hφ₃.tendsto_atTop :),
      fun z hz ↦ (hv₁p z hz).comp hφ₃.tendsto_atTop⟩
  · exact ⟨hZ₂, hcard ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
      hZ₂E, hv₂c, hv₂, hv₂p⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
