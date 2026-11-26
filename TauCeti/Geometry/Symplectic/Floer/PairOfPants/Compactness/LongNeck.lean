/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.AlmostComplex.Capped
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capped
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Capped
public import TauCeti.Geometry.Symplectic.Floer.Pullback
import TauCeti.Geometry.Symplectic.JHolomorphic.RealChart
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness at the long-neck end of the capped comparison family

The comparison between the pair-of-pants product and the quantum product caps the three ends of
the pair of pants `S = ℂ ∖ {0, 1}` with Piunikhin–Salamon–Schwarz planes, giving a sphere with
three poles `0`, `1` and `∞`. Its one-parameter family of Floer data is
`K_R = TauCeti.Floer.cappedComparisonPerturbation H R` with the almost complex structures
`J_R = TauCeti.Floer.cappedComparisonAlmostComplex h₀ J hJ R`. For `R ≥ 2` there are necks of
length `L = R - 1` along the three ends, on which the data are `H_q(t) dt` and `J_q(t)`. As
`R → ∞` the sphere breaks into the pair of pants, which keeps the inputs and the output, and three
PSS planes, one at each pole: the long-neck end of the family, whose broken configurations give
the composite of the pair-of-pants product with the PSS maps on its two inputs and its output.
This file proves the interior part of Gromov–Floer compactness at this end, for a symplectic
vector space target `(V, ω)`, uniformly in `R`, on the pair of pants and on the cap of each PSS
plane, where the signed longitudinal coordinate in the translated coordinate is at least `2`.
Compactness over
compact windows of parameters is in
`TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Capped`.

* **The pair of pants.** On the truncation `S_T` of the pair of pants, every signed longitudinal
  coordinate is at most `T`, so once `T ≤ L + 2 = R + 1` the data of the family are the
  pair-of-pants perturbation `TauCeti.Floer.pairOfPantsPerturbation H` and the pair-of-pants
  structure there (`TauCeti.Floer.cappedPerturbation_eq_smul_pairOfPantsPerturbation`,
  `TauCeti.Floer.cappedAlmostComplex_eq_pairOfPantsAlmostComplex`). They no longer depend on `R`.
* **The caps of the PSS planes.** Beyond the neck at `q` the data are the data with no neck,
  translated by
  `±L` along the end. In the coordinate `w` of the plane they are pulled back along the
  translation `χ = TauCeti.ThricePuncturedSphere.Puncture.endShift q L`, an affine map with
  positive real derivative, to the data `K_0 = TauCeti.Floer.cappedPerturbation 1 0 H` and
  `TauCeti.Floer.cappedAlmostComplex h₀ J hJ 1 0` with no neck, at the center `c_q` of the end,
  which is its pole for the input ends `0` and `1`, and at every point whose signed longitudinal
  coordinate on the end is at least `2`
  (`TauCeti.Floer.cappedPerturbation_endShift`, `TauCeti.Floer.cappedAlmostComplex_endShift`,
  `TauCeti.Floer.perturbationPullback_cappedComparisonPerturbation_endShift`). Since `χ` is
  holomorphic, `u ∘ χ` solves the Floer equation of these fixed data there
  (`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_realChart_endShift`), and its
  energy over a region `Ω` is the energy of `u` over `χ(Ω)`
  (`TauCeti.SymplecticForm.integral_floerEnergyDensity_image_endShift`). Below the cap, on the
  cylindrical end of the plane where the signed longitudinal coordinate `σ` is less than `2`, the
  pulled-back data are not those with no neck: for `σ ≥ 2 - L` their profile is
  `smoothTransition (3 - σ)`, the profile of the limit plane, so they still depend on `L`.

The energy identity of the family
(`TauCeti.SymplecticForm.abs_integral_floerEnergyDensity_cappedComparisonPerturbation_sub_le`)
bounds the energy of a solution of area at most `A` by `A + 2 (B₀ + B₁ + B_∞)` for `|H_q| ≤ B_q`,
for every `R ≥ 0`, so the energy of each piece is bounded uniformly in `R`. Compactness for fixed
data (`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`)
then applies on each piece.

For an arbitrary sequence of neck lengths `Lₖ`, solutions of the capped datum
`K_L = TauCeti.Floer.cappedPerturbation 1 L H`, for almost complex structures `Jₖ` that agree with
a fixed `C²` structure on the window, converge on each of the four pieces with a threshold `δ`
independent of the neck lengths:

* **The pair of pants.** On the truncation `S_R` the datum is the pair-of-pants datum as soon as
  `R ≤ L + 2`, so solutions with Floer energy at most `E` converge there off finitely many
  bubbling points
  (`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedPerturbation`).
* **The PSS planes, including their cylindrical ends.** Read the end `q` in its positive end chart
  `φ'_q` (`TauCeti.Floer.positiveEndChart`), translated by `L + 4`: `z ↦ φ'_q(z + (L + 4, 0))`.
  Wherever `s + L ≥ -2`, the datum in these coordinates is `β(-s - 1) H'_q(t) dt`, where `H'_q` is
  the end Hamiltonian of the positive end chart
  (`TauCeti.Floer.perturbationPullback_positiveEndChart_add_cappedPerturbation`). This is the
  perturbation of the negative PSS plane with Hamiltonian `H'_q` in the end coordinates of the
  plane (`TauCeti.Floer.PSSPlane.endComponent`), and it does not depend on `L`. On the output end,
  where the pair of pants is capped by a positive plane, the positive end chart reverses both
  coordinates, and the cap reads as the negative plane of `H'_∞(t) = -H_∞(-t)`. The translated
  maps solve the Floer equation of the plane wherever `s + L ≥ -2`
  (`isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_add_of_cappedPerturbation`), their
  energy over a subset of a band `ℝ × [t₀, t₀ + 1)` is the energy of the solution over its image
  (`lintegral_floerEnergyDensity_comp_positiveEndChart_add_eq_image_cappedPerturbation`), and on
  every compact window in such a band with `s + Lₖ ≥ -2` they converge off finitely many bubbling
  points (`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedPerturbation_plane`).
  The threshold does not depend on the band, so two overlapping bands cover a full annulus. For
  `r ≥ 1` the capped structures `TauCeti.Floer.cappedAlmostComplex` agree there with the
  `L`-independent negative plane structure of the end family
  (`TauCeti.Floer.cappedAlmostComplex_cylindricalEndLift_endSign_mul_add`).

## Main results

In the namespace `TauCeti.SymplecticForm`:

* `isComplexLinearMap_perturbedFDeriv_comp_realChart_endShift`,
  `integral_floerEnergyDensity_image_endShift`: the Floer equation and the energy on the cap of
  a PSS plane piece, read through the translation by the neck length.
* `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison_truncation`:
  on an open subset of the truncation `S_T`, solutions for parameters `Rₖ ≥ max 2 (T - 1)`
  converge off finitely many bubbling points.
* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_endShift_subseq_off_finset_cappedComparison`:
  on an open subset of a compact window of the plane, made of the center of the end `q` and points
  beyond the neck, the translated solutions `uₖ ∘ χ_{q, Rₖ - 1}` converge off finitely many
  bubbling points.
* `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison_longNeck`:
  a single subsequence along which the solutions converge on the pair of pants and the translated
  solutions converge on the caps of all three PSS planes.
* `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedPerturbation`,
  `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedPerturbation_plane`:
  for the capped datum with arbitrary neck lengths, convergence on the pair of pants and on the
  PSS plane pieces in the translated positive end charts, as described above.

In the coordinate `w` of the plane, the cylindrical ends of the PSS planes below their caps need
the limit data with profile `smoothTransition (3 - σ)` in place of the data with no neck; there
the PSS plane pieces are treated in the translated positive end charts instead, where the limit
datum is that of the negative PSS plane. The poles of the planes, the bubbles at the bubbling
points, the Floer cylinders that break off along the three necks, and the behaviour at the pole
`∞` itself, which is not a point of the plane chart, are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on
  the comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points), Section 10.9 (gluing and the limits of glued domains) and
  Section 12.1 (the PSS isomorphism).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open scoped NNReal ENNReal
open TauCeti.Complex (realChart equivRealProdCLM_symm_realChart realChart_injective
  det_fderiv_realChart_nonneg)

namespace TauCeti.Floer

/-- **The caps of the PSS plane pieces of the comparison family in fixed coordinates.** For
`R ≥ 2`, at the center `c_q` of the end `q`, which is its pole for an input end, and at every point
whose signed longitudinal coordinate on the end is at least `2`, the pullback of the comparison
datum `K_R` along the translation `TauCeti.ThricePuncturedSphere.Puncture.endShift q (R - 1)` by
the neck length is the datum `TauCeti.Floer.cappedPerturbation 1 0 H` with no neck. -/
theorem perturbationPullback_cappedComparisonPerturbation_endShift {M : Type*}
    {H : Puncture → ℝ → M → ℝ} {q : Puncture} (hH : Periodic (H q) 1) {R : ℝ} (hR : 2 ≤ R)
    {w : ℝ × ℝ} (hw : equivRealProdCLM.symm w = q.endCenter ∨
      2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) (v : ℝ × ℝ) (x : M) :
    perturbationPullback (realChart (q.endShift (R - 1)))
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x I) v w x =
      cappedPerturbation 1 0 H (equivRealProdCLM.symm w) x (equivRealProdCLM.symm v) := by
  rw [perturbationPullback_realChart _ (q.hasDerivAt_endShift _ _),
    cappedComparisonPerturbation_of_two_le H hR]
  exact cappedPerturbation_endShift hH (by linarith) hw x _

end TauCeti.Floer

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {J₀ : AlmostComplexStructure V}
  {J : Puncture → ℝ → V → AlmostComplexStructure V}

/-- **The Floer equation on the caps of the PSS plane pieces.** For `R ≥ 2`, let `χ` be the
translation `TauCeti.ThricePuncturedSphere.Puncture.endShift q (R - 1)` by the neck length along the
end `q`. At a point `w` which is the center `c_q` of the end, its pole for an input end, or has
signed longitudinal coordinate at least `2` on it, if `u` solves the Floer equation of the
comparison family at `χ(w)`, then `u ∘ χ` solves the Floer equation of the data
`TauCeti.Floer.cappedPerturbation 1 0 H` and `TauCeti.Floer.cappedAlmostComplex h₀ J hJ 1 0` with no
neck at `w`. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_realChart_endShift (ω : SymplecticForm V)
    (h₀ : ω.Compatible J₀) {hJ : ∀ q t x, ω.Tames (J q t x)} {q : Puncture}
    (hJp : Periodic (J q) 1) (hH : ∀ r, Periodic (H r) 1)
    (hHs : ∀ r, ContDiff ℝ 1 (uncurry (H r))) {R : ℝ} (hR : 2 ≤ R) {w : ℝ × ℝ}
    (hw : equivRealProdCLM.symm w = q.endCenter ∨
      2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) {u : ℝ × ℝ → V}
    (hu : DifferentiableAt ℝ u (realChart (q.endShift (R - 1)) w))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (cappedComparisonAlmostComplex h₀ J hJ R
        (equivRealProdCLM.symm (realChart (q.endShift (R - 1)) w))
        (u (realChart (q.endShift (R - 1)) w)))
      (ω.perturbedFDeriv
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x I)
        u (realChart (q.endShift (R - 1)) w) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (cappedAlmostComplex h₀ J hJ 1 0 (equivRealProdCLM.symm w)
        ((u ∘ realChart (q.endShift (R - 1))) w))
      (ω.perturbedFDeriv (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x I)
        (u ∘ realChart (q.endShift (R - 1))) w : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [equivRealProdCLM_symm_realChart, cappedComparisonAlmostComplex_of_two_le h₀ hR,
    cappedAlmostComplex_endShift h₀ hJp 1 (by linarith) hw] at h
  have hKd (v : ℂ) : DifferentiableAt ℝ (fun y ↦ cappedComparisonPerturbation H R
      (equivRealProdCLM.symm (realChart (q.endShift (R - 1)) w)) y v)
      (u (realChart (q.endShift (R - 1)) w)) := by
    rw [cappedComparisonPerturbation_of_two_le H hR]
    exact differentiableAt_cappedPerturbation_apply hH hHs 1 (R - 1) _ _ v
  have h' := ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback
    ((q.contDiff_realChart_endShift (R - 1) (n := 1)).differentiable one_ne_zero w) hu (hKd 1)
    (hKd I) (isComplexLinearMap_fderiv_realChart (q.hasDerivAt_endShift _ _)) h
  rwa [ω.perturbedFDeriv_congr
    (Ks' := fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
    (Kt' := fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x I) _
    (funext fun x ↦ by rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR hw,
      equivRealProdCLM_symm_stdComplexLineReal])
    (funext fun x ↦ by rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR hw,
      equivRealProdCLM_symm_stdComplexLineImag])] at h'

/-- **The energy on the caps of the PSS plane pieces.** For `R ≥ 2`, let `χ` be the translation
`TauCeti.ThricePuncturedSphere.Puncture.endShift q (R - 1)` by the neck length along the end `q`. On
a measurable set `Ω` of points which are the center `c_q` of the end, its pole for an input end, or
have signed longitudinal coordinate at least `2` on it, the energy of `u` for the comparison datum
`K_R` over `χ(Ω)` is the energy of `u ∘ χ` for the datum `TauCeti.Floer.cappedPerturbation 1 0 H`
with no neck over `Ω`. -/
theorem integral_floerEnergyDensity_image_endShift (ω : SymplecticForm V)
    (hH : ∀ r, Periodic (H r) 1) (hHs : ∀ r, ContDiff ℝ 1 (uncurry (H r))) {q : Puncture}
    {R : ℝ} (hR : 2 ≤ R) {Ω : Set (ℝ × ℝ)} (hΩm : MeasurableSet Ω)
    (hΩ : ∀ w ∈ Ω, equivRealProdCLM.symm w = q.endCenter ∨
      2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) {u : ℝ × ℝ → V}
    (hu : ∀ w ∈ Ω, DifferentiableAt ℝ u (realChart (q.endShift (R - 1)) w)) :
    ∫ z in realChart (q.endShift (R - 1)) '' Ω, ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) x I) u z =
      ∫ w in Ω, ω.floerEnergyDensity
        (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x I)
        (u ∘ realChart (q.endShift (R - 1))) w := by
  have hKd (z : ℝ × ℝ) (x : V) (v : ℂ) :
      DifferentiableAt ℝ (fun y ↦ cappedComparisonPerturbation H R (equivRealProdCLM.symm z) y v)
        x := by
    rw [cappedComparisonPerturbation_of_two_le H hR]
    exact differentiableAt_cappedPerturbation_apply hH hHs 1 (R - 1) z x v
  rw [ω.integral_floerEnergyDensity_image hΩm (realChart_injective (q.endShift_injective _)).injOn
    (fun w _ ↦ (q.contDiff_realChart_endShift (R - 1) (n := 1)).differentiable one_ne_zero w)
    (fun w _ ↦ det_fderiv_realChart_nonneg (q.hasDerivAt_endShift _ _)) hu
    (fun w _ ↦ hKd _ _ 1) (fun w _ ↦ hKd _ _ I)]
  refine setIntegral_congr_fun hΩm fun w hw ↦ ω.floerEnergyDensity_congr_perturbation _
    (funext fun x ↦ ?_) (funext fun x ↦ ?_)
  · rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR (hΩ w hw),
      equivRealProdCLM_symm_stdComplexLineReal]
  · rw [perturbationPullback_cappedComparisonPerturbation_endShift (hH q) hR (hΩ w hw),
      equivRealProdCLM_symm_stdComplexLineImag]

/-- **Solutions of the capped comparison family converge on the pair of pants, uniformly along the
long necks.** Let `H_q` be period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be
`ω`-compatible, and let `J_q(t, x)` be period-one `C²` families of `ω`-tame structures on the three
ends. Fix a truncation `S_T` of the pair of pants and a compact `K ⊆ V`. There is a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` maps of the plane chart `ℝ × ℝ ≅ ℂ` of the
three-pole sphere solving the Floer equation `(du - X_{K_{Rₖ}})^{0,1} = 0` for the structures
`J_{Rₖ}(z, u)` of the comparison family, with `Rₖ ≥ 2` and `T ≤ Rₖ + 1`, integrable energy density,
symplectic area at most `A`, and `uₖ(Ω) ⊆ K` for an open `Ω ⊆ S_T`. Then there are a subsequence
`φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`, and a continuous `v : Ω \ Z → K`
such that along `φ` every disc about a point of `Z` eventually carries Floer energy at least `δ` for
the pair-of-pants perturbation, the differentials are uniformly bounded on every compact subset of
`Ω \ Z`, and `u_{φ n} → v` locally uniformly on `Ω \ Z`. The parameters `Rₖ` need not be bounded. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison_truncation
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (T : ℝ) {K : Set V} (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃A : ℝ⦄, IsOpen Ω →
      Ω ⊆ equivRealProdCLM.symm ⁻¹' truncation T → (∀ k, 2 ≤ R k) → (∀ k, T ≤ R k + 1) →
      (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (cappedComparisonAlmostComplex h₀ J hJ (R k) (equivRealProdCLM.symm z) (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I) (u k))) →
      (∀ k, ∫ z, ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag) ≤
        A) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (equivRealProdCLM.symm z) x I) (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  -- On `S_T` the family is the pair-of-pants datum with the fixed structure of neck length `T`.
  have hKp := contDiffOn_uncurry_pairOfPantsPerturbation hH hHs
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (J := fun z x ↦ cappedAlmostComplex h₀ J hJ 1 T (equivRealProdCLM.symm z) x)
    (isOpen_thricePuncturedSphereReal.prod isOpen_univ) (hKp 1) (hKp I)
    (contDiff_cappedAlmostComplex_equivRealProdCLM h₀ hJp hJs 1 T).contDiffOn
    (isCompact_preimage_truncation T) hK
    (prod_mono (preimage_truncation_subset_thricePuncturedSphereReal T) (subset_univ K))
    fun z _ x _ ↦ tames_cappedAlmostComplex h₀ 1 T _ x
  refine ⟨δ, hδ, fun Ω R u A hΩ hΩT hR2 hRT hu hfl huK hint harea ↦ ?_⟩
  set KR : ℕ → ℂ → ℝ × ℝ → V → ℝ := fun k v z x ↦
    cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x v
  set Kb : ℂ → ℝ × ℝ → V → ℝ := fun v z x ↦
    pairOfPantsPerturbation H (equivRealProdCLM.symm z) x v
  -- Every signed longitudinal coordinate of a point of `Ω` is at most `T ≤ (Rₖ - 1) + 2`.
  have hσ {z : ℝ × ℝ} (hz : z ∈ Ω) {L : ℝ} (hL : T ≤ L + 2) (q : Puncture) :
      q.endSign * (q.endCoord (equivRealProdCLM.symm z)).re ≤ L + 2 :=
    ((mem_truncation.1 (hΩT hz)).2.2 q).trans hL
  have hKb (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) (v : ℂ) : KR k v z = Kb v z := by
    simp only [KR, Kb]
    rw [cappedComparisonPerturbation_eq_pairOfPantsPerturbation_of_mem_truncation H (hR2 k)
      (hRT k) (hΩT hz)]
  have hJb (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) (x : V) :
      cappedComparisonAlmostComplex h₀ J hJ (R k) (equivRealProdCLM.symm z) x =
        cappedAlmostComplex h₀ J hJ 1 T (equivRealProdCLM.symm z) x := by
    rw [cappedComparisonAlmostComplex_of_two_le h₀ (hR2 k),
      cappedAlmostComplex_eq_pairOfPantsAlmostComplex h₀ le_rfl (hσ hz (by linarith [hRT k])),
      cappedAlmostComplex_eq_pairOfPantsAlmostComplex h₀ le_rfl (hσ hz (by linarith))]
  -- The energy over `Ω` is at most the energy over the plane.
  have hE (k : ℕ) : ∫ z in Ω, ω.floerEnergyDensity (Kb 1) (Kb I) (u k) z ≤ A + 2 * ∑ q, B q := by
    rw [setIntegral_congr_fun hΩ.measurableSet fun z hz ↦
      ω.floerEnergyDensity_congr_perturbation (u k) (hKb k hz 1).symm (hKb k hz I).symm]
    exact setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le ω h₀ hJ hH
      (fun q ↦ (hHs q).of_le (by norm_num)) hB (by linarith [hR2 k])
      ((hu k).of_le (by norm_num)) (hfl k) (hint k) (harea k) Ω
  exact hconv hΩ hΩT (fun k ↦ (hu k).contDiffOn)
    (fun k z hz ↦ by
      have h := hfl k z
      rwa [hJb k hz, ω.perturbedFDeriv_congr _ (hKb k hz 1) (hKb k hz I)] at h)
    huK
    (fun k ↦ (hint k).integrableOn.congr_fun (fun z hz ↦
      ω.floerEnergyDensity_congr_perturbation _ (hKb k hz 1) (hKb k hz I)) hΩ.measurableSet)
    hE

/-- **The translated solutions converge on the caps of the PSS planes, uniformly along the long
necks.** Let
`H_q` be period-one `C³` Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible, and let
`J_q(t, x)` be period-one `C²` families of `ω`-tame structures on the three ends. Fix an end `q` and
compact sets `D ⊆ ℝ × ℝ` and `K ⊆ V`. There is a threshold `δ > 0` with the following property. Let
`uₖ` be `C³` maps of the plane chart `ℝ × ℝ ≅ ℂ` of the three-pole sphere solving the Floer equation
`(du - X_{K_{Rₖ}})^{0,1} = 0` for the structures `J_{Rₖ}(z, u)` of the comparison family, with
`Rₖ ≥ 2`, integrable energy density and symplectic area at most `A`. Read them beyond the necks of
length `Rₖ - 1` through the translations
`χₖ = TauCeti.ThricePuncturedSphere.Puncture.endShift q (Rₖ - 1)` along the end `q`. Let `Ω ⊆ D` be
open, made of points that are the center `c_q` of the end `q`, its pole for an input end, or have
signed longitudinal coordinate at least `2` on it, with `uₖ(χₖ(Ω)) ⊆ K`. Then there are a
subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ A + 2 (B₀ + B₁ + B_∞)`, and a continuous
`v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries Floer energy
at least `δ` for the datum `TauCeti.Floer.cappedPerturbation 1 0 H` with no neck, the differentials
of `u_{φ n} ∘ χ_{φ n}` are uniformly bounded on every compact subset of `Ω \ Z`, and
`u_{φ n} ∘ χ_{φ n} → v` locally uniformly on `Ω \ Z`. The parameters `Rₖ` need not be bounded.
Points of the plane whose signed longitudinal coordinate is less than `2`, on its cylindrical end
below the cap, are not covered. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_endShift_subseq_off_finset_cappedComparison
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (q : Puncture) {D : Set (ℝ × ℝ)}
    {K : Set V} (hD : IsCompact D) (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ w ∈ Ω, equivRealProdCLM.symm w = q.endCenter ∨
        2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) →
      (∀ k, 2 ≤ R k) → (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (cappedComparisonAlmostComplex h₀ J hJ (R k) (equivRealProdCLM.symm z) (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k ∘ realChart (q.endShift (R k - 1))) Ω K) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I) (u k))) →
      (∀ k, ∫ z, ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag) ≤
        A) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x I)
          (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))) y‖ ≤
            M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n) ∘ realChart (q.endShift (R (φ n) - 1))) v
          atTop (Ω \ ↑Z) := by
  -- The plane pieces carry the fixed data with no neck, which are smooth on the whole plane.
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (J := fun z x ↦ cappedAlmostComplex h₀ J hJ 1 0 (equivRealProdCLM.symm z) x) isOpen_univ
    (contDiff_cappedPerturbation_apply hH hHs 1 0 1).contDiffOn
    (contDiff_cappedPerturbation_apply hH hHs 1 0 I).contDiffOn
    (contDiff_cappedAlmostComplex_equivRealProdCLM h₀ hJp hJs 1 0).contDiffOn hD hK
    (subset_univ _) fun z _ x _ ↦ tames_cappedAlmostComplex h₀ 1 0 _ x
  refine ⟨δ, hδ, fun Ω R u A hΩ hΩD hΩq hR2 hu hfl huK hint harea ↦ ?_⟩
  have hHs1 (r : Puncture) : ContDiff ℝ 1 (uncurry (H r)) := (hHs r).of_le (by norm_num)
  have hud (k : ℕ) (z : ℝ × ℝ) : DifferentiableAt ℝ (u k) z :=
    ((hu k).differentiable (by norm_num)) z
  have hχ (k : ℕ) : ContDiff ℝ 3 (u k ∘ realChart (q.endShift (R k - 1))) :=
    (hu k).comp (q.contDiff_realChart_endShift (R k - 1))
  -- The energy of the translated map over `Ω` is the energy of the solution over `χₖ(Ω)`.
  have hE (k : ℕ) : ∫ w in Ω, ω.floerEnergyDensity
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x I)
      (u k ∘ realChart (q.endShift (R k - 1))) w ≤ A + 2 * ∑ q, B q := by
    rw [← ω.integral_floerEnergyDensity_image_endShift hH hHs1 (hR2 k) hΩ.measurableSet hΩq
      fun w _ ↦ hud k _]
    exact setIntegral_floerEnergyDensity_cappedComparisonPerturbation_le ω h₀ hJ hH hHs1 hB
      (by linarith [hR2 k]) ((hu k).of_le (by norm_num)) (hfl k) (hint k) (harea k) _
  -- The energy density of the translated map is continuous, so integrable on the compact `D`.
  have hint0 (k : ℕ) : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 0 H (equivRealProdCLM.symm z) x I)
      (u k ∘ realChart (q.endShift (R k - 1)))) Ω :=
    (((ω.continuousOn_floerEnergyDensity isOpen_univ ((hχ k).of_le (by norm_num)).contDiffOn
      (contDiff_cappedPerturbation_apply hH hHs1 1 0 1).contDiffOn
      (contDiff_cappedPerturbation_apply hH hHs1 1 0 I).contDiffOn).mono
        (subset_univ D)).integrableOn_compact hD).mono_set hΩD
  exact hconv hΩ hΩD (fun k ↦ (hχ k).contDiffOn)
    (fun k w hw ↦ ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_endShift h₀ (hJp q) hH hHs1
      (hR2 k) (hΩq w hw) (hud k _) (hfl k _))
    huK hint0 hE

/-- **Compactness at the long-neck end of the capped comparison family.** Let `H_q` be period-one
`C³` Hamiltonians with `|H_q| ≤ B_q`, let `J₀` be `ω`-compatible, and let `J_q(t, x)` be period-one
`C²` families of `ω`-tame structures on the three ends. Fix a truncation `S_T` of the pair of pants,
compact windows `D_q ⊆ ℝ × ℝ` of the plane for the three PSS planes, and a compact `K ⊆ V`. There is
a threshold `δ > 0` with the following property. Let `uₖ` be `C³` maps of the plane chart
`ℝ × ℝ ≅ ℂ` of the three-pole sphere solving the Floer equation of the comparison family at
parameters `Rₖ ≥ 2` with `T ≤ Rₖ + 1`, with integrable energy density and symplectic area at most
`A`. Let `Ω ⊆ S_T` be open with `uₖ(Ω) ⊆ K`, and for each end `q` let `Ω'_q ⊆ D_q` be open, made of
points that are the center `c_q` of the end `q`, its pole for an input end, or have signed
longitudinal coordinate at least `2` on it, with `uₖ(χ_{q,k}(Ω'_q)) ⊆ K` for the translations
`χ_{q,k} = TauCeti.ThricePuncturedSphere.Puncture.endShift q (Rₖ - 1)` along the end. Then along a
single subsequence `φ` the maps `u_{φ n}` converge locally uniformly on the pair of pants `Ω` off a
finite set `Z`, and for each end `q` the translated maps `u_{φ n} ∘ χ_{q, φ n}` converge locally
uniformly on the part `Ω'_q` of the cap of the PSS plane off a finite set `Z'_q`, where `#Z * δ`
and every `#Z'_q * δ` are at most `A + 2 (B₀ + B₁ + B_∞)`. For `Rₖ → ∞` the capped sphere breaks
into the pair of pants and the three PSS planes; on each plane this covers only the cap, not the
cylindrical end below it, where the signed longitudinal coordinate is less than `2`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison_longNeck
    (ω : SymplecticForm V) (h₀ : ω.Compatible J₀) (hJ : ∀ q t x, ω.Tames (J q t x))
    (hJp : ∀ q, Periodic (J q) 1)
    (hJs : ∀ q, ContDiff ℝ 2 fun p : ℝ × V ↦ (J q p.1 p.2).toLinearMap.toContinuousLinearMap)
    (hH : ∀ q, Periodic (H q) 1) (hHs : ∀ q, ContDiff ℝ 3 (uncurry (H q)))
    {B : Puncture → ℝ} (hB : ∀ q t x, |H q t x| ≤ B q) (T : ℝ) {D : Puncture → Set (ℝ × ℝ)}
    {K : Set V} (hD : ∀ q, IsCompact (D q)) (hK : IsCompact K) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃Ω' : Puncture → Set (ℝ × ℝ)⦄ ⦃R : ℕ → ℝ⦄
      ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃A : ℝ⦄, IsOpen Ω → Ω ⊆ equivRealProdCLM.symm ⁻¹' truncation T →
      (∀ q, IsOpen (Ω' q)) → (∀ q, Ω' q ⊆ D q) →
      (∀ q, ∀ w ∈ Ω' q, equivRealProdCLM.symm w = q.endCenter ∨
        2 ≤ q.endSign * (q.endCoord (equivRealProdCLM.symm w)).re) →
      (∀ k, 2 ≤ R k) → (∀ k, T ≤ R k + 1) → (∀ k, ContDiff ℝ 3 (u k)) →
      (∀ k z, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (cappedComparisonAlmostComplex h₀ J hJ (R k) (equivRealProdCLM.symm z) (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ q k, MapsTo (u k ∘ realChart (q.endShift (R k - 1))) (Ω' q) K) →
      (∀ k, Integrable (ω.floerEnergyDensity
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ cappedComparisonPerturbation H (R k) (equivRealProdCLM.symm z) x I) (u k))) →
      (∀ k, ∫ z, ω (fderiv ℝ (u k) z stdComplexLineReal) (fderiv ℝ (u k) z stdComplexLineImag) ≤
        A) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (Z' : Puncture → Finset (ℝ × ℝ)) (v : ℝ × ℝ → V)
        (v' : Puncture → ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ A + 2 * ∑ q, B q ∧ ContinuousOn v (Ω \ ↑Z) ∧
        MapsTo v (Ω \ ↑Z) K ∧ TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) ∧
        ∀ q, ↑(Z' q) ⊆ Ω' q ∧ (Z' q).card * δ ≤ A + 2 * ∑ q, B q ∧
          ContinuousOn (v' q) (Ω' q \ ↑(Z' q)) ∧ MapsTo (v' q) (Ω' q \ ↑(Z' q)) K ∧
          TendstoLocallyUniformlyOn (fun n ↦ u (φ n) ∘ realChart (q.endShift (R (φ n) - 1)))
            (v' q) atTop (Ω' q \ ↑(Z' q)) := by
  obtain ⟨δc, hδc, hcore⟩ :=
    exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedComparison_truncation ω h₀
      hJ hJp hJs hH hHs hB T hK
  choose δp hδp hplane using fun q ↦
    exists_pos_forall_tendstoLocallyUniformlyOn_comp_endShift_subseq_off_finset_cappedComparison
      ω h₀ hJ hJp hJs hH hHs hB q (hD q) hK
  refine ⟨min δc (min (δp .zero) (min (δp .one) (δp .inf))),
    lt_min hδc (lt_min (hδp _) (lt_min (hδp _) (hδp _))),
    fun Ω Ω' R u A hΩ hΩT hΩ' hΩ'D hΩ'q hR2 hRT hu hfl huK huK' hint harea ↦ ?_⟩
  have hcard {δ' : ℝ} (hδ' : min δc (min (δp .zero) (min (δp .one) (δp .inf))) ≤ δ')
      {Z₀ : Finset (ℝ × ℝ)} (h : Z₀.card * δ' ≤ A + 2 * ∑ q, B q) :
      Z₀.card * min δc (min (δp .zero) (min (δp .one) (δp .inf))) ≤ A + 2 * ∑ q, B q :=
    (mul_le_mul_of_nonneg_left hδ' (Nat.cast_nonneg _)).trans h
  -- Compactness on the pair of pants, then on the caps of the three PSS planes along further
  -- subsequences.
  obtain ⟨φ₀, Z, v, hφ₀, hZ, hZE, -, -, hvc, hvK, hv⟩ :=
    hcore hΩ hΩT hR2 hRT hu hfl huK hint harea
  obtain ⟨φ₁, Z₀, v₀, hφ₁, hZ₀, hZ₀E, -, -, hv₀c, hv₀K, hv₀⟩ :=
    hplane .zero (hΩ' .zero) (hΩ'D .zero) (hΩ'q .zero) (fun k ↦ hR2 (φ₀ k))
      (fun k ↦ hu (φ₀ k)) (fun k ↦ hfl (φ₀ k)) (fun k ↦ huK' .zero (φ₀ k))
      (fun k ↦ hint (φ₀ k)) (fun k ↦ harea (φ₀ k))
  obtain ⟨φ₂, Z₁, v₁, hφ₂, hZ₁, hZ₁E, -, -, hv₁c, hv₁K, hv₁⟩ :=
    hplane .one (hΩ' .one) (hΩ'D .one) (hΩ'q .one) (fun k ↦ hR2 (φ₀ (φ₁ k)))
      (fun k ↦ hu (φ₀ (φ₁ k))) (fun k ↦ hfl (φ₀ (φ₁ k))) (fun k ↦ huK' .one (φ₀ (φ₁ k)))
      (fun k ↦ hint (φ₀ (φ₁ k))) (fun k ↦ harea (φ₀ (φ₁ k)))
  obtain ⟨φ₃, Z₂, v₂, hφ₃, hZ₂, hZ₂E, -, -, hv₂c, hv₂K, hv₂⟩ :=
    hplane .inf (hΩ' .inf) (hΩ'D .inf) (hΩ'q .inf) (fun k ↦ hR2 (φ₀ (φ₁ (φ₂ k))))
      (fun k ↦ hu (φ₀ (φ₁ (φ₂ k)))) (fun k ↦ hfl (φ₀ (φ₁ (φ₂ k))))
      (fun k ↦ huK' .inf (φ₀ (φ₁ (φ₂ k)))) (fun k ↦ hint (φ₀ (φ₁ (φ₂ k))))
      (fun k ↦ harea (φ₀ (φ₁ (φ₂ k))))
  refine ⟨φ₀ ∘ φ₁ ∘ φ₂ ∘ φ₃, Z, fun q ↦ match q with | .zero => Z₀ | .one => Z₁ | .inf => Z₂, v,
    fun q ↦ match q with | .zero => v₀ | .one => v₁ | .inf => v₂,
    hφ₀.comp (hφ₁.comp (hφ₂.comp hφ₃)), hZ, hcard (min_le_left _ _) hZE, hvc, hvK,
    (hv.comp_tendsto (hφ₁.comp (hφ₂.comp hφ₃)).tendsto_atTop :), ?_⟩
  rintro (_ | _ | _)
  · exact ⟨hZ₀, hcard ((min_le_right _ _).trans (min_le_left _ _)) hZ₀E, hv₀c, hv₀K,
      (hv₀.comp_tendsto (hφ₂.comp hφ₃).tendsto_atTop :)⟩
  · exact ⟨hZ₁, hcard ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
      hZ₁E, hv₁c, hv₁K, (hv₁.comp_tendsto hφ₃.tendsto_atTop :)⟩
  · exact ⟨hZ₂, hcard ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
      hZ₂E, hv₂c, hv₂K, hv₂⟩

end TauCeti.SymplecticForm

/-! ### The capped datum with arbitrary neck lengths -/

namespace TauCeti.SymplecticForm

open Floer

section PairOfPants

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **Capped pairs of pants converge on the pair-of-pants piece as the necks stretch.** Let `H_q` be
period-one `C³` Hamiltonians, fix a truncation `S_R` and a compact `K ⊆ V`, and let `J` be a `C²`
family of structures on a neighbourhood `W` of `S_R × K`, read in real coordinates, which is
`ω`-tame on `S_R × K`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³`
solutions on `S` of the Floer equation `(du - X_K)^{0,1} = 0` of the capped perturbation
`K = cappedPerturbation 1 Lₖ H`, with neck lengths `Lₖ ≥ R - 2`, for structures `Jₖ(z, u)`, and
with Floer energy at most `E`. Let `Ω` be an open subset of `S_R` on which `Jₖ = J` and
`uₖ(Ω) ⊆ K`. Then there are a subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a
continuous `v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries
energy at least `δ` for the pair-of-pants datum, the differentials are bounded on every compact
subset of `Ω \ Z`, and `uₖ → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedPerturbation
    (ω : SymplecticForm V) (hH : ∀ r, Periodic (H r) 1) (hHs : ∀ r, ContDiff ℝ 3 (uncurry (H r)))
    (R : ℝ) {W : Set ((ℝ × ℝ) × V)} {K : Set V} (hW : IsOpen W) (hK : IsCompact K)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hTKW : (Complex.equivRealProdCLM.symm ⁻¹' truncation R) ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄
      ⦃Jk : ℕ → ℝ × ℝ → V → AlmostComplexStructure V⦄ ⦃E : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R → (∀ k, R ≤ L k + 2) →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk k z (u k z)) (ω.perturbedFDeriv
          (fun z x ↦ cappedPerturbation 1 (L k) H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation 1 (L k) H (Complex.equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, ∀ z ∈ Ω, Jk k z = J z) →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ cappedPerturbation 1 (L k) H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation 1 (L k) H (Complex.equivRealProdCLM.symm z) x I)
          (u k) z) ≤ E) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x I)
          (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  have hTS : T ⊆ thricePuncturedSphereReal := preimage_truncation_subset_thricePuncturedSphereReal R
  have hP := contDiffOn_uncurry_pairOfPantsPerturbation hH hHs
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (hW.inter (isOpen_thricePuncturedSphereReal.prod isOpen_univ))
    ((hP 1).mono inter_subset_right) ((hP I).mono inter_subset_right) (hJ.mono inter_subset_left)
    (isCompact_preimage_truncation R) hK
    (subset_inter hTKW (prod_mono hTS (subset_univ K))) hJt
  refine ⟨δ, hδ, fun Ω L u Jk E hΩ hΩT hLR hu hfl hJΩ hE huK ↦ ?_⟩
  set Kc : ℕ → ℂ → ℝ × ℝ → V → ℝ := fun k v z x ↦
    cappedPerturbation 1 (L k) H (Complex.equivRealProdCLM.symm z) x v
  set Kp : ℂ → ℝ × ℝ → V → ℝ := fun v z x ↦
    pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩT.trans hTS
  -- On the truncation `S_R ⊆ S_{L + 2}` the capped datum is the pair-of-pants datum.
  have hKp (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ T) (v : ℂ) : Kc k v z = Kp v z := by
    funext x
    have h := (mem_truncation.1 hz).2.2
    simp only [Kc, Kp, cappedPerturbation_eq_smul_pairOfPantsPerturbation
      (fun r ↦ (h r).trans (hLR k)) x, one_smul]
  -- So on `Ω` the `uₖ` solve the pair-of-pants equation.
  have hflp (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) : IsComplexLinearMap
      (AlmostComplexStructure.product ℝ) (J z (u k z))
      (ω.perturbedFDeriv (Kp 1) (Kp I) (u k) z : ℝ × ℝ →ₗ[ℝ] V) := by
    have h := hfl k z (hΩS hz)
    rwa [hJΩ k z hz, ω.perturbedFDeriv_congr _ (hKp k (hΩT hz) 1) (hKp k (hΩT hz) I)] at h
  -- The energy over `Ω` for the pair-of-pants datum is at most the total energy.
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity (Kp 1) (Kp I) (u k) z) ≤
      E := by
    refine le_trans (le_of_eq (setLIntegral_congr_fun hΩ.measurableSet fun z hz ↦ ?_))
      ((setLIntegral_le_lintegral _ _).trans (hE k))
    rw [ω.floerEnergyDensity_congr_perturbation _ (hKp k (hΩT hz) 1) (hKp k (hΩT hz) I)]
  have hIE (k : ℕ) := MeasureTheory.integrable_and_integral_le_of_lintegral_ofReal_le
    (((ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal
      ((hu k).of_le (by norm_num)) ((hP 1).of_le (by norm_num)) ((hP I).of_le (by norm_num))).mono
        hΩS).aestronglyMeasurable hΩ.measurableSet)
    (ae_restrict_of_forall_mem hΩ.measurableSet fun z hz ↦
      ω.floerEnergyDensity_nonneg (hJt z (hΩT hz) _ (huK k hz)) (hflp k hz)) (hlin k)
  exact hconv hΩ hΩT (fun k ↦ (hu k).mono hΩS) (fun k z hz ↦ hflp k hz) huK
    (fun k ↦ (hIE k).1) fun k ↦ (hIE k).2

end PairOfPants

/-! ### The PSS plane pieces -/

section Plane

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ} {q : Puncture} {L : ℝ}

omit [FiniteDimensional ℝ V] in
/-- On the part `s > 0` of the positive end chart of `q`, the components of the capped perturbation
are differentiable in the target point when the Hamiltonian `H_q` of that end is: only that end
contributes there. -/
private theorem differentiableAt_cappedPerturbation_positiveEndChart
    (hHd : ∀ t, Differentiable ℝ (H q t)) (a L : ℝ) {ζ : ℝ × ℝ} (hζ : 0 < ζ.1) (v : ℂ) (y : V) :
    DifferentiableAt ℝ
      (fun x ↦ cappedPerturbation a L H (Complex.equivRealProdCLM.symm (positiveEndChart q ζ)) x v)
      y := by
  have hw : 0 < q.endSign *
      (q.endCoord (Complex.equivRealProdCLM.symm (positiveEndChart q ζ))).re := by
    rw [positiveEndChart_apply, re_endCoord_endChart]
    simpa [← mul_assoc] using hζ
  set w := Complex.equivRealProdCLM.symm (positiveEndChart q ζ)
  have h : (fun x ↦ cappedPerturbation a L H w x v) = fun x ↦
      a * cappedEndProfile L (q.endSign * (q.endCoord w).re) * H q (q.endCoord w).im x *
        q.endAngularForm w v := by
    funext x
    rw [cappedPerturbation_def, Finset.sum_eq_single q (fun r _ hr ↦ ?_) (by simp)]
    · simp only [smul_apply, smul_eq_mul]
    · rw [cappedEndProfile_of_le_one
        ((endSign_mul_re_endCoord_nonpos (Ne.symm hr) hw).trans zero_le_one)]
      simp
  rw [h]
  exact (((hHd _) y).const_mul _).mul_const _

/-- **Capped solutions on the PSS plane pieces.** Let `u` solve, at the image of `z = (s, t)` with
`s + L ≥ -2` under the positive end chart of `q` translated by `L + 4`, the Floer equation of the
capped perturbation with neck length `L`. Then the translated map `u ∘ φ'_q(· + (L + 4, 0))` solves
at `z` the Floer equation of the negative PSS plane with Hamiltonian
`H'_q = positiveEndHamiltonian H q`, read in the end coordinates of the plane. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_add_of_cappedPerturbation
    (ω : SymplecticForm V) (hH : Periodic (H q) 1) (hHd : ∀ t, Differentiable ℝ (H q t))
    {J : AlmostComplexStructure V} {u : ℝ × ℝ → V} {z : ℝ × ℝ} (hz : -2 ≤ z.1 + L)
    (hu : DifferentiableAt ℝ u (positiveEndChart q (z + (L + 4, 0))))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x I) u
      (positiveEndChart q (z + (L + 4, 0))) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (PSSPlane.negative.endComponent (positiveEndHamiltonian H q) 1)
      (PSSPlane.negative.endComponent (positiveEndHamiltonian H q) I)
      (fun z ↦ u (positiveEndChart q (z + (L + 4, 0)))) z : ℝ × ℝ →ₗ[ℝ] V) := by
  have hψ := hasFDerivAt_positiveEndChart_add q (L + 4, 0) z
  have h0 : 0 < (z + (L + 4, 0)).1 := by
    rw [Prod.fst_add]
    linarith
  have hK := differentiableAt_cappedPerturbation_positiveEndChart hHd 1 L h0
  have hholo : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (fun z ↦ positiveEndChart q (z + (L + 4, 0))) z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
    rw [hψ.fderiv]
    exact isComplexLinearMap_fderiv_positiveEndChart q _
  have h' := ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback hψ.differentiableAt hu
    (hK 1 _) (hK I _) hholo h
  rwa [ω.perturbedFDeriv_congr _
    (funext fun x ↦ by rw [perturbationPullback_positiveEndChart_add_cappedPerturbation hH hz,
      equivRealProdCLM_symm_stdComplexLineReal, one_mul])
    (funext fun x ↦ by rw [perturbationPullback_positiveEndChart_add_cappedPerturbation hH hz,
      equivRealProdCLM_symm_stdComplexLineImag, one_mul])] at h'

/-- **The energy of a PSS plane piece.** Let `Ω` be a measurable subset of a band `ℝ × [t₀, t₀ + 1)`
of angular width one, with `s + L ≥ -2` at its points `(s, t)`, and `u` a map differentiable on
the image of `Ω` under the positive end chart of `q` translated by `L + 4`. The energy of the
translated map over `Ω`, for the perturbation of the negative PSS plane with Hamiltonian `H'_q` in
its end coordinates, is the energy of `u` over the image of `Ω`, for the capped perturbation with
neck length `L`. -/
theorem lintegral_floerEnergyDensity_comp_positiveEndChart_add_eq_image_cappedPerturbation
    (ω : SymplecticForm V) (hH : Periodic (H q) 1) (hHd : ∀ t, Differentiable ℝ (H q t))
    {u : ℝ × ℝ → V} {Ω : Set (ℝ × ℝ)} {t₀ : ℝ} (hΩ : MeasurableSet Ω)
    (hΩb : Ω ⊆ univ ×ˢ Ico t₀ (t₀ + 1)) (hΩL : ∀ z ∈ Ω, -2 ≤ z.1 + L)
    (hu : ∀ z ∈ Ω, DifferentiableAt ℝ u (positiveEndChart q (z + (L + 4, 0)))) :
    ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity
        (PSSPlane.negative.endComponent (positiveEndHamiltonian H q) 1)
        (PSSPlane.negative.endComponent (positiveEndHamiltonian H q) I)
        (fun z ↦ u (positiveEndChart q (z + (L + 4, 0)))) z) =
      ∫⁻ y in (fun z ↦ positiveEndChart q (z + (L + 4, 0))) '' Ω, ENNReal.ofReal
        (ω.floerEnergyDensity
          (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x I) u y) := by
  set ψ : ℝ × ℝ → ℝ × ℝ := fun z ↦ positiveEndChart q (z + (L + 4, 0))
  have hinj : InjOn ψ Ω := by
    intro a ha b hb hab
    have ha' : a + (L + 4, 0) ∈ univ ×ˢ Ico t₀ (t₀ + 1) := ⟨mem_univ _, by simpa using (hΩb ha).2⟩
    have hb' : b + (L + 4, 0) ∈ univ ×ˢ Ico t₀ (t₀ + 1) := ⟨mem_univ _, by simpa using (hΩb hb).2⟩
    exact add_right_cancel (injOn_positiveEndChart q t₀ ha' hb' hab)
  refine (lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hΩ hinj
    (fun z _ ↦ (hasFDerivAt_positiveEndChart_add q (L + 4, 0) z).differentiableAt)
    fun z hz ↦ ?_).symm
  have hψ := hasFDerivAt_positiveEndChart_add q (L + 4, 0) z
  have h0 : 0 < (z + (L + 4, 0)).1 := by
    rw [Prod.fst_add]
    linarith [hΩL z hz]
  have hK := differentiableAt_cappedPerturbation_positiveEndChart hHd 1 L h0
  have hcomp : (fun z ↦ u (ψ z)) = u ∘ ψ := rfl
  have hKs : perturbationPullback ψ
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x I)
      stdComplexLineReal z = PSSPlane.negative.endComponent (positiveEndHamiltonian H q) 1 z :=
    funext fun x ↦ by rw [perturbationPullback_positiveEndChart_add_cappedPerturbation hH
      (hΩL z hz), equivRealProdCLM_symm_stdComplexLineReal, one_mul]
  have hKt : perturbationPullback ψ
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x I)
      stdComplexLineImag z = PSSPlane.negative.endComponent (positiveEndHamiltonian H q) I z :=
    funext fun x ↦ by rw [perturbationPullback_positiveEndChart_add_cappedPerturbation hH
      (hΩL z hz), equivRealProdCLM_symm_stdComplexLineImag, one_mul]
  rw [← ω.floerEnergyDensity_congr_perturbation _ hKs hKt, hcomp,
    ω.floerEnergyDensity_perturbationPullback hψ.differentiableAt (hu z hz) (hK 1 _) (hK I _),
    hψ.fderiv, abs_of_pos (det_fderiv_positiveEndChart_pos q _)]

end Plane

section PlaneCompactness

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **Capped pairs of pants converge on the PSS plane pieces as the necks stretch.** Let `q` be an
end and `H_q` a period-one `C³` Hamiltonian. Fix compact sets `D ⊆ ℝ × ℝ` and `K ⊆ V`, and a `C²`
family `J` of structures on a neighbourhood `W` of `D × K` which is `ω`-tame on `D × K`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions on `S` of the Floer
equation `(du - X_K)^{0,1} = 0` of the capped perturbation `K = cappedPerturbation 1 Lₖ H`, for
structures `Jₖ(z, u)`, and with Floer energy at most `E`, and read them on the end `q` through the
positive end chart translated by `Lₖ + 4`, `wₖ(z) = uₖ(φ'_q(z + (Lₖ + 4, 0)))`. Let `Ω ⊆ D` be an
open subset of a band `ℝ × [t₀, t₀ + 1)` of angular width one, with `s + Lₖ ≥ -2` at every point
`(s, t)` of `Ω`, on which `Jₖ ∘ φ'_q(· + (Lₖ + 4, 0)) = J` and `wₖ(Ω) ⊆ K`. Then there are a
subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a continuous `v : Ω \ Z → K` such
that along `φ` every disc about a point of `Z` eventually carries energy at least `δ` for the
negative PSS plane datum with Hamiltonian `H'_q = positiveEndHamiltonian H q` in its end
coordinates, the differentials of the `wₖ` are bounded on every compact subset of `Ω \ Z`, and
`wₖ → v` locally uniformly on `Ω \ Z`. -/
theorem
    exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedPerturbation_plane
    (ω : SymplecticForm V) (q : Puncture) (hH : Periodic (H q) 1)
    (hHs : ContDiff ℝ 3 (uncurry (H q))) {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {K : Set V}
    (hW : IsOpen W) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃t₀ : ℝ⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄
      ⦃Jk : ℕ → ℝ × ℝ → V → AlmostComplexStructure V⦄ ⦃E : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ D → Ω ⊆ univ ×ˢ Ico t₀ (t₀ + 1) → (∀ k, ∀ z ∈ Ω, -2 ≤ z.1 + L k) →
      (∀ k, ContDiffOn ℝ 3 (u k) thricePuncturedSphereReal) →
      (∀ k, ∀ z ∈ thricePuncturedSphereReal,
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk k z (u k z)) (ω.perturbedFDeriv
          (fun z x ↦ cappedPerturbation 1 (L k) H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation 1 (L k) H (Complex.equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, ∀ z ∈ Ω, Jk k (positiveEndChart q (z + (L k + 4, 0))) = J z) →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ cappedPerturbation 1 (L k) H (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ cappedPerturbation 1 (L k) H (Complex.equivRealProdCLM.symm z) x I)
          (u k) z) ≤ E) →
      (∀ k, MapsTo (fun z ↦ u k (positiveEndChart q (z + (L k + 4, 0)))) Ω K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω,
          ω.floerEnergyDensity (PSSPlane.negative.endComponent (positiveEndHamiltonian H q) 1)
            (PSSPlane.negative.endComponent (positiveEndHamiltonian H q) I)
            (fun z ↦ u (φ n) (positiveEndChart q (z + (L (φ n) + 4, 0)))) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ M, ∀ n, ∀ y ∈ C,
          ‖fderiv ℝ (fun z ↦ u (φ n) (positiveEndChart q (z + (L (φ n) + 4, 0)))) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n z ↦ u (φ n) (positiveEndChart q (z + (L (φ n) + 4, 0)))) v
          atTop (Ω \ ↑Z) := by
  -- The datum of the negative PSS plane in its end coordinates is `β(-s - 1) H'_q(t) dt`.
  set Ps : ℝ × ℝ → V → ℝ := PSSPlane.negative.endComponent (positiveEndHamiltonian H q) 1
  set Pt : ℝ × ℝ → V → ℝ := PSSPlane.negative.endComponent (positiveEndHamiltonian H q) I
  have hP (v : ℂ) : ContDiff ℝ 3
      (uncurry (PSSPlane.negative.endComponent (positiveEndHamiltonian H q) v)) :=
    PSSPlane.negative.contDiff_uncurry_endComponent (n := 3) (periodic_positiveEndHamiltonian hH)
      (contDiff_uncurry_positiveEndHamiltonian hHs) v
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hW
    (hP 1).contDiffOn (hP I).contDiffOn hJ hD hK hDKW hJt
  refine ⟨δ, hδ, fun Ω t₀ L u Jk E hΩ hΩD hΩb hΩL hu hfl hJΩ hE huK ↦ ?_⟩
  -- The translated maps solve the Floer equation of the plane piece on `Ω`.
  set w : ℕ → ℝ × ℝ → V := fun k z ↦ u k (positiveEndChart q (z + (L k + 4, 0)))
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hψS (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) :
      positiveEndChart q (z + (L k + 4, 0)) ∈ thricePuncturedSphereReal :=
    positiveEndChart_mem_thricePuncturedSphereReal
      (by simp only [Prod.fst_add]; linarith [hΩL k z hz])
  have hdiffu (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) :
      DifferentiableAt ℝ (u k) (positiveEndChart q (z + (L k + 4, 0))) :=
    ((hu k).differentiableOn (by norm_num)).differentiableAt
      (isOpen_thricePuncturedSphereReal.mem_nhds (hψS k hz))
  have hHd (t : ℝ) : Differentiable ℝ (H q t) :=
    (hHs.differentiable (by norm_num)).comp ((differentiable_const t).prodMk differentiable_id)
  have hflw (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) :
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (w k z))
        (ω.perturbedFDeriv Ps Pt (w k) z : ℝ × ℝ →ₗ[ℝ] V) := by
    have h := hfl k _ (hψS k hz)
    rw [hJΩ k z hz] at h
    exact ω.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_add_of_cappedPerturbation hH
      hHd (hΩL k z hz) (hdiffu k hz) h
  -- Their energy over `Ω` is the energy of `uₖ` over the image of `Ω`, at most `E`.
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity Ps Pt (w k) z) ≤ E := by
    rw [ω.lintegral_floerEnergyDensity_comp_positiveEndChart_add_eq_image_cappedPerturbation hH
      hHd hΩm hΩb (hΩL k) fun z hz ↦ hdiffu k hz]
    exact (setLIntegral_le_lintegral _ _).trans (hE k)
  have hwΩ (k : ℕ) : ContDiffOn ℝ 3 (w k) Ω :=
    (hu k).comp ((contDiff_positiveEndChart q 3).comp (contDiff_id.add contDiff_const)).contDiffOn
      fun _ hz ↦ hψS k hz
  have hIE (k : ℕ) := MeasureTheory.integrable_and_integral_le_of_lintegral_ofReal_le
    ((ω.continuousOn_floerEnergyDensity hΩ ((hwΩ k).of_le (by norm_num))
      ((hP 1).of_le (by norm_num)).contDiffOn ((hP I).of_le (by norm_num)).contDiffOn
        ).aestronglyMeasurable hΩm)
    (ae_restrict_of_forall_mem hΩm fun z hz ↦
      ω.floerEnergyDensity_nonneg (hJt z (hΩD hz) _ (huK k hz)) (hflw k hz)) (hlin k)
  exact hconv hΩ hΩD hwΩ (fun k z hz ↦ hflw k hz) huK (fun k ↦ (hIE k).1) fun k ↦ (hIE k).2

end PlaneCompactness

end TauCeti.SymplecticForm
