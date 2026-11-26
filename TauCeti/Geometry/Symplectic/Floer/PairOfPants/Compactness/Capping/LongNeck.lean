/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Closed
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capping
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness at the long-neck end of the capping family in a closed manifold

The unit property of the pair-of-pants product is proved with the *capping family*: plumbing the
negative PSS plane with Hamiltonian `H_1` into the input end at `1` of the pair of pants
`S = ℂ ∖ {0, 1}` with Hamiltonians `H_0`, `H_1`, `H_∞`, along a neck of length `L`, gives the datum
`K_L = TauCeti.Floer.plumbedPerturbation (Pi.single ∞ H_1) H 1 L` on the capped plane `ℂ ∖ {0}`.
As `L → ∞` the capped plane breaks into the pair of pants and the inserted plane. This file proves
the interior part of Gromov–Floer compactness at this end of the family, for a closed manifold
target `M` with a nondegenerate two-form `ω`, uniformly in `L` and with no condition on where the
solutions take their values. `TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Capping`
proves the same for a symplectic vector space target, with images in a fixed compact set.

The general compactness theorem in a closed manifold,
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in the
namespace `TauCeti.SmoothTwoForm` (`TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`), is for
fixed data, while `K_L` depends on `L`. On each of the two pieces the solutions are read so that the
data no longer depend on `L`:

* **The pair of pants.** On the truncation `S_R`, for `L ≥ R + 2`, the capping datum is the
  pair-of-pants datum of the `H_q`
  (`Floer.plumbedPerturbation_eq_pairOfPantsPerturbation_of_mem_truncation`), so the solutions
  themselves solve a fixed Floer equation there.
* **The inserted plane.** Let `ψ_L` be the plumbing chart of the end at `1`, which carries the plane
  into the capped plane, its pole `0` to the capped puncture `1`. Outside the circle `s_∞ = -L/2`
  of the end of the plane, `u ∘ ψ_L` solves the Floer equation of the negative plane datum of `H_1`
  (`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_realChart_plumbingMap_single_inf`),
  and its energy over a region is the energy of `u` over the image
  (`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_image_plumbingMap_single_inf`). This region
  contains every compact window `D'` of the plane once `L` is large, the pole included.

In both cases the Floer energy over the window is at most the Floer energy of the solution over the
capped plane, and the energy densities are integrable over the window because they are continuous
on a neighbourhood of a compact set.

As in `TauCeti.Geometry.Symplectic.Floer.Compactness.Closed`, sizes in `M` are measured through an
injective differentiable map `e : M → F` into a normed space, such as the Whitney embedding of a
closed manifold, with the structures uniformly tame with respect to `e` and the pushforwards
through `e` of the Hamiltonian vector fields bounded.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping_plane`: on a compact
  window `D'` of the inserted plane, solutions of the capping family of energy at most `E` and neck
  lengths `Lₖ` large enough for `D'`, read through the plumbing charts `ψ_{Lₖ}`, have a subsequence
  converging off a finite set `Z'` of bubbling points, with `#Z' * δ ≤ E`.
* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping_pants`: the same on
  a compact window `D` of a truncation `S_R` of the pair of pants, for neck lengths `Lₖ ≥ R + 2`.
* `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping_longNeck`: along a
  single subsequence the solutions converge on a compact window of the pair of pants off a finite
  set `Z`, and read through `ψ_{Lₖ}` on a compact window of the plane off a finite set `Z'`, with
  `#Z * δ ≤ E` and `#Z' * δ ≤ E`.

The bubbles at the points of `Z` and `Z'`, the Floer cylinders that break off along the neck and the
regularity of the limits are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  unit of the pair-of-pants product.
* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on capping inputs of the pair of pants.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart)
open scoped Manifold NNReal Real
open TauCeti.MeasureTheory

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer

variable {E G M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace G M] [IsManifold I ⊤ M] [CompactSpace M] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {ω : SmoothTwoForm I M} {Hb : Puncture → ℝ → M → ℝ} {e : M → F}

omit [I.Boundaryless] [CompactSpace M] in
/-- For a `C¹` map `u` on the capped plane whose Floer energy for the capping datum `K_L` is at most
`E`, the energy density of `u ∘ ψ_L` for the negative plane datum is integrable over an open subset
`Ω'` of a compact window `D'` of the plane lying outside the circle `s_∞ = -L/2`, with integral at
most `E`. -/
private theorem integrableOn_and_setIntegral_floerEnergyDensity_comp_realChart_le
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 2 (uncurry (Hb r))) {L : ℝ} (hL : 4 < L)
    {D' Ω' : Set (ℝ × ℝ)} (hD' : IsCompact D') (hΩ' : IsOpen Ω') (hΩ'D : Ω' ⊆ D')
    (hwL : ∀ w ∈ D', inf.endSign * (inf.endCoord (equivRealProdCLM.symm w)).re ≤ L / 2)
    {u : ℝ × ℝ → M} (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u {z | equivRealProdCLM.symm z ≠ 0})
    {E₀ : ℝ≥0} (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one L
        (equivRealProdCLM.symm z) x Complex.I) u z) ≤ E₀) :
    IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm z) x Complex.I)
      (u ∘ realChart (one.plumbingMap L))) Ω' ∧
    ∫ w in Ω', ω.floerEnergyDensity
      (fun z x ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm z) x 1)
      (fun z x ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm z) x Complex.I)
      (u ∘ realChart (one.plumbingMap L)) w ≤ E₀ := by
  have hPo : IsOpen {z : ℝ × ℝ | equivRealProdCLM.symm z ≠ 0} :=
    isOpen_ne_fun equivRealProdCLM.symm.continuous continuous_const
  have hψ : ContDiff ℝ 1 (realChart (one.plumbingMap L)) := contDiff_realChart_plumbingMap one L
  have hψP {w : ℝ × ℝ} (hw : w ∈ D') :=
    equivRealProdCLM_symm_realChart_plumbingMap_ne_zero (by linarith) (hwL w hw)
  -- The Hamiltonian vector fields of the plane datum are continuous on the whole plane.
  have hX (v : ℂ) : ContinuousOn (fun p : (ℝ × ℝ) × M ↦ (⟨p.2, ω.hamiltonianVectorField
      (fun y ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm p.1) y v) p.2⟩ :
        TangentBundle I M)) ((realChart (one.plumbingMap L) ⁻¹'
          {z | equivRealProdCLM.symm z ≠ 0}) ×ˢ univ) :=
    (hω.contMDiff_hamiltonianVectorField_uncurry (n := 1) (by simp)
      (contMDiff_negativePlanePerturbation_apply (hHb one) (hHbs one) v)).continuous.continuousOn
  refine ⟨((ω.continuousOn_floerEnergyDensity (hPo.preimage hψ.continuous)
    (hu.comp hψ.contMDiff.contMDiffOn fun _ hw ↦ hw) (hX 1) (hX Complex.I)).mono
      fun w hw ↦ hψP hw).integrableOn_compact hD' |>.mono_set hΩ'D, ?_⟩
  -- The energy over `Ω'` is the energy of `u` over `ψ_L(Ω')`, at most `E`.
  rw [← ω.integral_floerEnergyDensity_image_plumbingMap_single_inf (by decide) hHb
    (fun r ↦ (hHbs r).of_le (by norm_num)) hL hΩ'.measurableSet (fun w hw ↦ hwL w (hΩ'D hw))
    fun w hw ↦ (hu.contMDiffAt (hPo.mem_nhds (hψP (hΩ'D hw)))).mdifferentiableAt one_ne_zero]
  exact setIntegral_le_of_lintegral_ofReal_le hE _

/-- **The plane piece at the long-neck end of the capping family, in a closed manifold.** Let `ω`
be a nondegenerate two-form on a closed manifold `M`, let `Hb` be period-one `C³` Hamiltonians, and
let `K_L` be the capping datum obtained by plumbing the negative plane with Hamiltonian `Hb 1` into
the input end at `1` of the pair of pants with Hamiltonians `Hb`, along a neck of length `L`; let
`ψ_L` be the plumbing chart, from the plane into the capped plane `ℂ ∖ {0}`. Fix a compact window
`D'` of the plane inside the disc `‖w‖ ≤ 2 exp (2πρ)`, contained in an open set `U'` on which
structures `J'(w, x)` on the tangent spaces of `M` are `C²` read in the chart at every point of `M`,
tamed by `ω` over `D'`. Let `e : M → F` be injective and differentiable, and over `D'` let `J'` be
uniformly tame with respect to `e`, `c ‖d e v‖² ≤ ω(v, J' v)` with `c > 0`, and let the
pushforwards through `e` of the Hamiltonian vector fields of the two components of the negative
plane datum be at most `B`. There is a threshold `δ > 0` with the following property. Let `uₖ` be
`C³` maps on the capped plane solving the Floer equation of `K_{Lₖ}` there for structures `Jₖ`, with
Floer energy at most `E` and neck lengths `Lₖ > 4` with `Lₖ ≥ 2ρ`, and let `Ω' ⊆ D'` be open, with
`Jₖ ∘ ψ_{Lₖ} = J'` there. Then the maps `uₖ ∘ ψ_{Lₖ}`, which solve the Floer equation of the
negative plane datum of `Hb 1` on `Ω'`, have a subsequence along which every disc about a point of
a finite set `Z' ⊆ Ω'` with `#Z' * δ ≤ E` eventually carries energy at least `δ`, the energy
densities are uniformly bounded on every compact subset of `Ω' \ Z'`, and the maps converge on
`Ω' \ Z'` to a continuous map `v'`, locally uniformly after applying `e` and pointwise in `M`. The
window `D'` may contain the pole `0` of the plane and the point `1`, where the capping fills in the
punctures of the inserted piece. The vector-space case is
`SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_capping_plane`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping_plane
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Hb r))) {ρ : ℝ}
    {U' D' : Set (ℝ × ℝ)} (hU' : IsOpen U') (hD' : IsCompact D') (hD'U' : D' ⊆ U')
    (hD'ρ : ∀ w ∈ D', ‖equivRealProdCLM.symm w‖ ≤ 2 * Real.exp (2 * π * ρ))
    {J' : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ' : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J') (U' ×ˢ (extChartAt I α).target))
    (hJ't : ∀ w ∈ D', ∀ x, (hω.symplecticFormAt x).Tames (J' w x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c B : ℝ} (hc : 0 < c)
    (hJ'c : ∀ w ∈ D', ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J' w x v))
    (hBs : ∀ w ∈ D', ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm w) y 1) x)‖ ≤ B)
    (hBt : ∀ w ∈ D', ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm w) y Complex.I) x)‖ ≤
        B) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω' : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄
      ⦃Jk : ℕ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)⦄ ⦃E₀ : ℝ≥0⦄,
      IsOpen Ω' → Ω' ⊆ D' → (∀ k, 4 < L k) → (∀ k, 2 * ρ ≤ L k) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) {z | equivRealProdCLM.symm z ≠ 0}) →
      (∀ k z, equivRealProdCLM.symm z ≠ 0 →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk k z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k, ∀ w ∈ Ω', Jk k (realChart (one.plumbingMap (L k)) w) = J' w) →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
            (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤ E₀) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z' : Finset (ℝ × ℝ), ↑Z' ⊆ Ω' ∧ Z'.card * δ ≤ E₀ ∧
        (∀ z ∈ Z', ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω', ω.floerEnergyDensity
          (fun z x ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n) ∘ realChart (one.plumbingMap (L (φ n)))) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω' \ ↑Z' → ∃ A, ∀ n, ∀ y ∈ C, ω.floerEnergyDensity
          (fun z x ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n) ∘ realChart (one.plumbingMap (L (φ n)))) y ≤ A) ∧
        ∃ v' : ℝ × ℝ → M, ContinuousOn v' (Ω' \ ↑Z') ∧
          TendstoLocallyUniformlyOn
            (fun n ↦ e ∘ (u (φ n) ∘ realChart (one.plumbingMap (L (φ n))))) (e ∘ v') atTop
            (Ω' \ ↑Z') ∧
          ∀ z ∈ Ω' \ ↑Z',
            Tendsto (fun n ↦ (u (φ n) ∘ realChart (one.plumbingMap (L (φ n)))) z) atTop
              (𝓝 (v' z)) := by
  -- The plane datum is smooth on the whole plane, including the pole, so its Hamiltonian vector
  -- fields are `C²` in every chart.
  have hK (v : ℂ) : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1)
      (uncurry fun z x ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm z) x v) :=
    contMDiff_negativePlanePerturbation_apply (hHb one) (hHbs one) v
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    he he_inj hU' hD' hD'U' hJ'
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) fun _ _ _ ↦ (hK 1).contMDiffAt)
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) fun _ _ _ ↦
      (hK Complex.I).contMDiffAt) hJ't hc hJ'c hBs hBt
  refine ⟨δ, hδ, fun Ω' L u Jk E₀ hΩ' hΩ'D hL4 hLρ hu hfl hJΩ' hE ↦ ?_⟩
  have hPo : IsOpen {z : ℝ × ℝ | equivRealProdCLM.symm z ≠ 0} :=
    isOpen_ne_fun equivRealProdCLM.symm.continuous continuous_const
  -- The window `D'` lies outside the circle `s_∞ = -Lₖ/2`, and `ψₖ` carries it into `ℂ ∖ {0}`.
  have hwL (k : ℕ) (w : ℝ × ℝ) (hw : w ∈ D') :
      inf.endSign * (inf.endCoord (equivRealProdCLM.symm w)).re ≤ L k / 2 :=
    endSign_mul_re_endCoord_inf_le (by linarith [hL4 k]) (hLρ k) (hD'ρ w hw)
  have hψP (k : ℕ) {w : ℝ × ℝ} (hw : w ∈ D') :=
    equivRealProdCLM_symm_realChart_plumbingMap_ne_zero (by linarith [hL4 k]) (hwL k w hw)
  have h (k : ℕ) := integrableOn_and_setIntegral_floerEnergyDensity_comp_realChart_le hω hHb
    (fun r ↦ (hHbs r).of_le (by norm_num)) (hL4 k) hD' hΩ' hΩ'D (hwL k)
    ((hu k).of_le (by norm_num)) (hE k)
  refine hconv hΩ' hΩ'D (fun k ↦ (hu k).comp
    (contDiff_realChart_plumbingMap one (L k)).contMDiff.contMDiffOn fun w hw ↦ hψP k (hΩ'D hw))
    (fun k w hw ↦ ?_) (fun k ↦ (h k).1) fun k ↦ (h k).2
  -- `uₖ ∘ ψₖ` solves the Floer equation of the plane datum.
  have h := hfl k _ (hψP k (hΩ'D hw))
  rw [hJΩ' k w hw] at h
  exact ω.isComplexLinearMap_perturbedMFDeriv_comp_realChart_plumbingMap_single_inf (by decide) hHb
    (fun r ↦ (hHbs r).of_le (by norm_num)) (hL4 k) (hwL k w (hΩ'D hw))
    (((hu k).contMDiffAt (hPo.mem_nhds (hψP k (hΩ'D hw)))).mdifferentiableAt (by norm_num)) h

/-- **The pair-of-pants piece at the long-neck end of the capping family, in a closed manifold.**
Let `ω` be a nondegenerate two-form on a closed manifold `M`, let `Hb` be period-one `C³`
Hamiltonians, and let `K_L` be the capping datum obtained by plumbing the negative plane with
Hamiltonian `Hb 1` into the input end at `1` of the pair of pants with Hamiltonians `Hb`, along a
neck of length `L`. Fix a compact window `D` of the truncation `S_R` of the pair of pants and
structures `J(z, x)` on the tangent spaces of `M` which are `C²` read in the chart at every point of
`M` over `S = ℂ ∖ {0, 1}` and tamed by `ω` over `D`. Let `e : M → F` be injective and
differentiable, and over `D` let `J` be uniformly tame with respect to `e`,
`c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`, and let the pushforwards through `e` of the Hamiltonian
vector fields of the two components of the pair-of-pants datum of `Hb` be at most `B`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` maps on the capped plane solving
the Floer equation of `K_{Lₖ}` there for structures `Jₖ`, with Floer energy at most `E` and neck
lengths `Lₖ ≥ R + 2`, and let `Ω ⊆ D` be open, with `Jₖ = J` there. Then the maps `uₖ`, which
solve the Floer equation of the pair-of-pants datum of `Hb` on `Ω`, have a subsequence along which
every disc about a point of a finite set `Z ⊆ Ω` with `#Z * δ ≤ E` eventually carries energy at
least `δ`, the energy densities are uniformly bounded on every compact subset of `Ω \ Z`, and the
maps converge on `Ω \ Z` to a continuous map `v`, locally uniformly after applying `e` and pointwise
in `M`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping_pants
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Hb r))) {R : ℝ}
    {D : Set (ℝ × ℝ)} (hD : IsCompact D) (hDT : D ⊆ equivRealProdCLM.symm ⁻¹' truncation R)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J)
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hBs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation Hb (equivRealProdCLM.symm z) y 1) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation Hb (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ B) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄
      ⦃Jk : ℕ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)⦄ ⦃E₀ : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, R + 2 ≤ L k) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) {z | equivRealProdCLM.symm z ≠ 0}) →
      (∀ k z, equivRealProdCLM.symm z ≠ 0 →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk k z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k, ∀ z ∈ Ω, Jk k z = J z) →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
            (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤ E₀) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation Hb (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Hb (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ A, ∀ n, ∀ y ∈ C, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation Hb (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Hb (equivRealProdCLM.symm z) x Complex.I)
          (u (φ n)) y ≤ A) ∧
        ∃ v : ℝ × ℝ → M, ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          ∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z)) := by
  have hDS : D ⊆ thricePuncturedSphereReal := fun z hz ↦ truncation_subset R (hDT hz)
  -- On `S` the pair-of-pants datum is `C³` jointly in the domain and target points, so its
  -- Hamiltonian vector fields are `C²` in every chart and continuous.
  have hK (v : ℂ) (z : ℝ × ℝ) (hz : z ∈ thricePuncturedSphereReal) (x : M) :
      ContMDiffAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) ((2 : ℕ∞) + 1)
        (uncurry fun z x ↦ pairOfPantsPerturbation Hb (equivRealProdCLM.symm z) x v) (z, x) :=
    (contMDiffAt_uncurry_pairOfPantsPerturbation hHb hHbs hz x v).of_le (by norm_num)
  have hX (v : ℂ) : ContinuousOn (fun p : (ℝ × ℝ) × M ↦ (⟨p.2, ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation Hb (equivRealProdCLM.symm p.1) y v) p.2⟩ :
        TangentBundle I M)) (thricePuncturedSphereReal ×ˢ univ) := fun p hp ↦
    (hω.contMDiffAt_hamiltonianVectorField_uncurry (n := 1) (by simp)
      ((hK v p.1 hp.1 p.2).of_le (by norm_num))).continuousAt.continuousWithinAt
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    he he_inj isOpen_thricePuncturedSphereReal hD hDS hJ
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK 1))
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt (hK Complex.I)) hJt hc hJc hBs hBt
  refine ⟨δ, hδ, fun Ω L u Jk E₀ hΩ hΩD hLR hu hfl hJΩ hE ↦ ?_⟩
  have hΩS : Ω ⊆ thricePuncturedSphereReal := hΩD.trans hDS
  -- On the truncation `S_R` the capping datum is the pair-of-pants datum of `Hb`, so `uₖ` solves
  -- the Floer equation of the pair-of-pants datum on `Ω`, with energy at most `E` there.
  refine hconv hΩ hΩD (fun k ↦ (hu k).mono fun z hz ↦ (hΩS hz).1)
    (fun k z hz ↦ hJΩ k z hz ▸ ω.perturbedMFDeriv_plumbedPerturbation_of_mem_truncation
      (Ha := Pi.single inf (Hb one)) (Hb := Hb) (q := one) (by decide) (by simp) (hLR k) (u k)
      (hDT (hΩD hz)) ▸ hfl k z (hΩS hz).1)
    (fun k ↦ (((ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal
      (((hu k).mono fun _ (hz : _ ∈ thricePuncturedSphereReal) ↦ hz.1).of_le (by norm_num))
      (hX 1) (hX Complex.I)).mono hDS).integrableOn_compact hD).mono_set hΩD) fun k ↦
    ω.setIntegral_floerEnergyDensity_pairOfPantsPerturbation_le (Ha := Pi.single inf (Hb one))
      (Hb := Hb) (q := one) (by decide) (by simp) (hLR k) hΩ.measurableSet (hΩD.trans hDT)
      (hE k)

/-- **Compactness at the long-neck end of the capping family, in a closed manifold.** Combine
the settings of `exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping_pants`,
with a compact window `D` of the truncation `S_R` of the pair of pants, and of
`exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping_plane`, with a compact
window `D'` of the inserted plane. There is a threshold `δ > 0` with the following
property. Let `uₖ`, `Ω` and `Ω'` be as there. Then along a single subsequence `uₖ` converges on
`Ω` off a finite set `Z` to a continuous
map `v`, and `uₖ ∘ ψ_{Lₖ}` converges on `Ω'` off a finite set `Z'` to a continuous map `v'`, both
locally uniformly after applying `e` and pointwise in `M`, with `#Z * δ ≤ E` and `#Z' * δ ≤ E`. As
the necks stretch, the capping family thus converges on the pair of pants and on the inserted plane,
including its pole. The vector-space case is
`SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_capping_longNeck`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping_longNeck
    (hω : ω.IsNondegenerate) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Hb r))) {R ρ : ℝ}
    {D U' D' : Set (ℝ × ℝ)} (hD : IsCompact D)
    (hDT : D ⊆ equivRealProdCLM.symm ⁻¹' truncation R) (hU' : IsOpen U') (hD' : IsCompact D')
    (hD'U' : D' ⊆ U') (hD'ρ : ∀ w ∈ D', ‖equivRealProdCLM.symm w‖ ≤ 2 * Real.exp (2 * π * ρ))
    {J J' : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J)
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ D, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    (hJ' : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J') (U' ×ˢ (extChartAt I α).target))
    (hJ't : ∀ w ∈ D', ∀ x, (hω.symplecticFormAt x).Tames (J' w x))
    (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c B : ℝ} (hc : 0 < c)
    (hJc : ∀ z ∈ D, ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hJ'c : ∀ w ∈ D', ∀ x v, c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J' w x v))
    (hBs : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation Hb (equivRealProdCLM.symm z) y 1) x)‖ ≤ B)
    (hBt : ∀ z ∈ D, ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ pairOfPantsPerturbation Hb (equivRealProdCLM.symm z) y Complex.I) x)‖ ≤ B)
    (hB's : ∀ w ∈ D', ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm w) y 1) x)‖ ≤ B)
    (hB't : ∀ w ∈ D', ∀ x, ‖mvfderiv I e x (ω.hamiltonianVectorField
      (fun y ↦ negativePlanePerturbation (Hb one) (equivRealProdCLM.symm w) y Complex.I) x)‖ ≤
        B) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω Ω' : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄
      ⦃Jk : ℕ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)⦄ ⦃E₀ : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ D → IsOpen Ω' → Ω' ⊆ D' →
      (∀ k, 4 < L k) → (∀ k, R + 2 ≤ L k) → (∀ k, 2 * ρ ≤ L k) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) {z | equivRealProdCLM.symm z ≠ 0}) →
      (∀ k z, equivRealProdCLM.symm z ≠ 0 →
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk k z (u k z))
          (ω.perturbedMFDeriv
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x 1)
            (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
              (equivRealProdCLM.symm z) x Complex.I)
            (u k) z).toLinearMap) →
      (∀ k, ∀ z ∈ Ω, Jk k z = J z) →
      (∀ k, ∀ w ∈ Ω', Jk k (realChart (one.plumbingMap (L k)) w) = J' w) →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
            (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation (Pi.single inf (Hb one)) Hb one (L k)
            (equivRealProdCLM.symm z) x Complex.I) (u k) z) ≤ E₀) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ Z Z' : Finset (ℝ × ℝ), ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        ↑Z' ⊆ Ω' ∧ Z'.card * δ ≤ E₀ ∧ ∃ v v' : ℝ × ℝ → M,
          ContinuousOn v (Ω \ ↑Z) ∧
          TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (φ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
          (∀ z ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) z) atTop (𝓝 (v z))) ∧
          ContinuousOn v' (Ω' \ ↑Z') ∧
          TendstoLocallyUniformlyOn
            (fun n ↦ e ∘ (u (φ n) ∘ realChart (one.plumbingMap (L (φ n))))) (e ∘ v') atTop
            (Ω' \ ↑Z') ∧
          ∀ z ∈ Ω' \ ↑Z',
            Tendsto (fun n ↦ (u (φ n) ∘ realChart (one.plumbingMap (L (φ n)))) z) atTop
              (𝓝 (v' z)) := by
  obtain ⟨δ₁, hδ₁, hconv₁⟩ :=
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping_pants hHb hHbs hD
      hDT hJ hJt he he_inj hc hJc hBs hBt
  obtain ⟨δ₂, hδ₂, hconv₂⟩ :=
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_capping_plane hHb hHbs
      hU' hD' hD'U' hD'ρ hJ' hJ't he he_inj hc hJ'c hB's hB't
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun Ω Ω' L u Jk E₀ hΩ hΩD hΩ' hΩ'D hL4 hLR hLρ hu hfl hJΩ
    hJΩ' hE ↦ ?_⟩
  -- On the pair of pants.
  obtain ⟨φ, hφ, Z, hZΩ, hZE, -, -, v, hvc, hlim, hpt⟩ := hconv₁ hΩ hΩD hLR hu hfl hJΩ hE
  -- On the inserted plane, along the same subsequence.
  obtain ⟨φ', hφ', Z', hZΩ', hZE', -, -, v', hvc', hlim', hpt'⟩ := hconv₂ hΩ' hΩ'D
    (fun n ↦ hL4 (φ n)) (fun n ↦ hLρ (φ n)) (fun n ↦ hu (φ n)) (fun n ↦ hfl (φ n))
    (fun n ↦ hJΩ' (φ n)) fun n ↦ hE (φ n)
  refine ⟨φ ∘ φ', hφ.comp hφ', Z, Z',
    hZΩ, (mul_le_mul_of_nonneg_left (min_le_left δ₁ δ₂) (Nat.cast_nonneg _)).trans hZE,
    hZΩ', (mul_le_mul_of_nonneg_left (min_le_right δ₁ δ₂) (Nat.cast_nonneg _)).trans hZE',
    v, v', hvc, hlim.comp_tendsto hφ'.tendsto_atTop,
    fun z hz ↦ (hpt z hz).comp hφ'.tendsto_atTop, hvc', hlim', hpt'⟩

end TauCeti.SmoothTwoForm.IsNondegenerate
