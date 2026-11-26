/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Action
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Energy
import TauCeti.Geometry.Symplectic.Floer.Compactness.Exhaustion
import TauCeti.Geometry.Symplectic.Floer.Compactness.Exhaustion.Closed
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Compactness.Manifold
import TauCeti.MeasureTheory.Integral.Bochner.Basic
import TauCeti.Topology.UniformSpace.LocallyUniformConvergence

/-!
# Compactness of plumbed four-punctured spheres as the neck stretches

Plumb the output end at `∞` of a pair of pants `S'`, with Hamiltonians `Ha`, into the input end
`q ≠ ∞` of a pair of pants `S`, with Hamiltonians `Hb q = Ha ∞`, along a neck of length `L`. The
result is the four-punctured sphere `Σ_L = ℂ ∖ {0, 1, ψ_L(1)}`, where `ψ_L` is the plumbing map
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L`, with the plumbed perturbation
`TauCeti.Floer.plumbedPerturbation`. As `L → ∞` these domains break into the two pairs of pants:
this is the broken-product end of the one-parameter families of four-punctured spheres that prove
the associativity of the pair-of-pants product. This file proves the interior part of
Gromov–Floer compactness at that end, for a symplectic vector space target `(V, ω)`, through
symplectic charts for a manifold target with a nondegenerate two-form (see the paragraph on
manifold targets below), and for a closed manifold target, with no condition on the images of the
solutions and convergence read after applying an injective map `e : M → F` (see the paragraph on
closed manifolds below).

Fix a truncation `S_R` (`TauCeti.ThricePuncturedSphere.truncation`) and let `L ≥ 2R + 2`. On the
receiving pair of pants, `S_R` lies in `Σ_L` and the plumbed datum there is the datum of `S`
(`TauCeti.Floer.plumbedPerturbation_eq_pairOfPantsPerturbation_of_mem_truncation`). On the
inserted pair of pants, `ψ_L` maps `S_R` into `Σ_L` and pulls the plumbed datum back to the datum
of `S'` (`TauCeti.Floer.perturbationPullback_plumbedPerturbation_of_mem_truncation`). Since
`ψ_L` is holomorphic, if `u` solves the Floer equation on `Σ_L` then `u ∘ ψ_L` solves the Floer
equation of `S'` on `S_R`
(`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_comp_realChart_plumbingMap`), and its
energy over a region `B` is the energy of `u` over `ψ_L(B)`.

So a sequence `uₖ` of Floer solutions on `Σ_{Lₖ}`, with neck lengths `Lₖ ≥ 2R + 2` and energy at
most `E`, restricts on each of the two pieces to a sequence of solutions of the Floer equation of
that pair of pants, with energy at most `E`. The compactness theorem for Floer solutions of bounded
energy (`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`)
applies on both pieces, first to the sequence and then to the resulting subsequence. The main
result of this file gives a threshold `δ > 0`, independent of the neck lengths, and a single
subsequence along which `uₖ` converges locally uniformly on open `Ω ⊆ S_R` off a finite set `Z`,
and `uₖ ∘ ψ_{Lₖ}` converges locally uniformly on open `Ω' ⊆ S_R` off a finite set `Z'`, with
`#Z * δ ≤ E` and `#Z' * δ ≤ E`. This is convergence on one fixed truncation of each piece.

When `Lₖ → ∞`, every compact subset of either pair of pants lies in the interior of the truncation
`S_{(Lₖ - 2)/2}` for all large `k`
(`TauCeti.ThricePuncturedSphere.exists_subset_interior_truncation`).
The theorem for solutions on exhausting domains
(`TauCeti.SymplecticForm.exists_tendstoLocallyUniformlyOn_subseq_off_discrete`) then applies on each
whole piece, and gives a single subsequence along which `uₖ` converges locally uniformly on `S`, and
`uₖ ∘ ψ_{Lₖ}` on `S`, off sets of bubbling points meeting every compact subset of `S` in finitely
many points
(`TauCeti.SymplecticForm.exists_tendstoLocallyUniformlyOn_subseq_off_discrete_plumbedPerturbation`).
Here the solutions take values in a fixed compact set and the structures agree with fixed ones on
the truncations `S_{(Lₖ - 2)/2}` of both pieces. The thresholds of the truncations shrink towards
the punctures, so these bubbling sets are not shown to be finite: that needs an energy threshold
uniform on the cylindrical ends.

The almost complex structures `Jₖ` on `Σ_{Lₖ}` are only required to agree with fixed structures
`J` on `Ω` and `J'` on `Ω'`, after the change of coordinates `ψ_{Lₖ}` on the inserted piece. The
plumbed structure `TauCeti.Floer.plumbedAlmostComplex` does so on `S_R` for `Lₖ ≥ 2R + 2`, so in
particular on `S_{(Lₖ - 2)/2}`
(`TauCeti.Floer.plumbedAlmostComplex_of_re_endCoord_le`,
`TauCeti.Floer.plumbedAlmostComplex_plumbingMap`). The regularity of the limits, the bubbles at
the points of `Z` and `Z'`, and the breaking of Floer cylinders off the neck are not treated here.

**Manifold targets.** For a manifold `M` with a nondegenerate two-form `ω`, such as a closed
symplectic manifold, and period-one `C³` Hamiltonians on `M`, the same argument runs through
symplectic charts, in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`
(`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_plumbedPerturbation`). On the
inserted pair of pants `u ∘ ψ_L` solves the Floer equation of `S'`, because the plumbing map is
holomorphic
(`TauCeti.SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_comp_realChart_plumbingMap`), and its
energy over a region `B` is the energy of `u` over `ψ_L(B)`
(`TauCeti.SmoothTwoForm.integral_floerEnergyDensity_plumbedPerturbation_inserted`). The compactness
theorem for Floer pairs of pants in a symplectic chart with energy bounded over the region
considered (in the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`,
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPants_of_setIntegral_le`)
then applies on each piece, to
the part `Ω` of the receiving truncation that the solutions map into a compact subset `K` of the
source of a chart `φ`, and to the part `Ω'` of the inserted truncation that the maps
`uₖ ∘ ψ_{Lₖ}` send into a compact subset `K'` of the source of a chart `φ'`, such as Darboux
charts. The structures are read in the charts by families `Jφ`, `Jφ'` on `V` with
`dφ_x ∘ J(z, x) = Jφ(z, φ x) ∘ dφ_x`, as in the chart theorem. The limits are read in the charts:
the coordinate maps converge locally uniformly off the bubbling points, and the maps themselves
converge pointwise in `M`.

**Closed manifolds.** When `M` is closed, no condition on the images of the solutions is needed.
On each piece the compactness theorem in a closed manifold
(`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset` in the
namespace `TauCeti.SmoothTwoForm`) applies to the truncation `S_R`, with sizes in `M` measured
through an injective differentiable map `e : M → F`, such as the Whitney embedding. This gives a
threshold `δ > 0`, independent of the neck lengths, and finite sets of bubbling points `Z ⊆ Ω`,
`Z' ⊆ Ω'` with `#Z * δ ≤ E` and `#Z' * δ ≤ E` at which energy at least `δ` concentrates, off which
`uₖ` and `uₖ ∘ ψ_{Lₖ}` converge, locally uniformly after applying `e` and pointwise in `M`
(`exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_plumbedPerturbation`, in the
namespace `TauCeti.SmoothTwoForm.IsNondegenerate`). When `Lₖ → ∞`, the theorem for solutions on
exhausting domains in a closed manifold
(`IsNondegenerate.exists_tendstoLocallyUniformlyOn_comp_subseq_off_discrete` in the namespace
`TauCeti.SmoothTwoForm`) applies on each whole piece, as for a vector space target, and gives the
convergence of `uₖ` on `S` and of `uₖ ∘ ψ_{Lₖ}` on `S` off sets of bubbling points meeting every
compact subset of `S` in finitely many points
(`exists_tendstoLocallyUniformlyOn_comp_subseq_off_discrete_plumbedPerturbation`). These limits
are the candidates for the two pieces of a broken-product limit of the associativity family; that
they solve the Floer equation, extend over the bubbling points and come with bubbles and broken
cylinders is not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the associativity of the pair-of-pants product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 10.9 (gluing and the limits of glued domains).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open TauCeti.Complex (realChart equivRealProdCLM_symm_realChart)
open scoped NNReal ENNReal

/-- The truncation `S_R`, read in real coordinates, for a neck length `L > 4` with `R ≤ L / 2`: it
lies in the plumbed four-punctured sphere `Σ_L`, and the plumbing map `ψ_L` carries it into `Σ_L`.
-/
private theorem TauCeti.ThricePuncturedSphere.Puncture.preimage_truncation_subset_plumbedSphere
    {q : Puncture} (hq : q ≠ inf) {R L : ℝ} (hL : 4 < L) (hRL : R ≤ L / 2) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆ {z : ℝ × ℝ |
        (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} ∧
      MapsTo (realChart (q.plumbingMap L)) (Complex.equivRealProdCLM.symm ⁻¹' truncation R)
        {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
  refine ⟨fun z hz ↦ mem_plumbedSphere_of_mem_truncation hq hL (truncation_mono hRL hz),
    fun w hw ↦ ?_⟩
  simp only [mem_ofPred_eq, equivRealProdCLM_symm_realChart]
  exact plumbingMap_mem_plumbedSphere_of_mem_truncation hq hL (truncation_mono hRL hw)

/-- As `Lₖ → ∞`, the interiors `Uₖ` of the truncations `S_{(Lₖ - 2)/2}`, read in real coordinates,
exhaust `S`: they are open subsets of the truncations, hence of `S`, they eventually contain every
compact subset of `S`, and `2 * ((Lₖ - 2) / 2) + 2 ≤ Lₖ`. -/
private theorem TauCeti.ThricePuncturedSphere.exhaustion_interior_truncation
    {L : ℕ → ℝ} (hL : Tendsto L atTop atTop) :
    (∀ k, IsOpen (Complex.equivRealProdCLM.symm ⁻¹' interior (truncation ((L k - 2) / 2)))) ∧
      (∀ k, Complex.equivRealProdCLM.symm ⁻¹' interior (truncation ((L k - 2) / 2)) ⊆
        Complex.equivRealProdCLM.symm ⁻¹' truncation ((L k - 2) / 2)) ∧
      (∀ k, Complex.equivRealProdCLM.symm ⁻¹' interior (truncation ((L k - 2) / 2)) ⊆
        Floer.thricePuncturedSphereReal) ∧
      (∀ C, IsCompact C → C ⊆ Floer.thricePuncturedSphereReal → ∀ᶠ k in atTop,
        C ⊆ Complex.equivRealProdCLM.symm ⁻¹' interior (truncation ((L k - 2) / 2))) ∧
      ∀ k, 2 * ((L k - 2) / 2) + 2 ≤ L k := by
  refine ⟨fun _ ↦ isOpen_interior.preimage Complex.equivRealProdCLM.symm.continuous,
    fun _ ↦ preimage_mono interior_subset,
    fun _ ↦ (preimage_mono interior_subset).trans
      (Floer.preimage_truncation_subset_thricePuncturedSphereReal _),
    fun C hC hCS ↦ ?_, fun _ ↦ by linarith⟩
  obtain ⟨R, hR⟩ := exists_subset_interior_truncation
    (hC.image Complex.equivRealProdCLM.symm.continuous) (image_subset_iff.2 hCS)
  filter_upwards [hL.eventually_ge_atTop (2 * R + 2)] with k hk
  exact (image_subset_iff.1 hR).trans
    (preimage_mono (interior_mono (truncation_mono (by linarith))))

namespace TauCeti.SymplecticForm

open Floer TauCeti.MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ha Hb : Puncture → ℝ → V → ℝ} {q : Puncture}

/-- **The receiving piece.** Let `4 < L` and `2R + 2 ≤ L`. A Floer solution `u` of the plumbed
perturbation on `Σ_L`, for structures `Jₖ` equal to `J` on an open `Ω ⊆ S_R`, is on `Ω` a Floer
solution of the receiving pair of pants for `J`, and its energy over `Ω` is at most its energy over
`Σ_L`. -/
private theorem receiving_piece (ω : SymplecticForm V) (hq : q ≠ inf)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHbs : ∀ r, ContDiff ℝ 3 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) {L R : ℝ} (hL4 : 4 < L) (hLR : 2 * R + 2 ≤ L) {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (hΩT : Ω ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R) {u : ℝ × ℝ → V}
    {Jk J : ℝ × ℝ → V → AlmostComplexStructure V} {E : ℝ≥0}
    (hu : ContDiffOn ℝ 3 u {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (hfl : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hJΩ : ∀ z ∈ Ω, Jk z = J z)
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x I) u z) ≤ E) :
    ContDiffOn ℝ 3 u Ω ∧
      (∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u z))
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x I)
          u z : ℝ × ℝ →ₗ[ℝ] V)) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x I) u) Ω ∧
      ∫ z in Ω, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x I) u z ≤ E := by
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  set P : Set (ℝ × ℝ) := {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}
  have hTS : T ⊆ thricePuncturedSphereReal := preimage_truncation_subset_thricePuncturedSphereReal R
  -- The truncation `S_R` lies in `Σ_L`, and there the plumbed datum is the datum of `S`.
  have hTP : T ⊆ P := (preimage_truncation_subset_plumbedSphere hq hL4 (by linarith)).1
  set Kb : ℂ → ℝ × ℝ → V → ℝ := fun v z x ↦
    pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x v
  set Kp : ℂ → ℝ × ℝ → V → ℝ := fun v z x ↦
    plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v
  have hKb {z : ℝ × ℝ} (hz : z ∈ T) (v : ℂ) : Kp v z = Kb v z :=
    funext fun x ↦ DFunLike.congr_fun
      (plumbedPerturbation_eq_pairOfPantsPerturbation_of_mem_truncation hq hab (by linarith) hz x) v
  -- The density is continuous on a neighbourhood of the compact truncation, so integrable.
  have hint : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x I) u) Ω :=
    (((ω.continuousOn_floerEnergyDensity
      (isOpen_thricePuncturedSphereReal.inter (isOpen_plumbedSphere q L))
      ((hu.mono inter_subset_right).of_le (by norm_num))
      ((contDiffOn_uncurry_pairOfPantsPerturbation hHb (fun r ↦ (hHbs r).of_le (by norm_num))
        1).mono (prod_mono inter_subset_left le_rfl))
      ((contDiffOn_uncurry_pairOfPantsPerturbation hHb (fun r ↦ (hHbs r).of_le (by norm_num))
        I).mono (prod_mono inter_subset_left le_rfl))).mono
        fun z hz ↦ ⟨hTS hz, hTP hz⟩).integrableOn_compact
      (isCompact_preimage_truncation R)).mono_set hΩT
  refine ⟨hu.mono fun z hz ↦ hTP (hΩT hz), fun z hz ↦ ?_, hint, ?_⟩
  · have h := hfl z (hTP (hΩT hz))
    rwa [hJΩ z hz, ω.perturbedFDeriv_congr _ (hKb (hΩT hz) 1) (hKb (hΩT hz) I)] at h
  · rw [setIntegral_congr_fun hΩ.measurableSet fun z hz ↦
      ω.floerEnergyDensity_congr_perturbation _ (hKb (hΩT hz) 1).symm (hKb (hΩT hz) I).symm]
    exact setIntegral_le_of_lintegral_ofReal_le hE _

/-- **The inserted piece.** Let `4 < L` and `2R + 2 ≤ L`, and let `ψ_L` be the plumbing map. If `u`
is a Floer solution of the plumbed perturbation on `Σ_L` whose structures `Jₖ` satisfy
`Jₖ ∘ ψ_L = J'` on an open `Ω ⊆ S_R`, then `u ∘ ψ_L` is on `Ω` a Floer solution of the inserted
pair of pants for `J'`, and its energy over `Ω` is at most the energy of `u` over `Σ_L`. -/
private theorem inserted_piece (ω : SymplecticForm V) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContDiff ℝ 3 (uncurry (Ha r))) (hHbs : ∀ r, ContDiff ℝ 3 (uncurry (Hb r)))
    (hab : Hb q = Ha inf) {L R : ℝ} (hL4 : 4 < L) (hLR : 2 * R + 2 ≤ L) {Ω : Set (ℝ × ℝ)}
    (hΩ : IsOpen Ω) (hΩT : Ω ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R) {u : ℝ × ℝ → V}
    {Jk J' : ℝ × ℝ → V → AlmostComplexStructure V} {E : ℝ≥0}
    (hu : ContDiffOn ℝ 3 u {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    (hfl : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk z (u z)) (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x I)
        u z : ℝ × ℝ →ₗ[ℝ] V))
    (hJΩ : ∀ w ∈ Ω, Jk (realChart (q.plumbingMap L) w) = J' w)
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x I) u z) ≤ E) :
    ContDiffOn ℝ 3 (u ∘ realChart (q.plumbingMap L)) Ω ∧
      (∀ w ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J' w ((u ∘ realChart (q.plumbingMap L)) w)) (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x I)
          (u ∘ realChart (q.plumbingMap L)) w : ℝ × ℝ →ₗ[ℝ] V)) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x I)
        (u ∘ realChart (q.plumbingMap L))) Ω ∧
      ∫ w in Ω, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x I)
        (u ∘ realChart (q.plumbingMap L)) w ≤ E := by
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  set P : Set (ℝ × ℝ) := {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1}
  set ψ := realChart (q.plumbingMap L)
  have hTS : T ⊆ thricePuncturedSphereReal := preimage_truncation_subset_thricePuncturedSphereReal R
  -- The plumbing map carries the truncation `S_R` into `Σ_L`.
  have hψP : MapsTo ψ T P := (preimage_truncation_subset_plumbedSphere hq hL4 (by linarith)).2
  have hψs : ContDiff ℝ 3 ψ := contDiff_realChart_plumbingMap q L
  have hU : IsOpen (thricePuncturedSphereReal ∩ ψ ⁻¹' P) :=
    isOpen_thricePuncturedSphereReal.inter ((isOpen_plumbedSphere q L).preimage hψs.continuous)
  have hua : ContDiffOn ℝ 3 (u ∘ ψ) (thricePuncturedSphereReal ∩ ψ ⁻¹' P) :=
    hu.comp hψs.contDiffOn fun _ hw ↦ hw.2
  have hint : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x I) (u ∘ ψ)) Ω :=
    (((ω.continuousOn_floerEnergyDensity hU (hua.of_le (by norm_num))
      ((contDiffOn_uncurry_pairOfPantsPerturbation hHa (fun r ↦ (hHas r).of_le (by norm_num))
        1).mono (prod_mono inter_subset_left le_rfl))
      ((contDiffOn_uncurry_pairOfPantsPerturbation hHa (fun r ↦ (hHas r).of_le (by norm_num))
        I).mono (prod_mono inter_subset_left le_rfl))).mono
        fun w hw ↦ ⟨hTS hw, hψP hw⟩).integrableOn_compact
      (isCompact_preimage_truncation R)).mono_set hΩT
  -- `Ω` lies beyond the collar `Re z_∞ ≤ 2 - L` of the inserted end at `∞`.
  have hsub : Ω ⊆ {w | (Complex.equivRealProdCLM.symm w ≠ 0 ∧
      Complex.equivRealProdCLM.symm w ≠ 1) ∧
      2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re} := fun w hw ↦ by
    have h := (mem_truncation.1 (hΩT hw)).2.2 inf
    rw [endSign_inf, neg_one_mul] at h
    exact ⟨⟨(mem_truncation.1 (hΩT hw)).1, (mem_truncation.1 (hΩT hw)).2.1⟩, by linarith⟩
  refine ⟨hua.mono fun w hw ↦ ⟨hTS (hΩT hw), hψP (hΩT hw)⟩, fun w hw ↦ ?_, hint, ?_⟩
  · -- On the inserted truncation `u ∘ ψ` solves the Floer equation of `S`.
    have h := hfl (ψ w) (hψP (hΩT hw))
    rw [hJΩ w hw] at h
    exact ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_plumbingMap hq hHa hHb
      (fun r ↦ (hHas r).of_le (by norm_num)) (fun r ↦ (hHbs r).of_le (by norm_num)) hab hL4
      (hsub hw) ((hu.differentiableOn (by norm_num)).differentiableAt
        ((isOpen_plumbedSphere q L).mem_nhds (hψP (hΩT hw)))) h
  · -- The energy of `u ∘ ψ` over `Ω` is the energy of `u` over `ψ(Ω)`.
    rw [← integral_floerEnergyDensity_image_plumbingMap ω hq hHa hHb
      (fun r ↦ (hHas r).of_le (by norm_num)) (fun r ↦ (hHbs r).of_le (by norm_num)) hab hL4
      hΩ.measurableSet hsub (hu.differentiableOn (by norm_num))]
    exact setIntegral_le_of_lintegral_ofReal_le hE _

/-- **Floer solutions on plumbed four-punctured spheres converge on both pieces.** Let `Ha`, `Hb` be
period-one `C³` Hamiltonians with `Hb q = Ha ∞`, `q ≠ ∞`. Fix a truncation `S_R` and a compact
`K ⊆ V`, and let `J`, `J'` be `C²` families of structures on the receiving and the inserted pair of
pants `S`, read in real coordinates, which are `ω`-tame on `S_R × K`. There is a threshold `δ > 0`
with the following property. Let `uₖ` be `C³` solutions of the Floer equation `(du - X_K)^{0,1} = 0`
of the plumbed perturbation `K` on the four-punctured spheres `Σ_{Lₖ}` with neck lengths `Lₖ > 4`
and `Lₖ ≥ 2R + 2`, for structures `Jₖ(z, u)`, and with Floer energy at most `E`. Let `Ω` and `Ω'` be
open subsets of `S_R`, on which `Jₖ = J` and `Jₖ ∘ ψ_{Lₖ} = J'` respectively, with `uₖ(Ω) ⊆ K` and
`uₖ(ψ_{Lₖ}(Ω')) ⊆ K`. Then there are a subsequence `φ`, finite sets `Z ⊆ Ω` and `Z' ⊆ Ω'` with
`#Z * δ ≤ E` and `#Z' * δ ≤ E`, and continuous maps `v : Ω \ Z → K` and `v' : Ω' \ Z' → K` such that
along `φ` the maps `uₖ` converge to `v` locally uniformly on `Ω \ Z`, and the maps `uₖ ∘ ψ_{Lₖ}` on
the inserted pair of pants converge to `v'` locally uniformly on `Ω' \ Z'`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_plumbedPerturbation
    (ω : SymplecticForm V) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHas : ∀ r, ContDiff ℝ 3 (uncurry (Ha r)))
    (hHbs : ∀ r, ContDiff ℝ 3 (uncurry (Hb r))) (hab : Hb q = Ha inf)
    (R : ℝ) {K : Set V} (hK : IsCompact K) {J J' : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (thricePuncturedSphereReal ×ˢ univ))
    (hJt : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x ∈ K, ω.Tames (J z x))
    (hJ' : ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap)
      (thricePuncturedSphereReal ×ˢ univ))
    (hJ't : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x ∈ K, ω.Tames (J' z x)) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω Ω' : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄
      ⦃Jk : ℕ → ℝ × ℝ → V → AlmostComplexStructure V⦄ ⦃E : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R →
      IsOpen Ω' → Ω' ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R →
      (∀ k, 4 < L k) → (∀ k, 2 * R + 2 ≤ L k) →
      (∀ k, ContDiffOn ℝ 3 (u k) {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1}) →
      (∀ k, ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1},
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk k z (u k z)) (ω.perturbedFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, ∀ z ∈ Ω, Jk k z = J z) →
      (∀ k, ∀ w ∈ Ω', Jk k (realChart (q.plumbingMap (L k)) w) = J' w) →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x I)
          (u k) z) ≤ E) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, MapsTo (u k ∘ realChart (q.plumbingMap (L k))) Ω' K) →
      ∃ (φ : ℕ → ℕ) (Z Z' : Finset (ℝ × ℝ)) (v v' : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧ ↑Z' ⊆ Ω' ∧ Z'.card * δ ≤ E ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) ∧
        ContinuousOn v' (Ω' \ ↑Z') ∧ MapsTo v' (Ω' \ ↑Z') K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n) ∘ realChart (q.plumbingMap (L (φ n)))) v'
          atTop (Ω' \ ↑Z') := by
  have hTS := preimage_truncation_subset_thricePuncturedSphereReal R
  have hS : IsOpen (thricePuncturedSphereReal ×ˢ (univ : Set V)) :=
    isOpen_thricePuncturedSphereReal.prod isOpen_univ
  have hTK := prod_mono hTS (subset_univ K)
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hS
    (contDiffOn_uncurry_pairOfPantsPerturbation hHb (fun r ↦ (hHbs r).of_le (by norm_num)) 1)
    (contDiffOn_uncurry_pairOfPantsPerturbation hHb (fun r ↦ (hHbs r).of_le (by norm_num)) I) hJ
    (isCompact_preimage_truncation R) hK hTK hJt
  obtain ⟨δ', hδ', hconv'⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hS
    (contDiffOn_uncurry_pairOfPantsPerturbation hHa (fun r ↦ (hHas r).of_le (by norm_num)) 1)
    (contDiffOn_uncurry_pairOfPantsPerturbation hHa (fun r ↦ (hHas r).of_le (by norm_num)) I) hJ'
    (isCompact_preimage_truncation R) hK hTK hJ't
  refine ⟨min δ δ', lt_min hδ hδ', fun Ω Ω' L u Jk E hΩ hΩT hΩ' hΩ'T hL4 hLR hu hfl hJΩ hJΩ' hE
    huK huK' ↦ ?_⟩
  -- Compactness on the receiving pair of pants, then on the inserted one along the subsequence.
  choose hub hflb hintb hEb using fun k ↦ receiving_piece ω hq hHb hHbs hab (hL4 k) (hLR k)
    hΩ hΩT (hu k) (hfl k) (hJΩ k) (hE k)
  choose hua hfla hinta hEa using fun k ↦ inserted_piece ω hq hHa hHb hHas hHbs hab (hL4 k)
    (hLR k) hΩ' hΩ'T (hu k) (hfl k) (hJΩ' k) (hE k)
  obtain ⟨φ, Z, v, hφ, hZΩ, hZE, -, -, hvc, hvK, hlim⟩ := hconv hΩ hΩT hub hflb huK hintb hEb
  obtain ⟨φ', Z', v', hφ', hZΩ', hZE', -, -, hvc', hvK', hlim'⟩ := hconv' hΩ' hΩ'T
    (fun n ↦ hua (φ n)) (fun n ↦ hfla (φ n)) (fun n ↦ huK' (φ n)) (fun n ↦ hinta (φ n))
    fun n ↦ hEa (φ n)
  refine ⟨φ ∘ φ', Z, Z', v, v', hφ.comp hφ', hZΩ,
    (mul_le_mul_of_nonneg_left (min_le_left δ δ') (Nat.cast_nonneg _)).trans hZE, hZΩ',
    (mul_le_mul_of_nonneg_left (min_le_right δ δ') (Nat.cast_nonneg _)).trans hZE', hvc, hvK,
    hlim.comp_tendsto hφ'.tendsto_atTop, hvc', hvK', hlim'⟩

/-- **Floer solutions on plumbed four-punctured spheres converge on both whole pieces.** Let `Ha`,
`Hb` be period-one `C³` Hamiltonians with `Hb q = Ha ∞`, `q ≠ ∞`, let `K ⊆ V` be compact, and let
`J`, `J'` be `C²` families of structures on the receiving and the inserted pair of pants `S`, read
in real coordinates, which are `ω`-tame on `S × K`. Let `uₖ` be `C³` solutions of the Floer
equation of the plumbed perturbation on the four-punctured spheres `Σ_{Lₖ}`, with `Lₖ > 4` and
`Lₖ → ∞`, for structures `Jₖ` which agree with `J` on the truncation `S_{(Lₖ - 2)/2}` and with
`J' ∘ ψ_{Lₖ}⁻¹` on its image under the plumbing map `ψ_{Lₖ}`, as the plumbed structure does. Suppose
that `uₖ(Σ_{Lₖ}) ⊆ K` and that the Floer energy of `uₖ` is at most `E`. Then there are a
subsequence `φ`, sets `Z, Z' ⊆ S` meeting every compact subset of `S` in finitely many points, and
continuous maps `v : S \ Z → K` and `v' : S \ Z' → K` such that along `φ` the maps `uₖ` converge to
`v` locally uniformly on `S \ Z`, and the maps `uₖ ∘ ψ_{Lₖ}` on the inserted pair of pants
converge to `v'` locally uniformly on `S \ Z'`. -/
theorem exists_tendstoLocallyUniformlyOn_subseq_off_discrete_plumbedPerturbation
    (ω : SymplecticForm V) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1) (hHas : ∀ r, ContDiff ℝ 3 (uncurry (Ha r)))
    (hHbs : ∀ r, ContDiff ℝ 3 (uncurry (Hb r))) (hab : Hb q = Ha inf)
    {K : Set V} (hK : IsCompact K) {J J' : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (thricePuncturedSphereReal ×ˢ univ))
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x ∈ K, ω.Tames (J z x))
    (hJ' : ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J' p.1 p.2).toLinearMap.toContinuousLinearMap)
      (thricePuncturedSphereReal ×ˢ univ))
    (hJ't : ∀ z ∈ thricePuncturedSphereReal, ∀ x ∈ K, ω.Tames (J' z x))
    {L : ℕ → ℝ} {u : ℕ → ℝ × ℝ → V} {Jk : ℕ → ℝ × ℝ → V → AlmostComplexStructure V} {E : ℝ≥0}
    (hL4 : ∀ k, 4 < L k) (hL : Tendsto L atTop atTop)
    (hu : ∀ k, ContDiffOn ℝ 3 (u k) {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1})
    (hfl : ∀ k, ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk k z (u k z)) (ω.perturbedFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x I)
        (u k) z : ℝ × ℝ →ₗ[ℝ] V))
    (hJΩ : ∀ k, ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation ((L k - 2) / 2),
      Jk k z = J z)
    (hJΩ' : ∀ k, ∀ w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation ((L k - 2) / 2),
      Jk k (realChart (q.plumbingMap (L k)) w) = J' w)
    (hE : ∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x I)
        (u k) z) ≤ E)
    (huK : ∀ k, MapsTo (u k) {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1} K) :
    ∃ (φ : ℕ → ℕ) (Z Z' : Set (ℝ × ℝ)) (v v' : ℝ × ℝ → V), StrictMono φ ∧
      Z ⊆ thricePuncturedSphereReal ∧
      (∀ C, IsCompact C → C ⊆ thricePuncturedSphereReal → (Z ∩ C).Finite) ∧
      Z' ⊆ thricePuncturedSphereReal ∧
      (∀ C, IsCompact C → C ⊆ thricePuncturedSphereReal → (Z' ∩ C).Finite) ∧
      ContinuousOn v (thricePuncturedSphereReal \ Z) ∧ MapsTo v (thricePuncturedSphereReal \ Z) K ∧
      TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (thricePuncturedSphereReal \ Z) ∧
      ContinuousOn v' (thricePuncturedSphereReal \ Z') ∧
      MapsTo v' (thricePuncturedSphereReal \ Z') K ∧
      TendstoLocallyUniformlyOn (fun n ↦ u (φ n) ∘ realChart (q.plumbingMap (L (φ n)))) v'
        atTop (thricePuncturedSphereReal \ Z') := by
  have hS : IsOpen (thricePuncturedSphereReal ×ˢ (univ : Set V)) :=
    isOpen_thricePuncturedSphereReal.prod isOpen_univ
  -- The pieces are exhausted by the interiors of the truncations `S_{(Lₖ - 2)/2}`.
  obtain ⟨hU, hUT, hUS, hUC, hLR⟩ := exhaustion_interior_truncation hL
  choose hub hflb hintb hEb using fun k ↦ receiving_piece ω hq hHb hHbs hab (hL4 k) (hLR k)
    (hU k) (hUT k) (hu k) (hfl k) (fun z hz ↦ hJΩ k z (hUT k hz)) (hE k)
  choose hua hfla hinta hEa using fun k ↦ inserted_piece ω hq hHa hHb hHas hHbs hab (hL4 k)
    (hLR k) (hU k) (hUT k) (hu k) (hfl k) (fun w hw ↦ hJΩ' k w (hUT k hw)) (hE k)
  -- Compactness on the receiving pair of pants, then on the inserted one along the subsequence.
  obtain ⟨φ, Z, v, hφ, hZS, hZC, -, -, hvc, hvK, hlim⟩ :=
    ω.exists_tendstoLocallyUniformlyOn_subseq_off_discrete hS
      (contDiffOn_uncurry_pairOfPantsPerturbation hHb (fun r ↦ hHbs r) 1)
      (contDiffOn_uncurry_pairOfPantsPerturbation hHb (fun r ↦ hHbs r) I) hJ
      isOpen_thricePuncturedSphereReal hK (prod_mono subset_rfl (subset_univ K)) hJt hU hUS hUC
      hub hflb (fun k ↦ (huK k).mono_left ((hUT k).trans
        (preimage_truncation_subset_plumbedSphere hq (hL4 k) (by linarith [hL4 k])).1))
      hintb (fun k ↦ hEb k)
  obtain ⟨φ', Z', v', hφ', hZS', hZC', -, -, hvc', hvK', hlim'⟩ :=
    ω.exists_tendstoLocallyUniformlyOn_subseq_off_discrete hS
      (contDiffOn_uncurry_pairOfPantsPerturbation hHa (fun r ↦ hHas r) 1)
      (contDiffOn_uncurry_pairOfPantsPerturbation hHa (fun r ↦ hHas r) I) hJ'
      isOpen_thricePuncturedSphereReal hK (prod_mono subset_rfl (subset_univ K)) hJ't
      (fun n ↦ hU (φ n)) (fun n ↦ hUS (φ n))
      (fun C hC hCS ↦ hφ.tendsto_atTop.eventually (hUC C hC hCS)) (fun n ↦ hua (φ n))
      (fun n ↦ hfla (φ n))
      (fun n ↦ (huK (φ n)).comp ((preimage_truncation_subset_plumbedSphere hq (hL4 (φ n))
        (by linarith [hL4 (φ n)])).2.mono_left (hUT (φ n))))
      (fun n ↦ hinta (φ n)) fun n ↦ hEa (φ n)
  refine ⟨φ ∘ φ', Z, Z', v, v', hφ.comp hφ', hZS, hZC, hZS', hZC', hvc, hvK,
    hlim.comp_tendsto hφ'.tendsto_atTop, hvc', hvK', hlim'⟩

end TauCeti.SymplecticForm

open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open Floer TauCeti.MeasureTheory

variable {E G M V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
  [IsManifold I ⊤ M] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {ω : SmoothTwoForm I M} {ω₀ : SymplecticForm V} {Ha Hb : Puncture → ℝ → M → ℝ} {q : Puncture}

/-- The truncations for a neck length `L > 4` with `L ≥ 2R + 2`: the truncation `S_R` lies in the
truncation `S_{max R 0}` at a nonnegative height, which lies in the plumbed four-punctured sphere
`Σ_L` and is carried into `Σ_L` by the plumbing map `ψ_L`. -/
private theorem preimage_truncation_max_subset_plumbedSphere (hq : q ≠ inf) {R L : ℝ} (hL : 4 < L)
    (hLR : 2 * R + 2 ≤ L) :
    Complex.equivRealProdCLM.symm ⁻¹' truncation R ⊆
        Complex.equivRealProdCLM.symm ⁻¹' truncation (max R 0) ∧
      Complex.equivRealProdCLM.symm ⁻¹' truncation (max R 0) ⊆ {z : ℝ × ℝ |
        (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} ∧
      MapsTo (realChart (q.plumbingMap L)) (Complex.equivRealProdCLM.symm ⁻¹' truncation (max R 0))
        {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧ Complex.equivRealProdCLM.symm z ≠ 1) ∧
          Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1} := by
  exact ⟨preimage_mono (truncation_mono (le_max_left R 0)),
    preimage_truncation_subset_plumbedSphere hq hL (max_le (by linarith) (by linarith))⟩

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **The receiving piece.** Let `u` be a `C³` solution of the Floer equation of the plumbed
perturbation on the four-punctured sphere `Σ_L`, `L > 4`, with Floer energy at most `E`. On an
open subset `Ω` of the truncation `S_R` of the receiving pair of pants, `L ≥ 2R + 2`, it is a `C³`
solution of the Floer equation of the receiving pair of pants, with integrable energy density
and energy at most `E` over `Ω`. -/
private theorem floer_restrict_receiving (hω : ω.IsNondegenerate) (hq : q ≠ inf)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Hb r))) (hab : Hb q = Ha inf)
    {R L : ℝ} (hL : 4 < L) (hLR : 2 * R + 2 ≤ L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {Jk : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hfl : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk z (u z)) (ω.perturbedMFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap) {E : ℝ≥0}
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) ≤ E) {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω)
    (hΩT : Ω ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω ∧
      (∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk z (u z))
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
          u z).toLinearMap) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I) u)
        Ω ∧
      ∫ z in Ω, ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z ≤ E := by
  -- The truncation `S_{max R 0}` lies in `Σ_L`.
  obtain ⟨hTT₀, hTP, -⟩ := preimage_truncation_max_subset_plumbedSphere hq hL hLR
  -- On `S_R` the plumbed datum is the datum of the receiving pair of pants.
  have hK {z : ℝ × ℝ} (hz : z ∈ Ω) (v : ℂ) :
      (fun x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x v) =
        fun x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x v :=
    funext fun x ↦ DFunLike.congr_fun
      (plumbedPerturbation_eq_pairOfPantsPerturbation_of_mem_truncation hq hab (by linarith)
        (hΩT hz) x) v
  have hD {z : ℝ × ℝ} (hz : z ∈ Ω) : ω.perturbedMFDeriv
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z := by
    refine ContinuousLinearMap.ext fun v ↦ ?_
    rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply, hK hz 1, hK hz Complex.I]
  refine ⟨hu.mono fun z hz ↦ hTP (hTT₀ (hΩT hz)), fun z hz ↦ hD hz ▸ hfl z (hTP (hTT₀ (hΩT hz))),
    (hω.integrableOn_floerEnergyDensity_pairOfPantsPerturbation_truncationAt hHb
      (fun r ↦ (hHbs r).of_le (by norm_num)) (fun _ ↦ le_max_right R 0)
      (isOpen_plumbedSphere q L) (by rwa [truncationAt_const]) (hu.of_le (by norm_num))).mono_set
      (by rw [truncationAt_const]; exact hΩT.trans hTT₀), ?_⟩
  have hdens {z : ℝ × ℝ} (hz : z ∈ Ω) : ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z := by
    rw [floerEnergyDensity_def, floerEnergyDensity_def, hD hz]
  rw [setIntegral_congr_fun hΩ.measurableSet fun z hz ↦ hdens hz]
  exact setIntegral_le_of_lintegral_ofReal_le hE _

omit [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] in
/-- **The inserted piece.** Let `u` be a `C³` solution of the Floer equation of the plumbed
perturbation on the four-punctured sphere `Σ_L`, `L > 4`, with Floer energy at most `E`. On an
open subset `Ω'` of the truncation `S_R` of the inserted pair of pants, `L ≥ 2R + 2`, the map
`u ∘ ψ_L` is a `C³` solution of the Floer equation of the inserted pair of pants, for the
structures `Jk ∘ ψ_L`, with integrable energy density and energy at most `E` over `Ω'`. -/
private theorem floer_comp_plumbingMap_inserted (hω : ω.IsNondegenerate) (hq : q ≠ inf)
    (hHa : ∀ r, Periodic (Ha r) 1) (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Hb r))) (hab : Hb q = Ha inf)
    {R L : ℝ} (hL : 4 < L) (hLR : 2 * R + 2 ≤ L) {u : ℝ × ℝ → M}
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1})
    {Jk : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hfl : ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap L 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk z (u z)) (ω.perturbedMFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u z).toLinearMap) {E : ℝ≥0}
    (hE : ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ plumbedPerturbation Ha Hb q L (Complex.equivRealProdCLM.symm z) x Complex.I)
      u z) ≤ E) {Ω' : Set (ℝ × ℝ)} (hΩ' : IsOpen Ω')
    (hΩ'T : Ω' ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u ∘ realChart (q.plumbingMap L)) Ω' ∧
      (∀ w ∈ Ω', IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (Jk (realChart (q.plumbingMap L) w) (u (realChart (q.plumbingMap L) w)))
        (ω.perturbedMFDeriv
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
          (u ∘ realChart (q.plumbingMap L)) w).toLinearMap) ∧
      IntegrableOn (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.plumbingMap L))) Ω' ∧
      ∫ w in Ω', ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
        (u ∘ realChart (q.plumbingMap L)) w ≤ E := by
  -- The plumbing chart carries the truncation `S_{max R 0}` into `Σ_L`.
  obtain ⟨hTT₀, -, hψP⟩ := preimage_truncation_max_subset_plumbedSphere hq hL hLR
  have hψ : ContDiff ℝ 3 (realChart (q.plumbingMap L)) := contDiff_realChart_plumbingMap q L
  have hua := hu.comp hψ.contMDiff.contMDiffOn (mapsTo_preimage _ _)
  refine ⟨hua.mono fun w hw ↦ hψP (hTT₀ (hΩ'T hw)), fun w hw ↦
    ω.isComplexLinearMap_perturbedMFDeriv_comp_realChart_plumbingMap hq hHa hHb
      (fun r ↦ (hHas r).of_le (by norm_num)) (fun r ↦ (hHbs r).of_le (by norm_num)) hab hL
      (mem_thricePuncturedSphereReal_iff.1
        (preimage_truncation_subset_thricePuncturedSphereReal R (hΩ'T hw)))
      (by linarith [(mem_truncation.1 (hΩ'T hw)).2.2 inf])
      (((hu.contMDiffAt ((isOpen_plumbedSphere q L).mem_nhds
        (hψP (hTT₀ (hΩ'T hw))))).mdifferentiableAt (by norm_num)))
      (hfl _ (hψP (hTT₀ (hΩ'T hw)))),
    (hω.integrableOn_floerEnergyDensity_pairOfPantsPerturbation_truncationAt hHa
      (fun r ↦ (hHas r).of_le (by norm_num)) (fun _ ↦ le_max_right R 0)
      ((isOpen_plumbedSphere q L).preimage hψ.continuous) (by rwa [truncationAt_const])
      (hua.of_le (by norm_num))).mono_set (by rw [truncationAt_const]; exact hΩ'T.trans hTT₀), ?_⟩
  -- The energy of `u ∘ ψ_L` over `Ω'` is the energy of `u` over `ψ_L(Ω')`.
  rw [← ω.integral_floerEnergyDensity_plumbedPerturbation_inserted hq hHa hHb
    (fun r ↦ (hHas r).of_le (by norm_num)) (fun r ↦ (hHbs r).of_le (by norm_num)) hab hL
    (hu.of_le (by norm_num)) hΩ'.measurableSet fun w hw ↦
      ⟨preimage_truncation_subset_thricePuncturedSphereReal R (hΩ'T hw), by
        linarith [(mem_truncation.1 (hΩ'T hw)).2.2 inf]⟩]
  exact setIntegral_le_of_lintegral_ofReal_le hE _

/-- **Floer solutions on plumbed four-punctured spheres in a manifold converge on both pieces.**
Let `ω` be a nondegenerate two-form on `M`, let `Ha`, `Hb` be period-one `C³` Hamiltonians on `M`
with `Hb q = Ha ∞`, `q ≠ ∞`, and fix a truncation `S_R`. Let `φ` and `φ'` be smooth partial
diffeomorphisms from `M` onto open subsets of `V` pulling the symplectic form `ω₀` back to `ω` on
compact sets `K ⊆ φ.source` and `K' ⊆ φ'.source`, such as Darboux charts, and let `J`, `J'` be
families of structures on the tangent spaces of `M` over the receiving and the inserted pair of
pants, tamed by `ω` over `S_R × K` and `S_R × K'`, read in the charts by families `Jφ`, `Jφ'`
which are `C²` on open sets containing `S_R × φ(K)` and `S_R × φ'(K')`. There is a threshold
`δ > 0` with the following property. Let `uₖ` be `C³` solutions of the Floer equation
`(du - X_K)^{0,1} = 0` of the plumbed perturbation `K` on the four-punctured spheres `Σ_{Lₖ}`,
with neck lengths `Lₖ > 4` and `Lₖ ≥ 2R + 2`, for structures `Jₖ(z, u)`, and with Floer energy at
most `E`. Let `Ω` and `Ω'` be open subsets of `S_R`, on which `Jₖ = J` and `Jₖ ∘ ψ_{Lₖ} = J'`
respectively, with `uₖ(Ω) ⊆ K` and `uₖ(ψ_{Lₖ}(Ω')) ⊆ K'`. Then there are a subsequence `σ`,
finite sets `Z ⊆ Ω` and `Z' ⊆ Ω'` with `#Z * δ ≤ E` and `#Z' * δ ≤ E`, and maps `v`, `v'`,
continuous on `Ω \ Z` and `Ω' \ Z'` with values in `K` and `K'`, such that along `σ` the
coordinate maps `φ ∘ uₖ` converge to `φ ∘ v` locally uniformly on `Ω \ Z` and `uₖ → v` pointwise
there, and on the inserted pair of pants the coordinate maps `φ' ∘ uₖ ∘ ψ_{Lₖ}` converge to
`φ' ∘ v'` locally uniformly on `Ω' \ Z'` and `uₖ ∘ ψ_{Lₖ} → v'` pointwise there. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_plumbedPerturbation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Hb r))) (hab : Hb q = Ha inf)
    (R : ℝ) (φ φ' : PartialDiffeomorph I 𝓘(ℝ, V) M V (⊤ : ℕ∞)) {K K' : Set M}
    {J J' : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Jφ Jφ' : ℝ × ℝ → V → AlmostComplexStructure V} {W W' : Set ((ℝ × ℝ) × V)}
    (hφ : ∀ x ∈ K, ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ x v) (mvfderiv I φ x w))
    (hφ' : ∀ x ∈ K', ∀ v w : TangentSpace I x,
      ω.eval₂ x v w = ω₀ (mvfderiv I φ' x v) (mvfderiv I φ' x w))
    (hJJ : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x ∈ K,
      IsComplexLinearMap (J z x) (Jφ z (φ x)) (mvfderiv I φ x).toLinearMap)
    (hJJ' : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x ∈ K',
      IsComplexLinearMap (J' z x) (Jφ' z (φ' x)) (mvfderiv I φ' x).toLinearMap)
    (hW : IsOpen W) (hW' : IsOpen W')
    (hJφ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (Jφ p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hJφ' : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (Jφ' p.1 p.2).toLinearMap.toContinuousLinearMap) W')
    (hK : IsCompact K) (hK' : IsCompact K') (hKφ : K ⊆ φ.source) (hKφ' : K' ⊆ φ'.source)
    (hTKW : (Complex.equivRealProdCLM.symm ⁻¹' truncation R) ×ˢ (φ '' K) ⊆ W)
    (hTKW' : (Complex.equivRealProdCLM.symm ⁻¹' truncation R) ×ˢ (φ' '' K') ⊆ W')
    (hJt : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x ∈ K,
      (hω.symplecticFormAt x).Tames (J z x))
    (hJ't : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x ∈ K',
      (hω.symplecticFormAt x).Tames (J' z x)) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω Ω' : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄
      ⦃Jk : ℕ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)⦄ ⦃E : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R →
      IsOpen Ω' → Ω' ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R →
      (∀ k, 4 < L k) → (∀ k, 2 * R + 2 ≤ L k) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1}) →
      (∀ k, ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1},
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk k z (u k z)) (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, ∀ z ∈ Ω, Jk k z = J z) →
      (∀ k, ∀ w ∈ Ω', Jk k (realChart (q.plumbingMap (L k)) w) = J' w) →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          (u k) z) ≤ E) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, MapsTo (u k ∘ realChart (q.plumbingMap (L k))) Ω' K') →
      ∃ (σ : ℕ → ℕ) (Z Z' : Finset (ℝ × ℝ)) (v v' : ℝ × ℝ → M), StrictMono σ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧ ↑Z' ⊆ Ω' ∧ Z'.card * δ ≤ E ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ ∘ u (σ n)) (φ ∘ v) atTop (Ω \ ↑Z) ∧
        (∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (σ n) y) atTop (𝓝 (v y))) ∧
        ContinuousOn v' (Ω' \ ↑Z') ∧ MapsTo v' (Ω' \ ↑Z') K' ∧
        TendstoLocallyUniformlyOn (fun n ↦ φ' ∘ (u (σ n) ∘ realChart (q.plumbingMap (L (σ n)))))
          (φ' ∘ v') atTop (Ω' \ ↑Z') ∧
        ∀ y ∈ Ω' \ ↑Z', Tendsto (fun n ↦ u (σ n) (realChart (q.plumbingMap (L (σ n))) y)) atTop
          (𝓝 (v' y)) := by
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  have hTS : T ⊆ thricePuncturedSphereReal := preimage_truncation_subset_thricePuncturedSphereReal R
  -- The thresholds of the chart compactness theorem for the two pairs of pants.
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPants_of_setIntegral_le
      φ hHb hHbs hφ hJJ hW hJφ (isCompact_preimage_truncation R) hTS hK hKφ hTKW hJt
  obtain ⟨δ', hδ', hconv'⟩ :=
    hω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPants_of_setIntegral_le
      φ' hHa hHas hφ' hJJ' hW' hJφ' (isCompact_preimage_truncation R) hTS hK' hKφ' hTKW' hJ't
  refine ⟨min δ δ', lt_min hδ hδ', fun Ω Ω' L u Jk E hΩ hΩT hΩ' hΩ'T hL4 hLR hu hfl hJΩ hJΩ' hE
    huK huK' ↦ ?_⟩
  -- Restricted to each piece, the solutions solve the Floer equation of that pair of pants.
  have hb (k : ℕ) := floer_restrict_receiving hω hq hHb hHbs hab (hL4 k) (hLR k) (hu k) (hfl k)
    (hE k) hΩ hΩT
  have ha (k : ℕ) := floer_comp_plumbingMap_inserted hω hq hHa hHb hHas hHbs hab (hL4 k) (hLR k)
    (hu k) (hfl k) (hE k) hΩ' hΩ'T
  -- Compactness on the receiving pair of pants, then on the inserted one along the subsequence.
  obtain ⟨σ, Z, v, hσ, hZΩ, hZE, -, -, hvc, hvK, hlim, hpt⟩ := hconv hΩ hΩT (fun k ↦ (hb k).1)
    (fun k z hz ↦ hJΩ k z hz ▸ (hb k).2.1 z hz) huK (fun k ↦ (hb k).2.2.1) fun k ↦ (hb k).2.2.2
  obtain ⟨σ', Z', v', hσ', hZΩ', hZE', -, -, hvc', hvK', hlim', hpt'⟩ := hconv' hΩ' hΩ'T
    (fun n ↦ (ha (σ n)).1) (fun n w hw ↦ hJΩ' (σ n) w hw ▸ (ha (σ n)).2.1 w hw)
    (fun n ↦ huK' (σ n)) (fun n ↦ (ha (σ n)).2.2.1) fun n ↦ (ha (σ n)).2.2.2
  refine ⟨σ ∘ σ', Z, Z', v, v', hσ.comp hσ', hZΩ,
    (mul_le_mul_of_nonneg_left (min_le_left δ δ') (Nat.cast_nonneg _)).trans hZE, hZΩ',
    (mul_le_mul_of_nonneg_left (min_le_right δ δ') (Nat.cast_nonneg _)).trans hZE', hvc, hvK,
    hlim.comp_tendsto hσ'.tendsto_atTop,
    fun y hy ↦ (hpt y hy).comp hσ'.tendsto_atTop, hvc', hvK', hlim', hpt'⟩

section Closed

variable [I.Boundaryless] [CompactSpace M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **Floer solutions on plumbed four-punctured spheres in a closed manifold converge on both
pieces.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, let `Ha`, `Hb` be
period-one `C³` Hamiltonians on `M` with `Hb q = Ha ∞`, `q ≠ ∞`, and fix a truncation `S_R`. Let
`J`, `J'` be structures on the tangent spaces of `M` over the receiving and the inserted pair of
pants, `C²` read in the chart at every point of `M` and tamed by `ω` over `S_R`. Let `e : M → F` be
injective and differentiable, such as the Whitney embedding, with `J` and `J'` uniformly tame with
respect to `e` over `S_R`, `c ‖d e v‖² ≤ ω(v, J v)` with `c > 0`, and the pushforwards through `e`
of the Hamiltonian vector fields of the components of both pair-of-pants perturbations at most `B`
over `S_R`. There is a threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions
of the Floer equation `(du - X_K)^{0,1} = 0` of the plumbed perturbation `K` on the four-punctured
spheres `Σ_{Lₖ}`, with neck lengths `Lₖ > 4` and `Lₖ ≥ 2R + 2`, for structures `Jₖ(z, u)`, and
with Floer energy at most `E`. Let `Ω` and `Ω'` be open subsets of `S_R`, on which `Jₖ = J` and
`Jₖ ∘ ψ_{Lₖ} = J'` respectively. Then there are a subsequence `σ`, finite sets `Z ⊆ Ω` and
`Z' ⊆ Ω'` with `#Z * δ ≤ E` and `#Z' * δ ≤ E`, and maps `v`, `v'`, continuous on `Ω \ Z` and
`Ω' \ Z'`, such that along `σ`

* every disc about a point of `Z` eventually carries energy at least `δ` for `uₖ` on the receiving
  pair of pants, and every disc about a point of `Z'` for `uₖ ∘ ψ_{Lₖ}` on the inserted one;
* `uₖ → v` on `Ω \ Z` and `uₖ ∘ ψ_{Lₖ} → v'` on `Ω' \ Z'`, locally uniformly after applying `e`
  and pointwise in `M`.

Unlike `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_plumbedPerturbation`, no
condition is put on the images of the solutions. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset_plumbedPerturbation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Hb r))) (hab : Hb q = Ha inf)
    (R : ℝ) {J J' : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J)
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target))
    (hJ' : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J')
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x,
      (hω.symplecticFormAt x).Tames (J z x))
    (hJ't : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x,
      (hω.symplecticFormAt x).Tames (J' z x))
    {e : M → F} (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e) {c B : ℝ}
    (hc : 0 < c)
    (hJc : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hJ'c : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J' z x v))
    (hBb : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x,
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) y 1) x)‖ ≤ B ∧
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) y Complex.I) x)‖ ≤
        B)
    (hBa : ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation R, ∀ x,
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) y 1) x)‖ ≤ B ∧
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) y Complex.I) x)‖ ≤
        B) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω Ω' : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → M⦄
      ⦃Jk : ℕ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)⦄ ⦃E : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R →
      IsOpen Ω' → Ω' ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation R →
      (∀ k, 4 < L k) → (∀ k, 2 * R + 2 ≤ L k) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1}) →
      (∀ k, ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
        Complex.equivRealProdCLM.symm z ≠ 1) ∧
        Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1},
        IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk k z (u k z)) (ω.perturbedMFDeriv
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          (u k) z).toLinearMap) →
      (∀ k, ∀ z ∈ Ω, Jk k z = J z) →
      (∀ k, ∀ w ∈ Ω', Jk k (realChart (q.plumbingMap (L k)) w) = J' w) →
      (∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x
            Complex.I)
          (u k) z) ≤ E) →
      ∃ (σ : ℕ → ℕ) (Z Z' : Finset (ℝ × ℝ)) (v v' : ℝ × ℝ → M), StrictMono σ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧ ↑Z' ⊆ Ω' ∧ Z'.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x Complex.I)
          (u (σ n)) y) ∧
        (∀ z ∈ Z', ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω', ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x Complex.I)
          (u (σ n) ∘ realChart (q.plumbingMap (L (σ n)))) y) ∧
        ContinuousOn v (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (σ n)) (e ∘ v) atTop (Ω \ ↑Z) ∧
        (∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (σ n) y) atTop (𝓝 (v y))) ∧
        ContinuousOn v' (Ω' \ ↑Z') ∧
        TendstoLocallyUniformlyOn (fun n ↦ e ∘ (u (σ n) ∘ realChart (q.plumbingMap (L (σ n)))))
          (e ∘ v') atTop (Ω' \ ↑Z') ∧
        ∀ y ∈ Ω' \ ↑Z', Tendsto (fun n ↦ u (σ n) (realChart (q.plumbingMap (L (σ n))) y)) atTop
          (𝓝 (v' y)) := by
  have hTS := preimage_truncation_subset_thricePuncturedSphereReal R
  -- The thresholds of the closed-manifold compactness theorem for the two pairs of pants.
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    he he_inj isOpen_thricePuncturedSphereReal (isCompact_preimage_truncation R) hTS hJ
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt
      (contMDiffAt_uncurry_pairOfPantsPerturbation_apply hHb hHbs 1))
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt
      (contMDiffAt_uncurry_pairOfPantsPerturbation_apply hHb hHbs Complex.I)) hJt hc hJc
    (fun z hz x ↦ (hBb z hz x).1) fun z hz x ↦ (hBb z hz x).2
  obtain ⟨δ', hδ', hconv'⟩ := hω.exists_pos_forall_tendstoLocallyUniformlyOn_comp_subseq_off_finset
    he he_inj isOpen_thricePuncturedSphereReal (isCompact_preimage_truncation R) hTS hJ'
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt
      (contMDiffAt_uncurry_pairOfPantsPerturbation_apply hHa hHas 1))
    (hω.contDiffOn_hamiltonianVectorFieldInChartAt
      (contMDiffAt_uncurry_pairOfPantsPerturbation_apply hHa hHas Complex.I)) hJ't hc hJ'c
    (fun z hz x ↦ (hBa z hz x).1) fun z hz x ↦ (hBa z hz x).2
  refine ⟨min δ δ', lt_min hδ hδ', fun Ω Ω' L u Jk E hΩ hΩT hΩ' hΩ'T hL4 hLR hu hfl hJΩ hJΩ' hE ↦
    ?_⟩
  -- Restricted to each piece, the solutions solve the Floer equation of that pair of pants.
  have hb (k : ℕ) := floer_restrict_receiving hω hq hHb hHbs hab (hL4 k) (hLR k) (hu k) (hfl k)
    (hE k) hΩ hΩT
  have ha (k : ℕ) := floer_comp_plumbingMap_inserted hω hq hHa hHb hHas hHbs hab (hL4 k) (hLR k)
    (hu k) (hfl k) (hE k) hΩ' hΩ'T
  -- Compactness on the receiving pair of pants, then on the inserted one along the subsequence.
  obtain ⟨σ, hσ, Z, hZΩ, hZE, hZ, -, v, hvc, hlim, hpt⟩ := hconv hΩ hΩT (fun k ↦ (hb k).1)
    (fun k z hz ↦ hJΩ k z hz ▸ (hb k).2.1 z hz) (fun k ↦ (hb k).2.2.1) fun k ↦ (hb k).2.2.2
  obtain ⟨σ', hσ', Z', hZΩ', hZE', hZ', -, v', hvc', hlim', hpt'⟩ := hconv' hΩ' hΩ'T
    (fun n ↦ (ha (σ n)).1) (fun n w hw ↦ hJΩ' (σ n) w hw ▸ (ha (σ n)).2.1 w hw)
    (fun n ↦ (ha (σ n)).2.2.1) fun n ↦ (ha (σ n)).2.2.2
  refine ⟨σ ∘ σ', Z, Z', v, v', hσ.comp hσ', hZΩ,
    (mul_le_mul_of_nonneg_left (min_le_left δ δ') (Nat.cast_nonneg _)).trans hZE, hZΩ',
    (mul_le_mul_of_nonneg_left (min_le_right δ δ') (Nat.cast_nonneg _)).trans hZE',
    fun z hz ε hε ↦ (hσ'.tendsto_atTop.eventually (hZ z hz ε hε)).mono fun _ h ↦
      (min_le_left δ δ').trans h,
    fun z hz ε hε ↦ (hZ' z hz ε hε).mono fun _ h ↦ (min_le_right δ δ').trans h, hvc,
    hlim.comp_tendsto hσ'.tendsto_atTop, fun y hy ↦ (hpt y hy).comp hσ'.tendsto_atTop, hvc',
    hlim', hpt'⟩

/-- **Floer solutions on plumbed four-punctured spheres in a closed manifold converge on both whole
pieces.** Let `ω` be a nondegenerate two-form on a closed manifold `M`, let `Ha`, `Hb` be
period-one `C³` Hamiltonians on `M` with `Hb q = Ha ∞`, `q ≠ ∞`, and let `J`, `J'` be structures
on the tangent spaces of `M` over the receiving and the inserted pair of pants `S`, `C²` read in
the chart at every point of `M` and tamed by `ω` over `S`. Let `e : M → F` be injective and
differentiable, such as the Whitney embedding, and over each compact subset of `S` let `J` and `J'`
be uniformly tame with respect to `e` and the pushforwards through `e` of the Hamiltonian vector
fields of the components of both pair-of-pants perturbations be bounded. Let `uₖ` be `C³`
solutions of the Floer equation of the plumbed perturbation on the four-punctured spheres
`Σ_{Lₖ}`, with `Lₖ > 4` and `Lₖ → ∞`, for structures `Jₖ` which agree with `J` on the truncation
`S_{(Lₖ - 2)/2}` and with `J' ∘ ψ_{Lₖ}⁻¹` on its image under the plumbing map `ψ_{Lₖ}`, as the
plumbed structure does, and with Floer energy at most `E`. Then there are a subsequence `σ`, sets
`Z, Z' ⊆ S` meeting every compact subset of `S` in finitely many points, and maps `v`, `v'`,
continuous on `S \ Z` and `S \ Z'`, such that along `σ` the maps `uₖ` converge to `v` on `S \ Z`,
and the maps `uₖ ∘ ψ_{Lₖ}` on the inserted pair of pants converge to `v'` on `S \ Z'`, locally
uniformly after applying `e` and pointwise in `M`. No condition is put on the images of the
solutions. -/
theorem exists_tendstoLocallyUniformlyOn_comp_subseq_off_discrete_plumbedPerturbation
    (hω : ω.IsNondegenerate) (hq : q ≠ inf) (hHa : ∀ r, Periodic (Ha r) 1)
    (hHb : ∀ r, Periodic (Hb r) 1)
    (hHas : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Ha r)))
    (hHbs : ∀ r, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 3 (uncurry (Hb r))) (hab : Hb q = Ha inf)
    {J J' : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    (hJ : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J)
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target))
    (hJ' : ∀ α, ContDiffOn ℝ 2 (almostComplexInChartAt I α J')
      (thricePuncturedSphereReal ×ˢ (extChartAt I α).target))
    (hJt : ∀ z ∈ thricePuncturedSphereReal, ∀ x, (hω.symplecticFormAt x).Tames (J z x))
    (hJ't : ∀ z ∈ thricePuncturedSphereReal, ∀ x, (hω.symplecticFormAt x).Tames (J' z x))
    {e : M → F} (he : ∀ x, MDifferentiableAt I 𝓘(ℝ, F) e x) (he_inj : Injective e)
    (hJc : ∀ C, IsCompact C → C ⊆ thricePuncturedSphereReal → ∃ c > 0, ∀ z ∈ C, ∀ x v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J z x v))
    (hJ'c : ∀ C, IsCompact C → C ⊆ thricePuncturedSphereReal → ∃ c > 0, ∀ z ∈ C, ∀ x v,
      c * ‖mvfderiv I e x v‖ ^ 2 ≤ hω.symplecticFormAt x v (J' z x v))
    (hBb : ∀ C, IsCompact C → C ⊆ thricePuncturedSphereReal → ∃ B, ∀ z ∈ C, ∀ x,
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) y 1) x)‖ ≤ B ∧
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) y Complex.I) x)‖ ≤
        B)
    (hBa : ∀ C, IsCompact C → C ⊆ thricePuncturedSphereReal → ∃ B, ∀ z ∈ C, ∀ x,
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) y 1) x)‖ ≤ B ∧
      ‖mvfderiv I e x (ω.hamiltonianVectorField
        (fun y ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) y Complex.I) x)‖ ≤
        B)
    {L : ℕ → ℝ} {u : ℕ → ℝ × ℝ → M}
    {Jk : ℕ → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)} {E : ℝ≥0}
    (hL4 : ∀ k, 4 < L k) (hL : Tendsto L atTop atTop)
    (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1})
    (hfl : ∀ k, ∀ z ∈ {z : ℝ × ℝ | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
      Complex.equivRealProdCLM.symm z ≠ 1) ∧
      Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1},
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (Jk k z (u k z)) (ω.perturbedMFDeriv
        (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        (u k) z).toLinearMap)
    (hJΩ : ∀ k, ∀ z ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation ((L k - 2) / 2),
      Jk k z = J z)
    (hJΩ' : ∀ k, ∀ w ∈ Complex.equivRealProdCLM.symm ⁻¹' truncation ((L k - 2) / 2),
      Jk k (realChart (q.plumbingMap (L k)) w) = J' w)
    (hE : ∀ k, ∫⁻ z, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x
          Complex.I)
        (u k) z) ≤ E) :
    ∃ (σ : ℕ → ℕ) (Z Z' : Set (ℝ × ℝ)) (v v' : ℝ × ℝ → M), StrictMono σ ∧
      Z ⊆ thricePuncturedSphereReal ∧
      (∀ C, IsCompact C → C ⊆ thricePuncturedSphereReal → (Z ∩ C).Finite) ∧
      Z' ⊆ thricePuncturedSphereReal ∧
      (∀ C, IsCompact C → C ⊆ thricePuncturedSphereReal → (Z' ∩ C).Finite) ∧
      ContinuousOn v (thricePuncturedSphereReal \ Z) ∧
      TendstoLocallyUniformlyOn (fun n ↦ e ∘ u (σ n)) (e ∘ v) atTop
        (thricePuncturedSphereReal \ Z) ∧
      (∀ y ∈ thricePuncturedSphereReal \ Z, Tendsto (fun n ↦ u (σ n) y) atTop (𝓝 (v y))) ∧
      ContinuousOn v' (thricePuncturedSphereReal \ Z') ∧
      TendstoLocallyUniformlyOn (fun n ↦ e ∘ (u (σ n) ∘ realChart (q.plumbingMap (L (σ n)))))
        (e ∘ v') atTop (thricePuncturedSphereReal \ Z') ∧
      ∀ y ∈ thricePuncturedSphereReal \ Z',
        Tendsto (fun n ↦ u (σ n) (realChart (q.plumbingMap (L (σ n))) y)) atTop (𝓝 (v' y)) := by
  -- The pieces are exhausted by the interiors of the truncations `S_{(Lₖ - 2)/2}`.
  obtain ⟨hU, hUT, hUS, hUC, hLR⟩ := exhaustion_interior_truncation hL
  -- Restricted to each piece, the solutions solve the Floer equation of that pair of pants.
  have hb (k : ℕ) := floer_restrict_receiving hω hq hHb hHbs hab (hL4 k) (hLR k) (hu k) (hfl k)
    (hE k) (hU k) (hUT k)
  have ha (k : ℕ) := floer_comp_plumbingMap_inserted hω hq hHa hHb hHas hHbs hab (hL4 k) (hLR k)
    (hu k) (hfl k) (hE k) (hU k) (hUT k)
  -- Compactness on the receiving pair of pants, then on the inserted one along the subsequence.
  obtain ⟨σ, Z, v, hσ, hZS, hZC, -, -, hvc, hlim, hpt⟩ :=
    hω.exists_tendstoLocallyUniformlyOn_comp_subseq_off_discrete he he_inj
      isOpen_thricePuncturedSphereReal hJ
      (hω.contDiffOn_hamiltonianVectorFieldInChartAt
        (contMDiffAt_uncurry_pairOfPantsPerturbation_apply hHb hHbs 1))
      (hω.contDiffOn_hamiltonianVectorFieldInChartAt
        (contMDiffAt_uncurry_pairOfPantsPerturbation_apply hHb hHbs Complex.I)) hJt hJc
      hBb hU hUS hUC (fun k ↦ (hb k).1)
      (fun k z hz ↦ hJΩ k z (hUT k hz) ▸ (hb k).2.1 z hz) (fun k ↦ (hb k).2.2.1)
      fun k ↦ (hb k).2.2.2
  obtain ⟨σ', Z', v', hσ', hZS', hZC', -, -, hvc', hlim', hpt'⟩ :=
    hω.exists_tendstoLocallyUniformlyOn_comp_subseq_off_discrete he he_inj
      isOpen_thricePuncturedSphereReal hJ'
      (hω.contDiffOn_hamiltonianVectorFieldInChartAt
        (contMDiffAt_uncurry_pairOfPantsPerturbation_apply hHa hHas 1))
      (hω.contDiffOn_hamiltonianVectorFieldInChartAt
        (contMDiffAt_uncurry_pairOfPantsPerturbation_apply hHa hHas Complex.I)) hJ't hJ'c
      hBa (fun n ↦ hU (σ n)) (fun n ↦ hUS (σ n))
      (fun C hC hCS ↦ hσ.tendsto_atTop.eventually (hUC C hC hCS)) (fun n ↦ (ha (σ n)).1)
      (fun n w hw ↦ hJΩ' (σ n) w (hUT (σ n) hw) ▸ (ha (σ n)).2.1 w hw)
      (fun n ↦ (ha (σ n)).2.2.1) fun n ↦ (ha (σ n)).2.2.2
  refine ⟨σ ∘ σ', Z, Z', v, v', hσ.comp hσ', hZS, hZC, hZS', hZC', hvc,
    hlim.comp_tendsto hσ'.tendsto_atTop, fun y hy ↦ (hpt y hy).comp hσ'.tendsto_atTop, hvc',
    hlim', hpt'⟩

end Closed

end TauCeti.SmoothTwoForm.IsNondegenerate
