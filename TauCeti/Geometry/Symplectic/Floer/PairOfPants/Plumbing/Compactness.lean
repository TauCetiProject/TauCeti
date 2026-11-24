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
Gromov–Floer compactness at that end, for a symplectic vector space target `(V, ω)` and, through
symplectic charts, for a manifold target with a nondegenerate two-form (see the paragraph on
manifold targets below).

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
When `Lₖ → ∞` every compact subset of either pair of pants lies in some `S_R`, but limits on the
two whole pieces of the broken domain need more work, not done here: an exhaustion by truncations
`S_{R_j}` with a diagonal subsequence, hypotheses on structure agreement and on a compact image
for every `R_j`, and control of the bubbling points as `R_j` grows.

The almost complex structures `Jₖ` on `Σ_{Lₖ}` are only required to agree with fixed structures
`J` on `Ω` and `J'` on `Ω'`, after the change of coordinates `ψ_{Lₖ}` on the inserted piece. The
plumbed structure `TauCeti.Floer.plumbedAlmostComplex` does so on `S_R` for `Lₖ ≥ 2R + 2`
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
converge pointwise in `M`. Covering the pieces by several charts is not treated here.

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

namespace TauCeti.SymplecticForm

open Floer TauCeti.MeasureTheory

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ha Hb : Puncture → ℝ → V → ℝ} {q : Puncture}

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
  set T := Complex.equivRealProdCLM.symm ⁻¹' truncation R
  have hTS : T ⊆ thricePuncturedSphereReal := preimage_truncation_subset_thricePuncturedSphereReal R
  have hS : IsOpen (thricePuncturedSphereReal ×ˢ (univ : Set V)) :=
    isOpen_thricePuncturedSphereReal.prod isOpen_univ
  have hK' (H : Puncture → ℝ → V → ℝ) (hH : ∀ r, Periodic (H r) 1)
      (hHs : ∀ r, ContDiff ℝ 3 (uncurry (H r))) {n : ℕ∞} (hn : (n : WithTop ℕ∞) ≤ 3) (v : ℂ) :
      ContDiffOn ℝ n
        (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
        (thricePuncturedSphereReal ×ˢ univ) := by
    rintro ⟨z, x⟩ ⟨hz, -⟩
    exact (contDiffAt_uncurry_pairOfPantsPerturbation hH (fun q ↦ (hHs q).of_le hn) hz x
      v).contDiffWithinAt
  have hTK := prod_mono hTS (subset_univ K)
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hS
    (hK' Hb hHb hHbs (by norm_num) 1) (hK' Hb hHb hHbs (by norm_num) I) hJ
    (isCompact_preimage_truncation R) hK hTK hJt
  obtain ⟨δ', hδ', hconv'⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hS
    (hK' Ha hHa hHas (by norm_num) 1) (hK' Ha hHa hHas (by norm_num) I) hJ'
    (isCompact_preimage_truncation R) hK hTK hJ't
  refine ⟨min δ δ', lt_min hδ hδ', fun Ω Ω' L u Jk E hΩ hΩT hΩ' hΩ'T hL4 hLR hu hfl hJΩ hJΩ' hE
    huK huK' ↦ ?_⟩
  -- The real-coordinate pair-of-pants data and the plumbed spheres.
  set Kb : ℂ → ℝ × ℝ → V → ℝ := fun v z x ↦
    pairOfPantsPerturbation Hb (Complex.equivRealProdCLM.symm z) x v
  set Ka : ℂ → ℝ × ℝ → V → ℝ := fun v z x ↦
    pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x v
  set Kp : ℕ → ℂ → ℝ × ℝ → V → ℝ := fun k v z x ↦
    plumbedPerturbation Ha Hb q (L k) (Complex.equivRealProdCLM.symm z) x v
  set P : ℕ → Set (ℝ × ℝ) := fun k ↦ {z | (Complex.equivRealProdCLM.symm z ≠ 0 ∧
    Complex.equivRealProdCLM.symm z ≠ 1) ∧ Complex.equivRealProdCLM.symm z ≠ q.plumbingMap (L k) 1}
  set ψ : ℕ → ℝ × ℝ → ℝ × ℝ := fun k ↦ realChart (q.plumbingMap (L k))
  have hRL (k : ℕ) : R + 2 < L k := by linarith [hLR k, hL4 k]
  have hRL2 (k : ℕ) : R ≤ L k / 2 := by linarith [hLR k]
  -- The truncation `S_R` lies in `Σ_L`, and the plumbing map carries it into `Σ_L`.
  have hTP (k : ℕ) : T ⊆ P k := fun z hz ↦
    mem_plumbedSphere_of_mem_truncation hq (hL4 k) (truncation_mono (hRL2 k) hz)
  have hψP (k : ℕ) : MapsTo (ψ k) T (P k) := fun w hw ↦ by
    simp only [P, ψ, mem_ofPred_eq, equivRealProdCLM_symm_realChart]
    exact plumbingMap_mem_plumbedSphere_of_mem_truncation hq (hL4 k) (truncation_mono (hRL2 k) hw)
  have hPopen (k : ℕ) : IsOpen (P k) := isOpen_plumbedSphere q (L k)
  have hψs (k : ℕ) : ContDiff ℝ 3 (ψ k) := contDiff_realChart_plumbingMap q (L k)
  -- On the receiving truncation the plumbed datum is the datum of `S`.
  have hKb (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ T) (v : ℂ) : Kp k v z = Kb v z :=
    funext fun x ↦ DFunLike.congr_fun
      (plumbedPerturbation_eq_pairOfPantsPerturbation_of_mem_truncation hq hab (hRL k).le hz x) v
  -- On the inserted truncation `u ∘ ψ` solves the Floer equation of `S`.
  have hfla (k : ℕ) {w : ℝ × ℝ} (hw : w ∈ T) (hJw : Jk k (ψ k w) = J' w) :
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J' w ((u k ∘ ψ k) w))
        (ω.perturbedFDeriv (Ka 1) (Ka I) (u k ∘ ψ k) w : ℝ × ℝ →ₗ[ℝ] V) := by
    have h := hfl k (ψ k w) (hψP k hw)
    rw [hJw] at h
    exact ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_plumbingMap hq hHa hHb
      (fun r ↦ (hHas r).of_le (by norm_num)) (fun r ↦ (hHbs r).of_le (by norm_num)) hab (hL4 k)
      (hRL k) hw (((hu k).differentiableOn (by norm_num)).differentiableAt
        ((hPopen k).mem_nhds (hψP k hw)))
      h
  -- The densities are continuous on neighbourhoods of the compact truncation, so integrable.
  have hUb (k : ℕ) : IsOpen (thricePuncturedSphereReal ∩ P k) :=
    isOpen_thricePuncturedSphereReal.inter (hPopen k)
  have hintb (k : ℕ) : IntegrableOn (ω.floerEnergyDensity (Kb 1) (Kb I) (u k)) Ω :=
    (((ω.continuousOn_floerEnergyDensity (hUb k)
      (((hu k).mono inter_subset_right).of_le (by norm_num))
      ((hK' Hb hHb hHbs (by norm_num) 1).mono (prod_mono inter_subset_left le_rfl))
      ((hK' Hb hHb hHbs (by norm_num) I).mono (prod_mono inter_subset_left le_rfl))).mono
        fun z hz ↦ ⟨hTS hz, hTP k hz⟩).integrableOn_compact
      (isCompact_preimage_truncation R)).mono_set hΩT
  have hUa (k : ℕ) : IsOpen (thricePuncturedSphereReal ∩ ψ k ⁻¹' P k) :=
    isOpen_thricePuncturedSphereReal.inter ((hPopen k).preimage (hψs k).continuous)
  have hua (k : ℕ) : ContDiffOn ℝ 3 (u k ∘ ψ k) (thricePuncturedSphereReal ∩ ψ k ⁻¹' P k) :=
    (hu k).comp (hψs k).contDiffOn fun _ hw ↦ hw.2
  have hinta (k : ℕ) : IntegrableOn (ω.floerEnergyDensity (Ka 1) (Ka I) (u k ∘ ψ k)) Ω' :=
    (((ω.continuousOn_floerEnergyDensity (hUa k) ((hua k).of_le (by norm_num))
      ((hK' Ha hHa hHas (by norm_num) 1).mono (prod_mono inter_subset_left le_rfl))
      ((hK' Ha hHa hHas (by norm_num) I).mono (prod_mono inter_subset_left le_rfl))).mono
        fun w hw ↦ ⟨hTS hw, hψP k hw⟩).integrableOn_compact
      (isCompact_preimage_truncation R)).mono_set hΩ'T
  -- The energy over each piece is at most the total energy.
  have hEb (k : ℕ) : ∫ z in Ω, ω.floerEnergyDensity (Kb 1) (Kb I) (u k) z ≤ E := by
    rw [setIntegral_congr_fun hΩ.measurableSet fun z hz ↦
      ω.floerEnergyDensity_congr_perturbation _ (hKb k (hΩT hz) 1).symm
        (hKb k (hΩT hz) I).symm]
    exact setIntegral_le_of_lintegral_ofReal_le (hE k) _
  have hEa (k : ℕ) : ∫ w in Ω', ω.floerEnergyDensity (Ka 1) (Ka I) (u k ∘ ψ k) w ≤ E := by
    have hsub : Ω' ⊆ {w | (Complex.equivRealProdCLM.symm w ≠ 0 ∧
        Complex.equivRealProdCLM.symm w ≠ 1) ∧
        2 - L k < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re} := fun w hw ↦ by
      have h := (mem_truncation.1 (hΩ'T hw)).2.2 inf
      rw [endSign_inf, neg_one_mul] at h
      exact ⟨⟨(mem_truncation.1 (hΩ'T hw)).1, (mem_truncation.1 (hΩ'T hw)).2.1⟩,
        by linarith [hRL k, hLR k, hL4 k]⟩
    rw [← integral_floerEnergyDensity_image_plumbingMap ω hq hHa hHb
      (fun r ↦ (hHas r).of_le (by norm_num)) (fun r ↦ (hHbs r).of_le (by norm_num)) hab (hL4 k)
      hΩ'.measurableSet hsub ((hu k).differentiableOn (by norm_num))]
    exact setIntegral_le_of_lintegral_ofReal_le (hE k) _
  -- Compactness on the receiving pair of pants, then on the inserted one along the subsequence.
  obtain ⟨φ, Z, v, hφ, hZΩ, hZE, -, -, hvc, hvK, hlim⟩ := hconv hΩ hΩT
    (fun k ↦ (hu k).mono fun z hz ↦ hTP k (hΩT hz))
    (fun k z hz ↦ by
      have h := hfl k z (hTP k (hΩT hz))
      rwa [hJΩ k z hz, ω.perturbedFDeriv_congr _ (hKb k (hΩT hz) 1) (hKb k (hΩT hz) I)] at h)
    huK hintb hEb
  obtain ⟨φ', Z', v', hφ', hZΩ', hZE', -, -, hvc', hvK', hlim'⟩ := hconv' hΩ' hΩ'T
    (fun n ↦ (hua (φ n)).mono fun w hw ↦ ⟨hTS (hΩ'T hw), hψP (φ n) (hΩ'T hw)⟩)
    (fun n w hw ↦ hfla (φ n) (hΩ'T hw) (hJΩ' (φ n) w hw)) (fun n ↦ huK' (φ n))
    (fun n ↦ hinta (φ n)) fun n ↦ hEa (φ n)
  refine ⟨φ ∘ φ', Z, Z', v, v', hφ.comp hφ', hZΩ,
    (mul_le_mul_of_nonneg_left (min_le_left δ δ') (Nat.cast_nonneg _)).trans hZE, hZΩ',
    (mul_le_mul_of_nonneg_left (min_le_right δ δ') (Nat.cast_nonneg _)).trans hZE', hvc, hvK,
    hlim.comp_tendsto hφ'.tendsto_atTop,
    hvc', hvK', hlim'⟩

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
  have hR₀ : max R 0 ≤ L / 2 := max_le (by linarith) (by linarith)
  refine ⟨preimage_mono (truncation_mono (le_max_left R 0)), fun z hz ↦
    mem_plumbedSphere_of_mem_truncation hq hL (truncation_mono hR₀ hz), fun w hw ↦ ?_⟩
  simp only [mem_ofPred_eq, equivRealProdCLM_symm_realChart]
  exact plumbingMap_mem_plumbedSphere_of_mem_truncation hq hL (truncation_mono hR₀ hw)

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

end TauCeti.SmoothTwoForm.IsNondegenerate
