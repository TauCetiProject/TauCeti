/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Plumbing.Action
import TauCeti.MeasureTheory.Integral.Bochner.Basic

/-!
# Compactness of plumbed four-punctured spheres as the neck stretches

Plumb the output end at `∞` of a pair of pants `S'`, with Hamiltonians `Ha`, into the input end
`q ≠ ∞` of a pair of pants `S`, with Hamiltonians `Hb q = Ha ∞`, along a neck of length `L`. The
result is the four-punctured sphere `Σ_L = ℂ ∖ {0, 1, ψ_L(1)}`, where `ψ_L` is the plumbing map
`TauCeti.ThricePuncturedSphere.Puncture.plumbingMap q L`, with the plumbed perturbation
`TauCeti.Floer.plumbedPerturbation`. As `L → ∞` these domains break into the two pairs of pants:
this is the broken-product end of the one-parameter families of four-punctured spheres that prove
the associativity of the pair-of-pants product. This file proves the interior part of
Gromov–Floer compactness at that end, for a symplectic vector space target `(V, ω)`.

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
    exact (ENNReal.ofReal_le_ofReal_iff E.coe_nonneg).1 (ofReal_integral_le_lintegral_ofReal.trans
      ((setLIntegral_le_lintegral _ _).trans ((hE k).trans_eq ENNReal.ofReal_coe_nnreal.symm)))
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
    exact (ENNReal.ofReal_le_ofReal_iff E.coe_nonneg).1 (ofReal_integral_le_lintegral_ofReal.trans
      ((setLIntegral_le_lintegral _ _).trans ((hE k).trans_eq ENNReal.ofReal_coe_nnreal.symm)))
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
    fun U hU z hz ↦ (hlim U hU z hz).imp fun _ ⟨ht, h⟩ ↦ ⟨ht, hφ'.tendsto_atTop.eventually h⟩,
    hvc', hvK', hlim'⟩

end TauCeti.SymplecticForm
