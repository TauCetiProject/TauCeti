/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
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

omit [FiniteDimensional ℝ V] in
/-- The pair-of-pants perturbation, read in real coordinates, is `C^n` on `S × V`. -/
private theorem contDiffOn_pairOfPantsPerturbation_real {H : Puncture → ℝ → V → ℝ}
    (hH : ∀ r, Periodic (H r) 1) {n : ℕ∞} (hHs : ∀ r, ContDiff ℝ n (uncurry (H r))) (v : ℂ) :
    ContDiffOn ℝ n
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
  rintro ⟨z, x⟩ ⟨hz, -⟩
  exact (contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).contDiffWithinAt

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
  have hTP : T ⊆ P := fun z hz ↦
    mem_plumbedSphere_of_mem_truncation hq hL4 (truncation_mono (by linarith) hz)
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
      ((contDiffOn_pairOfPantsPerturbation_real hHb (fun r ↦ (hHbs r).of_le (by norm_num))
        1).mono (prod_mono inter_subset_left le_rfl))
      ((contDiffOn_pairOfPantsPerturbation_real hHb (fun r ↦ (hHbs r).of_le (by norm_num))
        I).mono (prod_mono inter_subset_left le_rfl))).mono
        fun z hz ↦ ⟨hTS hz, hTP hz⟩).integrableOn_compact
      (isCompact_preimage_truncation R)).mono_set hΩT
  refine ⟨hu.mono fun z hz ↦ hTP (hΩT hz), fun z hz ↦ ?_, hint, ?_⟩
  · have h := hfl z (hTP (hΩT hz))
    rwa [hJΩ z hz, ω.perturbedFDeriv_congr _ (hKb (hΩT hz) 1) (hKb (hΩT hz) I)] at h
  · rw [setIntegral_congr_fun hΩ.measurableSet fun z hz ↦
      ω.floerEnergyDensity_congr_perturbation _ (hKb (hΩT hz) 1).symm (hKb (hΩT hz) I).symm]
    exact (ENNReal.ofReal_le_ofReal_iff E.coe_nonneg).1 (ofReal_integral_le_lintegral_ofReal.trans
      ((setLIntegral_le_lintegral _ _).trans (hE.trans_eq ENNReal.ofReal_coe_nnreal.symm)))

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
  have hψP : MapsTo ψ T P := fun w hw ↦ by
    simp only [P, ψ, mem_ofPred_eq, equivRealProdCLM_symm_realChart]
    exact plumbingMap_mem_plumbedSphere_of_mem_truncation hq hL4 (truncation_mono (by linarith) hw)
  have hψs : ContDiff ℝ 3 ψ := contDiff_realChart_plumbingMap q L
  have hU : IsOpen (thricePuncturedSphereReal ∩ ψ ⁻¹' P) :=
    isOpen_thricePuncturedSphereReal.inter ((isOpen_plumbedSphere q L).preimage hψs.continuous)
  have hua : ContDiffOn ℝ 3 (u ∘ ψ) (thricePuncturedSphereReal ∩ ψ ⁻¹' P) :=
    hu.comp hψs.contDiffOn fun _ hw ↦ hw.2
  have hint : IntegrableOn (ω.floerEnergyDensity
      (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsPerturbation Ha (Complex.equivRealProdCLM.symm z) x I) (u ∘ ψ)) Ω :=
    (((ω.continuousOn_floerEnergyDensity hU (hua.of_le (by norm_num))
      ((contDiffOn_pairOfPantsPerturbation_real hHa (fun r ↦ (hHas r).of_le (by norm_num))
        1).mono (prod_mono inter_subset_left le_rfl))
      ((contDiffOn_pairOfPantsPerturbation_real hHa (fun r ↦ (hHas r).of_le (by norm_num))
        I).mono (prod_mono inter_subset_left le_rfl))).mono
        fun w hw ↦ ⟨hTS hw, hψP hw⟩).integrableOn_compact
      (isCompact_preimage_truncation R)).mono_set hΩT
  refine ⟨hua.mono fun w hw ↦ ⟨hTS (hΩT hw), hψP (hΩT hw)⟩, fun w hw ↦ ?_, hint, ?_⟩
  · -- On the inserted truncation `u ∘ ψ` solves the Floer equation of `S`.
    have h := hfl (ψ w) (hψP (hΩT hw))
    rw [hJΩ w hw] at h
    exact ω.isComplexLinearMap_perturbedFDeriv_comp_realChart_plumbingMap hq hHa hHb
      (fun r ↦ (hHas r).of_le (by norm_num)) (fun r ↦ (hHbs r).of_le (by norm_num)) hab hL4
      (by linarith) (hΩT hw) ((hu.differentiableOn (by norm_num)).differentiableAt
        ((isOpen_plumbedSphere q L).mem_nhds (hψP (hΩT hw)))) h
  · -- The energy of `u ∘ ψ` over `Ω` is the energy of `u` over `ψ(Ω)`.
    have hsub : Ω ⊆ {w | (Complex.equivRealProdCLM.symm w ≠ 0 ∧
        Complex.equivRealProdCLM.symm w ≠ 1) ∧
        2 - L < (inf.endCoord (Complex.equivRealProdCLM.symm w)).re} := fun w hw ↦ by
      have h := (mem_truncation.1 (hΩT hw)).2.2 inf
      rw [endSign_inf, neg_one_mul] at h
      exact ⟨⟨(mem_truncation.1 (hΩT hw)).1, (mem_truncation.1 (hΩT hw)).2.1⟩, by linarith⟩
    rw [← integral_floerEnergyDensity_image_plumbingMap ω hq hHa hHb
      (fun r ↦ (hHas r).of_le (by norm_num)) (fun r ↦ (hHbs r).of_le (by norm_num)) hab hL4
      hΩ.measurableSet hsub (hu.differentiableOn (by norm_num))]
    exact (ENNReal.ofReal_le_ofReal_iff E.coe_nonneg).1 (ofReal_integral_le_lintegral_ofReal.trans
      ((setLIntegral_le_lintegral _ _).trans (hE.trans_eq ENNReal.ofReal_coe_nnreal.symm)))

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
    (contDiffOn_pairOfPantsPerturbation_real hHb (fun r ↦ (hHbs r).of_le (by norm_num)) 1)
    (contDiffOn_pairOfPantsPerturbation_real hHb (fun r ↦ (hHbs r).of_le (by norm_num)) I) hJ
    (isCompact_preimage_truncation R) hK hTK hJt
  obtain ⟨δ', hδ', hconv'⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hS
    (contDiffOn_pairOfPantsPerturbation_real hHa (fun r ↦ (hHas r).of_le (by norm_num)) 1)
    (contDiffOn_pairOfPantsPerturbation_real hHa (fun r ↦ (hHas r).of_le (by norm_num)) I) hJ'
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
    fun U hU z hz ↦ (hlim U hU z hz).imp fun _ ⟨ht, h⟩ ↦ ⟨ht, hφ'.tendsto_atTop.eventually h⟩,
    hvc', hvK', hlim'⟩

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
  set U : ℕ → Set (ℝ × ℝ) :=
    fun k ↦ Complex.equivRealProdCLM.symm ⁻¹' interior (truncation ((L k - 2) / 2))
  have hU (k : ℕ) : IsOpen (U k) :=
    isOpen_interior.preimage Complex.equivRealProdCLM.symm.continuous
  have hUT (k : ℕ) : U k ⊆ Complex.equivRealProdCLM.symm ⁻¹' truncation ((L k - 2) / 2) :=
    preimage_mono interior_subset
  have hUS (k : ℕ) : U k ⊆ thricePuncturedSphereReal :=
    (hUT k).trans (preimage_truncation_subset_thricePuncturedSphereReal _)
  have hUC : ∀ C, IsCompact C → C ⊆ thricePuncturedSphereReal → ∀ᶠ k in atTop, C ⊆ U k := by
    intro C hC hCS
    obtain ⟨R, hR⟩ := exists_subset_interior_truncation
      (hC.image Complex.equivRealProdCLM.symm.continuous) (image_subset_iff.2 hCS)
    filter_upwards [hL.eventually_ge_atTop (2 * R + 2)] with k hk
    exact (image_subset_iff.1 hR).trans
      (preimage_mono (interior_mono (truncation_mono (by linarith))))
  have hLR (k : ℕ) : 2 * ((L k - 2) / 2) + 2 ≤ L k := by linarith
  choose hub hflb hintb hEb using fun k ↦ receiving_piece ω hq hHb hHbs hab (hL4 k) (hLR k)
    (hU k) (hUT k) (hu k) (hfl k) (fun z hz ↦ hJΩ k z (hUT k hz)) (hE k)
  choose hua hfla hinta hEa using fun k ↦ inserted_piece ω hq hHa hHb hHas hHbs hab (hL4 k)
    (hLR k) (hU k) (hUT k) (hu k) (hfl k) (fun w hw ↦ hJΩ' k w (hUT k hw)) (hE k)
  -- Compactness on the receiving pair of pants, then on the inserted one along the subsequence.
  obtain ⟨φ, Z, v, hφ, hZS, hZC, -, -, hvc, hvK, hlim⟩ :=
    ω.exists_tendstoLocallyUniformlyOn_subseq_off_discrete hS
      (contDiffOn_pairOfPantsPerturbation_real hHb (fun r ↦ hHbs r) 1)
      (contDiffOn_pairOfPantsPerturbation_real hHb (fun r ↦ hHbs r) I) hJ
      isOpen_thricePuncturedSphereReal hK (prod_mono subset_rfl (subset_univ K)) hJt hU hUS hUC
      hub hflb (fun k ↦ (huK k).mono_left fun z hz ↦
        mem_plumbedSphere_of_mem_truncation hq (hL4 k)
          (truncation_mono (by linarith [hL4 k]) (hUT k hz))) hintb (fun k ↦ hEb k)
  obtain ⟨φ', Z', v', hφ', hZS', hZC', -, -, hvc', hvK', hlim'⟩ :=
    ω.exists_tendstoLocallyUniformlyOn_subseq_off_discrete hS
      (contDiffOn_pairOfPantsPerturbation_real hHa (fun r ↦ hHas r) 1)
      (contDiffOn_pairOfPantsPerturbation_real hHa (fun r ↦ hHas r) I) hJ'
      isOpen_thricePuncturedSphereReal hK (prod_mono subset_rfl (subset_univ K)) hJ't
      (fun n ↦ hU (φ n)) (fun n ↦ hUS (φ n))
      (fun C hC hCS ↦ hφ.tendsto_atTop.eventually (hUC C hC hCS)) (fun n ↦ hua (φ n))
      (fun n ↦ hfla (φ n))
      (fun n w hw ↦ huK (φ n) (by
        simpa only [mem_ofPred_eq, equivRealProdCLM_symm_realChart] using
          plumbingMap_mem_plumbedSphere_of_mem_truncation hq (hL4 (φ n))
            (truncation_mono (by linarith [hL4 (φ n)]) (hUT (φ n) hw))))
      (fun n ↦ hinta (φ n)) fun n ↦ hEa (φ n)
  refine ⟨φ ∘ φ', Z, Z', v, v', hφ.comp hφ', hZS, hZC, hZS', hZC', hvc, hvK,
    fun s hs z hz ↦ (hlim s hs z hz).imp fun _ ⟨ht, h⟩ ↦ ⟨ht, hφ'.tendsto_atTop.eventually h⟩,
    hvc', hvK', hlim'⟩

end TauCeti.SymplecticForm
