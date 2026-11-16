/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation

/-!
# Compactness of pairs of pants with continuation necks

Pair-of-pants products for two choices of end Hamiltonians are compared by the pairs of pants with
continuation necks, `K_L = TauCeti.Floer.pairOfPantsContinuationPerturbation G H L`: on each end
`q` the datum interpolates, across a neck at the signed longitudinal coordinate `L_q`, from the
inner Hamiltonian `G_q` to the outer Hamiltonian `H_q`. As the neck positions tend to infinity
these domains break into a pair of pants with end Hamiltonians `G` and continuation cylinders on
its ends; these broken configurations are the compositions of continuation maps with
pair-of-pants products compared by
`TauCeti.NovikovModule.kernelMap_kernelProduct_sub_kernelProduct_kernelMap`.

This file proves interior compactness on the two pieces of the broken domain, for a symplectic
vector space target `(V, ω)`, with all hypotheses on the maps local to the window considered.

**The pants piece.** On a truncation `S_R` the datum depends on the neck positions only through
`min L_q R` (`TauCeti.Floer.pairOfPantsContinuationPerturbation_eq_of_min_eq`), and it is smooth
jointly in the neck positions
(`TauCeti.Floer.contDiffAt_pairOfPantsContinuationPerturbation_neckPositions`). So compactness over
a compact parameter window
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`)
applies on `S_R` to every sequence of neck positions `Lₖ` whose truncations `min Lₖ R` lie in a
fixed compact set `C`; this includes all neck positions bounded below, in particular necks that
stay at fixed positions or tend to infinity:
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuationPerturbation`.
The threshold `δ` depends on `R`, `C`, the compact set `K` of the target and the structures, but
not on the neck positions themselves.

**The necks.** Read in the positive end chart `φ'_q` translated by the neck position, the map
`w ↦ u(φ'_q(w + (L_q, 0)))` solves the continuation equation of the cylinder where `s + L_q ≥ 2`,
and its energy density is the Jacobian of the chart times that of `u`
(`isComplexLinearMap_perturbedFDeriv_continuationHomotopy_comp_positiveEndChart_add`,
`floerEnergyDensity_continuationHomotopy_comp_positiveEndChart_add`). So the compactness theorem
for the fixed continuation datum applies on every window `[a, b] × [t₀, t₀ + 1]` of the cylinder
once `a + L_q ≥ 2`, with a threshold `δ` independent of the neck positions:
`exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart_add`.

In both theorems the energy bound is the energy of `u` over the part of `S` considered, at most the
total Floer energy on `S`, which
`TauCeti.SymplecticForm.lintegral_floerEnergyDensity_pairOfPantsContinuationPerturbation_le`
bounds by the end actions uniformly in the neck positions. Both theorems are stated for every
sequence, so applying them in turn, to the pants piece and to the necks one end at a time, gives a
single subsequence converging on all the chosen windows. Limits on the whole pieces, the
regularity of the limits, the bubbles at the concentration points, the breaking of Floer cylinders
off the necks, and the manifold-target version are not treated here.

## References

* M. Schwarz, *Cohomology operations from S¹-cobordisms in Floer homology*, PhD thesis,
  ETH Zürich (1995), on the compatibility of the pair-of-pants product with continuation maps.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology TauCeti.ThricePuncturedSphere
open scoped NNReal

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {G H : Puncture → ℝ → V → ℝ}

/-- A function which is continuous and nonnegative on an open set `Ω`, with
`∫⁻_Ω ofReal f ≤ E`, is integrable on `Ω` with integral at most `E`. -/
private theorem integrableOn_and_setIntegral_le_of_setLIntegral_le {f : ℝ × ℝ → ℝ}
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hf : ContinuousOn f Ω) (hf0 : ∀ z ∈ Ω, 0 ≤ f z) {E : ℝ≥0}
    (hE : ∫⁻ z in Ω, ENNReal.ofReal (f z) ≤ E) : IntegrableOn f Ω ∧ ∫ z in Ω, f z ≤ E := by
  have hm := hf.aestronglyMeasurable (μ := volume) hΩ.measurableSet
  have h0 : 0 ≤ᵐ[volume.restrict Ω] f :=
    (ae_restrict_iff' hΩ.measurableSet).2 (Eventually.of_forall hf0)
  refine ⟨⟨hm, (hasFiniteIntegral_iff_ofReal h0).2 (hE.trans_lt ENNReal.coe_lt_top)⟩, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae h0 hm]
  exact ENNReal.toReal_le_of_le_ofReal E.coe_nonneg (hE.trans_eq ENNReal.ofReal_coe_nnreal.symm)

/-- **Compactness on the pants side of the necks.** Let `G`, `H` be period-one `C³` inner and
outer Hamiltonians, fix a truncation `S_R`, a compact set `C` of neck positions, a compact
`K ⊆ V`, and a family `J_c` of structures on `S × V`, in real coordinates, depending on neck
positions `c`, `C²` jointly in `(c, z, x)` on an open neighbourhood of `C × S_R × K` and `ω`-tame
on `C × S_R × K`. There is a threshold `δ > 0` with the following property. Let `Lₖ` be neck
positions whose truncations `cₖ = min Lₖ R` lie in `C`, and let `uₖ` be maps which on an open
`Ω ⊆ S_R` are `C³`, solve the Floer equation `(du - X_{K_{Lₖ}})^{0,1} = 0` for the structures
`J_{cₖ}(z, u)`, have Floer energy at most `E` over `Ω` and satisfy `uₖ(Ω) ⊆ K`. Then there are a
subsequence `φ`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E` and a continuous `v : Ω \ Z → K` such
that along `φ` every disc about a point of `Z` eventually carries energy at least `δ`, the
differentials are bounded on compact subsets of `Ω \ Z`, and `u_{φ n} → v` locally uniformly on
`Ω \ Z`. For instance, `C` may be the box of truncations `min L R` of all neck positions `L`
bounded below by a fixed `a`. -/
theorem
  exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_pairOfPantsContinuationPerturbation
    (ω : SymplecticForm V) (hG : ∀ r, Periodic (G r) 1) (hH : ∀ r, Periodic (H r) 1)
    (hGs : ∀ r, ContDiff ℝ 3 (uncurry (G r))) (hHs : ∀ r, ContDiff ℝ 3 (uncurry (H r)))
    (R : ℝ) {C : Set (Puncture → ℝ)} {K : Set V} (hC : IsCompact C) (hK : IsCompact K)
    {J : (Puncture → ℝ) → ℝ × ℝ → V → AlmostComplexStructure V}
    {W : Set ((Puncture → ℝ) × ((ℝ × ℝ) × V))} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : (Puncture → ℝ) × ((ℝ × ℝ) × V) ↦
      (J p.1 p.2.1 p.2.2).toLinearMap.toContinuousLinearMap) W)
    (hCW : C ×ˢ ((equivRealProdCLM.symm ⁻¹' truncation R) ×ˢ K) ⊆ W)
    (hJt : ∀ c ∈ C, ∀ z ∈ equivRealProdCLM.symm ⁻¹' truncation R, ∀ x ∈ K, ω.Tames (J c z x)) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → Puncture → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ equivRealProdCLM.symm ⁻¹' truncation R →
      (∀ k, (fun q ↦ min (L k q) R) ∈ C) →
      (∀ k, ContDiffOn ℝ 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J (fun q ↦ min (L k q) R) z (u k z))
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x I)
          (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x I)
        (u k) z) ≤ E) →
      (∀ k, MapsTo (u k) Ω K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H (L (φ n)) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H (L (φ n)) (equivRealProdCLM.symm z) x I)
          (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z → ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  set T := equivRealProdCLM.symm ⁻¹' truncation R
  have hTS : T ⊆ thricePuncturedSphereReal := preimage_truncation_subset_thricePuncturedSphereReal R
  -- The compactness theorem needs a parameter space with an inner product: read the neck
  -- positions in the Euclidean space on the three punctures.
  set e := EuclideanSpace.equiv Puncture ℝ
  set Kp : ℂ → EuclideanSpace ℝ Puncture → ℝ × ℝ → V → ℝ := fun v p z x ↦
    pairOfPantsContinuationPerturbation G H (e p) (equivRealProdCLM.symm z) x v
  have hm {n : WithTop ℕ∞} : ContDiff ℝ n
      fun p : EuclideanSpace ℝ Puncture × ((ℝ × ℝ) × V) ↦ (e p.1, p.2) :=
    (e.contDiff.comp contDiff_fst).prodMk contDiff_snd
  set W' : Set (EuclideanSpace ℝ Puncture × ((ℝ × ℝ) × V)) := (fun p ↦ (e p.1, p.2)) ⁻¹'
    (W ∩ univ ×ˢ (thricePuncturedSphereReal ×ˢ univ))
  have hW' : IsOpen W' := (hW.inter (isOpen_univ.prod
    (isOpen_thricePuncturedSphereReal.prod isOpen_univ))).preimage (hm (n := 0)).continuous
  have hKp (v : ℂ) : ContDiffOn ℝ 3
      (fun p : EuclideanSpace ℝ Puncture × ((ℝ × ℝ) × V) ↦ Kp v p.1 p.2.1 p.2.2) W' :=
    fun p hp ↦ ((contDiffAt_pairOfPantsContinuationPerturbation_neckPositions hG hH hGs hHs
      (e p.1) hp.2.2.1 p.2.2 v).comp p hm.contDiffAt).contDiffWithinAt
  have hJ' : ContDiffOn ℝ 2 (fun p : EuclideanSpace ℝ Puncture × ((ℝ × ℝ) × V) ↦
      (J (e p.1) p.2.1 p.2.2).toLinearMap.toContinuousLinearMap) W' :=
    hJ.comp hm.contDiffOn fun _ hp ↦ hp.1
  have hCW' : (e ⁻¹' C) ×ˢ (T ×ˢ K) ⊆ W' := fun p hp ↦
    ⟨hCW ⟨hp.1, hp.2⟩, mem_univ _, hTS hp.2.1, mem_univ _⟩
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := Kp 1) (Kt := Kp I) (J := fun p ↦ J (e p)) hW' (hKp 1) (hKp I) hJ'
    (e.toHomeomorph.isCompact_preimage.2 hC) (isCompact_preimage_truncation R) hK hCW'
    fun p hp ↦ hJt _ hp
  refine ⟨δ, hδ, fun Ω L u E hΩ hΩT hLC hu hfl hE huK ↦ ?_⟩
  -- The truncated neck positions, as points of the Euclidean space.
  set p : ℕ → EuclideanSpace ℝ Puncture := fun k ↦ e.symm fun q ↦ min (L k q) R
  have hp (k : ℕ) : e (p k) = fun q ↦ min (L k q) R := e.apply_symm_apply _
  -- On the truncation the datum with necks at `L k` is the datum with necks at `min (L k) R`.
  have hKL (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ T) (v : ℂ) :
      (fun x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x v) =
        Kp v (p k) z :=
    funext fun x ↦ by
      simp only [Kp, hp]
      exact DFunLike.congr_fun (pairOfPantsContinuationPerturbation_eq_of_min_eq
        (R := fun _ ↦ R) (fun q ↦ (min_eq_left (min_le_right _ _)).symm)
        (mem_truncation.1 hz).2.2 x) v
  have hdens (k : ℕ) : EqOn (ω.floerEnergyDensity (Kp 1 (p k)) (Kp I (p k)) (u k))
      (ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x I)
        (u k)) Ω := fun z hz ↦
    ω.floerEnergyDensity_congr_perturbation _ (hKL k (hΩT hz) 1).symm (hKL k (hΩT hz) I).symm
  -- The energy densities are continuous and nonnegative on `Ω`, so integrable there.
  have hint (k : ℕ) := integrableOn_and_setIntegral_le_of_setLIntegral_le hΩ
    (ω.continuousOn_floerEnergyDensity hΩ ((hu k).of_le (by norm_num))
      (fun y hy ↦ (contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH
        (fun r ↦ (hGs r).of_le (by norm_num)) (fun r ↦ (hHs r).of_le (by norm_num)) (L k)
        (hTS (hΩT hy.1)) y.2 1).contDiffWithinAt)
      (fun y hy ↦ (contDiffAt_uncurry_pairOfPantsContinuationPerturbation hG hH
        (fun r ↦ (hGs r).of_le (by norm_num)) (fun r ↦ (hHs r).of_le (by norm_num)) (L k)
        (hTS (hΩT hy.1)) y.2 I).contDiffWithinAt))
    (fun z hz ↦ ω.floerEnergyDensity_nonneg (hJt _ (hLC k) z (hΩT hz) _ (huK k hz)) (hfl k z hz))
    (hE k)
  obtain ⟨φ, -, Z, v, hφ, -, -, hZΩ, hcard, hconc, hbd, hvc, hvK, hlim⟩ :=
    hconv (p := p) hΩ hΩT (fun k ↦ show e (p k) ∈ C by rw [hp]; exact hLC k) hu
      (fun k z hz ↦ by
        have h := hfl k z hz
        rwa [← hp, ω.perturbedFDeriv_congr _ (hKL k (hΩT hz) 1) (hKL k (hΩT hz) I)] at h)
      huK (fun k ↦ (hint k).1.congr_fun (hdens k).symm hΩ.measurableSet)
      fun k ↦ (setIntegral_congr_fun hΩ.measurableSet (hdens k)).trans_le (hint k).2
  refine ⟨φ, Z, v, hφ, hZΩ, hcard, fun z hz ε hε ↦ ?_, hbd, hvc, hvK, hlim⟩
  filter_upwards [hconc z hz ε hε] with n hn
  rwa [setIntegral_congr_fun (measurableSet_ball.inter hΩ.measurableSet)
    fun y hy ↦ hdens (φ n) hy.2] at hn

/-- **Compactness along the necks.** Let `G`, `H` be period-one `C³` inner and outer
Hamiltonians, fix an end `q`, a window `D = [a, b] × [t₀, t₀ + 1]` of the cylinder `ℝ × ℝ`, a
compact `K ⊆ V` and a family `J` of structures on the cylinder, `C²` on an open neighbourhood of
`D × K` and `ω`-tame on `D × K`. There is a threshold `δ > 0`, independent of the neck positions,
with the following property. Let `Lₖ` be neck positions with `a + Lₖ q ≥ 2`. Read the end `q` in
its positive end chart `φ'_q` translated by the neck position, `vₖ(w) = uₖ(φ'_q(w + (Lₖ q, 0)))`,
and let `Ω ⊆ D` be open. Suppose that `uₖ` is `C³` at the points `φ'_q(w + (Lₖ q, 0))` for
`w ∈ Ω`, solves the Floer equation of the pair-of-pants perturbation with continuation necks at
`Lₖ` there, with structures `J` in these coordinates, and has Floer energy at most `E` over the
image of `Ω`, and that `vₖ(Ω) ⊆ K`. Then there are a subsequence `φ`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ E` and a continuous `v : Ω \ Z → K` such that along `φ` every disc about a point of `Z`
eventually carries energy at least `δ` for the continuation datum `C'_q(s, t) dt` from `G'_q` to
`H'_q`, the differentials of the `vₖ` are bounded on compact subsets of `Ω \ Z`, and
`v_{φ n} → v` locally uniformly on `Ω \ Z`. This applies to necks that stay at fixed positions as
well as to necks moving off to infinity; the limit on the whole cylinder is not treated here. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_comp_positiveEndChart_add
    (ω : SymplecticForm V) (hG : ∀ r, Periodic (G r) 1) (hH : ∀ r, Periodic (H r) 1)
    (hGs : ∀ r, ContDiff ℝ 3 (uncurry (G r))) (hHs : ∀ r, ContDiff ℝ 3 (uncurry (H r)))
    (q : Puncture) (a b t₀ : ℝ) {K : Set V} (hK : IsCompact K)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {W : Set ((ℝ × ℝ) × V)} (hW : IsOpen W)
    (hJ : ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hDW : (Icc a b ×ˢ Icc t₀ (t₀ + 1)) ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ Icc a b ×ˢ Icc t₀ (t₀ + 1), ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → Puncture → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ Icc a b ×ˢ Icc t₀ (t₀ + 1) → (∀ k, 2 ≤ a + L k q) →
      (∀ k, ∀ w ∈ Ω, ContDiffAt ℝ 3 (u k) (positiveEndChart q (w + (L k q, 0)))) →
      (∀ k, ∀ w ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
        (J w (u k (positiveEndChart q (w + (L k q, 0)))))
        (ω.perturbedFDeriv
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x I)
          (u k) (positiveEndChart q (w + (L k q, 0))) : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, ∫⁻ z in (fun w ↦ positiveEndChart q (w + (L k q, 0))) '' Ω,
        ENNReal.ofReal (ω.floerEnergyDensity
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation G H (L k) (equivRealProdCLM.symm z) x I)
          (u k) z) ≤ E) →
      (∀ k, MapsTo (fun w ↦ u k (positiveEndChart q (w + (L k q, 0)))) Ω K) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity
          (fun _ _ ↦ 0)
          (continuationHomotopy (positiveEndHamiltonian G q) (positiveEndHamiltonian H q))
          (fun w ↦ u (φ n) (positiveEndChart q (w + (L (φ n) q, 0)))) y) ∧
        (∀ C, IsCompact C → C ⊆ Ω \ ↑Z → ∃ M, ∀ n, ∀ y ∈ C,
          ‖fderiv ℝ (fun w ↦ u (φ n) (positiveEndChart q (w + (L (φ n) q, 0)))) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn
          (fun n w ↦ u (φ n) (positiveEndChart q (w + (L (φ n) q, 0)))) v atTop (Ω \ ↑Z) := by
  set C' := continuationHomotopy (positiveEndHamiltonian G q) (positiveEndHamiltonian H q)
  have hC' : ContDiff ℝ 3 (uncurry C') := contDiff_uncurry_continuationHomotopy
    (contDiff_uncurry_positiveEndHamiltonian (hGs q))
    (contDiff_uncurry_positiveEndHamiltonian (hHs q))
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (Ks := fun _ _ ↦ 0) (Kt := C') hW contDiffOn_const hC'.contDiffOn hJ
    (isCompact_Icc.prod isCompact_Icc) hK hDW hJt
  refine ⟨δ, hδ, fun Ω L u E hΩ hΩD hL hu hfl hE huK ↦ ?_⟩
  -- Being open, `Ω` lies in the band `ℝ × (t₀, t₀ + 1)`, on which the translated chart is
  -- injective.
  have hΩI : Ω ⊆ univ ×ˢ Ico t₀ (t₀ + 1) := fun w hw ↦ by
    have h := hΩ.subset_interior_iff.2 hΩD hw
    rw [interior_prod_eq, interior_Icc, interior_Icc] at h
    exact ⟨mem_univ _, h.2.1.le, h.2.2⟩
  have hΩL (k : ℕ) : ∀ w ∈ Ω, 2 ≤ w.1 + L k q := fun w hw ↦ by
    linarith [(hΩD hw).1.1, hL k]
  -- The translated maps are `C³` on `Ω` and solve the continuation equation there.
  have hv (k : ℕ) : ContDiffOn ℝ 3 (fun w ↦ u k (positiveEndChart q (w + (L k q, 0)))) Ω :=
    fun w hw ↦ ((hu k w hw).comp w ((contDiff_positiveEndChart q 3).comp
      (contDiff_id.add contDiff_const)).contDiffAt).contDiffWithinAt
  have hfl' (k : ℕ) (w : ℝ × ℝ) (hw : w ∈ Ω) :=
    ω.isComplexLinearMap_perturbedFDeriv_continuationHomotopy_comp_positiveEndChart_add hG hH
      (fun r ↦ (hGs r).of_le (by norm_num)) (fun r ↦ (hHs r).of_le (by norm_num)) (hΩL k w hw)
      ((hu k w hw).differentiableAt (by norm_num)) (hfl k w hw)
  -- The energy of the translated map over `Ω` is the energy of `u k` over the image of `Ω`.
  have hEΩ (k : ℕ) : ∫⁻ w in Ω, ENNReal.ofReal (ω.floerEnergyDensity (fun _ _ ↦ 0) C'
      (fun w ↦ u k (positiveEndChart q (w + (L k q, 0)))) w) ≤ E := by
    rw [← lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul
      (φ := fun w ↦ positiveEndChart q (w + (L k q, 0))) hΩ.measurableSet
      ((injOn_positiveEndChart q t₀).comp (add_left_injective _).injOn
        fun w hw ↦ ⟨mem_univ _, by simpa using (hΩI hw).2⟩)
      (fun w _ ↦ ((contDiff_positiveEndChart q 1).differentiable one_ne_zero _).comp w
        (differentiableAt_id.add_const _))
      fun w hw ↦ by
        rw [fderiv_comp_add_right, abs_of_pos (det_fderiv_positiveEndChart_pos q _)]
        exact ω.floerEnergyDensity_continuationHomotopy_comp_positiveEndChart_add hG hH
          (fun r ↦ (hGs r).of_le (by norm_num)) (fun r ↦ (hHs r).of_le (by norm_num))
          (hΩL k w hw) ((hu k w hw).differentiableAt (by norm_num))]
    exact hE k
  -- The energy densities are continuous and nonnegative on `Ω`, so integrable there.
  have hint (k : ℕ) := integrableOn_and_setIntegral_le_of_setLIntegral_le hΩ
    (ω.continuousOn_floerEnergyDensity hΩ ((hv k).of_le (by norm_num)) contDiffOn_const
      (hC'.of_le (by norm_num)).contDiffOn)
    (fun w hw ↦ ω.floerEnergyDensity_nonneg (hJt w (hΩD hw) _ (huK k hw)) (hfl' k w hw)) (hEΩ k)
  exact hconv hΩ hΩD hv hfl' huK (fun k ↦ (hint k).1) fun k ↦ (hint k).2

end TauCeti.SymplecticForm
