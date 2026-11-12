/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Capped
public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.End.Chart
public import TauCeti.Geometry.Symplectic.Floer.Pullback

/-!
# Compactness of the capped pair of pants as the necks stretch

The comparison between the pair-of-pants product and the quantum product caps the three ends of
the pair of pants `S = ℂ ∖ {0, 1}` with Piunikhin–Salamon–Schwarz planes along necks of length
`L`. The Hamiltonian datum is `K_L = TauCeti.Floer.cappedPerturbation 1 L H`; the comparison
family `TauCeti.Floer.cappedComparisonPerturbation H R` is this datum with `L = R - 1` for
`R ≥ 2` (`TauCeti.Floer.cappedComparisonPerturbation_of_two_le`). As `L → ∞` the capped sphere
breaks into the pair of pants and three PSS planes joined along infinitely long necks: this is the
broken end of the comparison family, where it is the product of the pair of pants and the PSS
planes. This file proves the interior part of Gromov–Floer compactness at that end, for a
symplectic vector space target `(V, ω)`, on each of the four pieces.

* **The pair of pants.** On the truncation `S_R` the datum is the pair-of-pants datum
  `TauCeti.Floer.pairOfPantsPerturbation H` as soon as `R ≤ L + 2`
  (`TauCeti.Floer.cappedPerturbation_eq_smul_pairOfPantsPerturbation`). So solutions for neck
  lengths `Lₖ ≥ R - 2` with bounded energy restrict on `S_R` to solutions of the pair-of-pants
  equation, and converge there off finitely many bubbling points (`SymplecticForm.`
  `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedPerturbation`).
* **The PSS planes.** Read the end `q` in its positive end chart `φ'_q`
  (`TauCeti.Floer.positiveEndChart`), translated by `L + 4`: `z ↦ φ'_q(z + (L + 4, 0))`. Wherever
  `s + L ≥ -2`, the datum in these coordinates is `β(-s - 1) H'_q(t) dt`, where `β` is the smooth
  transition and `H'_q` the end Hamiltonian of the positive end chart
  (`TauCeti.Floer.perturbationPullback_positiveEndChart_add_cappedPerturbation`). This is the
  perturbation of the negative PSS plane with Hamiltonian `H'_q`, read in the end coordinates of
  the plane (`TauCeti.Floer.PSSPlane.endComponent`), and it does not depend on `L`: it is
  `H'_q(t) dt` on the neck side `s ≤ -2` and vanishes for `s ≥ -1`, towards the pole. On the
  output end, where the pair of pants is capped by a positive plane, the positive end chart
  reverses both coordinates, and the cap reads as the negative plane of `H'_∞(t) = -H_∞(-t)`.
  Since the translated end chart is holomorphic, the translated maps solve the Floer equation of
  the plane, and their energy over a band of angular width one is the energy of the solution over
  its image. On every compact window they converge off finitely many bubbling points
  (`SymplecticForm.`
  `exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedPerturbation_plane`).

In both theorems the threshold `δ` does not depend on the neck lengths, and the almost complex
structures `Jₖ` of the sequence are only required to agree with a fixed structure on the window,
after the change of coordinates on the plane pieces. The capped structures
`TauCeti.Floer.cappedAlmostComplex` do so: they are the pair-of-pants structure on `S_{L + 2}`
(`TauCeti.Floer.cappedAlmostComplex_eq_pairOfPantsAlmostComplex`), the end structure along the
neck (`TauCeti.Floer.cappedAlmostComplex_cylindricalEndLift_of_mem_Icc`), and the structure for
`L = 0` translated by `L` beyond it
(`TauCeti.Floer.cappedAlmostComplex_cylindricalEndLift_add_endSign_mul`). The theorems apply to
one piece at a time, and their conclusions are stable under passing to subsequences, so they can
be applied in turn to obtain one subsequence converging on all four pieces.

The windows of the plane pieces lie in the cylinder of the end, so they do not contain the poles.
The regularity of the limits, the bubbles at the bubbling points, the poles, and the breaking of
Floer cylinders off the necks are not treated here.

## References

* S. Piunikhin, D. Salamon and M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, in *Contact and symplectic geometry*, Publ. Newton Inst. 8 (1996), 171–200, on the
  comparison of the pair-of-pants product with the quantum product.
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 12.1 (the PSS isomorphism).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology
open TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open scoped NNReal ENNReal

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {H : Puncture → ℝ → V → ℝ}

/-- **Capped pairs of pants converge on the pair-of-pants piece as the necks stretch.** Let `H_q` be
period-one `C³` Hamiltonians, fix a truncation `S_R` and a compact `K ⊆ V`, and let `J` be a `C²`
family of structures on `S`, read in real coordinates, which is `ω`-tame on `S_R × K`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions on `S` of the Floer
equation `(du - X_K)^{0,1} = 0` of the capped perturbation `K = cappedPerturbation 1 Lₖ H`, with
neck lengths `Lₖ ≥ R - 2`, for structures `Jₖ(z, u)`, and with Floer energy at most `E`. Let `Ω` be
an open subset of `S_R` on which `Jₖ = J` and `uₖ(Ω) ⊆ K`. Then there are a subsequence `φ`, a
finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a continuous `v : Ω \ Z → K` such that along `φ` every
disc about a point of `Z` eventually carries energy at least `δ` for the pair-of-pants datum, the
differentials are bounded on every compact subset of `Ω \ Z`, and `uₖ → v` locally uniformly on
`Ω \ Z`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedPerturbation
    (ω : SymplecticForm V) (hH : ∀ r, Periodic (H r) 1) (hHs : ∀ r, ContDiff ℝ 3 (uncurry (H r)))
    (R : ℝ) {K : Set V} (hK : IsCompact K) {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap)
      (thricePuncturedSphereReal ×ˢ univ))
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
  have hP (v : ℂ) : ContDiffOn ℝ 3
      (uncurry fun z x ↦ pairOfPantsPerturbation H (Complex.equivRealProdCLM.symm z) x v)
      (thricePuncturedSphereReal ×ˢ univ) := by
    rintro ⟨z, x⟩ ⟨hz, -⟩
    exact (contDiffAt_uncurry_pairOfPantsPerturbation hH hHs hz x v).contDiffWithinAt
  obtain ⟨δ, hδ, hconv⟩ := ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset
    (isOpen_thricePuncturedSphereReal.prod isOpen_univ) (hP 1) (hP I) hJ
    (isCompact_preimage_truncation R) hK (prod_mono hTS (subset_univ K)) hJt
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
  have hf0 (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) : 0 ≤ ω.floerEnergyDensity (Kp 1) (Kp I) (u k) z := by
    have h := hfl k z (hΩS hz)
    rw [hJΩ k z hz, ω.perturbedFDeriv_congr _ (hKp k (hΩT hz) 1) (hKp k (hΩT hz) I)] at h
    exact ω.floerEnergyDensity_nonneg (hJt z (hΩT hz) _ (huK k hz)) h
  -- The energy over `Ω` for the pair-of-pants datum is at most the total energy.
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity (Kp 1) (Kp I) (u k) z) ≤
      E := by
    refine le_trans (le_of_eq (setLIntegral_congr_fun hΩ.measurableSet fun z hz ↦ ?_))
      ((setLIntegral_le_lintegral _ _).trans (hE k))
    rw [ω.floerEnergyDensity_congr_perturbation _ (hKp k (hΩT hz) 1) (hKp k (hΩT hz) I)]
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity (Kp 1) (Kp I) (u k)) Ω :=
    ⟨((ω.continuousOn_floerEnergyDensity isOpen_thricePuncturedSphereReal
      ((hu k).of_le (by norm_num)) ((hP 1).of_le (by norm_num)) ((hP I).of_le (by norm_num))).mono
        hΩS).aestronglyMeasurable hΩ.measurableSet,
      (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem hΩ.measurableSet
        fun z hz ↦ hf0 k hz)).2 ((hlin k).trans_lt ENNReal.coe_lt_top)⟩
  exact hconv hΩ hΩT (fun k ↦ (hu k).mono hΩS)
    (fun k z hz ↦ by
      have h := hfl k z (hΩS hz)
      rwa [hJΩ k z hz, ω.perturbedFDeriv_congr _ (hKp k (hΩT hz) 1) (hKp k (hΩT hz) I)] at h)
    huK hint fun k ↦ by
      rw [integral_eq_lintegral_of_nonneg_ae
        (ae_restrict_of_forall_mem hΩ.measurableSet fun z hz ↦ hf0 k hz)
        (hint k).aestronglyMeasurable]
      exact ENNReal.toReal_le_of_le_ofReal E.coe_nonneg
        ((hlin k).trans_eq ENNReal.ofReal_coe_nnreal.symm)

/-! ### The PSS plane pieces -/

section Plane

variable {q : Puncture} {L : ℝ}

/-- The derivative of the positive end chart translated by `L + 4` is that of the positive end
chart at the translated point. -/
private theorem hasFDerivAt_positiveEndChart_add (q : Puncture) (L : ℝ) (z : ℝ × ℝ) :
    HasFDerivAt (fun z ↦ positiveEndChart q (z + (L + 4, 0)))
      (fderiv ℝ (positiveEndChart q) (z + (L + 4, 0))) z :=
  (((contDiff_positiveEndChart q 1).differentiable one_ne_zero _).hasFDerivAt).comp z
    ((hasFDerivAt_id z).add_const _)

omit [FiniteDimensional ℝ V] in
/-- The components of the capped perturbation are differentiable in the target point. -/
private theorem differentiableAt_cappedPerturbation_apply (hH : ∀ r, Periodic (H r) 1)
    (hHs : ∀ r, ContDiff ℝ 1 (uncurry (H r))) (L : ℝ) (v : ℂ) (w : ℝ × ℝ) (y : V) :
    DifferentiableAt ℝ (fun x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm w) x v)
      y :=
  ((contDiff_cappedPerturbation_apply hH hHs 1 L v).comp
    (contDiff_const.prodMk contDiff_id)).differentiable one_ne_zero _

/-- **Capped solutions on the PSS plane pieces.** Let `u` solve, at the image of `z = (s, t)` with
`s + L ≥ -2` under the positive end chart of `q` translated by `L + 4`, the Floer equation of the
capped perturbation with neck length `L`. Then the translated map `u ∘ φ'_q(· + (L + 4, 0))` solves
at `z` the Floer equation of the negative PSS plane with Hamiltonian
`H'_q = positiveEndHamiltonian H q`, read in the end coordinates of the plane. -/
theorem isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_add_cappedPerturbation
    (ω : SymplecticForm V) (hH : ∀ r, Periodic (H r) 1)
    (hHs : ∀ r, ContDiff ℝ 1 (uncurry (H r))) {J : AlmostComplexStructure V} {u : ℝ × ℝ → V}
    {z : ℝ × ℝ} (hz : -2 ≤ z.1 + L)
    (hu : DifferentiableAt ℝ u (positiveEndChart q (z + (L + 4, 0))))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x I) u
      (positiveEndChart q (z + (L + 4, 0))) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J (ω.perturbedFDeriv
      (PSSPlane.negative.endComponent (positiveEndHamiltonian H q) 1)
      (PSSPlane.negative.endComponent (positiveEndHamiltonian H q) I)
      (fun z ↦ u (positiveEndChart q (z + (L + 4, 0)))) z : ℝ × ℝ →ₗ[ℝ] V) := by
  have hψ := hasFDerivAt_positiveEndChart_add q L z
  have hK := differentiableAt_cappedPerturbation_apply hH hHs L
  have hholo : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ)
      (fderiv ℝ (fun z ↦ positiveEndChart q (z + (L + 4, 0))) z : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) := by
    rw [hψ.fderiv]
    exact isComplexLinearMap_fderiv_positiveEndChart q _
  have h' := ω.isComplexLinearMap_perturbedFDeriv_perturbationPullback hψ.differentiableAt hu
    (hK 1 _ _) (hK I _ _) hholo h
  rwa [ω.perturbedFDeriv_congr _
    (funext fun x ↦ by rw [perturbationPullback_positiveEndChart_add_cappedPerturbation (hH q) hz,
      equivRealProdCLM_symm_stdComplexLineReal])
    (funext fun x ↦ by rw [perturbationPullback_positiveEndChart_add_cappedPerturbation (hH q) hz,
      equivRealProdCLM_symm_stdComplexLineImag])] at h'

/-- **The energy of a PSS plane piece.** Let `Ω` be a measurable subset of the band `ℝ × (0, 1)`
with `s + L ≥ -2` at its points `(s, t)`, and `u` a map differentiable on the image of `Ω` under the
positive end chart of `q` translated by `L + 4`. The energy of the translated map over `Ω`, for the
perturbation of the negative PSS plane with Hamiltonian `H'_q` in its end coordinates, is the energy
of `u` over the image of `Ω`, for the capped perturbation with neck length `L`. -/
theorem lintegral_floerEnergyDensity_comp_positiveEndChart_add_cappedPerturbation
    (ω : SymplecticForm V) (hH : ∀ r, Periodic (H r) 1)
    (hHs : ∀ r, ContDiff ℝ 1 (uncurry (H r))) {u : ℝ × ℝ → V} {Ω : Set (ℝ × ℝ)}
    (hΩ : MeasurableSet Ω) (hΩb : Ω ⊆ univ ×ˢ Ioo 0 1) (hΩL : ∀ z ∈ Ω, -2 ≤ z.1 + L)
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
    have ha' : a + (L + 4, 0) ∈ univ ×ˢ Ioo (0 : ℝ) 1 := ⟨mem_univ _, by simpa using (hΩb ha).2⟩
    have hb' : b + (L + 4, 0) ∈ univ ×ˢ Ioo (0 : ℝ) 1 := ⟨mem_univ _, by simpa using (hΩb hb).2⟩
    exact add_right_cancel (injOn_positiveEndChart q ha' hb' hab)
  have hK := differentiableAt_cappedPerturbation_apply hH hHs L
  refine (lintegral_ofReal_image_eq_lintegral_ofReal_of_eq_abs_det_mul hΩ hinj
    (fun z _ ↦ (hasFDerivAt_positiveEndChart_add q L z).differentiableAt) fun z hz ↦ ?_).symm
  have hψ := hasFDerivAt_positiveEndChart_add q L z
  have hcomp : (fun z ↦ u (ψ z)) = u ∘ ψ := rfl
  have hKs : perturbationPullback ψ
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x I)
      stdComplexLineReal z = PSSPlane.negative.endComponent (positiveEndHamiltonian H q) 1 z :=
    funext fun x ↦ by rw [perturbationPullback_positiveEndChart_add_cappedPerturbation (hH q)
      (hΩL z hz), equivRealProdCLM_symm_stdComplexLineReal]
  have hKt : perturbationPullback ψ
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ cappedPerturbation 1 L H (Complex.equivRealProdCLM.symm z) x I)
      stdComplexLineImag z = PSSPlane.negative.endComponent (positiveEndHamiltonian H q) I z :=
    funext fun x ↦ by rw [perturbationPullback_positiveEndChart_add_cappedPerturbation (hH q)
      (hΩL z hz), equivRealProdCLM_symm_stdComplexLineImag]
  rw [← ω.floerEnergyDensity_congr_perturbation _ hKs hKt, hcomp,
    ω.floerEnergyDensity_perturbationPullback hψ.differentiableAt (hu z hz) (hK 1 _ _) (hK I _ _),
    hψ.fderiv, abs_of_pos (det_fderiv_positiveEndChart_pos q _)]

end Plane

/-- **Capped pairs of pants converge on the PSS plane pieces as the necks stretch.** Let `H_q` be
period-one `C³` Hamiltonians and `q` an end. Fix compact sets `D ⊆ ℝ × ℝ` and `K ⊆ V`, and a `C²`
family `J` of structures on a neighbourhood `W` of `D × K` which is `ω`-tame on `D × K`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be `C³` solutions on `S` of the Floer
equation `(du - X_K)^{0,1} = 0` of the capped perturbation `K = cappedPerturbation 1 Lₖ H`, for
structures `Jₖ(z, u)`, and with Floer energy at most `E`, and read them on the end `q` through the
positive end chart translated by `Lₖ + 4`, `wₖ(z) = uₖ(φ'_q(z + (Lₖ + 4, 0)))`. Let `Ω ⊆ D` be an
open subset of the band `ℝ × (0, 1)` with `s + Lₖ ≥ -2` at every point `(s, t)` of `Ω`, on which
`Jₖ ∘ φ'_q(· + (Lₖ + 4, 0)) = J` and `wₖ(Ω) ⊆ K`. Then on `Ω` the maps `wₖ` solve the Floer
equation of the negative PSS plane with Hamiltonian `H'_q = positiveEndHamiltonian H q`, in the end
coordinates of the plane, and there are a subsequence `φ`, a finite set `Z ⊆ Ω` with
`#Z * δ ≤ E`, and a continuous `v : Ω \ Z → K` such that along `φ` every disc about a point of
`Z` eventually carries energy at least `δ` for that datum, the differentials of the `wₖ` are
bounded on every compact subset of `Ω \ Z`, and `wₖ → v` locally uniformly on `Ω \ Z`. -/
theorem
    exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset_cappedPerturbation_plane
    (ω : SymplecticForm V) (hH : ∀ r, Periodic (H r) 1) (hHs : ∀ r, ContDiff ℝ 3 (uncurry (H r)))
    (q : Puncture) {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {K : Set V} (hW : IsOpen W)
    {J : ℝ × ℝ → V → AlmostComplexStructure V}
    (hJ : ContDiffOn ℝ 2 (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ δ > (0 : ℝ), ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃L : ℕ → ℝ⦄ ⦃u : ℕ → ℝ × ℝ → V⦄
      ⦃Jk : ℕ → ℝ × ℝ → V → AlmostComplexStructure V⦄ ⦃E : ℝ≥0⦄,
      IsOpen Ω → Ω ⊆ D → Ω ⊆ univ ×ˢ Ioo 0 1 → (∀ k, ∀ z ∈ Ω, -2 ≤ z.1 + L k) →
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
  have hper := periodic_positiveEndHamiltonian (hH q)
  have hPs {n : ℕ∞} : ContDiff ℝ n (uncurry Ps) := by
    simp only [Ps, PSSPlane.endComponent_one]
    exact contDiff_const
  have hPt {n : ℕ∞} (hn : (n : WithTop ℕ∞) ≤ 3) : ContDiff ℝ n (uncurry Pt) := by
    simp only [Pt, PSSPlane.endComponent_I hper]
    exact (Real.smoothTransition.contDiff.comp
      ((contDiff_const.mul (contDiff_fst.comp contDiff_fst)).sub contDiff_const)).mul
      ((contDiff_uncurry_positiveEndHamiltonian ((hHs q).of_le hn)).comp
        ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))
  have hKs := (hPs (n := 3)).contDiffOn (s := W)
  have hKt := (hPt (n := 3) le_rfl).contDiffOn (s := W)
  obtain ⟨δ, hδ, hconv⟩ :=
    ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hW hKs hKt hJ hD hK hDKW hJt
  refine ⟨δ, hδ, fun Ω L u Jk E hΩ hΩD hΩb hΩL hu hfl hJΩ hE huK ↦ ?_⟩
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
  have hH1 (r : Puncture) : ContDiff ℝ 1 (uncurry (H r)) := (hHs r).of_le (by norm_num)
  have hflw (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) :
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (w k z))
        (ω.perturbedFDeriv Ps Pt (w k) z : ℝ × ℝ →ₗ[ℝ] V) := by
    have h := hfl k _ (hψS k hz)
    rw [hJΩ k z hz] at h
    exact ω.isComplexLinearMap_perturbedFDeriv_comp_positiveEndChart_add_cappedPerturbation hH hH1
      (hΩL k z hz) (hdiffu k hz) h
  have hf0 (k : ℕ) {z : ℝ × ℝ} (hz : z ∈ Ω) : 0 ≤ ω.floerEnergyDensity Ps Pt (w k) z :=
    ω.floerEnergyDensity_nonneg (hJt z (hΩD hz) _ (huK k hz)) (hflw k hz)
  -- Their energy over `Ω` is the energy of `uₖ` over the image of `Ω`, at most `E`.
  have hlin (k : ℕ) : ∫⁻ z in Ω, ENNReal.ofReal (ω.floerEnergyDensity Ps Pt (w k) z) ≤ E := by
    rw [ω.lintegral_floerEnergyDensity_comp_positiveEndChart_add_cappedPerturbation hH hH1 hΩm hΩb
      (hΩL k) fun z hz ↦ hdiffu k hz]
    exact (setLIntegral_le_lintegral _ _).trans (hE k)
  have hwΩ (k : ℕ) : ContDiffOn ℝ 3 (w k) Ω :=
    (hu k).comp ((contDiff_positiveEndChart q 3).comp (contDiff_id.add contDiff_const)).contDiffOn
      fun _ hz ↦ hψS k hz
  have hint (k : ℕ) : IntegrableOn (ω.floerEnergyDensity Ps Pt (w k)) Ω :=
    ⟨(ω.continuousOn_floerEnergyDensity hΩ ((hwΩ k).of_le (by norm_num))
      (hPs (n := 1)).contDiffOn ((hPt (n := 1) (by norm_num)).contDiffOn)
        ).aestronglyMeasurable hΩm,
      (hasFiniteIntegral_iff_ofReal (ae_restrict_of_forall_mem hΩm fun z hz ↦ hf0 k hz)).2
        ((hlin k).trans_lt ENNReal.coe_lt_top)⟩
  exact hconv hΩ hΩD hwΩ (fun k z hz ↦ hflw k hz) huK hint fun k ↦ by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_restrict_of_forall_mem hΩm fun z hz ↦ hf0 k hz)
      (hint k).aestronglyMeasurable]
    exact ENNReal.toReal_le_of_le_ofReal E.coe_nonneg
      ((hlin k).trans_eq ENNReal.ofReal_coe_nnreal.symm)

end TauCeti.SymplecticForm
