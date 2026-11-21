/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Basic
public import TauCeti.Geometry.Symplectic.Floer.DerivativeConvergence.Basic

/-!
# Limits of Floer solutions off the bubbling points

Let `(V, ω)` be a finite-dimensional symplectic vector space, `K = K_s ds + K_t dt` a
perturbation and `J(z, x)` a family of `ω`-tame almost complex structures on `V`, depending on the
domain point `z ∈ ℝ × ℝ`. The compactness theorem for Floer solutions
(`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`) extracts
from a sequence `uₖ` of solutions of `(du - X_K)^{0,1} = 0` with image in a compact set and energy
at most `E` a subsequence converging locally uniformly to a continuous map `v` off a finite set `Z`
of bubbling points. This file shows that, for smooth solutions, `v` is a Floer solution on the
complement of `Z` and the convergence holds in `C¹`:

* `v` is `C¹` on `Ω \ Z`, the derivatives `duₖ` converge to `dv` locally uniformly on `Ω \ Z`,
  and `v` solves `(dv - X_K)^{0,1} = 0` at every point of `Ω \ Z`;
* the energy of `v` over `Ω \ Z` is finite and at most `E`.

This is the statement of Gromov–Floer convergence away from the bubbling points: the limit is a
component of the limiting configuration, to which the bubbles at the points of `Z` and the
cylinders breaking off at the ends are to be attached.

The first point is the `C¹` convergence theorem for the coordinate equation
`∂ₜu - X(z, u) i = J(z, u)(∂ₛu - X(z, u) 1)`
(`TauCeti.Floer.tendstoLocallyUniformlyOn_fderiv_of_floer`), read in the coordinate
`Complex.equivRealProdCLM` of the domain. In the form of the Floer equation used here it is
`TauCeti.SymplecticForm.tendstoLocallyUniformlyOn_fderiv_of_floer`. The second is Fatou's
lemma: the energy density `ω(∂ₛu - X_{K_s}, ∂ₜu - X_{K_t})` of the limit is the pointwise limit of
the energy densities along the sequence, since it depends continuously on the value and the
derivative of the map (`TauCeti.SymplecticForm.tendsto_floerEnergyDensity`), so the energy is
lower semicontinuous (`TauCeti.SymplecticForm.setLIntegral_floerEnergyDensity_le_liminf`). The
limit equation is read back from the coordinate equation by
`TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_iff_fderiv_comp_equivRealProdCLM_I_sub`.

The same holds for solutions in a symplectic chart of a manifold, in the namespace
`TauCeti.SmoothTwoForm` of `TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold`:
`IsNondegenerate.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset`.

## Main results

* `TauCeti.SymplecticForm.tendstoLocallyUniformlyOn_fderiv_of_floer`: smooth Floer solutions
  with locally bounded derivatives converging pointwise converge in `C¹` to a Floer solution.
* `TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset`:
  smooth Floer solutions of bounded energy converge in `C¹` off finitely many bubbling points to a
  Floer solution of energy at most `E`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Section 4.6 (convergence away from the bubbling points) and
  Section 8.1 (inhomogeneous equations).
-/

public section

open Complex Filter Function MeasureTheory Metric Set Topology

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ks Kt : ℝ × ℝ → V → ℝ} {J : ℝ × ℝ → V → AlmostComplexStructure V}

/-- **The derivatives of Floer solutions converge.** Let `K = K_s ds + K_t dt` be `C²` and `J(z, x)`
be `C¹` on an open set `W ⊆ (ℝ × ℝ) × V`, and let `Ω ⊆ ℝ × ℝ` be open. Let `uₙ` be smooth solutions
of the Floer equation `(du - X_K)^{0,1} = 0` for `J(z, u)` on `Ω`, whose derivatives are bounded on
each compact subset of `Ω` uniformly in `n`, and which converge pointwise on `Ω` to a map `v` whose
graph over `Ω` lies in `W`. Then `v` is `C¹` on `Ω`, `duₙ → dv` locally uniformly on `Ω`, and `v`
solves the Floer equation on `Ω`. -/
theorem tendstoLocallyUniformlyOn_fderiv_of_floer (ω : SymplecticForm V)
    {W : Set ((ℝ × ℝ) × V)} {Ω : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 2 (uncurry Ks) W) (hKt : ContDiffOn ℝ 2 (uncurry Kt) W)
    (hJ : ContDiffOn ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hΩ : IsOpen Ω) {u : ℕ → ℝ × ℝ → V} {v : ℝ × ℝ → V} (hvW : ∀ z ∈ Ω, (z, v z) ∈ W)
    (hu : ∀ n, ContDiffOn ℝ (⊤ : ℕ∞) (u n) Ω)
    (hfl : ∀ n, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u n z))
      (ω.perturbedFDeriv Ks Kt (u n) z : ℝ × ℝ →ₗ[ℝ] V))
    (hbd : ∀ C, IsCompact C → C ⊆ Ω → ∃ M, ∀ n, ∀ z ∈ C, ‖fderiv ℝ (u n) z‖ ≤ M)
    (hlim : ∀ z ∈ Ω, Tendsto (fun n ↦ u n z) atTop (𝓝 (v z))) :
    ContDiffOn ℝ 1 v Ω ∧
      TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u n)) (fderiv ℝ v) atTop Ω ∧
      ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (v z))
        (ω.perturbedFDeriv Ks Kt v z : ℝ × ℝ →ₗ[ℝ] V) := by
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM with he
  set g : ℂ × V → (ℝ × ℝ) × V := fun q ↦ (e q.1, q.2)
  have hg {n : WithTop ℕ∞} : ContDiff ℝ n g := (e.contDiff.comp contDiff_fst).prodMk contDiff_snd
  -- The Hamiltonian one-form `X_K` is `C¹` on `W`.
  have hX : ContDiffOn ℝ 1 (uncurry (ω.hamiltonianOneForm Ks Kt)) W :=
    ω.contDiffOn_uncurry_hamiltonianOneForm hW hKs hKt
  -- Derivatives of `u n ∘ e` are bounded on compact subsets of `e ⁻¹' Ω`.
  have hbd' : ∀ C, IsCompact C → C ⊆ e ⁻¹' Ω →
      ∃ M, ∀ n, ∀ y ∈ C, ‖fderiv ℝ (u n ∘ e) y‖ ≤ M := by
    intro C hC hCΩ
    obtain ⟨M, hM⟩ := hbd (e '' C) (hC.image e.continuous) (image_subset_iff.2 hCΩ)
    refine ⟨M * ‖(e : ℂ →L[ℝ] ℝ × ℝ)‖, fun n y hy ↦ ?_⟩
    rw [e.comp_right_fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hM n _ (mem_image_of_mem e hy)) (norm_nonneg _))
  -- The coordinate theorem, for `u n ∘ e` on `e ⁻¹' Ω`.
  obtain ⟨hv', hconv', heq'⟩ := Floer.tendstoLocallyUniformlyOn_fderiv_of_floer
    (J := fun q ↦ (J (e q.1) q.2).toLinearMap.toContinuousLinearMap)
    (X := fun q ↦ ω.hamiltonianOneForm Ks Kt (e q.1) q.2 ∘L (e : ℂ →L[ℝ] ℝ × ℝ))
    (W := g ⁻¹' W) (Ω := e ⁻¹' Ω) (u := fun n ↦ u n ∘ e) (v := v ∘ e)
    (hW.preimage (hg (n := 0)).continuous) (hJ.comp hg.contDiffOn (mapsTo_preimage g W))
    ((hX.comp hg.contDiffOn (mapsTo_preimage g W)).clm_comp contDiffOn_const)
    (hΩ.preimage e.continuous) (fun y hy ↦ hvW (e y) hy)
    (fun n ↦ (hu n).comp e.contDiff.contDiffOn (mapsTo_preimage e Ω))
    (fun n y _ w ↦ by simp)
    (fun n y hy ↦
      (ω.isComplexLinearMap_perturbedFDeriv_iff_fderiv_comp_equivRealProdCLM_I_sub).1
        (hfl n (e y) hy)) hbd'
    (fun y hy ↦ hlim (e y) hy)
  -- Back to the original coordinates.
  have hmaps : MapsTo e.symm Ω (e ⁻¹' Ω) := fun z hz ↦ by simpa using hz
  have hfd (w : ℝ × ℝ → V) (z : ℝ × ℝ) :
      fderiv ℝ w z = fderiv ℝ (w ∘ e) (e.symm z) ∘L (e.symm : ℝ × ℝ →L[ℝ] ℂ) := by
    rw [e.comp_right_fderiv, e.apply_symm_apply, ContinuousLinearMap.comp_assoc]
    simp
  refine ⟨?_, ?_, fun z hz ↦ ?_⟩
  · have h := hv'.comp e.symm.contDiff.contDiffOn hmaps
    exact h.congr fun z _ ↦ by simp
  · have h := ((ContinuousLinearMap.compL ℝ (ℝ × ℝ) ℂ V).flip
      (e.symm : ℝ × ℝ →L[ℝ] ℂ)).uniformContinuous.comp_tendstoLocallyUniformlyOn
        (hconv'.comp e.symm hmaps e.symm.continuous.continuousOn)
    convert h using 1
    · funext n z
      exact hfd (u n) z
    · funext z
      exact hfd v z
  · have h := (ω.isComplexLinearMap_perturbedFDeriv_iff_fderiv_comp_equivRealProdCLM_I_sub
      (Ks := Ks) (Kt := Kt) (J := J) (u := v) (y := e.symm z)).2 (heq' (e.symm z) (hmaps hz))
    simpa [he] using h

/-- **Floer solutions of bounded energy converge in `C¹` off finitely many bubbling points.** Let
`K = K_s ds + K_t dt` be `C³` and `J(z, x)` be `C²` on an open set `W ⊆ (ℝ × ℝ) × V` containing
`D × K` for compact `D ⊆ ℝ × ℝ` and `K ⊆ V`, with `J(z, x)` tamed by `ω` on `D × K`. There is a
threshold `δ > 0` with the following property. Let `uₖ` be smooth solutions of the Floer equation
`(du - X_K)^{0,1} = 0` for `J(z, u)` on an open set `Ω ⊆ D`, with image in `K` and Floer energy
`∫_Ω ω(∂ₛuₖ - X_{K_s}, ∂ₜuₖ - X_{K_t}) ≤ E`. Then there are a subsequence `φ`, a finite set
`Z ⊆ Ω` with `#Z * δ ≤ E`, and a map `v : Ω \ Z → K` such that along `φ` every disc about a point of
`Z` eventually carries Floer energy at least `δ`, `u_{φ n} → v` and `du_{φ n} → dv` locally
uniformly on `Ω \ Z`, `v` is a `C¹` solution of the Floer equation on `Ω \ Z`, and the Floer energy
of `v` over `Ω \ Z` is finite and at most `E`. -/
theorem exists_pos_forall_tendstoLocallyUniformlyOn_fderiv_subseq_off_finset
    (ω : SymplecticForm V) {W : Set ((ℝ × ℝ) × V)} {D : Set (ℝ × ℝ)} {K : Set V}
    (hW : IsOpen W) (hKs : ContDiffOn ℝ 3 (uncurry Ks) W)
    (hKt : ContDiffOn ℝ 3 (uncurry Kt) W)
    (hJ : ContDiffOn ℝ 2
      (fun p : (ℝ × ℝ) × V ↦ (J p.1 p.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ K, ω.Tames (J z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, ContDiffOn ℝ (⊤ : ℕ∞) (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedFDeriv Ks Kt (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ E) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        ContDiffOn ℝ 1 v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) ∧
        TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (u (φ n))) (fderiv ℝ v) atTop (Ω \ ↑Z) ∧
        (∀ z ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (v z))
          (ω.perturbedFDeriv Ks Kt v z : ℝ × ℝ →ₗ[ℝ] V)) ∧
        IntegrableOn (ω.floerEnergyDensity Ks Kt v) (Ω \ ↑Z) ∧
        ∫ z in Ω \ ↑Z, ω.floerEnergyDensity Ks Kt v z ≤ E := by
  obtain ⟨δ, hδ, hconv⟩ :=
    ω.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset hW hKs hKt hJ hD hK hDKW hJt
  refine ⟨δ, hδ, fun Ω u E hΩ hΩD hu hfl huK hint hE ↦ ?_⟩
  obtain ⟨φ, Z, v, hφ, hZΩ, hcard, hconc, hbd, -, hvK, hlim⟩ :=
    hconv hΩ hΩD (fun k ↦ (hu k).of_le (WithTop.coe_le_coe.2 le_top)) hfl huK hint hE
  set S := Ω \ (Z : Set (ℝ × ℝ))
  have hS : IsOpen S := hΩ.sdiff Z.finite_toSet.isClosed
  have hvW (z : ℝ × ℝ) (hz : z ∈ S) : (z, v z) ∈ W := hDKW ⟨hΩD hz.1, hvK hz⟩
  obtain ⟨hv, hdconv, hveq⟩ := ω.tendstoLocallyUniformlyOn_fderiv_of_floer hW
    (hKs.of_le (by norm_num)) (hKt.of_le (by norm_num)) (hJ.of_le (by norm_num)) hS hvW
    (fun n ↦ (hu (φ n)).mono sdiff_subset) (fun n z hz ↦ hfl (φ n) z hz.1) hbd
    (fun z hz ↦ hlim.tendsto_at hz)
  -- The energy of `v` over `S` is at most `E`, by Fatou's lemma.
  have hX := (ω.contDiffOn_uncurry_hamiltonianOneForm (n := 0) hW (hKs.of_le (by norm_num))
    (hKt.of_le (by norm_num))).continuousOn
  have hnn (n : ℕ) (z : ℝ × ℝ) (hz : z ∈ Ω) : 0 ≤ ω.floerEnergyDensity Ks Kt (u (φ n)) z :=
    ω.floerEnergyDensity_nonneg (hJt z (hΩD hz) _ (huK (φ n) hz)) (hfl (φ n) z hz)
  obtain ⟨hint_v, hE_v⟩ := ω.integrableOn_floerEnergyDensity_and_setIntegral_le_of_tendsto
    hS.measurableSet (fun z hz ↦ ((hX.continuousAt (hW.mem_nhds (hvW z hz))).comp
      (Continuous.prodMk_right z).continuousAt)) (fun n z hz ↦ hnn n z hz.1)
    (fun n ↦ (hint (φ n)).mono_set sdiff_subset)
    (fun n ↦ (setIntegral_mono_set (hint (φ n)) (ae_restrict_of_forall_mem hΩ.measurableSet
      (hnn n)) (ae_of_all _ fun z (hz : z ∈ S) ↦ hz.1)).trans (hE (φ n)))
    (fun z hz ↦ hlim.tendsto_at hz) fun z hz ↦ hdconv.tendsto_at hz
  exact ⟨φ, Z, v, hφ, hZΩ, hcard, hconc, hv, hvK, hlim, hdconv, hveq, hint_v, hE_v⟩

end TauCeti.SymplecticForm
