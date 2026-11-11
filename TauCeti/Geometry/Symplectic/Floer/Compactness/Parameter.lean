/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.Topology.Algebra.Module.BilinearForm

/-!
# Compactness of Floer solutions over a compact parameter window

Moduli spaces of Floer solutions for a family of perturbation data, such as continuation, input
exchange, neck stretching, or the comparison between the pair-of-pants product and the quantum
product, are compactified over their parameter spaces. This file proves the interior part of
Gromov–Floer compactness uniformly over a compact window of parameters, for a symplectic vector
space target `(V, ω)` and the Floer equation `(du - X_{K_p})^{0,1} = 0` with Floer energy
`∫ ω(∂ₛu - X_{K_{p,s}}, ∂ₜu - X_{K_{p,t}})`.

Let the perturbation `K_p = K_{p,s} ds + K_{p,t} dt` and the almost complex structures `J_p(z, x)`
depend on a parameter `p` of a real inner product space `P`, jointly `C³` and `C²` with the domain
point `z ∈ ℝ × ℝ` and the target point `x ∈ V`, and let `J_p(z, x)` be tamed by `ω` for `p`, `z` and
`x` in compact sets `C`, `D` and `K`. There is a threshold `δ > 0` such that every sequence of
solutions for parameters `pₖ ∈ C`, on an open `Ω ⊆ D`, with image in `K` and Floer energy at most
`E`, has a subsequence whose parameters converge to some `p₀ ∈ C` and which converges locally
uniformly on `Ω` off a finite set `Z` of bubbling points with `#Z * δ ≤ E`
(`TauCeti.SymplecticForm.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`).

This combines the compactness theorem over compact parameter windows for the coordinate equation
(`TauCeti.Floer.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset`), whose
energy is `∫ ‖∂ₛu‖²`, with a bound `‖∂ₛu‖² ≤ A e + B` of `‖∂ₛu‖²` by the Floer energy density `e`
which is uniform over the parameter window. Since small discs have small area, energy `∫ ‖∂ₛu‖²`
concentrating at a bubbling point is also Floer energy. For a single datum this is
`TauCeti.SymplecticForm.exists_pos_forall_tendstoLocallyUniformlyOn_subseq_off_finset`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., Section 4.6
  (bubbling off finitely many points) and Section 8.1 (the energy of solutions of the
  inhomogeneous equation).
-/

public section

open Complex ContinuousLinearMap Filter MeasureTheory Metric Set Topology

namespace TauCeti.SymplecticForm

variable {V P : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P]
  {Ks Kt : P → ℝ × ℝ → V → ℝ} {J : P → ℝ × ℝ → V → AlmostComplexStructure V}

omit [InnerProductSpace ℝ P] in
/-- **The energy density bounds the derivative uniformly over a compact parameter window.** Let
`J_p(z, x)` be continuous and tamed by `ω`, and `X_{K_{p,s}}(z, x)` continuous, on `C × D × K` for
compact `C ⊆ P`, `D ⊆ ℝ × ℝ` and `K ⊆ V`. There are constants `A, B ≥ 0` such that for every
`p ∈ C`, every solution `u` of the Floer equation for `K_p` and `J_p(z, u)` at a point `z ∈ D`
with `u(z) ∈ K` satisfies `‖∂ₛu(z)‖² ≤ A ω(∂ₛu - X_{K_{p,s}}, ∂ₜu - X_{K_{p,t}}) + B`. -/
private theorem exists_forall_norm_fderiv_stdComplexLineReal_sq_le_of_parameter
    (ω : SymplecticForm V) {C : Set P} {D : Set (ℝ × ℝ)} {K : Set V} (hC : IsCompact C)
    (hD : IsCompact D) (hK : IsCompact K)
    (hJ : ContinuousOn (fun q : P × ((ℝ × ℝ) × V) ↦
      (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) (C ×ˢ (D ×ˢ K)))
    (hX : ContinuousOn (fun q : P × ((ℝ × ℝ) × V) ↦
      ω.hamiltonianVectorField (Ks q.1 q.2.1) q.2.2) (C ×ˢ (D ×ˢ K)))
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, ω.Tames (J p z x)) :
    ∃ A ≥ 0, ∃ B ≥ 0, ∀ ⦃p : P⦄ ⦃u : ℝ × ℝ → V⦄ ⦃z : ℝ × ℝ⦄, p ∈ C → z ∈ D → u z ∈ K →
      IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
        (ω.perturbedFDeriv (Ks p) (Kt p) u z : ℝ × ℝ →ₗ[ℝ] V) →
      ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 ≤
        A * ω.floerEnergyDensity (Ks p) (Kt p) u z + B := by
  set Jc : P × ((ℝ × ℝ) × V) → V →L[ℝ] V :=
    fun q ↦ (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap
  have hCDK : IsCompact (C ×ˢ (D ×ˢ K)) := hC.prod (hD.prod hK)
  -- A taming constant for `J` and a bound for `X_{K_s}`, uniform on `C × D × K`.
  obtain ⟨c, hc, hJc⟩ := hCDK.exists_pos_forall_mul_norm_sq_le
    (b := fun q ↦ ((ContinuousLinearMap.compL ℝ V V ℝ).flip (Jc q)).comp
      ω.toBilinForm.toContinuousBilinearMap)
    (((ContinuousLinearMap.compL ℝ V V ℝ).flip.continuous.comp_continuousOn hJ).clm_comp
      continuousOn_const)
    (fun q hq v hv ↦ by simpa [Jc] using hJt q.1 hq.1 q.2.1 hq.2.1 q.2.2 hq.2.2 v hv)
  obtain ⟨B, hB⟩ := hCDK.exists_bound_of_continuousOn hX
  refine ⟨2 / c, by positivity, 2 * B ^ 2, by positivity, fun p u z hp hz hu h ↦ ?_⟩
  have hq : (p, (z, u z)) ∈ C ×ˢ (D ×ˢ K) := ⟨hp, hz, hu⟩
  refine (ω.norm_fderiv_stdComplexLineReal_sq_le hc (fun v ↦ by simpa [Jc] using hJc _ hq v)
    h).trans ?_
  have hXB : ‖ω.hamiltonianVectorField (Ks p z) (u z)‖ ≤ B := by simpa using hB _ hq
  gcongr

omit [FiniteDimensional ℝ V] in
/-- If `‖∂ₛu‖² ≤ A f + B` on an open set `Ω` of finite measure, where `f` is integrable on `Ω`, and
`u` is `C¹` on `Ω`, then `‖∂ₛu‖²` is integrable on `Ω`. -/
private theorem integrableOn_norm_fderiv_stdComplexLineReal_sq_of_le {u : ℝ × ℝ → V}
    {f : ℝ × ℝ → ℝ} {Ω : Set (ℝ × ℝ)} {A B : ℝ} (hΩ : IsOpen Ω) (hΩfin : volume Ω ≠ ⊤)
    (hu : ContDiffOn ℝ 1 u Ω) (hint : IntegrableOn f Ω)
    (hle : ∀ z ∈ Ω, ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 ≤ A * f z + B) :
    IntegrableOn (fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2) Ω :=
  Integrable.mono' ((hint.const_mul A).fun_add (integrableOn_const (C := B) hΩfin))
    ((((hu.continuousOn_fderiv_of_isOpen hΩ le_rfl).clm_apply
      continuousOn_const).norm.pow 2).aestronglyMeasurable hΩ.measurableSet)
    (ae_restrict_of_forall_mem hΩ.measurableSet fun z hz ↦ by
      rw [Real.norm_of_nonneg (by positivity)]
      exact hle z hz)

omit [FiniteDimensional ℝ V] in
/-- If `‖∂ₛu‖² ≤ A f + B` on a measurable set `S` of finite measure, with `A, B ≥ 0` and `f ≥ 0`,
then `∫_S ‖∂ₛu‖² ≤ (A + B + 1)(|S| + ∫_S f)`. -/
private theorem setIntegral_norm_fderiv_stdComplexLineReal_sq_le_of_le {u : ℝ × ℝ → V}
    {f : ℝ × ℝ → ℝ} {S : Set (ℝ × ℝ)} {A B : ℝ} (hS : MeasurableSet S) (hSfin : volume S ≠ ⊤)
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (hgint : IntegrableOn (fun z ↦ ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2) S)
    (hint : IntegrableOn f S) (hf0 : ∀ z ∈ S, 0 ≤ f z)
    (hle : ∀ z ∈ S, ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 ≤ A * f z + B) :
    ∫ z in S, ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2 ≤
      (A + B + 1) * (volume.real S + ∫ z in S, f z) := by
  have hint0 : 0 ≤ ∫ z in S, f z := setIntegral_nonneg hS hf0
  have hm0 : 0 ≤ volume.real S := measureReal_nonneg
  calc ∫ z in S, ‖fderiv ℝ u z stdComplexLineReal‖ ^ 2
      ≤ ∫ z in S, (A * f z + B) :=
        setIntegral_mono_on hgint ((hint.const_mul A).fun_add (integrableOn_const (C := B) hSfin))
          hS hle
    _ = A * (∫ z in S, f z) + B * volume.real S := by
        rw [integral_add (hint.const_mul A) (integrableOn_const hSfin), integral_const_mul,
          setIntegral_const, smul_eq_mul, mul_comm (volume.real S)]
    _ ≤ (A + B + 1) * (volume.real S + ∫ z in S, f z) := by
        nlinarith [mul_nonneg hA0 hm0, mul_nonneg hB0 hint0]

omit [FiniteDimensional ℝ V] in
/-- `equivRealProdCLM` preserves volume, and in the complex coordinate the density `‖∂ₛw‖²` is
`‖∂ₛ(w ∘ equivRealProdCLM)‖²`, so the two are integrable together. -/
private theorem integrableOn_norm_fderiv_comp_equivRealProdCLM_one_sq_iff (w : ℝ × ℝ → V)
    (S : Set (ℝ × ℝ)) :
    IntegrableOn (fun y ↦ ‖fderiv ℝ (w ∘ equivRealProdCLM) y 1‖ ^ 2) (equivRealProdCLM ⁻¹' S) ↔
      IntegrableOn (fun z ↦ ‖fderiv ℝ w z stdComplexLineReal‖ ^ 2) S := by
  simp only [fderiv_comp_equivRealProdCLM_one]
  exact Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
    equivRealProdCLM.toHomeomorph.measurableEmbedding
    (f := fun z ↦ ‖fderiv ℝ w z stdComplexLineReal‖ ^ 2) (s := S)

omit [FiniteDimensional ℝ V] in
/-- The energy `∫ ‖∂ₛw‖²` does not change in the complex coordinate `equivRealProdCLM`. -/
private theorem setIntegral_norm_fderiv_comp_equivRealProdCLM_one_sq (w : ℝ × ℝ → V)
    (S : Set (ℝ × ℝ)) :
    ∫ y in equivRealProdCLM ⁻¹' S, ‖fderiv ℝ (w ∘ equivRealProdCLM) y 1‖ ^ 2 =
      ∫ z in S, ‖fderiv ℝ w z stdComplexLineReal‖ ^ 2 := by
  simp only [fderiv_comp_equivRealProdCLM_one]
  exact Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    equivRealProdCLM.toHomeomorph.measurableEmbedding
    (fun z ↦ ‖fderiv ℝ w z stdComplexLineReal‖ ^ 2) S

/-- `TauCeti.Floer.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset` for
solutions of the Floer equations `(du - X_{K_p})^{0,1} = 0` on the domain `ℝ × ℝ`, read through the
complex coordinate `equivRealProdCLM`; the energy is `∫ ‖∂ₛu‖²`. -/
private theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_of_norm
    (ω : SymplecticForm V) {W : Set (P × ((ℝ × ℝ) × V))} {C : Set P}
    {D : Set (ℝ × ℝ)} {K : Set V} (hW : IsOpen W)
    (hX : ContDiffOn ℝ 2
      (fun q : P × ((ℝ × ℝ) × V) ↦ ω.hamiltonianOneForm (Ks q.1) (Kt q.1) q.2.1 q.2.2) W)
    (hJ : ContDiffOn ℝ 2 (fun q : P × ((ℝ × ℝ) × V) ↦
      (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, p k ∈ C) → (∀ k, ContDiffOn ℝ 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
        (ω.perturbedFDeriv (Ks (p k)) (Kt (p k)) (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (fun z ↦ ‖fderiv ℝ (u k) z stdComplexLineReal‖ ^ 2) Ω) →
      (∀ k, ∫ z in Ω, ‖fderiv ℝ (u k) z stdComplexLineReal‖ ^ 2 ≤ E) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ p₀ ∈ C ∧
        Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ‖fderiv ℝ (u (φ n)) y stdComplexLineReal‖ ^ 2) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  classical
  set e : ℂ ≃L[ℝ] ℝ × ℝ := equivRealProdCLM with he
  set g : P × (ℂ × V) → P × ((ℝ × ℝ) × V) := fun q ↦ (q.1, (e q.2.1, q.2.2))
  have hg {n : WithTop ℕ∞} : ContDiff ℝ n g := contDiff_fst.prodMk
    ((e.contDiff.comp (contDiff_fst.comp contDiff_snd)).prodMk (contDiff_snd.comp contDiff_snd))
  obtain ⟨δ, hδ, hconv⟩ :=
    Floer.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (J := fun p y ↦ (J p (e y.1) y.2).toLinearMap.toContinuousLinearMap)
    (X := fun p y ↦ ω.hamiltonianOneForm (Ks p) (Kt p) (e y.1) y.2 ∘L (e : ℂ →L[ℝ] ℝ × ℝ))
    (hW.preimage (hg (n := 0)).continuous) (hJ.comp hg.contDiffOn (mapsTo_preimage g W))
    ((hX.comp hg.contDiffOn (mapsTo_preimage g W)).clm_comp
      (contDiffOn_const (c := (e : ℂ →L[ℝ] ℝ × ℝ))))
    hC (e.toHomeomorph.isCompact_preimage.2 hD) hK (fun q hq ↦ hCDKW ⟨hq.1, hq.2.1, hq.2.2⟩)
    (fun _ _ _ _ _ _ v ↦ by simp)
  refine ⟨δ, hδ, fun Ω p u E hΩ hΩD hpC hu hfl huK hint hE ↦ ?_⟩
  obtain ⟨φ, p₀, Z', v', hφ, hp₀, hplim, hZ'Ω, -, hconc', hbd', hvc', hvK', hlim'⟩ :=
    hconv (Ω := e ⁻¹' Ω) (p := p) (u := fun k ↦ u k ∘ e) (E := E)
      (hΩ.preimage e.continuous) (preimage_mono hΩD) hpC
      (fun k ↦ (hu k).comp e.contDiff.contDiffOn (mapsTo_preimage _ _))
      (fun k y hy ↦ by simpa [he] using ω.fderiv_comp_equivRealProdCLM_I_sub (hfl k (e y) hy))
      (fun k y hy ↦ huK k hy)
      (fun k ↦ (integrableOn_norm_fderiv_comp_equivRealProdCLM_one_sq_iff (u k) Ω).2 (hint k))
      (fun k ↦ (setIntegral_norm_fderiv_comp_equivRealProdCLM_one_sq (u k) Ω).trans_le (hE k))
  -- The bubbling set and the limit in the original coordinates.
  set Z : Finset (ℝ × ℝ) := Z'.image e with hZ_def
  have hpreZ : e ⁻¹' (Ω \ ↑Z) = e ⁻¹' Ω \ ↑Z' := by
    rw [preimage_sdiff, hZ_def, Finset.coe_image, e.injective.preimage_image]
  have hsymm : MapsTo e.symm (Ω \ ↑Z) (e ⁻¹' Ω \ ↑Z') := fun y hy ↦ by
    rw [← hpreZ]
    simpa using hy
  have hu_symm (k : ℕ) : (u k ∘ e) ∘ e.symm = u k := funext fun z ↦ by simp
  refine ⟨φ, p₀, Z, v' ∘ e.symm, hφ, hp₀, hplim, ?_, fun z hz ε hε ↦ ?_, fun C' hC' hC'Z ↦ ?_,
    hvc'.comp e.symm.continuous.continuousOn hsymm, fun y hy ↦ hvK' (hsymm hy), ?_⟩
  · rw [hZ_def, Finset.coe_image]
    exact image_subset_iff.2 hZ'Ω
  · -- A disc of `ℂ` lies in the disc of `ℝ × ℝ` of the same radius about the image point.
    obtain ⟨z', hz', rfl⟩ := Finset.mem_image.1 hz
    have hsub : ball z' ε ∩ e ⁻¹' Ω ⊆ e ⁻¹' (ball (e z') ε ∩ Ω) := fun y hy ↦
      ⟨(lipschitz_equivRealProd.dist_le_mul y z').trans_lt (by simpa using hy.1), hy.2⟩
    filter_upwards [hconc' z' hz' ε hε] with n hn
    rw [← setIntegral_norm_fderiv_comp_equivRealProdCLM_one_sq]
    exact hn.trans (setIntegral_mono_set
      ((integrableOn_norm_fderiv_comp_equivRealProdCLM_one_sq_iff _ _).2
        ((hint (φ n)).mono_set inter_subset_right))
      (Eventually.of_forall fun _ ↦ by positivity) hsub.eventuallyLE)
  · obtain ⟨M', hM'⟩ := hbd' (e ⁻¹' C') (e.toHomeomorph.isCompact_preimage.2 hC')
      (hpreZ ▸ preimage_mono hC'Z)
    refine ⟨M' * ‖(e.symm : ℝ × ℝ →L[ℝ] ℂ)‖, fun n y hy ↦ ?_⟩
    have hd := e.symm.comp_right_fderiv (f := u (φ n) ∘ e) (x := y)
    rw [hu_symm] at hd
    rw [hd]
    exact (opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hM' n _ (by simpa using hy)) (norm_nonneg _))
  · simpa only [hu_symm] using hlim'.comp e.symm hsymm e.symm.continuous.continuousOn

/-- **Floer solutions over a compact parameter window converge off finitely many bubbling
points.** Let `K_p = K_{p,s} ds + K_{p,t} dt` and `J_p(z, x)` depend on a parameter `p` of a real
inner product space `P`, jointly `C³` and `C²` with `z ∈ ℝ × ℝ` and `x ∈ V` on an open set
`W ⊆ P × ((ℝ × ℝ) × V)` containing `C × D × K` for compact `C ⊆ P`, `D ⊆ ℝ × ℝ` and `K ⊆ V`, with
`J_p(z, x)` tamed by `ω` on `C × D × K`. There is a threshold `δ > 0` with the following property.
Let `uₖ` be `C³` solutions of the Floer equation `(du - X_{K_{pₖ}})^{0,1} = 0` for `J_{pₖ}(z, u)`
on an open set `Ω ⊆ D`, for parameters `pₖ ∈ C`, with image in `K` and Floer energy
`∫_Ω ω(∂ₛuₖ - X_{K_{pₖ,s}}, ∂ₜuₖ - X_{K_{pₖ,t}}) ≤ E`. Then there are a subsequence `φ`, a limit
`p₀ ∈ C` of the parameters `p_{φ n}`, a finite set `Z ⊆ Ω` with `#Z * δ ≤ E`, and a continuous
`v : Ω \ Z → K` such that along `φ` every disc about a point of `Z` eventually carries Floer energy
at least `δ`, the differentials are uniformly bounded on every compact subset of `Ω \ Z`, and
`u_{φ n} → v` locally uniformly on `Ω \ Z`. -/
theorem exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset
    (ω : SymplecticForm V) {W : Set (P × ((ℝ × ℝ) × V))} {C : Set P}
    {D : Set (ℝ × ℝ)} {K : Set V} (hW : IsOpen W)
    (hKs : ContDiffOn ℝ 3 (fun q : P × ((ℝ × ℝ) × V) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContDiffOn ℝ 3 (fun q : P × ((ℝ × ℝ) × V) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContDiffOn ℝ 2 (fun q : P × ((ℝ × ℝ) × V) ↦
      (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, ω.Tames (J p z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → V⦄ ⦃E : ℝ⦄, IsOpen Ω → Ω ⊆ D →
      (∀ k, p k ∈ C) → (∀ k, ContDiffOn ℝ 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
        (ω.perturbedFDeriv (Ks (p k)) (Kt (p k)) (u k) z : ℝ × ℝ →ₗ[ℝ] V)) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) z ≤ E) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → V), StrictMono φ ∧ p₀ ∈ C ∧
        Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ E ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop, δ ≤ ∫ y in ball z ε ∩ Ω,
          ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n))) (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M, ∀ n, ∀ y ∈ C', ‖fderiv ℝ (u (φ n)) y‖ ≤ M) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        TendstoLocallyUniformlyOn (fun n ↦ u (φ n)) v atTop (Ω \ ↑Z) := by
  have hX := ω.contDiffOn_hamiltonianOneForm_parameter (n := 2) hW hKs hKt
  obtain ⟨A, hA0, B, hB0, hpt⟩ :=
    ω.exists_forall_norm_fderiv_stdComplexLineReal_sq_le_of_parameter (Ks := Ks) (Kt := Kt) hC hD
    hK (hJ.continuousOn.mono hCDKW)
    ((hX.continuousOn.mono hCDKW).clm_apply (continuousOn_const (c := stdComplexLineReal)) |>.congr
      fun q _ ↦ by simp)
    hJt
  obtain ⟨δ₀, hδ₀, hconv⟩ :=
    ω.exists_pos_forall_tendsto_tendstoLocallyUniformlyOn_subseq_off_finset_of_norm hW hX hJ hC hD
      hK hCDKW
  have hC₀0 : 0 < A + B + 1 := by positivity
  refine ⟨δ₀ / (2 * (A + B + 1)), by positivity, fun Ω p u E hΩ hΩD hpC hu hfl huK hint hE ↦ ?_⟩
  have hΩm : MeasurableSet Ω := hΩ.measurableSet
  have hΩfin : volume Ω ≠ ⊤ := ((measure_mono hΩD).trans_lt hD.measure_lt_top).ne
  -- On `Ω`, the energy density `f k` is nonnegative and bounds `‖∂ₛuₖ‖²` up to a constant.
  set f : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) with hf_def
  have hf0 (k : ℕ) : ∀ z ∈ Ω, 0 ≤ f k z := fun z hz ↦
    ω.floerEnergyDensity_nonneg (hJt _ (hpC k) z (hΩD hz) _ (huK k hz)) (hfl k z hz)
  have hgle (k : ℕ) : ∀ z ∈ Ω, ‖fderiv ℝ (u k) z stdComplexLineReal‖ ^ 2 ≤ A * f k z + B :=
    fun z hz ↦ hpt (hpC k) (hΩD hz) (huK k hz) (hfl k z hz)
  have hgint (k : ℕ) := integrableOn_norm_fderiv_stdComplexLineReal_sq_of_le hΩ hΩfin
    ((hu k).of_le (by norm_num)) (hint k) (hgle k)
  have hgS (k : ℕ) {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω) :=
    setIntegral_norm_fderiv_stdComplexLineReal_sq_le_of_le hS
      (ne_top_of_le_ne_top hΩfin (measure_mono hSΩ)) hA0 hB0 ((hgint k).mono_set hSΩ)
      ((hint k).mono_set hSΩ) (fun z hz ↦ hf0 k z (hSΩ hz)) fun z hz ↦ hgle k z (hSΩ hz)
  obtain ⟨φ, p₀, Z, v, hφ, hp₀, hplim, hZΩ, hconc', hbd, hvc, hvK, hlim⟩ :=
    hconv hΩ hΩD hpC hu hfl huK hgint fun k ↦ (hgS k hΩm le_rfl).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add (measureReal_mono hΩD hD.measure_lt_top.ne) (hE k)) hC₀0.le)
  -- Energy `δ₀` of `∂ₛu` concentrating at a point gives Floer energy `δ₀ / (2 (A + B + 1))`
  -- there, since small discs have small area.
  have hconc : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
      δ₀ / (2 * (A + B + 1)) ≤ ∫ y in ball z ε ∩ Ω, f (φ n) y := by
    intro z hz ε hε
    refine eventually_le_setIntegral_ball_of_le_measureReal_add_setIntegral_ball
      (δ := δ₀ / (A + B + 1))
      hΩm (by rw [Measure.volume_eq_prod]; exact measure_singleton _)
      ⟨1, one_pos, measure_ball_lt_top.ne⟩ (fun n ↦ hf0 (φ n))
      (fun n ↦ hint (φ n)) ?_ hε fun ρ hρ ↦ ?_
    · rw [mul_comm, ← div_div]
      exact half_lt_self (by positivity)
    filter_upwards [hconc' z hz ρ hρ] with n hn
    have h := hgS (φ n) (S := ball z ρ ∩ Ω) (measurableSet_ball.inter hΩm) inter_subset_right
    rw [div_le_iff₀ hC₀0]
    simp only [hf_def] at h ⊢
    linarith
  exact ⟨φ, p₀, Z, v, hφ, hp₀, hplim, hZΩ, card_mul_le_of_forall_eventually_le_setIntegral_ball hΩm
    (fun n ↦ hf0 (φ n)) (fun n ↦ hint (φ n)) (fun n ↦ hE (φ n)) hconc, hconc, hbd, hvc, hvK,
    hlim⟩

end TauCeti.SymplecticForm
