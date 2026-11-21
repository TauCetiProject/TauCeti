/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import TauCeti.Analysis.Hofer
import TauCeti.Geometry.Manifold.ExtChartAt
import TauCeti.Geometry.Manifold.SmoothEmbedding.Euclidean
import TauCeti.Geometry.Symplectic.Floer.Compactness.BoundedDensity
import TauCeti.Geometry.Symplectic.Floer.Compactness.MeanValue

/-!
# Energy quantization for Floer solutions on a manifold

Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M` modelled on a
finite-dimensional real normed space `E`, such as a closed symplectic manifold. Let `K_s, K_t` be
families of Hamiltonians and `J(p, z, x)` a family of `ω`-tame almost complex structures on the
tangent spaces of `M`, depending on a parameter `p` in a real inner product space `P`, a domain
point `z ∈ ℝ × ℝ` and a target point `x ∈ M`, with `(K_s, K_t)` jointly `C³` and `J` jointly `C²`
on an open neighbourhood `W` of a compact window `C × D × K`.

This file establishes uniform energy quantization at blow-up points on `M`
(`TauCeti.SmoothTwoForm.IsNondegenerate.`
`exists_pos_forall_eventually_le_setIntegral_ball_of_tendsto_floerEnergyDensity`): there is `δ > 0`
such that whenever `e(u_k)(z_k) → ∞` along `z_k → z₀ ∈ Ω`, every disc `ball z₀ ε ∩ Ω` eventually
carries Floer energy at least `δ`. The proof combines Hofer's lemma, the Euclidean embedding
derivative bound from `TauCeti.Geometry.Symplectic.Floer.Compactness.BoundedDensity`, and a
finite chart localization of the parametric mean-value inequality from
`TauCeti.Geometry.Symplectic.Floer.Compactness.MeanValue`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Section 4.6 (bubbling off finitely many points) and Section 8.1
  (inhomogeneous equations).
* H. Hofer and C. Viterbo, *The Weinstein conjecture in the presence of holomorphic spheres*,
  Comm. Pure Appl. Math. **45** (1992), 583–622 (Hofer's lemma).
-/

public section

noncomputable section

open Bundle Filter Function MeasureTheory Metric Real Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- **Localized intrinsic mean-value inequality relative to an embedding.** Given a smooth embedding
`emb : W_emb → ℝ^N` covering `K` with total extension `eM`, produces a Lebesgue number `η > 0` and
uniform MVI constants `(δ_mvi, M₁, M₂, M₃)` on discs whose embedded image has diameter `< η`. -/
private theorem exists_localized_mvi [I.Boundaryless] [T2Space M]
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set M} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J p z x))
    {W_emb : TopologicalSpace.Opens M} {N : ℕ}
    (emb : SmoothEmbedding I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) W_emb
      (EuclideanSpace ℝ (Fin N)))
    {eM : M → EuclideanSpace ℝ (Fin N)} (hKW : K ⊆ (W_emb : Set M))
    (heM_eq : ∀ x (hx : x ∈ (W_emb : Set M)), eM x = emb ⟨x, hx⟩)
    (heM_cmd : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (⊤ : ℕ∞) eM W_emb) :
    ∃ η > 0, ∃ δ_mvi > 0, ∃ M₁ > 0, ∃ M₂ > 0, ∃ M₃ ≥ 0,
      ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃c : ℝ × ℝ⦄ ⦃r : ℝ⦄,
        IsOpen Ω → Ω ⊆ D → p ∈ C → 0 ≤ r → closedBall c r ⊆ Ω →
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω → MapsTo u Ω K →
        (∀ z ∈ closedBall c r, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
          (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap) →
        (∀ z ∈ closedBall c r, dist (eM (u z)) (eM (u c)) < η) →
        M₁ * (π * r ^ 2) + M₂ * ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z <
          δ_mvi →
        π * r ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u c ≤
          M₃ * (π * r ^ 2 + ∫ z in ball c r, ω.floerEnergyDensity (Ks p) (Kt p) u z) := by
  classical
  have hW_swap : IsOpen ((fun q : (P × (ℝ × ℝ)) × M ↦ (q.1.1, (q.1.2, q.2))) ⁻¹' W) :=
    hW.preimage ((continuous_fst.comp continuous_fst).prodMk
      ((continuous_snd.comp continuous_fst).prodMk continuous_snd))
  obtain ⟨U₁, U₂, -, hU₂, hCDU₁, hKU₂, hprod⟩ :=
    generalized_tube_lemma (hC.prod hD) hK hW_swap fun ⟨⟨p, z⟩, x⟩ ⟨⟨hp, hz⟩, hx⟩ ↦
      hCDKW ⟨hp, hz, hx⟩
  let : LocallyCompactSpace H := I.isClosedEmbedding.locallyCompactSpace
  obtain ⟨n, -, α, u_cov, b, hcov, hsK_cov⟩ :=
    exists_finite_precompact_chart_cover_of_isOpen_cover (I := I) hK
      (V := fun _ : Unit ↦ U₂ ∩ W_emb) (fun _ ↦ hU₂.inter W_emb.isOpen)
      fun x hx ↦ mem_iUnion.2 ⟨(), hKU₂ hx, hKW hx⟩
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exact ⟨1, one_pos, 1, one_pos, 1, one_pos, 1, one_pos, 0, le_rfl,
      fun _ _ _ _ _ _ _ _ hr hcr _ huK _ _ _ ↦ by
        obtain ⟨i, -⟩ := mem_iUnion.1 (hsK_cov (huK (hcr (mem_closedBall_self hr))))
        exact (hn.false i).elim⟩
  have hchart : ∀ i : Fin n,
      ∃ δ_i > 0, ∃ M₁_i > 0, ∃ M₂_i > 0, ∃ M₃_i ≥ 0,
        ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : P⦄ ⦃u : ℝ × ℝ → M⦄ ⦃c : ℝ × ℝ⦄ ⦃r' : ℝ⦄,
          IsOpen Ω → Ω ⊆ D → p ∈ C → 0 ≤ r' → closedBall c r' ⊆ Ω →
          ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 u Ω → MapsTo u Ω K → MapsTo u (closedBall c r') (u_cov i) →
          (∀ z ∈ closedBall c r',
            IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p z (u z))
              (ω.perturbedMFDeriv (Ks p) (Kt p) u z).toLinearMap) →
          M₁_i * (π * r' ^ 2) + M₂_i * ∫ z in ball c r', ω.floerEnergyDensity (Ks p) (Kt p) u z <
            δ_i →
          π * r' ^ 2 * ω.floerEnergyDensity (Ks p) (Kt p) u c ≤
            M₃_i * (π * r' ^ 2 + ∫ z in ball c r', ω.floerEnergyDensity (Ks p) (Kt p) u z) := by
    intro i
    have hi := hcov i
    let Kα : Set E := b i ∩ (extChartAt I (α i)).symm ⁻¹' K
    have hKα_comp : IsCompact Kα := by
      have hcl : IsClosed Kα :=
        ((continuousOn_extChartAt_symm (α i)).mono
          hi.2.2.2.2.2.1).preimage_isClosed_of_isClosed hi.2.2.2.2.1.isClosed hK.isClosed
      exact hi.2.2.2.2.1.of_isClosed_subset hcl inter_subset_left
    have hKα_tgt : Kα ⊆ (extChartAt I (α i)).target :=
      inter_subset_left.trans hi.2.2.2.2.2.1
    have hKα_W : C ×ˢ (D ×ˢ ((extChartAt I (α i)).symm '' Kα)) ⊆ W := by
      rintro ⟨p, z, _⟩ ⟨hp, hz, y, hy, rfl⟩
      exact @hprod ((p, z), (extChartAt I (α i)).symm y)
        ⟨hCDU₁ ⟨hp, hz⟩, (hi.2.2.2.2.2.2.1 hy.1).1⟩
    have hKα_tame : ∀ p ∈ C, ∀ z ∈ D, ∀ y ∈ Kα,
        (hω.symplecticFormAt ((extChartAt I (α i)).symm y)).Tames
          (J p z ((extChartAt I (α i)).symm y)) :=
      fun p hp z hz _ hy ↦ hJt p hp z hz _ hy.2
    obtain ⟨δ_i, hδi, M₁_i, hM₁i, M₂_i, hM₂i, M₃_i, hM₃i, hmvi_i⟩ :=
      hω.exists_pos_forall_pi_mul_sq_mul_floerEnergyDensity_le_inChart (α i) hW hKs hKt hJ hC hD
        hKα_comp hKα_tgt hKα_W hKα_tame
    refine ⟨δ_i, hδi, M₁_i, hM₁i, M₂_i, hM₂i, M₃_i, hM₃i,
      fun Ω p u c r' hΩ hΩD hp hr' hcr hu huK huV hfl hsmall ↦ ?_⟩
    refine hmvi_i hΩ hΩD hp hr' hcr hu hfl (fun z hz ↦ ?_) hsmall
    have hzi := huV hz
    exact ⟨hi.2.2.2.1 hzi, hi.2.2.2.2.2.2.2 (mem_image_of_mem _ hzi), by
      rw [mem_preimage, (extChartAt I (α i)).left_inv (hi.2.2.2.1 hzi)]; exact huK (hcr hz)⟩
  choose δ_i hδi M₁_i hM₁i M₂_i hM₂i M₃_i hM₃i hmvi_i using hchart
  set δ_mvi := (Finset.univ : Finset (Fin n)).inf' Finset.univ_nonempty δ_i
  set M₁ := (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty M₁_i
  set M₂ := (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty M₂_i
  set M₃ := (Finset.univ : Finset (Fin n)).sup' Finset.univ_nonempty M₃_i
  have hδmvi_pos : 0 < δ_mvi := (Finset.lt_inf'_iff Finset.univ_nonempty).2 fun i _ ↦ hδi i
  have hM₁_pos : 0 < M₁ := by
    obtain ⟨i⟩ := hn; exact (hM₁i i).trans_le (Finset.le_sup' M₁_i (Finset.mem_univ i))
  have hM₂_pos : 0 < M₂ := by
    obtain ⟨i⟩ := hn; exact (hM₂i i).trans_le (Finset.le_sup' M₂_i (Finset.mem_univ i))
  have hM₃_nn : 0 ≤ M₃ := by
    obtain ⟨i⟩ := hn; exact (hM₃i i).trans (Finset.le_sup' M₃_i (Finset.mem_univ i))
  have hO_ex : ∀ i : Fin n, ∃ O : Set (EuclideanSpace ℝ (Fin N)),
      IsOpen O ∧ emb ⁻¹' O = ((↑) : W_emb → M) ⁻¹' u_cov i := fun i ↦
    emb.isEmbedding.isInducing.isOpen_iff.1 ((hcov i).2.1.preimage continuous_subtypeVal)
  choose O hO_open hO_eq using hO_ex
  have heMK_comp : IsCompact (eM '' K) := hK.image_of_continuousOn (heM_cmd.continuousOn.mono hKW)
  have heMK_cov : eM '' K ⊆ ⋃ i : Fin n, O i := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.1 (hsK_cov hx)
    refine mem_iUnion.2 ⟨i, ?_⟩
    rw [heM_eq x (hKW hx)]
    exact (Set.ext_iff.1 (hO_eq i) ⟨x, hKW hx⟩).2 hxi
  obtain ⟨η, hη, hLeb⟩ := lebesgue_number_lemma_of_metric heMK_comp hO_open heMK_cov
  refine ⟨η, hη, δ_mvi, hδmvi_pos, M₁, hM₁_pos, M₂, hM₂_pos, M₃, hM₃_nn,
    fun Ω p u c r' hΩ hΩD hp hr' hcr hu huK hfl hdist hsmall ↦ ?_⟩
  obtain ⟨i, hballO⟩ := hLeb (eM (u c)) ⟨u c, huK (hcr (mem_closedBall_self hr')), rfl⟩
  have huV : MapsTo u (closedBall c r') (u_cov i) := by
    intro z hz
    have hzO : eM (u z) ∈ O i := hballO (hdist z hz)
    rw [heM_eq (u z) (hKW (huK (hcr hz)))] at hzO
    exact (Set.ext_iff.1 (hO_eq i) ⟨u z, hKW (huK (hcr hz))⟩).1 hzO
  have hint_nn : 0 ≤ ∫ z in ball c r', ω.floerEnergyDensity (Ks p) (Kt p) u z :=
    setIntegral_nonneg measurableSet_ball fun z hz ↦
      floerEnergyDensity_nonneg hω
        (hJt p hp z (hΩD (hcr (ball_subset_closedBall hz))) (u z)
          (huK (hcr (ball_subset_closedBall hz))))
        (hfl z (ball_subset_closedBall hz))
  have hπr_nn : 0 ≤ π * r' ^ 2 := by positivity
  have hδ_le : δ_mvi ≤ δ_i i := Finset.inf'_le δ_i (Finset.mem_univ i)
  have hM₁_le : M₁_i i ≤ M₁ := Finset.le_sup' M₁_i (Finset.mem_univ i)
  have hM₂_le : M₂_i i ≤ M₂ := Finset.le_sup' M₂_i (Finset.mem_univ i)
  have hM₃_le : M₃_i i ≤ M₃ := Finset.le_sup' M₃_i (Finset.mem_univ i)
  have hres := hmvi_i i hΩ hΩD hp hr' hcr hu huK huV hfl (by nlinarith)
  nlinarith

/-- **Energy quantization at blow-up points on a manifold.** Let `ω` be a nondegenerate two-form
on a Hausdorff boundaryless manifold `M` modelled on a finite-dimensional space `E`. Let `K_s, K_t`
be jointly `C³` and `J` jointly `C²` on an open set `W ⊆ P × ((ℝ × ℝ) × M)` containing `C × D × K`
for compact `C ⊆ P`, `D ⊆ ℝ × ℝ` and `K ⊆ M`, with `J(p, z, x)` tamed by `ω` on `C × D × K`.
There is a quantum `δ > 0` such that whenever `C³` Floer solutions `u_k` on an open `Ω ⊆ D` for
parameters `p_k ∈ C`, with values in `K`, have energy densities `e(u_k)(z_k) → ∞` along points
`z_k → z₀ ∈ Ω`, every disc `ball z₀ ε ∩ Ω` eventually carries Floer energy at least `δ`. -/
theorem exists_pos_forall_eventually_le_setIntegral_ball_of_tendsto_floerEnergyDensity
    [I.Boundaryless] [T2Space M] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} {K : Set M} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hK : IsCompact K) (hCDKW : C ×ˢ (D ×ˢ K) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J p z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃z : ℕ → ℝ × ℝ⦄ ⦃z₀ : ℝ × ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, p k ∈ C) →
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) y (u k y))
        (ω.perturbedMFDeriv (Ks (p k)) (Kt (p k)) (u k) y).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)) Ω) →
      z₀ ∈ Ω → Tendsto z atTop (𝓝 z₀) →
      Tendsto (fun k ↦ ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) (z k)) atTop atTop →
      ∀ ε > 0, ∀ᶠ k in atTop,
        δ ≤ ∫ y in ball z₀ ε ∩ Ω, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) y := by
  have hXsM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKs
  have hXtM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKt
  obtain ⟨W_emb, N, emb, eM, hKW, heM_eq, heM_cmd, A_e, hAe, B_e, hBe, hbd_e⟩ :=
    hω.exists_opens_smoothEmbedding_norm_fderiv_sq_le hW hJ.continuousOn hXsM.continuousOn
      hXtM.continuousOn hC hD hK hCDKW hJt
  obtain ⟨η, hη, δ_mvi, hδmvi, M₁, -, M₂, hM₂, M₃, hM₃, hmvi⟩ :=
    hω.exists_localized_mvi hW hKs hKt hJ hC hD hK hCDKW hJt emb hKW heM_eq heM_cmd
  set c₀ := η / (4 * √A_e)
  have hc₀ : 0 < c₀ := by positivity
  set δ := min (δ_mvi / (2 * M₂)) ((π * c₀ ^ 2) / (2 * (M₃ + 1)))
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  refine ⟨δ, hδ, fun Ω p u z z₀ hΩ hΩD hpC hu hfl huK hint hz₀ hz hblow ε hε ↦ ?_⟩
  -- Step 1: Continuity and nonnegativity of `e_k`, then apply Hofer's lemma to `√(e_k)`.
  set e : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)
  have he_nn (k : ℕ) {y : ℝ × ℝ} (hy : y ∈ Ω) : 0 ≤ e k y :=
    floerEnergyDensity_nonneg hω (hJt (p k) (hpC k) y (hΩD hy) (u k y) (huK k hy)) (hfl k y hy)
  have he_cont (k : ℕ) : ContinuousOn (e k) Ω :=
    ω.continuousOn_floerEnergyDensity_of_isOpen_prod hW hXsM.continuousOn hXtM.continuousOn hΩ
      Subset.rfl ((hu k).of_le (by norm_num)) fun y hy ↦ hCDKW ⟨hpC k, hΩD hy, huK k hy⟩
  obtain ⟨r, hr, hrsub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    ((isOpen_ball.inter hΩ).mem_nhds ⟨mem_ball_self hε, hz₀⟩)
  obtain ⟨c, ρ, -, hc, -, hρl, hhof⟩ := exists_tendsto_hofer hr
    (fun k ↦ (he_cont k).mono (hrsub.trans inter_subset_right) |>.sqrt)
    (fun _ _ _ ↦ Real.sqrt_nonneg _) hz (Real.tendsto_sqrt_atTop.comp hblow)
  -- Step 2: Choose scales `s_k = c₀ / √(e_k(c_k)) → 0` so `eM ∘ u_k` stays within `< η` on
  -- `closedBall (c k) (s k)` and area terms become negligible.
  set lam : ℕ → ℝ := fun k ↦ √(e k (c k))
  have hlam : Tendsto lam atTop atTop :=
    tendsto_atTop_mono' atTop (hhof.mono fun k hk ↦ hk.1) (Real.tendsto_sqrt_atTop.comp hblow)
  set s : ℕ → ℝ := fun k ↦ c₀ / lam k
  have hs0 : Tendsto s atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlam
  have hsc_in : ∀ᶠ k in atTop, closedBall (c k) (s k) ⊆ ball z₀ ε ∩ Ω := by
    have hsum : Tendsto (fun k ↦ s k + dist (c k) z₀) atTop (𝓝 0) := by
      simpa using hs0.add (tendsto_iff_dist_tendsto_zero.1 hc)
    filter_upwards [hsum.eventually (gt_mem_nhds hr)] with k hk
    exact (closedBall_subset_closedBall' hk.le).trans hrsub
  have hs_le_ρ : ∀ᶠ k in atTop, s k ≤ ρ k := by
    filter_upwards [hlam.eventually_gt_atTop 0, hρl.eventually_ge_atTop c₀] with k hlk hrl
    exact (div_le_iff₀ hlk).2 (by linarith)
  have hB_small : ∀ᶠ k in atTop, √B_e * c₀ / lam k < η / 2 :=
    (tendsto_const_nhds.div_atTop hlam).eventually (gt_mem_nhds (half_pos hη))
  have hM₁_small : ∀ᶠ k in atTop, M₁ * (π * s k ^ 2) < δ_mvi / 2 := by
    have hlim : Tendsto (fun k ↦ M₁ * (π * s k ^ 2)) atTop (𝓝 0) := by
      simpa using (hs0.pow 2).const_mul π |>.const_mul M₁
    exact hlim.eventually (gt_mem_nhds (half_pos hδmvi))
  have hM₃_small : ∀ᶠ k in atTop, M₃ * (π * s k ^ 2) < (π * c₀ ^ 2) / 2 := by
    have hlim : Tendsto (fun k ↦ M₃ * (π * s k ^ 2)) atTop (𝓝 0) := by
      simpa using (hs0.pow 2).const_mul π |>.const_mul M₃
    exact hlim.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hhof, hlam.eventually_gt_atTop 0, hsc_in, hs_le_ρ, hB_small, hM₁_small,
    hM₃_small] with k hk hlk hsc hsr hBs hM₁s hM₃s
  have hsk_nn : 0 ≤ s k := by positivity
  -- Step 3: Use the mean-value theorem on `eM ∘ u_k` to keep `closedBall (c k) (s k)` within `< η`.
  have hdist : ∀ y ∈ closedBall (c k) (s k), dist (eM (u k y)) (eM (u k (c k))) < η := by
    intro y hy
    have heM_diff : ∀ w ∈ closedBall (c k) (s k), DifferentiableAt ℝ (eM ∘ u k) w := fun w hw ↦ by
      have hwΩ : w ∈ Ω := (hsc hw).2
      have hcd : ContDiffOn ℝ 3 (eM ∘ u k) Ω := contMDiffOn_iff_contDiffOn.1 <|
        (heM_cmd.of_le (by simp)).comp (hu k) ((huK k).mono_right hKW)
      exact (hcd.differentiableOn (by norm_num) w hwΩ).differentiableAt (hΩ.mem_nhds hwΩ)
    have hfd_le : ∀ w ∈ closedBall (c k) (s k),
        ‖fderiv ℝ (eM ∘ u k) w‖ ≤ 2 * √A_e * lam k + √B_e := by
      intro w hw
      have hwΩ : w ∈ Ω := (hsc hw).2
      have h1 : ‖fderiv ℝ (eM ∘ u k) w‖ ^ 2 ≤ A_e * e k w + B_e :=
        hbd_e (hpC k) (hΩD hwΩ) (huK k hwΩ)
          (((hu k).mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds hwΩ))
          (hfl k w hwΩ)
      have h2 : √(e k w) ≤ 2 * lam k := hk.2 w ((mem_closedBall'.1 hw).trans hsr)
      have h3 : e k w ≤ 4 * lam k ^ 2 := by
        have := Real.sq_sqrt (he_nn k hwΩ)
        nlinarith [Real.sqrt_nonneg (e k w)]
      have h4 : ‖fderiv ℝ (eM ∘ u k) w‖ ^ 2 ≤ (2 * √A_e * lam k + √B_e) ^ 2 := by
        have hAeq : (√A_e) ^ 2 = A_e := Real.sq_sqrt hAe.le
        have hBeq : (√B_e) ^ 2 = B_e := Real.sq_sqrt hBe
        have hcross : 0 ≤ √A_e * lam k * √B_e := by positivity
        nlinarith
      have hrhs_nn : 0 ≤ 2 * √A_e * lam k + √B_e := by positivity
      nlinarith [norm_nonneg (fderiv ℝ (eM ∘ u k) w)]
    have hmv := (convex_closedBall (c k) (s k)).norm_image_sub_le_of_norm_fderiv_le heM_diff hfd_le
      (mem_closedBall_self hsk_nn) hy
    rw [← dist_eq_norm] at hmv
    have hdy : ‖y - c k‖ ≤ s k := by simpa [dist_eq_norm] using mem_closedBall.1 hy
    have hprod : (2 * √A_e * lam k + √B_e) * s k = η / 2 + √B_e * c₀ / lam k := by
      have hsq : √A_e ≠ 0 := (Real.sqrt_pos.2 hAe).ne'
      simp only [s, c₀]
      field_simp [hlk.ne', hsq]
      ring
    have hle : dist (eM (u k y)) (eM (u k (c k))) ≤ (2 * √A_e * lam k + √B_e) * s k :=
      hmv.trans (mul_le_mul_of_nonneg_left hdy (by positivity))
    linarith
  -- Step 4: Contradict energy `< δ` via the localized mean-value inequality.
  by_contra hlt
  push Not at hlt
  have hint_ball : ∫ y in ball (c k) (s k), e k y ≤ ∫ y in ball z₀ ε ∩ Ω, e k y :=
    setIntegral_mono_set ((hint k).mono_set inter_subset_right)
      (ae_restrict_of_forall_mem (measurableSet_ball.inter hΩ.measurableSet)
        fun y hy ↦ he_nn k hy.2)
      (ball_subset_closedBall.trans hsc).eventuallySubset
  have hsmall : M₁ * (π * s k ^ 2) + M₂ * ∫ y in ball (c k) (s k), e k y < δ_mvi := by
    have hδ1 : δ ≤ δ_mvi / (2 * M₂) := min_le_left _ _
    have hM₂δ : M₂ * δ ≤ δ_mvi / 2 := by rw [le_div_iff₀ (by positivity)] at hδ1; linarith
    nlinarith
  have hmvi_k := hmvi hΩ hΩD (hpC k) hsk_nn (hsc.trans inter_subset_right) (hu k) (huK k)
    (fun y hy ↦ hfl k y (hsc hy).2) hdist hsmall
  have hlhs : π * s k ^ 2 * e k (c k) = π * c₀ ^ 2 := by
    have hsq : lam k ^ 2 = e k (c k) := Real.sq_sqrt (he_nn k (hsc (mem_closedBall_self hsk_nn)).2)
    rw [← hsq]; simp only [s]; field_simp [hlk.ne']
  have hδ2 : δ ≤ (π * c₀ ^ 2) / (2 * (M₃ + 1)) := min_le_right _ _
  have hM₃δ : M₃ * δ ≤ (π * c₀ ^ 2) / 2 := by rw [le_div_iff₀ (by positivity)] at hδ2; nlinarith
  nlinarith

end TauCeti.SmoothTwoForm.IsNondegenerate
