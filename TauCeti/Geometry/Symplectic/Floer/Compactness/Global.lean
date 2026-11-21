/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.UniformSpace.CompactConvergence
public import TauCeti.Geometry.Symplectic.Floer.Compactness.EnergyQuantization
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import TauCeti.Geometry.Manifold.ExtChartAt.CompactConvergence
import TauCeti.Geometry.Symplectic.Floer.Compactness.BoundedDensity
import TauCeti.Geometry.Symplectic.Floer.DerivativeConvergence.Manifold
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.Topology.ContinuousMap.Ascoli
import TauCeti.Topology.Separation.InvFunOn

/-!
# Global Gromov–Floer compactness on a manifold

Let `ω` be a nondegenerate two-form on a Hausdorff boundaryless manifold `M` modelled on a
finite-dimensional real normed space `E`, such as a closed symplectic manifold. Let `K_s, K_t` be
families of Hamiltonians and `J(p, z, x)` a family of `ω`-tame almost complex structures on the
tangent spaces of `M`, depending on a parameter `p` in a real inner product space `P`, a domain
point `z ∈ ℝ × ℝ` and a target point `x ∈ M`, with `(K_s, K_t)` jointly `C³` and `J` jointly `C²`
on an open neighbourhood `W` of a compact window `C × D × K`.

`TauCeti.Geometry.Symplectic.Floer.Compactness.Manifold` proved compactness for Floer solutions
staying in a single chart of `M`, and `EnergyQuantization` established the localized mean-value
inequality, Euclidean embedding derivative estimate, and uniform energy quantization at blow-up
points. This file combines those estimates with the energy-concentration extraction lemma,
Arzelà–Ascoli, and elliptic `C¹` convergence from
`TauCeti.Geometry.Symplectic.Floer.DerivativeConvergence.Manifold` to establish global Gromov–Floer
compactness on `M` without any single-chart assumption.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendsto_subseq_off_finset_of_isCompact`:
  global Gromov–Floer compactness for `C³` solutions with values in a compact subset `K ⊆ M` over
  a compact parameter window `C ⊆ P`.
* `exists_pos_forall_subseq_off_finset_of_isCompact`:
  unparametrized global compactness for a fixed Floer datum.
* `exists_pos_forall_tendsto_subseq_off_finset_of_compactSpace`:
  global Gromov–Floer compactness on a compact manifold `M`.
* `exists_pos_forall_tendsto_contMDiffOn_one_subseq_off_finset_of_isCompact`:
  global `C¹` Gromov–Floer compactness for smooth solutions over a compact parameter window.
* `exists_pos_forall_contMDiffOn_one_subseq_off_finset_of_isCompact`:
  unparametrized global `C¹` Gromov–Floer compactness for smooth solutions.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications **52**, 2012, Section 4.6 (bubbling off finitely many points), Section 8.1
  (inhomogeneous equations) and Appendix B.4 (elliptic regularity).
-/

public section

noncomputable section

open Bundle Complex ContinuousLinearMap Filter Function MeasureTheory Metric Real Set Topology
open scoped Manifold

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M]

section Compactness

variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]

/-- Eventual uniform derivative bound in a chart `extChartAt I α` on a compact `C' ⊆ U₀` mapped by
`v` into `(extChartAt I α).source`, from compact-open convergence in `C(U₀, M)` and energy-density
bounds. -/
private theorem chart_eventually_norm_fderiv_le [I.Boundaryless] [T2Space M]
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
    {Ω U₀ : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) (hΩD : Ω ⊆ D) (hU₀Ω : U₀ ⊆ Ω)
    {p : ℕ → P} {u : ℕ → ℝ × ℝ → M} {v : ℝ × ℝ → M}
    (hpC : ∀ n, p n ∈ C) (hu : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u n) Ω)
    (hfl : ∀ n, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p n) y (u n y))
      (ω.perturbedMFDeriv (Ks (p n)) (Kt (p n)) (u n) y).toLinearMap)
    (huK : ∀ n, MapsTo (u n) Ω K) (hvc : ContinuousOn v U₀)
    (hlim : Tendsto
      (fun n ↦ (⟨U₀.domRestrict (u n), ((hu n).continuousOn.mono hU₀Ω).domRestrict⟩ : C(U₀, M)))
      atTop (𝓝 ⟨U₀.domRestrict v, hvc.domRestrict⟩))
    (he_bd : ∀ C', IsCompact C' → C' ⊆ U₀ →
      ∃ M₀, ∀ n, ∀ y ∈ C', ω.floerEnergyDensity (Ks (p n)) (Kt (p n)) (u n) y ≤ M₀)
    (α : M) {C' : Set (ℝ × ℝ)} (hC' : IsCompact C') (hC'U₀ : C' ⊆ U₀)
    (hvα : MapsTo v C' (extChartAt I α).source) :
    ∃ M₀, ∀ᶠ n in atTop, ∀ y ∈ C', ‖fderiv ℝ (extChartAt I α ∘ u n) y‖ ≤ M₀ := by
  classical
  set e := extChartAt I α
  -- Enclose `e '' (v '' C')` inside a compact neighbourhood `Sα ⊆ e.target`.
  have hcomp_im : IsCompact (e '' (v '' C')) :=
    (hC'.image_of_continuousOn (hvc.mono hC'U₀)).image_of_continuousOn
      ((continuousOn_extChartAt α).mono (image_subset_iff.2 hvα))
  have hsub_tgt : e '' (v '' C') ⊆ e.target := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact e.map_source (hvα hy)
  obtain ⟨Sα, hSα_comp, hSα_sub, hSα_tgt⟩ :=
    exists_compact_between hcomp_im (isOpen_extChartAt_target α) hsub_tgt
  let Uα : Set M := e.source ∩ e ⁻¹' interior Sα
  have hUα_open : IsOpen Uα :=
    (continuousOn_extChartAt α).isOpen_inter_preimage (isOpen_extChartAt_source α) isOpen_interior
  have hvUα : MapsTo v C' Uα := fun y hy ↦ ⟨hvα hy, hSα_sub ⟨v y, ⟨y, hy, rfl⟩, rfl⟩⟩
  have hUα_Sα : ∀ x ∈ Uα, e x ∈ Sα := fun _ hx ↦ interior_subset hx.2
  have hL : IsCompact (((↑) : U₀ → ℝ × ℝ) ⁻¹' C') :=
    IsInducing.subtypeVal.isCompact_preimage' hC' (by simpa [Subtype.range_coe_subtype] using hC'U₀)
  have hevU : ∀ᶠ n in atTop, MapsTo (u n) C' Uα := by
    filter_upwards [(ContinuousMap.tendsto_nhds_compactOpen.1 hlim) _ hL Uα hUα_open
      fun y hy ↦ hvUα hy] with n hn y hy
    exact hn (x := ⟨y, hC'U₀ hy⟩) hy
  -- Intersect `Sα` with `e.symm ⁻¹' K` to apply the parametric chart energy–derivative bound.
  let Kα' : Set E := Sα ∩ e.symm ⁻¹' K
  have hKα'_comp : IsCompact Kα' := hSα_comp.of_isClosed_subset
    (((continuousOn_extChartAt_symm α).mono hSα_tgt).preimage_isClosed_of_isClosed
      hSα_comp.isClosed hK.isClosed) inter_subset_left
  have hKα'_tgt : Kα' ⊆ e.target := inter_subset_left.trans hSα_tgt
  have hXsM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKs
  have hXtM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKt
  have hWα_sub : C ×ˢ (D ×ˢ Kα') ⊆ {q : P × ((ℝ × ℝ) × E) |
      q.2.2 ∈ e.target ∧ (q.1, (q.2.1, e.symm q.2.2)) ∈ W} :=
    fun q hq ↦ ⟨hKα'_tgt hq.2.2, hCDKW ⟨hq.1, hq.2.1, hq.2.2.2⟩⟩
  obtain ⟨A_α, hAα, B_α, hBα, _, _, _, _, hcbd⟩ :=
    hω.exists_forall_norm_fderiv_extChartAt_comp_sq_le_and_floerEnergyDensity_le α hC hD hKα'_comp
      hKα'_tgt
      ((Floer.contDiffOn_almostComplexInChartAt (n := 2) (by simp) α hJ).continuousOn.mono hWα_sub)
      ((ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) (by simp) α hXsM).continuousOn.mono
        hWα_sub)
      ((ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 2) (by simp) α hXtM).continuousOn.mono
        hWα_sub)
      fun q₀ hq₀ z hz y hy ↦ hJt q₀ hq₀ z hz _ hy.2
  obtain ⟨Me, hMe⟩ := he_bd C' hC' hC'U₀
  refine ⟨√(A_α * max Me 0 + B_α), ?_⟩
  filter_upwards [hevU] with n hn y hy
  have hyΩ : y ∈ Ω := hU₀Ω (hC'U₀ hy)
  have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u n) y :=
    ((hu n).mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds hyΩ)
  have hmemKα' : e (u n y) ∈ Kα' :=
    ⟨hUα_Sα _ (hn hy), by rw [mem_preimage, e.left_inv (hn hy).1]; exact huK n hyΩ⟩
  have h1 := (hcbd (hpC n) (hΩD hyΩ) (hn hy).1 hmemKα' hdiff (hfl n y hyΩ)).1
  have h2 : ω.floerEnergyDensity (Ks (p n)) (Kt (p n)) (u n) y ≤ max Me 0 :=
    (hMe n y hy).trans (le_max_left _ _)
  have hsq : ‖fderiv ℝ (e ∘ u n) y‖ ^ 2 ≤ (√(A_α * max Me 0 + B_α)) ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]; nlinarith
  nlinarith [norm_nonneg (fderiv ℝ (e ∘ u n) y), Real.sqrt_nonneg (A_α * max Me 0 + B_α)]

/-- **Global Gromov–Floer compactness on a manifold over a compact parameter window.** Let `ω` be
a nondegenerate two-form on a Hausdorff boundaryless manifold `M` modelled on a finite-dimensional
real normed space `E`, and let `P` be a real inner product space of parameters. Let `K_s, K_t` be
jointly `C³` and `J` jointly `C²` on an open set `W ⊆ P × ((ℝ × ℝ) × M)` containing `C × D × K`
for compact `C ⊆ P`, `D ⊆ ℝ × ℝ` and `K ⊆ M`, with `J(p, z, x)` tamed by `ω` on `C × D × K`.

There is a threshold `δ > 0` with the following property. Let `u_k` be `C³` solutions of the Floer
equation `(du - X_{K_{p_k}})^{0,1} = 0` for `J_{p_k}` on an open `Ω ⊆ D`, for parameters `p_k ∈ C`,
taking values in `K` (without assuming they stay in a single chart), and with Floer energy
`∫_Ω e(u_k) ≤ E₀`. Then there exist a subsequence `φ`, a limit parameter `p₀ ∈ C` of `p_{φ n}`, a
finite bubbling set `Z ⊆ Ω` with `#Z * δ ≤ E₀`, and a continuous map `v : Ω \ Z → K` such that:
* along `φ`, every disc about a point of `Z` eventually carries Floer energy at least `δ`;
* the Floer energy densities `e(u_{φ n})` are uniformly bounded on every compact subset of `Ω \ Z`;
* `u_{φ n} → v` in `C(↥(Ω \ ↑Z), M)` with the compact-open topology (and in particular pointwise on
  `Ω \ Z`);
* in every chart `extChartAt I α` and on every compact `C' ⊆ Ω \ Z` with
  `MapsTo v C' (extChartAt I α).source`, the chart expressions `extChartAt I α ∘ u_{φ n}` converge
  uniformly to `extChartAt I α ∘ v` on `C'` and their differentials are eventually uniformly
  bounded on `C'`. -/
theorem exists_pos_forall_tendsto_subseq_off_finset_of_isCompact
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
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E₀ : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, p k ∈ C) →
      (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
        (ω.perturbedMFDeriv (Ks (p k)) (Kt (p k)) (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M)
        (hvc : ContinuousOn v (Ω \ ↑Z)),
        StrictMono φ ∧ p₀ ∈ C ∧ Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n)))
            (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M₀, ∀ n, ∀ y ∈ C', ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n))) (u (φ n)) y ≤
            M₀) ∧
        MapsTo v (Ω \ ↑Z) K ∧
        Tendsto (fun n ↦ (⟨(Ω \ ↑Z).domRestrict (u (φ n)),
          ((hu (φ n)).continuousOn.mono sdiff_subset).domRestrict⟩ : C(↥(Ω \ ↑Z), M)))
          atTop (𝓝 ⟨(Ω \ ↑Z).domRestrict v, hvc.domRestrict⟩) ∧
        (∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 (v y))) ∧
        (∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z → MapsTo v C' (extChartAt I α).source →
          TendstoUniformlyOn (fun n ↦ extChartAt I α ∘ u (φ n)) (extChartAt I α ∘ v) atTop C' ∧
          ∃ M₀, ∀ᶠ n in atTop, ∀ y ∈ C', ‖fderiv ℝ (extChartAt I α ∘ u (φ n)) y‖ ≤ M₀) := by
  classical
  obtain ⟨δ, hδ, hconc_blow⟩ :=
    hω.exists_pos_forall_eventually_le_setIntegral_ball_of_tendsto_floerEnergyDensity
      hW hKs hKt hJ hC hD hK hCDKW hJt
  have hXsM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKs
  have hXtM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 2) (by simp) hW hKt
  obtain ⟨W_emb, N, emb, eM, hKW, heM_eq, heM_cmd, A_e, hAe, B_e, hBe, hbd_e⟩ :=
    hω.exists_opens_smoothEmbedding_norm_fderiv_sq_le hW hJ.continuousOn hXsM.continuousOn
      hXtM.continuousOn hC hD hK hCDKW hJt
  refine ⟨δ, hδ, fun Ω p u E₀ hΩ hΩD hpC hu hfl huK hint hE ↦ ?_⟩
  rcases K.eq_empty_or_nonempty with rfl | ⟨x_def, -⟩
  · obtain ⟨p₀, hp₀, φ, hφ, hplim⟩ := hC.tendsto_subseq hpC
    rcases eq_empty_iff_forall_notMem.2 (fun z hz ↦ huK 0 hz) with rfl
    have hE₀ : 0 ≤ E₀ := by simpa using hE 0
    refine ⟨φ, p₀, ∅, u 0, by simp, hφ, hp₀, hplim, by simp, by simpa using hE₀,
      by simp, fun C' _ hC' ↦ ⟨0, fun _ y hy ↦ (hC' hy).1.elim⟩,
      by simp,
      tendsto_const_nhds.congr fun n ↦ ContinuousMap.ext fun y ↦ y.property.1.elim,
      fun y hy ↦ hy.1.elim,
      fun α C' _ hC' _ ↦ ⟨by
        have hC'e : C' = ∅ := eq_empty_iff_forall_notMem.2 fun y hy ↦ (hC' hy).1
        simp [hC'e, tendstoUniformlyOn_empty], 0,
        Eventually.of_forall fun _ y hy ↦ (hC' hy).1.elim⟩⟩
  -- Step 1: Extract finite bubbling set `Z ⊆ Ω` and subsequence `ψ` off which `e(u_{ψ n})` is
  -- uniformly bounded on compacts.
  set e : ℕ → ℝ × ℝ → ℝ := fun k ↦ ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)
  have he_nn (k : ℕ) {y : ℝ × ℝ} (hy : y ∈ Ω) : 0 ≤ e k y :=
    floerEnergyDensity_nonneg hω (hJt (p k) (hpC k) y (hΩD hy) (u k y) (huK k hy)) (hfl k y hy)
  have he_cont (k : ℕ) : ContinuousOn (e k) Ω :=
    ω.continuousOn_floerEnergyDensity_of_isOpen_prod hW hXsM.continuousOn hXtM.continuousOn hΩ
      Subset.rfl ((hu k).of_le (by norm_num)) fun y hy ↦ hCDKW ⟨hpC k, hΩD hy, huK k hy⟩
  obtain ⟨ψ, hψ, Z, hZΩ, hcard, hconc, he_bd⟩ :=
    exists_strictMono_finset_forall_le_of_concentration (g := e) (e := e) hΩ.measurableSet hδ
      he_cont (fun k y hy ↦ he_nn k hy) hint hE fun φ' _ z z₀ _ hz₀ hz hblow ε hε ↦
        hconc_blow hΩ hΩD (fun n ↦ hpC (φ' n)) (fun n ↦ hu (φ' n)) (fun n ↦ hfl (φ' n))
          (fun n ↦ huK (φ' n)) (fun n ↦ hint (φ' n)) hz₀ hz hblow ε hε
  -- Step 2: Converging parameter subsequence along `χ₁` and Arzelà–Ascoli on `eM ∘ u_{ψ₁ n}`.
  obtain ⟨p₀, hp₀, χ₁, hχ₁, hplim₁⟩ := hC.tendsto_subseq (fun n ↦ hpC (ψ n))
  set ψ₁ := ψ ∘ χ₁
  have hψ₁ : StrictMono ψ₁ := hψ.comp hχ₁
  set U₀ : Set (ℝ × ℝ) := Ω \ ↑Z
  have hU₀ : IsOpen U₀ := hΩ.sdiff Z.finite_toSet.isClosed
  have : LocallyCompactSpace U₀ := hU₀.locallyCompactSpace
  have heM_diff (n : ℕ) : DifferentiableOn ℝ (eM ∘ u (ψ₁ n)) U₀ :=
    (contMDiffOn_iff_contDiffOn.1 <|
      (heM_cmd.of_le (by simp)).comp (hu (ψ₁ n)) ((huK (ψ₁ n)).mono_right hKW)).differentiableOn
      (by norm_num) |>.mono sdiff_subset
  have hequi : EquicontinuousOn (fun n ↦ eM ∘ u (ψ₁ n)) U₀ := by
    refine equicontinuousOn_of_forall_isCompact_norm_fderiv_le hU₀ heM_diff fun C' hC' hC'U₀ ↦ ?_
    obtain ⟨M₀, hM₀⟩ := he_bd C' hC' hC'U₀
    refine ⟨√(A_e * max M₀ 0 + B_e), fun n y hy ↦ ?_⟩
    have h1 := hbd_e (hpC (ψ₁ n)) (hΩD (hC'U₀ hy).1) (huK (ψ₁ n) (hC'U₀ hy).1)
      (((hu (ψ₁ n)).mdifferentiableOn (by norm_num)).mdifferentiableAt (hΩ.mem_nhds (hC'U₀ hy).1))
      (hfl (ψ₁ n) y (hC'U₀ hy).1)
    have h2 : e (ψ₁ n) y ≤ max M₀ 0 := (hM₀ (χ₁ n) y hy).trans (le_max_left _ _)
    have hsq : ‖fderiv ℝ (eM ∘ u (ψ₁ n)) y‖ ^ 2 ≤ (√(A_e * max M₀ 0 + B_e)) ^ 2 := by
      rw [Real.sq_sqrt (by positivity)]; nlinarith
    nlinarith [norm_nonneg (fderiv ℝ (eM ∘ u (ψ₁ n)) y), Real.sqrt_nonneg (A_e * max M₀ 0 + B_e)]
  have he_cont_K : ContinuousOn eM K := heM_cmd.continuousOn.mono hKW
  obtain ⟨χ₂, hχ₂, G, hGc, hconvG⟩ :=
    TauCeti.exists_strictMono_tendstoLocallyUniformlyOn_of_equicontinuousOn hU₀ hequi
      fun x hx ↦ ⟨eM '' K, hK.image_of_continuousOn he_cont_K,
        fun n ↦ mem_image_of_mem eM (huK (ψ₁ n) hx.1)⟩
  set φ := ψ₁ ∘ χ₂
  have hφ : StrictMono φ := hψ₁.comp hχ₂
  -- Step 3: Pull `G` back to `v` via `IsCompact.exists_tendsto_of_tendsto_comp` and deduce
  -- compact-open convergence in `C(U₀, M)`.
  have : Nonempty M := ⟨x_def⟩
  have heM_inj : InjOn eM K := fun x hx y hy hxy ↦
    congrArg Subtype.val (emb.isEmbedding.injective
      (by simpa only [heM_eq x (hKW hx), heM_eq y (hKW hy)] using hxy))
  obtain ⟨v, hvc, hvK, hev, hpt⟩ := hK.exists_tendsto_of_tendsto_comp he_cont_K heM_inj
    (fun n ↦ (huK (φ n)).mono_left sdiff_subset) hGc fun z hz ↦ hconvG.tendsto_at hz
  let eM_u : ℕ → C(U₀, EuclideanSpace ℝ (Fin N)) := fun n ↦
    ⟨U₀.domRestrict (eM ∘ u (φ n)), (hequi.continuousOn (χ₂ n)).domRestrict⟩
  let eM_v : C(U₀, EuclideanSpace ℝ (Fin N)) :=
    ⟨U₀.domRestrict (eM ∘ v), (he_cont_K.comp hvc hvK).domRestrict⟩
  have hlim_a : Tendsto eM_u atTop (𝓝 eM_v) :=
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.2
      (tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.1
        (hconvG.congr_right hev.symm))
  let vW : C(U₀, W_emb) := ⟨fun y ↦ ⟨v y.val, hKW (hvK y.property)⟩,
    emb.isEmbedding.continuous_iff.2 <| by
      have : emb ∘ (fun y : U₀ ↦ (⟨v y.val, hKW (hvK y.property)⟩ : W_emb)) = eM_v :=
        funext fun y ↦ (heM_eq (v y.val) (hKW (hvK y.property))).symm
      rw [this]; exact eM_v.continuous⟩
  let uW : ℕ → C(U₀, W_emb) := fun n ↦
    ⟨fun y ↦ ⟨u (φ n) y.val, hKW (huK (φ n) y.property.1)⟩,
      (((hu (φ n)).continuousOn.mono sdiff_subset).domRestrict).subtype_mk fun y ↦
        hKW (huK (φ n) y.property.1)⟩
  have hlim_W : Tendsto uW atTop (𝓝 vW) := by
    refine (ContinuousMap.isInducing_postcomp ⟨emb, emb.isEmbedding.continuous⟩
      emb.isEmbedding.isInducing).tendsto_nhds_iff.2 ?_
    have heq_u : (⟨emb, emb.isEmbedding.continuous⟩ : C(W_emb, _)).comp ∘ uW = eM_u := by
      funext n; exact ContinuousMap.ext fun y ↦ (heM_eq _ _).symm
    have heq_v : (⟨emb, emb.isEmbedding.continuous⟩ : C(W_emb, _)).comp vW = eM_v :=
      ContinuousMap.ext fun y ↦ (heM_eq _ _).symm
    rw [heq_u, heq_v]; exact hlim_a
  have hlim_M : Tendsto
      (fun n ↦ (⟨U₀.domRestrict (u (φ n)),
        ((hu (φ n)).continuousOn.mono sdiff_subset).domRestrict⟩ : C(U₀, M)))
      atTop (𝓝 ⟨U₀.domRestrict v, hvc.domRestrict⟩) :=
    (ContinuousMap.continuous_postcomp
      ⟨Subtype.val, continuous_subtypeVal⟩).continuousAt.tendsto.comp hlim_W
  have he_bd_φ : ∀ C', IsCompact C' → C' ⊆ U₀ → ∃ M₀, ∀ n, ∀ y ∈ C', e (φ n) y ≤ M₀ :=
    fun C' hC' hC'U₀ ↦ let ⟨M₀, hM₀⟩ := he_bd C' hC' hC'U₀; ⟨M₀, fun n ↦ hM₀ (χ₁ (χ₂ n))⟩
  -- Step 4: Assemble all conclusions.
  refine ⟨φ, p₀, Z, v, hvc, hφ, hp₀, hplim₁.comp hχ₂.tendsto_atTop, hZΩ, hcard,
    fun z hz ε hε ↦ (hχ₁.comp hχ₂).tendsto_atTop.eventually (hconc z hz ε hε),
    he_bd_φ, hvK, hlim_M, hpt, fun α C' hC' hC'U₀ hvα ↦ ?_⟩
  refine ⟨ContinuousMap.tendstoUniformlyOn_extChartAt_comp_of_tendsto_domRestrict
    (fun n ↦ (hu (φ n)).continuousOn.mono sdiff_subset) hvc hlim_M α hC' hC'U₀ hvα, ?_⟩
  exact hω.chart_eventually_norm_fderiv_le hW hKs hKt hJ hC hD hK hCDKW hJt hΩ hΩD sdiff_subset
    (fun n ↦ hpC (φ n)) (fun n ↦ hu (φ n)) (fun n ↦ hfl (φ n)) (fun n ↦ huK (φ n)) hvc hlim_M
    he_bd_φ α hC' hC'U₀ hvα

/-- **Global Gromov–Floer compactness on a manifold for a fixed datum.** Specialization of
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_tendsto_subseq_off_finset_of_isCompact`
to a parameter-independent Floer datum `(J, K_s, K_t)` on an open neighbourhood `W ⊆ (ℝ × ℝ) × M`
of `D × K`. -/
theorem exists_pos_forall_subseq_off_finset_of_isCompact [I.Boundaryless] [T2Space M]
    {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : ℝ × ℝ → M → ℝ} {W : Set ((ℝ × ℝ) × M)} {D : Set (ℝ × ℝ)} {K : Set M}
    (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 3 (uncurry Ks) W)
    (hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 3 (uncurry Kt) W)
    (hJ : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun q : (ℝ × ℝ) × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        (J q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E₀ : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv Ks Kt (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M)
        (hvc : ContinuousOn v (Ω \ ↑Z)),
        StrictMono φ ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M₀, ∀ n, ∀ y ∈ C', ω.floerEnergyDensity Ks Kt (u (φ n)) y ≤ M₀) ∧
        MapsTo v (Ω \ ↑Z) K ∧
        Tendsto (fun n ↦ (⟨(Ω \ ↑Z).domRestrict (u (φ n)),
          ((hu (φ n)).continuousOn.mono sdiff_subset).domRestrict⟩ : C(↥(Ω \ ↑Z), M)))
          atTop (𝓝 ⟨(Ω \ ↑Z).domRestrict v, hvc.domRestrict⟩) ∧
        (∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 (v y))) ∧
        (∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z → MapsTo v C' (extChartAt I α).source →
          TendstoUniformlyOn (fun n ↦ extChartAt I α ∘ u (φ n)) (extChartAt I α ∘ v) atTop C' ∧
          ∃ M₀, ∀ᶠ n in atTop, ∀ y ∈ C', ‖fderiv ℝ (extChartAt I α ∘ u (φ n)) y‖ ≤ M₀) := by
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendsto_subseq_off_finset_of_isCompact
    (P := ℝ) (J := fun _ ↦ J) (Ks := fun _ ↦ Ks) (Kt := fun _ ↦ Kt) (W := univ ×ˢ W) (C := {0})
    (isOpen_univ.prod hW) (hKs.comp contMDiffOn_snd fun _ hq ↦ hq.2)
    (hKt.comp contMDiffOn_snd fun _ hq ↦ hq.2) (hJ.comp contMDiffOn_snd fun _ hq ↦ hq.2)
    isCompact_singleton hD hK (prod_mono (subset_univ _) hDKW) fun _ _ ↦ hJt
  refine ⟨δ, hδ, fun Ω u E₀ hΩ hΩD hu hfl huK hint hE ↦ ?_⟩
  obtain ⟨φ, -, Z, v, hvc, hφ, -, -, hrest⟩ :=
    hconv (p := fun _ ↦ 0) hΩ hΩD (fun _ ↦ rfl) hu hfl huK hint hE
  exact ⟨φ, Z, v, hvc, hφ, hrest⟩

/-- **Global Gromov–Floer compactness on a compact manifold over a compact parameter window.**
Specialization of
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_tendsto_subseq_off_finset_of_isCompact`
to `K = Set.univ` when `M` is compact. -/
theorem exists_pos_forall_tendsto_subseq_off_finset_of_compactSpace
    [I.Boundaryless] [T2Space M] [CompactSpace M] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))}
    {C : Set P} {D : Set (ℝ × ℝ)} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 3
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    (hC : IsCompact C) (hD : IsCompact D) (hCDW : C ×ˢ (D ×ˢ (univ : Set M)) ⊆ W)
    (hJt : ∀ p ∈ C, ∀ z ∈ D, ∀ x : M, (hω.symplecticFormAt x).Tames (J p z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E₀ : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, p k ∈ C) →
      (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
        (ω.perturbedMFDeriv (Ks (p k)) (Kt (p k)) (u k) z).toLinearMap) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M)
        (hvc : ContinuousOn v (Ω \ ↑Z)),
        StrictMono φ ∧ p₀ ∈ C ∧ Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n)))
            (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M₀, ∀ n, ∀ y ∈ C', ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n))) (u (φ n)) y ≤
            M₀) ∧
        Tendsto (fun n ↦ (⟨(Ω \ ↑Z).domRestrict (u (φ n)),
          ((hu (φ n)).continuousOn.mono sdiff_subset).domRestrict⟩ : C(↥(Ω \ ↑Z), M)))
          atTop (𝓝 ⟨(Ω \ ↑Z).domRestrict v, hvc.domRestrict⟩) ∧
        (∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 (v y))) ∧
        (∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z → MapsTo v C' (extChartAt I α).source →
          TendstoUniformlyOn (fun n ↦ extChartAt I α ∘ u (φ n)) (extChartAt I α ∘ v) atTop C' ∧
          ∃ M₀, ∀ᶠ n in atTop, ∀ y ∈ C', ‖fderiv ℝ (extChartAt I α ∘ u (φ n)) y‖ ≤ M₀) := by
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendsto_subseq_off_finset_of_isCompact
    hW hKs hKt hJ hC hD isCompact_univ hCDW fun p hp z hz x _ ↦ hJt p hp z hz x
  refine ⟨δ, hδ, fun Ω p u E₀ hΩ hΩD hpC hu hfl hint hE ↦ ?_⟩
  obtain ⟨φ, p₀, Z, v, hvc, hφ, hp₀, hplim, hZΩ, hcard, hconc, hebd, -, hlim, hpt, hch⟩ :=
    hconv hΩ hΩD hpC hu hfl (fun _ ↦ mapsTo_univ _ _) hint hE
  exact ⟨φ, p₀, Z, v, hvc, hφ, hp₀, hplim, hZΩ, hcard, hconc, hebd, hlim, hpt, hch⟩

end Compactness

section SmoothCompactness

/-- **Global `C¹` Gromov–Floer compactness for smooth solutions on a manifold over a compact
parameter window.** Combines
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_tendsto_subseq_off_finset_of_isCompact`
with `contMDiffOn_one_and_isComplexLinearMap_of_tendsto_floer_parametric` when the parameter space
`P` is finite-dimensional and the solutions `u_k` are smooth (`C^∞`). In addition to compact-open
convergence in `C(↥(Ω \ ↑Z), M)` and energy quantization off the finite bubbling set `Z ⊆ Ω`, the
limit `v` is `C¹` on `Ω \ Z`, solves the intrinsic Floer equation for the limit parameter `p₀` at
every point of `Ω \ Z`, and in every chart `extChartAt I α` both the coordinate maps and their
differentials converge uniformly on every compact `C' ⊆ Ω \ Z` with
`MapsTo v C' (extChartAt I α).source`. -/
theorem exists_pos_forall_tendsto_contMDiffOn_one_subseq_off_finset_of_isCompact
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
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
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃p : ℕ → P⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E₀ : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (∀ k, p k ∈ C) →
      (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
        (ω.perturbedMFDeriv (Ks (p k)) (Kt (p k)) (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M)
        (hv_cmd : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v (Ω \ ↑Z)),
        StrictMono φ ∧ p₀ ∈ C ∧ Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n)))
            (u (φ n)) y) ∧
        MapsTo v (Ω \ ↑Z) K ∧
        (∀ y ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p₀ y (v y))
          (ω.perturbedMFDeriv (Ks p₀) (Kt p₀) v y).toLinearMap) ∧
        Tendsto (fun n ↦ (⟨(Ω \ ↑Z).domRestrict (u (φ n)),
          ((hu (φ n)).continuousOn.mono sdiff_subset).domRestrict⟩ : C(↥(Ω \ ↑Z), M)))
          atTop (𝓝 ⟨(Ω \ ↑Z).domRestrict v, hv_cmd.continuousOn.domRestrict⟩) ∧
        (∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z → MapsTo v C' (extChartAt I α).source →
          TendstoUniformlyOn (fun n ↦ extChartAt I α ∘ u (φ n)) (extChartAt I α ∘ v) atTop C' ∧
          TendstoUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u (φ n)))
            (fderiv ℝ (extChartAt I α ∘ v)) atTop C') := by
  let L : P ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ P)) := toEuclidean
  let ψ : EuclideanSpace ℝ (Fin (Module.finrank ℝ P)) × ((ℝ × ℝ) × M) → P × ((ℝ × ℝ) × M) :=
    fun q ↦ (L.symm q.1, q.2)
  have hψ : ContMDiff
      (𝓘(ℝ, EuclideanSpace ℝ (Fin (Module.finrank ℝ P))).prod (𝓘(ℝ, ℝ × ℝ).prod I))
      (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (⊤ : ℕ∞) ψ :=
    (L.symm.contDiff.contMDiff.comp contMDiff_fst).prodMk contMDiff_snd
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendsto_subseq_off_finset_of_isCompact
    (J := fun q ↦ J (L.symm q)) (Ks := fun q ↦ Ks (L.symm q)) (Kt := fun q ↦ Kt (L.symm q))
    (W := ψ ⁻¹' W) (C := L '' C) (hW.preimage hψ.continuous)
    (hKs.comp (hψ.of_le (by simp)).contMDiffOn (mapsTo_preimage _ _))
    (hKt.comp (hψ.of_le (by simp)).contMDiffOn (mapsTo_preimage _ _))
    (hJ.comp (hψ.of_le (by simp)).contMDiffOn (mapsTo_preimage _ _))
    (hC.image L.continuous) hD hK
    (by rintro ⟨_, z, x⟩ ⟨⟨p, hp, rfl⟩, hz, hx⟩; simpa [ψ] using hCDKW ⟨hp, hz, hx⟩)
    (by rintro _ ⟨p, hp, rfl⟩ z hz x hx; simpa using hJt p hp z hz x hx)
  refine ⟨δ, hδ, fun Ω p u E₀ hΩ hΩD hpC hu hfl huK hint hE ↦ ?_⟩
  obtain ⟨φ, q₀, Z, v, hvc, hφ, ⟨p₀, hp₀, rfl⟩, hqlim, hZΩ, hcard, hconc, -, hvK, hlim, -, hch⟩ :=
    hconv (p := fun k ↦ L (p k)) hΩ hΩD (fun k ↦ ⟨p k, hpC k, rfl⟩)
      (fun k ↦ (hu k).of_le (by simp)) (by simpa using hfl) huK
      (by simpa using hint) (by simpa using hE)
  have hplim : Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) := by
    simpa [Function.comp_def] using L.symm.continuous.continuousAt.tendsto.comp hqlim
  have hconc' : ∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
      δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n)))
        (u (φ n)) y := by
    simpa using hconc
  obtain ⟨hv_cmd, hv_fl, hch_fd⟩ :=
    hω.contMDiffOn_one_and_isComplexLinearMap_of_tendsto_floer_parametric hW
      (hKs.of_le (by norm_num)) (hKt.of_le (by norm_num)) (hJ.of_le (by norm_num))
      (hΩ.sdiff Z.finite_toSet.isClosed) hplim (fun y hy ↦ hCDKW ⟨hp₀, hΩD hy.1, hvK hy⟩)
      (fun n ↦ (hu (φ n)).mono sdiff_subset) (fun n y hy ↦ hfl (φ n) y hy.1) hvc hlim
      fun α C' hC' hC'Z hvα ↦ (hch α C' hC' hC'Z hvα).2
  exact ⟨φ, p₀, Z, v, hv_cmd, hφ, hp₀, hplim, hZΩ, hcard, hconc', hvK, hv_fl, hlim,
    fun α C' hC' hC'Z hvα ↦ ⟨(hch α C' hC' hC'Z hvα).1, hch_fd α C' hC' hC'Z hvα⟩⟩

/-- **Unparametrized global `C¹` Gromov–Floer compactness for smooth solutions on a manifold.**
Specialization of `exists_pos_forall_tendsto_contMDiffOn_one_subseq_off_finset_of_isCompact` to a
fixed Floer datum `(J, K_s, K_t)`. -/
theorem exists_pos_forall_contMDiffOn_one_subseq_off_finset_of_isCompact
    [I.Boundaryless] [T2Space M] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : ℝ × ℝ → M → ℝ} {W : Set ((ℝ × ℝ) × M)} {D : Set (ℝ × ℝ)} {K : Set M}
    (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 3 (uncurry Ks) W)
    (hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 3 (uncurry Kt) W)
    (hJ : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 2
      (fun q : (ℝ × ℝ) × M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2
        (J q.1 q.2).toLinearMap.toContinuousLinearMap) W)
    (hD : IsCompact D) (hK : IsCompact K) (hDKW : D ×ˢ K ⊆ W)
    (hJt : ∀ z ∈ D, ∀ x ∈ K, (hω.symplecticFormAt x).Tames (J z x)) :
    ∃ δ > 0, ∀ ⦃Ω : Set (ℝ × ℝ)⦄ ⦃u : ℕ → ℝ × ℝ → M⦄ ⦃E₀ : ℝ⦄,
      IsOpen Ω → Ω ⊆ D → (hu : ∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv Ks Kt (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M)
        (hv_cmd : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v (Ω \ ↑Z)),
        StrictMono φ ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        MapsTo v (Ω \ ↑Z) K ∧
        (∀ y ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (v y))
          (ω.perturbedMFDeriv Ks Kt v y).toLinearMap) ∧
        Tendsto (fun n ↦ (⟨(Ω \ ↑Z).domRestrict (u (φ n)),
          ((hu (φ n)).continuousOn.mono sdiff_subset).domRestrict⟩ : C(↥(Ω \ ↑Z), M)))
          atTop (𝓝 ⟨(Ω \ ↑Z).domRestrict v, hv_cmd.continuousOn.domRestrict⟩) ∧
        (∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z → MapsTo v C' (extChartAt I α).source →
          TendstoUniformlyOn (fun n ↦ extChartAt I α ∘ u (φ n)) (extChartAt I α ∘ v) atTop C' ∧
          TendstoUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u (φ n)))
            (fderiv ℝ (extChartAt I α ∘ v)) atTop C') := by
  obtain ⟨δ, hδ, hconv⟩ :=
    hω.exists_pos_forall_tendsto_contMDiffOn_one_subseq_off_finset_of_isCompact
      (P := ℝ) (J := fun _ ↦ J) (Ks := fun _ ↦ Ks) (Kt := fun _ ↦ Kt) (W := univ ×ˢ W) (C := {0})
      (isOpen_univ.prod hW) (hKs.comp contMDiffOn_snd fun _ hq ↦ hq.2)
      (hKt.comp contMDiffOn_snd fun _ hq ↦ hq.2) (hJ.comp contMDiffOn_snd fun _ hq ↦ hq.2)
      isCompact_singleton hD hK (prod_mono (subset_univ _) hDKW) fun _ _ ↦ hJt
  refine ⟨δ, hδ, fun Ω u E₀ hΩ hΩD hu hfl huK hint hE ↦ ?_⟩
  obtain ⟨φ, -, Z, v, hv_cmd, hφ, -, -, hrest⟩ :=
    hconv (p := fun _ ↦ 0) hΩ hΩD (fun _ ↦ rfl) hu hfl huK hint hE
  exact ⟨φ, Z, v, hv_cmd, hφ, hrest⟩

end SmoothCompactness

end TauCeti.SmoothTwoForm.IsNondegenerate
