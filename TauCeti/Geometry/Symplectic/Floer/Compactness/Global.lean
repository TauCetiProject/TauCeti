/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Compactness.EnergyQuantization
import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Topology.UniformSpace.CompactConvergence
import TauCeti.MeasureTheory.Integral.EnergyConcentration
import TauCeti.Topology.ContinuousMap.Ascoli

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
Arzelà–Ascoli, and elliptic `C¹` convergence to establish global Gromov–Floer compactness on `M`
without any single-chart assumption.

## Main results

In the namespace `TauCeti.SmoothTwoForm.IsNondegenerate`:

* `exists_pos_forall_tendsto_subseq_off_finset_of_isCompact`:
  global Gromov–Floer compactness for `C³` solutions with values in a compact subset `K ⊆ M` over
  a compact parameter window `C ⊆ P`.
* `exists_pos_forall_subseq_off_finset_of_isCompact`:
  unparametrized global compactness for a fixed Floer datum.
* `exists_pos_forall_tendsto_subseq_off_finset_of_compactSpace`:
  global Gromov–Floer compactness on a compact manifold `M`.
* `contMDiffOn_one_and_isComplexLinearMap_of_tendsto_floer_parametric`:
  `C¹` convergence and passage of the intrinsic Floer equation to the limit for smooth solutions
  along a converging parameter sequence.
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

omit [FiniteDimensional ℝ E] [IsManifold I (⊤ : ℕ∞) M] in
/-- Compact-open convergence of continuous maps `u_n → v` on `U₀` implies uniform convergence of
their chart expressions `extChartAt I α ∘ u_n → extChartAt I α ∘ v` on every compact `C' ⊆ U₀`
mapped by `v` into `(extChartAt I α).source`. -/
private theorem chart_tendstoUniformlyOn_of_compactOpen {U₀ : Set (ℝ × ℝ)}
    {u : ℕ → ℝ × ℝ → M} {v : ℝ × ℝ → M} (huc : ∀ n, ContinuousOn (u n) U₀) (hvc : ContinuousOn v U₀)
    (hco : ∀ C' U, IsCompact C' → C' ⊆ U₀ → IsOpen U → MapsTo v C' U →
      ∀ᶠ n in atTop, MapsTo (u n) C' U)
    (α : M) {C' : Set (ℝ × ℝ)} (hC' : IsCompact C') (hC'U₀ : C' ⊆ U₀)
    (hvα : MapsTo v C' (extChartAt I α).source) :
    TendstoUniformlyOn (fun n ↦ extChartAt I α ∘ u n) (extChartAt I α ∘ v) atTop C' := by
  have : CompactSpace C' := isCompact_iff_compactSpace.1 hC'
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1
    (hco C' (extChartAt I α).source hC' hC'U₀ (isOpen_extChartAt_source α) hvα)
  let Usrc : Set M := (extChartAt I α).source
  let vM : C(C', M) := ⟨C'.domRestrict v, (hvc.mono hC'U₀).domRestrict⟩
  let uM : ℕ → C(C', M) := fun n ↦
    ⟨C'.domRestrict (u (n + N₀)), ((huc (n + N₀)).mono hC'U₀).domRestrict⟩
  have hlim_M : Tendsto uM atTop (𝓝 vM) := by
    rw [ContinuousMap.tendsto_nhds_compactOpen]
    intro L hL U hU hLU
    have hL' : IsCompact (((↑) : C' → ℝ × ℝ) '' L) := hL.image continuous_subtypeVal
    have hL'U₀ : ((↑) : C' → ℝ × ℝ) '' L ⊆ U₀ := by
      rintro _ ⟨y, -, rfl⟩; exact hC'U₀ y.property
    have hvL' : MapsTo v (((↑) : C' → ℝ × ℝ) '' L) U := by
      rintro _ ⟨y, hy, rfl⟩; exact hLU hy
    filter_upwards [(tendsto_add_atTop_nat N₀).eventually (hco _ U hL' hL'U₀ hU hvL')] with
      n hn y hy
    exact hn ⟨y, hy, rfl⟩
  let vS : C(C', Usrc) := ⟨fun y ↦ ⟨v y.val, hvα y.property⟩,
    ((hvc.mono hC'U₀).domRestrict).subtype_mk fun y ↦ hvα y.property⟩
  let uS : ℕ → C(C', Usrc) := fun n ↦
    ⟨fun y ↦ ⟨u (n + N₀) y.val, hN₀ (n + N₀) (Nat.le_add_left N₀ n) y.property⟩,
      (((huc (n + N₀)).mono hC'U₀).domRestrict).subtype_mk fun y ↦
        hN₀ (n + N₀) (Nat.le_add_left N₀ n) y.property⟩
  have hlim_S : Tendsto uS atTop (𝓝 vS) :=
    (ContinuousMap.isInducing_postcomp ⟨Subtype.val, continuous_subtypeVal⟩
      IsInducing.subtypeVal).tendsto_nhds_iff.2 hlim_M
  let eC : C(Usrc, E) :=
    ⟨Usrc.domRestrict (extChartAt I α), (continuousOn_extChartAt α).domRestrict⟩
  have hlim_E : Tendsto (fun n ↦ eC.comp (uS n)) atTop (𝓝 (eC.comp vS)) :=
    (ContinuousMap.continuous_postcomp eC).continuousAt.tendsto.comp hlim_S
  have hunif_tail : TendstoUniformlyOn (fun n ↦ extChartAt I α ∘ u (n + N₀)) (extChartAt I α ∘ v)
      atTop C' := by
    rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
    exact ContinuousMap.tendsto_iff_tendstoUniformly.1 hlim_E
  rw [Metric.tendstoUniformlyOn_iff] at hunif_tail ⊢
  intro ε hε
  have hmap : ∀ᶠ n in map (· + N₀) atTop,
      ∀ x ∈ C', dist ((extChartAt I α ∘ v) x) ((extChartAt I α ∘ u n) x) < ε :=
    Filter.eventually_map.2 (hunif_tail ε hε)
  rwa [Filter.map_add_atTop_eq_nat] at hmap

/-- Eventual uniform derivative bound in a chart `extChartAt I α` on a compact `C' ⊆ U₀` mapped by
`v` into `(extChartAt I α).source`, from compact-open convergence and energy-density bounds. -/
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
    (hco : ∀ C' U, IsCompact C' → C' ⊆ U₀ → IsOpen U → MapsTo v C' U →
      ∀ᶠ n in atTop, MapsTo (u n) C' U)
    (he_bd : ∀ C', IsCompact C' → C' ⊆ U₀ →
      ∃ M₀, ∀ n, ∀ y ∈ C', ω.floerEnergyDensity (Ks (p n)) (Kt (p n)) (u n) y ≤ M₀)
    (α : M) {C' : Set (ℝ × ℝ)} (hC' : IsCompact C') (hC'U₀ : C' ⊆ U₀)
    (hvα : MapsTo v C' (extChartAt I α).source) :
    ∃ M₀, ∀ᶠ n in atTop, ∀ y ∈ C', ‖fderiv ℝ (extChartAt I α ∘ u n) y‖ ≤ M₀ := by
  classical
  set e := extChartAt I α
  -- Cover the compact chart image `e '' (v '' C')` by finitely many balls inside `e.target`.
  have hcomp_im : IsCompact (e '' (v '' C')) :=
    (hC'.image_of_continuousOn (hvc.mono hC'U₀)).image_of_continuousOn
      ((continuousOn_extChartAt α).mono (image_subset_iff.2 hvα))
  have hsub_tgt : e '' (v '' C') ⊆ e.target := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩; exact e.map_source (hvα hy)
  have hball_ex : ∀ q ∈ e '' (v '' C'), ∃ r > 0, closedBall q r ⊆ e.target := fun q hq ↦
    Metric.nhds_basis_closedBall.mem_iff.1 ((isOpen_extChartAt_target α).mem_nhds (hsub_tgt hq))
  choose r hr_pos hr_sub using hball_ex
  obtain ⟨t, ht⟩ := hcomp_im.elim_finite_subcover
    (fun q : (e '' (v '' C')) ↦ ball q.val (r q.val q.property)) (fun _ ↦ isOpen_ball)
    (fun q hq ↦ mem_iUnion.2 ⟨⟨q, hq⟩, mem_ball_self (hr_pos q hq)⟩)
  let Sα : Set E := ⋃ q ∈ t, closedBall q.val (r q.val q.property)
  have hSα_comp : IsCompact Sα := t.isCompact_biUnion fun q _ ↦ isCompact_closedBall _ _
  have hSα_tgt : Sα ⊆ e.target := by
    intro w hw; obtain ⟨q, -, hwq⟩ := mem_iUnion₂.1 hw; exact hr_sub q.val q.property hwq
  let Uα : Set M := e.source ∩ e ⁻¹' (⋃ q ∈ t, ball q.val (r q.val q.property))
  have hUα_open : IsOpen Uα :=
    (continuousOn_extChartAt α).isOpen_inter_preimage (isOpen_extChartAt_source α)
      (isOpen_biUnion fun _ _ ↦ isOpen_ball)
  have hvUα : MapsTo v C' Uα := fun y hy ↦ ⟨hvα hy, ht ⟨v y, ⟨y, hy, rfl⟩, rfl⟩⟩
  have hUα_Sα : ∀ x ∈ Uα, e x ∈ Sα := fun x hx ↦ by
    obtain ⟨q, hqt, hxq⟩ := mem_iUnion₂.1 hx.2
    exact mem_iUnion₂.2 ⟨q, hqt, ball_subset_closedBall hxq⟩
  have hevU : ∀ᶠ n in atTop, MapsTo (u n) C' Uα := hco C' Uα hC' hC'U₀ hUα_open hvUα
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
* `u_{φ n} → v` in the compact-open topology on `Ω \ Z` (and in particular pointwise on `Ω \ Z`);
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
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
        (ω.perturbedMFDeriv (Ks (p k)) (Kt (p k)) (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M),
        StrictMono φ ∧ p₀ ∈ C ∧ Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n)))
            (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M₀, ∀ n, ∀ y ∈ C', ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n))) (u (φ n)) y ≤
            M₀) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        (∀ C' U, IsCompact C' → C' ⊆ Ω \ ↑Z → IsOpen U → MapsTo v C' U →
          ∀ᶠ n in atTop, MapsTo (u (φ n)) C' U) ∧
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
    refine ⟨φ, p₀, ∅, u 0, hφ, hp₀, hplim, by simp, by simpa using hE₀,
      by simp, fun C' _ hC' ↦ ⟨0, fun _ y hy ↦ (hC' hy).1.elim⟩,
      by simp, by simp,
      fun C' _ _ hC' _ _ ↦ Eventually.of_forall fun _ y hy ↦ (hC' hy).1.elim,
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
  have he_cont (k : ℕ) : ContinuousOn (e k) Ω := by
    intro y hy
    have hqW : (p k, (y, u k y)) ∈ W := hCDKW ⟨hpC k, hΩD hy, huK k hy⟩
    have hslice : ContinuousAt (fun q : (ℝ × ℝ) × M ↦ (p k, q)) (y, u k y) :=
      continuousAt_const.prodMk continuousAt_id
    exact (ω.continuousAt_floerEnergyDensity
      (((hu k).of_le (by norm_num)).contMDiffAt (hΩ.mem_nhds hy))
      ((hXsM.continuousOn.continuousAt (hW.mem_nhds hqW)).comp hslice)
      ((hXtM.continuousOn.continuousAt (hW.mem_nhds hqW)).comp hslice)).continuousWithinAt
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
  let Umap : ℕ → C(U₀, EuclideanSpace ℝ (Fin N)) := fun n ↦
    ⟨U₀.domRestrict (eM ∘ u (ψ₁ n)), (hequi.continuousOn n).domRestrict⟩
  have heMK_comp : IsCompact (eM '' K) := hK.image_of_continuousOn (heM_cmd.continuousOn.mono hKW)
  have hcomp_AA : IsCompact (closure (range Umap)) :=
    ArzelaAscoli.isCompact_closure_range_of_equicontinuous
      ((equicontinuous_restrict_iff _).mpr hequi) fun x ↦
        ⟨eM '' K, heMK_comp, fun n ↦ ⟨u (ψ₁ n) x.val, huK (ψ₁ n) x.property.1, rfl⟩⟩
  obtain ⟨a, -, χ₂, hχ₂, hlim_a⟩ := hcomp_AA.tendsto_subseq (x := Umap)
    fun n ↦ subset_closure (mem_range_self n)
  set φ := ψ₁ ∘ χ₂
  have hφ : StrictMono φ := hψ₁.comp hχ₂
  -- Step 3: Pull the limit `a : C(U₀, ℝ^N)` back along `emb` to `v : ℝ × ℝ → M` and deduce
  -- compact-open convergence on `U₀` via `ContinuousMap.isInducing_postcomp`.
  have ha_mem (y : ℝ × ℝ) (hy : y ∈ U₀) : a ⟨y, hy⟩ ∈ eM '' K := by
    have hpt : Tendsto (fun n ↦ eM (u (φ n) y)) atTop (𝓝 (a ⟨y, hy⟩)) :=
      (continuous_eval_const (⟨y, hy⟩ : U₀)).continuousAt.tendsto.comp hlim_a
    exact heMK_comp.isClosed.mem_of_tendsto hpt
      (Eventually.of_forall fun n ↦ ⟨u (φ n) y, huK (φ n) hy.1, rfl⟩)
  let v : ℝ × ℝ → M := fun y ↦ if hy : y ∈ U₀ then Classical.choose (ha_mem y hy) else x_def
  have hvK : MapsTo v U₀ K := fun y hy ↦ by
    simp only [v, hy, ↓reduceDIte]; exact (Classical.choose_spec (ha_mem y hy)).1
  have heMv (y : ℝ × ℝ) (hy : y ∈ U₀) : eM (v y) = a ⟨y, hy⟩ := by
    simp only [v, hy, ↓reduceDIte]; exact (Classical.choose_spec (ha_mem y hy)).2
  let vW : C(U₀, W_emb) := ⟨fun y ↦ ⟨v y.val, hKW (hvK y.property)⟩,
    emb.isEmbedding.continuous_iff.2 <| by
    have : emb ∘ (fun y : U₀ ↦ (⟨v y.val, hKW (hvK y.property)⟩ : W_emb)) = a := by
      funext y
      rw [Function.comp_apply, ← heM_eq (v y.val) (hKW (hvK y.property)), heMv y.val y.property]
    rw [this]; exact a.continuous⟩
  let uW : ℕ → C(U₀, W_emb) := fun n ↦
    ⟨fun y ↦ ⟨u (φ n) y.val, hKW (huK (φ n) y.property.1)⟩,
      (((hu (φ n)).continuousOn.mono sdiff_subset).domRestrict).subtype_mk fun y ↦
        hKW (huK (φ n) y.property.1)⟩
  have hvc : ContinuousOn v U₀ :=
    continuousOn_iff_continuous_domRestrict.2 (continuous_subtypeVal.comp vW.continuous)
  have hlim_W : Tendsto uW atTop (𝓝 vW) := by
    refine (ContinuousMap.isInducing_postcomp ⟨emb, emb.isEmbedding.continuous⟩
      emb.isEmbedding.isInducing).tendsto_nhds_iff.2 ?_
    have heq_u : (⟨emb, emb.isEmbedding.continuous⟩ : C(W_emb, _)).comp ∘ uW = Umap ∘ χ₂ := by
      funext n; exact ContinuousMap.ext fun y ↦ (heM_eq _ _).symm
    have heq_v : (⟨emb, emb.isEmbedding.continuous⟩ : C(W_emb, _)).comp vW = a :=
      ContinuousMap.ext fun y ↦ by
        dsimp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, vW]
        rw [← heM_eq (v y.val) (hKW (hvK y.property)), heMv y.val y.property]
    rw [heq_u, heq_v]; exact hlim_a
  have hlim_M : Tendsto (fun n ↦ (⟨Subtype.val, continuous_subtypeVal⟩ : C(W_emb, M)).comp (uW n))
      atTop (𝓝 ((⟨Subtype.val, continuous_subtypeVal⟩ : C(W_emb, M)).comp vW)) :=
    (ContinuousMap.continuous_postcomp
      ⟨Subtype.val, continuous_subtypeVal⟩).continuousAt.tendsto.comp hlim_W
  have hco : ∀ C' U, IsCompact C' → C' ⊆ U₀ → IsOpen U → MapsTo v C' U →
      ∀ᶠ n in atTop, MapsTo (u (φ n)) C' U := by
    intro C' U hC' hC'U₀ hU hvU
    have hL : IsCompact (((↑) : U₀ → ℝ × ℝ) ⁻¹' C') := IsInducing.subtypeVal.isCompact_preimage' hC'
      (by simpa [Subtype.range_coe_subtype] using hC'U₀)
    have hmap : MapsTo ((⟨Subtype.val, continuous_subtypeVal⟩ : C(W_emb, M)).comp vW)
        (((↑) : U₀ → ℝ × ℝ) ⁻¹' C') U := fun y hy ↦ hvU hy
    filter_upwards [(ContinuousMap.tendsto_nhds_compactOpen.1 hlim_M) _ hL U hU hmap] with
      n hn y hy
    exact hn (x := ⟨y, hC'U₀ hy⟩) hy
  have he_bd_φ : ∀ C', IsCompact C' → C' ⊆ U₀ → ∃ M₀, ∀ n, ∀ y ∈ C', e (φ n) y ≤ M₀ :=
    fun C' hC' hC'U₀ ↦ let ⟨M₀, hM₀⟩ := he_bd C' hC' hC'U₀; ⟨M₀, fun n ↦ hM₀ (χ₁ (χ₂ n))⟩
  -- Step 4: Assemble all conclusions.
  refine ⟨φ, p₀, Z, v, hφ, hp₀, hplim₁.comp hχ₂.tendsto_atTop, hZΩ, hcard,
    fun z hz ε hε ↦ (hχ₁.comp hχ₂).tendsto_atTop.eventually (hconc z hz ε hε),
    he_bd_φ, hvc, hvK, hco, ?_, ?_⟩
  · intro y hy
    rw [_root_.tendsto_nhds]
    intro U hU hvyU
    filter_upwards [hco {y} U isCompact_singleton (singleton_subset_iff.2 hy) hU
      (by simpa using hvyU)] with n hn
    exact hn rfl
  · intro α C' hC' hC'U₀ hvα
    refine ⟨chart_tendstoUniformlyOn_of_compactOpen
      (fun n ↦ (hu (φ n)).continuousOn.mono sdiff_subset) hvc hco α hC' hC'U₀ hvα, ?_⟩
    exact hω.chart_eventually_norm_fderiv_le hW hKs hKt hJ hC hD hK hCDKW hJt hΩ hΩD sdiff_subset
      (fun n ↦ hpC (φ n)) (fun n ↦ hu (φ n)) (fun n ↦ hfl (φ n)) (fun n ↦ huK (φ n)) hvc hco
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
      IsOpen Ω → Ω ⊆ D → (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv Ks Kt (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M),
        StrictMono φ ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M₀, ∀ n, ∀ y ∈ C', ω.floerEnergyDensity Ks Kt (u (φ n)) y ≤ M₀) ∧
        ContinuousOn v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        (∀ C' U, IsCompact C' → C' ⊆ Ω \ ↑Z → IsOpen U → MapsTo v C' U →
          ∀ᶠ n in atTop, MapsTo (u (φ n)) C' U) ∧
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
  obtain ⟨φ, -, Z, v, hφ, -, -, hrest⟩ :=
    hconv (p := fun _ ↦ 0) hΩ hΩD (fun _ ↦ rfl) hu hfl huK hint hE
  exact ⟨φ, Z, v, hφ, hrest⟩

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
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 3 (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
        (ω.perturbedMFDeriv (Ks (p k)) (Kt (p k)) (u k) z).toLinearMap) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M),
        StrictMono φ ∧ p₀ ∈ C ∧ Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n)))
            (u (φ n)) y) ∧
        (∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z →
          ∃ M₀, ∀ n, ∀ y ∈ C', ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n))) (u (φ n)) y ≤
            M₀) ∧
        ContinuousOn v (Ω \ ↑Z) ∧
        (∀ C' U, IsCompact C' → C' ⊆ Ω \ ↑Z → IsOpen U → MapsTo v C' U →
          ∀ᶠ n in atTop, MapsTo (u (φ n)) C' U) ∧
        (∀ y ∈ Ω \ ↑Z, Tendsto (fun n ↦ u (φ n) y) atTop (𝓝 (v y))) ∧
        (∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω \ ↑Z → MapsTo v C' (extChartAt I α).source →
          TendstoUniformlyOn (fun n ↦ extChartAt I α ∘ u (φ n)) (extChartAt I α ∘ v) atTop C' ∧
          ∃ M₀, ∀ᶠ n in atTop, ∀ y ∈ C', ‖fderiv ℝ (extChartAt I α ∘ u (φ n)) y‖ ≤ M₀) := by
  obtain ⟨δ, hδ, hconv⟩ := hω.exists_pos_forall_tendsto_subseq_off_finset_of_isCompact
    hW hKs hKt hJ hC hD isCompact_univ hCDW fun p hp z hz x _ ↦ hJt p hp z hz x
  refine ⟨δ, hδ, fun Ω p u E₀ hΩ hΩD hpC hu hfl hint hE ↦ ?_⟩
  obtain ⟨φ, p₀, Z, v, hφ, hp₀, hplim, hZΩ, hcard, hconc, hebd, hvc, -, hco, hpt, hch⟩ :=
    hconv hΩ hΩD hpC hu hfl (fun _ ↦ mapsTo_univ _ _) hint hE
  exact ⟨φ, p₀, Z, v, hφ, hp₀, hplim, hZΩ, hcard, hconc, hebd, hvc, hco, hpt, hch⟩

end Compactness

section DerivativeConvergence

/-- Local `C¹` convergence and passage of the chart Floer equation on a small disc around `z₀ ∈ Ω`
mapped by `v` into `(extChartAt I α).source`. -/
private theorem chart_c1_on_ball {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P] [I.Boundaryless] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {p : ℕ → P} {p₀ : P} {u : ℕ → ℝ × ℝ → M} {v : ℝ × ℝ → M}
    (hp : Tendsto p atTop (𝓝 p₀)) (hvW : ∀ y ∈ Ω, (p₀, (y, v y)) ∈ W)
    (hu : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u n) Ω)
    (hfl : ∀ n, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p n) y (u n y))
      (ω.perturbedMFDeriv (Ks (p n)) (Kt (p n)) (u n) y).toLinearMap)
    (hvc : ContinuousOn v Ω)
    (hco : ∀ C' U, IsCompact C' → C' ⊆ Ω → IsOpen U → MapsTo v C' U →
      ∀ᶠ n in atTop, MapsTo (u n) C' U)
    (hbd : ∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω → MapsTo v C' (extChartAt I α).source →
      ∃ M₀, ∀ᶠ n in atTop, ∀ y ∈ C', ‖fderiv ℝ (extChartAt I α ∘ u n) y‖ ≤ M₀)
    (α : M) {z₀ : ℝ × ℝ} (hz₀ : z₀ ∈ Ω) (hvz₀ : v z₀ ∈ (extChartAt I α).source) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ MapsTo v (ball z₀ r) (extChartAt I α).source ∧
      ContDiffOn ℝ 1 (extChartAt I α ∘ v) (ball z₀ r) ∧
      TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u n))
        (fderiv ℝ (extChartAt I α ∘ v)) atTop (ball z₀ r) ∧
      fderiv ℝ (extChartAt I α ∘ v) z₀ stdComplexLineImag -
          ω.hamiltonianVectorFieldInChartAt α (Kt p₀) (z₀, extChartAt I α (v z₀)) =
        Floer.almostComplexInChartAt I α (J p₀) (z₀, extChartAt I α (v z₀))
          (fderiv ℝ (extChartAt I α ∘ v) z₀ stdComplexLineReal -
            ω.hamiltonianVectorFieldInChartAt α (Ks p₀) (z₀, extChartAt I α (v z₀))) := by
  set e := extChartAt I α
  set eℂ := Complex.equivRealProdCLM
  -- Step 1: Choose a small closed disc around `z₀` mapped into `e.source` with uniform `C¹` bound.
  have hU_open : IsOpen (Ω ∩ v ⁻¹' e.source) :=
    hvc.isOpen_inter_preimage hΩ (isOpen_extChartAt_source α)
  obtain ⟨r, hr, hcl_sub⟩ := Metric.nhds_basis_closedBall.mem_iff.1
    (hU_open.mem_nhds ⟨hz₀, hvz₀⟩)
  have hcl_Ω : closedBall z₀ r ⊆ Ω := hcl_sub.trans inter_subset_left
  have hcl_v : MapsTo v (closedBall z₀ r) e.source := fun y hy ↦ (hcl_sub hy).2
  have hev_src := hco (closedBall z₀ r) e.source (isCompact_closedBall z₀ r) hcl_Ω
    (isOpen_extChartAt_source α) hcl_v
  obtain ⟨M₀, hev_bd⟩ := hbd α (closedBall z₀ r) (isCompact_closedBall z₀ r) hcl_Ω hcl_v
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev_src.and hev_bd)
  -- Step 2: Set up the `C¹` coordinate Floer data on `ℂ` and apply parametric `C¹` convergence.
  have hXsM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 1) (by simp) hW hKs
  have hXtM := hω.contMDiffOn_hamiltonianVectorField_prod (n := 1) (by simp) hW hKt
  set Wα : Set (P × ((ℝ × ℝ) × E)) :=
    {q | q.2.2 ∈ e.target ∧ (q.1, (q.2.1, e.symm q.2.2)) ∈ W}
  have hWα : IsOpen Wα :=
    (continuousOn_fst.prodMk ((continuousOn_fst.comp continuousOn_snd (mapsTo_univ _ _)).prodMk
      ((continuousOn_extChartAt_symm α).comp (continuousOn_snd.comp continuousOn_snd
        (mapsTo_univ _ _)) fun _ hq ↦ hq))).isOpen_inter_preimage
      ((isOpen_extChartAt_target α).preimage (continuous_snd.comp continuous_snd)) hW
  let LP : P ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ P)) := toEuclidean
  let LE : E ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := toEuclidean
  let g : EuclideanSpace ℝ (Fin (Module.finrank ℝ P)) ×
      (ℂ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) → P × ((ℝ × ℝ) × E) :=
    fun q ↦ (LP.symm q.1, (eℂ q.2.1, LE.symm q.2.2))
  have hg : ContDiff ℝ 1 g := (LP.symm.contDiff.comp contDiff_fst).prodMk
    ((eℂ.contDiff.comp (contDiff_fst.comp contDiff_snd)).prodMk
      (LE.symm.contDiff.comp (contDiff_snd.comp contDiff_snd)))
  let J' : EuclideanSpace ℝ (Fin (Module.finrank ℝ P)) →
      ℂ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun q₁ q₂ ↦
    LE.toContinuousLinearMap.comp
      ((Floer.almostComplexInChartAt I α (J (LP.symm q₁)) (eℂ q₂.1, LE.symm q₂.2)).comp
        LE.symm.toContinuousLinearMap)
  let X' : EuclideanSpace ℝ (Fin (Module.finrank ℝ P)) →
      ℂ × EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) →
      ℂ →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) := fun q₁ q₂ ↦
    LE.toContinuousLinearMap.comp
      (((ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight
          (ω.hamiltonianVectorFieldInChartAt α (Ks (LP.symm q₁)) (eℂ q₂.1, LE.symm q₂.2)) +
        (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight
          (ω.hamiltonianVectorFieldInChartAt α (Kt (LP.symm q₁)) (eℂ q₂.1, LE.symm q₂.2))).comp
        eℂ.toContinuousLinearMap)
  have hJ' : ContDiffOn ℝ 1 (uncurry J') (g ⁻¹' Wα) :=
    contDiffOn_const.clm_comp
      (((Floer.contDiffOn_almostComplexInChartAt (n := 1) (by simp) α hJ).comp hg.contDiffOn
        (mapsTo_preimage _ _)).clm_comp contDiffOn_const)
  have hX' : ContDiffOn ℝ 1 (uncurry X') (g ⁻¹' Wα) :=
    contDiffOn_const.clm_comp
      ((((contDiffOn_const.smulRight
          ((ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 1) (by simp) α hXsM).comp
            hg.contDiffOn (mapsTo_preimage _ _))).add
        (contDiffOn_const.smulRight
          ((ω.contDiffOn_hamiltonianVectorFieldInChartAt (n := 1) (by simp) α hXtM).comp
            hg.contDiffOn (mapsTo_preimage _ _)))).clm_comp contDiffOn_const))
  set Uℂ : Set ℂ := eℂ ⁻¹' ball z₀ r
  have hUℂ : IsOpen Uℂ := isOpen_ball.preimage eℂ.continuous
  obtain ⟨hv_cd, hconv_tail, hCR_v⟩ := Floer.tendstoLocallyUniformlyOn_fderiv_of_floer_parametric
    (J := J') (X := X') (hWα.preimage hg.continuous) hJ' hX' hUℂ
    (p := fun n ↦ LP (p (n + N))) (p₀ := LP p₀)
    (u := fun n ↦ (LE ∘ (e ∘ u (n + N))) ∘ eℂ) (v := (LE ∘ (e ∘ v)) ∘ eℂ)
    ((LP.continuous.continuousAt.tendsto.comp hp).comp (tendsto_add_atTop_nat N))
    (fun y hy ↦ by
      have hysrc := hcl_v (ball_subset_closedBall hy)
      refine ⟨?_, ?_⟩
      · dsimp only [g, Function.comp_apply]
        rw [LE.symm_apply_apply]
        exact e.map_source hysrc
      · dsimp only [g, Function.comp_apply]
        rw [LP.symm_apply_apply, LE.symm_apply_apply, e.left_inv hysrc]
        exact hvW (eℂ y) (hcl_Ω (ball_subset_closedBall hy)))
    (fun n ↦ (LE.contDiff.comp_contDiffOn
      (contMDiffOn_iff_contDiffOn.1 <|
        (contMDiffOn_extChartAt (n := (⊤ : ℕ∞))).comp
          ((hu (n + N)).mono (ball_subset_closedBall.trans hcl_Ω))
          fun z hz ↦ by
            rw [mem_preimage, ← extChartAt_source I]
            exact (hN (n + N) (Nat.le_add_left N n)).1 (ball_subset_closedBall hz))).comp
      eℂ.contDiff.contDiffOn (mapsTo_preimage _ _))
    (fun n y hy w ↦ by
      simp only [J', ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        Function.comp_apply, LE.symm_apply_apply]
      rw [Floer.almostComplexInChartAt_apply_apply
        (e.map_source ((hN (n + N) (Nat.le_add_left N n)).1 (ball_subset_closedBall hy))),
        map_neg, LE.apply_symm_apply])
    (fun n y hy ↦ by
      have hzcl : eℂ y ∈ closedBall z₀ r := ball_subset_closedBall hy
      have hzΩ : eℂ y ∈ Ω := hcl_Ω hzcl
      have hsrc : u (n + N) (eℂ y) ∈ e.source := (hN (n + N) (Nat.le_add_left N n)).1 hzcl
      have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I (u (n + N)) (eℂ y) :=
        ((hu (n + N)).mdifferentiableOn (by simp)).mdifferentiableAt (hΩ.mem_nhds hzΩ)
      have hfl_n := ω.fderiv_extChartAt_comp_stdComplexLineImag_sub (J := J (p (n + N)))
        (Ks := Ks (p (n + N))) (Kt := Kt (p (n + N))) hdiff hsrc (hfl (n + N) (eℂ y) hzΩ)
      have hcongr := congrArg LE hfl_n
      simpa only [J', X', eℂ, LP.symm_apply_apply, LE.symm_apply_apply,
        ContinuousLinearEquiv.map_sub, LE.comp_fderiv, fderiv_comp_equivRealProdCLM_one,
        fderiv_comp_equivRealProdCLM_I, ContinuousLinearMap.comp_apply,
        ContinuousLinearEquiv.coe_coe, add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', equivRealProdCLM_one,
        equivRealProdCLM_I, stdComplexLineReal_fst, stdComplexLineReal_snd,
        stdComplexLineImag_fst, stdComplexLineImag_snd, one_smul, zero_smul, zero_add, add_zero,
        Function.comp_apply] using hcongr)
    (fun C'' _ hC''U ↦ ⟨‖(LE : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E)))‖ *
        max M₀ 0 * ‖(eℂ : ℂ →L[ℝ] ℝ × ℝ)‖, fun n y hy ↦ by
      have hzcl : eℂ y ∈ closedBall z₀ r := ball_subset_closedBall (hC''U hy)
      have h1 : ‖fderiv ℝ (e ∘ u (n + N)) (eℂ y)‖ ≤ max M₀ 0 :=
        ((hN (n + N) (Nat.le_add_left N n)).2 (eℂ y) hzcl).trans (le_max_left _ _)
      have hcomp : fderiv ℝ ((LE ∘ (e ∘ u (n + N))) ∘ eℂ) y =
          (LE : E →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))).comp
            ((fderiv ℝ (e ∘ u (n + N)) (eℂ y)).comp (eℂ : ℂ →L[ℝ] ℝ × ℝ)) := by
        rw [eℂ.comp_right_fderiv, LE.comp_fderiv, ContinuousLinearMap.comp_assoc]
      rw [hcomp]
      refine (opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_left
        ((opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _)))
        (norm_nonneg _)) |>.trans_eq (by ring)⟩)
    (fun y hy ↦ by
      have hysrc := hcl_v (ball_subset_closedBall hy)
      have hpt_u : Tendsto (fun n ↦ u (n + N) (eℂ y)) atTop (𝓝 (v (eℂ y))) := by
        rw [_root_.tendsto_nhds]
        intro U hU hvyU
        have hev := hco {eℂ y} U isCompact_singleton
          (singleton_subset_iff.2 (hcl_Ω (ball_subset_closedBall hy))) hU (by simpa using hvyU)
        filter_upwards [(tendsto_add_atTop_nat N).eventually hev] with n hn
        exact hn rfl
      exact (LE.continuous.continuousAt.tendsto).comp
        (((continuousOn_extChartAt α).continuousAt
          ((isOpen_extChartAt_source α).mem_nhds hysrc)).tendsto.comp hpt_u))
  -- Step 3: Transport `C¹` regularity, derivative convergence and the equation back to `ℝ × ℝ`.
  have hv_cd' : ContDiffOn ℝ 1 (e ∘ v) (ball z₀ r) := by
    have heq : (fun z ↦ LE.symm (((LE ∘ (e ∘ v)) ∘ eℂ) (eℂ.symm z))) = e ∘ v :=
      funext fun z ↦ by simp
    rw [← heq]
    exact LE.symm.contDiff.comp_contDiffOn
      (hv_cd.comp eℂ.symm.contDiff.contDiffOn fun z hz ↦ by simpa [Uℂ] using hz)
  let adj : (ℂ →L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) →L[ℝ] (ℝ × ℝ →L[ℝ] E) :=
    (ContinuousLinearMap.compL ℝ (ℝ × ℝ) ℂ E).flip eℂ.symm.toContinuousLinearMap ∘L
      (ContinuousLinearMap.compL ℝ ℂ (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) E)
        LE.symm.toContinuousLinearMap
  have hconv_real_tail : TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (e ∘ u (n + N)))
      (fderiv ℝ (e ∘ v)) atTop (ball z₀ r) := by
    have h1 := (adj.uniformContinuous.comp_tendstoLocallyUniformlyOn hconv_tail).comp eℂ.symm
      (fun z (hz : z ∈ ball z₀ r) ↦ by simpa [Uℂ] using hz) eℂ.symm.continuous.continuousOn
    refine (h1.congr_right fun z _ ↦ ?_).congr fun n z _ ↦ ?_
    · have heq : (LE.symm ∘ ((LE ∘ (e ∘ v)) ∘ eℂ)) ∘ eℂ.symm = e ∘ v :=
        funext fun w ↦ by simp
      have hL := LE.symm.comp_fderiv (f := (LE ∘ (e ∘ v)) ∘ eℂ) (x := eℂ.symm z)
      have hR := eℂ.symm.comp_right_fderiv (f := LE.symm ∘ ((LE ∘ (e ∘ v)) ∘ eℂ)) (x := z)
      rw [heq] at hR
      rw [hR, hL]
      rfl
    · have heq : (LE.symm ∘ ((LE ∘ (e ∘ u (n + N))) ∘ eℂ)) ∘ eℂ.symm = e ∘ u (n + N) :=
        funext fun w ↦ by simp
      have hL := LE.symm.comp_fderiv (f := (LE ∘ (e ∘ u (n + N))) ∘ eℂ) (x := eℂ.symm z)
      have hR := eℂ.symm.comp_right_fderiv
        (f := LE.symm ∘ ((LE ∘ (e ∘ u (n + N))) ∘ eℂ)) (x := z)
      rw [heq] at hR
      rw [hR, hL]
      rfl
  have hconv_real : TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (e ∘ u n))
      (fderiv ℝ (e ∘ v)) atTop (ball z₀ r) := by
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_ball] at hconv_real_tail ⊢
    intro C'' hC'' hC''c
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hmap : ∀ᶠ n in map (· + N) atTop,
        ∀ x ∈ C'', dist (fderiv ℝ (e ∘ v) x) (fderiv ℝ (e ∘ u n) x) < ε :=
      Filter.eventually_map.2
        (Metric.tendstoUniformlyOn_iff.1 (hconv_real_tail C'' hC'' hC''c) ε hε)
    rwa [Filter.map_add_atTop_eq_nat] at hmap
  refine ⟨r, hr, ball_subset_closedBall.trans hcl_Ω, hcl_v.mono_left ball_subset_closedBall, hv_cd',
    hconv_real, ?_⟩
  have hCR0 := congrArg LE.symm (hCR_v (eℂ.symm z₀)
    (show eℂ (eℂ.symm z₀) ∈ ball z₀ r by rw [eℂ.apply_symm_apply]; exact mem_ball_self hr))
  simpa only [J', X', eℂ, LP.symm_apply_apply, LE.symm_apply_apply, LE.comp_fderiv,
    ContinuousLinearEquiv.map_sub, fderiv_comp_equivRealProdCLM_one,
    fderiv_comp_equivRealProdCLM_I, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, add_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', equivRealProdCLM_one,
    equivRealProdCLM_I, stdComplexLineReal_fst, stdComplexLineReal_snd,
    stdComplexLineImag_fst, stdComplexLineImag_snd, one_smul, zero_smul, zero_add, add_zero,
    Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using hCR0

/-- **Global `C¹` convergence and passage of the Floer equation to the limit on a manifold.**
Let `ω` be a nondegenerate two-form on a boundaryless manifold `M` modelled on a
finite-dimensional space `E`, and let `P` be a finite-dimensional parameter space. Let `K_s, K_t`
be jointly `C²` and `J` jointly `C¹` on an open set `W ⊆ P × ((ℝ × ℝ) × M)`. Suppose `u_n` are
smooth (`C^∞`) solutions of the Floer equation on an open `Ω ⊆ ℝ × ℝ` for parameters `p_n → p₀`,
converging in the compact-open topology to a continuous map `v : Ω → M` with
`(p₀, (y, v y)) ∈ W` on `Ω`, and suppose the chart differentials `d(extChartAt I α ∘ u_n)` are
eventually uniformly bounded on every compact `C' ⊆ Ω` with `MapsTo v C' (extChartAt I α).source`.

Then `v` is `C¹` on `Ω`, solves the intrinsic Floer equation `(dv - X_{K_{p₀}})^{0,1} = 0` for
`J_{p₀}` at every point of `Ω`, and in every chart `extChartAt I α`, the differentials
`d(extChartAt I α ∘ u_n)` converge uniformly to `d(extChartAt I α ∘ v)` on every compact
`C' ⊆ Ω` with `MapsTo v C' (extChartAt I α).source`. -/
theorem contMDiffOn_one_and_isComplexLinearMap_of_tendsto_floer_parametric
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [I.Boundaryless] {ω : SmoothTwoForm I M} (hω : ω.IsNondegenerate)
    {J : P → ℝ × ℝ → (x : M) → AlmostComplexStructure (TangentSpace I x)}
    {Ks Kt : P → ℝ × ℝ → M → ℝ} {W : Set (P × ((ℝ × ℝ) × M))} (hW : IsOpen W)
    (hKs : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ Ks q.1 q.2.1 q.2.2) W)
    (hKt : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) 𝓘(ℝ) 2
      (fun q : P × ((ℝ × ℝ) × M) ↦ Kt q.1 q.2.1 q.2.2) W)
    (hJ : ContMDiffOn (𝓘(ℝ, P).prod (𝓘(ℝ, ℝ × ℝ).prod I)) (I.prod 𝓘(ℝ, E →L[ℝ] E)) 1
      (fun q : P × ((ℝ × ℝ) × M) ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x) q.2.2
        (J q.1 q.2.1 q.2.2).toLinearMap.toContinuousLinearMap) W)
    {Ω : Set (ℝ × ℝ)} (hΩ : IsOpen Ω) {p : ℕ → P} {p₀ : P} {u : ℕ → ℝ × ℝ → M} {v : ℝ × ℝ → M}
    (hp : Tendsto p atTop (𝓝 p₀)) (hvW : ∀ y ∈ Ω, (p₀, (y, v y)) ∈ W)
    (hu : ∀ n, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u n) Ω)
    (hfl : ∀ n, ∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p n) y (u n y))
      (ω.perturbedMFDeriv (Ks (p n)) (Kt (p n)) (u n) y).toLinearMap)
    (hvc : ContinuousOn v Ω)
    (hco : ∀ C' U, IsCompact C' → C' ⊆ Ω → IsOpen U → MapsTo v C' U →
      ∀ᶠ n in atTop, MapsTo (u n) C' U)
    (hbd : ∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω → MapsTo v C' (extChartAt I α).source →
      ∃ M₀, ∀ᶠ n in atTop, ∀ y ∈ C', ‖fderiv ℝ (extChartAt I α ∘ u n) y‖ ≤ M₀) :
    ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v Ω ∧
      (∀ y ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p₀ y (v y))
        (ω.perturbedMFDeriv (Ks p₀) (Kt p₀) v y).toLinearMap) ∧
      ∀ α : M, ∀ C', IsCompact C' → C' ⊆ Ω → MapsTo v C' (extChartAt I α).source →
        TendstoUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u n))
          (fderiv ℝ (extChartAt I α ∘ v)) atTop C' := by
  have hv_cmd : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v Ω := by
    intro z₀ hz₀
    obtain ⟨r, hr, -, -, hv_cd, -, -⟩ :=
      hω.chart_c1_on_ball hW hKs hKt hJ hΩ hp hvW hu hfl hvc hco hbd (v z₀) hz₀
        (mem_extChartAt_source (v z₀))
    have hAt : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) I 1 v z₀ := by
      rw [contMDiffAt_iff]
      refine ⟨hvc.continuousAt (hΩ.mem_nhds hz₀), ?_⟩
      simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
        Function.comp_id, id_eq] using
        (hv_cd.contDiffAt (ball_mem_nhds z₀ hr)).contDiffWithinAt
    exact hAt.contMDiffWithinAt
  refine ⟨hv_cmd, ?_, ?_⟩
  · intro z₀ hz₀
    obtain ⟨-, -, -, -, -, -, hCR⟩ :=
      hω.chart_c1_on_ball hW hKs hKt hJ hΩ hp hvW hu hfl hvc hco hbd (v z₀) hz₀
        (mem_extChartAt_source (v z₀))
    have hdiff : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I v z₀ :=
      (hv_cmd.mdifferentiableOn one_ne_zero).mdifferentiableAt (hΩ.mem_nhds hz₀)
    exact (ω.isComplexLinearMap_perturbedMFDeriv_iff_fderiv_extChartAt_comp hdiff
      (mem_extChartAt_source (v z₀))).2 hCR
  · intro α C' hC' hC'Ω hvα
    set U := Ω ∩ v ⁻¹' (extChartAt I α).source
    have hU : IsOpen U := hvc.isOpen_inter_preimage hΩ (isOpen_extChartAt_source α)
    have hball : ∀ z : U, ∃ r > 0, TendstoLocallyUniformlyOn
        (fun n ↦ fderiv ℝ (extChartAt I α ∘ u n)) (fderiv ℝ (extChartAt I α ∘ v)) atTop
        (ball z.val r) := fun z ↦ by
      obtain ⟨r, hr, -, -, -, hconv, -⟩ :=
        hω.chart_c1_on_ball hW hKs hKt hJ hΩ hp hvW hu hfl hvc hco hbd α z.property.1 z.property.2
      exact ⟨r, hr, hconv⟩
    choose r hr hconv using hball
    have hloc : TendstoLocallyUniformlyOn (fun n ↦ fderiv ℝ (extChartAt I α ∘ u n))
        (fderiv ℝ (extChartAt I α ∘ v)) atTop U :=
      (tendstoLocallyUniformlyOn_iUnion (fun _ ↦ isOpen_ball) hconv).mono fun z hz ↦
        mem_iUnion.2 ⟨⟨z, hz⟩, mem_ball_self (hr ⟨z, hz⟩)⟩
    exact (tendstoLocallyUniformlyOn_iff_forall_isCompact hU).1 hloc C'
      (fun y hy ↦ ⟨hC'Ω hy, hvα hy⟩) hC'

/-- **Global `C¹` Gromov–Floer compactness for smooth solutions on a manifold over a compact
parameter window.** Combines
`TauCeti.SmoothTwoForm.IsNondegenerate.exists_pos_forall_tendsto_subseq_off_finset_of_isCompact`
with `contMDiffOn_one_and_isComplexLinearMap_of_tendsto_floer_parametric` when the parameter space
`P` is finite-dimensional and the solutions `u_k` are smooth (`C^∞`). In addition to compact-open
convergence and energy quantization off the finite bubbling set `Z ⊆ Ω`, the limit `v` is `C¹` on
`Ω \ Z`, solves the intrinsic Floer equation for the limit parameter `p₀` at every point of
`Ω \ Z`, and in every chart `extChartAt I α` both the coordinate maps and their differentials
converge uniformly on every compact `C' ⊆ Ω \ Z` with `MapsTo v C' (extChartAt I α).source`. -/
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
      (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J (p k) z (u k z))
        (ω.perturbedMFDeriv (Ks (p k)) (Kt (p k)) (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity (Ks (p k)) (Kt (p k)) (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (p₀ : P) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M),
        StrictMono φ ∧ p₀ ∈ C ∧ Tendsto (fun n ↦ p (φ n)) atTop (𝓝 p₀) ∧
        ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity (Ks (p (φ n))) (Kt (p (φ n)))
            (u (φ n)) y) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        (∀ y ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J p₀ y (v y))
          (ω.perturbedMFDeriv (Ks p₀) (Kt p₀) v y).toLinearMap) ∧
        (∀ C' U, IsCompact C' → C' ⊆ Ω \ ↑Z → IsOpen U → MapsTo v C' U →
          ∀ᶠ n in atTop, MapsTo (u (φ n)) C' U) ∧
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
  obtain ⟨φ, q₀, Z, v, hφ, ⟨p₀, hp₀, rfl⟩, hqlim, hZΩ, hcard, hconc, -, hvc, hvK, hco, -, hch⟩ :=
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
      (fun n ↦ (hu (φ n)).mono sdiff_subset) (fun n y hy ↦ hfl (φ n) y hy.1) hvc hco
      fun α C' hC' hC'Z hvα ↦ (hch α C' hC' hC'Z hvα).2
  exact ⟨φ, p₀, Z, v, hφ, hp₀, hplim, hZΩ, hcard, hconc', hv_cmd, hvK, hv_fl, hco,
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
      IsOpen Ω → Ω ⊆ D → (∀ k, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I (⊤ : ℕ∞) (u k) Ω) →
      (∀ k, ∀ z ∈ Ω, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J z (u k z))
        (ω.perturbedMFDeriv Ks Kt (u k) z).toLinearMap) →
      (∀ k, MapsTo (u k) Ω K) →
      (∀ k, IntegrableOn (ω.floerEnergyDensity Ks Kt (u k)) Ω) →
      (∀ k, ∫ z in Ω, ω.floerEnergyDensity Ks Kt (u k) z ≤ E₀) →
      ∃ (φ : ℕ → ℕ) (Z : Finset (ℝ × ℝ)) (v : ℝ × ℝ → M),
        StrictMono φ ∧ ↑Z ⊆ Ω ∧ Z.card * δ ≤ E₀ ∧
        (∀ z ∈ Z, ∀ ε > 0, ∀ᶠ n in atTop,
          δ ≤ ∫ y in ball z ε ∩ Ω, ω.floerEnergyDensity Ks Kt (u (φ n)) y) ∧
        ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 v (Ω \ ↑Z) ∧ MapsTo v (Ω \ ↑Z) K ∧
        (∀ y ∈ Ω \ ↑Z, IsComplexLinearMap (AlmostComplexStructure.product ℝ) (J y (v y))
          (ω.perturbedMFDeriv Ks Kt v y).toLinearMap) ∧
        (∀ C' U, IsCompact C' → C' ⊆ Ω \ ↑Z → IsOpen U → MapsTo v C' U →
          ∀ᶠ n in atTop, MapsTo (u (φ n)) C' U) ∧
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
  obtain ⟨φ, -, Z, v, hφ, -, -, hrest⟩ :=
    hconv (p := fun _ ↦ 0) hΩ hΩD (fun _ ↦ rfl) hu hfl huK hint hE
  exact ⟨φ, Z, v, hφ, hrest⟩

end DerivativeConvergence

end TauCeti.SmoothTwoForm.IsNondegenerate
