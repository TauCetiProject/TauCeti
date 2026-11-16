/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.Topology.Algebra.Projectivization.Action
import Mathlib.Analysis.Matrix.Normed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Instances.Int
import Mathlib.Topology.Metrizable.Urysohn
import TauCeti.GroupTheory.Amenable.Extension
import TauCeti.GroupTheory.Amenable.Finite
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.MeasureTheory.Group.Action
import TauCeti.Topology.Compactification.OnePoint.Amenable

/-!
# Invariant probability measures on the projective line

Let `𝕜` be `ℝ` or `ℂ`, and let `G` be a group represented faithfully in `GL(2, 𝕜)` by matrices with
`‖det(φ g)‖ = 1` which escape compact sets of `Matrix (Fin 2) (Fin 2) 𝕜` along the cofinite filter.
If `G` preserves a Borel probability measure `μ` on the projective line `ℙ 𝕜 (Fin 2 → 𝕜)`, then `G`
has Følner sets (`TauCeti.HasFoelnerSets G`) and is amenable for every group topology
(`TauCeti.Amenable G`). This is the `GL(2, 𝕜)` case of Furstenberg's lemma on projective invariant
measures.

When `G` is finite the conclusion is immediate. When `G` is infinite, choose `g_n ∈ G` with
`‖φ g_n‖ → ∞`. On the compact unit sphere of `2 × 2` matrices over `𝕜`, a subsequence of
`‖φ g_n‖⁻¹ • φ g_n` converges to a matrix `B` of norm `1` and determinant `0`. By
`Projectivization.exists_linearProjectionDomain_eq_and_linearProjection_eq_of_det_eq_zero`,
`Projectivization.linearProjection B.mulVecLin` is defined away from a point `p` and takes a
constant value `q` there, so away from `p`,
`Projectivization.tendsto_smul_of_tendsto_smul_coe` shows that `φ g_n • y → q`; passing to a
further subsequence, `φ g_n • p` also converges to some `r`. Dominated convergence of
`∫ f(φ g_n • y) dμ(y) = ∫ f(y) dμ(y)` identifies `μ` with the convex combination
`μ {p} • δ_r + μ {p}ᶜ • δ_q`, so `μ` has an atom `x₀`. Thus the stabilizer of `x₀` in `G` has
finite index (`MeasureTheory.finiteIndex_stabilizer_of_smulInvariant_of_measure_singleton_ne_zero`);
since projective-line stabilizers in `GL(2, 𝕜)` are amenable
(`MonoidHom.amenable_comap_projectivization_stabilizer`), so is `G`
(`Subgroup.amenable_of_finiteIndex`).

Specializing to closed discrete subgroups of `SL(2, 𝕜)` (Fuchsian and Kleinian groups) and to
injective homomorphisms into `GL(2, ℤ)` supplies the invariant-measure step in Burger's criterion
for relative property (T) of `(ℤ² ⋊ G, ℤ²)`.

## Main results

* `TauCeti.hasFoelnerSets_of_map_smul_projectivization_eq`,
  `TauCeti.amenable_of_map_smul_projectivization_eq`: a group with a proper unimodular
  representation in `GL(2, 𝕜)` preserving a Borel probability measure on `ℙ 𝕜 (Fin 2 → 𝕜)` has
  Følner sets, hence is amenable.
* `TauCeti.hasFoelnerSets_of_injective_gl_int_of_map_smul_projectivization_eq`,
  `TauCeti.amenable_of_injective_gl_int_of_map_smul_projectivization_eq`: specialization to groups
  embedding in `GL(2, ℤ)`.
* `Subgroup.hasFoelnerSets_of_map_smul_projectivization_eq`,
  `Subgroup.amenable_of_map_smul_projectivization_eq`: specialization to discrete subgroups of
  `SL(2, 𝕜)` (in the root `Subgroup` namespace for dot notation on `H : Subgroup SL(2, 𝕜)`).

## References

* H. Furstenberg, *Boundary theory and stochastic processes on homogeneous spaces*, Proc. Sympos.
  Pure Math. 26 (1973), 193–229.
* B. Bekka, P. de la Harpe and A. Valette, *Kazhdan's Property (T)*, Cambridge University Press
  (2008), Lemma 4.2.3 and Proposition 4.2.4.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, Example 14.2.8.
-/

public section

noncomputable section

open Filter Matrix MeasureTheory MulAction Set Topology
open scoped BoundedContinuousFunction LinearAlgebra.Projectivization MatrixGroups

namespace TauCeti

section Furstenberg

variable {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace (ℙ 𝕜 (Fin 2 → 𝕜))]
  [BorelSpace (ℙ 𝕜 (Fin 2 → 𝕜))]

open scoped Matrix.Norms.Elementwise in
/-- **Furstenberg's lemma on the projective line.** If a group `G` admits an injective homomorphism
`φ : G →* GL (Fin 2) 𝕜` (`𝕜 = ℝ` or `ℂ`) with `‖(φ g).det‖ = 1` and `φ g` escaping compact sets of
`Matrix (Fin 2) (Fin 2) 𝕜` along `cofinite`, and `G` preserves a Borel probability measure `μ` on
`ℙ 𝕜 (Fin 2 → 𝕜)`, then `G` has Følner sets. -/
theorem hasFoelnerSets_of_map_smul_projectivization_eq {G : Type*} [Group G]
    {φ : G →* GL (Fin 2) 𝕜} (hφ : Function.Injective φ)
    (hdet : ∀ g : G, ‖(φ g : Matrix (Fin 2) (Fin 2) 𝕜).det‖ = 1)
    (hproper : Tendsto (fun g : G => (φ g : Matrix (Fin 2) (Fin 2) 𝕜)) cofinite
      (cocompact (Matrix (Fin 2) (Fin 2) 𝕜)))
    {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, Measure.map (φ g • ·) μ = μ) :
    HasFoelnerSets G := by
  let _ : TopologicalSpace G := ⊥
  have : DiscreteTopology G := ⟨rfl⟩
  rw [← amenable_iff_hasFoelnerSets]
  by_cases hfin : Finite G
  · exact Amenable.of_finite
  rw [not_finite_iff_infinite] at hfin
  have := FiniteDimensional.proper_rclike 𝕜 (Matrix (Fin 2) (Fin 2) 𝕜)
  have hnorm_top : Tendsto (fun g : G => ‖(φ g : Matrix (Fin 2) (Fin 2) 𝕜)‖) cofinite atTop :=
    tendsto_norm_cocompact_atTop.comp hproper
  -- Choose `u n ∈ G` with `‖φ (u n)‖ ≥ n + 1`.
  have hex (n : ℕ) : ∃ g : G, (n : ℝ) + 1 ≤ ‖(φ g : Matrix (Fin 2) (Fin 2) 𝕜)‖ := by
    have hfin_bad : {g : G | ¬ ((n : ℝ) + 1 ≤ ‖(φ g : Matrix (Fin 2) (Fin 2) 𝕜)‖)}.Finite :=
      eventually_cofinite.mp (hnorm_top.eventually_ge_atTop ((n : ℝ) + 1))
    obtain ⟨g, hg⟩ := (Set.infinite_univ.sdiff hfin_bad).nonempty
    exact ⟨g, not_not.mp hg.2⟩
  choose u hu using hex
  let M : ℕ → ℝ := fun n => ‖(φ (u n) : Matrix (Fin 2) (Fin 2) 𝕜)‖
  have hM_pos (n : ℕ) : 0 < M n := lt_of_lt_of_le (by positivity) (hu n)
  have hM_top : Tendsto M atTop atTop :=
    tendsto_atTop_mono hu (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  -- Normalize `φ (u n)` onto the compact unit sphere of `2 × 2` matrices over `𝕜`.
  let A : ℕ → Matrix (Fin 2) (Fin 2) 𝕜 :=
    fun n => (((M n)⁻¹ : ℝ) : 𝕜) • (φ (u n) : Matrix (Fin 2) (Fin 2) 𝕜)
  have hA_mem (n : ℕ) : A n ∈ Metric.sphere (0 : Matrix (Fin 2) (Fin 2) 𝕜) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_smul, RCLike.norm_ofReal,
      abs_of_nonneg (inv_nonneg.mpr (hM_pos n).le)]
    exact inv_mul_cancel₀ (hM_pos n).ne'
  obtain ⟨B, hBsphere, k₁, hk₁, hBk₁⟩ :=
    (isCompact_sphere (0 : Matrix (Fin 2) (Fin 2) 𝕜) 1).tendsto_subseq hA_mem
  have hB_norm : ‖B‖ = 1 := mem_sphere_zero_iff_norm.mp hBsphere
  have hB0 : B ≠ 0 := fun h => by simp [h] at hB_norm
  -- The limit `B` has determinant `0` since `‖det (A n)‖ = ‖φ (u n)‖⁻² → 0`.
  have hB_det : B.det = 0 := by
    have hdet_tendsto : Tendsto (fun n => ‖(A (k₁ n)).det‖) atTop (𝓝 ‖B.det‖) :=
      ((continuous_id.matrix_det.tendsto B).comp hBk₁).norm
    have hdet_zero : Tendsto (fun n => ‖(A (k₁ n)).det‖) atTop (𝓝 0) := by
      have hinv : Tendsto (fun n => ((M (k₁ n))⁻¹) ^ 2) atTop (𝓝 0) := by
        simpa using ((tendsto_inv_atTop_zero.comp (hM_top.comp hk₁.tendsto_atTop)).pow 2)
      refine hinv.congr fun n => ?_
      dsimp only [A]
      rw [Matrix.det_smul, Fintype.card_fin, norm_mul, norm_pow, RCLike.norm_ofReal,
        abs_of_nonneg (inv_nonneg.mpr (hM_pos (k₁ n)).le), hdet, mul_one]
    exact norm_eq_zero.mp (tendsto_nhds_unique hdet_tendsto hdet_zero)
  obtain ⟨p, q, hp_dom, hpq⟩ :=
    Projectivization.exists_linearProjectionDomain_eq_and_linearProjection_eq_of_det_eq_zero
      hB0 hB_det
  -- Pass to a further subsequence so `φ (u _) • p` also converges to some `r`.
  obtain ⟨r, -, k₂, hk₂, hrk₂⟩ :=
    isCompact_univ.tendsto_subseq (x := fun n => φ (u (k₁ n)) • p) (fun _ => mem_univ _)
  let gseq : ℕ → G := fun n => u (k₁ (k₂ n))
  have hlim_off {y : ℙ 𝕜 (Fin 2 → 𝕜)} (hy : y ≠ p) :
      Tendsto (fun n => φ (gseq n) • y) atTop (𝓝 q) := by
    have hy_dom : y ∈ Projectivization.linearProjectionDomain B.mulVecLin :=
      hp_dom.symm ▸ Set.mem_compl_singleton_iff.mpr hy
    have hsub : Tendsto (fun n => (((M (k₁ (k₂ n)))⁻¹ : ℝ) : 𝕜) •
        (φ (gseq n) : Matrix (Fin 2) (Fin 2) 𝕜)) atTop (𝓝 B) :=
      hBk₁.comp hk₂.tendsto_atTop
    simpa [hpq y hy] using
      Projectivization.tendsto_smul_of_tendsto_smul_coe hsub tendsto_const_nhds hy_dom
  -- Dominated convergence identifies `μ` with `μ {p} • dirac r + μ {p}ᶜ • dirac q`.
  let ν : Measure (ℙ 𝕜 (Fin 2 → 𝕜)) := μ {p} • Measure.dirac r + μ {p}ᶜ • Measure.dirac q
  have : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    simp only [ν, add_apply, smul_apply,
      Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply,
      smul_eq_mul, mul_one]
    rw [measure_add_measure_compl (measurableSet_singleton p), measure_univ]
  have hμ_eq_ν : μ = ν := by
    classical
    refine ext_of_forall_integral_eq_of_IsFiniteMeasure fun f => ?_
    have hconst (n : ℕ) : ∫ y, f (φ (gseq n) • y) ∂μ = ∫ y, f y ∂μ := by
      calc ∫ y, f (φ (gseq n) • y) ∂μ
          = ∫ y, f y ∂(Measure.map (φ (gseq n) • ·) μ) :=
            (integral_map (continuous_const_smul (φ (gseq n))).aemeasurable
              f.continuous.aestronglyMeasurable).symm
        _ = ∫ y, f y ∂μ := by rw [hμ (gseq n)]
    have hpt (y : ℙ 𝕜 (Fin 2 → 𝕜)) :
        Tendsto (fun n => f (φ (gseq n) • y)) atTop (𝓝 (if y = p then f r else f q)) := by
      split_ifs with hy
      · subst hy
        exact (f.continuous.tendsto r).comp hrk₂
      · exact (f.continuous.tendsto q).comp (hlim_off hy)
    have hdom_conv :
        Tendsto (fun n => ∫ y, f (φ (gseq n) • y) ∂μ) atTop
          (𝓝 (∫ y, (if y = p then (f r : ℝ) else f q) ∂μ)) := by
      refine tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
        (fun n => (f.continuous.comp (continuous_const_smul _)).aestronglyMeasurable)
        (integrable_const ‖f‖)
        (fun n => ae_of_all _ fun y => f.norm_coe_le_norm _)
        (ae_of_all _ hpt)
    have hint_eq : ∫ y, f y ∂μ = ∫ y, (if y = p then (f r : ℝ) else f q) ∂μ :=
      tendsto_nhds_unique (tendsto_const_nhds.congr fun n => (hconst n).symm) hdom_conv
    have hite (y : ℙ 𝕜 (Fin 2 → 𝕜)) : (if y = p then (f r : ℝ) else f q) =
        ({p} : Set _).indicator (fun _ => (f r : ℝ)) y +
          ({p}ᶜ : Set _).indicator (fun _ => (f q : ℝ)) y := by
      by_cases hy : y = p <;> simp [hy]
    have hp_meas : MeasurableSet ({p} : Set (ℙ 𝕜 (Fin 2 → 𝕜))) := measurableSet_singleton p
    have hint_rhs :
        ∫ y, (if y = p then (f r : ℝ) else f q) ∂μ = μ.real {p} * f r + μ.real {p}ᶜ * f q := by
      simp_rw [hite]
      rw [integral_add ((integrable_const _).indicator hp_meas)
        ((integrable_const _).indicator hp_meas.compl),
        integral_indicator_const _ hp_meas, integral_indicator_const _ hp_meas.compl,
        smul_eq_mul, smul_eq_mul]
    have hint_ν : ∫ y, f y ∂ν = μ.real {p} * f r + μ.real {p}ᶜ * f q := by
      dsimp only [ν]
      rw [integral_add_measure
          ((f.integrable (μ := Measure.dirac r)).smul_measure (measure_ne_top μ {p}))
          ((f.integrable (μ := Measure.dirac q)).smul_measure (measure_ne_top μ {p}ᶜ)),
        integral_smul_measure, integral_smul_measure, integral_dirac, integral_dirac,
        smul_eq_mul, smul_eq_mul, Measure.real, Measure.real]
    linarith
  -- Hence `μ` gives positive mass to either `{r}` or `{q}`.
  have hatom : ∃ x₀ : ℙ 𝕜 (Fin 2 → 𝕜), μ {x₀} ≠ 0 := by
    by_contra! h0
    have h1 : μ ({r} ∪ {q}) = 1 := by
      rw [hμ_eq_ν]
      simp only [ν, add_apply, smul_apply,
        Measure.dirac_apply' _ ((measurableSet_singleton r).union (measurableSet_singleton q)),
        Set.indicator_of_mem (Set.mem_union_left _ (Set.mem_singleton r)),
        Set.indicator_of_mem (Set.mem_union_right _ (Set.mem_singleton q)),
        Pi.one_apply, smul_eq_mul, mul_one]
      rw [measure_add_measure_compl (measurableSet_singleton p), measure_univ]
    have hle : μ ({r} ∪ {q}) ≤ μ {r} + μ {q} := measure_union_le _ _
    rw [h1, h0 r, h0 q, add_zero] at hle
    exact one_ne_zero (le_bot_iff.mp hle)
  obtain ⟨x₀, hx₀⟩ := hatom
  have : SMulInvariantMeasure φ.range (ℙ 𝕜 (Fin 2 → 𝕜)) μ :=
    ⟨fun ⟨_, g, rfl⟩ s hs =>
      (Measure.map_apply (continuous_const_smul (φ g)).measurable hs).symm.trans
        (congrArg (· s) (hμ g))⟩
  have hfin_range : (stabilizer φ.range x₀).FiniteIndex :=
    finiteIndex_stabilizer_of_smulInvariant_of_measure_singleton_ne_zero φ.range hx₀
  have : ((stabilizer (GL (Fin 2) 𝕜) x₀).comap φ).FiniteIndex := by
    rw [Subgroup.finiteIndex_iff, Subgroup.index_comap, Subgroup.relIndex, stabilizer_subgroupOf,
      ← Subgroup.finiteIndex_iff]
    exact hfin_range
  have : Amenable ((stabilizer (GL (Fin 2) 𝕜) x₀).comap φ) :=
    φ.amenable_comap_projectivization_stabilizer hφ x₀
  exact ((stabilizer (GL (Fin 2) 𝕜) x₀).comap φ).amenable_of_finiteIndex

/-- Topological-group version of `hasFoelnerSets_of_map_smul_projectivization_eq`: the group is
amenable for every group topology. -/
theorem amenable_of_map_smul_projectivization_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {φ : G →* GL (Fin 2) 𝕜} (hφ : Function.Injective φ)
    (hdet : ∀ g : G, ‖(φ g : Matrix (Fin 2) (Fin 2) 𝕜).det‖ = 1)
    (hproper : Tendsto (fun g : G => (φ g : Matrix (Fin 2) (Fin 2) 𝕜)) cofinite
      (cocompact (Matrix (Fin 2) (Fin 2) 𝕜)))
    {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, Measure.map (φ g • ·) μ = μ) :
    Amenable G :=
  .of_hasFoelnerSets (hasFoelnerSets_of_map_smul_projectivization_eq hφ hdet hproper hμ)

/-- A group `G` embedding in `GL(2, ℤ)` and preserving a Borel probability measure on
`ℙ 𝕜 (Fin 2 → 𝕜)` (`𝕜 = ℝ` or `ℂ`) has Følner sets. -/
theorem hasFoelnerSets_of_injective_gl_int_of_map_smul_projectivization_eq {G : Type*} [Group G]
    {ψ : G →* GL (Fin 2) ℤ} (hψ : Function.Injective ψ)
    {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ g : G,
      Measure.map (Matrix.GeneralLinearGroup.map (Int.castRingHom 𝕜) (ψ g) • ·) μ = μ) :
    HasFoelnerSets G := by
  let φ : G →* GL (Fin 2) 𝕜 := (Matrix.GeneralLinearGroup.map (Int.castRingHom 𝕜)).comp ψ
  have hφ : Function.Injective φ :=
    (Matrix.GeneralLinearGroup.map_injective Int.cast_injective).comp hψ
  have hdet (g : G) : ‖(φ g : Matrix (Fin 2) (Fin 2) 𝕜).det‖ = 1 := by
    have hmap : (φ g : Matrix (Fin 2) (Fin 2) 𝕜) =
        (Int.castRingHom 𝕜).mapMatrix (ψ g : Matrix (Fin 2) (Fin 2) ℤ) := rfl
    rw [hmap, ← RingHom.map_det, Int.coe_castRingHom]
    rcases Int.units_eq_one_or (Matrix.GeneralLinearGroup.det (ψ g)) with hu | hu <;>
    · have hval : (ψ g : Matrix (Fin 2) (Fin 2) ℤ).det =
          ((Matrix.GeneralLinearGroup.det (ψ g) : ℤˣ) : ℤ) := rfl
      rw [hval, hu]
      simp
  have hproper : Tendsto (fun g : G => (φ g : Matrix (Fin 2) (Fin 2) 𝕜)) cofinite
      (cocompact (Matrix (Fin 2) (Fin 2) 𝕜)) := by
    have hce_int : IsClosedEmbedding ((↑) : ℤ → 𝕜) := by
      have heq : ((↑) : ℤ → 𝕜) = (RCLike.ofRealLI (K := 𝕜)) ∘ ((↑) : ℤ → ℝ) := by
        ext z
        simp
      rw [heq]
      exact (RCLike.ofRealLI (K := 𝕜)).isometry.isClosedEmbedding.comp
        Int.isClosedEmbedding_coe_real
    have hce : IsClosedEmbedding
        ((Int.castRingHom 𝕜).mapMatrix : Matrix (Fin 2) (Fin 2) ℤ → Matrix (Fin 2) (Fin 2) 𝕜) :=
      IsClosedEmbedding.piMap fun _ => IsClosedEmbedding.piMap fun _ => hce_int
    have hco : Tendsto ((Int.castRingHom 𝕜).mapMatrix :
        Matrix (Fin 2) (Fin 2) ℤ → Matrix (Fin 2) (Fin 2) 𝕜)
        cofinite (cocompact (Matrix (Fin 2) (Fin 2) 𝕜)) := by
      rw [← Filter.cocompact_eq_cofinite (Matrix (Fin 2) (Fin 2) ℤ)]
      exact hce.tendsto_cocompact
    have hinj_val : Function.Injective (fun g : G => (ψ g : Matrix (Fin 2) (Fin 2) ℤ)) :=
      Units.val_injective.comp hψ
    exact hco.comp hinj_val.tendsto_cofinite
  exact hasFoelnerSets_of_map_smul_projectivization_eq hφ hdet hproper hμ

/-- Topological-group version of
`hasFoelnerSets_of_injective_gl_int_of_map_smul_projectivization_eq`. -/
theorem amenable_of_injective_gl_int_of_map_smul_projectivization_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    {ψ : G →* GL (Fin 2) ℤ} (hψ : Function.Injective ψ)
    {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ g : G,
      Measure.map (Matrix.GeneralLinearGroup.map (Int.castRingHom 𝕜) (ψ g) • ·) μ = μ) :
    Amenable G :=
  .of_hasFoelnerSets (hasFoelnerSets_of_injective_gl_int_of_map_smul_projectivization_eq hψ hμ)

end Furstenberg

end TauCeti

namespace Subgroup

open Filter Matrix MeasureTheory Topology
open scoped LinearAlgebra.Projectivization MatrixGroups

variable {𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace (ℙ 𝕜 (Fin 2 → 𝕜))]
  [BorelSpace (ℙ 𝕜 (Fin 2 → 𝕜))]

/-- A discrete subgroup of `SL(2, 𝕜)` (`𝕜 = ℝ` or `ℂ`) preserving a Borel probability measure on
`ℙ 𝕜 (Fin 2 → 𝕜)` has Følner sets. -/
theorem hasFoelnerSets_of_map_smul_projectivization_eq (H : Subgroup SL(2, 𝕜))
    [DiscreteTopology H] {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ h : H, Measure.map ((h : SL(2, 𝕜)) • ·) μ = μ) :
    TauCeti.HasFoelnerSets H := by
  let φ : H →* GL (Fin 2) 𝕜 := Matrix.SpecialLinearGroup.toGL.comp H.subtype
  have hφ : Function.Injective φ :=
    Matrix.SpecialLinearGroup.toGL_injective.comp H.subtype_injective
  have hdet (h : H) : ‖(φ h : Matrix (Fin 2) (Fin 2) 𝕜).det‖ = 1 := by
    simp [φ]
  have hclosed : IsClosed (H : Set SL(2, 𝕜)) := Subgroup.isClosed_of_discreteTopology
  have hce : IsClosedEmbedding (fun h : H => (φ h : Matrix (Fin 2) (Fin 2) 𝕜)) :=
    Matrix.SpecialLinearGroup.isClosedEmbedding_val.comp hclosed.isClosedEmbedding_subtypeVal
  have hproper : Tendsto (fun h : H => (φ h : Matrix (Fin 2) (Fin 2) 𝕜)) cofinite
      (cocompact (Matrix (Fin 2) (Fin 2) 𝕜)) := by
    rw [← Filter.cocompact_eq_cofinite H]
    exact hce.tendsto_cocompact
  -- Both actions multiply representatives on `ℙ 𝕜 (Fin 2 → 𝕜)` by the underlying matrix.
  have hsmul (g : SL(2, 𝕜)) (x : ℙ 𝕜 (Fin 2 → 𝕜)) :
      Matrix.SpecialLinearGroup.toGL g • x = g • x := rfl
  exact TauCeti.hasFoelnerSets_of_map_smul_projectivization_eq hφ hdet hproper fun h => by
    simpa [φ, funext (hsmul h)] using hμ h

/-- A discrete subgroup of `SL(2, 𝕜)` (`𝕜 = ℝ` or `ℂ`) preserving a Borel probability measure on
`ℙ 𝕜 (Fin 2 → 𝕜)` is amenable. -/
theorem amenable_of_map_smul_projectivization_eq (H : Subgroup SL(2, 𝕜))
    [DiscreteTopology H] {μ : Measure (ℙ 𝕜 (Fin 2 → 𝕜))} [IsProbabilityMeasure μ]
    (hμ : ∀ h : H, Measure.map ((h : SL(2, 𝕜)) • ·) μ = μ) :
    TauCeti.Amenable H :=
  .of_hasFoelnerSets (H.hasFoelnerSets_of_map_smul_projectivization_eq hμ)

end Subgroup
