/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.RegularValue.Scalar.Level
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Cotangent

/-!
# The unit codisc and cosphere bundles of a Riemannian manifold

A Riemannian metric `g` on a manifold `M` measures covectors, and so singles out two subsets of the
cotangent bundle `T*M = TauCeti.CotangentBundle I M`:

* the **unit codisc bundle** `D*M = {z | ‖z.2‖ ≤ 1}` (`TauCeti.CotangentBundle.codiscBundle`);
* the **unit cosphere bundle** `S*M = {z | ‖z.2‖ = 1}` (`TauCeti.CotangentBundle.cosphereBundle`).

Here `‖p‖` is the norm of a covector for `g`, the operator norm for the metric norm on the tangent
space. With the canonical symplectic form of `T*M` and the Liouville form `-λ`, the codisc bundle
of a compact manifold is the standard example of a Liouville domain, and these are the sets on
which the symplectic capacities of cotangent bundles are computed. This file establishes their
point-set and smooth structure.

Both sets are closed, and compact when `M` is compact
(`TauCeti.CotangentBundle.isCompact_codiscBundle`): over a chart domain the bundle coordinates of a
covector of norm at most one are bounded, since the chart-local frame has bounded length over a
compact set.

Since every nonzero value is a regular value of the norm of covectors
(`TauCeti.CotangentBundle.isRegularValue_norm_snd`), `S*M` is a regular level. For a smooth metric
on a boundaryless manifold, it carries the atlas `TauCeti.scalarRegularLevelChartedSpace` of
regular levels, for which it is a smooth manifold of dimension `dim T*M - 1`
(`TauCeti.CotangentBundle.instIsManifoldCosphereBundle`) and a smoothly embedded hypersurface of
`T*M` (`TauCeti.CotangentBundle.isSmoothEmbedding_coe_cosphereBundle`) whose tangent spaces are
the kernels of the differential of the norm
(`TauCeti.CotangentBundle.range_mfderiv_coe_cosphereBundle`).

## Main definitions

* `TauCeti.CotangentBundle.codiscBundle`: the unit codisc bundle `D*M`.
* `TauCeti.CotangentBundle.cosphereBundle`: the unit cosphere bundle `S*M`.

## Main results

* `TauCeti.CotangentBundle.isClosed_codiscBundle` and
  `TauCeti.CotangentBundle.isCompact_codiscBundle`: `D*M` is closed, and compact over a compact
  manifold; similarly for `S*M`.
* `TauCeti.CotangentBundle.instIsManifoldCosphereBundle`: `S*M` is a smooth manifold.
* `TauCeti.CotangentBundle.isSmoothEmbedding_coe_cosphereBundle`: its inclusion into `T*M` is a
  smooth embedding.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 and Chapter 12.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.2.
-/

public section

noncomputable section

open Bundle Set Filter Metric Riemannian.Tensor
open Manifold
open scoped Manifold Topology ContDiff

namespace TauCeti

namespace CotangentBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The **unit codisc bundle** `D*M` of a Riemannian manifold: the covectors of norm at most one. -/
def codiscBundle : Set (CotangentBundle I M) :=
  {z | ‖z.2‖ ≤ 1}

variable (I M) in
/-- The **unit cosphere bundle** `S*M` of a Riemannian manifold: the covectors of norm one. Its
body is exposed because the manifold structure on `S*M` is that of the regular level
`{z // ‖z.2‖ = 1}`, read through this definition. -/
@[expose] def cosphereBundle : Set (CotangentBundle I M) :=
  {z | ‖z.2‖ = 1}

@[simp]
theorem mem_codiscBundle {z : CotangentBundle I M} : z ∈ codiscBundle I M ↔ ‖z.2‖ ≤ 1 :=
  Iff.rfl

@[simp]
theorem mem_cosphereBundle {z : CotangentBundle I M} : z ∈ cosphereBundle I M ↔ ‖z.2‖ = 1 :=
  Iff.rfl

theorem cosphereBundle_subset_codiscBundle : cosphereBundle I M ⊆ codiscBundle I M :=
  fun _ hz ↦ hz.le

/-- A covector of the unit cosphere bundle is not zero. -/
theorem snd_ne_zero_of_mem_cosphereBundle {z : CotangentBundle I M}
    (hz : z ∈ cosphereBundle I M) : z.2 ≠ 0 := fun h ↦ by
  rw [mem_cosphereBundle, h, (ContinuousLinearMap.opNorm_zero_iff _).2 rfl] at hz
  exact zero_ne_one hz

variable [FiniteDimensional ℝ E] [IsManifold I 1 M]

section Topology

variable [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

theorem isClosed_codiscBundle : IsClosed (codiscBundle I M) :=
  isClosed_le continuous_norm_snd continuous_const

theorem isClosed_cosphereBundle : IsClosed (cosphereBundle I M) :=
  isClosed_eq continuous_norm_snd continuous_const

/-- Over a neighbourhood of every point, the covectors of norm at most one lie in a compact set:
in the chart at the point, their base points stay in a compact set and their bundle coordinates
are bounded, because the chart-local frame has bounded length over it. -/
private theorem exists_isCompact_norm_le (x : M) :
    ∃ U ∈ 𝓝 x, ∃ L : Set (CotangentBundle I M), IsCompact L ∧
      ∀ z : CotangentBundle I M, z.proj ∈ U → ‖z.2‖ ≤ 1 → z ∈ L := by
  set φ := extChartAt I x
  set z₀ : CotangentBundle I M := ⟨x, 0⟩
  set Ψ := extChartAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) z₀
  -- A compact neighbourhood `K'` of `φ x` in the range of `I`, inside the chart target.
  obtain ⟨ε, ε0, hε⟩ := Metric.mem_nhdsWithin_iff.1 (extChartAt_target_mem_nhdsWithin (I := I) x)
  set K' := closedBall (φ x) (ε / 2) ∩ range I
  have hK'φ : K' ⊆ φ.target := fun q hq ↦
    hε ⟨closedBall_subset_ball (half_lt_self ε0) hq.1, hq.2⟩
  have hK' : IsCompact K' := (isCompact_closedBall _ _).inter_right I.isClosed_range
  -- Its preimage `K` is a compact subset of the chart source.
  set K := φ.symm '' K'
  have hK : IsCompact K := hK'.image_of_continuousOn ((continuousOn_extChartAt_symm x).mono hK'φ)
  have hKs : K ⊆ (chartAt H x).source := by
    rintro _ ⟨q, hq, rfl⟩
    rw [← extChartAt_source (I := I)]
    exact φ.map_target (hK'φ hq)
  -- The chart-local frame has length at most `C` over `K`.
  obtain ⟨C, hframe⟩ := exists_norm_chartLocalFrame_le (I := I) x hK hKs
  obtain ⟨C₀, -, hC₀⟩ := (Module.finBasis ℝ E).exists_opNorm_le (F := ℝ)
  refine ⟨φ.source ∩ φ ⁻¹' ball (φ x) (ε / 2), ?_, Ψ.symm '' (K' ×ˢ closedBall 0 (C₀ * max C 0)),
    ?_, ?_⟩
  · exact inter_mem (extChartAt_source_mem_nhds x)
      ((continuousAt_extChartAt x).preimage_mem_nhds (ball_mem_nhds _ (half_pos ε0)))
  · refine (hK'.prod (isCompact_closedBall _ _)).image_of_continuousOn
      ((continuousOn_extChartAt_symm z₀).mono ?_)
    rintro ⟨q, p⟩ ⟨hq, -⟩
    rw [FiberBundle.extChartAt_target, hom_trivializationAt_baseSet,
      TangentBundle.trivializationAt_baseSet]
    refine ⟨⟨hK'φ hq, ?_, by simp⟩, mem_univ _⟩
    rw [← extChartAt_source (I := I)]
    exact φ.map_target (hK'φ hq)
  · rintro z ⟨hzs, hzb⟩ hz
    have hzK' : φ z.proj ∈ K' :=
      ⟨ball_subset_closedBall hzb, extChartAt_target_subset_range x (φ.map_source hzs)⟩
    have hzK : z.proj ∈ K := ⟨φ z.proj, hzK', φ.left_inv hzs⟩
    have hzs' : z.proj ∈ (chartAt H z₀.proj).source := by rwa [← extChartAt_source (I := I)]
    have hzΨ : z ∈ Ψ.source := by
      simp only [Ψ, FiberBundle.chartedSpace_chartAt, mfld_simps]
      rw [Trivialization.coe_fst' _ (by simpa using hzs')]
      exact ⟨⟨hzs', by simp⟩, hzs'⟩
    refine ⟨Ψ z, ?_, Ψ.left_inv hzΨ⟩
    rw [extChartAt_apply]
    refine ⟨hzK', mem_closedBall_zero_iff.2 (hC₀ (le_max_right C 0) fun i ↦ ?_)⟩
    -- The coordinates of `z` on the basis are the values of `z.2` on the chart-local frame.
    rw [ContinuousLinearMap.comp_apply, ← chartLocalFrame_eq_symmL]
    calc ‖z.2 (chartLocalFrame (I := I) x i z.proj)‖
        ≤ ‖z.2‖ * ‖chartLocalFrame (I := I) x i z.proj‖ := z.2.le_opNorm _
      _ ≤ 1 * max C 0 :=
        mul_le_mul hz ((hframe _ hzK i).trans (le_max_left C 0)) (norm_nonneg _) zero_le_one
      _ = max C 0 := one_mul _

/-- **The unit codisc bundle of a compact Riemannian manifold is compact.** -/
theorem isCompact_codiscBundle [CompactSpace M] : IsCompact (codiscBundle I M) := by
  choose U hU L hL hUL using exists_isCompact_norm_le (I := I) (M := M)
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U fun x _ ↦ hU x
  refine (t.isCompact_biUnion fun x _ ↦ hL x).of_isClosed_subset isClosed_codiscBundle ?_
  intro z hz
  obtain ⟨x, hx, hzx⟩ := mem_iUnion₂.1 (ht (mem_univ z.proj))
  exact mem_iUnion₂.2 ⟨x, hx, hUL x z hzx hz⟩

/-- The unit cosphere bundle of a compact Riemannian manifold is compact. -/
theorem isCompact_cosphereBundle [CompactSpace M] : IsCompact (cosphereBundle I M) :=
  isCompact_codiscBundle.of_isClosed_subset isClosed_cosphereBundle
    cosphereBundle_subset_codiscBundle

instance [CompactSpace M] : CompactSpace (cosphereBundle I M) :=
  isCompact_iff_compactSpace.1 isCompact_cosphereBundle

end Topology

section Manifold

variable [IsManifold I ∞ M] [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The norm of covectors is smooth at the points of the unit cosphere bundle. -/
theorem contMDiffAt_norm_snd_of_mem_cosphereBundle (z : CotangentBundle I M)
    (hz : z ∈ cosphereBundle I M) :
    ContMDiffAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) ∞ (fun z : CotangentBundle I M ↦ ‖z.2‖) z := by
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  exact contMDiffAt_norm_snd (snd_ne_zero_of_mem_cosphereBundle hz)

variable [I.Boundaryless]

/-- The unit cosphere bundle of a smooth Riemannian manifold without boundary, with the atlas of
the regular level `‖z.2‖ = 1` of the norm of covectors. -/
instance : ChartedSpace (Fin (Module.finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)
    (cosphereBundle I M) :=
  scalarRegularLevelChartedSpace
    (fun z hz ↦ (contMDiffAt_norm_snd_of_mem_cosphereBundle z hz).of_le ENat.LEInfty.out)
    (isRegularValue_norm_snd one_ne_zero)

/-- **The unit cosphere bundle is a smooth manifold**, of dimension `dim T*M - 1`. -/
instance instIsManifoldCosphereBundle :
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) ∞ (cosphereBundle I M) :=
  isManifold_scalarRegularLevel ENat.LEInfty.out contMDiffAt_norm_snd_of_mem_cosphereBundle
    (isRegularValue_norm_snd one_ne_zero)

/-- **The unit cosphere bundle is a smoothly embedded hypersurface** of the cotangent bundle. -/
theorem isSmoothEmbedding_coe_cosphereBundle :
    IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (Subtype.val : cosphereBundle I M → CotangentBundle I M) :=
  isSmoothEmbedding_coe_scalarRegularLevel ENat.LEInfty.out
    contMDiffAt_norm_snd_of_mem_cosphereBundle
    (isRegularValue_norm_snd one_ne_zero)

/-- The tangent space of the unit cosphere bundle at a covector is the kernel of the
differential of the norm of covectors there. -/
theorem range_mfderiv_coe_cosphereBundle (z : cosphereBundle I M) :
    (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
        (Subtype.val : cosphereBundle I M → CotangentBundle I M) z).range =
      (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) (fun z : CotangentBundle I M ↦ ‖z.2‖) z).ker :=
  range_mfderiv_coe_scalarRegularLevel _ _ z

end Manifold

end CotangentBundle

end TauCeti
