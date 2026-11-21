/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize
public import TauCeti.Geometry.Manifold.RegularValue.Level
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Cotangent
import TauCeti.Geometry.Manifold.Riemannian.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

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
(`TauCeti.CotangentBundle.isCompact_codiscBundle`) by `IsCompact.norm_le_bundle_of_continuous`:
near each point the bundle coordinates of a covector are bounded by a multiple of its norm, since
the inverse tangent trivialization is locally bounded.

Since every nonzero value is a regular value of the norm of covectors
(`TauCeti.CotangentBundle.isRegularValue_norm_snd`), `S*M` is a regular level. For a smooth metric
on a boundaryless manifold, it carries the atlas `TauCeti.regularLevelChartedSpace` of
regular levels, for which it is a smooth manifold of dimension `dim T*M - 1`
(`TauCeti.CotangentBundle.instIsManifoldCosphereBundle`) and a smoothly embedded hypersurface of
`T*M` (`TauCeti.CotangentBundle.isSmoothEmbedding_coe_cosphereBundle`) whose tangent spaces are
the kernels of the differential of the norm
(`TauCeti.CotangentBundle.range_mfderiv_coe_cosphereBundle`).

Dividing a nonzero covector by its norm (`TauCeti.CotangentBundle.normalize`) lands in `S*M`, and
normalizing a smooth family of nonzero covectors gives a smooth map into `S*M`
(`TauCeti.CotangentBundle.contMDiff_normalize_cosphereBundle`).

## Main definitions

* `TauCeti.CotangentBundle.codiscBundle`: the unit codisc bundle `D*M`.
* `TauCeti.CotangentBundle.cosphereBundle`: the unit cosphere bundle `S*M`.
* `TauCeti.CotangentBundle.normalize`: the covector of norm one on the ray of a covector.

## Main results

* `TauCeti.CotangentBundle.isClosed_codiscBundle` and
  `TauCeti.CotangentBundle.isCompact_codiscBundle`: `D*M` is closed, and compact over a compact
  manifold; similarly for `S*M`.
* `TauCeti.CotangentBundle.instIsManifoldCosphereBundle`: `S*M` is a smooth manifold.
* `TauCeti.CotangentBundle.isSmoothEmbedding_coe_cosphereBundle`: its inclusion into `T*M` is a
  smooth embedding.
* `TauCeti.CotangentBundle.contMDiff_normalize_cosphereBundle`: normalizing a smooth family of
  nonzero covectors is smooth into `S*M`.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 and Chapter 12.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.2.
-/

public section

noncomputable section

open Bundle Set Filter Riemannian.Tensor
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
  {z | ‖z.snd‖ ≤ 1}

variable (I M) in
/-- The **unit cosphere bundle** `S*M` of a Riemannian manifold: the covectors of norm one. Its
body is exposed because the manifold structure on `S*M` is that of the regular level
`{z // ‖z.2‖ = 1}`, read through this definition. -/
@[expose] def cosphereBundle : Set (CotangentBundle I M) :=
  {z | ‖z.snd‖ = 1}

@[simp]
theorem mem_codiscBundle {z : CotangentBundle I M} : z ∈ codiscBundle I M ↔ ‖z.snd‖ ≤ 1 :=
  Iff.rfl

@[simp]
theorem mem_cosphereBundle {z : CotangentBundle I M} : z ∈ cosphereBundle I M ↔ ‖z.snd‖ = 1 :=
  Iff.rfl

theorem cosphereBundle_subset_codiscBundle : cosphereBundle I M ⊆ codiscBundle I M :=
  fun _ hz ↦ hz.le

/-- A covector of the unit cosphere bundle is not zero. -/
theorem snd_ne_zero_of_mem_cosphereBundle {z : CotangentBundle I M}
    (hz : z ∈ cosphereBundle I M) : z.snd ≠ 0 := fun h ↦ by
  rw [mem_cosphereBundle, h, (ContinuousLinearMap.opNorm_zero_iff _).2 rfl] at hz
  exact zero_ne_one hz

/-! ### Normalization of covectors -/

/-- The covector of norm one on the ray of a covector `q`, over the same base point
(`NormedSpace.normalize` on fibres). -/
def normalize (q : CotangentBundle I M) : CotangentBundle I M :=
  TotalSpace.mk' (E →L[ℝ] ℝ) q.proj (NormedSpace.normalize q.snd)

@[simp]
theorem proj_normalize (q : CotangentBundle I M) : (normalize q).proj = q.proj :=
  (rfl)

@[simp]
theorem snd_normalize (q : CotangentBundle I M) : (normalize q).snd = NormedSpace.normalize q.snd :=
  (rfl)

/-- Normalization divides a covector by its norm (the definition of `NormedSpace.normalize`). -/
theorem normalize_eq_mk_smul (q : CotangentBundle I M) :
    normalize q = TotalSpace.mk' (E →L[ℝ] ℝ) q.proj (‖q.snd‖⁻¹ • q.snd) := by
  rw [normalize, NormedSpace.normalize]

/-- The normalization of a covector other than zero has norm one. -/
theorem norm_snd_normalize {q : CotangentBundle I M} (hq : q.snd ≠ 0) : ‖(normalize q).snd‖ = 1 :=
  NormedSpace.norm_normalize (V := TangentSpace I q.proj →L[ℝ] ℝ) hq

/-- The normalization of a covector other than zero lies in the unit cosphere bundle. -/
theorem normalize_mem_cosphereBundle {q : CotangentBundle I M} (hq : q.snd ≠ 0) :
    normalize q ∈ cosphereBundle I M :=
  norm_snd_normalize hq

/-- Normalization only depends on the ray of a covector. -/
theorem normalize_mk_smul_of_pos (q : CotangentBundle I M) {c : ℝ} (hc : 0 < c) :
    normalize (TotalSpace.mk' (E →L[ℝ] ℝ) q.proj (c • q.snd)) = normalize q := by
  simp only [normalize, NormedSpace.normalize_smul_of_pos hc]

/-- A covector of norm one is its own normalization. -/
theorem normalize_eq_self_of_norm_eq_one {q : CotangentBundle I M} (hq : ‖q.snd‖ = 1) :
    normalize q = q := by
  rw [normalize, NormedSpace.normalize_eq_self_of_norm_eq_one hq]

variable [FiniteDimensional ℝ E]

section Topology

variable [IsManifold I 1 M] [IsContMDiffRiemannianBundle I 0 E (fun x : M ↦ TangentSpace I x)]

theorem isClosed_codiscBundle : IsClosed (codiscBundle I M) :=
  isClosed_le continuous_norm_snd continuous_const

theorem isClosed_cosphereBundle : IsClosed (cosphereBundle I M) :=
  isClosed_eq continuous_norm_snd continuous_const

/-- **The unit codisc bundle of a compact Riemannian manifold is compact.** -/
theorem isCompact_codiscBundle [CompactSpace M] : IsCompact (codiscBundle I M) := by
  have := IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := I) (n := 0) (F := E)
    (V := fun x : M ↦ TangentSpace I x)
  convert (isCompact_univ (X := M)).norm_le_bundle_of_continuous (F := E →L[ℝ] ℝ)
    (E := fun x : M ↦ TangentSpace I x →L[ℝ] ℝ) continuous_norm_snd (fun x ↦ ?_) 1 using 1
  · ext; simp
  -- In bundle coordinates, a covector is composed with the inverse tangent trivialization, which
  -- is locally bounded.
  set e := trivializationAt E (TangentSpace I) x
  obtain ⟨C, -, hC⟩ := eventually_norm_symmL_trivializationAt_lt E (fun x : M ↦ TangentSpace I x) x
  refine ⟨C, ?_⟩
  filter_upwards [hC, e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' x)]
    with y hy hyb p
  rw [Trivialization.continuousLinearMapAt_apply_of_mem (R := ℝ) _ (by simpa [e] using hyb),
    mul_comm]
  simp only [hom_trivializationAt, Trivialization.continuousLinearMap_apply,
    Trivial.fiberBundle_trivializationAt', Trivial.continuousLinearMapAt_trivialization,
    ContinuousLinearMap.id_comp]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (mul_le_mul_of_nonneg_left hy.le (norm_nonneg _))

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
    ContMDiffAt (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) ∞ (fun z : CotangentBundle I M ↦ ‖z.snd‖) z := by
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  exact contMDiffAt_norm_snd (snd_ne_zero_of_mem_cosphereBundle hz)

variable [I.Boundaryless]

/-- The unit cosphere bundle of a smooth Riemannian manifold without boundary, with the atlas of
the regular level `‖z.2‖ = 1` of the norm of covectors. -/
instance : ChartedSpace (Fin (Module.finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)
    (cosphereBundle I M) :=
  regularLevelChartedSpace
    (fun z hz ↦ (contMDiffAt_norm_snd_of_mem_cosphereBundle z hz).of_le ENat.LEInfty.out)
    (isRegularValue_norm_snd one_ne_zero) (by rw [Module.finrank_self])

/-- **The unit cosphere bundle is a smooth manifold**, of dimension `dim T*M - 1`. -/
instance instIsManifoldCosphereBundle :
    IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) ∞ (cosphereBundle I M) :=
  isManifold_regularLevel ENat.LEInfty.out contMDiffAt_norm_snd_of_mem_cosphereBundle
    (isRegularValue_norm_snd one_ne_zero) (by rw [Module.finrank_self])

/-- **The unit cosphere bundle is a smoothly embedded hypersurface** of the cotangent bundle. -/
theorem isSmoothEmbedding_coe_cosphereBundle :
    IsSmoothEmbedding 𝓘(ℝ, Fin (Module.finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ)
      (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ (Subtype.val : cosphereBundle I M → CotangentBundle I M) :=
  isSmoothEmbedding_coe_regularLevel ENat.LEInfty.out
    contMDiffAt_norm_snd_of_mem_cosphereBundle
    (isRegularValue_norm_snd one_ne_zero) (by rw [Module.finrank_self])

/-- The tangent space of the unit cosphere bundle at a covector is the kernel of the
differential of the norm of covectors there. -/
theorem range_mfderiv_coe_cosphereBundle (z : cosphereBundle I M) :
    (mfderiv 𝓘(ℝ, Fin (Module.finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) (I.prod 𝓘(ℝ, E →L[ℝ] ℝ))
        (Subtype.val : cosphereBundle I M → CotangentBundle I M) z).range =
      (mfderiv (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) 𝓘(ℝ) (fun z : CotangentBundle I M ↦ ‖z.snd‖) z).ker :=
  range_mfderiv_coe_regularLevel _ _ (by rw [Module.finrank_self]) z

/-- **Normalizing a smooth family of nonzero covectors is smooth into the unit cosphere
bundle.** -/
theorem contMDiff_normalize_cosphereBundle {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {N : Type*} [TopologicalSpace N] [ChartedSpace G N] {f : N → CotangentBundle I M}
    (hf : ContMDiff J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ f) (hf0 : ∀ y, (f y).snd ≠ 0) :
    ContMDiff J 𝓘(ℝ, Fin (Module.finrank ℝ (E × (E →L[ℝ] ℝ)) - 1) → ℝ) ∞
      (fun y ↦ (⟨normalize (f y), normalize_mem_cosphereBundle (hf0 y)⟩ : cosphereBundle I M)) := by
  have : IsManifold I (∞ + 1) M := IsManifold.of_le (n := ∞) (by simp)
  -- The inverse norm of the family is smooth, since the norm is smooth away from zero.
  have hc : ContMDiff J 𝓘(ℝ) ∞ fun y ↦ ‖(f y).snd‖⁻¹ := fun y ↦
    ((contMDiffAt_norm_snd (n := ∞) (hf0 y)).comp y (hf y)).inv₀
      ((norm_ne_zero_iff (a := (f y).snd)).2 (hf0 y))
  -- Read in the cotangent bundle, the normalized family is `y ↦ ‖(f y).snd‖⁻¹ • f y`.
  have hval : ContMDiff J (I.prod 𝓘(ℝ, E →L[ℝ] ℝ)) ∞ fun y ↦ normalize (f y) := by
    simp only [normalize_eq_mk_smul]
    exact hc.smul_totalSpace hf
  exact (ContMDiff.iff_comp_isImmersion isSmoothEmbedding_coe_cosphereBundle.isImmersion).2
    ⟨hval.continuous.subtype_mk _, hval⟩

end Manifold

end CotangentBundle

end TauCeti
