/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedRange
public import TauCeti.Topology.Algebra.Module.LinearPMap.Basic

/-!
# The Hodge decomposition of a Hilbert complex

Let `d₀ : E →ₗ.[𝕜] F` and `d₁ : F →ₗ.[𝕜] G` be densely defined partial linear maps between
Hilbert spaces, with `d₁` closed and `range d₀ ≤ ker d₁`. This is one segment of a Hilbert complex,
in the sense of Brüning and Lesch; the model is the `L²` de Rham complex, where `d₀` and `d₁` are
the weak exterior derivative in two consecutive degrees. The **harmonic space**
`LinearPMap.harmonicSpace d₀ d₁ = ker d₁ ⊓ ker d₀†` consists of the vectors that are closed for the
complex and coclosed for its adjoint. This file proves the **Hodge decomposition**

`F = closure (range d₀) ⊕ harmonicSpace d₀ d₁ ⊕ closure (range d₁†)`,

an orthogonal decomposition. The characterization of closed ranges by a **Poincaré inequality**,
`LinearPMap.isClosed_range_iff_exists_norm_le_mul_norm`, holds for any closed operator and is in
`TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedRange`.

The pair has the **compactness property** with weight `ε : F →L[𝕜] F`,
`LinearPMap.CompactProperty d₀ d₁ ε`, when the vectors `u` of `dom d₁` with `ε u ∈ dom d₀†` and
`u`, `d₁ u` and `d₀† (ε u)` of norm at most one form a relatively compact subset of `F`. For
`ε = id`, this says that `dom d₁ ∩ dom d₀†`, with its graph norm, embeds compactly into `F`. For a
complex with this property at `ε = id`, the ranges of `d₁` and `d₀†` are closed, with Poincaré
inequalities for `d₀†` and `d₁`, and so is the range of `d₀` when `d₀` is closed; the harmonic
space is finite dimensional. On a bounded Lipschitz domain, the
compactness property of the `L²` de Rham complex is the content of Picard's compactness theorem.
These are the consequences of the compactness property in Arnold, Falk and Winther (2010),
§3.1.3.

For bounded operators with closed range, the decomposition of the kernel is
`ContinuousLinearMap.range_sup_ker_inf_ker_adjoint`. Here the operators are unbounded, as the
exterior derivative is on `L²` forms, so the decomposition uses the closures of the ranges, and
needs no closed range assumption. It rests on the descriptions of closures of ranges as
orthogonal complements of kernels, `LinearPMap.topologicalClosure_range_eq_orthogonal_ker_adjoint`
and `LinearPMap.topologicalClosure_range_adjoint_eq_orthogonal_ker`, in
`TauCeti.Analysis.InnerProductSpace.LinearPMap.SelfAdjoint`.

## Main results

* `LinearPMap.harmonicSpace_eq_orthogonal_sup`: the harmonic space is the orthogonal complement of
  `closure (range d₀) ⊔ closure (range d₁†)`.
* `LinearPMap.topologicalClosure_range_sup_harmonicSpace`: for a complex, the kernel of `d₁` is
  `closure (range d₀) ⊔ harmonicSpace d₀ d₁`, the weak Hodge decomposition of the closed vectors.
* `LinearPMap.topologicalClosure_range_sup_harmonicSpace_sup_topologicalClosure_range_adjoint`:
  the three summands of the Hodge decomposition span `F`; the three orthogonality relations are
  `LinearPMap.isOrtho_topologicalClosure_range_harmonicSpace`,
  `LinearPMap.isOrtho_harmonicSpace_topologicalClosure_range_adjoint` and
  `LinearPMap.isOrtho_topologicalClosure_range_topologicalClosure_range_adjoint`.
* `LinearPMap.compactProperty_iff_tendsto_subseq`: the compactness property in terms of
  sequences, which have convergent subsequences when bounded in the graph norm.
* `LinearPMap.CompactProperty.isClosed_range_left` and
  `LinearPMap.CompactProperty.isClosed_range_right`: the compactness property at `ε = id` closes
  the ranges of `d₀` and `d₁`.
* `LinearPMap.CompactProperty.finiteDimensional_harmonicSpace`: the compactness property at
  `ε = id` makes the harmonic space finite dimensional.

## References

* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus: from Hodge theory to
  numerical stability*, Bull. Amer. Math. Soc. 47 (2010), §3.1.
* D. N. Arnold, R. S. Falk, R. Winther, *Finite element exterior calculus, homological techniques,
  and applications*, Acta Numerica 15 (2006), §3.
* J. Brüning, M. Lesch, *Hilbert complexes*, J. Funct. Anal. 108 (1992).
-/

public section

noncomputable section

open Filter Topology

namespace LinearPMap

variable {𝕜 E F G : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup G] [InnerProductSpace 𝕜 G]

/-! ### The harmonic space and the Hodge decomposition -/

section Hodge

variable [CompleteSpace E] {d₀ : E →ₗ.[𝕜] F} {d₁ : F →ₗ.[𝕜] G}

variable (d₀ d₁) in
/-- The **harmonic space** `ker d₁ ⊓ ker d₀†` of a pair of composable partial linear maps
`d₀ : E →ₗ.[𝕜] F` and `d₁ : F →ₗ.[𝕜] G`: the vectors of `F` that are closed for `d₁` and coclosed
for the adjoint of `d₀`. -/
def harmonicSpace : Submodule 𝕜 F :=
  d₁.ker ⊓ d₀†.ker

/-- The harmonic space is the intersection of the kernel of `d₁` with the kernel of `d₀†`. -/
theorem harmonicSpace_def : harmonicSpace d₀ d₁ = d₁.ker ⊓ d₀†.ker :=
  (rfl)

@[simp]
theorem mem_harmonicSpace_iff {x : F} : x ∈ harmonicSpace d₀ d₁ ↔ x ∈ d₁.ker ∧ x ∈ d₀†.ker :=
  Submodule.mem_inf

/-- Harmonic vectors are closed: they lie in the kernel of `d₁`. -/
theorem harmonicSpace_le_ker : harmonicSpace d₀ d₁ ≤ d₁.ker :=
  inf_le_left

/-- Harmonic vectors are coclosed: they lie in the kernel of `d₀†`. -/
theorem harmonicSpace_le_ker_adjoint : harmonicSpace d₀ d₁ ≤ d₀†.ker :=
  inf_le_right

/-- The harmonic space is closed when `d₁` is closed and `d₀` is densely defined. -/
theorem isClosed_harmonicSpace (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed) :
    _root_.IsClosed (harmonicSpace d₀ d₁ : Set F) :=
  hc₁.isClosed_ker.inter (adjoint_isClosed hd₀).isClosed_ker

/-- The harmonic space consists of the vectors of `ker d₁` orthogonal to the range of `d₀`. -/
theorem harmonicSpace_eq_ker_inf_orthogonal_range (hd₀ : Dense (d₀.domain : Set E)) :
    harmonicSpace d₀ d₁ = d₁.ker ⊓ (LinearMap.range d₀.toFun)ᗮ := by
  rw [harmonicSpace_def, orthogonal_range_eq_ker_adjoint hd₀]

/-- **Harmonic vectors are orthogonal to exact and coexact ones.** For `d₀` densely defined and
`d₁` closed and densely defined, the harmonic space is the orthogonal complement of
`closure (range d₀) ⊔ closure (range d₁†)`. -/
theorem harmonicSpace_eq_orthogonal_sup [CompleteSpace F] [CompleteSpace G]
    (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed) (hd₁ : Dense (d₁.domain : Set F)) :
    harmonicSpace d₀ d₁ = ((LinearMap.range d₀.toFun).topologicalClosure ⊔
      (LinearMap.range d₁†.toFun).topologicalClosure)ᗮ := by
  rw [← Submodule.inf_orthogonal, topologicalClosure_range_eq_orthogonal_ker_adjoint hd₀,
    topologicalClosure_range_adjoint_eq_orthogonal_ker hc₁ hd₁,
    Submodule.orthogonal_orthogonal_eq_closure, Submodule.orthogonal_orthogonal_eq_closure,
    (adjoint_isClosed hd₀).isClosed_ker.submodule_topologicalClosure_eq,
    hc₁.isClosed_ker.submodule_topologicalClosure_eq, harmonicSpace_def, inf_comm]

omit [CompleteSpace E] in
/-- In a complex `range d₀ ≤ ker d₁` with `d₁` closed, the closure of the range of `d₀` is still
contained in the kernel of `d₁`. -/
theorem topologicalClosure_range_le_ker (hc₁ : d₁.IsClosed)
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ≤ d₁.ker :=
  Submodule.topologicalClosure_minimal _ hcomplex hc₁.isClosed_ker

/-- The closure of the range of `d₀` is orthogonal to the harmonic space. -/
theorem isOrtho_topologicalClosure_range_harmonicSpace (hd₀ : Dense (d₀.domain : Set E)) :
    (LinearMap.range d₀.toFun).topologicalClosure ⟂ harmonicSpace d₀ d₁ := by
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le, Submodule.orthogonal_closure,
    orthogonal_range_eq_ker_adjoint hd₀]
  exact harmonicSpace_le_ker_adjoint

/-- The harmonic space is orthogonal to the closure of the range of `d₁†`. -/
theorem isOrtho_harmonicSpace_topologicalClosure_range_adjoint [CompleteSpace F]
    (hd₁ : Dense (d₁.domain : Set F)) :
    harmonicSpace d₀ d₁ ⟂ (LinearMap.range d₁†.toFun).topologicalClosure := by
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le]
  exact (Submodule.topologicalClosure_minimal _
    (adjoint_isFormalAdjoint hd₁).range_le_orthogonal_ker (Submodule.isClosed_orthogonal _)).trans
    (Submodule.orthogonal_le harmonicSpace_le_ker)

omit [CompleteSpace E] in
/-- In a complex, the closures of the ranges of `d₀` and of `d₁†` are orthogonal. -/
theorem isOrtho_topologicalClosure_range_topologicalClosure_range_adjoint [CompleteSpace F]
    (hd₁ : Dense (d₁.domain : Set F)) (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ⟂
      (LinearMap.range d₁†.toFun).topologicalClosure := by
  rw [Submodule.isOrtho_comm, Submodule.isOrtho_iff_le, Submodule.orthogonal_closure]
  exact (Submodule.topologicalClosure_minimal _
    (adjoint_isFormalAdjoint hd₁).range_le_orthogonal_ker (Submodule.isClosed_orthogonal _)).trans
    (Submodule.orthogonal_le hcomplex)

/-- **The Hodge decomposition of the closed vectors.** In a complex `range d₀ ≤ ker d₁`, with `d₀`
densely defined and `d₁` closed, the kernel of `d₁` is the sum of the closure of the range of
`d₀` and the harmonic space. -/
theorem topologicalClosure_range_sup_harmonicSpace [CompleteSpace F]
    (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed)
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ⊔ harmonicSpace d₀ d₁ = d₁.ker := by
  have : (LinearMap.range d₀.toFun).topologicalClosure.HasOrthogonalProjection :=
    have := (Submodule.isClosed_topologicalClosure (LinearMap.range d₀.toFun)).completeSpace_coe
    inferInstance
  rw [harmonicSpace_eq_ker_inf_orthogonal_range hd₀, ← Submodule.orthogonal_closure, inf_comm]
  exact Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection
    (topologicalClosure_range_le_ker hc₁ hcomplex)

/-- **The Hodge decomposition.** In a complex `range d₀ ≤ ker d₁`, with `d₀` densely defined and
`d₁` closed and densely defined, `F` is the sum of the closure of the range of `d₀`, the harmonic
space and the closure of the range of `d₁†`. The three summands are pairwise orthogonal
(`isOrtho_topologicalClosure_range_harmonicSpace`,
`isOrtho_harmonicSpace_topologicalClosure_range_adjoint` and
`isOrtho_topologicalClosure_range_topologicalClosure_range_adjoint`). -/
theorem topologicalClosure_range_sup_harmonicSpace_sup_topologicalClosure_range_adjoint
    [CompleteSpace F] [CompleteSpace G] (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed)
    (hd₁ : Dense (d₁.domain : Set F)) (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    (LinearMap.range d₀.toFun).topologicalClosure ⊔ harmonicSpace d₀ d₁ ⊔
      (LinearMap.range d₁†.toFun).topologicalClosure = ⊤ := by
  have : d₁.ker.HasOrthogonalProjection :=
    have := hc₁.isClosed_ker.completeSpace_coe
    inferInstance
  rw [topologicalClosure_range_sup_harmonicSpace hd₀ hc₁ hcomplex,
    topologicalClosure_range_adjoint_eq_orthogonal_ker hc₁ hd₁]
  exact Submodule.sup_orthogonal_of_hasOrthogonalProjection

end Hodge

/-! ### The compactness property -/

section Compact

variable [CompleteSpace E] {d₀ : E →ₗ.[𝕜] F} {d₁ : F →ₗ.[𝕜] G} {ε : F →L[𝕜] F}

variable (d₀ d₁ ε) in
/-- The **compactness property** with weight `ε : F →L[𝕜] F` of a pair of composable partial
linear maps `d₀ : E →ₗ.[𝕜] F` and `d₁ : F →ₗ.[𝕜] G`: the vectors `u` of `dom d₁` with
`ε u ∈ dom d₀†`, `‖u‖ ≤ 1`, `‖d₁ u‖ ≤ 1` and `‖d₀† (ε u)‖ ≤ 1` form a relatively compact subset
of `F`. For `ε = id`, this says that `dom d₁ ∩ dom d₀†` with its graph norm embeds compactly
into `F`; a general `ε` is the weight of a weighted `L²` inner product `⟪ε ·, ·⟫`. -/
def CompactProperty : Prop :=
  IsCompact (_root_.closure {u : F | ∃ (h₁ : u ∈ d₁.domain) (h₀ : ε u ∈ d₀†.domain),
    ‖u‖ ≤ 1 ∧ ‖d₁ ⟨u, h₁⟩‖ ≤ 1 ∧ ‖d₀† ⟨ε u, h₀⟩‖ ≤ 1})

variable (d₀ d₁ ε) in
/-- The compactness property is the relative compactness of the vectors `u` of `dom d₁` with
`ε u ∈ dom d₀†`, `‖u‖ ≤ 1`, `‖d₁ u‖ ≤ 1` and `‖d₀† (ε u)‖ ≤ 1`. -/
theorem compactProperty_def : CompactProperty d₀ d₁ ε ↔
    IsCompact (_root_.closure {u : F | ∃ (h₁ : u ∈ d₁.domain) (h₀ : ε u ∈ d₀†.domain),
      ‖u‖ ≤ 1 ∧ ‖d₁ ⟨u, h₁⟩‖ ≤ 1 ∧ ‖d₀† ⟨ε u, h₀⟩‖ ≤ 1}) :=
  Iff.rfl

variable (d₀ d₁ ε) in
/-- **The compactness property in terms of sequences.** The pair `d₀`, `d₁` has the compactness
property with weight `ε` if and only if every sequence `u` in `dom d₁` with `ε u ∈ dom d₀†` and
`‖u i‖ ≤ 1`, `‖d₁ (u i)‖ ≤ 1` and `‖d₀† (ε (u i))‖ ≤ 1` has a convergent subsequence. -/
theorem compactProperty_iff_tendsto_subseq : CompactProperty d₀ d₁ ε ↔
    ∀ (u : ℕ → F) (hu : ∀ i, u i ∈ d₁.domain) (hε : ∀ i, ε (u i) ∈ d₀†.domain),
      (∀ i, ‖u i‖ ≤ 1 ∧ ‖d₁ ⟨u i, hu i⟩‖ ≤ 1 ∧ ‖d₀† ⟨ε (u i), hε i⟩‖ ≤ 1) →
        ∃ a, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) := by
  refine ⟨fun h u hu hε hb ↦ ?_, fun H ↦ IsSeqCompact.isCompact fun x hx ↦ ?_⟩
  · obtain ⟨a, -, φ, hφ, hlim⟩ := h.tendsto_subseq fun i ↦ subset_closure ⟨hu i, hε i, hb i⟩
    exact ⟨a, φ, hφ, hlim⟩
  -- Approximate a sequence of the closure by one of the set, within `1 / (n + 1)`.
  have hy : ∀ n : ℕ, ∃ y, (∃ (h₁ : y ∈ d₁.domain) (h₀ : ε y ∈ d₀†.domain),
      ‖y‖ ≤ 1 ∧ ‖d₁ ⟨y, h₁⟩‖ ≤ 1 ∧ ‖d₀† ⟨ε y, h₀⟩‖ ≤ 1) ∧ dist (x n) y < 1 / (n + 1) :=
    fun n ↦ Metric.mem_closure_iff.1 (hx n) _ Nat.one_div_pos_of_nat
  choose y hy hdist using hy
  choose h₁ h₀ hb using hy
  obtain ⟨a, φ, hφ, hlim⟩ := H y h₁ h₀ hb
  have hxlim : Tendsto (x ∘ φ) atTop (𝓝 a) := hlim.congr_dist <|
    (squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ (dist_comm _ _).le.trans (hdist n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat).comp hφ.tendsto_atTop
  exact ⟨a, isClosed_closure.mem_of_tendsto hxlim (Eventually.of_forall fun n ↦ hx (φ n)), φ, hφ,
    hxlim⟩

variable (d₀ d₁) in
/-- **The compactness property at `ε = id`** is the relative compactness of the vectors `u` of
`dom d₁ ∩ dom d₀†` with `‖u‖ ≤ 1`, `‖d₁ u‖ ≤ 1` and `‖d₀† u‖ ≤ 1`. -/
theorem compactProperty_id_iff : CompactProperty d₀ d₁ (ContinuousLinearMap.id 𝕜 F) ↔
    IsCompact (_root_.closure {u : F | ∃ (h₁ : u ∈ d₁.domain) (h₀ : u ∈ d₀†.domain),
      ‖u‖ ≤ 1 ∧ ‖d₁ ⟨u, h₁⟩‖ ≤ 1 ∧ ‖d₀† ⟨u, h₀⟩‖ ≤ 1}) :=
  -- `ContinuousLinearMap.id 𝕜 F u` is `u` by definition, so both sets are the same.
  Iff.rfl

variable (d₀ d₁ ε) in
/-- In finite dimension every pair of partial linear maps has the compactness property, for
every weight. -/
theorem compactProperty_of_finiteDimensional [FiniteDimensional 𝕜 F] :
    CompactProperty d₀ d₁ ε := by
  have := FiniteDimensional.proper_rclike 𝕜 F
  refine ((Metric.isBounded_closedBall (x := (0 : F)) (r := 1)).subset ?_).isCompact_closure
  rintro u ⟨-, -, hu, -⟩
  exact mem_closedBall_zero_iff.2 hu

/-- A vector in the kernel of a partial linear map lies in its domain, with value of norm at most
one. -/
private theorem exists_norm_apply_le_one_of_mem_ker {H : Type*} [NormedAddCommGroup H]
    [NormedSpace 𝕜 H] {f : F →ₗ.[𝕜] H} {u : F} (hu : u ∈ f.ker) :
    ∃ h : u ∈ f.domain, ‖f ⟨u, h⟩‖ ≤ 1 :=
  ⟨f.ker_le_domain hu, by
    rw [(coe_mem_ker_iff (x := ⟨u, f.ker_le_domain hu⟩)).1 hu, norm_zero]
    exact zero_le_one⟩

/-- **The Poincaré inequality for `d₁`.** In a complex `range d₀ ≤ ker d₁` with the compactness
property at `ε = id`, `d₀` densely defined and `d₁` closed, for some `c > 0`, `‖u‖ ≤ c ‖d₁ u‖`
for every `u` in the domain of `d₁` orthogonal to its kernel. -/
theorem CompactProperty.exists_norm_le_mul_norm_right
    (h : CompactProperty d₀ d₁ (ContinuousLinearMap.id 𝕜 F)) (hd₀ : Dense (d₀.domain : Set E))
    (hc₁ : d₁.IsClosed) (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    ∃ c > 0, ∀ u : d₁.domain, (u : F) ∈ d₁.kerᗮ → ‖(u : F)‖ ≤ c * ‖d₁ u‖ := by
  refine exists_norm_le_mul_norm_of_isCompact_closure hc₁ ((compactProperty_id_iff d₀ d₁).1 h)
    fun u hu hu1 hdu ↦ ?_
  -- A vector orthogonal to `ker d₁` is orthogonal to `range d₀`, so `d₀†` kills it.
  have hker : (u : F) ∈ d₀†.ker := by
    rw [← orthogonal_range_eq_ker_adjoint hd₀]
    exact Submodule.orthogonal_le hcomplex hu
  obtain ⟨h₀, hz⟩ := exists_norm_apply_le_one_of_mem_ker hker
  exact ⟨u.property, h₀, hu1, hdu, hz⟩

/-- **The Poincaré inequality for `d₀†`.** In a complex `range d₀ ≤ ker d₁` with the compactness
property at `ε = id`, `d₀` densely defined and `d₁` closed, for some `c > 0`, `‖u‖ ≤ c ‖d₀† u‖`
for every `u` in the domain of `d₀†` orthogonal to its kernel. -/
theorem CompactProperty.exists_norm_le_mul_norm_adjoint_left [CompleteSpace F]
    (h : CompactProperty d₀ d₁ (ContinuousLinearMap.id 𝕜 F)) (hd₀ : Dense (d₀.domain : Set E))
    (hc₁ : d₁.IsClosed) (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    ∃ c > 0, ∀ u : d₀†.domain, (u : F) ∈ d₀†.kerᗮ → ‖(u : F)‖ ≤ c * ‖d₀† u‖ := by
  refine exists_norm_le_mul_norm_of_isCompact_closure (adjoint_isClosed hd₀)
    ((compactProperty_id_iff d₀ d₁).1 h) fun u hu hu1 hdu ↦ ?_
  -- A vector orthogonal to `ker d₀†` lies in the closure of `range d₀`, so `d₁` kills it.
  have hker : (u : F) ∈ d₁.ker := by
    rw [← topologicalClosure_range_eq_orthogonal_ker_adjoint hd₀] at hu
    exact topologicalClosure_range_le_ker hc₁ hcomplex hu
  obtain ⟨h₁, hz⟩ := exists_norm_apply_le_one_of_mem_ker hker
  exact ⟨h₁, u.property, hu1, hz, hdu⟩

/-- **The range of `d₁` is closed.** In a complex `range d₀ ≤ ker d₁` with the compactness
property at `ε = id`, `d₀` densely defined and `d₁` closed, the range of `d₁` is closed. -/
theorem CompactProperty.isClosed_range_right [CompleteSpace F]
    (h : CompactProperty d₀ d₁ (ContinuousLinearMap.id 𝕜 F))
    (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed)
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    _root_.IsClosed (LinearMap.range d₁.toFun : Set G) :=
  have ⟨_, _, hc⟩ := h.exists_norm_le_mul_norm_right hd₀ hc₁ hcomplex
  isClosed_range_of_norm_le_mul_norm hc₁ hc

/-- **The range of `d₀†` is closed.** In a complex `range d₀ ≤ ker d₁` with the compactness
property at `ε = id`, `d₀` densely defined and `d₁` closed, the range of `d₀†` is closed. -/
theorem CompactProperty.isClosed_range_adjoint_left [CompleteSpace F]
    (h : CompactProperty d₀ d₁ (ContinuousLinearMap.id 𝕜 F)) (hd₀ : Dense (d₀.domain : Set E))
    (hc₁ : d₁.IsClosed) (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    _root_.IsClosed (LinearMap.range d₀†.toFun : Set E) :=
  have ⟨_, _, hc⟩ := h.exists_norm_le_mul_norm_adjoint_left hd₀ hc₁ hcomplex
  isClosed_range_of_norm_le_mul_norm (adjoint_isClosed hd₀) hc

/-- **The range of `d₀` is closed.** In a complex `range d₀ ≤ ker d₁` with the compactness
property at `ε = id`, `d₀` closed and densely defined and `d₁` closed, the range of `d₀` is
closed. -/
theorem CompactProperty.isClosed_range_left [CompleteSpace F]
    (h : CompactProperty d₀ d₁ (ContinuousLinearMap.id 𝕜 F))
    (hc₀ : d₀.IsClosed) (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed)
    (hcomplex : LinearMap.range d₀.toFun ≤ d₁.ker) :
    _root_.IsClosed (LinearMap.range d₀.toFun : Set F) :=
  isClosed_range_of_isClosed_range_adjoint hc₀ hd₀
    (h.isClosed_range_adjoint_left hd₀ hc₁ hcomplex)

/-- **The harmonic space is finite dimensional.** If `d₀` and `d₁` have the compactness property
at `ε = id`, with `d₀` densely defined and `d₁` closed, the harmonic space `ker d₁ ⊓ ker d₀†` is
finite dimensional. -/
theorem CompactProperty.finiteDimensional_harmonicSpace
    (h : CompactProperty d₀ d₁ (ContinuousLinearMap.id 𝕜 F))
    (hd₀ : Dense (d₀.domain : Set E)) (hc₁ : d₁.IsClosed) :
    FiniteDimensional 𝕜 (harmonicSpace d₀ d₁) := by
  have hemb := (isClosed_harmonicSpace hd₀ hc₁).isClosedEmbedding_subtypeVal
  refine FiniteDimensional.of_isCompact_closedBall₀ 𝕜 one_pos <|
    (hemb.isCompact_preimage ((compactProperty_id_iff d₀ d₁).1 h)).of_isClosed_subset
      Metric.isClosed_closedBall fun x hx ↦ subset_closure ?_
  -- The unit ball of the harmonic space lies in the set of the compactness property, since
  -- `d₁` and `d₀†` vanish on harmonic vectors.
  obtain ⟨hk₁, hk₀⟩ := mem_harmonicSpace_iff.1 x.property
  obtain ⟨h₁, hz₁⟩ := exists_norm_apply_le_one_of_mem_ker hk₁
  obtain ⟨h₀, hz₀⟩ := exists_norm_apply_le_one_of_mem_ker hk₀
  exact ⟨h₁, h₀, mem_closedBall_zero_iff.1 hx, hz₁, hz₀⟩

end Compact

end LinearPMap
