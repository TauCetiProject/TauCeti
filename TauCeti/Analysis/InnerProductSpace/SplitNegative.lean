/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.Analysis.Normed.Module.Connected
public import TauCeti.Analysis.InnerProductSpace.Indefinite
public import TauCeti.Analysis.Normed.Module.NegativeSubspace
public import TauCeti.LinearAlgebra.Orientation.Basic

/-!
# Negative subspaces of the split form `-‖u‖² + ‖v‖²`

On a product `E × F` of real normed spaces consider the split indefinite form
`Q(u, v) = -‖u‖² + ‖v‖²`. It is the quadratic part of a Morse function in normalized coordinates,
with negative coordinates `u` and positive coordinates `v`. A submodule `W ≤ E × F` is
*split-negative* (`Submodule.IsSplitNegative`) if `Q` is negative on its nonzero vectors, that is
`‖v‖ < ‖u‖` for every nonzero `(u, v) ∈ W`.

Such a `W` meets the positive factor `0 × F` only in `0`, so the projection to `E` is injective on
it and `dim W ≤ dim E` (`Submodule.finrank_le_of_norm_snd_lt`). The graph of a linear map
`T : E → F` is split-negative exactly when `T` strictly decreases the norm of every nonzero vector
(`Submodule.isSplitNegative_graph_iff`); when `E` is finite-dimensional this means `‖T‖ < 1`
(`ContinuousLinearMap.opNorm_lt_one_iff_forall_mem_graph_norm_snd_lt`).

When `E` is a finite-dimensional inner product space, a split-negative subspace is maximal exactly
when its dimension is `dim E` (`Submodule.maximal_isSplitNegative_iff`): a split-negative
subspace of smaller dimension stays split-negative after adding a nonzero vector `(u, 0)` with `u`
orthogonal to its projection. The maximal split-negative subspaces are exactly the graphs of the
continuous linear maps `T : E → F` with `‖T‖ < 1`
(`Submodule.maximal_isSplitNegative_iff_exists_eq_graph`), and `T ↦ graph T` is a bijection from
the open unit ball of `E →L[ℝ] F` onto the set of maximal split-negative subspaces
(`TauCeti.splitNegativeGraphEquiv`). These are the graph coordinates on the space of maximal
negative subspaces of `Q`. Topologized through them (`TauCeti.splitNegativeGraphTopology`), that
space is homeomorphic to the open unit ball (`TauCeti.splitNegativeGraphHomeomorph`), a convex
set, hence contractible (`TauCeti.contractibleSpace_maximal_isSplitNegative`).

In graph coordinates every maximal split-negative subspace `W` is identified with `E` by the
projection to the first factor (`Submodule.splitNegativeFstEquiv`), whose inverse is
`u ↦ (u, T u)`. Through this identification, an orientation of `E` carried to `W` by a linear
isomorphism `e : E ≃ W` agrees with the orientation carried by the graph coordinates exactly when
the first component of `e` has positive determinant
(`Submodule.orientation_map_eq_map_splitNegativeFstEquiv_symm_iff`).

The negative column `u ↦ (A u, B u)` of the derivative of a transition between two Morse charts
pulls `Q` back to `-‖u‖²` (`ContinuousLinearMap.norm_le_norm_fst_of_norm_sq_sub` and its
neighbours). Its range is a maximal split-negative subspace
(`ContinuousLinearMap.maximal_isSplitNegative_range_of_norm_sq_sub`), the graph of `B ∘ A⁻¹`
when `A` is invertible (`LinearMap.range_eq_graph_of_fst_eq_equiv`). So the two charts induce
the same orientation on their common negative subspace, compared through graph coordinates,
exactly when the negative block `A` of the transition has positive determinant
(`ContinuousLinearMap.orientation_map_ofInjective_eq_iff_det_pos`). The polar part
`h = A (AᵀA)^(-1/2)` of `A`, the orthogonal map comparing the characteristic discs of the two
charts, differs from `A` by a positive definite factor, so the criterion is equivalently
`det h = 1`.

## References

* J. Milnor, *Morse Theory*, Princeton University Press, 1963, §3, Remark 3.3.
-/

public section

open Module

variable {E F : Type*}

namespace Submodule

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {W W' : Submodule ℝ (E × F)}

/-- A submodule `W` of `E × F` is *split-negative* if the split indefinite form
`Q(u, v) = -‖u‖² + ‖v‖²` is negative on every nonzero vector of `W`: `‖v‖ < ‖u‖` for every
nonzero `(u, v) ∈ W`. -/
def IsSplitNegative (W : Submodule ℝ (E × F)) : Prop :=
  ∀ w ∈ W, w ≠ 0 → ‖w.2‖ < ‖w.1‖

theorem isSplitNegative_iff : W.IsSplitNegative ↔ ∀ w ∈ W, w ≠ 0 → ‖w.2‖ < ‖w.1‖ :=
  Iff.rfl

@[simp]
theorem isSplitNegative_bot : (⊥ : Submodule ℝ (E × F)).IsSplitNegative := by
  intro w hw hw0
  exact absurd ((mem_bot ℝ).1 hw) hw0

/-- A submodule of a split-negative subspace is split-negative. -/
theorem IsSplitNegative.mono (hW : W.IsSplitNegative) (h : W' ≤ W) : W'.IsSplitNegative :=
  fun w hw ↦ hW w (h hw)

/-- A nonzero vector of a split-negative subspace has nonzero first component. -/
theorem IsSplitNegative.fst_ne_zero (hW : W.IsSplitNegative) {w : E × F} (hw : w ∈ W)
    (hw0 : w ≠ 0) : w.1 ≠ 0 := by
  intro h
  have := hW w hw hw0
  rw [h, norm_zero] at this
  exact (norm_nonneg _).not_gt this

/-- A split-negative subspace meets the positive factor `0 × F` only in `0`. -/
theorem IsSplitNegative.disjoint_ker_fst (hW : W.IsSplitNegative) :
    Disjoint W (LinearMap.ker (LinearMap.fst ℝ E F)) := by
  rw [disjoint_def]
  intro w hw hw'
  by_contra hw0
  exact hW.fst_ne_zero hw hw0 hw'

/-- The graph of a linear map `T : E → F` is split-negative exactly when `T` strictly decreases
the norm of every nonzero vector. -/
theorem isSplitNegative_graph_iff (T : E →ₗ[ℝ] F) :
    (LinearMap.graph T).IsSplitNegative ↔ ∀ u, u ≠ 0 → ‖T u‖ < ‖u‖ := by
  refine ⟨fun h u hu ↦ h (u, T u) rfl fun h0 ↦ hu congr(($h0).1), fun h w hw hw0 ↦ ?_⟩
  rw [LinearMap.mem_graph_iff] at hw
  rw [hw]
  refine h _ fun h1 ↦ hw0 (Prod.ext h1 ?_)
  rw [hw, h1, map_zero, Prod.snd_zero]

end Normed

section InnerProduct

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {W : Submodule ℝ (E × F)}

omit [FiniteDimensional ℝ E] in
/-- If a nonzero vector `u` is orthogonal to the projection of a split-negative subspace `W` to
`E`, then adding `(u, 0)` to `W` keeps it split-negative. -/
private theorem IsSplitNegative.sup_span_inl (hW : W.IsSplitNegative) {u : E}
    (hu : u ∈ (LinearMap.range ((LinearMap.fst ℝ E F).comp W.subtype))ᗮ) (hu0 : u ≠ 0) :
    (W ⊔ span ℝ {((u, 0) : E × F)}).IsSplitNegative := by
  intro x hx hx0
  obtain ⟨w, hw, y, hy, rfl⟩ := mem_sup.1 hx
  obtain ⟨t, rfl⟩ := mem_span_singleton.1 hy
  have horth : inner ℝ w.1 (t • u) = 0 :=
    inner_right_of_mem_orthogonal (LinearMap.mem_range.2 ⟨⟨w, hw⟩, rfl⟩) (smul_mem _ t hu)
  have hpyth := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_mk, smul_zero, add_zero]
  by_cases hw0 : w = 0
  · subst hw0
    have ht : t ≠ 0 := by
      rintro rfl
      simp at hx0
    simp [norm_smul, ht, hu0]
  · have h1 := hW w hw hw0
    have h2 : ‖w.1‖ ≤ ‖w.1 + t • u‖ := by
      nlinarith [norm_nonneg (w.1 + t • u), norm_nonneg w.1, mul_self_nonneg ‖t • u‖]
    exact h1.trans_le h2

/-- Over a finite-dimensional inner product space `E`, a split-negative subspace of `E × F` is
maximal exactly when its dimension is `dim E`. -/
theorem maximal_isSplitNegative_iff :
    Maximal IsSplitNegative W ↔ W.IsSplitNegative ∧ finrank ℝ W = finrank ℝ E := by
  refine ⟨fun h ↦ ⟨h.prop, le_antisymm (W.finrank_le_of_norm_snd_lt h.prop)
    (not_lt.1 fun hlt ↦ ?_)⟩,
    fun ⟨hW, hdim⟩ ↦ ⟨hW, fun W' hW' hle ↦ ?_⟩⟩
  · -- A subspace of smaller dimension can be enlarged by a vector orthogonal to its projection.
    have hP : LinearMap.range ((LinearMap.fst ℝ E F).comp W.subtype) ≠ ⊤ := by
      intro htop
      have := LinearMap.finrank_range_of_inj (W.injective_fst_of_norm_snd_lt h.prop)
      rw [htop, finrank_top] at this
      omega
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 (mt orthogonal_eq_bot_iff.1 hP)
    have hmem : ((u, 0) : E × F) ∈ W :=
      h.2 (h.prop.sup_span_inl hu hu0) le_sup_left (mem_sup_right (mem_span_singleton_self _))
    exact hu0 (inner_self_eq_zero.1
      (inner_right_of_mem_orthogonal (LinearMap.mem_range.2 ⟨⟨_, hmem⟩, rfl⟩) hu))
  · exact (eq_of_le_of_finrank_eq_of_norm_snd_lt _ _ hle hdim hW').ge

/-- The projection of a maximal split-negative subspace to the negative factor is bijective. -/
theorem bijective_fst_of_maximal_isSplitNegative (hW : Maximal IsSplitNegative W) :
    Function.Bijective ((LinearMap.fst ℝ E F).comp W.subtype) := by
  have := W.finiteDimensional_of_norm_snd_lt hW.prop
  have hinj := W.injective_fst_of_norm_snd_lt hW.prop
  exact ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (maximal_isSplitNegative_iff.1 hW).2).1 hinj⟩

/-- Over a finite-dimensional inner product space `E`, the maximal split-negative subspaces of
`E × F` are exactly the graphs of the continuous linear maps `T : E → F` with `‖T‖ < 1`. -/
theorem maximal_isSplitNegative_iff_exists_eq_graph :
    Maximal IsSplitNegative W ↔
      ∃ T : E →L[ℝ] F, ‖T‖ < 1 ∧ W = LinearMap.graph (T : E →ₗ[ℝ] F) := by
  constructor
  · intro h
    exact W.exists_eq_graph_of_finrank_eq_of_norm_snd_lt (maximal_isSplitNegative_iff.1 h).2 h.prop
  · rintro ⟨T, hT, rfl⟩
    refine maximal_isSplitNegative_iff.2
      ⟨T.opNorm_lt_one_iff_forall_mem_graph_norm_snd_lt.1 hT, ?_⟩
    rw [LinearMap.graph_eq_range_prod, LinearMap.finrank_range_of_inj]
    intro x y hxy
    exact congr(($hxy).1)

/-- The projection to the negative factor `E` of a maximal split-negative subspace `W` of `E × F`,
as a linear equivalence. If `W` is the graph of `T`, its inverse is `u ↦ (u, T u)`
(`Submodule.coe_splitNegativeFstEquiv_symm_apply`). -/
noncomputable def splitNegativeFstEquiv (hW : Maximal IsSplitNegative W) : W ≃ₗ[ℝ] E :=
  LinearEquiv.ofBijective ((LinearMap.fst ℝ E F).comp W.subtype)
    (bijective_fst_of_maximal_isSplitNegative hW)

@[simp]
theorem splitNegativeFstEquiv_apply (hW : Maximal IsSplitNegative W) (w : W) :
    splitNegativeFstEquiv hW w = (w : E × F).1 := by
  simp [splitNegativeFstEquiv]

theorem coe_splitNegativeFstEquiv (hW : Maximal IsSplitNegative W) :
    (splitNegativeFstEquiv hW : W →ₗ[ℝ] E) = (LinearMap.fst ℝ E F).comp W.subtype := by
  ext
  simp

/-- If a maximal split-negative subspace is the graph of `T`, the inverse of its projection to
the negative factor is `u ↦ (u, T u)`. -/
theorem coe_splitNegativeFstEquiv_symm_apply (hW : Maximal IsSplitNegative W) {T : E →ₗ[ℝ] F}
    (hT : W = LinearMap.graph T) (u : E) :
    ((splitNegativeFstEquiv hW).symm u : E × F) = (u, T u) := by
  set w := (splitNegativeFstEquiv hW).symm u
  have h1 : (w : E × F).1 = u := by
    rw [← splitNegativeFstEquiv_apply hW, LinearEquiv.apply_symm_apply]
  have h2 : (w : E × F).2 = T (w : E × F).1 := (LinearMap.mem_graph_iff _ _).1 (hT ▸ w.2)
  exact Prod.ext h1 (h2.trans (h1 ▸ rfl))

/-- **Comparison of orientations of a maximal negative subspace.** Let `e : E ≃ W` identify `E`
with a maximal split-negative subspace `W`. An orientation of `E` carried to `W` along `e` agrees
with the orientation carried along the graph coordinates of `W` exactly when the first component
`u ↦ (e u).1` of `e` has positive determinant. -/
theorem orientation_map_eq_map_splitNegativeFstEquiv_symm_iff {ι : Type*} [Fintype ι]
    (hW : Maximal IsSplitNegative W) (e : E ≃ₗ[ℝ] W) (o : Orientation ℝ E ι)
    (hι : Fintype.card ι = finrank ℝ E) :
    Orientation.map ι e o = Orientation.map ι (splitNegativeFstEquiv hW).symm o ↔
      0 < LinearMap.det ((LinearMap.fst ℝ E F).comp (W.subtype.comp (e : E →ₗ[ℝ] W))) := by
  rw [← Orientation.map_symm, Equiv.eq_symm_apply, ← Orientation.map_trans,
    Orientation.map_eq_iff_det_pos _ _ hι, LinearEquiv.coe_trans, coe_splitNegativeFstEquiv,
    LinearMap.comp_assoc]

end InnerProduct

end Submodule

namespace TauCeti

open Submodule

variable (E F) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Taking graphs is a bijection from the open unit ball of `E →L[ℝ] F` onto the maximal
split-negative subspaces of `E × F`. -/
private theorem bijective_graph_ball :
    Function.Bijective fun T : Metric.ball (0 : E →L[ℝ] F) 1 ↦
      (⟨LinearMap.graph ((T : E →L[ℝ] F) : E →ₗ[ℝ] F),
        maximal_isSplitNegative_iff_exists_eq_graph.2 ⟨T, mem_ball_zero_iff.1 T.2, rfl⟩⟩ :
        {W : Submodule ℝ (E × F) // Maximal IsSplitNegative W}) := by
  refine ⟨fun T₁ T₂ h ↦ Subtype.ext ?_, fun W ↦ ?_⟩
  · -- Graph coordinates are unique on a full-dimensional negative subspace.
    set W := LinearMap.graph ((T₁ : E →L[ℝ] F) : E →ₗ[ℝ] F)
    have h' : W = LinearMap.graph ((T₂ : E →L[ℝ] F) : E →ₗ[ℝ] F) := congrArg Subtype.val h
    have hW : Maximal IsSplitNegative W :=
      maximal_isSplitNegative_iff_exists_eq_graph.2 ⟨T₁, mem_ball_zero_iff.1 T₁.2, rfl⟩
    obtain ⟨hneg, hdim⟩ := maximal_isSplitNegative_iff.1 hW
    exact ((existsUnique_eq_graph_iff_finrank_eq_and_norm_snd_lt W).2 ⟨hdim, hneg⟩).unique
      ⟨mem_ball_zero_iff.1 T₁.2, rfl⟩ ⟨mem_ball_zero_iff.1 T₂.2, h'⟩
  · obtain ⟨T, hT, hW⟩ := maximal_isSplitNegative_iff_exists_eq_graph.1 W.2
    exact ⟨⟨T, mem_ball_zero_iff.2 hT⟩, Subtype.ext hW.symm⟩

/-- **Graph coordinates on maximal negative subspaces.** Over a finite-dimensional inner product
space `E`, taking graphs is a bijection from the open unit ball of `E →L[ℝ] F` onto the maximal
split-negative subspaces of `E × F`, those on which `-‖u‖² + ‖v‖²` is negative definite. -/
noncomputable def splitNegativeGraphEquiv :
    Metric.ball (0 : E →L[ℝ] F) 1 ≃ {W : Submodule ℝ (E × F) // Maximal IsSplitNegative W} :=
  Equiv.ofBijective _ (bijective_graph_ball E F)

variable {E F}

@[simp]
theorem coe_splitNegativeGraphEquiv_apply (T : Metric.ball (0 : E →L[ℝ] F) 1) :
    (splitNegativeGraphEquiv E F T : Submodule ℝ (E × F)) =
      LinearMap.graph ((T : E →L[ℝ] F) : E →ₗ[ℝ] F) := by
  simp [splitNegativeGraphEquiv]

variable (E F)

/-- The graph-coordinate topology on the maximal split-negative subspaces of `E × F`: the
topology induced from the open unit ball of `E →L[ℝ] F` by the inverse of
`TauCeti.splitNegativeGraphEquiv`. -/
noncomputable instance splitNegativeGraphTopology :
    TopologicalSpace {W : Submodule ℝ (E × F) // Maximal IsSplitNegative W} :=
  TopologicalSpace.induced (splitNegativeGraphEquiv E F).symm inferInstance

/-- Graph coordinates as a homeomorphism from the open unit ball of `E →L[ℝ] F` onto the maximal
split-negative subspaces of `E × F`, with the graph-coordinate topology. -/
noncomputable def splitNegativeGraphHomeomorph :
    Metric.ball (0 : E →L[ℝ] F) 1 ≃ₜ {W : Submodule ℝ (E × F) // Maximal IsSplitNegative W} :=
  ((splitNegativeGraphEquiv E F).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

@[simp]
theorem coe_splitNegativeGraphHomeomorph :
    ⇑(splitNegativeGraphHomeomorph E F) = splitNegativeGraphEquiv E F := by
  ext
  simp [splitNegativeGraphHomeomorph]

/-- **Contractibility of the space of maximal negative subspaces.** In graph coordinates, the
space of maximal split-negative subspaces of `E × F` is contractible: it is homeomorphic to the
open unit ball of `E →L[ℝ] F`, a convex set. -/
instance contractibleSpace_maximal_isSplitNegative :
    ContractibleSpace {W : Submodule ℝ (E × F) // Maximal IsSplitNegative W} :=
  haveI := Metric.contractibleSpace_ball (x := (0 : E →L[ℝ] F)) one_pos
  (splitNegativeGraphHomeomorph E F).symm.contractibleSpace

end TauCeti

namespace ContinuousLinearMap

section Normed

variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (L : E →L[ℝ] E × F)

/-- The range of an isometric negative column is split-negative. -/
theorem isSplitNegative_range_of_norm_sq_sub
    (hL : ∀ u, ‖(L u).1‖ ^ 2 - ‖(L u).2‖ ^ 2 = ‖u‖ ^ 2) :
    (LinearMap.range (L : E →ₗ[ℝ] E × F)).IsSplitNegative := by
  rintro _ ⟨u, rfl⟩ hu
  exact L.norm_snd_lt_norm_fst_of_norm_sq_sub hL fun h ↦ hu (by simp [h])

end Normed

section InnerProduct

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  (L : E →L[ℝ] E × F) (hL : ∀ u, ‖(L u).1‖ ^ 2 - ‖(L u).2‖ ^ 2 = ‖u‖ ^ 2)

include hL

/-- Over a finite-dimensional inner product space, the range of an isometric negative column is a
maximal split-negative subspace. -/
theorem maximal_isSplitNegative_range_of_norm_sq_sub :
    Maximal Submodule.IsSplitNegative (LinearMap.range (L : E →ₗ[ℝ] E × F)) :=
  Submodule.maximal_isSplitNegative_iff.2 ⟨L.isSplitNegative_range_of_norm_sq_sub hL,
    LinearMap.finrank_range_of_inj (L.injective_of_norm_sq_sub hL)⟩

/-- **Chart-induced orientations of a negative subspace.** Let `u ↦ (A u, B u)` be an isometric
negative column, for instance the negative column of the derivative of a transition between two
Morse charts, and let `o` be an orientation of `E`. The orientation `o` carried to its range
along the column agrees with `o` carried along the graph coordinates of the range exactly when
the negative block `A` has positive determinant. -/
theorem orientation_map_ofInjective_eq_iff_det_pos {ι : Type*} [Fintype ι]
    (o : Orientation ℝ E ι) (hι : Fintype.card ι = finrank ℝ E) :
    Orientation.map ι (LinearEquiv.ofInjective (L : E →ₗ[ℝ] E × F)
        (L.injective_of_norm_sq_sub hL)) o =
      Orientation.map ι (Submodule.splitNegativeFstEquiv
        (L.maximal_isSplitNegative_range_of_norm_sq_sub hL)).symm o ↔
      0 < LinearMap.det (((fst ℝ E F).comp L : E →L[ℝ] E) : E →ₗ[ℝ] E) := by
  rw [Submodule.orientation_map_eq_map_splitNegativeFstEquiv_symm_iff _ _ _ hι]
  congr! 2

end InnerProduct

end ContinuousLinearMap
