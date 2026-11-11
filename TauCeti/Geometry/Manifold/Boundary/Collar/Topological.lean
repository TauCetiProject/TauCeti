/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Brown
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local

/-!
# The topological collar of the boundary of a manifold

Let `M` be a `C^k` manifold with boundary modelled on the half-space `𝓡∂ (n + 1)`, with `k ≠ 0`.
Every boundary point has a product collar chart
(`TauCeti.exists_isProductCollarChart_of_mem_boundary`), whose source is homeomorphic to its part
of the boundary times a half-open interval (`TauCeti.IsProductCollarChart.homeomorphProd`).
Rescaling the interval to `[0, 1)` makes this a collar of the boundary points of the source, in
the sense of `TauCeti.IsCollar`, whose points of positive depth are interior points of `M`
(`TauCeti.IsProductCollarChart.exists_isCollar`). So the inclusion of the boundary `∂M → M` is
locally collared in the sense of M. Brown (`TauCeti.isLocallyCollared_subtypeVal_boundary`).

When the boundary is compact and `M` is Hausdorff, Brown's collaring theorem
(`TauCeti.IsLocallyCollared.isCollared`) assembles these local collars into a single collar: an
open embedding `c : ∂M × [0, 1) → M` with `c (x, 0) = x`
(`TauCeti.isCollared_subtypeVal_boundary`). This holds in particular for compact `M`, whose
boundary is closed (`TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`).

The collar is only a topological one. It is what comparisons of the relative homology
`H_*(M, ∂M)` with the homology of `M` relative to an open neighbourhood of the boundary use, for
instance to construct the fundamental class of a compact manifold relative to its boundary. A
smooth collar, a diffeomorphism onto its image, is a stronger statement not treated here.

## Main results

* `TauCeti.IsProductCollarChart.exists_isCollar`: the boundary points of the source of a product
  collar chart have a collar meeting the boundary only at depth zero.
* `TauCeti.isLocallyCollared_subtypeVal_boundary`: the boundary of a `C^k` manifold, `k ≠ 0`, is
  locally collared.
* `TauCeti.isCollared_subtypeVal_boundary`: a compact boundary of a Hausdorff `C^k` manifold,
  `k ≠ 0`, is collared.
* `TauCeti.isCollared_subtypeVal_boundary_of_compactSpace`: the boundary of a compact Hausdorff
  `C^k` manifold, `k ≠ 0`, is collared.

## References

* M. Brown, *Locally flat imbeddings of topological manifolds*, Annals of Mathematics 75 (1962),
  331–341.
* R. Connelly, *A new proof of Brown's collaring theorem*, Proceedings of the American Mathematical
  Society 27 (1971), 180–182.
-/

public section

open Set Topology
open scoped Manifold

namespace TauCeti

/-- The scaling `t ↦ ε t` of half-open intervals, `[0, 1) ≃ₜ [0, ε)`. -/
private noncomputable def icoScale {ε : ℝ} (hε : 0 < ε) :
    ↥(Ico (0 : ℝ) 1) ≃ₜ ↥(Ico (0 : ℝ) ε) where
  toFun t := ⟨ε * t, mul_nonneg hε.le t.2.1, mul_lt_of_lt_one_right hε t.2.2⟩
  invFun s := ⟨s / ε, div_nonneg s.2.1 hε.le, (div_lt_one hε).2 s.2.2⟩
  left_inv t := Subtype.ext (mul_div_cancel_left₀ _ hε.ne')
  right_inv s := Subtype.ext (mul_div_cancel₀ _ hε.ne')
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem coe_icoScale {ε : ℝ} (hε : 0 < ε) (t : ↥(Ico (0 : ℝ) 1)) :
    (icoScale hε t : ℝ) = ε * t :=
  (rfl)

/-- The depth coordinate of a local collar: `t ∈ [0, 1)` is sent to the point of normal coordinate
`ε t` of the initial segment `[0, ε)` of the one-dimensional half-space model. -/
private noncomputable def depthHomeomorph {ε : ℝ} (hε : 0 < ε) :
    ↥(Ico (0 : ℝ) 1) ≃ₜ ↥(EuclideanHalfSpace.normalIio ε) :=
  (icoScale hε).trans (EuclideanHalfSpace.homeomorphNormalIio ε).symm

private theorem depthHomeomorph_apply_coe_zero {ε : ℝ} (hε : 0 < ε) (t : ↥(Ico (0 : ℝ) 1)) :
    (depthHomeomorph hε t : EuclideanHalfSpace 1).1 0 = ε * t := by
  rw [← EuclideanHalfSpace.coe_homeomorphNormalIio, depthHomeomorph, Homeomorph.trans_apply,
    Homeomorph.apply_symm_apply, coe_icoScale]

variable {n : ℕ} {k : WithTop ℕ∞} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

namespace IsProductCollarChart

variable {φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin n) × EuclideanHalfSpace 1)}
  {V : Set (EuclideanSpace ℝ (Fin n))} {ε : ℝ}

/-- The boundary points lying in a set `s`, read as a subset of the boundary or of `s`. -/
private def boundaryPreimageHomeomorph (s : Set M) :
    ↥(((↑) : (𝓡∂ (n + 1)).boundary M → M) ⁻¹' s) ≃ₜ ↥(s ∩ (𝓡∂ (n + 1)).boundary M) where
  toFun y := ⟨y.1, y.2, y.1.2⟩
  invFun y := ⟨⟨y, y.2.2⟩, y.2.1⟩
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- The local collar of a product collar chart, as a homeomorphism from the boundary points of
its source times `[0, 1)` onto its source. -/
private noncomputable def collarHomeomorph (h : IsProductCollarChart k φ V ε) :
    ↥(((↑) : (𝓡∂ (n + 1)).boundary M → M) ⁻¹' φ.source) × ↥(Ico (0 : ℝ) 1) ≃ₜ ↥φ.source :=
  ((boundaryPreimageHomeomorph φ.source).prodCongr (depthHomeomorph h.height_pos)).trans
    h.homeomorphProd.symm

private theorem homeomorphProd_collarHomeomorph (h : IsProductCollarChart k φ V ε)
    (p : ↥(((↑) : (𝓡∂ (n + 1)).boundary M → M) ⁻¹' φ.source) × ↥(Ico (0 : ℝ) 1)) :
    h.homeomorphProd (h.collarHomeomorph p) =
      (boundaryPreimageHomeomorph φ.source p.1, depthHomeomorph h.height_pos p.2) :=
  h.homeomorphProd.apply_symm_apply _

/-- The chart value of a point of the local collar has normal coordinate `ε t` at depth `t`. -/
private theorem snd_collarHomeomorph (h : IsProductCollarChart k φ V ε)
    (p : ↥(((↑) : (𝓡∂ (n + 1)).boundary M → M) ⁻¹' φ.source) × ↥(Ico (0 : ℝ) 1)) :
    (φ (h.collarHomeomorph p)).2.1 0 = ε * p.2 := by
  rw [← h.coe_homeomorphProd_snd, h.homeomorphProd_collarHomeomorph,
    depthHomeomorph_apply_coe_zero]

/-- The local collar sends a boundary point at depth zero to itself. -/
private theorem collarHomeomorph_zero (h : IsProductCollarChart k φ V ε)
    (y : ↥(((↑) : (𝓡∂ (n + 1)).boundary M → M) ⁻¹' φ.source)) :
    (h.collarHomeomorph (y, ⟨0, le_rfl, zero_lt_one⟩) : M) = y := by
  -- A boundary point of the chart source has normal coordinate zero, and both points have the
  -- same tangential coordinate.
  have hy0 : (φ y).2 = 0 := EuclideanHalfSpace.eq_zero_iff.2 ((h.mem_boundary_iff _ y.2).1 y.1.2)
  refine φ.injOn (h.collarHomeomorph _).2 y.2 (Prod.ext ?_ ?_)
  · have hfst := h.map_homeomorphProd_fst (h.collarHomeomorph (y, ⟨0, le_rfl, zero_lt_one⟩))
    rw [h.homeomorphProd_collarHomeomorph] at hfst
    exact (congrArg Prod.fst hfst).symm
  · rw [hy0, EuclideanHalfSpace.eq_zero_iff, h.snd_collarHomeomorph, mul_zero]

/-- **The local collar of a product collar chart.** The boundary points of the source of a product
collar chart have a collar in `M`, an open embedding of their product with `[0, 1)` whose zero
slice is the inclusion, and whose points of positive depth are not boundary points of `M`. -/
theorem exists_isCollar (h : IsProductCollarChart k φ V ε) :
    ∃ c : ↥(((↑) : (𝓡∂ (n + 1)).boundary M → M) ⁻¹' φ.source) × ↥(Ico (0 : ℝ) 1) → M,
      IsCollar (((↑) : (𝓡∂ (n + 1)).boundary M → M) ∘ (↑)) c ∧
        ∀ p, c p ∈ (𝓡∂ (n + 1)).boundary M → (p.2 : ℝ) = 0 := by
  refine ⟨fun p ↦ h.collarHomeomorph p,
    ⟨φ.open_source.isOpenEmbedding_subtypeVal.comp h.collarHomeomorph.isOpenEmbedding,
      h.collarHomeomorph_zero⟩, fun p hp ↦ ?_⟩
  have hp0 := (h.mem_boundary_iff _ (h.collarHomeomorph p).2).1 hp
  rw [h.snd_collarHomeomorph] at hp0
  exact (mul_eq_zero.1 hp0).resolve_left h.height_pos.ne'

end IsProductCollarChart

variable [IsManifold (𝓡∂ (n + 1)) k M]

/-- **The boundary of a manifold is locally collared.** For a `C^k` manifold with boundary,
`k ≠ 0`, every boundary point has an open neighbourhood in the boundary with a collar in `M` whose
points of positive depth are interior points: the local collar of a product collar chart. -/
theorem isLocallyCollared_subtypeVal_boundary (hk : k ≠ 0) :
    IsLocallyCollared ((↑) : (𝓡∂ (n + 1)).boundary M → M) := by
  refine isLocallyCollared_iff.2 fun x ↦ ?_
  obtain ⟨φ, V, ε, hxφ, h⟩ := exists_isProductCollarChart_of_mem_boundary hk x.2
  obtain ⟨c, hc, hc0⟩ := h.exists_isCollar
  exact ⟨_, φ.open_source.preimage continuous_subtype_val, hxφ, c, hc,
    fun p ⟨y, hy⟩ ↦ hc0 p (hy ▸ y.2)⟩

/-- **The collar of a compact boundary.** If the boundary of a Hausdorff `C^k` manifold, `k ≠ 0`,
is compact, then it is collared: there is an open embedding `c : ∂M × [0, 1) → M` with
`c (x, 0) = x`. This is Brown's collaring theorem applied to the local collars. -/
theorem isCollared_subtypeVal_boundary (hk : k ≠ 0) [T2Space M]
    (hK : IsCompact ((𝓡∂ (n + 1)).boundary M)) :
    IsCollared ((↑) : (𝓡∂ (n + 1)).boundary M → M) :=
  have := isCompact_iff_compactSpace.1 hK
  (isLocallyCollared_subtypeVal_boundary hk).isCollared Subtype.val_injective

/-- **The boundary of a compact manifold is collared.** For a compact Hausdorff `C^k` manifold
with boundary, `k ≠ 0`, there is an open embedding `c : ∂M × [0, 1) → M` with `c (x, 0) = x`. -/
theorem isCollared_subtypeVal_boundary_of_compactSpace (hk : k ≠ 0) [CompactSpace M] [T2Space M] :
    IsCollared ((↑) : (𝓡∂ (n + 1)).boundary M → M) :=
  isCollared_subtypeVal_boundary hk ((𝓡∂ (n + 1)).isClosed_boundary hk).isCompact

end TauCeti
