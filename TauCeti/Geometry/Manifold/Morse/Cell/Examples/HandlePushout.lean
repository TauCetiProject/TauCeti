/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Cell.HandlePushout
public import TauCeti.Geometry.Manifold.Morse.Sphere.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import TauCeti.AlgebraicTopology.Disk
import TauCeti.Geometry.Manifold.Morse.Examples.QuadraticWell
import TauCeti.Topology.Algebra.Polynomial.Basic

/-!
# Handle attachments in examples

Milnor's handle attachment theorem in pushout form
(`TauCeti.IsMorse.exists_isPushout_sublevel_handles`) presents the sublevel `M_{c+ε} = {f ≤ c + ε}`
of a Morse function as the lower sublevel `M_{c-ε}` with one handle `𝔻 λ × 𝔻 (m - λ)` attached for
each critical point of index `λ` on the level `c`, along closed embeddings
`α : ∂𝔻 λ × 𝔻 (m - λ) → M_{c-ε}` into the level `f⁻¹(c - ε)`. This file reads off what the theorem
says for the simplest Morse functions, one for each extreme case of the index.

At a level with a single critical point the coproducts of the theorem have a single summand, so
the theorem presents `M_{c+ε}` as the pushout of `M_{c-ε}` and one handle along its attaching map
(`TauCeti.IsMorse.exists_isPushout_sublevel_handle`).

* **Index `0`: the quadratic well.** For `f(x) = x²` on `ℝ` at the level `0`, the lower sublevel
  `{x² ≤ -ε}` is empty and the attaching region `∂𝔻 0 × 𝔻 1` of the handle at the minimum `0` is
  empty, so the handle map `𝔻 0 × 𝔻 1 → {x² ≤ ε}` is itself a homeomorphism, carrying the top
  `𝔻 0 × ∂𝔻 1` of the handle onto the two ends `±√ε`
  (`TauCeti.exists_isIso_handle_sq_real`). The sublevel is the interval `[-√ε, √ε]`
  (`Real.setOf_sq_le_eq_Icc`): a handle of index `0` adds a new component, here the only one.
  The handle is a product of closed balls: the compact sublevel is not homeomorphic to the open
  unit ball of `EuclideanSpace ℝ (Fin 1)`, an open interval
  (`TauCeti.not_nonempty_homeomorph_setOf_sq_le_ball`).
* **Index `1` in dimension `1`: the inverted well.** For `f(x) = -x²` on `ℝ` at the level `0`, the
  critical point `0` has index `1` (`TauCeti.manifoldMorseIndex_neg_sq_real`). The lower sublevel
  `{-x² ≤ -ε} = {ε ≤ x²}` is the union of the two rays `(-∞, -√ε]` and `[√ε, ∞)`
  (`Real.setOf_le_sq_eq_union`), and the line `{-x² ≤ ε} = ℝ` is the pushout of these rays
  and the arc `𝔻 1 × 𝔻 0` along an attaching map `∂𝔻 1 × 𝔻 0 → {-x² ≤ -ε}` sending the two points
  of the attaching sphere to the two ends `-√ε` and `√ε` of the rays
  (`TauCeti.exists_isPushout_neg_sq_real`): the arc joins the two rays into the line.
* **Index `n` in dimension `n`: the height on the sphere.** For the height `h = ⟪·, v⟫` on `Sⁿ` at
  its maximum value `1`, the critical point `v` has index `n`. The sphere `{h ≤ 1 + ε} = Sⁿ` is the
  pushout of `{h ≤ 1 - ε}` and the disc `𝔻 n × 𝔻 0` along an attaching map
  `∂𝔻 n × 𝔻 0 → {h ≤ 1 - ε}` that is a closed embedding whose image is the whole level sphere
  `{h = 1 - ε}` (`TauCeti.exists_isPushout_sphereHeight`): it lies in that level by the theorem,
  and it covers it because the level `{h = 1 + ε}` above is empty, while the theorem places every
  point of the lower level off the attaching regions on the upper level. Attaching the disc closes
  up the sphere.

When the level `c` carries no critical point, the index type of the handles is empty, and the
theorem says that `M_{c+ε}` is homeomorphic to `M_{c-ε}`; this is the deformation across a band
without critical points (`TauCeti.exists_sublevelHomeomorph`), and is recorded below as an example.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.2 and Remark 3.3.
-/

public section

noncomputable section

open CategoryTheory Limits Function Set Metric Topology
open scoped Manifold ContDiff

universe u

namespace TauCeti

/-! ### The quadratic well -/

/-- **The handle of the quadratic well.** At the level `0` of `f(x) = x²` on `ℝ`, the handle
attachment theorem (`TauCeti.IsMorse.exists_isPushout_sublevel_handles`) attaches one handle
`𝔻 0 × 𝔻 1`, at the minimum `0`, which has index `0`, to the empty lower sublevel `{x² ≤ -ε}`, along
its empty attaching region. So for some `0 < ε ≤ 1` the handle map `χ : 𝔻 0 × 𝔻 1 → {x² ≤ ε}` is an
isomorphism, and it carries the top `𝔻 0 × ∂𝔻 1` of the handle onto the boundary level `x² = ε`,
the two ends `±√ε` of the interval `{x² ≤ ε} = [-√ε, √ε]`. -/
theorem exists_isIso_handle_sq_real :
    ∃ ε, 0 < ε ∧ ε ≤ 1 ∧
      ∃ χ : TopCat.of (TopCat.disk.{0} 0 × TopCat.disk.{0} 1) ⟶ TopCat.of {x : ℝ | x ^ 2 ≤ ε},
        IsIso χ ∧ ∀ w, (χ w : ℝ) ^ 2 = ε ↔ w.2 ∈ range (TopCat.diskBoundaryInclusion 1) := by
  obtain ⟨ε, hε, hε1, h⟩ :=
    isMorse_sq_real.exists_isPushout_sublevel_handle (c := 0) one_pos
      ((isProperMap_pow two_ne_zero).isCompact_preimage isCompact_Icc)
      (by rw [criticalPoints_sq_real, inter_eq_left, singleton_subset_iff]; simp)
      manifoldMorseIndex_sq_real_zero (l := 1) (by simp)
  rw [zero_sub, zero_add] at h
  obtain ⟨α, χ, j, hpush, -, -, htop, -⟩ := h
  -- The lower sublevel is empty, and so is the attaching region mapping to it, so the attaching
  -- map is the homeomorphism of empty spaces, and its pushout `χ` is an isomorphism too.
  have : IsEmpty {x : ℝ | x ^ 2 ≤ -ε} :=
    ⟨fun x ↦ by have h : (x : ℝ) ^ 2 ≤ -ε := x.property; nlinarith [sq_nonneg (x : ℝ)]⟩
  have : IsEmpty (TopCat.diskBoundary.{0} 0 × TopCat.disk.{0} 1) := ⟨fun s ↦ isEmptyElim (α s)⟩
  have : IsIso α := by
    rw [show α = (TopCat.isoOfHomeo .empty).hom from TopCat.ext isEmptyElim]
    infer_instance
  exact ⟨ε, hε, hε1, χ, hpush.isIso_inr_of_isIso, htop⟩

/-- **The handles are closed.** The sublevel `{x² ≤ ε}` of the quadratic well is compact, so it is
not homeomorphic to the open unit ball of `EuclideanSpace ℝ (Fin 1)`, an open interval, which is not
compact. So the handle `𝔻 0 × 𝔻 1` of `TauCeti.exists_isIso_handle_sq_real` cannot be replaced by
the product of open unit balls, which is homeomorphic to that open interval. -/
theorem not_nonempty_homeomorph_setOf_sq_le_ball (ε : ℝ) :
    ¬ Nonempty ({x : ℝ | x ^ 2 ≤ ε} ≃ₜ ball (0 : EuclideanSpace ℝ (Fin 1)) 1) := by
  rintro ⟨e⟩
  have : CompactSpace {x : ℝ | x ^ 2 ≤ ε} := isCompact_iff_compactSpace.1 <|
    (isCompact_Icc (a := -√ε) (b := √ε)).of_isClosed_subset
      (isClosed_le (continuous_pow 2) continuous_const) fun x hx ↦ abs_le.1 (Real.abs_le_sqrt hx)
  have hB : IsCompact (ball (0 : EuclideanSpace ℝ (Fin 1)) 1) :=
    isCompact_iff_compactSpace.2 e.compactSpace
  -- A compact open ball would be closed, and its frontier, the unit sphere, would be empty.
  obtain ⟨y, hy⟩ :=
    (NormedSpace.sphere_nonempty (x := (0 : EuclideanSpace ℝ (Fin 1)))).2 zero_le_one
  rw [← frontier_ball _ one_ne_zero, hB.isClosed.frontier_eq, isOpen_ball.interior_eq,
    sdiff_self] at hy
  exact hy

/-! ### The inverted well -/

/-- A map from the two points of `∂𝔻 1 × 𝔻 0` to `ℝ` which is injective and takes values of square
`a` has image `{-√a, √a}`. -/
private theorem range_eq_of_injective_of_sq_eq {a : ℝ}
    (g : TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0 → ℝ) (hg : Function.Injective g)
    (hsq : ∀ s, g s ^ 2 = a) : range g = {-√a, √a} := by
  have hmem (s) : g s = -√a ∨ g s = √a := by
    have h := Real.sqrt_sq_eq_abs (g s)
    rw [hsq s] at h
    rcases abs_eq (Real.sqrt_nonneg a) |>.1 h.symm with h' | h'
    exacts [Or.inr h', Or.inl h']
  -- The two points `(±1, 0)` of `∂𝔻 1 × 𝔻 0` go to the two square roots, in some order.
  let sp : TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0 :=
    (ULift.up ⟨EuclideanSpace.single 0 1, by simp⟩, diskCenter 0)
  let sm : TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0 :=
    (ULift.up ⟨EuclideanSpace.single 0 (-1), by simp⟩, diskCenter 0)
  have hne : g sp ≠ g sm := hg.ne fun h ↦ by
    have := congrArg (fun s : TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0 ↦
      (s.1.down : EuclideanSpace ℝ (Fin 1)) 0) h
    norm_num [sp, sm] at this
  refine Subset.antisymm (range_subset_iff.2 fun s ↦ ?_) fun y hy ↦ ?_
  · rcases hmem s with h | h <;> simp [h]
  · rcases hy with rfl | rfl <;> rcases hmem sp with hp | hp <;> rcases hmem sm with hm | hm
    all_goals first
      | exact ⟨sp, hp⟩ | exact ⟨sm, hm⟩ | exact absurd (hp.trans hm.symm) hne

/-- **The handle of the inverted well.** At the level `0` of `f(x) = -x²` on `ℝ`, the handle
attachment theorem (`TauCeti.IsMorse.exists_isPushout_sublevel_handles`) attaches one handle
`𝔻 1 × 𝔻 0`, at the maximum `0`, which has index `1`. So for some `0 < ε ≤ 1` the line
`{-x² ≤ ε} = ℝ` is the pushout of the lower sublevel `{-x² ≤ -ε}` and the arc `𝔻 1 × 𝔻 0` along
the attaching map `α : ∂𝔻 1 × 𝔻 0 → {-x² ≤ -ε}`, and `α` is a closed embedding sending the two
points of the attaching sphere `∂𝔻 1` onto the two points `-√ε` and `√ε` of the level `-x² = -ε`.
These are the ends of the two rays `(-∞, -√ε]` and `[√ε, ∞)` that make up the lower sublevel
`{-x² ≤ -ε} = {ε ≤ x²}` (`Real.setOf_le_sq_eq_union`), so the arc joins the two rays into the
line. -/
theorem exists_isPushout_neg_sq_real :
    ∃ ε, 0 < ε ∧ ε ≤ 1 ∧
      ∃ (α : TopCat.of (TopCat.diskBoundary.{0} 1 × TopCat.disk.{0} 0) ⟶
          TopCat.of {x : ℝ | -x ^ 2 ≤ -ε})
        (χ : TopCat.of (TopCat.disk.{0} 1 × TopCat.disk.{0} 0) ⟶ TopCat.of {x : ℝ | -x ^ 2 ≤ ε})
        (j : TopCat.of {x : ℝ | -x ^ 2 ≤ -ε} ⟶ TopCat.of {x : ℝ | -x ^ 2 ≤ ε}),
        IsPushout α (TopCat.ofHom ((TopCat.diskBoundaryInclusion 1).hom.prodMap
          (ContinuousMap.id _))) j χ ∧
        IsClosedEmbedding α ∧ range (fun s ↦ (α s : ℝ)) = {-√ε, √ε} := by
  obtain ⟨ε, hε, hε1, h⟩ :=
    isMorse_neg_sq_real.exists_isPushout_sublevel_handle (c := 0) one_pos
      (((Homeomorph.neg ℝ).isProperMap.comp (isProperMap_pow two_ne_zero)).isCompact_preimage
        isCompact_Icc)
      (by rw [criticalPoints_neg_sq_real, inter_eq_left, singleton_subset_iff]; simp)
      manifoldMorseIndex_neg_sq_real (l := 0) (by simp)
  rw [zero_sub, zero_add] at h
  obtain ⟨α, χ, j, hpush, hemb, hlev, -, -⟩ := h
  exact ⟨ε, hε, hε1, α, χ, j, hpush, hemb, range_eq_of_injective_of_sq_eq _
    (Subtype.val_injective.comp hemb.injective) fun s ↦ by simpa using hlev s⟩

/-! ### The height on the sphere -/

section Sphere

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (Module.finrank ℝ E = n + 1)]

/-- **The handle at the top of the sphere.** At the level `1` of the height `h = ⟪·, v⟫` on the
unit sphere `Sⁿ`, the handle attachment theorem
(`TauCeti.IsMorse.exists_isPushout_sublevel_handles`) attaches one handle `𝔻 n × 𝔻 0`, at the north
pole `v`, which has index `n`. So for some `0 < ε ≤ 1` the sphere `{h ≤ 1 + ε} = Sⁿ` is the pushout
of the lower sublevel `{h ≤ 1 - ε}` and the disc `𝔻 n × 𝔻 0` along the attaching map
`α : ∂𝔻 n × 𝔻 0 → {h ≤ 1 - ε}`, and `α` is a closed embedding whose image is the whole level sphere
`{h = 1 - ε}`. The theorem puts the image in that level; it fills the level because the level
`{h = 1 + ε}` above the maximum is empty, while the theorem sends every point of `{h = 1 - ε}` off
the attaching region to that upper level. So the disc is attached along the whole level sphere and
closes up `Sⁿ`. -/
theorem exists_isPushout_sphereHeight (v : sphere (0 : E) 1) :
    ∃ ε, 0 < ε ∧ ε ≤ 1 ∧
      ∃ (α : TopCat.of (TopCat.diskBoundary.{u} n × TopCat.disk.{u} 0) ⟶
          TopCat.of {x | sphereHeight v x ≤ 1 - ε})
        (χ : TopCat.of (TopCat.disk.{u} n × TopCat.disk.{u} 0) ⟶
          TopCat.of {x | sphereHeight v x ≤ 1 + ε})
        (j : TopCat.of {x | sphereHeight v x ≤ 1 - ε} ⟶ TopCat.of {x | sphereHeight v x ≤ 1 + ε}),
        IsPushout α (TopCat.ofHom ((TopCat.diskBoundaryInclusion n).hom.prodMap
          (ContinuousMap.id _))) j χ ∧
        IsClosedEmbedding α ∧
          range (fun s ↦ (α s : sphere (0 : E) 1)) = {x | sphereHeight v x = 1 - ε} := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hlevel : criticalPoints (𝓡 n) (sphereHeight v) ∩ sphereHeight v ⁻¹' {1} = {v} := by
    ext x
    simp only [criticalPoints_sphereHeight, mem_inter_iff, mem_insert_iff, mem_singleton_iff,
      mem_preimage]
    constructor
    · rintro ⟨hx | hx, h⟩
      · exact hx
      · rw [hx, sphereHeight_neg_self] at h
        norm_num at h
    · rintro rfl
      exact ⟨Or.inl rfl, sphereHeight_self x⟩
  obtain ⟨ε, hε, hε1, α, χ, j, hpush, hemb, hlev, -, hj⟩ :=
    (isMorse_sphereHeight (n := n) v).exists_isPushout_sublevel_handle (c := 1) one_pos
      (isClosed_Icc.preimage (contMDiff_sphereHeight (n := n) (m := 0) v).continuous).isCompact
      hlevel (manifoldMorseIndex_sphereHeight_self v) (l := 0) (by simp)
  refine ⟨ε, hε, hε1, α, χ, j, hpush, hemb,
    Subset.antisymm (range_subset_iff.2 hlev) fun x hx ↦ ?_⟩
  -- Every point of the level `h = 1 - ε` lies on the attaching region: otherwise the theorem would
  -- send it to the empty level `h = 1 + ε`.
  by_contra hx'
  have h := (hj ⟨x, le_of_eq hx⟩ fun ⟨s, hs⟩ ↦ hx' ⟨s, congrArg Subtype.val hs⟩).2 hx
  linarith [sphereHeight_le_one v (j ⟨x, le_of_eq hx⟩ : sphere (0 : E) 1)]

end Sphere

/-! ### A level without critical points -/

/-- With no critical point on the level `c`, the handle attachment theorem attaches no handle, and
says that `{f ≤ c + ε}` is homeomorphic to `{f ≤ c - ε}`, as the deformation across a band without
critical points does (`TauCeti.exists_sublevelHomeomorph`). -/
example {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] {M : Type u}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] {f : M → ℝ}
    (hf : IsMorse I f) {c δ : ℝ} (hδ : 0 < δ) (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ)))
    (hc : criticalPoints I f ∩ f ⁻¹' {c} = ∅) :
    ∃ ε, 0 < ε ∧ ε ≤ δ ∧ Nonempty ({x | f x ≤ c - ε} ≃ₜ {x | f x ≤ c + ε}) := by
  obtain ⟨ε, hε, hεδ, α, χ, j, hpush, -⟩ := hf.exists_isPushout_sublevel_handles hδ hcompact
  have : IsEmpty ↥(criticalPoints I f ∩ f ⁻¹' {c}) := by rw [hc]; infer_instance
  -- The map between the coproducts over the empty set of handles is an isomorphism, with inverse
  -- the map out of the empty coproduct, and so is its pushout `j`.
  have : IsIso j := hpush.isIso_inl_of_isIso
    ⟨⟨Sigma.desc isEmptyElim, Sigma.hom_ext _ _ isEmptyElim, Sigma.hom_ext _ _ isEmptyElim⟩⟩
  exact ⟨ε, hε, hεδ, ⟨TopCat.homeoOfIso (asIso j)⟩⟩

end TauCeti
