/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Smooth
public import TauCeti.Geometry.Manifold.Orientation.OpenSubset
public import TauCeti.Geometry.Manifold.Orientation.Inversion
import TauCeti.Geometry.Manifold.Orientation.Glue
import TauCeti.Geometry.Manifold.ContMDiff.Subtype

/-!
# The orientation of a connected sum

The connected sum `TauCeti.ConnectedSum e₁ e₂` of two manifolds `M` and `N` removes the centres of
the balls `e₁ : E → M` and `e₂ : E → N` and glues `e₁ v` to `e₂ (inversion 0 1 v)` for `v ≠ 0`. For
oriented summands the result is oriented, provided the balls are chosen to induce opposite
orientations of `E`. This file constructs that orientation.

Let `o₁` and `o₂` be orientations of `M` and `N`, and let `oE` be an orientation of `E` such that
`e₁` preserves orientation from `oE` to `o₁` and `e₂` reverses orientation from `oE` to `o₂`, at
every `v ≠ 0`. The inversion `v ↦ v / ‖v‖²` reverses every orientation of `E`
(`TauCeti.Manifold.Orientation.isOrientationReversingAt_inversion`), so the gluing map
`e₂ ∘ inversion 0 1 ∘ e₁⁻¹` preserves orientation from `o₁` to `o₂`. Hence the orientations of the
punctured summands `M ∖ {e₁ 0}` and `N ∖ {e₂ 0}`, carried to the connected sum by the derivative of
the quotient map, agree wherever both are defined. The inclusions of the punctured summands are
injective local diffeomorphisms whose ranges cover `M # N`, so these orientations glue to an
orientation of `M # N` (`TauCeti.Manifold.Orientation.glue`), which is
`TauCeti.ConnectedSum.orientation`.

If instead both balls preserve orientation from `oE`, then `e₂` reverses orientation from `oE` to
`-o₂`, and the same construction orients `M # N` compatibly with `o₁` and `-o₂`. So the oriented
connected sum depends on the orientations of the summands, not only on the manifolds.

## Main definitions

* `TauCeti.ConnectedSum.orientation`: the orientation of the connected sum of oriented manifolds
  along balls inducing opposite orientations of `E`.

## Main results

* `TauCeti.ConnectedSum.isOrientationPreservingAt_inl`,
  `TauCeti.ConnectedSum.isOrientationPreservingAt_inr`: the inclusions of the punctured summands
  into the connected sum preserve orientation.
* `TauCeti.ConnectedSum.eq_orientation_iff`: this property characterizes the orientation.
* `TauCeti.ConnectedSum.orientable`: the connected sum of oriented manifolds along such balls is
  orientable.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1 (the connected
  sum of oriented manifolds).
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in Mathematics
  218, Springer (2013), Chapter 15 (orientations, and their pullbacks along local
  diffeomorphisms).
-/

public section

noncomputable section

open Set Function Filter Topology TopologicalSpace EuclideanGeometry Module
open scoped Manifold

namespace TauCeti.ConnectedSum

open Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T1Space M] [ChartedSpace H M] [IsManifold I 1 M]
  {N : Type*} [TopologicalSpace N] [T1Space N] [ChartedSpace H N] [IsManifold I 1 N]
  {e₁ : E → M} {e₂ : E → N} {ι : Type*} [Fintype ι]
  (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
  (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I 1 e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I 1 e₂)

/-- `TauCeti.ConnectedSum.isLocalDiffeomorph_inl` and `isLocalDiffeomorph_inr` are stated at a
smoothness `n : ℕ∞`, so at `n = 1` their smoothness is the cast of `1 : ℕ∞`; the orientation API
needs it nonzero. -/
private local instance : NeZero ((1 : ℕ∞) : WithTop ℕ∞) := ⟨one_ne_zero⟩

variable (o₁ : Manifold.Orientation I M ι) (o₂ : Manifold.Orientation I N ι)
  (oE : Manifold.Orientation 𝓘(ℝ, E) E ι)

/-- **The gluing preserves orientation.** If `e₁` preserves and `e₂` reverses orientation from
`oE`, then at glued points `e₁ v` and `e₂ (inversion 0 1 v)` the inclusions of the punctured
summands into the connected sum carry `o₁` and `o₂` to the same tangent orientation. -/
private theorem map_orientationAt_inl_eq_inr
    (he₁ : ∀ v ≠ 0, IsOrientationPreservingAt oE o₁ e₁ v)
    (he₂ : ∀ v ≠ 0, IsOrientationReversingAt oE o₂ e₂ v) (x : puncture e₁) (y : puncture e₂)
    (hxy : inl e₁ e₂ x = inr e₁ e₂ y) :
    letI := chartedSpace (H := H) h₁ h₂
    _root_.Orientation.map ι ((isLocalDiffeomorph_inl h₁ h₂ d₁ d₂ x).mfderivToContinuousLinearEquiv
        one_ne_zero).toLinearEquiv ((o₁.restrict (puncture e₁)).orientationAt x) =
      _root_.Orientation.map ι ((isLocalDiffeomorph_inr h₁ h₂ d₁ d₂
        y).mfderivToContinuousLinearEquiv one_ne_zero).toLinearEquiv
        ((o₂.restrict (puncture e₂)).orientationAt y) := by
  let := chartedSpace (H := H) h₁ h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  rw [← mk_inl, ← mk_inr, mk_eq_mk_iff h₁.injective h₂.injective] at hxy
  obtain ⟨v, hv, rfl, rfl⟩ :=
    rel_inl_inr.1 ((hxy.resolve_left Sum.inl_ne_inr).resolve_right not_rel_inr_inl)
  -- Both are read off the punctured space `E ∖ {0}`, mapped into the two punctured summands by
  -- `ρ₁ = e₁` and `ρ₂ = e₂ ∘ inversion 0 1`, whose composites with the quotient map agree.
  let P := puncture (id : E → E)
  have hP (w : P) : (w : E) ≠ 0 := mem_puncture.1 w.2
  let ρ₁ : P → puncture e₁ := fun w ↦ ⟨e₁ w, mem_puncture.2 (h₁.injective.ne (hP w))⟩
  let ρ₂ : P → puncture e₂ := fun w ↦
    ⟨e₂ (inversion 0 1 w), apply_inversion_mem_puncture h₂.injective (hP w)⟩
  have hρ : inl e₁ e₂ ∘ ρ₁ = inr e₁ e₂ ∘ ρ₂ :=
    funext fun w ↦ by
      simpa only [comp_apply, mk_inl, mk_inr] using inl_eq_inr (e₁ := e₁) (e₂ := e₂) (w : E) (hP w)
        (ρ₁ w).2 (ρ₂ w).2
  let oP := oE.restrict P
  let w₀ : P := ⟨v, mem_puncture.2 hv⟩
  have hv' : inversion (0 : E) 1 v ≠ 0 := by simpa [inversion_eq_center one_ne_zero] using hv
  -- `ρ₁` and `ρ₂` are differentiable at `w₀` and preserve orientation from `oP`.
  have hinv : ContMDiffAt 𝓘(ℝ, E) 𝓘(ℝ, E) 1 (inversion (0 : E) 1 ∘ Subtype.val) w₀ :=
    (contDiffAt_const.inversion contDiffAt_const contDiffAt_id hv).contMDiffAt.comp w₀
      contMDiff_subtype_val.contMDiffAt
  have hρ₁d : MDifferentiableAt 𝓘(ℝ, E) I ρ₁ w₀ :=
    ((ContMDiffAt.subtypeVal_comp_iff (puncture e₁) ρ₁ w₀).mp
      (d₁.contMDiff.comp contMDiff_subtype_val).contMDiffAt).mdifferentiableAt one_ne_zero
  have hρ₂d : MDifferentiableAt 𝓘(ℝ, E) I ρ₂ w₀ :=
    ((ContMDiffAt.subtypeVal_comp_iff (puncture e₂) ρ₂ w₀).mp
      (d₂.contMDiff.contMDiffAt.comp w₀ hinv)).mdifferentiableAt one_ne_zero
  have hval₁ : IsOrientationPreservingAt oP o₁ (e₁ ∘ Subtype.val) w₀ :=
    (he₁ v hv).comp (isOrientationPreservingAt_restrict oE P w₀)
  have hval₂ : IsOrientationPreservingAt oP o₂ ((e₂ ∘ inversion 0 1) ∘ Subtype.val) w₀ :=
    ((he₂ _ hv').comp (isOrientationReversingAt_inversion oE one_ne_zero hv)).comp
      (isOrientationPreservingAt_restrict oE P w₀)
  have hρ₁ : IsOrientationPreservingAt oP (o₁.restrict (puncture e₁)) ρ₁ w₀ :=
    (isOrientationPreservingAt_restrict o₁ _ (ρ₁ w₀)).of_comp hval₁ hρ₁d
  have hρ₂ : IsOrientationPreservingAt oP (o₂.restrict (puncture e₂)) ρ₂ w₀ :=
    (isOrientationPreservingAt_restrict o₂ _ (ρ₂ w₀)).of_comp hval₂ hρ₂d
  -- The two transports of `oP` agree, being derivatives of the same map `P → M # N`. The lemma is
  -- elaborated before its type is matched with the goal, which names `ρ₁ w₀` and `ρ₂ w₀` unfolded.
  exact (map_orientationAt_eq_of_comp_eventuallyEq (isLocalDiffeomorph_inl h₁ h₂ d₁ d₂)
    (isLocalDiffeomorph_inr h₁ h₂ d₁ d₂) hρ₁ hρ₂ hρ₁d hρ₂d (.of_eq hρ) :)

/-- **The orientation of the connected sum.** Let `o₁` and `o₂` be orientations of `M` and `N`,
and let the balls `e₁` and `e₂` induce opposite orientations of `E`: `e₁` preserves and `e₂`
reverses orientation from an orientation `oE` of `E`, away from the centre. Then the connected sum
`M # N` carries the orientation which agrees with `o₁` on `M ∖ {e₁ 0}` and with `o₂` on
`N ∖ {e₂ 0}` (`TauCeti.ConnectedSum.isOrientationPreservingAt_inl`,
`TauCeti.ConnectedSum.isOrientationPreservingAt_inr`). The two agree on the glued punctured balls
because the inversion `v ↦ v / ‖v‖²` reverses orientation. -/
def orientation (he₁ : ∀ v ≠ 0, IsOrientationPreservingAt oE o₁ e₁ v)
    (he₂ : ∀ v ≠ 0, IsOrientationReversingAt oE o₂ e₂ v) :
    letI := chartedSpace (H := H) h₁ h₂
    Manifold.Orientation I (ConnectedSum e₁ e₂) ι :=
  letI := chartedSpace (H := H) h₁ h₂
  haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
  glue (isLocalDiffeomorph_inl h₁ h₂ d₁ d₂) (isLocalDiffeomorph_inr h₁ h₂ d₁ d₂)
    (inl_injective h₁.injective h₂.injective) (inr_injective h₁.injective h₂.injective)
    (range_inl_union_range_inr e₁ e₂) (map_orientationAt_inl_eq_inr h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂)

variable {o₁ o₂ oE} (he₁ : ∀ v ≠ 0, IsOrientationPreservingAt oE o₁ e₁ v)
  (he₂ : ∀ v ≠ 0, IsOrientationReversingAt oE o₂ e₂ v)

/-- The inclusion of the punctured first summand `M ∖ {e₁ 0}` into the connected sum preserves
orientation at `x`, from any orientation `o` of `M ∖ {e₁ 0}` which agrees with `o₁` at `x`: that
is, for which the inclusion into `M` preserves orientation at `x`. -/
theorem isOrientationPreservingAt_inl {o : Manifold.Orientation I (puncture e₁) ι}
    {x : puncture e₁} (ho : IsOrientationPreservingAt o o₁ Subtype.val x) :
    letI := chartedSpace (H := H) h₁ h₂
    haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
    IsOrientationPreservingAt o (orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂) (inl e₁ e₂) x := by
  let := chartedSpace (H := H) h₁ h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  -- At `x`, `o` agrees with the restriction of `o₁`, since both are carried to `o₁` by the
  -- derivative of the inclusion.
  obtain ⟨D, hD, hDo⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 ho
  have hx : o.orientationAt x = (o₁.restrict (puncture e₁)).orientationAt x :=
    (_root_.Orientation.map ι D.toLinearEquiv).injective <| hDo.trans
      ((isOrientationPreservingAt_iff_of_coe_eq _ _ _ x D hD).1
        (isOrientationPreservingAt_restrict o₁ _ x)).symm
  obtain ⟨D', hD', hD'o⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 <|
    isOrientationPreservingAt_glue_left (isLocalDiffeomorph_inl h₁ h₂ d₁ d₂)
    (isLocalDiffeomorph_inr h₁ h₂ d₁ d₂) (inl_injective h₁.injective h₂.injective)
    (inr_injective h₁.injective h₂.injective) (range_inl_union_range_inr e₁ e₂)
    (map_orientationAt_inl_eq_inr h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂) x
  exact (isOrientationPreservingAt_iff _ _ _ _).2 ⟨D', hD', hx ▸ hD'o⟩

/-- The inclusion of the punctured second summand `N ∖ {e₂ 0}` into the connected sum preserves
orientation at `y`, from any orientation `o` of `N ∖ {e₂ 0}` which agrees with `o₂` at `y`: that
is, for which the inclusion into `N` preserves orientation at `y`. -/
theorem isOrientationPreservingAt_inr {o : Manifold.Orientation I (puncture e₂) ι}
    {y : puncture e₂} (ho : IsOrientationPreservingAt o o₂ Subtype.val y) :
    letI := chartedSpace (H := H) h₁ h₂
    haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
    IsOrientationPreservingAt o (orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂) (inr e₁ e₂) y := by
  let := chartedSpace (H := H) h₁ h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  -- At `y`, `o` agrees with the restriction of `o₂`, since both are carried to `o₂` by the
  -- derivative of the inclusion.
  obtain ⟨D, hD, hDo⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 ho
  have hy : o.orientationAt y = (o₂.restrict (puncture e₂)).orientationAt y :=
    (_root_.Orientation.map ι D.toLinearEquiv).injective <| hDo.trans
      ((isOrientationPreservingAt_iff_of_coe_eq _ _ _ y D hD).1
        (isOrientationPreservingAt_restrict o₂ _ y)).symm
  obtain ⟨D', hD', hD'o⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 <|
    isOrientationPreservingAt_glue_right (isLocalDiffeomorph_inl h₁ h₂ d₁ d₂)
    (isLocalDiffeomorph_inr h₁ h₂ d₁ d₂) (inl_injective h₁.injective h₂.injective)
    (inr_injective h₁.injective h₂.injective) (range_inl_union_range_inr e₁ e₂)
    (map_orientationAt_inl_eq_inr h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂) y
  exact (isOrientationPreservingAt_iff _ _ _ _).2 ⟨D', hD', hy ▸ hD'o⟩

/-- **The orientation of the connected sum is characterized by its summands.** For orientations
`o₁'` of `M ∖ {e₁ 0}` and `o₂'` of `N ∖ {e₂ 0}` restricting `o₁` and `o₂`, an orientation of the
connected sum is `TauCeti.ConnectedSum.orientation` exactly when the inclusions of the two punctured
summands preserve orientation from `o₁'` and `o₂'`. -/
theorem eq_orientation_iff {o₁' : Manifold.Orientation I (puncture e₁) ι}
    {o₂' : Manifold.Orientation I (puncture e₂) ι}
    (ho₁ : ∀ x, IsOrientationPreservingAt o₁' o₁ Subtype.val x)
    (ho₂ : ∀ y, IsOrientationPreservingAt o₂' o₂ Subtype.val y)
    {o : letI := chartedSpace (H := H) h₁ h₂; Manifold.Orientation I (ConnectedSum e₁ e₂) ι} :
    letI := chartedSpace (H := H) h₁ h₂
    haveI := isManifold (n := 1) h₁ h₂ d₁ d₂
    o = orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂ ↔
      (∀ x, IsOrientationPreservingAt o₁' o (inl e₁ e₂) x) ∧
        ∀ y, IsOrientationPreservingAt o₂' o (inr e₁ e₂) y := by
  let := chartedSpace (H := H) h₁ h₂
  have := isManifold (n := 1) h₁ h₂ d₁ d₂
  refine ⟨?_, fun ⟨hl, hr⟩ ↦ ?_⟩
  · rintro rfl
    exact ⟨fun x ↦ isOrientationPreservingAt_inl h₁ h₂ d₁ d₂ he₁ he₂ (ho₁ x),
      fun y ↦ isOrientationPreservingAt_inr h₁ h₂ d₁ d₂ he₁ he₂ (ho₂ y)⟩
  ext b
  obtain ⟨x, rfl⟩ | ⟨y, rfl⟩ := (range_inl_union_range_inr e₁ e₂).symm ▸ mem_univ b
  · exact (hl x).orientationAt_eq (isOrientationPreservingAt_inl h₁ h₂ d₁ d₂ he₁ he₂ (ho₁ x))
  · exact (hr y).orientationAt_eq (isOrientationPreservingAt_inr h₁ h₂ d₁ d₂ he₁ he₂ (ho₂ y))

include d₁ d₂ in
/-- **The connected sum of oriented manifolds is orientable**, when the balls induce opposite
orientations of `E`. -/
theorem orientable {o₁ : Manifold.Orientation I M (Fin (finrank ℝ E))}
    {o₂ : Manifold.Orientation I N (Fin (finrank ℝ E))}
    {oE : Manifold.Orientation 𝓘(ℝ, E) E (Fin (finrank ℝ E))}
    (he₁ : ∀ v ≠ 0, IsOrientationPreservingAt oE o₁ e₁ v)
    (he₂ : ∀ v ≠ 0, IsOrientationReversingAt oE o₂ e₂ v) :
    letI := chartedSpace (H := H) h₁ h₂
    Orientable I (ConnectedSum e₁ e₂) :=
  letI := chartedSpace (H := H) h₁ h₂
  ⟨⟨orientation h₁ h₂ d₁ d₂ o₁ o₂ oE he₁ he₂⟩⟩

end TauCeti.ConnectedSum
