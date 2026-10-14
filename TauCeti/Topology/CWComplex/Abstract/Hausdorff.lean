/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.DisjointOpens
public import TauCeti.Topology.CWComplex.Abstract.ClosedEmbedding
public import TauCeti.Topology.Separation.Sigma

/-!
# Relative CW complexes on Hausdorff spaces are Hausdorff

Mathlib's categorical relative CW complex `c : TopCat.RelativeCWComplex f`, for a morphism
`f : X ⟶ Y` of `TopCat`, presents `Y` as the colimit of a sequence of spaces starting at `X`, each
obtained from the previous one by attaching disks along their boundary spheres. This file proves
that `Y` is Hausdorff when `X` is (`TopCat.RelativeCWComplex.t2Space`); in particular a CW complex
in this sense is Hausdorff (`TopCat.CWComplex.t2Space`). Mathlib's theory of classical CW
complexes assumes a Hausdorff ambient space, so this is needed to read a classical CW structure off
a categorical one.

The proof extends open sets cell by cell. The inclusion of the boundary sphere of a disk extends
disjoint open sets in the sense of `TauCeti.TopCat.extendsDisjointOpens`: an open subset `U` of the
sphere extends to the open cone `{x | 1 / 2 < ‖x‖ ∧ x / ‖x‖ ∈ U}`
(`TauCeti.TopCat.extendsDisjointOpens_diskBoundaryInclusion`). Hence so does every map between
the stages of the complex, and every map from a stage to `Y`. Two points of `Y` lie in a common
stage, so they are separated by open sets once that stage is Hausdorff. A stage obtained by
attaching cells to a Hausdorff space is Hausdorff (`HomotopicalAlgebra.AttachCells.t2Space`): two
points of the old space are separated by extending open sets, and a point of an open cell is
separated from the other points inside the disks, which are regular.

The statements hold for any relative cell complex in `TopCat` whose basic cells are closed
embeddings extending disjoint open sets into regular Hausdorff spaces
(`HomotopicalAlgebra.RelativeCellComplex.t2Space`).

## Implementation notes

The cells attached at each step are indexed by a type in the universe of the spaces, as they are
for `TopCat.RelativeCWComplex`, so that the coproduct of the attached disks is identified with
their disjoint union `Σ i, B i` (`TopCat.sigmaCofanIsColimit`), which is regular by
`Sigma.regularSpace`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Appendix: the neighbourhoods `N_ε(A)` of subsets of a cell complex, built cell by cell by
  radial extension, and Proposition A.3 that cell complexes are normal.
* R. Fritsch and R. Piccinini, *Cellular Structures in Topology*, Cambridge University Press,
  1990, for the categorical definition.
-/

public section

open CategoryTheory Limits MorphismProperty Topology TauCeti.TopCat

universe w' t u

namespace TauCeti.TopCat

/-- The inclusion `∂𝔻 n ⟶ 𝔻 n` of the boundary sphere of the disk extends disjoint open sets: an
open subset `U` of the sphere is the trace of the open cone `{x | 1 / 2 < ‖x‖ ∧ x / ‖x‖ ∈ U}`,
and the cones over disjoint sets are disjoint. -/
theorem extendsDisjointOpens_diskBoundaryInclusion (n : ℕ) :
    extendsDisjointOpens (TopCat.diskBoundaryInclusion.{u} n) := by
  -- The points of the disk and of its boundary as vectors of `E`.
  let ν (z : TopCat.disk.{u} n) : EuclideanSpace ℝ (Fin n) :=
    ((z : ULift.{u} (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
      EuclideanSpace ℝ (Fin n))
  let μ (s : TopCat.diskBoundary.{u} n) : EuclideanSpace ℝ (Fin n) :=
    ((s : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).down :
      EuclideanSpace ℝ (Fin n))
  have hμ : IsEmbedding μ := IsEmbedding.subtypeVal.comp IsEmbedding.uliftDown
  have hνμ (s : TopCat.diskBoundary.{u} n) : ν (TopCat.diskBoundaryInclusion n s) = μ s := rfl
  have hμ₁ (s : TopCat.diskBoundary.{u} n) : ‖μ s‖ = 1 := mem_sphere_zero_iff_norm.1
    (s : ULift.{u} (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) 1)).down.2
  -- The radial projection, continuous away from the centre.
  let N : Set (TopCat.disk.{u} n) := {z | 1 / 2 < ‖ν z‖}
  have hN : IsOpen N :=
    isOpen_lt continuous_const (continuous_subtype_val.comp continuous_uliftDown).norm
  have hρ : ContinuousOn (fun z ↦ ‖ν z‖⁻¹ • ν z) N := by
    have hν : Continuous ν := continuous_subtype_val.comp continuous_uliftDown
    refine (ContinuousOn.inv₀ hν.norm.continuousOn fun z hz ↦ ?_).smul hν.continuousOn
    exact (lt_trans (by norm_num) hz).ne'
  -- An open subset `U` of the sphere extends to an open cone whose points project into `U`.
  have cone (U : Set (TopCat.diskBoundary.{u} n)) (hU : IsOpen U) :
      ∃ U' : Set (TopCat.disk.{u} n), IsOpen U' ∧ TopCat.diskBoundaryInclusion n ⁻¹' U' = U ∧
        ∀ z ∈ U', ∃ s ∈ U, μ s = ‖ν z‖⁻¹ • ν z := by
    obtain ⟨Ũ, hŨ, rfl⟩ := hμ.isInducing.isOpen_iff.1 hU
    refine ⟨N ∩ (fun z ↦ ‖ν z‖⁻¹ • ν z) ⁻¹' Ũ, hρ.isOpen_inter_preimage hN hŨ, ?_, ?_⟩
    · ext s
      simp [N, hνμ, hμ₁, show (2 : ℝ)⁻¹ < 1 by norm_num]
    · rintro z ⟨hz, hzŨ⟩
      have h₁ : ‖‖ν z‖⁻¹ • ν z‖ = 1 := by
        rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (lt_trans (by norm_num) hz).ne']
      exact ⟨ULift.up ⟨_, mem_sphere_zero_iff_norm.2 h₁⟩, hzŨ, rfl⟩
  rw [extendsDisjointOpens_iff]
  intro U V hU hV hUV
  obtain ⟨U', hU', hU'U, hU'₁⟩ := cone U hU
  obtain ⟨V', hV', hV'V, hV'₁⟩ := cone V hV
  refine ⟨U', V', hU', hV', Set.disjoint_left.2 fun z hzU hzV ↦ ?_, hU'U, hV'V⟩
  obtain ⟨s, hs, hsz⟩ := hU'₁ z hzU
  obtain ⟨s', hs', hs'z⟩ := hV'₁ z hzV
  exact Set.disjoint_left.1 hUV hs (hμ.injective (hsz.trans hs'z.symm) ▸ hs')

end TauCeti.TopCat

namespace HomotopicalAlgebra

variable {α : Type t} {A B : α → TopCat.{u}} {g : ∀ a, A a ⟶ B a} {X₁ X₂ : TopCat.{u}}
  {f : X₁ ⟶ X₂}

/-- Attaching cells to a Hausdorff space gives a Hausdorff space, provided the cells are closed
embeddings into regular Hausdorff spaces which extend disjoint open sets. -/
theorem AttachCells.t2Space (a : AttachCells.{u} g f) [T2Space X₁] [∀ k, T2Space (B k)]
    [∀ k, RegularSpace (B k)] (hg : ∀ i, extendsDisjointOpens (g (a.π i)))
    (hg' : ∀ i, IsClosedEmbedding (g (a.π i))) : T2Space X₂ := by
  -- The space of cells is the disjoint union of the targets of the attached cells.
  let e := TopCat.homeoOfIso
    (a.isColimit₂.coconePointUniqueUpToIso (TopCat.sigmaCofanIsColimit fun i ↦ B (a.π i)))
  -- The carrier of `TopCat.sigmaCofan` is the sigma type, which instance search does not see.
  have : T2Space (TopCat.sigmaCofan fun i ↦ B (a.π i)).pt :=
    inferInstanceAs (T2Space (Σ i, B (a.π i)))
  have : RegularSpace (TopCat.sigmaCofan fun i ↦ B (a.π i)).pt :=
    inferInstanceAs (RegularSpace (Σ i, B (a.π i)))
  have : T2Space a.cofan₂.pt := e.isEmbedding.t2Space
  have : RegularSpace a.cofan₂.pt := e.isEmbedding.isInducing.regularSpace
  have hm : extendsDisjointOpens a.m :=
    IsStableUnderColimitsOfShape.condition _ _ _ _ a.isColimit₁ a.isColimit₂
      (Discrete.natTrans fun i ↦ g (a.π i.as)) (fun i ↦ hg i.as) a.m (fun i ↦ a.hm i.as)
  have hm' : IsClosedEmbedding a.m := (TauCeti.TopCat.isClosedEmbedding_iff _).1 <|
    IsStableUnderColimitsOfShape.condition _ _ _ _ a.isColimit₁ a.isColimit₂
      (Discrete.natTrans fun i ↦ g (a.π i.as))
      (fun i ↦ (TauCeti.TopCat.isClosedEmbedding_iff _).2 (hg' i.as)) a.m (fun i ↦ a.hm i.as)
  exact t2Space_of_isPushout a.isPushout hm hm'.isClosed_range

namespace RelativeCellComplex

variable {J : Type w'} [LinearOrder J] [OrderBot J] [SuccOrder J] [WellFoundedLT J]
  {α : J → Type t} {A B : (j : J) → α j → TopCat.{u}}
  {basicCell : (j : J) → (i : α j) → A j i ⟶ B j i} {X Y : TopCat.{u}} {f : X ⟶ Y}
  (c : RelativeCellComplex.{u} basicCell f)

/-- A relative cell complex `f : X ⟶ Y` in `TopCat` on a Hausdorff space `X` has a Hausdorff
target `Y`, provided its basic cells are closed embeddings into regular Hausdorff spaces which
extend disjoint open sets. -/
theorem t2Space [T2Space X] [∀ j i, T2Space (B j i)] [∀ j i, RegularSpace (B j i)]
    (hc : ∀ s : c.Cells, extendsDisjointOpens (basicCell s.j s.i))
    (hc' : ∀ s : c.Cells, IsClosedEmbedding (basicCell s.j s.i)) : T2Space Y := by
  let h : extendsDisjointOpens.TransfiniteCompositionOfShape J f :=
    (c.transfiniteCompositionOfShape' hc).ofLE (pushouts_le_iff.2 (coproducts_le _))
  have := h.isWellOrderContinuous
  have hF (j : J) : T2Space (c.F.obj j) := by
    induction j using SuccOrder.limitRecOn with
    | isMin j hj =>
      obtain rfl := hj.eq_bot
      exact (TopCat.homeoOfIso c.isoBot).isEmbedding.t2Space
    | succ j hj ih =>
      exact (c.attachCells j hj).t2Space (fun i ↦ hc ⟨j, hj, i⟩) (fun i ↦ hc' ⟨j, hj, i⟩)
    | isSuccLimit j hj ih =>
      have (k : Set.Iio j) : T2Space (((Set.principalSegIio j).monotone.functor ⋙ c.F).obj k) :=
        ih k.1 k.2
      exact t2Space_of_isColimit (c.F.isColimitOfIsWellOrderContinuous j hj)
        fun k ↦ h.mem_map _
  exact t2Space_of_isColimit c.isColimit h.mem_incl_app

end RelativeCellComplex

end HomotopicalAlgebra

namespace TopCat

/-- **A relative CW complex on a Hausdorff space is Hausdorff.** If `f : X ⟶ Y` is a relative CW
complex in Mathlib's categorical sense and `X` is Hausdorff, then so is `Y`. -/
theorem RelativeCWComplex.t2Space {X Y : TopCat.{u}} {f : X ⟶ Y} (c : RelativeCWComplex f)
    [T2Space X] : T2Space Y :=
  HomotopicalAlgebra.RelativeCellComplex.t2Space c
    (fun s ↦ extendsDisjointOpens_diskBoundaryInclusion s.j)
    (fun s ↦ isClosedEmbedding_diskBoundaryInclusion s.j)

/-- **A CW complex is Hausdorff.** -/
theorem CWComplex.t2Space {X : TopCat.{u}} (c : CWComplex X) : T2Space X :=
  have : T2Space (⊥_ TopCat.{u}) :=
    (TopCat.homeoOfIso TopCat.initialIsoPEmpty).isEmbedding.t2Space
  RelativeCWComplex.t2Space c

end TopCat
