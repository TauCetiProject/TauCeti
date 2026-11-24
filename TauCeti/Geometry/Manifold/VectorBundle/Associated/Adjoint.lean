/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.Adjoint.Module
public import TauCeti.Geometry.Manifold.VectorBundle.Associated.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Associated.BilinMap
public import Mathlib.Algebra.Lie.Abelian
import Mathlib.Analysis.Calculus.ContDiff.Basic
import TauCeti.Geometry.Lie.Subgroup.Commutative
import TauCeti.Topology.Algebra.Lie.Bracket

/-!
# The adjoint bundle of a principal bundle

Let `P` be a principal bundle over `B` whose structure group is a real Lie group `G` with Lie
algebra `𝔤`. Its **adjoint bundle** `ad(P) = P ×_G 𝔤` (`TauCeti.AdjointBundle I G P`) is the vector
bundle associated with the adjoint action of `G` on `𝔤`
(`TauCeti.Lie.AdjointModule I G`): its points over `b` are the classes `[p, X]` of a point `p` of
the fibre of `P` over `b` and of `X ∈ 𝔤`, with `[p • g, X] = [p, Ad_g X]`. Connection forms
differ by `ad(P)`-valued one-forms and curvature forms are `ad(P)`-valued two-forms, so this is the
bundle in which the gauge theory of `P` takes values.

Since `G` acts on `𝔤` by Lie algebra automorphisms, the bracket of `𝔤` read in any principal frame
does not depend on the frame. So every fibre of `ad(P)` is a Lie algebra, with
`⁅[p, X], [p, Y]⁆ = [p, ⁅X, Y⁆]` (`TauCeti.AdjointBundle.lie_mk`), and every associated chart is a
Lie algebra isomorphism onto `𝔤` (`TauCeti.AdjointBundle.trivializationAt_lie_snd`). The pointwise
bracket of two smooth sections of `ad(P)` is smooth (`ContMDiff.lie_adjointBundle`). For a
commutative Lie group the adjoint action is trivial, so the class `[p, X]` does not depend on the
frame `p` (`TauCeti.AdjointBundle.mk_eq_mk_of_isMulCommutative`), and the bracket of `ad(P)`
vanishes (`TauCeti.AdjointBundle.instIsLieAbelian`).

An `Ad`-invariant bilinear form `β` on `𝔤`, such as minus the Killing form of a compact semisimple
group, induces a fibre pairing on `ad(P)`, `β_b ([p, X], [p, Y]) = β (X, Y)`. This is the
general construction `TauCeti.AssociatedBundle.bilinMap` for the invariant bilinear maps on an
associated bundle: it is nondegenerate when `β` is
(`TauCeti.AssociatedBundle.nondegenerate_bilinMap_iff`), commutes with pullback
(`TauCeti.AssociatedBundle.bilinMap_pullbackEquiv`) and pairs smooth sections to smooth functions
(`ContMDiff.bilinMap_associatedBundle`). It is `ad`-invariant on each fibre,
`β_b (⁅x, y⁆, z) = -β_b (y, ⁅x, z⁆)` (`TauCeti.AdjointBundle.bilinMap_lie_eq_neg_bilinMap_lie`).

## References

* S. Kobayashi and K. Nomizu, *Foundations of Differential Geometry*, volume I, Chapter II, §5.
* D. S. Freed and K. K. Uhlenbeck, *Instantons and Four-Manifolds*, second edition, Springer,
  1991, Appendix A.
-/

public section

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace TauCeti

variable {n : ℕ∞ω} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I ∞ G]
  {B : Type*} [TopologicalSpace B]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]

open Lie

variable (I G P) in
/-- The **adjoint bundle** `ad(P) = P ×_G 𝔤` of a principal `G`-bundle `P`: the bundle associated
with the adjoint action of `G` on its Lie algebra `𝔤`. Its fibres are Lie algebras
(`TauCeti.AdjointBundle.lie_mk`). -/
abbrev AdjointBundle : B → Type _ :=
  AssociatedBundle G P (AdjointModule I G)

namespace AdjointBundle

open AssociatedBundle

/-! ### The fibrewise Lie algebra structure -/

/-- Each fibre of the adjoint bundle is a Lie ring, with the bracket of `𝔤` read in any principal
frame (`TauCeti.AdjointBundle.lie_mk`). -/
instance instLieRing (b : B) : LieRing (AdjointBundle I G P b) :=
  -- The fibre is a type synonym of `𝔤`, with the additive structure of `𝔤`.
  inferInstanceAs (LieRing (AdjointModule I G))

instance instLieAlgebra (b : B) : LieAlgebra ℝ (AdjointBundle I G P b) :=
  inferInstanceAs (LieAlgebra ℝ (AdjointModule I G))

/-- **The bracket of the adjoint bundle in a principal frame**: `⁅[p, X], [p, Y]⁆ = [p, ⁅X, Y⁆]`
for every point `p` of the principal bundle. -/
@[simp]
theorem lie_mk {b : B} (p : P b) (X Y : AdjointModule I G) :
    ⁅mk G p X, mk G p Y⁆ = mk G p ⁅X, Y⁆ := by
  rw [mk_def, mk_def, mk_def]
  -- In the preferred chart at `b`, the classes have coordinates `g • X`, `g • Y` and
  -- `g • ⁅X, Y⁆`, and the fibre bracket is the bracket of `𝔤`.
  exact (AdjointModule.smul_lie _ X Y).symm

/-- **Associated charts preserve the bracket**: on its base set, the chart at `i` sends the
bracket of two points of a fibre to the bracket of their coordinates. -/
theorem trivializationAt_lie_snd {i b : B} (hb : b ∈ (trivializationAt G P i).baseSet)
    (x y : AdjointBundle I G P b) :
    (trivializationAt (AdjointModule I G) (AdjointBundle I G P) i ⟨b, ⁅x, y⁆⟩).2 =
      ⁅(trivializationAt (AdjointModule I G) (AdjointBundle I G P) i ⟨b, x⟩).2,
        (trivializationAt (AdjointModule I G) (AdjointBundle I G P) i ⟨b, y⟩).2⁆ := by
  obtain ⟨p, X, rfl⟩ := exists_mk x
  obtain ⟨Y, rfl⟩ := (mk_bijective (G := G) (F := AdjointModule I G) p).2 y
  rw [lie_mk, trivializationAt_mk_snd hb, trivializationAt_mk_snd hb, trivializationAt_mk_snd hb,
    AdjointModule.smul_lie]

omit [CompleteSpace E] in
/-- For a commutative structure group the adjoint action is trivial, so the class `[p, X]` in the
adjoint bundle does not depend on the frame `p`. -/
theorem mk_eq_mk_of_isMulCommutative [IsMulCommutative G] {b : B} (p q : P b)
    (X : AdjointModule I G) : mk G p X = mk G q X := by
  rw [mk_eq_mk_iff, AdjointModule.smul_eq_self]

/-- For a commutative structure group, the fibres of the adjoint bundle are abelian Lie
algebras, since the Lie algebra of a commutative Lie group is abelian
(`TauCeti.Lie.isLieAbelian_groupLieAlgebra_of_isMulCommutative`). -/
instance instIsLieAbelian [FiniteDimensional ℝ E] [IsMulCommutative G] (b : B) :
    IsLieAbelian (AdjointBundle I G P b) := by
  have : T2Space G := I.t2Space_of_lieGroup ∞
  have : BoundarylessManifold I G := ContMDiffMul.boundarylessManifold
  have : LieGroup I (minSmoothness ℝ 3) G := LieGroup.minSmoothness_of_isRCLikeNormedField
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨p, X, rfl⟩ := exists_mk x
  obtain ⟨Y, rfl⟩ := (mk_bijective (G := G) (F := AdjointModule I G) p).2 y
  obtain ⟨X, rfl⟩ := AdjointModule.of.surjective X
  obtain ⟨Y, rfl⟩ := AdjointModule.of.surjective Y
  rw [lie_mk, ← AdjointModule.of_lie, trivial_lie_zero, map_zero, mk_zero]

/-! ### Invariant pairings -/

/-- **The pairing induced by an `Ad`-invariant form is `ad`-invariant on each fibre**:
`β_b (⁅x, y⁆, z) = -β_b (y, ⁅x, z⁆)`. An `Ad`-invariant bilinear form on `𝔤` is invariant under
the bracket (`TauCeti.Lie.AdjointModule.lieInvariant_of_smul_invariant`), and the induced pairing
reads it in a principal frame. -/
theorem bilinMap_lie_eq_neg_bilinMap_lie [FiniteDimensional ℝ E]
    {β : AdjointModule I G →L[ℝ] AdjointModule I G →L[ℝ] ℝ}
    (hβ : ∀ (g : G) (X Y : AdjointModule I G), β (g • X) (g • Y) = β X Y) {b : B}
    (x y z : AdjointBundle I G P b) :
    bilinMap G P β b ⁅x, y⁆ z = -bilinMap G P β b y ⁅x, z⁆ := by
  have hlie := AdjointModule.lieInvariant_of_smul_invariant hβ
  obtain ⟨p, X, rfl⟩ := exists_mk x
  obtain ⟨Y, rfl⟩ := (mk_bijective (G := G) (F := AdjointModule I G) p).2 y
  obtain ⟨Z, rfl⟩ := (mk_bijective (G := G) (F := AdjointModule I G) p).2 z
  rw [lie_mk, lie_mk, bilinMap_mk hβ, bilinMap_mk hβ]
  simpa only [ContinuousLinearMap.toBilinForm_apply] using hlie X Y Z

end AdjointBundle

/-! ### Smoothness of the bracket -/

section Smooth

variable [FiniteDimensional ℝ E]
  {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B]
  {EM HM M : Type*} [NormedAddCommGroup EM] [NormedSpace ℝ EM]
  [TopologicalSpace HM] {IM : ModelWithCorners ℝ EM HM}
  [TopologicalSpace M] [ChartedSpace HM M]
  {b : M → B} {v w : ∀ m, AdjointBundle I G P (b m)} {s : Set M} {x : M}

/-- **The bracket of smooth maps into the adjoint bundle is smooth**, within a set: the pointwise
bracket of two maps into `ad(P)` over a common base map, smooth within `s` at `x`, is smooth within
`s` at `x`. -/
theorem _root_.ContMDiffWithinAt.lie_adjointBundle
    (hv : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P))) s x)
    (hw : ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P))) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, ⁅v m, w m⁆⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P))) s x := by
  refine contMDiffWithinAt_totalSpace_iff.mpr ⟨(contMDiffWithinAt_totalSpace_iff.mp hv).1, ?_⟩
  -- Near `x`, the coordinate of the bracket is the bracket of the coordinates.
  exact AssociatedBundle.contMDiffWithinAt_of_trivializationAt
    (lieL ℝ (AdjointModule I G) (AdjointModule I G)).isBoundedBilinearMap.contDiff hv hw
    fun y hy ↦ by rw [lieL_apply]; exact AdjointBundle.trivializationAt_lie_snd hy (v y) (w y)

/-- The bracket of maps into the adjoint bundle smooth at a point is smooth there. -/
theorem _root_.ContMDiffAt.lie_adjointBundle
    (hv : ContMDiffAt IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P))) x)
    (hw : ContMDiffAt IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P))) x) :
    ContMDiffAt IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, ⁅v m, w m⁆⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P))) x := by
  rw [← contMDiffWithinAt_univ] at *
  exact hv.lie_adjointBundle hw

/-- The bracket of maps into the adjoint bundle smooth on a set is smooth there. -/
theorem _root_.ContMDiffOn.lie_adjointBundle
    (hv : ContMDiffOn IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P))) s)
    (hw : ContMDiffOn IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P))) s) :
    ContMDiffOn IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, ⁅v m, w m⁆⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P))) s :=
  fun x hx ↦ (hv x hx).lie_adjointBundle (hw x hx)

/-- **The pointwise bracket of two smooth maps into the adjoint bundle is smooth.** In particular
the smooth sections of `ad(P)` are closed under the pointwise bracket. -/
theorem _root_.ContMDiff.lie_adjointBundle
    (hv : ContMDiff IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, v m⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P))))
    (hw : ContMDiff IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, w m⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P)))) :
    ContMDiff IM (IB.prod 𝓘(ℝ, AdjointModule I G)) n
      (fun m ↦ (⟨b m, ⁅v m, w m⁆⟩ : TotalSpace (AdjointModule I G) (AdjointBundle I G P))) :=
  fun x ↦ (hv x).lie_adjointBundle (hw x)

end Smooth

end TauCeti
