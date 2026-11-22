/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Biproduct
public import Mathlib.Topology.FiberBundle.Constructions

/-!
# Whitney sums of variable-rank bundle atlases as fibrewise products

`TauCeti.FiniteRankAtlas.whitneySum A D` (in
`TauCeti.Topology.VectorBundle.FiniteRank.Atlas.Biproduct`) is the Whitney sum of two
variable-rank atlases, with rank `A.rank + D.rank : LocallyConstant X ℕ`.

`whitneySumTotalSpaceHomeomorph` identifies `TotalSpace Unit (whitneySum A D).Fiber` with the
fibrewise-product `Bundle.TotalSpace` `TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber)` equipped with
`FiberBundle.Prod.topologicalSpace`, over the identity of `X` and by `whitneySumFiberEquiv`
(`TauCeti.splitCoords`) on every fibre. This yields the two-component continuity characterization
`continuous_whitneySum_iff`. No compactness, separation, nonemptiness, bounded-rank, or
scalar-completeness hypothesis is required.

The fibrewise-product (`×ᵇ`) comparison parallels the constant-rank development for
`TauCeti.FiniteRankBundleCore` in `TauCeti.Topology.VectorBundle.FiniteRank.Biproduct`, lifting
coordinate splitting along `TauCeti.splitCoords` and Mathlib's `FiberBundle.Prod.topologicalSpace`
to variable-rank atlases.

## References

* M. F. Atiyah, *K-Theory*, §1.1–1.2.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, §3.
-/

public section

open Bundle

namespace TauCeti.FiniteRankAtlas

universe u v

variable {𝕜 : Type v} [NontriviallyNormedField 𝕜]
  {X : Type u} [TopologicalSpace X]

/-- The continuous linear equivalence splitting each coordinate fibre of `whitneySum A D` into the
product of the fibres of `A` and `D`. -/
def whitneySumFiberEquiv (A D : FiniteRankAtlas 𝕜 X) (x : X) :
    (whitneySum A D).Fiber x ≃L[𝕜] (A.Fiber ×ᵇ D.Fiber) x :=
  splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)

theorem whitneySumFiberEquiv_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (v : (whitneySum A D).Fiber x) :
    whitneySumFiberEquiv A D x v = splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x) v := (rfl)

theorem whitneySumFiberEquiv_symm_apply (A D : FiniteRankAtlas 𝕜 X) (x : X)
    (w : (A.Fiber ×ᵇ D.Fiber) x) :
    (whitneySumFiberEquiv A D x).symm w =
      (splitCoords (𝕜 := 𝕜) (A.rank x) (D.rank x)).symm w := (rfl)

/-- The reconstructed total space `TotalSpace Unit (whitneySum A D).Fiber` is homeomorphic to the
fibrewise-product total space `TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber)` equipped with
`FiberBundle.Prod.topologicalSpace`, over the identity of `X` and by `whitneySumFiberEquiv` on each
fibre. -/
def whitneySumTotalSpaceHomeomorph (A D : FiniteRankAtlas 𝕜 X) :
    TotalSpace Unit (whitneySum A D).Fiber ≃ₜ
      TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber) where
  toFun p := ⟨p.proj, whitneySumFiberEquiv A D p.proj p.snd⟩
  invFun p := ⟨p.proj, (whitneySumFiberEquiv A D p.proj).symm p.snd⟩
  left_inv p := by
    rcases p with ⟨x, v⟩
    exact congrArg (TotalSpace.mk' Unit x) ((whitneySumFiberEquiv A D x).symm_apply_apply v)
  right_inv p := by
    rcases p with ⟨x, w⟩
    exact congrArg (TotalSpace.mk' (Unit × Unit) x)
      ((whitneySumFiberEquiv A D x).apply_symm_apply w)
  continuous_toFun := by
    rw [(FiberBundle.Prod.isInducing_diag Unit A.Fiber Unit D.Fiber).continuous_iff]
    have h := (continuous_mk_whitneySum_iff (A := A) (D := D) (b := TotalSpace.proj)
      (s := fun p : TotalSpace Unit (whitneySum A D).Fiber => p.snd)).1 continuous_id
    exact h.1.prodMk h.2
  continuous_invFun := by
    have hdiag := (FiberBundle.Prod.isInducing_diag Unit A.Fiber Unit D.Fiber).continuous
    refine (continuous_mk_whitneySum_iff (A := A) (D := D) (b := TotalSpace.proj)
      (s := fun p : TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber) =>
        (whitneySumFiberEquiv A D p.proj).symm p.snd)).2 ⟨?_, ?_⟩
    · refine hdiag.fst.congr fun p => ?_
      exact congrArg (TotalSpace.mk' Unit p.proj)
        (congrArg Prod.fst ((whitneySumFiberEquiv A D p.proj).apply_symm_apply p.snd)).symm
    · refine hdiag.snd.congr fun p => ?_
      exact congrArg (TotalSpace.mk' Unit p.proj)
        (congrArg Prod.snd ((whitneySumFiberEquiv A D p.proj).apply_symm_apply p.snd)).symm

@[simp] theorem whitneySumTotalSpaceHomeomorph_apply (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace Unit (whitneySum A D).Fiber) :
    whitneySumTotalSpaceHomeomorph A D p = ⟨p.proj, whitneySumFiberEquiv A D p.proj p.snd⟩ := (rfl)

@[simp] theorem whitneySumTotalSpaceHomeomorph_symm_apply (A D : FiniteRankAtlas 𝕜 X)
    (p : TotalSpace (Unit × Unit) (A.Fiber ×ᵇ D.Fiber)) :
    (whitneySumTotalSpaceHomeomorph A D).symm p =
      ⟨p.proj, (whitneySumFiberEquiv A D p.proj).symm p.snd⟩ := (rfl)

/-- A map into `TotalSpace Unit (whitneySum A D).Fiber` is continuous if and only if its two
coordinate-block projections into `TotalSpace Unit A.Fiber` and `TotalSpace Unit D.Fiber` are
continuous. -/
theorem continuous_whitneySum_iff {Y : Type*} [TopologicalSpace Y] {A D : FiniteRankAtlas 𝕜 X}
    {f : Y → TotalSpace Unit (whitneySum A D).Fiber} :
    Continuous f ↔
      Continuous (fun y => (⟨(f y).proj, (whitneySumFiberEquiv A D (f y).proj (f y).snd).1⟩ :
        TotalSpace Unit A.Fiber)) ∧
      Continuous (fun y => (⟨(f y).proj, (whitneySumFiberEquiv A D (f y).proj (f y).snd).2⟩ :
        TotalSpace Unit D.Fiber)) := by
  rw [← (whitneySumTotalSpaceHomeomorph A D).comp_continuous_iff,
    (FiberBundle.Prod.isInducing_diag Unit A.Fiber Unit D.Fiber).continuous_iff]
  exact continuous_prodMk

end TauCeti.FiniteRankAtlas
