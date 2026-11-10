/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Basic
public import TauCeti.Topology.FiberBundle.Associated.Pullback

/-!
# Smooth pullback comparison for associated bundles

Associating after pullback and pulling back after associating have the same local fibre
coordinates. Their canonical comparison is therefore a diffeomorphism for the native charts
through the fibre. The family criterion below also applies within arbitrary subsets.

The comparison itself only needs a continuous base map: the two chart systems agree even
before smoothness of their transitions is established. When the principal bundle, action and
base map are smooth, install the theorem `TauCeti.AssociatedBundle.contMDiffFiberBundle`
as a local instance (for example with `haveI`). Together with the instance
`TauCeti.ContMDiffFiberBundle.pullback`, it supplies `C^n` bundle structures on both sides
and hence `C^n` manifold structures on their total spaces. No linearity of the fibre action
is needed.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*,
  §§10.7 and 10.11.
-/

public section

noncomputable section

open Bundle Set TauCeti
open scoped Manifold ContDiff Topology

namespace TauCeti.AssociatedBundle

variable {n : ℕ∞ω} {𝕜 B B' G F M : Type*} [NontriviallyNormedField 𝕜]
  [TopologicalSpace B]
  {EB' : Type*} [NormedAddCommGroup EB'] [NormedSpace 𝕜 EB'] {HB' : Type*} [TopologicalSpace HB']
  {IB' : ModelWithCorners 𝕜 EB' HB'} [TopologicalSpace B'] [ChartedSpace HB' B']
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  [Group G] [TopologicalSpace G] [MulAction G F] [ContinuousSMul G F]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, Nonempty (P b)]
  [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  [∀ b, Nonempty (AssociatedBundle G P F b)]
  {K : Type*} [FunLike K B' B] [ContinuousMapClass K B' B] (f : K)

/-- A family is `C^n` in the associated pullback bundle exactly when its image under the
canonical comparison is `C^n` in the pullback associated bundle. -/
theorem contMDiffWithinAt_pullbackHomeomorph_iff
    {q : M → TotalSpace F (AssociatedBundle G ((f : B' → B) *ᵖ P) F)}
    {s : Set M} {x₀ : M} :
    ContMDiffWithinAt IM (IB'.prod IF) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F _ (q x)) s x₀ ↔
      ContMDiffWithinAt IM (IB'.prod IF) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F _ (pullbackHomeomorph f (q x))) s x₀ := by
  simp only [pullbackHomeomorph_apply, ManifoldTotalSpace.contMDiffWithinAt_iff,
    Pullback.trivializationAt_snd]
  refine and_congr_right fun hbase ↦ ?_
  apply Filter.EventuallyEq.contMDiffWithinAt_iff
  · filter_upwards [(((map_continuous f).continuousAt.comp_continuousWithinAt
      hbase.continuousWithinAt))
      ((trivializationAt G P (f (q x₀).proj)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt G P (f (q x₀).proj)))] with x hx
    exact trivializationAt_pullbackEquiv_snd f hx _
  · exact trivializationAt_pullbackEquiv_snd f
      (mem_baseSet_trivializationAt G P (f (q x₀).proj)) _

/-- A family is `C^n` in the associated pullback bundle exactly when its image under the
canonical comparison is `C^n` in the pullback associated bundle. -/
theorem contMDiff_pullbackHomeomorph_iff
    {q : M → TotalSpace F (AssociatedBundle G ((f : B' → B) *ᵖ P) F)} :
    ContMDiff IM (IB'.prod IF) n (fun x ↦ ManifoldTotalSpace.homeomorph F _ (q x)) ↔
      ContMDiff IM (IB'.prod IF) n
        (fun x ↦ ManifoldTotalSpace.homeomorph F _ (pullbackHomeomorph f (q x))) := by
  simp only [ContMDiff, ← contMDiffWithinAt_univ,
    contMDiffWithinAt_pullbackHomeomorph_iff (IB' := IB') (IF := IF) f]

/-- The canonical pullback homeomorphism is a diffeomorphism in the charts through the fibre. -/
def pullbackDiffeomorph :
    ManifoldTotalSpace F (AssociatedBundle G ((f : B' → B) *ᵖ P) F) ≃ₘ^n⟮IB'.prod IF, IB'.prod IF⟯
      ManifoldTotalSpace F ((f : B' → B) *ᵖ (AssociatedBundle G P F)) where
  toEquiv := ((ManifoldTotalSpace.homeomorph F _).symm.trans
    ((pullbackHomeomorph f).trans (ManifoldTotalSpace.homeomorph F _))).toEquiv
  contMDiff_toFun := (contMDiff_pullbackHomeomorph_iff
    (IB' := IB') (IF := IF) f).mp (contMDiff_id.congr fun y ↦
      (ManifoldTotalSpace.homeomorph F _).apply_symm_apply y)
  contMDiff_invFun := (contMDiff_pullbackHomeomorph_iff
    (IB' := IB') (IF := IF) f).mpr (contMDiff_id.congr fun y ↦
      ((pullbackHomeomorph f).trans (ManifoldTotalSpace.homeomorph F _)).apply_symm_apply y)

/-- The diffeomorphism is the canonical homeomorphism read through the total-space type copies. -/
@[simp]
theorem pullbackDiffeomorph_apply
    (z : TotalSpace F (AssociatedBundle G ((f : B' → B) *ᵖ P) F)) :
    pullbackDiffeomorph (n := n) (IB' := IB') (IF := IF) (G := G) (P := P) f
        (ManifoldTotalSpace.homeomorph F _ z) =
      ManifoldTotalSpace.homeomorph F _ (pullbackHomeomorph f z) := by
  rw [← Diffeomorph.coe_toEquiv]
  simp [pullbackDiffeomorph, Homeomorph.trans_apply]

/-- The inverse diffeomorphism is the inverse canonical homeomorphism in the same charts. -/
@[simp]
theorem pullbackDiffeomorph_symm_apply
    (z : TotalSpace F ((f : B' → B) *ᵖ (AssociatedBundle G P F))) :
    (pullbackDiffeomorph (n := n) (IB' := IB') (IF := IF) (G := G) (P := P) f).symm
        (ManifoldTotalSpace.homeomorph F _ z) =
      ManifoldTotalSpace.homeomorph F _ ((pullbackHomeomorph f).symm z) := by
  apply (pullbackDiffeomorph (n := n) (IB' := IB') (IF := IF) (G := G) (P := P) f).injective
  simp only [Diffeomorph.coe_toEquiv, Diffeomorph.apply_symm_apply,
    pullbackDiffeomorph_apply, Homeomorph.apply_symm_apply]

end TauCeti.AssociatedBundle
