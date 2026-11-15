/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.FiberBundle.Associated.Basic
public import TauCeti.Topology.FiberBundle.Associated.Map

/-!
# Smooth maps of associated bundles

An equivariant `C^n` map of model fibres induces a `C^n` map of associated bundles.
The induced map is expressed in the existing charts through the fibre, without choosing
new bundle structures. In particular, smooth representation intertwiners descend to smooth
maps of associated bundles. The statements also cover nonlinear maps and finite regularity.

## References

* I. Kolář, P. W. Michor, J. Slovák, *Natural Operations in Differential Geometry*, Springer,
  1993, §§10.7 and 10.9.
-/

public section

open Bundle MulOpposite Set TauCeti TauCeti.AssociatedBundle
open scoped Manifold Topology ContDiff

variable {n : ℕ∞ω} {𝕜 B G F F' M : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] {HB : Type*} [TopologicalSpace HB]
  {IB : ModelWithCorners 𝕜 EB HB} [TopologicalSpace B] [ChartedSpace HB B]
  [Group G] [TopologicalSpace G]
  {EF : Type*} [NormedAddCommGroup EF] [NormedSpace 𝕜 EF] {HF : Type*} [TopologicalSpace HF]
  {IF : ModelWithCorners 𝕜 EF HF} [TopologicalSpace F] [ChartedSpace HF F]
  [MulAction G F] [ContinuousSMul G F]
  {EF' : Type*} [NormedAddCommGroup EF'] [NormedSpace 𝕜 EF']
  {HF' : Type*} [TopologicalSpace HF'] {IF' : ModelWithCorners 𝕜 EF' HF'}
  [TopologicalSpace F'] [ChartedSpace HF' F'] [MulAction G F'] [ContinuousSMul G F']
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {P : B → Type*} [TopologicalSpace (TotalSpace G P)] [∀ b, TopologicalSpace (P b)]
  [FiberBundle G P] [∀ b, MulAction Gᵐᵒᵖ (P b)] [PrincipalBundle G P]
  {y : M → TotalSpace F (AssociatedBundle G P F)} {s : Set M} {x₀ : M}

/-- Applying a `C^n` equivariant fibre map preserves `C^n` families within a set at a point. -/
theorem ContMDiffWithinAt.associatedBundleTotalSpaceMap (f : F →[G] F')
    (hf : ContMDiffAt IF IF' n f
      (trivializationAt F (AssociatedBundle G P F) (y x₀).proj (y x₀)).2)
    (hy : ContMDiffWithinAt IM (IB.prod IF) n
      (fun x ↦ ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F) (y x)) s x₀) :
    ContMDiffWithinAt IM (IB.prod IF') n
      (fun x ↦ ManifoldTotalSpace.homeomorph F' (AssociatedBundle G P F')
        (totalSpaceMap f (y x))) s x₀ := by
  rw [ManifoldTotalSpace.contMDiffWithinAt_iff] at hy ⊢
  simp only [totalSpaceMap_proj]
  refine ⟨hy.1, ?_⟩
  have hx₀ := mem_baseSet_trivializationAt G P (y x₀).proj
  have hcoord := hf.comp_contMDiffWithinAt x₀ hy.2
  refine hcoord.congr_of_eventuallyEq ?_
    (congrArg Prod.snd (trivializationAt_totalSpaceMap f hx₀ (y x₀).2))
  filter_upwards [hy.1.continuousWithinAt
    ((trivializationAt G P (y x₀).proj).open_baseSet.mem_nhds hx₀)] with x hx
  exact congrArg Prod.snd (trivializationAt_totalSpaceMap f hx (y x).2)

/-- Applying a `C^n` equivariant fibre map preserves families `C^n` at a point. -/
theorem ContMDiffAt.associatedBundleTotalSpaceMap (f : F →[G] F')
    (hf : ContMDiffAt IF IF' n f
      (trivializationAt F (AssociatedBundle G P F) (y x₀).proj (y x₀)).2)
    (hy : ContMDiffAt IM (IB.prod IF) n
      (fun x ↦ ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F) (y x)) x₀) :
    ContMDiffAt IM (IB.prod IF') n
      (fun x ↦ ManifoldTotalSpace.homeomorph F' (AssociatedBundle G P F')
        (totalSpaceMap f (y x))) x₀ :=
  ContMDiffWithinAt.associatedBundleTotalSpaceMap f hf hy

/-- Applying a `C^n` equivariant fibre map preserves families `C^n` on a set. -/
theorem ContMDiffOn.associatedBundleTotalSpaceMap (f : F →[G] F') (hf : ContMDiff IF IF' n f)
    (hy : ContMDiffOn IM (IB.prod IF) n
      (fun x ↦ ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F) (y x)) s) :
    ContMDiffOn IM (IB.prod IF') n
      (fun x ↦ ManifoldTotalSpace.homeomorph F' (AssociatedBundle G P F')
        (totalSpaceMap f (y x))) s :=
  fun x hx ↦ (hy x hx).associatedBundleTotalSpaceMap f (hf _)

/-- Applying a `C^n` equivariant fibre map preserves `C^n` families. -/
theorem ContMDiff.associatedBundleTotalSpaceMap (f : F →[G] F') (hf : ContMDiff IF IF' n f)
    (hy : ContMDiff IM (IB.prod IF) n
      (fun x ↦ ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F) (y x))) :
    ContMDiff IM (IB.prod IF') n
      (fun x ↦ ManifoldTotalSpace.homeomorph F' (AssociatedBundle G P F')
        (totalSpaceMap f (y x))) :=
  fun x ↦ ContMDiffAt.associatedBundleTotalSpaceMap f (hf _) (hy x)

namespace TauCeti.AssociatedBundle

-- `ManifoldTotalSpace.fiberwiseMap` requires a common model fibre for source and target.
-- Here the two model fibres may differ, so we transport through their respective homeomorphisms.
/-- The map of associated total spaces induced by a `C^n` equivariant fibre map is `C^n`. -/
theorem contMDiff_totalSpaceMap (f : F →[G] F') (hf : ContMDiff IF IF' n f) :
    ContMDiff (IB.prod IF) (IB.prod IF') n
      (fun v : ManifoldTotalSpace F (AssociatedBundle G P F) ↦
        ManifoldTotalSpace.homeomorph F' (AssociatedBundle G P F')
          (totalSpaceMap f ((ManifoldTotalSpace.homeomorph F (AssociatedBundle G P F)).symm v))) :=
  ContMDiff.associatedBundleTotalSpaceMap f hf
    (contMDiff_id.congr fun v ↦ (ManifoldTotalSpace.homeomorph F _).apply_symm_apply v)

/-- An equivariant diffeomorphism of fibres induces a diffeomorphism of associated bundles. -/
noncomputable def diffeomorph (f : F ≃ₘ^n⟮IF, IF'⟯ F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) :
    ManifoldTotalSpace F (AssociatedBundle G P F) ≃ₘ^n⟮IB.prod IF, IB.prod IF'⟯
      ManifoldTotalSpace F' (AssociatedBundle G P F') where
  toEquiv := ((ManifoldTotalSpace.homeomorph F _).symm.trans
    ((homeomorph (P := P) f.toHomeomorph hf).trans
      (ManifoldTotalSpace.homeomorph F' _))).toEquiv
  contMDiff_toFun := by
    let φ : F →[G] F' := ⟨f.toHomeomorph, hf⟩
    have hφ : ⇑φ = f.toHomeomorph := rfl
    have hφ_smooth : ContMDiff IF IF' n φ := by
      simpa only [hφ, Diffeomorph.coe_toHomeomorph] using f.contMDiff
    refine (contMDiff_totalSpaceMap (P := P) (IB := IB) φ hφ_smooth).congr fun v ↦ ?_
    exact congrArg (ManifoldTotalSpace.homeomorph F' _)
      (homeomorph_apply f.toHomeomorph hf ((ManifoldTotalSpace.homeomorph F _).symm v))
  contMDiff_invFun := by
    let ψ := (⟨f.toHomeomorph, hf⟩ : F →[G] F').inverse
      f.toHomeomorph.symm f.toHomeomorph.left_inv f.toHomeomorph.right_inv
    have hψ : ⇑ψ = f.toHomeomorph.symm := rfl
    have hψ_smooth : ContMDiff IF' IF n ψ := by
      simpa only [hψ, Diffeomorph.coe_toHomeomorph_symm] using f.symm.contMDiff
    refine (contMDiff_totalSpaceMap (P := P) (IB := IB) ψ hψ_smooth).congr fun v ↦ ?_
    exact congrArg (ManifoldTotalSpace.homeomorph F _)
      (homeomorph_symm_apply f.toHomeomorph hf ((ManifoldTotalSpace.homeomorph F' _).symm v))

/-- The induced diffeomorphism is the associated map transported to the manifold type copies. -/
theorem diffeomorph_apply (f : F ≃ₘ^n⟮IF, IF'⟯ F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v)
    (v : ManifoldTotalSpace F (AssociatedBundle G P F)) :
    diffeomorph (IB := IB) (P := P) f hf v =
      ManifoldTotalSpace.homeomorph F' _
        (totalSpaceMap (⟨f, hf⟩ : F →[G] F')
          ((ManifoldTotalSpace.homeomorph F _).symm v)) := by
  exact congrArg (ManifoldTotalSpace.homeomorph F' _)
    (homeomorph_apply f.toHomeomorph hf ((ManifoldTotalSpace.homeomorph F _).symm v))

/-- The induced diffeomorphism sends the class of `(p, v)` to that of `(p, f v)`. -/
@[simp]
theorem diffeomorph_mk (f : F ≃ₘ^n⟮IF, IF'⟯ F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) {b : B} (p : P b) (v : F) :
    diffeomorph (IB := IB) (P := P) f hf
        (ManifoldTotalSpace.homeomorph F _ ⟨b, mk G p v⟩) =
      ManifoldTotalSpace.homeomorph F' _ ⟨b, mk G p (f v)⟩ := by
  have hφ : ⇑(⟨f, hf⟩ : F →[G] F') = f := rfl
  rw [diffeomorph_apply, Homeomorph.symm_apply_apply, totalSpaceMap_mk, hφ]

/-- The inverse induced diffeomorphism applies the inverse fibre map to each class. -/
@[simp]
theorem diffeomorph_symm_mk (f : F ≃ₘ^n⟮IF, IF'⟯ F')
    (hf : ∀ (g : G) v, f (g • v) = g • f v) {b : B} (p : P b) (v : F') :
    (diffeomorph (IB := IB) (P := P) f hf).symm
        (ManifoldTotalSpace.homeomorph F' _ ⟨b, mk G p v⟩) =
      ManifoldTotalSpace.homeomorph F _ ⟨b, mk G p (f.symm v)⟩ := by
  apply (diffeomorph (IB := IB) (P := P) f hf).injective
  simp

end TauCeti.AssociatedBundle
