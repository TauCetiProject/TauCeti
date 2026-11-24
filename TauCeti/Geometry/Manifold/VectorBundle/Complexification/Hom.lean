/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complexification.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Complexification

/-!
# Smooth complexification of real Hom bundles

`bundleHomComplexificationDiffeomorph` compares the original native total spaces of complexified
real Hom and complex Hom into a complexified real vector bundle. Both directions are smooth and
preserve the base point. `instContMDiffVectorBundleComplexificationHom` proves smoothness of the
existing complex-Hom bundle atlas over a real base from the original real bundle transitions.
There is no finite-rank or completeness assumption on the coefficient model.
-/

public section
noncomputable section
open Bundle FiberBundle Set TauCeti
open scoped TensorProduct ContDiff Manifold Topology
namespace TauCeti



variable {B F G : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  {V L : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace G L)] [FiberBundle G L] [VectorBundle ℝ G L]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] L x)] [∀ x, IsComplexificationTopology (L x)]

variable [∀ x, IsTopologicalAddGroup (L x)] [∀ x, ContinuousSMul ℝ (L x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))]
  [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)]

section Smooth
variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B] {n : ℕ∞ω}

/-- The original-fibre map is jointly smooth without a finite-rank hypothesis. -/
theorem contMDiff_bundleHomComplexificationEquiv :
    ContMDiff (IB.prod 𝓘(ℝ, Complexification (F →L[ℝ] G)))
      (IB.prod 𝓘(ℝ, Complexification F →L[ℂ] Complexification G)) n
      (fun p : TotalSpace (Complexification (F →L[ℝ] G))
        (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ↦
          TotalSpace.mk' (Complexification F →L[ℂ] Complexification G)
            (E := fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) p.proj
            (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) p.proj p.snd)) := by
  apply contMDiff_bundleMap_of_constant_coordinates (IB := IB) (n := n)
    (fun x u ↦ bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x u)
    (A := (Complexification.continuousLinearMapEquiv F G).toContinuousLinearMap.restrictScalars ℝ)
  intro a x hx u
  apply bundleHomComplexificationEquiv_in_trivializationAt (G := G) a x _ u
  simpa only [trivializationAt_complexification, hom_trivializationAt,
    Trivialization.baseSet_complexification, Trivialization.baseSet_continuousLinearMap]
      using hx.1

/-- The inverse coefficient comparison is smooth on the original native total spaces. -/
theorem contMDiff_bundleHomComplexificationEquiv_symm :
    ContMDiff (IB.prod 𝓘(ℝ, Complexification F →L[ℂ] Complexification G))
      (IB.prod 𝓘(ℝ, Complexification (F →L[ℝ] G))) n
      (fun p : TotalSpace (Complexification F →L[ℂ] Complexification G)
        (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) ↦
          TotalSpace.mk' (Complexification (F →L[ℝ] G))
            (E := fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) p.proj
            ((bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) p.proj).symm
              p.snd)) := by
  apply contMDiff_bundleMap_of_constant_coordinates (IB := IB) (n := n)
    (fun x A ↦ (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) x).symm A)
    (A := (Complexification.continuousLinearMapEquiv F
      G).symm.toContinuousLinearMap.restrictScalars ℝ)
  intro a x hx A
  apply bundleHomComplexificationEquiv_symm_in_trivializationAt (G := G) a x _ A
  simpa only [trivializationAt_complexification, hom_trivializationAt,
    Trivialization.baseSet_complexification, Trivialization.baseSet_continuousLinearMap]
      using hx.1

/-- The coefficient comparison is a base-preserving diffeomorphism of native total spaces. -/
def bundleHomComplexificationDiffeomorph :
    TotalSpace (Complexification (F →L[ℝ] G)) (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
      ≃ₘ^n⟮IB.prod 𝓘(ℝ, Complexification (F →L[ℝ] G)),
        IB.prod 𝓘(ℝ, Complexification F →L[ℂ] Complexification G)⟯
      TotalSpace (Complexification F →L[ℂ] Complexification G)
        (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) where
  toFun p :=
    ⟨p.proj, bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) p.proj p.snd⟩
  invFun p := ⟨p.proj, (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L)
    p.proj).symm p.snd⟩
  left_inv p := by simp only [ContinuousLinearEquiv.symm_apply_apply]
  right_inv p := by simp only [ContinuousLinearEquiv.apply_symm_apply]
  contMDiff_toFun := contMDiff_bundleHomComplexificationEquiv
  contMDiff_invFun := contMDiff_bundleHomComplexificationEquiv_symm

/-- Evaluation of the original native total-space comparison. -/
@[simp] theorem bundleHomComplexificationDiffeomorph_apply
    (p : TotalSpace (Complexification (F →L[ℝ] G))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) :
    bundleHomComplexificationDiffeomorph (IB := IB) (n := n) p =
      ⟨p.proj, bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) p.proj p.snd⟩ :=
        by rfl

/-- Evaluation of the inverse on the original native total space. -/
@[simp] theorem bundleHomComplexificationDiffeomorph_symm_apply
    (p : TotalSpace (Complexification F →L[ℂ] Complexification G)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) :
    (bundleHomComplexificationDiffeomorph (IB := IB) (n := n)).symm p =
      ⟨p.proj, (bundleHomComplexificationEquiv (F := F) (G := G) (V := V) (L := L) p.proj).symm
        p.snd⟩ :=
        by rfl

variable [ContMDiffVectorBundle n F V IB] [ContMDiffVectorBundle n G L IB]

/-- Complex Hom between complexifications of a real bundle and a real vector bundle is a
real `C^n` vector bundle with its native Hom atlas. -/
instance instContMDiffVectorBundleComplexificationHom :
    ContMDiffVectorBundle n (Complexification F →L[ℂ] Complexification G)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) IB where
  contMDiffOn_coordChangeL := by
    intro t t' ht ht'
    obtain ⟨e, d, he, hd, rfl⟩ := mem_trivializationAtlas_complexificationHom_iff.mp ht
    obtain ⟨e', d', he', hd', rfl⟩ := mem_trivializationAtlas_complexificationHom_iff.mp ht'
    have : MemTrivializationAtlas e := he
    have : MemTrivializationAtlas d := hd
    have : MemTrivializationAtlas e' := he'
    have : MemTrivializationAtlas d' := hd'
    have hs := contMDiffOn_coordChangeL (IB := IB) (n := n)
      (e.continuousLinearMap (RingHom.id ℝ) d).complexification
      (e'.continuousLinearMap (RingHom.id ℝ) d').complexification
    have h := ContMDiffOn.clm_comp
      (contMDiffOn_const (c := (Complexification.continuousLinearMapEquiv
        F G).toContinuousLinearMap.restrictScalars ℝ))
      (hs.clm_comp
        (contMDiffOn_const (c := (Complexification.continuousLinearMapEquiv
          F G).symm.toContinuousLinearMap.restrictScalars ℝ)))
    simp only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] at h ⊢
    exact h.congr fun x hx ↦ coordChangeL_complexificationHom e e' d d' hx

end Smooth
end TauCeti
