/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Complexification.Hom
public import TauCeti.Geometry.Manifold.VectorBundle.Complexification

/-!
# Smooth complexification of real Hom into a line bundle

`bundleHomComplexificationDiffeomorph` compares the original native total spaces of complexified
real Hom and complex Hom into a complexified real line bundle. Both directions are smooth and
preserve the base point. `contMDiffVectorBundle_complexificationHom` proves smoothness of the
existing complex-Hom bundle atlas over a real base from the original real bundle transitions.
There is no finite-rank or completeness assumption on the coefficient model.
-/

public section
noncomputable section
open Bundle FiberBundle Set TauCeti
open scoped TensorProduct ContDiff Manifold Topology
namespace TauCeti

section ConstantCoordinates

variable {B EB HB F₁ F₂ : Type*} [TopologicalSpace B]
  [NormedAddCommGroup EB] [NormedSpace ℝ EB] [TopologicalSpace HB]
  {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  {E₁ E₂ : B → Type*} [∀ x, TopologicalSpace (E₁ x)] [∀ x, TopologicalSpace (E₂ x)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [FiberBundle F₂ E₂] {n : ℕ∞ω}

private theorem contMDiff_bundleMap_of_constant_coordinates
    (φ : ∀ x, E₁ x → E₂ x) (A : F₁ →L[ℝ] F₂)
    (hφ : ∀ a x, x ∈ (trivializationAt F₁ E₁ a).baseSet ∩
        (trivializationAt F₂ E₂ a).baseSet → ∀ v,
      (trivializationAt F₂ E₂ a ⟨x, φ x v⟩).2 =
        A (trivializationAt F₁ E₁ a ⟨x, v⟩).2) :
    ContMDiff (IB.prod 𝓘(ℝ, F₁)) (IB.prod 𝓘(ℝ, F₂)) n
      (fun p : TotalSpace F₁ E₁ ↦ TotalSpace.mk' F₂ (E := E₂) p.proj (φ p.proj p.2)) := by
  intro p
  rw [Bundle.contMDiffAt_totalSpace_iff]
  refine ⟨contMDiffAt_proj _, ?_⟩
  have hc := (Bundle.contMDiffAt_totalSpace_iff.mp
    (contMDiffAt_id (I := IB.prod 𝓘(ℝ, F₁)) (x := p) (n := n))).2
  have hm := (A.contDiff (n := n)).contMDiff
  refine (hm.contMDiffAt.comp p hc).congr_of_eventuallyEq ?_
  have hb := ((FiberBundle.continuous_proj F₁ E₁).continuousAt).preimage_mem_nhds
    (((trivializationAt F₁ E₁ p.proj).open_baseSet.inter
      (trivializationAt F₂ E₂ p.proj).open_baseSet).mem_nhds
        ⟨mem_baseSet_trivializationAt F₁ E₁ p.proj,
          mem_baseSet_trivializationAt F₂ E₂ p.proj⟩)
  filter_upwards [hb] with q hq
  exact hφ p.proj q.proj hq q.2

end ConstantCoordinates

variable {B F : Type*} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V L : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  [∀ x, AddCommGroup (L x)] [∀ x, Module ℝ (L x)] [∀ x, TopologicalSpace (L x)]
  [TopologicalSpace (TotalSpace ℝ L)] [FiberBundle ℝ L] [VectorBundle ℝ ℝ L]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] V x)] [∀ x, IsComplexificationTopology (V x)]
  [∀ x, TopologicalSpace (ℂ ⊗[ℝ] L x)] [∀ x, IsComplexificationTopology (L x)]

attribute [local instance] instIsTopologicalAddGroupLineBundleFiber
  instContinuousSMulLineBundleFiber

variable [∀ x, TopologicalSpace (ℂ ⊗[ℝ] (V x →L[ℝ] L x))]
  [∀ x, IsComplexificationTopology (V x →L[ℝ] L x)]

section Smooth
variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB} [ChartedSpace HB B] {n : ℕ∞ω}

/-- The original-fibre map is jointly smooth without a finite-rank hypothesis. -/
theorem contMDiff_bundleHomComplexificationEquiv :
    ContMDiff (IB.prod 𝓘(ℝ, Complexification (F →L[ℝ] ℝ)))
      (IB.prod 𝓘(ℝ, Complexification F →L[ℂ] Complexification ℝ)) n
      (fun p : TotalSpace (Complexification (F →L[ℝ] ℝ))
        (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) ↦
          TotalSpace.mk' (Complexification F →L[ℂ] Complexification ℝ)
            (E := fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) p.proj
            (bundleHomComplexificationEquiv (F := F) (V := V) (L := L) p.proj p.2)) := by
  apply contMDiff_bundleMap_of_constant_coordinates (IB := IB) (n := n)
    (fun x u ↦ bundleHomComplexificationEquiv F (V := V) (L := L) x u)
    (A := (Complexification.strongDualLineEquiv F).toContinuousLinearMap.restrictScalars ℝ)
  intro a x hx u
  apply bundleHomComplexificationEquiv_in_trivializationAt a x _ u
  simpa only [trivializationAt_complexification, hom_trivializationAt,
    Trivialization.baseSet_complexification, Trivialization.baseSet_continuousLinearMap]
      using hx.1

/-- Both directions are proved smooth on the original native bundle atlas. -/
theorem contMDiff_bundleHomComplexificationEquiv_symm :
    ContMDiff (IB.prod 𝓘(ℝ, Complexification F →L[ℂ] Complexification ℝ))
      (IB.prod 𝓘(ℝ, Complexification (F →L[ℝ] ℝ))) n
      (fun p : TotalSpace (Complexification F →L[ℂ] Complexification ℝ)
        (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) ↦
          TotalSpace.mk' (Complexification (F →L[ℝ] ℝ))
            (E := fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x)) p.proj
            ((bundleHomComplexificationEquiv (F := F) (V := V) (L := L) p.proj).symm p.2)) := by
  apply contMDiff_bundleMap_of_constant_coordinates (IB := IB) (n := n)
    (fun x A ↦ (bundleHomComplexificationEquiv F (V := V) (L := L) x).symm A)
    (A := (Complexification.strongDualLineEquiv F).symm.toContinuousLinearMap.restrictScalars ℝ)
  intro a x hx A
  apply bundleHomComplexificationEquiv_symm_in_trivializationAt a x _ A
  simpa only [trivializationAt_complexification, hom_trivializationAt,
    Trivialization.baseSet_complexification, Trivialization.baseSet_continuousLinearMap]
      using hx.1

/-- Native total-space comparison, with both smoothness proofs independently supplied. -/
def bundleHomComplexificationDiffeomorph :
    TotalSpace (Complexification (F →L[ℝ] ℝ)) (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))
      ≃ₘ^n⟮IB.prod 𝓘(ℝ, Complexification (F →L[ℝ] ℝ)),
        IB.prod 𝓘(ℝ, Complexification F →L[ℂ] Complexification ℝ)⟯
      TotalSpace (Complexification F →L[ℂ] Complexification ℝ)
        (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x)) where
  toFun p := ⟨p.proj, bundleHomComplexificationEquiv (F := F) (V := V) (L := L) p.proj p.2⟩
  invFun p := ⟨p.proj, (bundleHomComplexificationEquiv (F := F) (V := V) (L := L) p.proj).symm p.2⟩
  left_inv p := by simp
  right_inv p := by simp
  contMDiff_toFun := contMDiff_bundleHomComplexificationEquiv
  contMDiff_invFun := contMDiff_bundleHomComplexificationEquiv_symm

/-- Evaluation of the original native total-space comparison. -/
@[simp] theorem bundleHomComplexificationDiffeomorph_apply
    (p : TotalSpace (Complexification (F →L[ℝ] ℝ))
      (fun x ↦ ℂ ⊗[ℝ] (V x →L[ℝ] L x))) :
    bundleHomComplexificationDiffeomorph (IB := IB) (n := n) p =
      ⟨p.proj, bundleHomComplexificationEquiv (F := F) (V := V) (L := L) p.proj p.2⟩ := by rfl

/-- Evaluation of the inverse on the original native total space. -/
@[simp] theorem bundleHomComplexificationDiffeomorph_symm_apply
    (p : TotalSpace (Complexification F →L[ℂ] Complexification ℝ)
      (fun x ↦ (ℂ ⊗[ℝ] V x) →L[ℂ] (ℂ ⊗[ℝ] L x))) :
    (bundleHomComplexificationDiffeomorph (IB := IB) (n := n)).symm p =
      ⟨p.proj, (bundleHomComplexificationEquiv (F := F) (V := V) (L := L) p.proj).symm p.2⟩ :=
        by rfl

variable [ContMDiffVectorBundle n F V IB] [ContMDiffVectorBundle n ℝ L IB]

/-- Complex Hom between complexifications of a real bundle and a real line bundle is a
real `C^n` vector bundle with its native Hom atlas. -/
instance instContMDiffVectorBundleComplexificationHom :
    ContMDiffVectorBundle n (Complexification F →L[ℂ] Complexification ℝ)
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
      (contMDiffOn_const (c := (Complexification.strongDualLineEquiv
        F).toContinuousLinearMap.restrictScalars ℝ))
      (hs.clm_comp
        (contMDiffOn_const (c := (Complexification.strongDualLineEquiv
          F).symm.toContinuousLinearMap.restrictScalars ℝ)))
    simp only [Trivialization.baseSet_complexification,
      Trivialization.baseSet_continuousLinearMap] at h ⊢
    exact h.congr fun x hx ↦ complexificationHom_coordChange e e' d d' hx

end Smooth
end TauCeti
