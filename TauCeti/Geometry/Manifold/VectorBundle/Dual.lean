/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import TauCeti.Geometry.Manifold.VectorBundle.Hom.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Trivial
public import TauCeti.Topology.VectorBundle.Dual
import TauCeti.Topology.Algebra.Module.FiniteDimension

/-!
# Smooth transpose maps and duality in vector bundles

For a vector bundle `V` over `B`, Mathlib realizes `StrongDual 𝕜 (V x)` as the Hom bundle into
`Bundle.Trivial B 𝕜`. Thus fibrewise precomposition gives `C^n` regularity of fibrewise dual
(transpose) maps (`ContMDiffWithinAt.clm_bundle_dual_precomp`). In finite rank over a complete
field, this upgrades to an equivalence (`TauCeti.contMDiffWithinAt_clm_bundle_dual_precomp_iff`,
`TauCeti.contMDiff_clm_bundle_dual_precomp_iff`,
`TauCeti.contMDiff_totalSpaceMap_dual_precomp_iff`), inducing dual bundle diffeomorphisms
(`TauCeti.bundleDualDiffeomorph`, `TauCeti.exists_bundleDiffeomorph_dual_precomp_iff`).

## References
* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapters 10–11.
-/

public section

noncomputable section

open Bundle FiberBundle Set
open scoped Manifold ContDiff Topology

section

variable {𝕜 EB EM HB HM B M : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [TopologicalSpace HB] [TopologicalSpace HM] {IB : ModelWithCorners 𝕜 EB HB}
  {IM : ModelWithCorners 𝕜 EM HM} [TopologicalSpace B] [ChartedSpace HB B]
  [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}

section Precomp

variable {F₁ F₂ : Type*} [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
  [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] {V₁ V₂ : B → Type*}
  [∀ x, AddCommGroup (V₁ x)] [∀ x, Module 𝕜 (V₁ x)] [∀ x, TopologicalSpace (V₁ x)]
  [∀ x, AddCommGroup (V₂ x)] [∀ x, Module 𝕜 (V₂ x)] [∀ x, TopologicalSpace (V₂ x)]
  [∀ x, IsTopologicalAddGroup (V₂ x)] [∀ x, ContinuousSMul 𝕜 (V₂ x)]
  [TopologicalSpace (TotalSpace F₁ V₁)] [TopologicalSpace (TotalSpace F₂ V₂)]
  [FiberBundle F₁ V₁] [VectorBundle 𝕜 F₁ V₁] [FiberBundle F₂ V₂] [VectorBundle 𝕜 F₂ V₂]

section

variable {b : M → B} {s : Set M} {x : M} {A : ∀ y, V₁ (b y) →L[𝕜] V₂ (b y)}

/-- Fibrewise dual (transpose) of a `C^n` Hom-bundle section is `C^n` within `s` at `x`. -/
theorem ContMDiffWithinAt.clm_bundle_dual_precomp
    (hA : ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n (fun y ↦ TotalSpace.mk'
      (F₁ →L[𝕜] F₂) (E := fun z ↦ V₁ z →L[𝕜] V₂ z) (b y) (A y)) s x) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁)) n (fun y ↦
      TotalSpace.mk' (StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁) (E := fun z ↦
        StrongDual 𝕜 (V₂ z) →L[𝕜] StrongDual 𝕜 (V₁ z)) (b y) (.precomp 𝕜 (A y))) s x :=
  hA.clm_bundle_precomp (F₃ := 𝕜) (Trivial B 𝕜)

/-- Fibrewise dual (transpose) of a Hom-bundle section `C^n` at `x` is `C^n` at `x`. -/
theorem ContMDiffAt.clm_bundle_dual_precomp
    (hA : ContMDiffAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n (fun y ↦ TotalSpace.mk'
      (F₁ →L[𝕜] F₂) (E := fun z ↦ V₁ z →L[𝕜] V₂ z) (b y) (A y)) x) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁)) n (fun y ↦
      TotalSpace.mk' (StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁) (E := fun z ↦
        StrongDual 𝕜 (V₂ z) →L[𝕜] StrongDual 𝕜 (V₁ z)) (b y) (.precomp 𝕜 (A y))) x :=
  ContMDiffWithinAt.clm_bundle_dual_precomp hA

/-- Fibrewise dual (transpose) of a Hom-bundle section `C^n` on `s` is `C^n` on `s`. -/
theorem ContMDiffOn.clm_bundle_dual_precomp
    (hA : ContMDiffOn IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n (fun y ↦ TotalSpace.mk'
      (F₁ →L[𝕜] F₂) (E := fun z ↦ V₁ z →L[𝕜] V₂ z) (b y) (A y)) s) :
    ContMDiffOn IM (IB.prod 𝓘(𝕜, StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁)) n (fun y ↦
      TotalSpace.mk' (StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁) (E := fun z ↦
        StrongDual 𝕜 (V₂ z) →L[𝕜] StrongDual 𝕜 (V₁ z)) (b y) (.precomp 𝕜 (A y))) s :=
  fun y hy ↦ (hA y hy).clm_bundle_dual_precomp

/-- Fibrewise dual (transpose) of a `C^n` Hom-bundle section is `C^n`. -/
theorem ContMDiff.clm_bundle_dual_precomp
    (hA : ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n (fun y ↦ TotalSpace.mk'
      (F₁ →L[𝕜] F₂) (E := fun z ↦ V₁ z →L[𝕜] V₂ z) (b y) (A y))) :
    ContMDiff IM (IB.prod 𝓘(𝕜, StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁)) n (fun y ↦
      TotalSpace.mk' (StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁) (E := fun z ↦
        StrongDual 𝕜 (V₂ z) →L[𝕜] StrongDual 𝕜 (V₁ z)) (b y) (.precomp 𝕜 (A y))) :=
  fun y ↦ (hA y).clm_bundle_dual_precomp

end

namespace TauCeti

section FiniteRankDual

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F₂]

/-- Over a complete field with finite-dimensional target model fibre `F₂`, a Hom-bundle section
along `b` is `C^n` within `s` at `x` iff its fibrewise dual (transpose) section is. -/
theorem contMDiffWithinAt_clm_bundle_dual_precomp_iff {b : M → B}
    {A : ∀ y, V₁ (b y) →L[𝕜] V₂ (b y)} {s : Set M} {x : M} :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁)) n (fun y ↦
        TotalSpace.mk' (StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁) (E := fun z ↦
          StrongDual 𝕜 (V₂ z) →L[𝕜] StrongDual 𝕜 (V₁ z)) (b y) (.precomp 𝕜 (A y))) s x ↔
      ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n (fun y ↦ TotalSpace.mk'
        (F₁ →L[𝕜] F₂) (E := fun z ↦ V₁ z →L[𝕜] V₂ z) (b y) (A y)) s x := by
  refine ⟨fun hdual ↦ ?_, ContMDiffWithinAt.clm_bundle_dual_precomp⟩
  rw [contMDiffWithinAt_hom_bundle] at hdual ⊢
  refine ⟨hdual.1, ?_⟩
  let _ : NormedAddCommGroup (StrongDual 𝕜 (StrongDual 𝕜 F₂)) := inferInstance
  let _ : NormedSpace 𝕜 (StrongDual 𝕜 (StrongDual 𝕜 F₂)) := inferInstance
  let j₂ : F₂ ≃L[𝕜] StrongDual 𝕜 (StrongDual 𝕜 F₂) := LinearEquiv.toContinuousLinearEquiv <|
    (Module.evalEquiv 𝕜 F₂).trans (((LinearMap.toContinuousLinearMap :
      Module.Dual 𝕜 F₂ ≃ₗ[𝕜] StrongDual 𝕜 F₂).arrowCongr (.refl 𝕜 𝕜)).trans
      LinearMap.toContinuousLinearMap)
  let L_inv : (StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁) →L[𝕜] F₁ →L[𝕜] F₂ :=
    (ContinuousLinearMap.compL 𝕜 F₁ (StrongDual 𝕜 (StrongDual 𝕜 F₂)) F₂
      j₂.symm.toContinuousLinearMap).comp
      (ContinuousLinearMap.flipₗᵢ 𝕜 (StrongDual 𝕜 F₂) F₁ 𝕜).toLinearIsometry.toContinuousLinearMap
  have hret (T : F₁ →L[𝕜] F₂) : L_inv (ContinuousLinearMap.precomp 𝕜 T) = T := by
    ext v; apply j₂.injective; ext α; simp [L_inv, ContinuousLinearMap.flipₗᵢ, j₂]
  have hnear := hdual.1.insert.continuousWithinAt.preimage_mem_nhdsWithin <|
    ((trivializationAt F₁ V₁ (b x)).open_baseSet.inter
      (trivializationAt F₂ V₂ (b x)).open_baseSet).mem_nhds
      ⟨mem_baseSet_trivializationAt' (b x), mem_baseSet_trivializationAt' (b x)⟩
  have hcomp := L_inv.contDiff.contMDiff.contMDiffAt.comp_contMDiffWithinAt x hdual.2
  have heq : (fun y ↦ ContinuousLinearMap.inCoordinates F₁ V₁ F₂ V₂ (b x) (b y) (b x) (b y) (A y))
      =ᶠ[𝓝[insert x s] x] fun y ↦ L_inv (ContinuousLinearMap.inCoordinates (StrongDual 𝕜 F₂)
        (fun z ↦ StrongDual 𝕜 (V₂ z)) (StrongDual 𝕜 F₁) (fun z ↦ StrongDual 𝕜 (V₁ z))
        (b x) (b y) (b x) (b y) (.precomp 𝕜 (A y))) := by
    filter_upwards [hnear] with y hy
    rw [ContinuousLinearMap.inCoordinates_precomp (F₃ := 𝕜) (Trivial B 𝕜) (A y) hy.1 hy.2
      (by simp [Trivial.eq_trivialization]), hret]
  exact hcomp.congr_of_eventuallyEq (heq.filter_mono (nhdsWithin_mono _ (subset_insert x s)))
    (heq.self_of_nhdsWithin (mem_insert x s))

/-- Over a complete field with finite-dimensional target model fibre `F₂`, a Hom-bundle section
along `b` is `C^n` iff its fibrewise dual (transpose) section is `C^n`. -/
theorem contMDiff_clm_bundle_dual_precomp_iff {b : M → B} {A : ∀ y, V₁ (b y) →L[𝕜] V₂ (b y)} :
    ContMDiff IM (IB.prod 𝓘(𝕜, StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁)) n (fun y ↦
        TotalSpace.mk' (StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁) (E := fun z ↦
          StrongDual 𝕜 (V₂ z) →L[𝕜] StrongDual 𝕜 (V₁ z)) (b y) (.precomp 𝕜 (A y))) ↔
      ContMDiff IM (IB.prod 𝓘(𝕜, F₁ →L[𝕜] F₂)) n
        (fun y ↦ TotalSpace.mk' (F₁ →L[𝕜] F₂) (E := fun z ↦ V₁ z →L[𝕜] V₂ z) (b y) (A y)) :=
  forall_congr' fun x ↦ by simpa only [← contMDiffWithinAt_univ] using
    contMDiffWithinAt_clm_bundle_dual_precomp_iff (s := univ) (x := x)

variable [FiniteDimensional 𝕜 F₁]

/-- In finite dimensions over a complete field, the total-space map induced by the fibrewise dual
of `ψ : ∀ x, V₁ x →L[𝕜] V₂ x` is `C^n` iff the total-space map induced by `ψ` is `C^n`. -/
theorem contMDiff_totalSpaceMap_dual_precomp_iff (ψ : ∀ x, V₁ x →L[𝕜] V₂ x) :
    ContMDiff (IB.prod 𝓘(𝕜, StrongDual 𝕜 F₂)) (IB.prod 𝓘(𝕜, StrongDual 𝕜 F₁)) n
        (fun p : TotalSpace (StrongDual 𝕜 F₂) (fun x ↦ StrongDual 𝕜 (V₂ x)) ↦ TotalSpace.mk'
          (StrongDual 𝕜 F₁) (E := fun x ↦ StrongDual 𝕜 (V₁ x)) p.proj
          (.precomp 𝕜 (ψ p.proj) p.snd)) ↔
      ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
        (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (ψ p.proj p.snd)) := by
  rw [← contMDiff_hom_bundle_iff (IB := IB) (fun x ↦ ContinuousLinearMap.precomp 𝕜 (ψ x)),
    ← contMDiff_hom_bundle_iff (IB := IB) ψ]
  exact contMDiff_clm_bundle_dual_precomp_iff (b := id)

/-- `C^n` diffeomorphism of dual total spaces induced by a family of fibrewise continuous linear
equivalences with `C^n` total-space map. -/
def bundleDualDiffeomorph (e : ∀ x, V₁ x ≃L[𝕜] V₂ x)
    (he : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (e p.proj p.snd))) :
    TotalSpace (StrongDual 𝕜 F₂) (fun x ↦ StrongDual 𝕜 (V₂ x)) ≃ₘ^n⟮
      IB.prod 𝓘(𝕜, StrongDual 𝕜 F₂), IB.prod 𝓘(𝕜, StrongDual 𝕜 F₁)⟯
      TotalSpace (StrongDual 𝕜 F₁) (fun x ↦ StrongDual 𝕜 (V₁ x)) :=
  bundleDiffeomorph (bundleDualEquiv e) <|
    ((contMDiff_totalSpaceMap_dual_precomp_iff (IB := IB) (n := n)
      (fun x ↦ (e x).toContinuousLinearMap)).2 he).congr fun _ ↦ by simp

/-- Evaluation of `bundleDualDiffeomorph`. -/
@[simp] theorem bundleDualDiffeomorph_apply (e : ∀ x, V₁ x ≃L[𝕜] V₂ x)
    (he : ContMDiff (IB.prod 𝓘(𝕜, F₁)) (IB.prod 𝓘(𝕜, F₂)) n
      (fun p : TotalSpace F₁ V₁ ↦ TotalSpace.mk' F₂ p.proj (e p.proj p.snd)))
    (p : TotalSpace (StrongDual 𝕜 F₂) (fun x ↦ StrongDual 𝕜 (V₂ x))) :
    bundleDualDiffeomorph e he p =
      ⟨p.proj, ContinuousLinearMap.precomp 𝕜 (e p.proj).toContinuousLinearMap p.snd⟩ := by
  simp [bundleDualDiffeomorph]

/-- In finite dimensions over a complete field, the fibrewise dual of `ψ : ∀ x, V₁ x →L[𝕜] V₂ x`
underlies a `C^n` diffeomorphism of dual total spaces iff `ψ` underlies a `C^n` diffeomorphism of
the original total spaces. -/
theorem exists_bundleDiffeomorph_dual_precomp_iff (ψ : ∀ x, V₁ x →L[𝕜] V₂ x) :
    (∃ Φ : TotalSpace (StrongDual 𝕜 F₂) (fun x ↦ StrongDual 𝕜 (V₂ x)) ≃ₘ^n⟮
        IB.prod 𝓘(𝕜, StrongDual 𝕜 F₂), IB.prod 𝓘(𝕜, StrongDual 𝕜 F₁)⟯
        TotalSpace (StrongDual 𝕜 F₁) (fun x ↦ StrongDual 𝕜 (V₁ x)),
        ⇑Φ = fun p ↦ TotalSpace.mk' (StrongDual 𝕜 F₁) (E := fun x ↦ StrongDual 𝕜 (V₁ x))
          p.proj (.precomp 𝕜 (ψ p.proj) p.snd)) ↔
      ∃ Ψ : TotalSpace F₁ V₁ ≃ₘ^n⟮IB.prod 𝓘(𝕜, F₁), IB.prod 𝓘(𝕜, F₂)⟯ TotalSpace F₂ V₂,
        ⇑Ψ = fun p ↦ TotalSpace.mk' F₂ p.proj (ψ p.proj p.snd) := by
  rw [exists_bundleDiffeomorph_iff (fun x ↦ (ContinuousLinearMap.precomp 𝕜 (ψ x) :
      StrongDual 𝕜 (V₂ x) →L[𝕜] StrongDual 𝕜 (V₁ x))),
    exists_bundleDiffeomorph_iff ψ, contMDiff_totalSpaceMap_dual_precomp_iff]
  refine and_congr_right fun _ ↦ forall_congr' fun x ↦ ?_
  let e₁ := (trivializationAt F₁ V₁ x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F₁ V₁ x)
  let e₂ := (trivializationAt F₂ V₂ x).continuousLinearEquivAt 𝕜 x
    (mem_baseSet_trivializationAt F₂ V₂ x)
  let T : F₁ →L[𝕜] F₂ := e₂.toContinuousLinearMap.comp ((ψ x).comp e₁.symm.toContinuousLinearMap)
  have hdual : (e₁.arrowCongr (.refl 𝕜 𝕜) : StrongDual 𝕜 (V₁ x) → StrongDual 𝕜 F₁) ∘
      (ContinuousLinearMap.precomp 𝕜 (ψ x) : StrongDual 𝕜 (V₂ x) →L[𝕜] StrongDual 𝕜 (V₁ x)) ∘
        (e₂.arrowCongr (.refl 𝕜 𝕜)).symm = ContinuousLinearMap.precomp 𝕜 T := by
    ext α v; simp [T, ContinuousLinearEquiv.arrowCongr_apply]
  have h1 : Function.Bijective
      (ContinuousLinearMap.precomp 𝕜 T : StrongDual 𝕜 F₂ →L[𝕜] StrongDual 𝕜 F₁) ↔
      Function.Bijective (ContinuousLinearMap.precomp 𝕜 (ψ x) :
        StrongDual 𝕜 (V₂ x) →L[𝕜] StrongDual 𝕜 (V₁ x)) := by
    rw [← hdual, EquivLike.comp_bijective, EquivLike.bijective_comp]
  have h2 : Function.Bijective T ↔ Function.Bijective (ψ x) := by
    rw [show (T : F₁ → F₂) = e₂ ∘ (ψ x) ∘ e₁.symm from rfl,
      EquivLike.comp_bijective, EquivLike.bijective_comp]
  exact h1.symm.trans (T.precomp_bijective_iff_of_finiteDimensional.trans h2)

end FiniteRankDual

end TauCeti

end Precomp

end
