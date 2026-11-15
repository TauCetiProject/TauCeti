/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Smooth maps into trivial bundles

The trivial bundle `Bundle.Trivial B F` has the single global trivialization
`Bundle.Trivial.trivialization B F`, so a map into its total space is smooth exactly when its base
map and its fibre map into `F` are smooth. When the fibre `W` is instead a finite-dimensional
Hausdorff topological module without a fixed norm, `Bundle.TrivialModel 𝕜 W` supplies
`Fin (Module.finrank 𝕜 W) → 𝕜` as a nominal coordinate model fibre equipping `Bundle.Trivial B W`
with a `C^n` vector bundle structure without `AddCommGroup` diamonds on `W`.
-/

public section

open Bundle Set
open scoped Manifold ContDiff

section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {EB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
  {HB : Type*} [TopologicalSpace HB] {I : ModelWithCorners 𝕜 EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {EM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  {HM : Type*} [TopologicalSpace HM] {J : ModelWithCorners 𝕜 EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] {n : ℕ∞ω}

namespace Bundle.Trivial

/-- A map into the trivial bundle is smooth at a point exactly when its base map and its fibre
map are smooth there. -/
theorem contMDiffAt_mk_iff {b : M → B} {f : M → F} {x : M} :
    ContMDiffAt J (I.prod 𝓘(𝕜, F)) n
        (fun y ↦ TotalSpace.mk' F (E := Trivial B F) (b y) (f y)) x ↔
      ContMDiffAt J I n b x ∧ ContMDiffAt J 𝓘(𝕜, F) n f x := by
  rw [Bundle.contMDiffAt_totalSpace_iff]
  simp

/-- A map into the trivial bundle is smooth exactly when its base map and its fibre map are
smooth. -/
theorem contMDiff_mk_iff {b : M → B} {f : M → F} :
    ContMDiff J (I.prod 𝓘(𝕜, F)) n (fun y ↦ TotalSpace.mk' F (E := Trivial B F) (b y) (f y)) ↔
      ContMDiff J I n b ∧ ContMDiff J 𝓘(𝕜, F) n f :=
  (forall_congr' fun _ ↦ contMDiffAt_mk_iff).trans forall_and

end Bundle.Trivial

end

/-! ### Trivial bundles with finite-dimensional topological-module fibres -/

noncomputable section

namespace Bundle

/-- The coordinate normed space `Fin (Module.finrank 𝕜 W) → 𝕜` used as the model fibre of
`Bundle.Trivial B W` when `W` is a finite-dimensional topological vector space without a fixed
norm, avoiding instance diamonds with `Bundle.Trivial.fiberBundle`. -/
def TrivialModel (𝕜 W : Type*) [DivisionRing 𝕜] [AddCommGroup W] [Module 𝕜 W] : Type _ :=
  Fin (Module.finrank 𝕜 W) → 𝕜

namespace TrivialModel

section Normed

variable {𝕜 W : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup W] [Module 𝕜 W]

instance instNormedAddCommGroup : NormedAddCommGroup (TrivialModel 𝕜 W) :=
  inferInstanceAs (NormedAddCommGroup (Fin (Module.finrank 𝕜 W) → 𝕜))

instance instNormedSpace : NormedSpace 𝕜 (TrivialModel 𝕜 W) :=
  inferInstanceAs (NormedSpace 𝕜 (Fin (Module.finrank 𝕜 W) → 𝕜))

instance instFiniteDimensional : FiniteDimensional 𝕜 (TrivialModel 𝕜 W) :=
  inferInstanceAs (FiniteDimensional 𝕜 (Fin (Module.finrank 𝕜 W) → 𝕜))

instance instCompleteSpace [CompleteSpace 𝕜] : CompleteSpace (TrivialModel 𝕜 W) :=
  inferInstanceAs (CompleteSpace (Fin (Module.finrank 𝕜 W) → 𝕜))

end Normed

section Bundle

variable {𝕜 B W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [TopologicalSpace B] [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W]
  [IsTopologicalAddGroup W] [ContinuousSMul 𝕜 W] [T2Space W] [FiniteDimensional 𝕜 W]

variable (𝕜 W) in
/-- Continuous linear equivalence between `W` and `TrivialModel 𝕜 W` via `Module.finBasis 𝕜 W`. -/
def equiv : W ≃L[𝕜] TrivialModel 𝕜 W :=
  LinearEquiv.toContinuousLinearEquiv ((Module.finBasis 𝕜 W).equivFun : W ≃ₗ[𝕜] TrivialModel 𝕜 W)

instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (TrivialModel 𝕜 W) (Bundle.Trivial B W)) :=
  TopologicalSpace.induced TotalSpace.proj ‹TopologicalSpace B› ⊓
    TopologicalSpace.induced TotalSpace.snd ‹TopologicalSpace W›

variable (𝕜 B W) in
/-- Homeomorphism between the total space of `Bundle.Trivial B W` (modelled on `TrivialModel 𝕜 W`)
and `B × TrivialModel 𝕜 W`. -/
def homeomorphProd : TotalSpace (TrivialModel 𝕜 W) (Bundle.Trivial B W) ≃ₜ B × TrivialModel 𝕜 W :=
  (Equiv.mk (fun p ↦ (p.proj, p.snd)) (fun q ↦ ⟨q.1, q.2⟩) (fun _ ↦ rfl) (fun _ ↦ rfl)
    |>.toHomeomorphOfIsInducing
      ⟨by simp only [instTopologicalSpaceProd, induced_inf, induced_compose]; rfl⟩).trans
    ((Homeomorph.refl B).prodCongr (equiv 𝕜 W).toHomeomorph)

@[simp] theorem homeomorphProd_apply (p : TotalSpace (TrivialModel 𝕜 W) (Bundle.Trivial B W)) :
    homeomorphProd 𝕜 B W p = (p.proj, equiv 𝕜 W p.snd) := (rfl)

@[simp] theorem homeomorphProd_symm_apply (q : B × TrivialModel 𝕜 W) :
    (homeomorphProd 𝕜 B W).symm q = ⟨q.1, (equiv 𝕜 W).symm q.2⟩ := (rfl)

variable (𝕜 B W) in
/-- Global trivialization of `Bundle.Trivial B W` with model fibre `TrivialModel 𝕜 W`. -/
def trivialization :
    Trivialization (TrivialModel 𝕜 W) (π (TrivialModel 𝕜 W) (Bundle.Trivial B W)) :=
  { toOpenPartialHomeomorph := (homeomorphProd 𝕜 B W).toOpenPartialHomeomorph, baseSet := univ
    open_baseSet := isOpen_univ, source_eq := rfl, target_eq := univ_prod_univ.symm
    proj_toFun _ _ := rfl }

@[simp] theorem trivialization_baseSet : (trivialization 𝕜 B W).baseSet = univ := (rfl)

@[simp] theorem trivialization_source : (trivialization 𝕜 B W).source = univ := (rfl)

@[simp] theorem trivialization_apply (p : TotalSpace (TrivialModel 𝕜 W) (Bundle.Trivial B W)) :
    trivialization 𝕜 B W p = (p.proj, equiv 𝕜 W p.snd) := (rfl)

@[simp] theorem toOpenPartialHomeomorph_trivialization_symm_apply (q : B × TrivialModel 𝕜 W) :
    (trivialization 𝕜 B W).toOpenPartialHomeomorph.symm q = ⟨q.1, (equiv 𝕜 W).symm q.2⟩ := (rfl)

instance instFiberBundle : FiberBundle (TrivialModel 𝕜 W) (Bundle.Trivial B W) where
  trivializationAtlas' := {trivialization 𝕜 B W}
  trivializationAt' _ := trivialization 𝕜 B W
  mem_baseSet_trivializationAt' _ := by simp
  trivialization_mem_atlas' _ := mem_singleton _
  totalSpaceMk_isInducing' b := by
    have hcomp : TotalSpace.mk (F := TrivialModel 𝕜 W) (E := Bundle.Trivial B W) b =
        (homeomorphProd 𝕜 B W).symm ∘ (fun y ↦ (b, y)) ∘ equiv 𝕜 W :=
      funext fun w ↦ (congrArg (TotalSpace.mk (F := TrivialModel 𝕜 W) (E := Bundle.Trivial B W) b)
        ((equiv 𝕜 W).symm_apply_apply w).symm).trans
        (homeomorphProd_symm_apply (b, equiv 𝕜 W w)).symm
    rw [hcomp]
    exact (homeomorphProd 𝕜 B W).symm.isInducing.comp
      ((Topology.isInducing_const_prod.2 .id).comp (equiv 𝕜 W).toHomeomorph.isInducing)

@[simp] theorem trivializationAt_eq (b : B) :
    trivializationAt (TrivialModel 𝕜 W) (Bundle.Trivial B W) b = trivialization 𝕜 B W := (rfl)

theorem eq_trivialization
    (e : Trivialization (TrivialModel 𝕜 W) (π (TrivialModel 𝕜 W) (Bundle.Trivial B W)))
    [h : MemTrivializationAtlas e] : e = trivialization 𝕜 B W :=
  mem_singleton_iff.1 h.out

instance instIsLinearTrivialization : (trivialization 𝕜 B W).IsLinear 𝕜 where
  linear _ _ := ⟨(equiv 𝕜 W).map_add, (equiv 𝕜 W).map_smul⟩

@[simp] theorem trivialization_symm_apply (b : B) (v : TrivialModel 𝕜 W) :
    (trivialization 𝕜 B W).symm b v = (equiv 𝕜 W).symm v := by
  have hv : (trivialization 𝕜 B W ⟨b, (equiv 𝕜 W).symm v⟩).2 = v := by simp
  simpa only [hv] using
    (trivialization 𝕜 B W).symm_apply_apply_mk (b := b) (by simp) ((equiv 𝕜 W).symm v)

theorem trivialization_coordChangeL (b : B) :
    (trivialization 𝕜 B W).coordChangeL 𝕜 (trivialization 𝕜 B W) b =
      ContinuousLinearEquiv.refl 𝕜 (TrivialModel 𝕜 W) := by
  ext v; rw [Trivialization.coordChangeL_apply']; exacts [by simp, ⟨mem_univ _, mem_univ _⟩]

instance instVectorBundle : VectorBundle 𝕜 (TrivialModel 𝕜 W) (Bundle.Trivial B W) where
  trivialization_linear' e _ := by obtain rfl := eq_trivialization e; infer_instance
  continuousOn_coordChange' e e' _ _ := by
    obtain rfl := eq_trivialization e; obtain rfl := eq_trivialization e'
    simp only [trivialization_coordChangeL]; exact continuous_const.continuousOn

@[simp] theorem trivialization_continuousLinearMapAt_apply (b : B) (w : W) :
    (trivialization 𝕜 B W).continuousLinearMapAt 𝕜 b w = equiv 𝕜 W w := by
  rw [Trivialization.continuousLinearMapAt_apply,
    (trivialization 𝕜 B W).coe_linearMapAt_of_mem (mem_univ b)]; rfl

instance instContMDiffVectorBundle {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB]
    [TopologicalSpace HB] {IB : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B] {n : ℕ∞ω} :
    ContMDiffVectorBundle n (TrivialModel 𝕜 W) (Bundle.Trivial B W) IB where
  contMDiffOn_coordChangeL e e' _ _ := by
    obtain rfl := eq_trivialization e; obtain rfl := eq_trivialization e'
    simp_rw [trivialization_coordChangeL]; exact contMDiff_const.contMDiffOn

variable {EB HB EM HM M : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  {I : ModelWithCorners 𝕜 EB HB} [ChartedSpace HB B] [NormedAddCommGroup EM] [NormedSpace 𝕜 EM]
  [TopologicalSpace HM] {J : ModelWithCorners 𝕜 EM HM} [TopologicalSpace M] [ChartedSpace HM M]
  {n : ℕ∞ω} {b : M → B} {f : M → W}

/-- A map into `TotalSpace (TrivialModel 𝕜 W) (Bundle.Trivial B W)` is `C^n` at a point iff its
base map and its `TrivialModel`-valued fibre map are `C^n` there. -/
theorem contMDiffAt_mk_iff {x : M} :
    ContMDiffAt J (I.prod 𝓘(𝕜, TrivialModel 𝕜 W)) n
        (fun y ↦ TotalSpace.mk' (TrivialModel 𝕜 W) (E := Bundle.Trivial B W) (b y) (f y)) x ↔
      ContMDiffAt J I n b x ∧
        ContMDiffAt J 𝓘(𝕜, TrivialModel 𝕜 W) n (fun y ↦ equiv 𝕜 W (f y)) x := by
  rw [Bundle.contMDiffAt_totalSpace_iff]; simp

theorem contMDiff_mk_iff :
    ContMDiff J (I.prod 𝓘(𝕜, TrivialModel 𝕜 W)) n
        (fun y ↦ TotalSpace.mk' (TrivialModel 𝕜 W) (E := Bundle.Trivial B W) (b y) (f y)) ↔
      ContMDiff J I n b ∧ ContMDiff J 𝓘(𝕜, TrivialModel 𝕜 W) n (fun y ↦ equiv 𝕜 W (f y)) :=
  (forall_congr' fun _ ↦ contMDiffAt_mk_iff).trans forall_and

end Bundle

end TrivialModel

end Bundle

end
