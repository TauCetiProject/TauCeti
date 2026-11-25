/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Diffeomorph
public import Mathlib.Geometry.Manifold.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Smooth maps into trivial bundles

The trivial bundle `Bundle.Trivial B F` has the single global trivialization
`Bundle.Trivial.trivialization B F`, so a map into its total space is smooth (or differentiable at
a point) exactly when its base map and its fibre map into `F` are; in particular its constant
sections are smooth, the underlying `F`-valued function of a smooth section is smooth
(`ContMDiffSection.contMDiff_coe_trivial`), and a section is differentiable at a point exactly when
its fibre map is (`Bundle.Trivial.mdifferentiableAt_section_iff`). `Bundle.Trivial.homeomorphProd`
upgrades to a `C^n` diffeomorphism `Bundle.Trivial.diffeomorphProd` between
`TotalSpace F (Bundle.Trivial B F)` and `B × F`. When the fibre `W` is instead a finite-dimensional
Hausdorff topological module over a complete nontrivially normed field `𝕜` without a fixed norm,
`TauCeti.TrivialModel 𝕜 W` supplies `Fin (Module.finrank 𝕜 W) → 𝕜` as a nominal coordinate model
fibre equipping `Bundle.Trivial B W` with a `C^n` vector bundle structure without `AddCommGroup`
diamonds on `W`.

The topology, fibre bundle, vector bundle, and `C^n` vector bundle instances for
`TauCeti.TrivialModel` directly adapt Mathlib's `Bundle.Trivial.fiberBundle`
(`Mathlib.Topology.FiberBundle.Constructions`), `Bundle.Trivial.vectorBundle`
(`Mathlib.Topology.VectorBundle.Constructions`), and `Bundle.Trivial.contMDiffVectorBundle`
(`Mathlib.Geometry.Manifold.VectorBundle.Basic`) by Nicolò Cavalleri, Sébastien Gouëzel,
Heather Macbeth, and Floris van Doorn.
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

/-- A section of the trivial bundle is differentiable at a point exactly when its fibre map into
`F` is differentiable there. -/
theorem mdifferentiableAt_section_iff {σ : B → F} {x : B} :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun y ↦ TotalSpace.mk' F (E := Trivial B F) y (σ y)) x ↔
      MDifferentiableAt I 𝓘(𝕜, F) σ x := by
  rw [mdifferentiableAt_section]
  simp only [Trivial.fiberBundle_trivializationAt', Trivial.trivialization_apply]

/-- A map into the trivial bundle is differentiable at a point exactly when its base map and its
fibre map are differentiable there. -/
theorem mdifferentiableAt_mk_iff {b : M → B} {f : M → F} {x : M} :
    MDifferentiableAt J (I.prod 𝓘(𝕜, F))
        (fun y ↦ TotalSpace.mk' F (E := Trivial B F) (b y) (f y)) x ↔
      MDifferentiableAt J I b x ∧ MDifferentiableAt J 𝓘(𝕜, F) f x := by
  rw [mdifferentiableAt_totalSpace]
  simp

/-- A constant section of the trivial bundle is smooth. -/
theorem contMDiff_mk_const (c : F) :
    ContMDiff I (I.prod 𝓘(𝕜, F)) n (fun y : B ↦ TotalSpace.mk' F (E := Trivial B F) y c) :=
  contMDiff_mk_iff.2 ⟨contMDiff_id, contMDiff_const⟩

/-- A constant section of the trivial bundle is differentiable. -/
theorem mdifferentiableAt_mk_const (c : F) {x : B} :
    MDifferentiableAt I (I.prod 𝓘(𝕜, F)) (fun y : B ↦ TotalSpace.mk' F (E := Trivial B F) y c) x :=
  mdifferentiableAt_mk_iff.2 ⟨mdifferentiableAt_id, mdifferentiableAt_const⟩

omit [TopologicalSpace B] in
/-- On the trivial line bundle, a function times the constant section `1` is the function. -/
protected theorem smul_one (σ : B → 𝕜) : (σ • (1 : B → 𝕜) : Π y : B, Trivial B 𝕜 y) = σ :=
  funext fun _ ↦ mul_one _

/-- The underlying `F`-valued function of a smooth section of the trivial bundle is smooth. -/
theorem _root_.ContMDiffSection.contMDiff_coe_trivial (s : Cₛ^n⟮I; F, Trivial B F⟯) :
    ContMDiff I 𝓘(𝕜, F) n (fun x ↦ (s x : F)) :=
  (contMDiff_mk_iff.1 s.contMDiff).2

section Diffeomorph

variable (I B F n)

/-- `C^n` diffeomorphism between the total space of the trivial bundle and the Cartesian product,
upgrading `Bundle.Trivial.homeomorphProd`. -/
def diffeomorphProd :
    TotalSpace F (Trivial B F) ≃ₘ^n⟮I.prod 𝓘(𝕜, F), I.prod 𝓘(𝕜, F)⟯ B × F where
  toFun p := (p.proj, p.snd)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  contMDiff_toFun := (Bundle.contMDiff_proj (Trivial B F)).prodMk
    ((contMDiff_mk_iff (f := fun p : TotalSpace F (Trivial B F) ↦ p.snd)).mp contMDiff_id).2
  contMDiff_invFun := contMDiff_mk_iff.mpr ⟨contMDiff_fst, contMDiff_snd⟩

/-- Forward formula for `Bundle.Trivial.diffeomorphProd`. -/
@[simp]
theorem diffeomorphProd_apply (p : TotalSpace F (Trivial B F)) :
    diffeomorphProd I B F n p = (p.proj, p.snd) :=
  (rfl)

/-- Inverse formula for `Bundle.Trivial.diffeomorphProd`. -/
@[simp]
theorem diffeomorphProd_symm_apply (q : B × F) :
    (diffeomorphProd I B F n).symm q = ⟨q.1, q.2⟩ :=
  (rfl)

/-- The underlying homeomorphism of `Bundle.Trivial.diffeomorphProd` is
`Bundle.Trivial.homeomorphProd`. -/
@[simp]
theorem toHomeomorph_diffeomorphProd :
    (diffeomorphProd I B F n).toHomeomorph = homeomorphProd B F :=
  Homeomorph.ext fun p ↦ by simp

end Diffeomorph

end Bundle.Trivial
end

/-! ### Trivial bundles with finite-dimensional topological-module fibres -/

noncomputable section
namespace TauCeti

/-- The coordinate normed space `Fin (Module.finrank 𝕜 W) → 𝕜` used as the model fibre of
`Bundle.Trivial B W` for a finite-dimensional topological module `W` without a fixed norm. -/
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

section FiberBundle
variable {𝕜 B W : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] [TopologicalSpace B]
  [AddCommGroup W] [Module 𝕜 W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousSMul 𝕜 W] [T2Space W] [FiniteDimensional 𝕜 W]

variable (𝕜 W) in
/-- Continuous linear equivalence between `W` and `TrivialModel 𝕜 W` via `Module.finBasis 𝕜 W`. -/
def equiv : W ≃L[𝕜] TrivialModel 𝕜 W :=
  LinearEquiv.toContinuousLinearEquiv ((Module.finBasis 𝕜 W).equivFun : W ≃ₗ[𝕜] TrivialModel 𝕜 W)

instance instTopologicalSpaceTotalSpace :
    TopologicalSpace (TotalSpace (TrivialModel 𝕜 W) (Bundle.Trivial B W)) :=
  TopologicalSpace.induced TotalSpace.proj ‹TopologicalSpace B› ⊓
    TopologicalSpace.induced TotalSpace.snd ‹TopologicalSpace W›

variable (𝕜 B W) in
/-- Homeomorphism `TotalSpace (TrivialModel 𝕜 W) (Bundle.Trivial B W) ≃ₜ B × TrivialModel 𝕜 W`. -/
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
  ⟨(homeomorphProd 𝕜 B W).toOpenPartialHomeomorph, univ, isOpen_univ, rfl,
    univ_prod_univ.symm, fun _ _ ↦ rfl⟩

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
        (homeomorphProd 𝕜 B W).symm ∘ (fun y ↦ (b, y)) ∘ equiv 𝕜 W := funext fun _ ↦ by simp
    rw [hcomp]; exact (homeomorphProd 𝕜 B W).symm.isInducing.comp
      ((Topology.isInducing_const_prod.2 .id).comp (equiv 𝕜 W).toHomeomorph.isInducing)

@[simp] theorem trivializationAt_eq (b : B) :
    trivializationAt (TrivialModel 𝕜 W) (Bundle.Trivial B W) b = trivialization 𝕜 B W := (rfl)

theorem eq_trivialization
    (e : Trivialization (TrivialModel 𝕜 W) (π (TrivialModel 𝕜 W) (Bundle.Trivial B W)))
    [h : MemTrivializationAtlas e] : e = trivialization 𝕜 B W := mem_singleton_iff.1 h.out

instance instIsLinearTrivialization : (trivialization 𝕜 B W).IsLinear 𝕜 :=
  ⟨fun _ _ ↦ ⟨(equiv 𝕜 W).map_add, (equiv 𝕜 W).map_smul⟩⟩

@[simp] theorem trivialization_symm_apply (b : B) (v : TrivialModel 𝕜 W) :
    (trivialization 𝕜 B W).symm b v = (equiv 𝕜 W).symm v := by
  have hv : (trivialization 𝕜 B W ⟨b, (equiv 𝕜 W).symm v⟩).2 = v := by simp
  simpa only [hv] using
    (trivialization 𝕜 B W).symm_apply_apply_mk (mem_univ b) ((equiv 𝕜 W).symm v)

theorem trivialization_coordChangeL (b : B) : (trivialization 𝕜 B W).coordChangeL 𝕜
    (trivialization 𝕜 B W) b = .refl 𝕜 (TrivialModel 𝕜 W) := by
  ext v; rw [Trivialization.coordChangeL_apply']; exacts [by simp, ⟨mem_univ _, mem_univ _⟩]

instance instVectorBundle : VectorBundle 𝕜 (TrivialModel 𝕜 W) (Bundle.Trivial B W) where
  trivialization_linear' e _ := by obtain rfl := eq_trivialization e; infer_instance
  continuousOn_coordChange' e e' _ _ := by
    obtain rfl := eq_trivialization e; obtain rfl := eq_trivialization e'
    simp [trivialization_coordChangeL, continuous_const.continuousOn]

@[simp] theorem trivialization_continuousLinearMapAt_apply (b : B) (w : W) :
    (trivialization 𝕜 B W).continuousLinearMapAt 𝕜 b w = equiv 𝕜 W w := by
  simp [Trivialization.continuousLinearMapAt_apply,
    (trivialization 𝕜 B W).coe_linearMapAt_of_mem (mem_univ b)]

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

/-- A map into `TotalSpace (TrivialModel 𝕜 W) (Bundle.Trivial B W)` is `C^n` at a point if and only
if its base map and its `TrivialModel.equiv 𝕜 W`-valued fibre map are `C^n` there. -/
theorem contMDiffAt_mk_iff {x : M} :
    ContMDiffAt J (I.prod 𝓘(𝕜, TrivialModel 𝕜 W)) n
        (fun y ↦ TotalSpace.mk' (TrivialModel 𝕜 W) (E := Bundle.Trivial B W) (b y) (f y)) x ↔
      ContMDiffAt J I n b x ∧
        ContMDiffAt J 𝓘(𝕜, TrivialModel 𝕜 W) n (fun y ↦ equiv 𝕜 W (f y)) x := by
  rw [Bundle.contMDiffAt_totalSpace_iff]; simp

/-- A map into `TotalSpace (TrivialModel 𝕜 W) (Bundle.Trivial B W)` is `C^n` if and only if its
base map and its `TrivialModel.equiv 𝕜 W`-valued fibre map are `C^n`. -/
theorem contMDiff_mk_iff :
    ContMDiff J (I.prod 𝓘(𝕜, TrivialModel 𝕜 W)) n
        (fun y ↦ TotalSpace.mk' (TrivialModel 𝕜 W) (E := Bundle.Trivial B W) (b y) (f y)) ↔
      ContMDiff J I n b ∧ ContMDiff J 𝓘(𝕜, TrivialModel 𝕜 W) n (fun y ↦ equiv 𝕜 W (f y)) :=
  (forall_congr' fun _ ↦ contMDiffAt_mk_iff).trans forall_and

end FiberBundle
end TrivialModel
end TauCeti
end
