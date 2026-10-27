/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.Basic

/-!
# The maximal atlas of compatible trivializations of a `C^n` vector bundle

Mathlib makes the total space of a vector bundle `E` with fibre `F` over `B` a charted space
modelled on `B × F`, whose charts are the trivializations of the bundle's atlas, and shows that
for a `C^n` vector bundle these charts are compatible for the groupoid
`contMDiffFiberwiseLinear B F IB n` of bi-`C^n` fiberwise linear maps. The maximal atlas of that
groupoid is the set of all trivializations compatible with the bundle's `C^n` structure. Over
`𝓘(ℂ, EB)` it is the maximal atlas of holomorphic trivializations of a holomorphic vector bundle.

This file characterizes that maximal atlas by gauges. For two linear trivializations `e` and
`e'`, the coordinate change `e.symm ≫ₕ e'` lies in the groupoid exactly when the fibrewise
coordinate changes `e.coordChangeL 𝕜 e'` and `e'.coordChangeL 𝕜 e` are `C^n` on the overlap of
the base sets. Hence a linear trivialization lies in the maximal atlas exactly when its
coordinate changes with every trivialization of the bundle's atlas are `C^n` gauges, and the
coordinate changes between any two members of the maximal atlas are `C^n`.

Changes of frame are gauge transforms. `Bundle.Trivialization.transFiberwiseLinear` modifies a
trivialization `e` by a family `φ : B → F ≃L[𝕜] F`, and a gauge transform of a member of the
maximal atlas is again a member exactly when `φ` and its fibrewise inverse are `C^n` on the base
set. Finally, the smoothness criteria for maps into the total space and for sections, which
Mathlib states for trivializations of the bundle's atlas, hold verbatim for every member of the
maximal atlas.

## Main results

* `Bundle.Trivialization.symm_trans_mem_contMDiffFiberwiseLinear_iff`: the coordinate change
  between two linear trivializations is bi-`C^n` fiberwise linear exactly when both fibrewise
  coordinate changes are `C^n` on the overlap.
* `Bundle.Trivialization.mem_maximalAtlas_contMDiffFiberwiseLinear_iff`: a linear trivialization
  lies in the maximal atlas exactly when its coordinate changes with the atlas are `C^n`.
* `Bundle.Trivialization.contMDiffOn_coordChangeL_of_mem_maximalAtlas`: coordinate changes
  between members of the maximal atlas are `C^n`.
* `Bundle.Trivialization.transFiberwiseLinear`: the gauge transform of a trivialization, with
  coordinate changes `Bundle.Trivialization.coordChangeL_transFiberwiseLinear_left` and
  `Bundle.Trivialization.coordChangeL_transFiberwiseLinear_right`.
* `Bundle.Trivialization.transFiberwiseLinear_mem_maximalAtlas_iff`: a gauge transform of a
  member of the maximal atlas is a member exactly when the gauge is bi-`C^n`.
* `Bundle.Trivialization.contMDiffWithinAt_iff_of_mem_maximalAtlas`,
  `Bundle.Trivialization.contMDiffAt_section_iff_of_mem_maximalAtlas`: smoothness of maps into
  the total space and of sections can be read off in any member of the maximal atlas.

## References

* Norman Steenrod, *The Topology of Fibre Bundles*, Princeton University Press, 1951,
  Part I, §§2–3 (coordinate bundles, coordinate transformations and equivalent atlases).
* Daniel Huybrechts, *Complex Geometry: An Introduction*, Springer, 2005, Section 2.2
  (holomorphic vector bundles and their holomorphic trivializations).
-/

public section

open Bundle Set Filter OpenPartialHomeomorph
open scoped Manifold Topology ContDiff

variable {𝕜 B F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [TopologicalSpace B]

namespace Bundle.Trivialization

/-! ### Gauge transforms of trivializations -/

section Gauge

variable {Z : Type*} [TopologicalSpace Z] {proj : Z → B} (e : Trivialization F proj)
  (φ : B → F ≃L[𝕜] F) (hφ : ContinuousOn (fun x ↦ (φ x : F →L[𝕜] F)) e.baseSet)
  (h2φ : ContinuousOn (fun x ↦ ((φ x).symm : F →L[𝕜] F)) e.baseSet)

/-- The gauge transform of a trivialization `e` by a family `φ` of continuous linear
automorphisms of the fibre, continuous with continuous inverse on `e.baseSet`: it sends `p` to
`((e p).1, φ (e p).1 (e p).2)`, and has the same base set as `e`. -/
def transFiberwiseLinear : Trivialization F proj where
  toOpenPartialHomeomorph := e.toOpenPartialHomeomorph.trans'
    (FiberwiseLinear.openPartialHomeomorph φ e.open_baseSet hφ h2φ) e.target_eq
  baseSet := e.baseSet
  open_baseSet := e.open_baseSet
  source_eq := e.source_eq
  target_eq := rfl
  proj_toFun := e.proj_toFun

@[simp]
theorem transFiberwiseLinear_apply (p : Z) :
    e.transFiberwiseLinear φ hφ h2φ p = ((e p).1, φ (e p).1 (e p).2) :=
  (rfl)

@[simp]
theorem transFiberwiseLinear_symm_apply (x : B × F) :
    (e.transFiberwiseLinear φ hφ h2φ).toOpenPartialHomeomorph.symm x =
      e.toOpenPartialHomeomorph.symm (x.1, (φ x.1).symm x.2) :=
  (rfl)

@[simp]
theorem baseSet_transFiberwiseLinear : (e.transFiberwiseLinear φ hφ h2φ).baseSet = e.baseSet :=
  (rfl)

end Gauge

variable {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ x, AddCommMonoid (E x)]
  [∀ x, Module 𝕜 (E x)]

section Gauge

variable (e : Trivialization F (π F E)) (φ : B → F ≃L[𝕜] F)
  (hφ : ContinuousOn (fun x ↦ (φ x : F →L[𝕜] F)) e.baseSet)
  (h2φ : ContinuousOn (fun x ↦ ((φ x).symm : F →L[𝕜] F)) e.baseSet)

/-- A gauge transform of a linear trivialization is linear. -/
instance isLinear_transFiberwiseLinear [e.IsLinear 𝕜] :
    (e.transFiberwiseLinear φ hφ h2φ).IsLinear 𝕜 where
  linear b hb := by
    refine ⟨fun v w ↦ ?_, fun c v ↦ ?_⟩ <;>
      simp [e.coe_coe_fst hb, (e.linear 𝕜 hb).map_add, (e.linear 𝕜 hb).map_smul]

variable (e' : Trivialization F (π F E)) [e.IsLinear 𝕜] [e'.IsLinear 𝕜] {b : B}

/-- The coordinate change out of a gauge transform first undoes the gauge. -/
theorem coordChangeL_transFiberwiseLinear_left (hb : b ∈ e.baseSet ∩ e'.baseSet) :
    (e.transFiberwiseLinear φ hφ h2φ).coordChangeL 𝕜 e' b =
      (φ b).symm.trans (e.coordChangeL 𝕜 e' b) := by
  ext v
  rw [coordChangeL_apply' (R := 𝕜) (e.transFiberwiseLinear φ hφ h2φ) e' hb,
    transFiberwiseLinear_symm_apply, ContinuousLinearEquiv.trans_apply, coordChangeL_apply' _ _ hb]

/-- The coordinate change into a gauge transform applies the gauge last. -/
theorem coordChangeL_transFiberwiseLinear_right (hb : b ∈ e'.baseSet ∩ e.baseSet) :
    e'.coordChangeL 𝕜 (e.transFiberwiseLinear φ hφ h2φ) b =
      (e'.coordChangeL 𝕜 e b).trans (φ b) := by
  ext v
  rw [coordChangeL_apply' (R := 𝕜) e' (e.transFiberwiseLinear φ hφ h2φ) hb,
    transFiberwiseLinear_apply, e'.apply_symm_apply_eq_coordChangeL (R := 𝕜) e hb,
    ContinuousLinearEquiv.trans_apply]

end Gauge

/-! ### Membership in the groupoid of fiberwise linear maps -/

variable {EB HB : Type*} [NormedAddCommGroup EB] [NormedSpace 𝕜 EB] [TopologicalSpace HB]
  [ChartedSpace HB B] {IB : ModelWithCorners 𝕜 EB HB} {n : ℕ∞ω}

/-- The coordinate change `e.symm ≫ₕ e'` between two linear trivializations is a bi-`C^n`
fiberwise linear map exactly when the fibrewise coordinate changes in both directions are `C^n`
on the overlap of the base sets. -/
theorem symm_trans_mem_contMDiffFiberwiseLinear_iff (e e' : Trivialization F (π F E))
    [e.IsLinear 𝕜] [e'.IsLinear 𝕜] :
    e.toOpenPartialHomeomorph.symm ≫ₕ e'.toOpenPartialHomeomorph ∈
        contMDiffFiberwiseLinear B F IB n ↔
      ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b ↦ (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
          (e.baseSet ∩ e'.baseSet) ∧
        ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b ↦ (e'.coordChangeL 𝕜 e b : F →L[𝕜] F))
          (e.baseSet ∩ e'.baseSet) := by
  have hsource : (e.toOpenPartialHomeomorph.symm ≫ₕ e'.toOpenPartialHomeomorph).source =
      (e.baseSet ∩ e'.baseSet) ×ˢ univ := by
    simp only [trans_toPartialEquiv, symm_toPartialEquiv, e.symm_trans_source_eq e']
  have hsymm : ∀ b ∈ e.baseSet ∩ e'.baseSet,
      ((e.coordChangeL 𝕜 e' b).symm : F →L[𝕜] F) = e'.coordChangeL 𝕜 e b :=
    fun b hb ↦ by rw [e.symm_coordChangeL e' (inter_comm _ _ ▸ hb)]
  rw [mem_contMDiffFiberwiseLinear_iff]
  constructor
  · rintro ⟨φ, U, hU, hφ, h2φ, heφ⟩
    -- The gauge `φ` agrees with the coordinate change on the overlap, which is its domain `U`.
    have hU : U = e.baseSet ∩ e'.baseSet := by
      ext b
      have := congrArg ((b, (0 : F)) ∈ ·) (heφ.source_eq.symm.trans hsource)
      simpa [FiberwiseLinear.openPartialHomeomorph] using this
    subst hU
    have hφe : ∀ b ∈ e.baseSet ∩ e'.baseSet, φ b = e.coordChangeL 𝕜 e' b := fun b hb ↦ by
      ext v
      have := heφ.eqOn (x := (b, v)) (by rw [hsource]; exact ⟨hb, mem_univ v⟩)
      rw [coe_trans, Function.comp_apply, coe_coe,
        e.apply_symm_apply_eq_coordChangeL (R := 𝕜) e' hb] at this
      exact (congrArg Prod.snd this).symm
    refine ⟨hφ.congr fun b hb ↦ by rw [hφe b hb], h2φ.congr fun b hb ↦ ?_⟩
    rw [← hsymm b hb, hφe b hb]
  · rintro ⟨h, h'⟩
    refine ⟨_, _, e.open_baseSet.inter e'.open_baseSet, h,
      h'.congr fun b hb ↦ hsymm b hb, eqOnSourceSetoid.symm ⟨?_, ?_⟩⟩
    · -- The source of `FiberwiseLinear.openPartialHomeomorph` is `U ×ˢ univ` by definition.
      rw [hsource]
      rfl
    · rintro ⟨b, v⟩ hb
      exact (e.apply_symm_apply_eq_coordChangeL e' hb.1 v).symm

/-! ### The maximal atlas -/

variable [∀ x, TopologicalSpace (E x)] [FiberBundle F E]

variable {e e' : Trivialization F (π F E)} [e.IsLinear 𝕜] [e'.IsLinear 𝕜]

/-- The fibrewise coordinate change between two members of the maximal atlas of `C^n`
trivializations is `C^n` on the overlap of their base sets. -/
theorem contMDiffOn_coordChangeL_of_mem_maximalAtlas
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    (he' : e'.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E)) :
    ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b ↦ (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
      (e.baseSet ∩ e'.baseSet) :=
  ((symm_trans_mem_contMDiffFiberwiseLinear_iff e e').1
    (StructureGroupoid.compatible_of_mem_maximalAtlas he he')).1

/-- The fibrewise coordinate change between two members of the maximal atlas of `C^n`
trivializations is `C^n` at every point of the overlap of their base sets. -/
theorem contMDiffAt_coordChangeL_of_mem_maximalAtlas
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    (he' : e'.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    {b : B} (hb : b ∈ e.baseSet) (hb' : b ∈ e'.baseSet) :
    ContMDiffAt IB 𝓘(𝕜, F →L[𝕜] F) n (fun b ↦ (e.coordChangeL 𝕜 e' b : F →L[𝕜] F)) b :=
  (contMDiffOn_coordChangeL_of_mem_maximalAtlas he he').contMDiffAt
    ((e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨hb, hb'⟩)

variable {EM HM : Type*} [NormedAddCommGroup EM] [NormedSpace 𝕜 EM] [TopologicalSpace HM]
  {IM : ModelWithCorners 𝕜 EM HM} {M : Type*} [TopologicalSpace M] [ChartedSpace HM M]
  {f : M → TotalSpace F E} {s : Set M} {x₀ : M}

/-- A map into the total space whose base map is `C^n` and whose fibre coordinate in one member
of the maximal atlas of `C^n` trivializations is `C^n` has `C^n` fibre coordinate in every other
member whose source contains the point. -/
theorem _root_.ContMDiffWithinAt.change_section_trivialization_of_mem_maximalAtlas
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    (he' : e'.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    (hp : ContMDiffWithinAt IM IB n (π F E ∘ f) s x₀)
    (hf : ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e (f y)).2) s x₀)
    (hx : f x₀ ∈ e.source) (hx' : f x₀ ∈ e'.source) :
    ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun y ↦ (e' (f y)).2) s x₀ := by
  rw [mem_source] at hx hx'
  refine (((contMDiffAt_coordChangeL_of_mem_maximalAtlas he he' hx hx').comp_contMDiffWithinAt
    x₀ hp).clm_apply hf).congr_of_eventuallyEq ?_ ?_
  · filter_upwards [hp.continuousWithinAt
      ((e.open_baseSet.inter e'.open_baseSet).mem_nhds ⟨hx, hx'⟩)] with y hy
    simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    have hy : (f y).proj ∈ e.baseSet ∩ e'.baseSet := hy
    rw [coordChangeL_apply' _ _ hy, e.symm_apply_mk_proj (e.mem_source.2 hy.1)]
  · simp only [Function.comp_apply, ContinuousLinearEquiv.coe_coe]
    rw [coordChangeL_apply' _ _ ⟨hx, hx'⟩, e.symm_apply_mk_proj (e.mem_source.2 hx)]

variable [VectorBundle 𝕜 F E]

variable (IB n) in
/-- A linear trivialization lies in the maximal atlas of `C^n` trivializations exactly when its
fibrewise coordinate changes with every trivialization of the bundle's atlas, in both directions,
are `C^n` on the overlaps of the base sets. -/
theorem mem_maximalAtlas_contMDiffFiberwiseLinear_iff (e : Trivialization F (π F E))
    [e.IsLinear 𝕜] :
    e.toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E) ↔
      ∀ (e' : Trivialization F (π F E)) [MemTrivializationAtlas e'],
        ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b ↦ (e.coordChangeL 𝕜 e' b : F →L[𝕜] F))
            (e.baseSet ∩ e'.baseSet) ∧
          ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun b ↦ (e'.coordChangeL 𝕜 e b : F →L[𝕜] F))
            (e.baseSet ∩ e'.baseSet) := by
  rw [mem_maximalAtlas_iff]
  constructor
  · intro h e' he'
    exact (symm_trans_mem_contMDiffFiberwiseLinear_iff e e').1
      (h _ ⟨e', he'.out, rfl⟩).1
  · rintro h _ ⟨e', he', rfl⟩
    have : MemTrivializationAtlas e' := ⟨he'⟩
    obtain ⟨h₁, h₂⟩ := h e'
    rw [symm_trans_mem_contMDiffFiberwiseLinear_iff, symm_trans_mem_contMDiffFiberwiseLinear_iff,
      inter_comm e'.baseSet]
    exact ⟨⟨h₁, h₂⟩, h₂, h₁⟩

variable (IB n) in
/-- Every trivialization of the atlas of a `C^n` vector bundle lies in the maximal atlas of `C^n`
trivializations. Unlike `StructureGroupoid.subset_maximalAtlas`, this needs no manifold structure
on the base. -/
theorem mem_maximalAtlas_of_memTrivializationAtlas [ContMDiffVectorBundle n F E IB]
    (e : Trivialization F (π F E)) [MemTrivializationAtlas e] :
    e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E) :=
  (mem_maximalAtlas_contMDiffFiberwiseLinear_iff IB n e).2 fun e' _ ↦
    ⟨contMDiffOn_coordChangeL e e', inter_comm e.baseSet _ ▸ contMDiffOn_coordChangeL e' e⟩

/-- A gauge transform of a member of the maximal atlas of `C^n` trivializations is again a member
exactly when the gauge and its fibrewise inverse are `C^n` on the base set. -/
theorem transFiberwiseLinear_mem_maximalAtlas_iff
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    (φ : B → F ≃L[𝕜] F) (hφ : ContinuousOn (fun x ↦ (φ x : F →L[𝕜] F)) e.baseSet)
    (h2φ : ContinuousOn (fun x ↦ ((φ x).symm : F →L[𝕜] F)) e.baseSet) :
    (e.transFiberwiseLinear φ hφ h2φ).toOpenPartialHomeomorph ∈
        (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E) ↔
      ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x ↦ (φ x : F →L[𝕜] F)) e.baseSet ∧
        ContMDiffOn IB 𝓘(𝕜, F →L[𝕜] F) n (fun x ↦ ((φ x).symm : F →L[𝕜] F)) e.baseSet := by
  set eφ := e.transFiberwiseLinear φ hφ h2φ
  constructor
  · -- The coordinate changes between `e` and its gauge transform are `φ` and its inverse.
    intro hφe
    have h₁ := contMDiffOn_coordChangeL_of_mem_maximalAtlas he hφe
    have h₂ := contMDiffOn_coordChangeL_of_mem_maximalAtlas hφe he
    simp only [eφ, baseSet_transFiberwiseLinear, inter_self] at h₁ h₂
    refine ⟨h₁.congr fun b hb ↦ ?_, h₂.congr fun b hb ↦ ?_⟩
    · rw [coordChangeL_transFiberwiseLinear_right _ _ _ _ _ ⟨hb, hb⟩]
      ext v
      rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.trans_apply, coordChangeL_apply' _ _ ⟨hb, hb⟩,
        e.apply_symm_apply' hb]
    · rw [coordChangeL_transFiberwiseLinear_left _ _ _ _ _ ⟨hb, hb⟩]
      ext v
      rw [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.trans_apply, coordChangeL_apply' _ _ ⟨hb, hb⟩,
        e.apply_symm_apply' hb]
  · -- The coordinate changes of the gauge transform with the atlas compose those of `e` with
    -- the gauge.
    rintro ⟨h, h'⟩
    rw [mem_maximalAtlas_contMDiffFiberwiseLinear_iff] at he ⊢
    intro e' _
    obtain ⟨h₁, h₂⟩ := he e'
    refine ⟨(h₁.clm_comp (h'.mono inter_subset_left)).congr fun b hb ↦ ?_,
      ((h.mono inter_subset_left).clm_comp h₂).congr fun b hb ↦ ?_⟩
    · rw [coordChangeL_transFiberwiseLinear_left _ _ _ _ _ hb, ← ContinuousLinearEquiv.comp_coe]
    · rw [coordChangeL_transFiberwiseLinear_right _ _ _ _ _ (inter_comm _ _ ▸ hb),
        ← ContinuousLinearEquiv.comp_coe]

/-! ### Smoothness read in a member of the maximal atlas -/

variable [ContMDiffVectorBundle n F E IB]

/-- A map into the total space of a `C^n` vector bundle is `C^n` within a set at a point exactly
when its base map and its fibre coordinate in a member of the maximal atlas of `C^n`
trivializations, whose source contains the point, are. -/
theorem contMDiffWithinAt_iff_of_mem_maximalAtlas
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    (hx : f x₀ ∈ e.source) :
    ContMDiffWithinAt IM (IB.prod 𝓘(𝕜, F)) n f s x₀ ↔
      ContMDiffWithinAt IM IB n (fun x ↦ (f x).proj) s x₀ ∧
        ContMDiffWithinAt IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) s x₀ := by
  set e₀ := trivializationAt F E (f x₀).proj
  have he₀ := mem_maximalAtlas_of_memTrivializationAtlas IB n e₀
  have hx₀ : f x₀ ∈ e₀.source := FiberBundle.mem_trivializationAt_proj_source
  rw [e₀.contMDiffWithinAt_iff hx₀]
  exact and_congr_right fun hp ↦
    ⟨(hp.change_section_trivialization_of_mem_maximalAtlas he₀ he · hx₀ hx),
      (hp.change_section_trivialization_of_mem_maximalAtlas he he₀ · hx hx₀)⟩

/-- A map into the total space of a `C^n` vector bundle is `C^n` at a point exactly when its base
map and its fibre coordinate in a member of the maximal atlas of `C^n` trivializations, whose
source contains the point, are. -/
theorem contMDiffAt_iff_of_mem_maximalAtlas
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    (hx : f x₀ ∈ e.source) :
    ContMDiffAt IM (IB.prod 𝓘(𝕜, F)) n f x₀ ↔
      ContMDiffAt IM IB n (fun x ↦ (f x).proj) x₀ ∧
        ContMDiffAt IM 𝓘(𝕜, F) n (fun x ↦ (e (f x)).2) x₀ :=
  Trivialization.contMDiffWithinAt_iff_of_mem_maximalAtlas he hx

/-- A section of a `C^n` vector bundle is `C^n` within a set at a point of the base set of a member
of the maximal atlas of `C^n` trivializations exactly when its coordinate in that member is. -/
theorem contMDiffWithinAt_section_iff_of_mem_maximalAtlas
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    {σ : ∀ x, E x} {a : Set B} {b₀ : B} (hb₀ : b₀ ∈ e.baseSet) :
    ContMDiffWithinAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (σ x)) a b₀ ↔
      ContMDiffWithinAt IB 𝓘(𝕜, F) n (fun x ↦ (e ⟨x, σ x⟩).2) a b₀ := by
  rw [Trivialization.contMDiffWithinAt_iff_of_mem_maximalAtlas
    (IM := IB) (f := fun x ↦ TotalSpace.mk' F x (σ x)) he
    ((e.mem_source (x := TotalSpace.mk' F b₀ (σ b₀))).2 hb₀)]
  exact and_iff_right contMDiffWithinAt_id

/-- A section of a `C^n` vector bundle is `C^n` at a point of the base set of a member of the
maximal atlas of `C^n` trivializations exactly when its coordinate in that member is. -/
theorem contMDiffAt_section_iff_of_mem_maximalAtlas
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    {σ : ∀ x, E x} {b₀ : B} (hb₀ : b₀ ∈ e.baseSet) :
    ContMDiffAt IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (σ x)) b₀ ↔
      ContMDiffAt IB 𝓘(𝕜, F) n (fun x ↦ (e ⟨x, σ x⟩).2) b₀ :=
  contMDiffWithinAt_section_iff_of_mem_maximalAtlas he hb₀

/-- A section of a `C^n` vector bundle is `C^n` on an open subset of the base set of a member of
the maximal atlas of `C^n` trivializations exactly when its coordinate in that member is. -/
theorem contMDiffOn_section_iff_of_mem_maximalAtlas
    (he : e.toOpenPartialHomeomorph ∈
      (contMDiffFiberwiseLinear B F IB n).maximalAtlas (TotalSpace F E))
    {σ : ∀ x, E x} {a : Set B} (ha : IsOpen a) (ha' : a ⊆ e.baseSet) :
    ContMDiffOn IB (IB.prod 𝓘(𝕜, F)) n (fun x ↦ TotalSpace.mk' F x (σ x)) a ↔
      ContMDiffOn IB 𝓘(𝕜, F) n (fun x ↦ (e ⟨x, σ x⟩).2) a := by
  refine ⟨fun h x hx ↦ ?_, fun h x hx ↦ ?_⟩ <;>
  have := (h x hx).contMDiffAt <| ha.mem_nhds hx
  · exact ((contMDiffAt_section_iff_of_mem_maximalAtlas he (ha' hx)).mp this).contMDiffWithinAt
  · exact ((contMDiffAt_section_iff_of_mem_maximalAtlas he (ha' hx)).mpr this).contMDiffWithinAt

end Bundle.Trivialization
