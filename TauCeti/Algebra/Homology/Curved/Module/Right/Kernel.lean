/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian

/-!
# Kernels of closed maps of curved right modules

The kernel of a closed map has the inherited grading and the restricted differential. The
closedness of the map makes its kernel stable under the differential; the Leibniz and curvature
laws restrict to this submodule. Its inclusion is a kernel in the existing closed category.

`kernelEquiv` identifies the carrier of `kernelObj` with the kernel submodule and provides its
inherited right action. The grading and differential equations characterize this curved
object, and `kernelIsLimit` gives the universal property of its inclusion `kernelι`.
`forgetDifferentialKernelIso` identifies its underlying graded object with the graded kernel.
These kernels and their preservation are used by the graded-split exact structure.

## References

* The Tau Ceti contributors, `TauCeti.Algebra.Category.GradedModuleCat.Abelian`.
* L. Positselski, *Differential graded Koszul duality: an introductory survey*, Section 7.6.
-/

public section

open CategoryTheory CategoryTheory.Limits MulOpposite

namespace TauCeti.CurvedDGRightModuleCat

universe u

-- Closed objects keep the original curved-module carrier.
attribute [local implicit_reducible] ForgetEnrichment

variable {R A : Type u} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {w : A}
  {h : IsCurvedDGAlgebra 𝒜 d w} {M N : CurvedDGRightModuleCat.{u, u, u} h}
  (f : ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M ⟶
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N)

/-- The differential restricted to the kernel of a closed map. -/
noncomputable def kernelDifferential : LinearMap.ker (closedHom f) →ₗ[R]
    LinearMap.ker (closedHom f) :=
  LinearMap.codRestrict ((LinearMap.ker (closedHom f)).restrictScalars R)
    (M.differential.comp ((LinearMap.ker (closedHom f)).subtype.restrictScalars R))
    (fun x ↦ by
      simp only [Submodule.restrictScalars_mem, LinearMap.mem_ker, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply, Submodule.subtype_apply]
      rw [← differential_closedHom, x.2, map_zero])

/-- The restricted differential is the source differential on underlying elements. -/
@[simp]
theorem coe_kernelDifferential (x : LinearMap.ker (closedHom f)) :
    (kernelDifferential f x : M) = M.differential x :=
  (rfl)

/-- The reused graded kernel has exactly the source's homogeneous pieces on its subtype. -/
private theorem mem_gradedKernel_piece_iff {p : ℤ} {x : LinearMap.ker (closedHom f)} :
    x ∈ (GradedModuleCat.kernelObj ((forgetDifferential (h := h)).map f)).grading.piece p ↔
      (x : M) ∈ M.grading p := by
  simp only [GradedModuleCat.kernelObj, InternalGrading.mem_ker_piece]
  -- The element is typed through the kernel subtype of the forgetful object. Rewriting
  -- that object equality would change its dependent element type; align this foreign
  -- carrier once in the helper, then use the public grading equation.
  change (x : M) ∈ (toGradedModuleCat M).grading.piece p ↔ (x : M) ∈ M.grading p
  rw [toGradedModuleCat_piece]

/-- The curved module carried by the kernel of a closed map. -/
noncomputable def kernelObj : CurvedDGRightModuleCat.{u, u, u} h := by
  let K := GradedModuleCat.kernelObj ((forgetDifferential (h := h)).map f)
  letI : DirectSum.Decomposition K.grading.piece := inferInstance
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece K.grading.piece :=
    K.gradedSMul
  refine
    { carrier := LinearMap.ker (closedHom f)
      grading := K.grading.piece
      differential := kernelDifferential f
      isCurvedDGRightModule := ?_ }
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.isHomogeneous_def.mpr
    intro p x hx
    apply (mem_gradedKernel_piece_iff f).mpr
    simpa only [coe_kernelDifferential] using
      M.isCurvedDGRightModule.isHomogeneous.map_mem ((mem_gradedKernel_piece_iff f).mp hx)
  · intro p x hx a
    apply Subtype.ext
    simpa only [coe_kernelDifferential, Units.smul_def, Submodule.coe_smul,
      Submodule.coe_smul_of_tower, Submodule.coe_add] using
      M.isCurvedDGRightModule.leibniz ((mem_gradedKernel_piece_iff f).mp hx) a
  · intro x
    apply Subtype.ext
    simpa only [coe_kernelDifferential, Submodule.coe_smul] using
      M.isCurvedDGRightModule.sq_eq x.1

/-- The kernel carrier is the kernel submodule. Its linearity characterizes the inherited
right action; consumers use this equivalence rather than unfolding `kernelObj`. -/
noncomputable def kernelEquiv : kernelObj f ≃ₗ[Aᵐᵒᵖ] LinearMap.ker (closedHom f) :=
  LinearEquiv.refl Aᵐᵒᵖ (LinearMap.ker (closedHom f))

/-- The kernel's differential corresponds to the restricted source differential. -/
@[simp]
theorem kernelEquiv_differential (x : kernelObj f) :
    kernelEquiv f ((kernelObj f).differential x) = kernelDifferential f (kernelEquiv f x) :=
  (rfl)

/-- Homogeneity in the curved kernel is homogeneity in the source under its carrier comparison. -/
@[simp]
theorem mem_kernelObj_grading_iff {p : ℤ} {x : kernelObj f} :
    x ∈ (kernelObj f).grading p ↔ (kernelEquiv f x : M) ∈ M.grading p :=
  mem_gradedKernel_piece_iff f

/-- The inclusion of the curved kernel is a closed map. -/
noncomputable def kernelι :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (kernelObj f) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M :=
  closedHomOf ((LinearMap.ker (closedHom f)).subtype.comp (kernelEquiv f).toLinearMap)
    (fun _ _ hx ↦ (mem_kernelObj_grading_iff f).mp hx)
    (fun x ↦ by
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, Submodule.subtype_apply,
        kernelEquiv_differential, coe_kernelDifferential])

/-- The underlying kernel inclusion is its carrier comparison followed by subtype inclusion. -/
@[simp]
theorem hom_kernelι :
    closedHom (kernelι f) =
      (LinearMap.ker (closedHom f)).subtype.comp (kernelEquiv f).toLinearMap := by
  dsimp only [kernelι]
  exact closedHom_closedHomOf _ _ _

/-- The kernel inclusion followed by the original map is zero. -/
@[reassoc (attr := simp)]
theorem kernelι_comp : kernelι f ≫ f = 0 := by
  apply closedHom_ext
  intro x
  simp only [closedHom_comp, hom_kernelι, closedHom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply, LinearEquiv.coe_coe, Submodule.subtype_apply]
  exact (kernelEquiv f x).2

/-- The kernel fork in the closed category of curved right modules. -/
noncomputable def kernelCone : KernelFork f :=
  KernelFork.ofι (kernelι f) (kernelι_comp f)

/-- The point of the sealed kernel fork is the characteristic kernel object. -/
@[simp]
theorem kernelCone_pt : (kernelCone f).pt =
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (kernelObj f) :=
  (rfl)

/-- The kernel fork's projection is the characteristic inclusion after identifying its point. -/
@[simp]
theorem kernelCone_ι : eqToHom (kernelCone_pt f).symm ≫ (kernelCone f).ι = kernelι f := by
  -- This is the defining constructor equation, including its point transport.
  change (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (kernelObj f))) ≫
    kernelι f = kernelι f
  exact Category.id_comp _

/-- The curved kernel inclusion satisfies the kernel universal property. -/
noncomputable def kernelIsLimit : IsLimit (kernelCone f) :=
  KernelFork.IsLimit.ofι (kernelι f) (kernelι_comp f)
    (fun g hg ↦ closedHomOf
      ((kernelEquiv f).symm.toLinearMap.comp
        (LinearMap.codRestrict (LinearMap.ker (closedHom f)) (closedHom g) fun x ↦ by
          rw [LinearMap.mem_ker]
          have hs := congrArg (fun l ↦ closedHom l x) hg
          simpa only [closedHom_comp, LinearMap.comp_apply, closedHom_zero, LinearMap.zero_apply]
            using hs))
      (fun _ _ hx ↦ (mem_kernelObj_grading_iff f).mpr (by
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
          LinearMap.codRestrict_apply] using closedHom_mem g hx))
      (fun x ↦ by
        apply (kernelEquiv f).injective
        apply Subtype.ext
        simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, kernelEquiv_differential,
          LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply, coe_kernelDifferential]
          using differential_closedHom g x))
    (fun g hg ↦ by
      apply closedHom_ext
      intro x
      simp only [closedHom_comp, hom_kernelι, closedHom_closedHomOf, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply,
        Submodule.subtype_apply])
    (fun g hg m hm ↦ by
      apply closedHom_ext
      intro x
      apply (kernelEquiv f).injective
      apply Subtype.ext
      have hs := congrArg (fun l ↦ closedHom l x) hm
      simp only [closedHom_comp, hom_kernelι, LinearMap.comp_apply, LinearEquiv.coe_coe,
        Submodule.subtype_apply] at hs
      simpa only [closedHom_closedHomOf, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply] using hs)

/-- The closed category of curved right modules has kernels. -/
noncomputable instance : HasKernels
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  ⟨fun f ↦ HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/-- Forgetting the differential of the curved kernel gives the usual graded kernel. -/
noncomputable def forgetDifferentialKernelIso :
    (forgetDifferential (h := h)).obj
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (kernelObj f)) ≅
      GradedModuleCat.kernelObj ((forgetDifferential (h := h)).map f) :=
  GradedModuleCat.isoMk (kernelEquiv f) fun p x ↦ by
    -- `isoMk` fixes the element's type in the forgetful object. Its object equality
    -- cannot rewrite this dependent predicate without a transport; reduce only that
    -- forgetful grading view, retaining the sealed kernel and its characteristic API.
    change x ∈ (toGradedModuleCat (kernelObj f)).grading.piece p ↔ _
    rw [toGradedModuleCat_piece]
    exact (mem_kernelObj_grading_iff f).trans (mem_gradedKernel_piece_iff f).symm

/-- The graded comparison is the kernel's characteristic carrier equivalence. -/
@[simp]
theorem forgetDifferentialKernelIso_hom_hom :
    (forgetDifferentialKernelIso f).hom.hom = (kernelEquiv f).toLinearMap := by
  simp only [forgetDifferentialKernelIso, GradedModuleCat.isoMk_hom_hom]

/-- The graded forgetful functor preserves the kernel of a closed map. -/
noncomputable instance : PreservesLimit (parallelPair f 0) (forgetDifferential (h := h)) := by
  refine preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
    (((kernelCone f).isLimitMapConeEquiv (forgetDifferential (h := h))).symm ?_)
  let e : (kernelCone f).map (forgetDifferential (h := h)) ≅
      GradedModuleCat.kernelCone ((forgetDifferential (h := h)).map f) :=
    Fork.ext (forgetDifferentialKernelIso f) (by
      apply GradedModuleCat.hom_ext
      rw [GradedModuleCat.hom_comp, forgetDifferentialKernelIso_hom_hom, KernelFork.map_ι]
      -- Rewriting the graded map's `hom` changes the subtype carrier while the target
      -- of `kernelEquiv` stays fixed; Lean rejects that dependent rewrite motive.
      -- Align only this foreign cone/forgetful boundary, then use the characteristic
      -- map equation. The sealed kernel object's construction is never unfolded.
      change (LinearMap.ker (closedHom f)).subtype.comp (kernelEquiv f).toLinearMap =
        closedHom (kernelι f)
      exact (hom_kernelι f).symm)
  exact (IsLimit.equivIsoLimit e).symm
    (GradedModuleCat.kernelIsLimit ((forgetDifferential (h := h)).map f))

end TauCeti.CurvedDGRightModuleCat
