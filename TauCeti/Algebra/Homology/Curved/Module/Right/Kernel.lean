/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded
public import TauCeti.Algebra.Homology.Curved.Module.Right.Biproduct
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian

/-!
# Kernels of closed maps of curved right modules

The kernel of a closed map has the inherited grading and the restricted differential. The
closedness of the map makes its kernel stable under the differential; the Leibniz and curvature
laws restrict to this submodule. Its inclusion is a kernel in the existing closed category.

The underlying grading reuses `TauCeti.GradedModuleCat.kernelObj`, and the universal-property
proof follows `TauCeti.GradedModuleCat.kernelIsLimit`, adding the differential compatibility
of the factorization. This is a prerequisite for the graded-split exact structure.

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
      -- Membership in the restricted kernel is the underlying closed map's zero equation.
      change closedHom f (M.differential x.1) = 0
      rw [← differential_closedHom, x.2, map_zero])

/-- The restricted differential is the source differential on underlying elements. -/
@[simp]
theorem coe_kernelDifferential (x : LinearMap.ker (closedHom f)) :
    (kernelDifferential f x : M) = M.differential x :=
  (rfl)

/-- The curved module carried by the kernel of a closed map. -/
@[expose, implicit_reducible]
noncomputable def kernelModule : CurvedDGRightModuleCat.{u, u, u} h := by
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
    simp only [K, GradedModuleCat.kernelObj, InternalGrading.mem_ker_piece] at hx ⊢
    -- The graded kernel uses the original source's pieces, restricted to its kernel subtype.
    change (x : M) ∈ (toGradedModuleCat M).grading.piece p at hx
    change (kernelDifferential f x : M) ∈ (toGradedModuleCat M).grading.piece (p + 1)
    rw [toGradedModuleCat_piece] at hx ⊢
    rw [coe_kernelDifferential]
    exact M.isCurvedDGRightModule.isHomogeneous.map_mem hx
  · intro p x hx a
    apply Subtype.ext
    simp only [coe_kernelDifferential, Submodule.coe_smul, Submodule.coe_add,
      K, GradedModuleCat.kernelObj, InternalGrading.mem_ker_piece] at hx ⊢
    -- Reduce the inherited grading and subtype operations to the source module's Leibniz rule.
    change (x : M) ∈ (toGradedModuleCat M).grading.piece p at hx
    rw [toGradedModuleCat_piece] at hx
    change M.differential (op a • x.1) =
      op a • M.differential x.1 + p.negOnePow • (op (d a) • x.1)
    exact M.isCurvedDGRightModule.leibniz hx a
  · intro x
    apply Subtype.ext
    simp only [coe_kernelDifferential, Submodule.coe_smul]
    exact M.isCurvedDGRightModule.sq_eq x.1

/-- Homogeneity in the curved kernel is homogeneity in the source. -/
@[simp]
theorem mem_kernelModule_grading_iff {p : ℤ} {x : LinearMap.ker (closedHom f)} :
    x ∈ (kernelModule f).grading p ↔ (x : M) ∈ M.grading p := by
  -- The curved kernel's grading is the existing graded kernel's restricted grading.
  change x ∈ (GradedModuleCat.kernelObj ((forgetDifferential (h := h)).map f)).grading.piece p ↔ _
  simp only [GradedModuleCat.kernelObj, InternalGrading.mem_ker_piece]
  change (x : M) ∈ (toGradedModuleCat M).grading.piece p ↔ _
  rw [toGradedModuleCat_piece]

/-- The inclusion of the curved kernel is a closed map. -/
noncomputable def kernelInclusion :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (kernelModule f) ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) M :=
  closedHomOf (LinearMap.ker (closedHom f)).subtype
    (fun _ _ hx ↦ (mem_kernelModule_grading_iff f).mp hx)
    (fun _ ↦ (coe_kernelDifferential f _).symm)

/-- The underlying kernel inclusion is the submodule inclusion. -/
@[simp]
theorem closedHom_kernelInclusion :
    closedHom (kernelInclusion f) = (LinearMap.ker (closedHom f)).subtype := by
  dsimp only [kernelInclusion]
  exact closedHom_closedHomOf _ _ _

/-- The kernel inclusion followed by the original map is zero. -/
@[reassoc (attr := simp)]
theorem kernelInclusion_comp : kernelInclusion f ≫ f = 0 := by
  apply closedHom_ext
  intro x
  simp only [closedHom_comp, closedHom_kernelInclusion, closedHom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply]
  exact x.2

/-- The kernel fork in the closed category of curved right modules. -/
@[expose]
noncomputable def kernelCone : KernelFork f :=
  KernelFork.ofι (kernelInclusion f) (kernelInclusion_comp f)

/-- The curved kernel inclusion satisfies the kernel universal property. -/
noncomputable def kernelIsLimit : IsLimit (kernelCone f) :=
  KernelFork.IsLimit.ofι (kernelInclusion f) (kernelInclusion_comp f)
    (fun g hg ↦ closedHomOf
      (LinearMap.codRestrict (LinearMap.ker (closedHom f)) (closedHom g) fun x ↦ by
        -- Evaluate kernel membership before using the fork's closed-map equation.
        change closedHom f (closedHom g x) = 0
        have hs := congrArg (fun l ↦ closedHom l x) hg
        simpa only [closedHom_comp, LinearMap.comp_apply, closedHom_zero, LinearMap.zero_apply]
          using hs)
      (fun _ _ hx ↦ (mem_kernelModule_grading_iff f).mpr (closedHom_mem g hx))
      (fun x ↦ by
        apply Subtype.ext
        exact differential_closedHom g x))
    (fun g hg ↦ by
      apply closedHom_ext
      intro x
      simp only [closedHom_comp, LinearMap.comp_apply, closedHom_kernelInclusion,
        closedHom_closedHomOf]
      rfl)
    (fun g hg m hm ↦ by
      apply closedHom_ext
      intro x
      apply Subtype.ext
      have hs := congrArg (fun l ↦ closedHom l x) hm
      simp only [closedHom_comp, LinearMap.comp_apply, closedHom_kernelInclusion] at hs
      erw [closedHom_closedHomOf]
      exact hs)

noncomputable instance : HasKernels
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  ⟨fun f ↦ HasLimit.mk ⟨_, kernelIsLimit f⟩⟩

/-- Forgetting the differential of the curved kernel gives the usual graded kernel. -/
noncomputable def forgetDifferentialKernelIso :
    (forgetDifferential (h := h)).obj
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (kernelModule f)) ≅
      GradedModuleCat.kernelObj ((forgetDifferential (h := h)).map f) :=
  GradedModuleCat.isoMk (LinearEquiv.refl Aᵐᵒᵖ (LinearMap.ker (closedHom f))) fun p x ↦ by
    -- Forgetting the differential recovers the graded kernel's chosen homogeneous pieces.
    change x ∈ (toGradedModuleCat (kernelModule f)).grading.piece p ↔ _
    rw [toGradedModuleCat_piece]
    rfl

/-- The graded forgetful functor preserves the kernel of a closed map. -/
noncomputable instance : PreservesLimit (parallelPair f 0) (forgetDifferential (h := h)) := by
  refine preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
    (((kernelCone f).isLimitMapConeEquiv (forgetDifferential (h := h))).symm ?_)
  let e : (kernelCone f).map (forgetDifferential (h := h)) ≅
      GradedModuleCat.kernelCone ((forgetDifferential (h := h)).map f) :=
    Fork.ext (forgetDifferentialKernelIso f) (by
      apply GradedModuleCat.hom_ext
      -- The comparison is the identity on the kernel subtype, so evaluate its map composition.
      change (LinearMap.ker (closedHom f)).subtype.comp LinearMap.id =
        closedHom (kernelInclusion f)
      rw [LinearMap.comp_id, closedHom_kernelInclusion])
  exact (IsLimit.equivIsoLimit e).symm
    (GradedModuleCat.kernelIsLimit ((forgetDifferential (h := h)).map f))

end TauCeti.CurvedDGRightModuleCat
