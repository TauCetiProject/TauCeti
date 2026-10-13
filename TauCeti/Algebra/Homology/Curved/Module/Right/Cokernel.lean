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
# Cokernels of closed maps of curved right modules

The cokernel of a closed map is the quotient by its image, with the quotient grading and the
induced differential. The image is stable under the differential because the map is closed.
The Leibniz and curvature laws descend to the quotient, and its projection is a cokernel in
the existing closed category.

The quotient grading reuses `TauCeti.GradedModuleCat.cokernelObj`. The factorization proof
adapts `TauCeti.GradedModuleCat.cokernelIsColimit`, adding differential compatibility. These
cokernels are a prerequisite for the graded-split exact structure.

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

/-- The target differential induces a differential on the quotient by the image. -/
noncomputable def cokernelDifferential : (N ⧸ LinearMap.range (closedHom f)) →ₗ[R]
    N ⧸ LinearMap.range (closedHom f) :=
  (((LinearMap.range (closedHom f)).restrictScalars R).liftQ
    (((LinearMap.range (closedHom f)).mkQ.restrictScalars R).comp N.differential)
    (fun x hx ↦ by
      obtain ⟨y, rfl⟩ := (LinearMap.mem_range).mp hx
      -- Evaluate the restricted quotient map on a representative of the image.
      change Submodule.Quotient.mk (N.differential (closedHom f y)) = 0
      rw [differential_closedHom]
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨M.differential y, rfl⟩)).comp
    (Submodule.Quotient.restrictScalarsEquiv R (LinearMap.range (closedHom f))).symm.toLinearMap

/-- The induced differential sends the class of `x` to the class of its differential. -/
@[simp]
theorem cokernelDifferential_mk (x : N) :
    cokernelDifferential f (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (N.differential x) := by
  simp only [cokernelDifferential, LinearMap.comp_apply, LinearEquiv.coe_coe,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.liftQ_apply,
    LinearMap.restrictScalars_apply, Submodule.mkQ_apply]

/-- The curved module carried by the quotient of the target by the image of a closed map. -/
@[expose, implicit_reducible]
noncomputable def cokernelModule : CurvedDGRightModuleCat.{u, u, u} h := by
  let Q := GradedModuleCat.cokernelObj ((forgetDifferential (h := h)).map f)
  letI : DirectSum.Decomposition Q.grading.piece := inferInstance
  letI : SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece Q.grading.piece :=
    Q.gradedSMul
  refine
    { carrier := N ⧸ LinearMap.range (closedHom f)
      grading := Q.grading.piece
      differential := cokernelDifferential f
      isCurvedDGRightModule := ?_ }
  refine ⟨?_, ?_, ?_⟩
  · apply LinearMap.isHomogeneous_def.mpr
    intro p x hx
    obtain ⟨y, hy, rfl⟩ := (GradedModuleCat.mem_cokernelGrading_piece_iff _).mp hx
    -- The existing quotient grading chooses a homogeneous representative in the target.
    change y ∈ (toGradedModuleCat N).grading.piece p at hy
    rw [toGradedModuleCat_piece] at hy
    rw [cokernelDifferential_mk]
    apply (GradedModuleCat.mem_cokernelGrading_piece_iff _).mpr
    refine ⟨N.differential y, ?_, rfl⟩
    change N.differential y ∈ (toGradedModuleCat N).grading.piece (p + 1)
    rw [toGradedModuleCat_piece]
    exact N.isCurvedDGRightModule.isHomogeneous.map_mem hy
  · intro p x hx a
    obtain ⟨y, hy, rfl⟩ := (GradedModuleCat.mem_cokernelGrading_piece_iff _).mp hx
    -- Read that representative's degree in the original target before applying its Leibniz rule.
    change y ∈ (toGradedModuleCat N).grading.piece p at hy
    rw [toGradedModuleCat_piece] at hy
    simp only [← Submodule.Quotient.mk_smul]
    erw [cokernelDifferential_mk, cokernelDifferential_mk]
    rw [← Submodule.Quotient.mk_smul, N.isCurvedDGRightModule.leibniz hy a]
    exact map_add ((LinearMap.range (closedHom f)).mkQ) _ _
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [cokernelDifferential_mk, cokernelDifferential_mk,
        N.isCurvedDGRightModule.sq_eq, Submodule.Quotient.mk_smul]

/-- Homogeneous elements of the curved cokernel are classes of homogeneous target elements. -/
@[simp]
theorem mem_cokernelModule_grading_iff {p : ℤ} {x : N ⧸ LinearMap.range (closedHom f)} :
    x ∈ (cokernelModule f).grading p ↔
      ∃ y ∈ N.grading p, Submodule.Quotient.mk y = x := by
  -- The curved cokernel retains the existing graded quotient's homogeneous pieces.
  change x ∈ (GradedModuleCat.cokernelGrading ((forgetDifferential (h := h)).map f)).piece p ↔ _
  rw [GradedModuleCat.mem_cokernelGrading_piece_iff]
  change (∃ y ∈ (toGradedModuleCat N).grading.piece p, Submodule.Quotient.mk y = x) ↔ _
  rw [toGradedModuleCat_piece]
  rfl

/-- The projection onto the curved cokernel is a closed map. -/
noncomputable def cokernelProjection :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cokernelModule f) :=
  closedHomOf (LinearMap.range (closedHom f)).mkQ
    (fun _ x hx ↦ (mem_cokernelModule_grading_iff f).mpr ⟨x, hx, rfl⟩)
    (fun x ↦ cokernelDifferential_mk f x)

/-- The underlying cokernel projection is the quotient map. -/
@[simp]
theorem closedHom_cokernelProjection :
    closedHom (cokernelProjection f) = (LinearMap.range (closedHom f)).mkQ := by
  dsimp only [cokernelProjection]
  exact closedHom_closedHomOf _ _ _

/-- The original map followed by its cokernel projection is zero. -/
@[reassoc (attr := simp)]
theorem comp_cokernelProjection : f ≫ cokernelProjection f = 0 := by
  apply closedHom_ext
  intro x
  simp only [closedHom_comp, closedHom_cokernelProjection, closedHom_zero, LinearMap.comp_apply,
    LinearMap.zero_apply]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

/-- The cokernel cofork in the closed category of curved right modules. -/
@[expose]
noncomputable def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelProjection f) (comp_cokernelProjection f)

/-- The curved cokernel projection satisfies the cokernel universal property. -/
noncomputable def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  CokernelCofork.IsColimit.ofπ (cokernelProjection f) (comp_cokernelProjection f)
    (fun g hg ↦ closedHomOf
      ((LinearMap.range (closedHom f)).liftQ (closedHom g) fun x hx ↦ by
        obtain ⟨y, rfl⟩ := (LinearMap.mem_range).mp hx
        apply LinearMap.mem_ker.mpr
        have hs := congrArg (fun l ↦ closedHom l y) hg
        simpa only [closedHom_comp, LinearMap.comp_apply, closedHom_zero, LinearMap.zero_apply]
          using hs)
      (fun _ x hx ↦ by
        obtain ⟨y, hy, rfl⟩ := (mem_cokernelModule_grading_iff f).mp hx
        rw [Submodule.liftQ_apply]
        exact closedHom_mem g hy)
      (fun x ↦ by
        induction x using Submodule.Quotient.induction_on with
        | _ x =>
          erw [cokernelDifferential_mk]
          exact differential_closedHom g x))
    (fun g hg ↦ by
      apply closedHom_ext
      intro x
      erw [closedHom_comp, closedHom_cokernelProjection, closedHom_closedHomOf]
      rfl)
    (fun g hg m hm ↦ by
      apply closedHom_ext
      intro x
      induction x using Submodule.Quotient.induction_on with
      | _ x =>
        have hs := congrArg (fun l ↦ closedHom l x) hm
        simp only [closedHom_comp, LinearMap.comp_apply, closedHom_cokernelProjection] at hs
        erw [closedHom_closedHomOf]
        exact hs)

noncomputable instance : HasCokernels
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  ⟨fun f ↦ HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

/-- Forgetting the differential of the curved cokernel gives the usual graded cokernel. -/
noncomputable def forgetDifferentialCokernelIso :
    (forgetDifferential (h := h)).obj
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cokernelModule f)) ≅
      GradedModuleCat.cokernelObj ((forgetDifferential (h := h)).map f) :=
  GradedModuleCat.isoMk (LinearEquiv.refl Aᵐᵒᵖ (N ⧸ LinearMap.range (closedHom f))) fun p x ↦ by
    -- Forgetting the differential recovers exactly the inherited quotient grading.
    change x ∈ (toGradedModuleCat (cokernelModule f)).grading.piece p ↔ _
    rw [toGradedModuleCat_piece]
    rfl

/-- The graded forgetful functor preserves the cokernel of a closed map. -/
noncomputable instance : PreservesColimit (parallelPair f 0) (forgetDifferential (h := h)) := by
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
    (((cokernelCocone f).isColimitMapCoconeEquiv (forgetDifferential (h := h))).symm ?_)
  let e : (cokernelCocone f).map (forgetDifferential (h := h)) ≅
      GradedModuleCat.cokernelCocone ((forgetDifferential (h := h)).map f) :=
    Cofork.ext (forgetDifferentialCokernelIso f) (by
      apply GradedModuleCat.hom_ext
      -- The comparison is the identity on the quotient, so evaluate its underlying composition.
      change LinearMap.id.comp (closedHom (cokernelProjection f)) =
        (LinearMap.range (closedHom f)).mkQ
      rw [LinearMap.id_comp, closedHom_cokernelProjection])
  exact (IsColimit.equivIsoColimit e).symm
    (GradedModuleCat.cokernelIsColimit ((forgetDifferential (h := h)).map f))

end TauCeti.CurvedDGRightModuleCat
