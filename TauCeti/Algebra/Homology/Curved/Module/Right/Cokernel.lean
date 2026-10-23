/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.Algebra.Homology.Curved.Module.Right.Graded
public import TauCeti.Algebra.Category.GradedModuleCat.Abelian

/-!
# Cokernels of closed maps of curved right modules

The cokernel of a closed map is the quotient by its image, with the quotient grading and the
induced differential. The image is stable under the differential because the map is closed.
The Leibniz and curvature laws descend to the quotient, and its projection is a cokernel in
the existing closed category.

`cokernelEquiv` identifies the carrier of `cokernelObj` with the range quotient and provides its
inherited right action. Its homogeneous elements are classes of homogeneous target elements,
and its differential sends the class of an element to the class of its differential.
`cokernelIsColimit` gives the universal property of the projection `cokernelπ`, and
`forgetDifferentialCokernelIso` gives the graded comparison. These cokernels and their
preservation are used by the graded-split exact structure.

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
      simp only [LinearMap.mem_ker, LinearMap.comp_apply,
        LinearMap.restrictScalars_apply, Submodule.mkQ_apply]
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

/-- The reused graded quotient consists of classes of homogeneous target elements. -/
private theorem mem_gradedCokernel_piece_iff {p : ℤ}
    {x : N ⧸ LinearMap.range (closedHom f)} :
    x ∈ (GradedModuleCat.cokernelObj ((forgetDifferential (h := h)).map f)).grading.piece p ↔
      ∃ y ∈ N.grading p, Submodule.Quotient.mk y = x := by
  dsimp only [GradedModuleCat.cokernelObj]
  rw [GradedModuleCat.mem_cokernelGrading_piece_iff]
  -- A representative is typed in the forgetful target's carrier. Rewriting its
  -- object equality changes that dependent type, so align the foreign grading
  -- view once here before using the public equation for its homogeneous pieces.
  change (∃ y ∈ (toGradedModuleCat N).grading.piece p, Submodule.Quotient.mk y = x) ↔ _
  rw [toGradedModuleCat_piece]
  rfl

/-- The curved module carried by the quotient of the target by the image of a closed map. -/
noncomputable def cokernelObj : CurvedDGRightModuleCat.{u, u, u} h := by
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
    obtain ⟨y, hy, rfl⟩ := (mem_gradedCokernel_piece_iff f).mp hx
    rw [cokernelDifferential_mk]
    apply (mem_gradedCokernel_piece_iff f).mpr
    exact ⟨N.differential y, N.isCurvedDGRightModule.isHomogeneous.map_mem hy, rfl⟩
  · intro p x hx a
    obtain ⟨y, hy, rfl⟩ := (mem_gradedCokernel_piece_iff f).mp hx
    simp only [← Submodule.Quotient.mk_smul]
    erw [cokernelDifferential_mk, cokernelDifferential_mk]
    rw [← Submodule.Quotient.mk_smul, N.isCurvedDGRightModule.leibniz hy a]
    exact map_add ((LinearMap.range (closedHom f)).mkQ) _ _
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | _ x =>
      rw [cokernelDifferential_mk, cokernelDifferential_mk,
        N.isCurvedDGRightModule.sq_eq, Submodule.Quotient.mk_smul]

/-- The cokernel carrier is the range quotient. The equivalence's linearity supplies the
inherited right action without exposing the construction of `cokernelObj`. -/
noncomputable def cokernelEquiv : cokernelObj f ≃ₗ[Aᵐᵒᵖ] N ⧸ LinearMap.range (closedHom f) :=
  LinearEquiv.refl Aᵐᵒᵖ (N ⧸ LinearMap.range (closedHom f))

/-- The cokernel differential corresponds to the induced quotient differential. -/
@[simp]
theorem cokernelEquiv_differential (x : cokernelObj f) :
    cokernelEquiv f ((cokernelObj f).differential x) =
      cokernelDifferential f (cokernelEquiv f x) :=
  (rfl)

/-- Homogeneous cokernel elements correspond to classes of homogeneous target elements. -/
@[simp]
theorem mem_cokernelObj_grading_iff {p : ℤ} {x : cokernelObj f} :
    x ∈ (cokernelObj f).grading p ↔
      ∃ y ∈ N.grading p, Submodule.Quotient.mk y = cokernelEquiv f x :=
  mem_gradedCokernel_piece_iff f

/-- The projection onto the curved cokernel is a closed map. -/
noncomputable def cokernelπ :
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) N ⟶
      ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cokernelObj f) :=
  closedHomOf ((cokernelEquiv f).symm.toLinearMap.comp (LinearMap.range (closedHom f)).mkQ)
    (fun _ x hx ↦ (mem_cokernelObj_grading_iff f).mpr ⟨x, hx, by simp⟩)
    (fun x ↦ by
      apply (cokernelEquiv f).injective
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, cokernelEquiv_differential,
        LinearEquiv.apply_symm_apply, Submodule.mkQ_apply, cokernelDifferential_mk])

/-- The underlying cokernel projection is the quotient map followed by its carrier comparison. -/
@[simp]
theorem hom_cokernelπ :
    closedHom (cokernelπ f) =
      (cokernelEquiv f).symm.toLinearMap.comp (LinearMap.range (closedHom f)).mkQ := by
  dsimp only [cokernelπ]
  exact closedHom_closedHomOf _ _ _

/-- The original map followed by its cokernel projection is zero. -/
@[reassoc (attr := simp)]
theorem comp_cokernelπ : f ≫ cokernelπ f = 0 := by
  apply closedHom_ext
  intro x
  apply (cokernelEquiv f).injective
  simp only [closedHom_comp, hom_cokernelπ, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.apply_symm_apply, closedHom_zero, LinearMap.zero_apply, map_zero]
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩

/-- The cokernel cofork in the closed category of curved right modules. -/
noncomputable def cokernelCocone : CokernelCofork f :=
  CokernelCofork.ofπ (cokernelπ f) (comp_cokernelπ f)

/-- The point of the sealed cokernel cofork is the characteristic cokernel object. -/
@[simp]
theorem cokernelCocone_pt : (cokernelCocone f).pt =
    ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cokernelObj f) :=
  (rfl)

/-- The cokernel projection agrees with the characteristic projection after identifying its
point. -/
@[simp]
theorem cokernelCocone_π :
    (cokernelCocone f).π ≫ eqToHom (cokernelCocone_pt f) = cokernelπ f := by
  -- This is the defining constructor equation, including its point transport.
  change cokernelπ f ≫
    (𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cokernelObj f))) = cokernelπ f
  exact Category.comp_id _

/-- The curved cokernel projection satisfies the cokernel universal property. -/
noncomputable def cokernelIsColimit : IsColimit (cokernelCocone f) :=
  CokernelCofork.IsColimit.ofπ (cokernelπ f) (comp_cokernelπ f)
    (fun g hg ↦ closedHomOf
      (((LinearMap.range (closedHom f)).liftQ (closedHom g) fun x hx ↦ by
        obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
        apply LinearMap.mem_ker.mpr
        have hs := congrArg (fun l ↦ closedHom l y) hg
        simpa only [closedHom_comp, LinearMap.comp_apply, closedHom_zero, LinearMap.zero_apply]
          using hs).comp (cokernelEquiv f).toLinearMap)
      (fun _ x hx ↦ by
        obtain ⟨y, hy, he⟩ := (mem_cokernelObj_grading_iff f).mp hx
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
        rw [← he, Submodule.liftQ_apply]
        exact closedHom_mem g hy)
      (fun x ↦ by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, cokernelEquiv_differential]
        induction (cokernelEquiv f x) using Submodule.Quotient.induction_on with
        | _ y =>
          simp only [Submodule.liftQ_apply, cokernelDifferential_mk]
          exact differential_closedHom g y))
    (fun g hg ↦ by
      apply closedHom_ext
      intro x
      simp only [closedHom_comp, hom_cokernelπ, LinearMap.comp_apply, closedHom_closedHomOf,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, Submodule.mkQ_apply,
        Submodule.liftQ_apply])
    (fun g hg m hm ↦ by
      apply closedHom_ext
      intro x
      obtain ⟨z, rfl⟩ := (cokernelEquiv f).symm.surjective x
      induction z using Submodule.Quotient.induction_on with
      | _ y =>
        have hs := congrArg (fun l ↦ closedHom l y) hm
        simp only [closedHom_comp, hom_cokernelπ, LinearMap.comp_apply, LinearEquiv.coe_coe,
          Submodule.mkQ_apply] at hs
        simpa only [closedHom_closedHomOf, LinearMap.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.apply_symm_apply, Submodule.liftQ_apply]
          using hs)

/-- The closed category of curved right modules has cokernels. -/
noncomputable instance : HasCokernels
    (ForgetEnrichment (CochainComplex (ModuleCat R) ℤ) (CurvedDGRightModuleCat.{u, u, u} h)) :=
  ⟨fun f ↦ HasColimit.mk ⟨_, cokernelIsColimit f⟩⟩

/-- Forgetting the differential of the curved cokernel gives the usual graded cokernel. -/
noncomputable def forgetDifferentialCokernelIso :
    (forgetDifferential (h := h)).obj
        (ForgetEnrichment.of (CochainComplex (ModuleCat R) ℤ) (cokernelObj f)) ≅
      GradedModuleCat.cokernelObj ((forgetDifferential (h := h)).map f) :=
  GradedModuleCat.isoMk (cokernelEquiv f) fun p x ↦ by
    -- `isoMk` fixes a representative in the forgetful object's dependent carrier.
    -- Rewriting the object equality would transport that representative; align
    -- only the grading view, leaving the cokernel object behind its sealed API.
    change x ∈ (toGradedModuleCat (cokernelObj f)).grading.piece p ↔ _
    rw [toGradedModuleCat_piece]
    exact (mem_cokernelObj_grading_iff f).trans (mem_gradedCokernel_piece_iff f).symm

/-- The graded comparison is the cokernel's characteristic carrier equivalence. -/
@[simp]
theorem forgetDifferentialCokernelIso_hom_hom :
    (forgetDifferentialCokernelIso f).hom.hom = (cokernelEquiv f).toLinearMap := by
  simp only [forgetDifferentialCokernelIso, GradedModuleCat.isoMk_hom_hom]

/-- The graded forgetful functor preserves the cokernel of a closed map. -/
noncomputable instance : PreservesColimit (parallelPair f 0) (forgetDifferential (h := h)) := by
  refine preservesColimit_of_preserves_colimit_cocone (cokernelIsColimit f)
    (((cokernelCocone f).isColimitMapCoconeEquiv (forgetDifferential (h := h))).symm ?_)
  let e : (cokernelCocone f).map (forgetDifferential (h := h)) ≅
      GradedModuleCat.cokernelCocone ((forgetDifferential (h := h)).map f) :=
    Cofork.ext (forgetDifferentialCokernelIso f) (by
      apply GradedModuleCat.hom_ext
      rw [GradedModuleCat.hom_comp, forgetDifferentialCokernelIso_hom_hom,
        GradedModuleCat.hom_cokernelCocone_π, CokernelCofork.map_π,
        forgetDifferential_map_hom]
      -- The local carrier view is fixed by the sealed point equation.
      change (cokernelEquiv f).toLinearMap.comp (closedHom (cokernelπ f)) = _
      rw [hom_cokernelπ]
      apply LinearMap.ext
      intro x
      exact LinearEquiv.apply_symm_apply (cokernelEquiv f) _)
  exact (IsColimit.equivIsoColimit e).symm
    (GradedModuleCat.cokernelIsColimit ((forgetDifferential (h := h)).map f))

end TauCeti.CurvedDGRightModuleCat
