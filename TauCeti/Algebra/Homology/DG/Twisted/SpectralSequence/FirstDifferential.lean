/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.GradedPieceDifferential
public import TauCeti.Algebra.Homology.DG.Twisted.FirstPage
public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence
public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.Algebra.Homology.ModuleCat.ShortExact
import TauCeti.Algebra.Homology.SpectralSequence.Filtered.FirstPage

/-!
# The first differential of the index spectral sequence

On the first page of the index spectral sequence of a twisted complex (page `2` in Mathlib's
numbering), the object at `(p, q)` is the cohomology in degree `p + q` of the graded piece
`⊕_{ind x = q + 1} ℳ ⊗ ⟨x⟩` (`TauCeti.TwistingCocycle.indexSpectralSequenceFirstPageXIso`).  This
file computes the differential of that page: it sends the class of a cycle `f` to the class of
`TauCeti.TwistingCocycle.indexGradedPieceD1X f`, that is of the restriction of its twisted
differential to the generators of index `q`, the entries `m x y` with `ind x - ind y = 1` of the
twisting cocycle.

The entries `m x y` with `ind x - ind y = 1` are cycles of degree zero of the algebra (the twisting
equation has no intermediate generators), so this is the action of their classes on the cohomology
of `ℳ`.  The identification of the cohomology of `TauCeti.shiftedModuleComplex` with the graded
pieces of `TauCeti.IsDGRightModule.Cohomology`, through which this action is the module structure
of `H(ℳ)` over `H(𝒜)`, is not made here.

## Main definitions

* `TauCeti.TwistingCocycle.twistedIndexCokernelIsoOfEq` and
  `TauCeti.TwistingCocycle.indexSpectralSequenceFirstPageXIsoOfEq`: the identification of the
  first page with the cohomology of the graded pieces, with the indices given by equations.

## Main results

* `TauCeti.TwistingCocycle.indexSpectralSequence_page_two_d_apply`: the differential of the first
  page of the index spectral sequence.
* `TauCeti.TwistingCocycle.homologyMap_indexGradedPieceEval_page_two_d`: its entries under the
  splitting of `TauCeti.indexGradedPieceHomologyIso`, between a generator `x` of index `b + 1` and
  a generator `y` of index `b`, are induced by `α ↦ α · m x y` up to the Koszul sign.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe uR uA uM uP

namespace TwistingCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} {ind : P → ℤ}
  [Fintype P] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ] {dM : M →ₗ[R] M}
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  (m : TwistingCocycle 𝒜 d P ind) (hM : IsDGRightModule h ℳ dM)

/-- The differential of the first page, between the identifications of its source and target with
the cohomology of the graded pieces, is the connecting map of the short exact sequence of graded
pieces. -/
private theorem page_two_d_comp_eq (a b : ℤ) :
    (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a, b) b (b + 1) rfl rfl (a + b) rfl).inv ≫
    ((m.indexSpectralSequence dM hM).page 2).d (a, b) (a + 2, b - 1) ≫
      (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a + 2, b - 1) (b - 1) b rfl (by omega)
        (a + b + 1) (by simp only; omega)).hom =
    HomologicalComplex.homologyMap (m.twistedIndexCokernelIsoOfEq dM hM b (b + 1) rfl).inv
        (a + b) ≫
      (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact _ _).δ (a + b) (a + b + 1)
        rfl ≫
      HomologicalComplex.homologyMap
        (m.twistedIndexCokernelIsoOfEq dM hM (b - 1) b (by omega)).hom (a + b + 1) := by
  have key := CochainComplex.spectralSequence_first_page_d_eq
    (m.twistedIndexFiltrationFunctor dM hM) a b
  rw [key]
  simp only [indexSpectralSequenceFirstPageXIsoOfEq_eq, Iso.trans_inv, Iso.trans_hom,
    HomologicalComplex.homologyMapIso_inv, HomologicalComplex.homologyMapIso_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  congr 1
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _))

/-- **A cycle of a graded piece lifts to the index filtration.** A cycle `f` of the graded piece
of index `b + 1` is the projection of an element `s` of the `(b + 1)`-st stage of the filtration,
whose differential is the image of an element `w` of the `b`-th stage projecting to the
restriction of the twisted differential of `f` to the generators of index `b`. -/
private theorem exists_lift_indexGradedPieceD1X (a b : ℤ)
    (f : (indexGradedPieceComplex hM ind (b + 1)).X (a + b))
    (hf : ((indexGradedPieceComplex hM ind (b + 1)).d (a + b) (a + b + 1)).hom f = 0) :
    ∃ (s : (m.twistedIndexCochainComplex hM (b + 1)).X (a + b))
      (w : (m.twistedIndexCochainComplex hM b).X (a + b + 1)),
      ((m.twistedIndexCochainComplexMap hM (Int.le_add_one le_rfl)).f (a + b + 1)).hom w =
        ((m.twistedIndexCochainComplex hM (b + 1)).d (a + b) (a + b + 1)).hom s ∧
      ((m.twistedIndexCochainComplexProj dM hM (b + 1)).f (a + b)).hom s = f ∧
      ((m.twistedIndexCochainComplexProj dM hM b).f (a + b + 1)).hom w =
        m.indexGradedPieceD1X hM b (b + 1) (a + b) f := by
  -- The lift `s'` of `f` to the `(b + 1)`-st stage of the filtration, and the element `w` of the
  -- `b`-th stage whose image is the differential of `s'`.
  set ef := indexExtend R M ind (b + 1) (indexGradedPieceComplexXEquiv hM ind (b + 1) (a + b) f)
    with hef
  have hef_mem : ef ∈ twistedIndexGrading ℳ ind (b + 1) (a + b) :=
    mem_twistedIndexGrading_iff.2
      ⟨(mem_twistedIndexFiltration_iff _).1 (indexExtend_mem_twistedIndexFiltration _),
        mem_twistedTotalGrading_iff.1
          (indexExtend_mem_twistedTotalGrading (indexGradedPieceComplexXEquiv hM ind (b + 1)
            (a + b) f).2)⟩
  let s' := (m.twistedIndexCochainComplexXEquiv hM (b + 1) (a + b)).symm ⟨ef, hef_mem⟩
  have hs' : (m.twistedIndexCochainComplexXEquiv hM (b + 1) (a + b) s' : P → M) = ef :=
    congrArg Subtype.val ((m.twistedIndexCochainComplexXEquiv hM (b + 1) (a + b)).apply_symm_apply
      ⟨ef, hef_mem⟩)
  have hds' : (m.twistedIndexCochainComplexXEquiv hM (b + 1) (a + b + 1)
      (((m.twistedIndexCochainComplex hM (b + 1)).d (a + b) (a + b + 1)).hom s') : P → M) =
      twistedDifferential m.m ℳ dM ef := by
    rw [m.twistedIndexCochainComplexXEquiv_d, hs']
  have hw_mem : twistedDifferential m.m ℳ dM ef ∈ twistedIndexGrading ℳ ind b (a + b + 1) :=
    mem_twistedIndexGrading_iff.2
      ⟨fun x hx ↦ m.twistedDifferential_indexExtend_eq_zero hM b (b + 1) rfl (a + b) f hf x hx,
        by
          rw [← hds']
          exact (mem_twistedIndexGrading_iff.1 (m.twistedIndexCochainComplexXEquiv hM (b + 1)
            (a + b + 1) (((m.twistedIndexCochainComplex hM (b + 1)).d (a + b)
              (a + b + 1)).hom s')).2).2⟩
  let w := (m.twistedIndexCochainComplexXEquiv hM b (a + b + 1)).symm ⟨_, hw_mem⟩
  have hw : (m.twistedIndexCochainComplexXEquiv hM b (a + b + 1) w : P → M) =
      twistedDifferential m.m ℳ dM ef :=
    congrArg Subtype.val ((m.twistedIndexCochainComplexXEquiv hM b (a + b + 1)).apply_symm_apply
      ⟨_, hw_mem⟩)
  -- The transition map sends `w` to the differential of `s'`.
  have hofLE : ((m.twistedIndexCochainComplexMap hM (Int.le_add_one le_rfl)).f (a + b + 1)).hom
      w = ((m.twistedIndexCochainComplex hM (b + 1)).d (a + b) (a + b + 1)).hom s' :=
    (m.twistedIndexCochainComplexXEquiv hM (b + 1) (a + b + 1)).injective (Subtype.ext (by
      rw [m.twistedIndexCochainComplexMap_apply, hw, hds']))
  -- The projections of `s'` and `w` to the graded pieces.
  have hprojs : ((m.twistedIndexCochainComplexProj dM hM (b + 1)).f (a + b)).hom s' = f :=
    (indexGradedPieceComplexXEquiv hM ind (b + 1) (a + b)).injective (Subtype.ext (by
      rw [m.twistedIndexCochainComplexProj_f_apply, hs', hef, funLeft_indexExtend]))
  have hprojw : ((m.twistedIndexCochainComplexProj dM hM b).f (a + b + 1)).hom w =
      m.indexGradedPieceD1X hM b (b + 1) (a + b) f :=
    (indexGradedPieceComplexXEquiv hM ind b (a + b + 1)).injective (Subtype.ext (by
      rw [m.twistedIndexCochainComplexProj_f_apply, hw,
        indexGradedPieceComplexXEquiv_indexGradedPieceD1X]))
  exact ⟨s', w, hofLE, hprojs, hprojw⟩

/-- The transition map of the index filtration sends the image of `w` to the differential of the
image of `s`, when it sends `w` to the differential of `s`. -/
private theorem twistedIndexFiltrationFunctor_map_objIso_inv_apply (a b : ℤ)
    (s' : (m.twistedIndexCochainComplex hM (b + 1)).X (a + b))
    (w : (m.twistedIndexCochainComplex hM b).X (a + b + 1))
    (hofLE : ((m.twistedIndexCochainComplexMap hM (Int.le_add_one le_rfl)).f (a + b + 1)).hom w =
      ((m.twistedIndexCochainComplex hM (b + 1)).d (a + b) (a + b + 1)).hom s') :
    (((m.twistedIndexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b = b from rfl) rfl))).f
        (a + b + 1)).hom
        (((m.twistedIndexFiltrationFunctorObjIso dM hM b).inv.f (a + b + 1)).hom w) =
      (((m.twistedIndexFiltrationFunctor dM hM).obj ((b + 1 : ℤ) : EInt)).d (a + b) (a + b + 1)).hom
        (((m.twistedIndexFiltrationFunctorObjIso dM hM (b + 1)).inv.f (a + b)).hom s') := by
  set Fn := m.twistedIndexFiltrationFunctor dM hM
  set s := ((m.twistedIndexFiltrationFunctorObjIso dM hM (b + 1)).inv.f (a + b)).hom s'
  set t := ((m.twistedIndexFiltrationFunctorObjIso dM hM b).inv.f (a + b + 1)).hom w
  have hinj : Function.Injective
      ((m.twistedIndexFiltrationFunctorObjIso dM hM (b + 1)).hom.f (a + b + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine hinj ?_
  have h₁ := congrArg (fun φ ↦ (φ.f (a + b + 1)).hom t)
    (m.twistedIndexFiltrationFunctor_map_objIso_hom dM hM b)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
  rw [h₁, show ((m.twistedIndexFiltrationFunctorObjIso dM hM b).hom.f (a + b + 1)).hom t = w from
    congrArg (fun φ ↦ (φ.f (a + b + 1)).hom w)
      (m.twistedIndexFiltrationFunctorObjIso dM hM b).inv_hom_id, hofLE,
    HomologicalComplex.Hom.comm_apply]
  exact (congrArg (fun φ ↦ (φ.f (a + b + 1)).hom
    (((m.twistedIndexCochainComplex hM (b + 1)).d (a + b) (a + b + 1)).hom s'))
    (m.twistedIndexFiltrationFunctorObjIso dM hM (b + 1)).inv_hom_id).symm

/-- The image in the cokernel of the transition map of the image of `s'` is the image of `f`, when
`s'` projects to `f` in the graded piece. -/
private theorem cokernel_π_objIso_inv_apply (a b : ℤ)
    (s' : (m.twistedIndexCochainComplex hM (b + 1)).X (a + b))
    (f : (indexGradedPieceComplex hM ind (b + 1)).X (a + b))
    (hprojs : ((m.twistedIndexCochainComplexProj dM hM (b + 1)).f (a + b)).hom s' = f) :
    ((cokernel.π ((m.twistedIndexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b = b from rfl) rfl)))).f
        (a + b)).hom
        (((m.twistedIndexFiltrationFunctorObjIso dM hM (b + 1)).inv.f (a + b)).hom s') =
      ((m.twistedIndexCokernelIsoOfEq dM hM b (b + 1) rfl).inv.f (a + b)).hom f := by
  set Fn := m.twistedIndexFiltrationFunctor dM hM
  set s := ((m.twistedIndexFiltrationFunctorObjIso dM hM (b + 1)).inv.f (a + b)).hom s'
  have h₁ := congrArg (fun φ ↦ (φ.f (a + b)).hom s)
    (m.cokernel_π_comp_twistedIndexCokernelIsoOfEq_hom dM hM b (b + 1) rfl)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
  rw [show ((m.twistedIndexFiltrationFunctorObjIso dM hM (b + 1)).hom.f (a + b)).hom s = s' from
    congrArg (fun φ ↦ (φ.f (a + b)).hom s')
      (m.twistedIndexFiltrationFunctorObjIso dM hM (b + 1)).inv_hom_id, hprojs] at h₁
  have h₂ := congrArg (fun φ ↦ (φ.f (a + b)).hom (((cokernel.π (Fn.map (homOfLE
    (CochainComplex.coe_le_coe_of_eq_add_one (show b = b from rfl) rfl)))).f
        (a + b)).hom s))
    (m.twistedIndexCokernelIsoOfEq dM hM b (b + 1) rfl).hom_inv_id
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply] at h₂
  rw [h₁] at h₂
  exact h₂.symm

/-- The image in the cokernel of the inclusion `F_{b-1} ⟶ F_b` of the image of `w` is the
restriction of the twisted differential of `f`, when `w` projects to it in the graded piece. -/
private theorem cokernel_π_objIso_inv_apply_d1X (a b : ℤ)
    (w : (m.twistedIndexCochainComplex hM b).X (a + b + 1))
    (f : (indexGradedPieceComplex hM ind (b + 1)).X (a + b))
    (hprojw : ((m.twistedIndexCochainComplexProj dM hM b).f (a + b + 1)).hom w =
      m.indexGradedPieceD1X hM b (b + 1) (a + b) f) :
    ((m.twistedIndexCokernelIsoOfEq dM hM (b - 1) b (by omega)).hom.f (a + b + 1)).hom
      (((cokernel.π ((m.twistedIndexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b - 1 = b - 1 from rfl)
      (show b = b - 1 + 1 by lia))))).f (a + b + 1)).hom
        (((m.twistedIndexFiltrationFunctorObjIso dM hM b).inv.f (a + b + 1)).hom w)) =
      m.indexGradedPieceD1X hM b (b + 1) (a + b) f := by
  set Fn := m.twistedIndexFiltrationFunctor dM hM
  set t := ((m.twistedIndexFiltrationFunctorObjIso dM hM b).inv.f (a + b + 1)).hom w
  have h₁ := congrArg (fun φ ↦ (φ.f (a + b + 1)).hom t)
    (m.cokernel_π_comp_twistedIndexCokernelIsoOfEq_hom dM hM (b - 1) b (by omega))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
  rw [show ((m.twistedIndexFiltrationFunctorObjIso dM hM b).hom.f (a + b + 1)).hom t = w from
    congrArg (fun φ ↦ (φ.f (a + b + 1)).hom w)
      (m.twistedIndexFiltrationFunctorObjIso dM hM b).inv_hom_id] at h₁
  exact h₁.trans hprojw

/-- **The first differential of the index spectral sequence.** On the first page (page `2` in
Mathlib's numbering), the differential from `(a, b)` to `(a + 2, b - 1)` sends the class of a
cycle `f` of the graded piece of the generators of index `b + 1` to the class of the restriction
of the twisted differential of `f`, extended by zero, to the generators of index `b`. -/
theorem indexSpectralSequence_page_two_d_apply (a b : ℤ)
    (f : (indexGradedPieceComplex hM ind (b + 1)).X (a + b))
    (hf : ((indexGradedPieceComplex hM ind (b + 1)).d (a + b) (a + b + 1)).hom f = 0) :
    (m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a + 2, b - 1) (b - 1) b rfl (by omega)
        (a + b + 1) (by simp only; omega)).hom
      ((((m.indexSpectralSequence dM hM).page 2).d (a, b) (a + 2, b - 1)).hom
        ((m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a, b) b (b + 1) rfl rfl (a + b) rfl).inv
          (((indexGradedPieceComplex hM ind (b + 1)).homologyπ (a + b)).hom
            ((indexGradedPieceComplex hM ind (b + 1)).moduleCatCyclesMk f (a + b + 1)
              (by simp) hf)))) =
      ((indexGradedPieceComplex hM ind b).homologyπ (a + b + 1)).hom
        ((indexGradedPieceComplex hM ind b).moduleCatCyclesMk
          (m.indexGradedPieceD1X hM b (b + 1) (a + b) f) (a + b + 1 + 1) (by simp)
          (m.d_indexGradedPieceD1X hM b (b + 1) rfl (a + b) f hf)) := by
  have hcls := congrArg (fun φ ↦ φ.hom (((indexGradedPieceComplex hM ind (b + 1)).homologyπ
    (a + b)).hom ((indexGradedPieceComplex hM ind (b + 1)).moduleCatCyclesMk f (a + b + 1)
      (by simp) hf))) (m.page_two_d_comp_eq hM a b)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcls
  refine hcls.trans ?_
  rw [HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  obtain ⟨s', w, hofLE, hprojs, hprojw⟩ := m.exists_lift_indexGradedPieceD1X hM a b f hf
  have hz₃ : ((cokernel ((m.twistedIndexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b = b from rfl) rfl)))).d
        (a + b) (a + b + 1))
      (((m.twistedIndexCokernelIsoOfEq dM hM b (b + 1) rfl).inv.f (a + b)).hom f) = 0 := by
    rw [HomologicalComplex.Hom.comm_apply]
    exact (congrArg _ hf).trans (map_zero _)
  obtain ⟨hc, hδ⟩ := exists_δ_kernelCokernelSequence_L₃_eq
    ((m.twistedIndexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b - 1 = b - 1 from rfl)
      (show b = b - 1 + 1 by lia))))
    ((m.twistedIndexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b = b from rfl) rfl))) (a + b)
    (((m.twistedIndexFiltrationFunctorObjIso dM hM (b + 1)).inv.f (a + b)).hom s')
    (((m.twistedIndexFiltrationFunctorObjIso dM hM b).inv.f (a + b + 1)).hom w)
    (m.twistedIndexFiltrationFunctor_map_objIso_inv_apply hM a b s' w hofLE) _ hz₃
    (m.cokernel_π_objIso_inv_apply hM a b s' f hprojs)
  refine (congrArg (HomologicalComplex.homologyMap
    (m.twistedIndexCokernelIsoOfEq dM hM (b - 1) b (by omega)).hom (a + b + 1)).hom hδ).trans ?_
  refine (HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk _ _ _ _ hc).trans ?_
  simp only [m.cokernel_π_objIso_inv_apply_d1X hM a b w f hprojw]

section Components

variable [DecidableEq P] {b : ℤ} (x : {x : P // ind x = b + 1}) (y : {y : P // ind y = b})

/-- **The entries of the first differential of the index spectral sequence.** Under the splitting
of the first page into the cohomology of `ℳ` (`indexGradedPieceHomologyIso`), the entry of the
differential from `(a, b)` to `(a + 2, b - 1)` between a generator `x` of index `b + 1` and a
generator `y` of index `b` sends the class of a cycle `α` to the class of `α · m x y`, up to the
Koszul sign (`shiftedModuleComplexXEquiv_indexGradedPieceEval_D1X_single`). -/
theorem homologyMap_indexGradedPieceEval_page_two_d (a : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (b + 1)).X (a + b))
    (hα : ((shiftedModuleComplex.{uR, uA, uM, uP} hM (b + 1)).d (a + b) (a + b + 1)).hom α = 0) :
    (HomologicalComplex.homologyMap (indexGradedPieceEval hM ind y) (a + b + 1)).hom
      ((m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a + 2, b - 1) (b - 1) b rfl (by omega)
        (a + b + 1) (by simp only; omega)).hom
          ((((m.indexSpectralSequence dM hM).page 2).d (a, b) (a + 2, b - 1)).hom
            ((m.indexSpectralSequenceFirstPageXIsoOfEq dM hM (a, b) b (b + 1) rfl rfl (a + b)
              rfl).inv
              ((HomologicalComplex.homologyMap (indexGradedPieceSingle hM ind x) (a + b)).hom
                (((shiftedModuleComplex.{uR, uA, uM, uP} hM (b + 1)).homologyπ (a + b)).hom
                  ((shiftedModuleComplex.{uR, uA, uM, uP} hM (b + 1)).moduleCatCyclesMk α
                    (a + b + 1) (by simp) hα)))))) =
      ((shiftedModuleComplex.{uR, uA, uM, uP} hM b).homologyπ (a + b + 1)).hom
        ((shiftedModuleComplex.{uR, uA, uM, uP} hM b).moduleCatCyclesMk
          (((indexGradedPieceEval hM ind y).f (a + b + 1)).hom
            (m.indexGradedPieceD1X hM b (b + 1) (a + b)
              (((indexGradedPieceSingle hM ind x).f (a + b)).hom α)))
          (a + b + 1 + 1) (by simp)
          (HomologicalComplex.Hom.d_apply_eq_zero_of_d_apply_eq_zero _ _ _ _
            (m.d_indexGradedPieceD1X hM b (b + 1) rfl (a + b) _
              (HomologicalComplex.Hom.d_apply_eq_zero_of_d_apply_eq_zero _ _ _ _ hα)))) := by
  rw [HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk,
    m.indexSpectralSequence_page_two_d_apply hM a b _
      (HomologicalComplex.Hom.d_apply_eq_zero_of_d_apply_eq_zero _ _ _ _ hα)]
  exact HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk _ _ _ _ _

end Components

end TwistingCocycle

end TauCeti
