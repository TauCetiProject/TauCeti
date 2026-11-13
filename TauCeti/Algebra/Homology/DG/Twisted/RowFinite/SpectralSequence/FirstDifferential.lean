/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.SpectralSequence.Splitting
public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.Action
public import TauCeti.Algebra.Homology.ModuleCat.ShortExact
import TauCeti.Algebra.Homology.SpectralSequence.Filtered.FirstPage

/-!
# The first differential of a row-finite index spectral sequence

Let `m` be a one-sided row-finite twisting cocycle on an arbitrary graded set of generators `P`,
and let `ℳ` be a DG right module. On the first page of the index spectral sequence of the
row-finite twisted complex (page `2` in Mathlib's numbering), the object at `(p, q)` is the
cohomology in degree `p + q` of the graded piece of index `q + 1`, the complex of finite-support
families of coefficients on the generators of that index
(`TauCeti.RowFiniteTwistingCocycle.indexSpectralSequenceFirstPageXIso`). This file computes the
differential of that page.

Extending a family on the generators of index `p` by zero, taking its row-finite twisted
differential and restricting to the generators of index `q` gives a map between the graded
pieces (`TauCeti.RowFiniteTwistingCocycle.indexGradedPieceD1X`). For `q + 1 = p` it sends cycles
to cycles: the twisted differential of a cycle extended by zero lies in the filtration stage of
index `q`. The first differential sends the class of a cycle `f` to the class of its image
(`TauCeti.RowFiniteTwistingCocycle.indexSpectralSequence_page_two_d_apply`).

On a coefficient `α` inserted at a generator `x` of index `b + 1`, the image is the finite sum,
over the generators `y` of index `b` in the row of `x`, of `α · m x y` inserted at `y`, up to the
Koszul sign (`TauCeti.RowFiniteTwistingCocycle.indexGradedPieceD1X_single`). This is the
row-finite form of `TauCeti.TwistingCocycle.indexSpectralSequence_page_two_d_apply`: the rows are
finite, so the sum is finite although there may be infinitely many generators of index `b`.

## Main definitions

* `TauCeti.RowFiniteTwistingCocycle.indexGradedPieceD1X`: the restriction of the twisted
  differential from the graded piece of index `p` to that of index `q`.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.d_indexGradedPieceD1X`: for `q + 1 = p`, it sends cycles to
  cycles.
* `TauCeti.RowFiniteTwistingCocycle.indexGradedPieceD1X_single`: its value on a coefficient
  inserted at one generator, as a finite sum over the row of that generator.
* `TauCeti.RowFiniteTwistingCocycle.indexSpectralSequence_page_two_d_apply`: the differential of
  the first page of the row-finite index spectral sequence.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {ind : P → ℤ} {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} {dM : M →ₗ[R] M}

namespace RowFiniteTwistingCocycle

variable (m : RowFiniteTwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hA ℳ dM)

/-! ### The differential between two graded pieces -/

/-- The restriction to the generators of index `q` of the row-finite twisted differential, from
the degree-`n` term of the graded piece of index `p` to the degree-`(n + 1)` term of that of index
`q`: a family on the generators of index `p` is extended by zero, and its twisted differential is
restricted to the generators of index `q`. -/
noncomputable def indexGradedPieceD1X (q p n : ℤ) :
    (rowFiniteIndexGradedPieceComplex ind hM p).X n →ₗ[R]
      (rowFiniteIndexGradedPieceComplex ind hM q).X (n + 1) :=
  (rowFiniteIndexGradedPieceComplexXEquiv hM q (n + 1)).symm.toLinearMap ∘ₗ
    ((Finsupp.lsubtypeDomain {y | ind y = q} ∘ₗ m.coefficientDifferential hM ∘ₗ
        Finsupp.lmapDomain M R Subtype.val ∘ₗ
          (rowFiniteTotalGrading ℳ (fun x : {x // ind x = p} ↦ ind x) n).subtype).codRestrict
        _ fun f ↦ (mem_rowFiniteTotalGrading_iff ℳ _).2 fun y ↦ by
      have h := (mem_rowFiniteTotalGrading_iff ℳ ind).1
        ((m.isHomogeneous_coefficientDifferential hM).map_mem
          (mapDomain_subtypeVal_mem_rowFiniteTotalGrading f.2)) y.1
      -- Restriction to the generators of index `q` evaluates at the underlying generator.
      exact h) ∘ₗ
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n).toLinearMap

/-- `indexGradedPieceD1X` restricts the twisted differential of the family extended by zero to the
generators of index `q`. -/
@[simp]
theorem rowFiniteIndexGradedPieceComplexXEquiv_indexGradedPieceD1X_apply (q p n : ℤ)
    (f : (rowFiniteIndexGradedPieceComplex ind hM p).X n) (y : {y // ind y = q}) :
    (rowFiniteIndexGradedPieceComplexXEquiv hM q (n + 1) (m.indexGradedPieceD1X hM q p n f) :
        {y // ind y = q} →₀ M) y =
      m.coefficientDifferential hM ((rowFiniteIndexGradedPieceComplexXEquiv hM p n f :
        {x // ind x = p} →₀ M).mapDomain Subtype.val) y := by
  simp only [indexGradedPieceD1X, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearEquiv.apply_symm_apply]
  -- The remaining equation holds by unfolding the corestriction of the codomain.
  rfl

variable {m} (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)
include hm

/-- The twisted differential of a cycle of the graded piece of index `p = q + 1`, extended by
zero, vanishes at the generators of index greater than `q`. -/
theorem coefficientDifferential_mapDomain_apply_eq_zero (q p : ℤ) (hqp : q + 1 = p) (n : ℤ)
    (f : (rowFiniteIndexGradedPieceComplex ind hM p).X n)
    (hf : ((rowFiniteIndexGradedPieceComplex ind hM p).d n (n + 1)).hom f = 0) :
    ∀ y, q < ind y →
      m.coefficientDifferential hM ((rowFiniteIndexGradedPieceComplexXEquiv hM p n f :
        {x // ind x = p} →₀ M).mapDomain Subtype.val) y = 0 := by
  intro y hy
  have hF := mapDomain_subtypeVal_mem_rowFiniteIndexFiltration (R := R)
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n f : {x // ind x = p} →₀ M)
  rcases lt_or_eq_of_le (show p ≤ ind y by omega) with hlt | heq
  · exact (mem_rowFiniteIndexFiltration_iff ind).1
      (m.coefficientDifferential_mem_rowFiniteIndexFiltration hM hm hF) y hlt
  · -- At a generator of index `p` the twisted differential is the coefficient differential.
    rw [m.coefficientDifferential_apply_of_eq hM hm hF heq.symm,
      show y = ((⟨y, heq.symm⟩ : {x // ind x = p}) : P) from rfl,
      Finsupp.mapDomain_apply_of_injective Subtype.val_injective]
    have h := DFunLike.congr_fun (rowFiniteIndexGradedPieceComplexXEquiv_d hM p n f) ⟨y, heq.symm⟩
    rw [hf] at h
    simpa using h.symm

/-- The restriction of the twisted differential sends the cycles of the graded piece of index
`p = q + 1` to cycles of the graded piece of index `q`. -/
theorem d_indexGradedPieceD1X (q p : ℤ) (hqp : q + 1 = p) (n : ℤ)
    (f : (rowFiniteIndexGradedPieceComplex ind hM p).X n)
    (hf : ((rowFiniteIndexGradedPieceComplex ind hM p).d n (n + 1)).hom f = 0) :
    ((rowFiniteIndexGradedPieceComplex ind hM q).d (n + 1) (n + 1 + 1)).hom
      (m.indexGradedPieceD1X hM q p n f) = 0 := by
  refine (rowFiniteIndexGradedPieceComplexXEquiv hM q (n + 1 + 1)).injective
    (Subtype.ext (Finsupp.ext fun y ↦ ?_))
  have hF : m.coefficientDifferential hM ((rowFiniteIndexGradedPieceComplexXEquiv hM p n f :
      {x // ind x = p} →₀ M).mapDomain Subtype.val) ∈ rowFiniteIndexFiltration (R := R) ind q :=
    (mem_rowFiniteIndexFiltration_iff ind).2
      (m.coefficientDifferential_mapDomain_apply_eq_zero hM hm q p hqp n f hf)
  -- At a generator of index `q`, the coefficient differential of the restricted family is the
  -- twisted differential of the twisted differential, which vanishes.
  have key := m.coefficientDifferential_apply_of_eq hM hm hF y.2
  rw [m.coefficientDifferential_sq_zero] at key
  rw [rowFiniteIndexGradedPieceComplexXEquiv_d]
  simpa using key.symm

omit hm in
/-- **The restricted differential on one generator**: inserting `α` at a generator `x` of index
`b + 1`, restricting the twisted differential to the generators of index `b` and evaluating at
such a generator `y` gives `α · m x y`, up to the Koszul sign. -/
theorem rowFiniteIndexGradedPieceComplexXEquiv_indexGradedPieceD1X_single_apply {b : ℤ}
    (x : {x // ind x = b + 1}) (y : {y // ind y = b}) (n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (b + 1)).X n) :
    (rowFiniteIndexGradedPieceComplexXEquiv hM b (n + 1) (m.indexGradedPieceD1X hM b (b + 1) n
        (((rowFiniteIndexGradedPieceSingle hM ind x).f n).hom α)) : {y // ind y = b} →₀ M) y =
      op (m.m x y) • (InternalGrading.ofDecomposition ℳ).koszulTwist 1
        (shiftedModuleComplexXEquiv hM (b + 1) n α : M) := by
  classical
  have hyx : (y : P) ≠ x := fun h ↦ by
    have h₁ := x.2
    rw [← h, y.2] at h₁
    omega
  set α₀ := (shiftedModuleComplexXEquiv hM (b + 1) n α : M)
  -- The row of `x` evaluated at `y`.
  have hsum : ((m.m x).sum fun z a ↦ Finsupp.single z (op a • α₀)) y = op (m.m x y) • α₀ := by
    rw [Finsupp.sum_apply, Finsupp.sum, Finset.sum_eq_single (y : P)]
    · simp
    · intro z _ hz
      simp [hz]
    · intro hy
      simp [Finsupp.notMem_support_iff.1 hy]
  rw [rowFiniteIndexGradedPieceComplexXEquiv_indexGradedPieceD1X_apply,
    rowFiniteIndexGradedPieceComplexXEquiv_rowFiniteIndexGradedPieceSingle_f,
    Finsupp.mapDomain_single,
    m.coefficientDifferential_single hM x.1 (shiftedModuleComplexXEquiv hM (b + 1) n α).2]
  rw [Finsupp.add_apply, Finsupp.single_eq_of_ne hyx, zero_add, Finsupp.smul_apply,
    hsum, koszulTwist_one_eq_negOnePow_smul (shiftedModuleComplexXEquiv hM (b + 1) n α).2]
  exact smul_comm _ _ _

omit hm in
/-- **The restricted differential on one generator, as a finite sum**: inserting `α` at a
generator `x` of index `b + 1` and restricting the twisted differential to the generators of index
`b` gives the sum, over the generators `y` of index `b` in the row of `x`, of `α · m x y` inserted
at `y`, up to the Koszul sign. -/
theorem indexGradedPieceD1X_single {b : ℤ} (x : {x // ind x = b + 1}) (n : ℤ)
    (α : (shiftedModuleComplex.{uR, uA, uM, uP} hM (b + 1)).X n) :
    m.indexGradedPieceD1X hM b (b + 1) n (((rowFiniteIndexGradedPieceSingle hM ind x).f n).hom α) =
      ∑ y ∈ m.indexRowSupport b x,
        ((rowFiniteIndexGradedPieceSingle hM ind y).f (n + 1)).hom
          (shiftedModuleComplexActX hM (m.m_mem_zero_of_subtype x y) b n α) := by
  classical
  refine (rowFiniteIndexGradedPieceComplexXEquiv hM b (n + 1)).injective
    (Subtype.ext (Finsupp.ext fun y ↦ ?_))
  rw [rowFiniteIndexGradedPieceComplexXEquiv_indexGradedPieceD1X_single_apply, map_sum,
    Submodule.coe_sum, Finsupp.finsetSum_apply]
  simp only [rowFiniteIndexGradedPieceComplexXEquiv_rowFiniteIndexGradedPieceSingle_f,
    shiftedModuleComplexXEquiv_shiftedModuleComplexActX]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hz
    simp [Finsupp.single_eq_of_ne' hz]
  · intro hy
    simp [not_not.1 (m.mem_indexRowSupport_iff.not.1 hy)]

/-! ### The first differential of the index spectral sequence -/

/-- The differential of the first page, between the identifications of its source and target with
the cohomology of the graded pieces, is the connecting map of the short exact sequence of graded
pieces. -/
private theorem page_two_d_comp_eq (a b : ℤ) :
    (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm (a, b) b (b + 1) rfl rfl (a + b) rfl).inv ≫
    ((m.indexSpectralSequence hM hm).page 2).d (a, b) (a + 2, b - 1) ≫
      (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm (a + 2, b - 1) (b - 1) b rfl (by omega)
        (a + b + 1) (by simp only; omega)).hom =
    HomologicalComplex.homologyMap (m.indexCokernelIsoOfEq hM hm b (b + 1) rfl).inv (a + b) ≫
      (TauCeti.kernelCokernelCompSequence_snakeInput_L₃_shortExact _ _).δ (a + b) (a + b + 1)
        rfl ≫
      HomologicalComplex.homologyMap
        (m.indexCokernelIsoOfEq hM hm (b - 1) b (by omega)).hom (a + b + 1) := by
  have key := CochainComplex.spectralSequence_first_page_d_eq
    (m.indexFiltrationFunctor hM hm) a b
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
    (f : (rowFiniteIndexGradedPieceComplex ind hM (b + 1)).X (a + b))
    (hf : ((rowFiniteIndexGradedPieceComplex ind hM (b + 1)).d (a + b) (a + b + 1)).hom f = 0) :
    ∃ (s : (m.indexCochainComplex hM hm (b + 1)).X (a + b))
      (w : (m.indexCochainComplex hM hm b).X (a + b + 1)),
      ((m.indexCochainComplexMap hM hm (Int.le_add_one le_rfl)).f (a + b + 1)).hom w =
        ((m.indexCochainComplex hM hm (b + 1)).d (a + b) (a + b + 1)).hom s ∧
      ((m.indexCochainComplexProj hM hm (b + 1)).f (a + b)).hom s = f ∧
      ((m.indexCochainComplexProj hM hm b).f (a + b + 1)).hom w =
        m.indexGradedPieceD1X hM b (b + 1) (a + b) f := by
  -- The lift `s'` of `f` to the `(b + 1)`-st stage of the filtration, its extension by zero, and
  -- the element `w` of the `b`-th stage given by its twisted differential.
  set f₀ := (rowFiniteIndexGradedPieceComplexXEquiv hM (b + 1) (a + b) f :
    {x // ind x = b + 1} →₀ M)
  set ef := f₀.mapDomain Subtype.val with hef
  have hef_mem : ef ∈ rowFiniteIndexGrading ℳ ind (b + 1) (a + b) :=
    mem_rowFiniteIndexGrading_iff.2
      ⟨(mem_rowFiniteIndexFiltration_iff ind).1
          (mapDomain_subtypeVal_mem_rowFiniteIndexFiltration (R := R) f₀),
        (mem_rowFiniteTotalGrading_iff ℳ ind).1 (mapDomain_subtypeVal_mem_rowFiniteTotalGrading
          (rowFiniteIndexGradedPieceComplexXEquiv hM (b + 1) (a + b) f).2)⟩
  let s' := (m.indexCochainComplexXEquiv hM hm (b + 1) (a + b)).symm ⟨ef, hef_mem⟩
  have hs' : (m.indexCochainComplexXEquiv hM hm (b + 1) (a + b) s' : P →₀ M) = ef :=
    congrArg Subtype.val ((m.indexCochainComplexXEquiv hM hm (b + 1) (a + b)).apply_symm_apply
      ⟨ef, hef_mem⟩)
  have hds' : (m.indexCochainComplexXEquiv hM hm (b + 1) (a + b + 1)
      (((m.indexCochainComplex hM hm (b + 1)).d (a + b) (a + b + 1)).hom s') : P →₀ M) =
      m.coefficientDifferential hM ef := by
    rw [m.indexCochainComplexXEquiv_d, hs']
  have hw_mem : m.coefficientDifferential hM ef ∈ rowFiniteIndexGrading ℳ ind b (a + b + 1) :=
    mem_rowFiniteIndexGrading_iff.2
      ⟨m.coefficientDifferential_mapDomain_apply_eq_zero hM hm b (b + 1) rfl (a + b) f hf, by
        rw [← hds']
        exact (mem_rowFiniteIndexGrading_iff.1 (m.indexCochainComplexXEquiv hM hm (b + 1)
          (a + b + 1) (((m.indexCochainComplex hM hm (b + 1)).d (a + b)
            (a + b + 1)).hom s')).2).2⟩
  let w := (m.indexCochainComplexXEquiv hM hm b (a + b + 1)).symm ⟨_, hw_mem⟩
  have hw : (m.indexCochainComplexXEquiv hM hm b (a + b + 1) w : P →₀ M) =
      m.coefficientDifferential hM ef :=
    congrArg Subtype.val ((m.indexCochainComplexXEquiv hM hm b (a + b + 1)).apply_symm_apply
      ⟨_, hw_mem⟩)
  -- The transition map sends `w` to the differential of `s'`.
  have hofLE : ((m.indexCochainComplexMap hM hm (Int.le_add_one le_rfl)).f (a + b + 1)).hom
      w = ((m.indexCochainComplex hM hm (b + 1)).d (a + b) (a + b + 1)).hom s' :=
    (m.indexCochainComplexXEquiv hM hm (b + 1) (a + b + 1)).injective (Subtype.ext (by
      rw [m.indexCochainComplexMap_apply, hw, hds']))
  -- The projections of `s'` and `w` to the graded pieces.
  have hprojs : ((m.indexCochainComplexProj hM hm (b + 1)).f (a + b)).hom s' = f :=
    (rowFiniteIndexGradedPieceComplexXEquiv hM (b + 1) (a + b)).injective (Subtype.ext
      (Finsupp.ext fun x ↦ by
        rw [m.indexCochainComplexProj_f_apply, rowFiniteIndexProjection_apply]
        simp only [hs', hef]
        exact Finsupp.mapDomain_apply_of_injective Subtype.val_injective _ _))
  have hprojw : ((m.indexCochainComplexProj hM hm b).f (a + b + 1)).hom w =
      m.indexGradedPieceD1X hM b (b + 1) (a + b) f :=
    (rowFiniteIndexGradedPieceComplexXEquiv hM b (a + b + 1)).injective (Subtype.ext
      (Finsupp.ext fun y ↦ by
        rw [m.indexCochainComplexProj_f_apply, rowFiniteIndexProjection_apply,
          rowFiniteIndexGradedPieceComplexXEquiv_indexGradedPieceD1X_apply]
        simp only [hw, hef, f₀]))
  exact ⟨s', w, hofLE, hprojs, hprojw⟩

/-- The transition map of the index filtration sends the image of `w` to the differential of the
image of `s`, when it sends `w` to the differential of `s`. -/
private theorem indexFiltrationFunctor_map_objIso_inv_apply (a b : ℤ)
    (s' : (m.indexCochainComplex hM hm (b + 1)).X (a + b))
    (w : (m.indexCochainComplex hM hm b).X (a + b + 1))
    (hofLE : ((m.indexCochainComplexMap hM hm (Int.le_add_one le_rfl)).f (a + b + 1)).hom w =
      ((m.indexCochainComplex hM hm (b + 1)).d (a + b) (a + b + 1)).hom s') :
    (((m.indexFiltrationFunctor hM hm).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b = b from rfl) rfl))).f
        (a + b + 1)).hom
        (((m.indexFiltrationFunctorObjIso hM hm b).inv.f (a + b + 1)).hom w) =
      (((m.indexFiltrationFunctor hM hm).obj ((b + 1 : ℤ) : EInt)).d (a + b) (a + b + 1)).hom
        (((m.indexFiltrationFunctorObjIso hM hm (b + 1)).inv.f (a + b)).hom s') := by
  set t := ((m.indexFiltrationFunctorObjIso hM hm b).inv.f (a + b + 1)).hom w
  have hinj : Function.Injective
      ((m.indexFiltrationFunctorObjIso hM hm (b + 1)).hom.f (a + b + 1)).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  refine hinj ?_
  have h₁ := congrArg (fun φ ↦ (φ.f (a + b + 1)).hom t)
    (m.indexFiltrationFunctor_map_objIso_hom hM hm b)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
  rw [h₁, show ((m.indexFiltrationFunctorObjIso hM hm b).hom.f (a + b + 1)).hom t = w from
    congrArg (fun φ ↦ (φ.f (a + b + 1)).hom w)
      (m.indexFiltrationFunctorObjIso hM hm b).inv_hom_id, hofLE,
    HomologicalComplex.Hom.comm_apply]
  exact (congrArg (fun φ ↦ (φ.f (a + b + 1)).hom
    (((m.indexCochainComplex hM hm (b + 1)).d (a + b) (a + b + 1)).hom s'))
    (m.indexFiltrationFunctorObjIso hM hm (b + 1)).inv_hom_id).symm

/-- The image in the cokernel of the transition map of the image of `s'` is the image of `f`, when
`s'` projects to `f` in the graded piece. -/
private theorem cokernel_π_objIso_inv_apply (a b : ℤ)
    (s' : (m.indexCochainComplex hM hm (b + 1)).X (a + b))
    (f : (rowFiniteIndexGradedPieceComplex ind hM (b + 1)).X (a + b))
    (hprojs : ((m.indexCochainComplexProj hM hm (b + 1)).f (a + b)).hom s' = f) :
    ((cokernel.π ((m.indexFiltrationFunctor hM hm).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b = b from rfl) rfl)))).f
        (a + b)).hom
        (((m.indexFiltrationFunctorObjIso hM hm (b + 1)).inv.f (a + b)).hom s') =
      ((m.indexCokernelIsoOfEq hM hm b (b + 1) rfl).inv.f (a + b)).hom f := by
  set Fn := m.indexFiltrationFunctor hM hm
  set s := ((m.indexFiltrationFunctorObjIso hM hm (b + 1)).inv.f (a + b)).hom s'
  have h₁ := congrArg (fun φ ↦ (φ.f (a + b)).hom s)
    (m.cokernel_π_comp_indexCokernelIsoOfEq_hom hM hm b (b + 1) rfl)
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
  rw [show ((m.indexFiltrationFunctorObjIso hM hm (b + 1)).hom.f (a + b)).hom s = s' from
    congrArg (fun φ ↦ (φ.f (a + b)).hom s')
      (m.indexFiltrationFunctorObjIso hM hm (b + 1)).inv_hom_id, hprojs] at h₁
  have h₂ := congrArg (fun φ ↦ (φ.f (a + b)).hom (((cokernel.π (Fn.map (homOfLE
    (CochainComplex.coe_le_coe_of_eq_add_one (show b = b from rfl) rfl)))).f
        (a + b)).hom s))
    (m.indexCokernelIsoOfEq hM hm b (b + 1) rfl).hom_inv_id
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply] at h₂
  rw [h₁] at h₂
  exact h₂.symm

/-- The image in the cokernel of the inclusion `F_{b-1} ⟶ F_b` of the image of `w` is the
restriction of the twisted differential of `f`, when `w` projects to it in the graded piece. -/
private theorem cokernel_π_objIso_inv_apply_d1X (a b : ℤ)
    (w : (m.indexCochainComplex hM hm b).X (a + b + 1))
    (f : (rowFiniteIndexGradedPieceComplex ind hM (b + 1)).X (a + b))
    (hprojw : ((m.indexCochainComplexProj hM hm b).f (a + b + 1)).hom w =
      m.indexGradedPieceD1X hM b (b + 1) (a + b) f) :
    ((m.indexCokernelIsoOfEq hM hm (b - 1) b (by omega)).hom.f (a + b + 1)).hom
      (((cokernel.π ((m.indexFiltrationFunctor hM hm).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b - 1 = b - 1 from rfl)
      (show b = b - 1 + 1 by lia))))).f (a + b + 1)).hom
        (((m.indexFiltrationFunctorObjIso hM hm b).inv.f (a + b + 1)).hom w)) =
      m.indexGradedPieceD1X hM b (b + 1) (a + b) f := by
  set t := ((m.indexFiltrationFunctorObjIso hM hm b).inv.f (a + b + 1)).hom w
  have h₁ := congrArg (fun φ ↦ (φ.f (a + b + 1)).hom t)
    (m.cokernel_π_comp_indexCokernelIsoOfEq_hom hM hm (b - 1) b (by omega))
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
  rw [show ((m.indexFiltrationFunctorObjIso hM hm b).hom.f (a + b + 1)).hom t = w from
    congrArg (fun φ ↦ (φ.f (a + b + 1)).hom w)
      (m.indexFiltrationFunctorObjIso hM hm b).inv_hom_id] at h₁
  exact h₁.trans hprojw

/-- **The first differential of the row-finite index spectral sequence.** On the first page
(page `2` in Mathlib's numbering), the differential from `(a, b)` to `(a + 2, b - 1)` sends the
class of a cycle `f` of the graded piece of the generators of index `b + 1` to the class of the
restriction of the twisted differential of `f`, extended by zero, to the generators of index
`b`. -/
theorem indexSpectralSequence_page_two_d_apply (a b : ℤ)
    (f : (rowFiniteIndexGradedPieceComplex ind hM (b + 1)).X (a + b))
    (hf : ((rowFiniteIndexGradedPieceComplex ind hM (b + 1)).d (a + b) (a + b + 1)).hom f = 0) :
    (m.indexSpectralSequenceFirstPageXIsoOfEq hM hm (a + 2, b - 1) (b - 1) b rfl (by omega)
        (a + b + 1) (by simp only; omega)).hom
      ((((m.indexSpectralSequence hM hm).page 2).d (a, b) (a + 2, b - 1)).hom
        ((m.indexSpectralSequenceFirstPageXIsoOfEq hM hm (a, b) b (b + 1) rfl rfl (a + b) rfl).inv
          (((rowFiniteIndexGradedPieceComplex ind hM (b + 1)).homologyπ (a + b)).hom
            ((rowFiniteIndexGradedPieceComplex ind hM (b + 1)).moduleCatCyclesMk f (a + b + 1)
              (by simp) hf)))) =
      ((rowFiniteIndexGradedPieceComplex ind hM b).homologyπ (a + b + 1)).hom
        ((rowFiniteIndexGradedPieceComplex ind hM b).moduleCatCyclesMk
          (m.indexGradedPieceD1X hM b (b + 1) (a + b) f) (a + b + 1 + 1) (by simp)
          (m.d_indexGradedPieceD1X hM hm b (b + 1) rfl (a + b) f hf)) := by
  have hcls := congrArg (fun φ ↦ φ.hom (((rowFiniteIndexGradedPieceComplex ind hM (b + 1)).homologyπ
    (a + b)).hom ((rowFiniteIndexGradedPieceComplex ind hM (b + 1)).moduleCatCyclesMk f (a + b + 1)
      (by simp) hf))) (m.page_two_d_comp_eq hM hm a b)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hcls
  refine hcls.trans ?_
  rw [HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  obtain ⟨s', w, hofLE, hprojs, hprojw⟩ := m.exists_lift_indexGradedPieceD1X hM hm a b f hf
  have hz₃ : ((cokernel ((m.indexFiltrationFunctor hM hm).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b = b from rfl) rfl)))).d
        (a + b) (a + b + 1))
      (((m.indexCokernelIsoOfEq hM hm b (b + 1) rfl).inv.f (a + b)).hom f) = 0 := by
    rw [HomologicalComplex.Hom.comm_apply]
    exact (congrArg _ hf).trans (map_zero _)
  obtain ⟨hc, hδ⟩ := exists_δ_kernelCokernelSequence_L₃_eq
    ((m.indexFiltrationFunctor hM hm).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b - 1 = b - 1 from rfl)
      (show b = b - 1 + 1 by lia))))
    ((m.indexFiltrationFunctor hM hm).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (show b = b from rfl) rfl))) (a + b)
    (((m.indexFiltrationFunctorObjIso hM hm (b + 1)).inv.f (a + b)).hom s')
    (((m.indexFiltrationFunctorObjIso hM hm b).inv.f (a + b + 1)).hom w)
    (m.indexFiltrationFunctor_map_objIso_inv_apply hM hm a b s' w hofLE) _ hz₃
    (m.cokernel_π_objIso_inv_apply hM hm a b s' f hprojs)
  refine (congrArg (HomologicalComplex.homologyMap
    (m.indexCokernelIsoOfEq hM hm (b - 1) b (by omega)).hom (a + b + 1)).hom hδ).trans ?_
  refine (HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk _ _ _ _ hc).trans ?_
  simp only [m.cokernel_π_objIso_inv_apply_d1X hM hm a b w f hprojw]

end RowFiniteTwistingCocycle

end TauCeti
