/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Filtration
-- The stage inclusions reuse the graded-complex construction of the coefficient complex.
import all TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The index filtration of a row-finite twisted complex with coefficients

Let `m` be a row-finite twisting cocycle on an arbitrary graded set of generators `P`, and let
`M` be a DG right module. The twisted complex `M ⊗ ⟨P⟩` has underlying module `P →₀ M`. Its
index filtration `F_p` consists of the coefficient vectors supported on generators of index at
most `p`. If `m` is one-sided (`m x y = 0` whenever `ind x ≤ ind y`), every twisting term of the
differential strictly lowers the index, so each `F_p` is a subcomplex.

Unlike the finite case, the filtration need not be bounded: it is exhaustive in every degree
(every vector has finite support), and it starts at zero below a lower bound for the indices.
The graded piece `F_p / F_{p-1}` is the twisted complex of the zero cocycle on the generators of
index `p`, that is, finitely supported families of elements of `M` with the coefficient
differential acting coordinatewise. These are the filtered-complex inputs to the index spectral
sequence of a twisted complex over an infinite cell structure.

## Main definitions

* `TauCeti.RowFiniteTwistingCocycle.indexCochainComplex`: the stage `F_p` as a cochain complex.
* `TauCeti.RowFiniteTwistingCocycle.indexSubobject`: the stages as subobjects of the
  coefficient complex.
* `TauCeti.RowFiniteTwistingCocycle.indexCochainComplexProj`: the restriction `F_p ⟶ M ⊗ ⟨P_p⟩`
  to the generators of index `p`.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.coefficientDifferential_sub_mem_rowFiniteIndexFiltration`:
  the twisting part of the differential strictly lowers the index filtration.
* `TauCeti.RowFiniteTwistingCocycle.exists_mem_range_indexSubobject_arrow_f`: the filtration is
  exhaustive in every degree.
* `TauCeti.RowFiniteTwistingCocycle.indexSubobject_eq_bot`: the filtration vanishes below all
  generator indices.
* `TauCeti.RowFiniteTwistingCocycle.shortExact_indexCochainComplexMap_proj`: the sequence
  `F_p ⟶ F_{p+1} ⟶ M ⊗ ⟨P_{p+1}⟩` is short exact.

## Implementation notes

This module adapts the finite construction of `TauCeti.Algebra.Homology.DG.Twisted.Filtration`
to finite-support vectors on an arbitrary generator set. `indexCochainComplex`,
`indexCochainComplexMap`, `indexCochainComplexι`, `indexSubobject`, `indexCochainComplexProj`
and `shortExact_indexCochainComplexMap_proj` follow `TwistingCocycle.twistedIndexCochainComplex`,
`TwistingCocycle.twistedIndexCochainComplexMap`, `TwistingCocycle.twistedIndexCochainComplexι`,
`TwistingCocycle.twistedIndexSubobject`, `TwistingCocycle.twistedIndexCochainComplexProj` and
`TwistingCocycle.twistedIndexShortComplex_shortExact` there.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
-/

public noncomputable section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM} {P : Type uP}
  [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]
  {ind : P → ℤ}

namespace RowFiniteTwistingCocycle

variable {dA : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 dA} {dM : M →ₗ[R] M}
  (m : RowFiniteTwistingCocycle 𝒜 dA P ind) (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)
  (hM : IsDGRightModule hA ℳ dM)

/-! ### The differential and the index filtration -/

section Differential

include hm

/-- The twisting part of the coefficient differential strictly lowers the index filtration. -/
theorem coefficientDifferential_sub_mem_rowFiniteIndexFiltration {p : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind p) :
    m.coefficientDifferential hM f - Finsupp.mapRange.linearMap dM f ∈
      rowFiniteIndexFiltration (R := R) ind (p - 1) := by
  classical
  -- Reduce to elementary vectors `single x α` with `ind x ≤ p` and `α` homogeneous.
  have key : ∀ x, ind x ≤ p → ∀ α : M, m.coefficientDifferential hM (Finsupp.single x α) -
      Finsupp.mapRange.linearMap dM (Finsupp.single x α) ∈
        rowFiniteIndexFiltration (R := R) ind (p - 1) := by
    intro x hx α
    induction α using DirectSum.Decomposition.inductionOn ℳ with
    | zero => simp
    | @homogeneous q α =>
      rw [m.coefficientDifferential_single hM x α.2, Finsupp.mapRange.linearMap_apply,
        Finsupp.mapRange_single, add_sub_cancel_left, Units.smul_def]
      refine zsmul_mem (Submodule.finsuppSum_mem _ _ _ _ fun y hy ↦ ?_) _
      have hyx : ind y < ind x := lt_of_not_ge fun h ↦ hy (hm x y h)
      exact (mem_rowFiniteIndexFiltration_iff ind).mpr fun z hz ↦
        Finsupp.single_eq_of_ne (by rintro rfl; omega)
    | add α β hα hβ =>
      simpa only [Finsupp.single_add, map_add, add_sub_add_comm] using add_mem hα hβ
  rw [← LinearMap.sub_apply, ← Finsupp.sum_single f, map_finsuppSum]
  refine Submodule.finsuppSum_mem _ _ _ _ fun x hx ↦ key x ?_ _
  by_contra h
  exact hx ((mem_rowFiniteIndexFiltration_iff ind).mp hf x (lt_of_not_ge h))

/-- The coefficient differential preserves every stage of the index filtration. -/
theorem coefficientDifferential_mem_rowFiniteIndexFiltration {p : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind p) :
    m.coefficientDifferential hM f ∈ rowFiniteIndexFiltration (R := R) ind p := by
  have hcoeff : Finsupp.mapRange.linearMap dM f ∈ rowFiniteIndexFiltration (R := R) ind p :=
    (mem_rowFiniteIndexFiltration_iff ind).mpr fun x hx ↦ by
      simp [(mem_rowFiniteIndexFiltration_iff ind).mp hf x hx]
  have h := rowFiniteIndexFiltration_mono (R := R) (A := M) ind (by omega : p - 1 ≤ p)
    (m.coefficientDifferential_sub_mem_rowFiniteIndexFiltration hm hM hf)
  simpa only [sub_add_cancel] using add_mem h hcoeff

/-- On the generators of index `p`, the differential of a vector of `F_p` is the coefficient
differential of its restriction: the twisted differential of the zero cocycle. -/
theorem subtypeDomain_coefficientDifferential {p : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind p) :
    (m.coefficientDifferential hM f).subtypeDomain (fun x ↦ ind x = p) =
      (0 : RowFiniteTwistingCocycle 𝒜 dA {x // ind x = p} fun x ↦ ind x).coefficientDifferential
        hM (f.subtypeDomain fun x ↦ ind x = p) := by
  ext x
  have h := (mem_rowFiniteIndexFiltration_iff ind).mp
    (m.coefficientDifferential_sub_mem_rowFiniteIndexFiltration hm hM hf) x.val (by omega)
  simpa [sub_eq_zero] using h

end Differential

/-! ### The filtration stages as cochain complexes -/

section Complex

include hm

/-- The coefficient differential carries the degree-`n` part of `F_p` into degree `n + 1`. -/
theorem coefficientDifferential_mem_rowFiniteIndexGrading {p n : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexGrading ℳ ind p n) :
    m.coefficientDifferential hM f ∈ rowFiniteIndexGrading ℳ ind p (n + 1) :=
  mem_rowFiniteIndexGrading_iff.mpr
    ⟨m.coefficientDifferential_mem_rowFiniteIndexFiltration hm hM
        (mem_rowFiniteIndexGrading_iff.mp hf).1,
      (m.isHomogeneous_coefficientDifferential hM).map_mem (mem_rowFiniteIndexGrading_iff.mp hf).2⟩

/-- The `p`-th stage `F_p` of the index filtration as a cochain complex of modules. -/
def indexCochainComplex (p : ℤ) : CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (rowFiniteIndexGrading ℳ ind p) (m.coefficientDifferential hM)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦
      m.coefficientDifferential_mem_rowFiniteIndexGrading hm hM hf)
    fun _ f ↦ m.coefficientDifferential_sq_zero hM f

/-- The degree-`n` term of `F_p` is the intersection of the filtration stage with the total
grading. -/
def indexCochainComplexXEquiv (p n : ℤ) :
    (m.indexCochainComplex hm hM p).X n ≃ₗ[R] rowFiniteIndexGrading ℳ ind p n :=
  gradedCochainComplexXEquiv n

/-- The differential of `F_p` is the coefficient differential. -/
theorem indexCochainComplexXEquiv_d (p n : ℤ) (f : (m.indexCochainComplex hm hM p).X n) :
    (m.indexCochainComplexXEquiv hm hM p (n + 1)
        (((m.indexCochainComplex hm hM p).d n (n + 1)).hom f) : P →₀ M) =
      m.coefficientDifferential hM (m.indexCochainComplexXEquiv hm hM p n f) :=
  gradedCochainComplexXEquiv_d n f

/-- The inclusion `F_p ⟶ F_q` of filtration stages, for `p ≤ q`. -/
def indexCochainComplexMap {p q : ℤ} (hpq : p ≤ q) :
    m.indexCochainComplex hm hM p ⟶ m.indexCochainComplex hm hM q :=
  gradedCochainComplexInclusion fun _ ↦ rowFiniteIndexGrading_mono hpq

@[simp]
theorem indexCochainComplexMap_apply {p q : ℤ} (hpq : p ≤ q) (n : ℤ)
    (f : (m.indexCochainComplex hm hM p).X n) :
    (m.indexCochainComplexXEquiv hm hM q n
        (((m.indexCochainComplexMap hm hM hpq).f n).hom f) : P →₀ M) =
      m.indexCochainComplexXEquiv hm hM p n f :=
  gradedCochainComplexInclusion_apply _ n f

/-- The inclusion `F_p ⟶ F_q` is injective in each degree. -/
theorem injective_indexCochainComplexMap_f {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    Function.Injective ((m.indexCochainComplexMap hm hM hpq).f n) := fun f g hfg ↦
  (m.indexCochainComplexXEquiv hm hM p n).injective (Subtype.ext (by
    simpa only [indexCochainComplexMap_apply] using
      congrArg (fun t ↦ (m.indexCochainComplexXEquiv hm hM q n t : P →₀ M)) hfg))

/-- The inclusion of a filtration stage into the coefficient complex. -/
def indexCochainComplexι (p : ℤ) :
    m.indexCochainComplex hm hM p ⟶ m.coefficientCochainComplex hM :=
  gradedCochainComplexInclusion (rowFiniteIndexGrading_le_rowFiniteTotalGrading p)

@[simp]
theorem indexCochainComplexι_apply (p n : ℤ) (f : (m.indexCochainComplex hm hM p).X n) :
    (m.coefficientCochainComplexXEquiv hM n (((m.indexCochainComplexι hm hM p).f n).hom f) :
        P →₀ M) =
      m.indexCochainComplexXEquiv hm hM p n f :=
  gradedCochainComplexInclusion_apply _ n f

instance mono_indexCochainComplexι (p : ℤ) : Mono (m.indexCochainComplexι hm hM p) := by
  refine HomologicalComplex.mono_of_mono_f _ fun n ↦ (ModuleCat.mono_iff_injective _).mpr ?_
  intro f g hfg
  apply (m.indexCochainComplexXEquiv hm hM p n).injective
  apply Subtype.ext
  simpa only [indexCochainComplexι_apply] using
    congrArg (fun t ↦ (m.coefficientCochainComplexXEquiv hM n t : P →₀ M)) hfg

@[reassoc (attr := simp)]
theorem indexCochainComplexMap_ι {p q : ℤ} (hpq : p ≤ q) :
    m.indexCochainComplexMap hm hM hpq ≫ m.indexCochainComplexι hm hM q =
      m.indexCochainComplexι hm hM p := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_)
  apply (m.coefficientCochainComplexXEquiv hM n).injective
  apply Subtype.ext
  simp

instance mono_indexCochainComplexMap {p q : ℤ} (hpq : p ≤ q) :
    Mono (m.indexCochainComplexMap hm hM hpq) :=
  mono_of_mono_fac (m.indexCochainComplexMap_ι hm hM hpq)

@[simp]
theorem indexCochainComplexMap_refl (p : ℤ) :
    m.indexCochainComplexMap hm hM (le_refl p) = 𝟙 _ := by
  simp [← cancel_mono (m.indexCochainComplexι hm hM p)]

@[reassoc (attr := simp)]
theorem indexCochainComplexMap_comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    m.indexCochainComplexMap hm hM hpq ≫ m.indexCochainComplexMap hm hM hqr =
      m.indexCochainComplexMap hm hM (hpq.trans hqr) := by
  simp [← cancel_mono (m.indexCochainComplexι hm hM r)]

/-- The index filtration as subobjects of the coefficient complex. -/
def indexSubobject (p : ℤ) : Subobject (m.coefficientCochainComplex hM) :=
  Subobject.mk (m.indexCochainComplexι hm hM p)

theorem indexSubobject_eq_mk (p : ℤ) :
    m.indexSubobject hm hM p = Subobject.mk (m.indexCochainComplexι hm hM p) :=
  (rfl)

/-- In degree `n`, the `p`-th stage of the filtration consists of the vectors vanishing on the
generators of index greater than `p`. -/
theorem mem_range_indexSubobject_arrow_f_iff (p n : ℤ) (f : (m.coefficientCochainComplex hM).X n) :
    f ∈ LinearMap.range ((m.indexSubobject hm hM p).arrow.f n).hom ↔
      ∀ x, p < ind x → (m.coefficientCochainComplexXEquiv hM n f : P →₀ M) x = 0 := by
  rw [indexSubobject_eq_mk, ← Subobject.underlyingIso_hom_comp_eq_mk, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.2 ((ModuleCat.epi_iff_surjective _).1 inferInstance))]
  constructor
  · rintro ⟨g, rfl⟩
    rw [indexCochainComplexι_apply]
    exact (mem_rowFiniteIndexFiltration_iff ind).mp
      (mem_rowFiniteIndexGrading_iff.mp (m.indexCochainComplexXEquiv hm hM p n g).2).1
  · intro hf
    let g := m.coefficientCochainComplexXEquiv hM n f
    have hg : (g : P →₀ M) ∈ rowFiniteIndexGrading ℳ ind p n :=
      mem_rowFiniteIndexGrading_iff.mpr ⟨(mem_rowFiniteIndexFiltration_iff ind).mpr hf, g.2⟩
    refine ⟨(m.indexCochainComplexXEquiv hm hM p n).symm ⟨g, hg⟩, ?_⟩
    apply (m.coefficientCochainComplexXEquiv hM n).injective
    apply Subtype.ext
    simp [g]

/-- The index filtration is increasing. -/
theorem indexSubobject_mono : Monotone (m.indexSubobject hm hM) := fun _ _ hpq ↦
  Subobject.mk_le_mk_of_comm (m.indexCochainComplexMap hm hM hpq)
    (m.indexCochainComplexMap_ι hm hM hpq)

/-- The index filtration is exhaustive in every degree: every finite-support vector lies in
some stage, without a bound on the generator indices. -/
theorem exists_mem_range_indexSubobject_arrow_f (n : ℤ)
    (f : (m.coefficientCochainComplex hM).X n) :
    ∃ p, f ∈ LinearMap.range ((m.indexSubobject hm hM p).arrow.f n).hom := by
  have hf : (m.coefficientCochainComplexXEquiv hM n f : P →₀ M) ∈
      ⨆ p, rowFiniteIndexFiltration (R := R) ind p := by
    rw [iSup_rowFiniteIndexFiltration_eq_top]
    exact Submodule.mem_top
  obtain ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed _
    (rowFiniteIndexFiltration_mono (R := R) (A := M) ind).directed_le).mp hf
  exact ⟨p, (m.mem_range_indexSubobject_arrow_f_iff hm hM p n f).mpr
    ((mem_rowFiniteIndexFiltration_iff ind).mp hp)⟩

/-- Below all generator indices the index filtration vanishes. -/
theorem indexSubobject_eq_bot {p : ℤ} (hp : ∀ x, p < ind x) :
    m.indexSubobject hm hM p = ⊥ := by
  refine Subobject.mk_eq_bot_iff_zero.mpr (HomologicalComplex.hom_ext _ _ fun n ↦
    ModuleCat.hom_ext (LinearMap.ext fun f ↦ ?_))
  apply (m.coefficientCochainComplexXEquiv hM n).injective
  apply Subtype.ext
  ext x
  simpa using (mem_rowFiniteIndexFiltration_iff ind).mp
    (mem_rowFiniteIndexGrading_iff.mp (m.indexCochainComplexXEquiv hm hM p n f).2).1 x (hp x)

/-- Above all generator indices the index filtration is the whole coefficient complex. -/
theorem indexSubobject_eq_top {p : ℤ} (hp : ∀ x, ind x ≤ p) :
    m.indexSubobject hm hM p = ⊤ := by
  have : ∀ n, IsIso ((m.indexCochainComplexι hm hM p).f n) := fun n ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr
      ⟨(ModuleCat.mono_iff_injective _).mp inferInstance, fun f ↦ by
        have hf := (m.mem_range_indexSubobject_arrow_f_iff hm hM p n f).mpr
          fun x hx ↦ absurd (hp x) (not_le.mpr hx)
        rw [indexSubobject_eq_mk, ← Subobject.underlyingIso_hom_comp_eq_mk] at hf
        obtain ⟨g, rfl⟩ := hf
        exact ⟨_, rfl⟩⟩
  have := HomologicalComplex.Hom.isIso_of_components (m.indexCochainComplexι hm hM p)
  exact Subobject.mk_eq_top_of_isIso _

end Complex

/-! ### The graded pieces of the index filtration -/

section GradedPiece

/-- Restriction of a vector of total degree `n` to the generators of index `p`. -/
private def restrictIndex (p n : ℤ) :
    rowFiniteIndexGrading ℳ ind p n →ₗ[R]
      rowFiniteTotalGrading ℳ (fun x : {x // ind x = p} ↦ ind x) n :=
  ((rowFiniteIndexProjection ind p).comp
    (Submodule.inclusion (rowFiniteIndexGrading_le_rowFiniteIndexFiltration p n))).codRestrict _
    fun f ↦ (mem_rowFiniteTotalGrading_iff ℳ _).mpr fun x ↦ by
      rw [LinearMap.comp_apply, rowFiniteIndexProjection_apply, Submodule.coe_inclusion]
      exact (mem_rowFiniteTotalGrading_iff ℳ ind).mp (mem_rowFiniteIndexGrading_iff.mp f.2).2 x

omit [DirectSum.Decomposition ℳ] in
private theorem restrictIndex_apply (p n : ℤ) (f : rowFiniteIndexGrading ℳ ind p n) :
    (restrictIndex p n f : {x // ind x = p} →₀ M) = (f : P →₀ M).subtypeDomain (ind · = p) := by
  ext x
  rw [restrictIndex, LinearMap.codRestrict_apply, LinearMap.comp_apply,
    rowFiniteIndexProjection_apply, Submodule.coe_inclusion, Finsupp.subtypeDomain_apply]

include hm

/-- The restriction `F_p ⟶ M ⊗ ⟨P_p⟩` from the `p`-th stage of the index filtration to the
twisted complex of the zero cocycle on the generators of index `p`. -/
def indexCochainComplexProj (p : ℤ) :
    m.indexCochainComplex hm hM p ⟶
      (0 : RowFiniteTwistingCocycle 𝒜 dA {x // ind x = p} fun x ↦ ind x).coefficientCochainComplex
        hM where
  f n := ModuleCat.ofHom ((coefficientCochainComplexXEquiv _ hM n).symm.toLinearMap ∘ₗ
    restrictIndex p n ∘ₗ (m.indexCochainComplexXEquiv hm hM p n).toLinearMap)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦ (coefficientCochainComplexXEquiv _ hM
      (i + 1)).injective (Subtype.ext ?_))
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearEquiv.coe_coe, coefficientCochainComplexXEquiv_d, LinearEquiv.apply_symm_apply,
      restrictIndex_apply, indexCochainComplexXEquiv_d]
    exact (m.subtypeDomain_coefficientDifferential hm hM
      (mem_rowFiniteIndexGrading_iff.mp (m.indexCochainComplexXEquiv hm hM p i f).2).1).symm

/-- The restriction map restricts the underlying vector to the generators of index `p`. -/
@[simp]
theorem indexCochainComplexProj_f_apply (p n : ℤ) (f : (m.indexCochainComplex hm hM p).X n) :
    (coefficientCochainComplexXEquiv _ hM n (((m.indexCochainComplexProj hm hM p).f n).hom f) :
        {x // ind x = p} →₀ M) =
      (m.indexCochainComplexXEquiv hm hM p n f : P →₀ M).subtypeDomain (ind · = p) := by
  simp [indexCochainComplexProj, restrictIndex_apply]

@[reassoc (attr := simp)]
theorem indexCochainComplexMap_comp_proj (p : ℤ) :
    m.indexCochainComplexMap hm hM (Int.le_add_one le_rfl) ≫
      m.indexCochainComplexProj hm hM (p + 1) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
    (coefficientCochainComplexXEquiv _ hM n).injective (Subtype.ext ?_))
  ext x
  simpa using (mem_rowFiniteIndexFiltration_iff ind).mp
    (mem_rowFiniteIndexGrading_iff.mp (m.indexCochainComplexXEquiv hm hM p n f).2).1 x
    (by omega)

/-- The restriction `F_p ⟶ M ⊗ ⟨P_p⟩` is surjective in each degree: a vector on the generators
of index `p` extends by zero. -/
theorem surjective_indexCochainComplexProj_f (p n : ℤ) :
    Function.Surjective ((m.indexCochainComplexProj hm hM p).f n) := by
  classical
  intro g
  let g' := (coefficientCochainComplexXEquiv _ hM n g : {x // ind x = p} →₀ M)
  have hg' : g'.extendDomain ∈ rowFiniteIndexGrading ℳ ind p n := by
    refine mem_rowFiniteIndexGrading_iff.mpr ⟨(mem_rowFiniteIndexFiltration_iff ind).mpr
      fun x hx ↦ ?_, (mem_rowFiniteTotalGrading_iff ℳ ind).mpr fun x ↦ ?_⟩
    · simp [Finsupp.extendDomain_apply, hx.ne']
    · rw [Finsupp.extendDomain_apply]
      split_ifs with hx
      · exact (mem_rowFiniteTotalGrading_iff ℳ _).mp (coefficientCochainComplexXEquiv _ hM n g).2
          ⟨x, hx⟩
      · exact zero_mem _
  refine ⟨(m.indexCochainComplexXEquiv hm hM p n).symm ⟨_, hg'⟩,
    (coefficientCochainComplexXEquiv _ hM n).injective (Subtype.ext ?_)⟩
  simp [g']

/-- A vector of `F_{p+1}` vanishing on the generators of index `p + 1` comes from `F_p`. -/
theorem exists_indexCochainComplexMap_f_eq (p n : ℤ)
    (g : (m.indexCochainComplex hm hM (p + 1)).X n)
    (hg : ((m.indexCochainComplexProj hm hM (p + 1)).f n) g = 0) :
    ∃ f, ((m.indexCochainComplexMap hm hM (Int.le_add_one le_rfl)).f n) f = g := by
  have hg' := congrArg (fun t ↦
    (coefficientCochainComplexXEquiv _ hM n t : {x // ind x = p + 1} →₀ M)) hg
  simp only [indexCochainComplexProj_f_apply, map_zero, ZeroMemClass.coe_zero] at hg'
  have hmem := mem_rowFiniteIndexGrading_iff.mp (m.indexCochainComplexXEquiv hm hM (p + 1) n g).2
  have hker : (⟨_, hmem.1⟩ : rowFiniteIndexFiltration (R := R) ind (p + 1)) ∈
      LinearMap.ker (rowFiniteIndexProjection ind (p + 1)) := by
    rw [LinearMap.mem_ker]
    ext x
    simpa using DFunLike.congr_fun hg' x
  rw [ker_rowFiniteIndexProjection, Submodule.mem_comap, add_sub_cancel_right] at hker
  have hp : (m.indexCochainComplexXEquiv hm hM (p + 1) n g : P →₀ M) ∈
      rowFiniteIndexGrading ℳ ind p n :=
    mem_rowFiniteIndexGrading_iff.mpr ⟨hker, hmem.2⟩
  exact ⟨(m.indexCochainComplexXEquiv hm hM p n).symm ⟨_, hp⟩,
    (m.indexCochainComplexXEquiv hm hM (p + 1) n).injective (Subtype.ext (by simp))⟩

/-- **The graded pieces of the index filtration.** The sequence
`F_p ⟶ F_{p+1} ⟶ M ⊗ ⟨P_{p+1}⟩` is short exact: the quotient `F_{p+1} / F_p` is the twisted
complex of the zero cocycle on the generators of index `p + 1`. -/
theorem shortExact_indexCochainComplexMap_proj (p : ℤ) :
    (ShortComplex.mk _ _ (m.indexCochainComplexMap_comp_proj hm hM p)).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    ShortComplex.ShortExact.mk'
      ((ShortComplex.moduleCat_exact_iff _).mpr
        (m.exists_indexCochainComplexMap_f_eq hm hM p n))
      ((ModuleCat.mono_iff_injective _).mpr
        (m.injective_indexCochainComplexMap_f hm hM (Int.le_add_one le_rfl) n))
      ((ModuleCat.epi_iff_surjective _).mpr
        (m.surjective_indexCochainComplexProj_f hm hM (p + 1) n))

end GradedPiece

end RowFiniteTwistingCocycle

end TauCeti
