/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Filtration
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive
-- Unfold the coefficient complex privately, to include the filtration stages into it.
import all TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Coefficients
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The index spectral sequence of a row-finite twisted complex

Let `m` be a row-finite twisting cocycle on an arbitrary graded set of generators `P`, and let
`ℳ` be a DG right module. The **index filtration** `F_p` of the coefficient complex `P →₀ M`
consists of the finite-support vectors carried by generators of index at most `p`. When the
cocycle is one-sided (`m x y = 0` whenever `ind x ≤ ind y`, automatic over a cohomologically
nonpositive algebra by `TwistingCocycle.one_sided_of_nonpos`), the twisted differential preserves
it: the coefficient differential keeps the generator, and every twisting term strictly lowers its
index.

This file builds the filtration stages as subcomplexes and their graded pieces, and the spectral
sequence of the filtration, extending the finite construction
`TwistingCocycle.indexSpectralSequence` to arbitrary generator sets.

* The graded piece `F_p / F_{p-1}` is the complex of finite-support families of coefficients on
  the generators of index `p`, with the coefficient differential in each coordinate
  (`RowFiniteTwistingCocycle.indexShortComplex_shortExact`). So the first page of the index
  spectral sequence is its cohomology
  (`RowFiniteTwistingCocycle.indexSpectralSequenceFirstPageXIso`).
* The filtration is exhaustive with no finiteness hypothesis on `P`, unlike a product of
  coefficient modules, so the induced filtration of the cohomology of the twisted complex is
  exhaustive (`RowFiniteTwistingCocycle.exists_mem_range_indexAbutmentFiltrationι`). It vanishes
  below a lower bound for the generator indices
  (`RowFiniteTwistingCocycle.indexSubobject_eq_bot`).
* If moreover `ℳ` is cohomologically nonpositive, as the chains of a fibre are, a vector of total
  degree `n` is carried by generators of index at most `-n`, so the graded pieces vanish in each
  degree from some index on. With generator indices bounded below, as for the cells of a CW
  complex, the spectral sequence then converges strongly
  (`RowFiniteTwistingCocycle.indexSpectralSequencePageXIsoGraded`).

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3--4.
* C. A. Weibel, *An Introduction to Homological Algebra*, Theorem 5.5.1.
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

section GradedPiece

variable (hM : IsDGRightModule hA ℳ dM) (ind) in
/-- The complex of finite-support families of coefficients on the generators of index `p`, with
the coefficient differential in each coordinate. It is the graded piece `F_p / F_{p-1}` of the
index filtration of a row-finite twisted complex
(`RowFiniteTwistingCocycle.indexShortComplex_shortExact`). -/
noncomputable def rowFiniteIndexGradedPieceComplex (p : ℤ) :
    CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (rowFiniteTotalGrading ℳ fun x : {x // ind x = p} ↦ ind x)
    (Finsupp.mapRange.linearMap dM)
    (LinearMap.isHomogeneous_def.mpr fun n f hf ↦ by
      rw [mem_rowFiniteTotalGrading_iff] at hf ⊢
      intro x
      simpa [add_right_comm] using hM.isHomogeneous.map_mem (hf x))
    fun _ f ↦ by ext x; simp [hM.sq_zero]

variable (hM : IsDGRightModule hA ℳ dM)

/-- Identify a term of the graded-piece complex with the families of total degree `n`. -/
noncomputable def rowFiniteIndexGradedPieceComplexXEquiv (p n : ℤ) :
    (rowFiniteIndexGradedPieceComplex ind hM p).X n ≃ₗ[R]
      rowFiniteTotalGrading ℳ (fun x : {x // ind x = p} ↦ ind x) n :=
  gradedCochainComplexXEquiv n

/-- The differential of the graded-piece complex is the coefficient differential in each
coordinate. -/
theorem rowFiniteIndexGradedPieceComplexXEquiv_d (p n : ℤ)
    (f : (rowFiniteIndexGradedPieceComplex ind hM p).X n) :
    (rowFiniteIndexGradedPieceComplexXEquiv hM p (n + 1)
        (((rowFiniteIndexGradedPieceComplex ind hM p).d n (n + 1)).hom f) :
          {x // ind x = p} →₀ M) =
      Finsupp.mapRange.linearMap dM (rowFiniteIndexGradedPieceComplexXEquiv hM p n f) :=
  gradedCochainComplexXEquiv_d n f

/-- For cohomologically nonpositive coefficients, the graded piece of index `p` vanishes in each
degree `n` with `0 < n + p`. -/
theorem isZero_rowFiniteIndexGradedPieceComplex_X (hℳ : ∀ k, 0 < k → ℳ k = ⊥) {p n : ℤ}
    (hpn : 0 < n + p) : IsZero ((rowFiniteIndexGradedPieceComplex ind hM p).X n) := by
  rw [ModuleCat.isZero_iff_subsingleton]
  refine ⟨fun f g ↦ (rowFiniteIndexGradedPieceComplexXEquiv hM p n).injective ?_⟩
  ext x
  have hf := (mem_rowFiniteTotalGrading_iff ℳ _).mp
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n f).2 x
  have hg := (mem_rowFiniteTotalGrading_iff ℳ _).mp
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n g).2 x
  rw [x.2, hℳ _ hpn, Submodule.mem_bot] at hf hg
  rw [hf, hg]

end GradedPiece

namespace RowFiniteTwistingCocycle

variable (m : RowFiniteTwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hA ℳ dM)

/-! ### The differential and the index filtration -/

variable {m} (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)
include hm

/-- On a single generator `x`, the twisting part of the coefficient differential is carried by
generators of index less than `ind x`. -/
theorem coefficientDifferential_single_sub_mem (x : P) (α : M) :
    m.coefficientDifferential hM (Finsupp.single x α) - Finsupp.single x (dM α) ∈
      rowFiniteIndexFiltration (R := R) ind (ind x - 1) := by
  classical
  induction α using DirectSum.Decomposition.inductionOn ℳ with
  | zero => simp
  | @homogeneous q α =>
    rw [m.coefficientDifferential_single hM x α.2, add_sub_cancel_left]
    refine Submodule.smul_of_tower_mem _ _ (Submodule.finsuppSum_mem _ _ _ _ fun y hy ↦ ?_)
    have hyx : ind y < ind x := lt_of_not_ge fun h ↦ hy (hm x y h)
    rw [mem_rowFiniteIndexFiltration_iff]
    intro z hz
    exact Finsupp.single_eq_of_ne (by rintro rfl; omega)
  | add α β hα hβ =>
    rw [Finsupp.single_add, map_add, map_add, Finsupp.single_add, add_sub_add_comm]
    exact add_mem hα hβ

/-- On a vector carried by generators of index at most `p`, the twisting part of the coefficient
differential is carried by generators of index at most `p - 1`. -/
theorem coefficientDifferential_sub_mem_rowFiniteIndexFiltration {p : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind p) :
    m.coefficientDifferential hM f - Finsupp.mapRange.linearMap dM f ∈
      rowFiniteIndexFiltration (R := R) ind (p - 1) := by
  have h₁ : m.coefficientDifferential hM f =
      f.sum fun x α ↦ m.coefficientDifferential hM (Finsupp.single x α) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    rw [map_finsuppSum]
  have h₂ : Finsupp.mapRange.linearMap dM f = f.sum fun x α ↦ Finsupp.single x (dM α) := by
    conv_lhs => rw [← Finsupp.sum_single f]
    rw [map_finsuppSum]
    simp
  have hsum : m.coefficientDifferential hM f - Finsupp.mapRange.linearMap dM f =
      f.sum fun x α ↦ m.coefficientDifferential hM (Finsupp.single x α) -
        Finsupp.single x (dM α) := by
    rw [h₁, h₂, Finsupp.sum_sub]
  rw [hsum]
  refine Submodule.finsuppSum_mem _ _ _ _ fun x hx ↦ ?_
  have hxp : ind x ≤ p := le_of_not_gt fun h ↦
    hx ((mem_rowFiniteIndexFiltration_iff ind).mp hf x h)
  exact rowFiniteIndexFiltration_mono ind (by omega)
    (m.coefficientDifferential_single_sub_mem hM hm x (f x))

/-- The coefficient differential preserves every stage of the index filtration. -/
theorem coefficientDifferential_mem_rowFiniteIndexFiltration {p : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind p) :
    m.coefficientDifferential hM f ∈ rowFiniteIndexFiltration (R := R) ind p := by
  have hd : Finsupp.mapRange.linearMap dM f ∈ rowFiniteIndexFiltration (R := R) ind p := by
    rw [mem_rowFiniteIndexFiltration_iff] at hf ⊢
    intro x hx
    simp [hf x hx]
  simpa using add_mem (rowFiniteIndexFiltration_mono ind (by omega : p - 1 ≤ p)
    (m.coefficientDifferential_sub_mem_rowFiniteIndexFiltration hM hm hf)) hd

/-- On the generators of maximal index `p` of a filtration stage, the coefficient differential is
the coefficient differential of the module. -/
theorem coefficientDifferential_apply_of_eq {p : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) ind p) {x : P} (hx : ind x = p) :
    m.coefficientDifferential hM f x = dM (f x) := by
  have h := (mem_rowFiniteIndexFiltration_iff ind).mp
    (m.coefficientDifferential_sub_mem_rowFiniteIndexFiltration hM hm hf) x (by omega)
  simpa [sub_eq_zero] using h

/-- The coefficient differential carries the degree-`n` part of `F_p` into degree `n + 1`. -/
theorem coefficientDifferential_mem_rowFiniteIndexGrading {p n : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexGrading ℳ ind p n) :
    m.coefficientDifferential hM f ∈ rowFiniteIndexGrading ℳ ind p (n + 1) :=
  mem_rowFiniteIndexGrading_iff.mpr ⟨(mem_rowFiniteIndexFiltration_iff ind).mp
      (m.coefficientDifferential_mem_rowFiniteIndexFiltration hM hm
        (rowFiniteIndexGrading_le_rowFiniteIndexFiltration p n hf)),
    (mem_rowFiniteTotalGrading_iff ℳ ind).mp ((m.isHomogeneous_coefficientDifferential hM).map_mem
      (rowFiniteIndexGrading_le_rowFiniteTotalGrading p n hf))⟩

/-! ### The filtration stages as subcomplexes -/

variable (m) in
/-- The `p`th stage `F_p` of the index filtration of the row-finite coefficient complex, as a
cochain complex of modules. -/
noncomputable def indexCochainComplex (p : ℤ) : CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  gradedCochainComplex (rowFiniteIndexGrading ℳ ind p) (m.coefficientDifferential hM)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦
      m.coefficientDifferential_mem_rowFiniteIndexGrading hM hm hf)
    fun _ f ↦ m.coefficientDifferential_sq_zero hM f

variable (m)

/-- Identify a term of `F_p` with the vectors of total degree `n` carried by generators of index
at most `p`. -/
noncomputable def indexCochainComplexXEquiv (p n : ℤ) :
    (m.indexCochainComplex hM hm p).X n ≃ₗ[R] rowFiniteIndexGrading ℳ ind p n :=
  gradedCochainComplexXEquiv n

/-- The differential of `F_p` is the coefficient differential. -/
theorem indexCochainComplexXEquiv_d (p n : ℤ) (f : (m.indexCochainComplex hM hm p).X n) :
    (m.indexCochainComplexXEquiv hM hm p (n + 1)
        (((m.indexCochainComplex hM hm p).d n (n + 1)).hom f) : P →₀ M) =
      m.coefficientDifferential hM (m.indexCochainComplexXEquiv hM hm p n f) :=
  gradedCochainComplexXEquiv_d n f

/-- The inclusion `F_p ⟶ F_q` of filtration stages, for `p ≤ q`. -/
noncomputable def indexCochainComplexMap {p q : ℤ} (hpq : p ≤ q) :
    m.indexCochainComplex hM hm p ⟶ m.indexCochainComplex hM hm q :=
  gradedCochainComplexInclusion fun _ ↦ rowFiniteIndexGrading_mono hpq

@[simp]
theorem indexCochainComplexMap_apply {p q : ℤ} (hpq : p ≤ q) (n : ℤ)
    (f : (m.indexCochainComplex hM hm p).X n) :
    (m.indexCochainComplexXEquiv hM hm q n
      (((m.indexCochainComplexMap hM hm hpq).f n).hom f) : P →₀ M) =
      m.indexCochainComplexXEquiv hM hm p n f :=
  gradedCochainComplexInclusion_apply _ n f

/-- The transition map from a filtration stage to itself is the identity. -/
@[simp]
theorem indexCochainComplexMap_id (p : ℤ) :
    m.indexCochainComplexMap hM hm (le_refl p) = 𝟙 (m.indexCochainComplex hM hm p) :=
  gradedCochainComplexInclusion_refl

/-- The transition maps of the index filtration compose. -/
@[reassoc (attr := simp)]
theorem indexCochainComplexMap_comp {p q r : ℤ} (hpq : p ≤ q) (hqr : q ≤ r) :
    m.indexCochainComplexMap hM hm hpq ≫ m.indexCochainComplexMap hM hm hqr =
      m.indexCochainComplexMap hM hm (hpq.trans hqr) :=
  gradedCochainComplexInclusion_comp _ _

theorem injective_indexCochainComplexMap_f {p q : ℤ} (hpq : p ≤ q) (n : ℤ) :
    Function.Injective ((m.indexCochainComplexMap hM hm hpq).f n) :=
  injective_gradedCochainComplexInclusion_f _ n

/-- The inclusion of the filtration stage `F_p` into the coefficient complex. -/
noncomputable def indexCochainComplexι (p : ℤ) :
    m.indexCochainComplex hM hm p ⟶ m.coefficientCochainComplex hM :=
  gradedCochainComplexInclusion (rowFiniteIndexGrading_le_rowFiniteTotalGrading p)

@[simp]
theorem indexCochainComplexι_apply (p n : ℤ) (f : (m.indexCochainComplex hM hm p).X n) :
    (m.coefficientCochainComplexXEquiv hM n
      (((m.indexCochainComplexι hM hm p).f n).hom f) : P →₀ M) =
      m.indexCochainComplexXEquiv hM hm p n f :=
  gradedCochainComplexInclusion_apply _ n f

instance mono_indexCochainComplexι (p : ℤ) : Mono (m.indexCochainComplexι hM hm p) :=
  mono_gradedCochainComplexInclusion _

@[reassoc (attr := simp)]
theorem indexCochainComplexMap_ι {p q : ℤ} (hpq : p ≤ q) :
    m.indexCochainComplexMap hM hm hpq ≫ m.indexCochainComplexι hM hm q =
      m.indexCochainComplexι hM hm p :=
  gradedCochainComplexInclusion_comp _ _

/-- The index filtration as subobjects of the row-finite coefficient complex. -/
noncomputable def indexSubobject (p : ℤ) : Subobject (m.coefficientCochainComplex hM) :=
  Subobject.mk (m.indexCochainComplexι hM hm p)

/-- The filtration subobject is represented by the inclusion of the filtration stage. -/
theorem indexSubobject_eq_mk (p : ℤ) :
    m.indexSubobject hM hm p = Subobject.mk (m.indexCochainComplexι hM hm p) :=
  (rfl)

theorem indexSubobject_mono : Monotone (m.indexSubobject hM hm) := fun _ _ hpq ↦
  Subobject.mk_le_mk_of_comm (m.indexCochainComplexMap hM hm hpq)
    (m.indexCochainComplexMap_ι hM hm hpq)

/-- In degree `n`, the stage `F_p` consists of the vectors carried by generators of index at
most `p`. -/
theorem mem_range_indexSubobject_arrow_f_iff (p n : ℤ)
    (f : (m.coefficientCochainComplex hM).X n) :
    f ∈ LinearMap.range ((m.indexSubobject hM hm p).arrow.f n).hom ↔
      ∀ x, p < ind x → (m.coefficientCochainComplexXEquiv hM n f : P →₀ M) x = 0 := by
  rw [indexSubobject_eq_mk, range_subobjectMk_arrow_f_hom]
  exact (mem_range_gradedCochainComplexInclusion_f_iff _ n f).trans <|
    mem_rowFiniteIndexGrading_iff.trans <| and_iff_left <|
      (mem_rowFiniteTotalGrading_iff ℳ ind).mp (m.coefficientCochainComplexXEquiv hM n f).2

/-- **The index filtration is exhaustive**, with no finiteness hypothesis on the generators:
every vector lies in some stage. -/
theorem exists_mem_range_indexSubobject_arrow_f (n : ℤ)
    (f : (m.coefficientCochainComplex hM).X n) :
    ∃ q, f ∈ LinearMap.range ((m.indexSubobject hM hm q).arrow.f n).hom := by
  have hf : (m.coefficientCochainComplexXEquiv hM n f : P →₀ M) ∈
      ⨆ p, rowFiniteIndexFiltration (R := R) ind p := by
    rw [iSup_rowFiniteIndexFiltration_eq_top]
    exact Submodule.mem_top
  obtain ⟨q, hq⟩ :=
    (Submodule.mem_iSup_of_directed _ (rowFiniteIndexFiltration_mono ind).directed_le).mp hf
  exact ⟨q, (m.mem_range_indexSubobject_arrow_f_iff hM hm q n f).mpr
    ((mem_rowFiniteIndexFiltration_iff ind).mp hq)⟩

/-- Below every generator index the index filtration vanishes. -/
theorem indexSubobject_eq_bot {p : ℤ} (hp : ∀ x, p < ind x) :
    m.indexSubobject hM hm p = ⊥ := by
  refine Subobject.mk_eq_bot_iff_zero.mpr (HomologicalComplex.hom_ext _ _ fun n ↦ ?_)
  ext f : 2
  have hf := rowFiniteIndexGrading_le_rowFiniteIndexFiltration p n
    (m.indexCochainComplexXEquiv hM hm p n f).2
  rw [rowFiniteIndexFiltration_eq_bot ind hp, Submodule.mem_bot] at hf
  apply (m.coefficientCochainComplexXEquiv hM n).injective
  apply Subtype.ext
  simpa using hf

/-! ### The graded pieces of the index filtration -/

/-- The restriction `F_p ⟶ ⊕_{ind x = p} ℳ` from the `p`th stage of the index filtration to the
families of coefficients on the generators of index `p`. -/
noncomputable def indexCochainComplexProj (p : ℤ) :
    m.indexCochainComplex hM hm p ⟶ rowFiniteIndexGradedPieceComplex ind hM p where
  f n := ModuleCat.ofHom
    ((rowFiniteIndexGradedPieceComplexXEquiv hM p n).symm.toLinearMap ∘ₗ
      ((rowFiniteIndexProjection ind p ∘ₗ
          Submodule.inclusion (rowFiniteIndexGrading_le_rowFiniteIndexFiltration p n)).codRestrict
        _ fun f ↦ (mem_rowFiniteTotalGrading_iff ℳ _).mpr fun x ↦ by
          simpa only [LinearMap.comp_apply, rowFiniteIndexProjection_apply,
            Submodule.coe_inclusion] using (mem_rowFiniteIndexGrading_iff.mp f.2).2 x) ∘ₗ
        (m.indexCochainComplexXEquiv hM hm p n).toLinearMap)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦
      (rowFiniteIndexGradedPieceComplexXEquiv hM p (i + 1)).injective (Subtype.ext ?_))
    ext x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      rowFiniteIndexGradedPieceComplexXEquiv_d, indexCochainComplexXEquiv_d, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply, rowFiniteIndexProjection_apply,
      Submodule.coe_inclusion, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_apply]
    exact (m.coefficientDifferential_apply_of_eq hM hm
      (rowFiniteIndexGrading_le_rowFiniteIndexFiltration p i
        (m.indexCochainComplexXEquiv hM hm p i f).2) x.2).symm

@[simp]
theorem indexCochainComplexProj_f_apply (p n : ℤ) (f : (m.indexCochainComplex hM hm p).X n) :
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n
        (((m.indexCochainComplexProj hM hm p).f n).hom f) : {x // ind x = p} →₀ M) =
      rowFiniteIndexProjection ind p ⟨_, rowFiniteIndexGrading_le_rowFiniteIndexFiltration p n
        (m.indexCochainComplexXEquiv hM hm p n f).2⟩ := by
  simp only [indexCochainComplexProj, ModuleCat.hom_ofHom, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.codRestrict_apply,
    Submodule.inclusion_apply]

@[reassoc (attr := simp)]
theorem indexCochainComplexMap_comp_proj (p : ℤ) :
    m.indexCochainComplexMap hM hm (Int.le_add_one le_rfl) ≫
      m.indexCochainComplexProj hM hm (p + 1) = 0 := by
  ext n f : 3
  apply (rowFiniteIndexGradedPieceComplexXEquiv hM (p + 1) n).injective
  apply Subtype.ext
  ext x
  simpa using (mem_rowFiniteIndexGrading_iff.mp (m.indexCochainComplexXEquiv hM hm p n f).2).1 x
    (x.2.symm ▸ lt_add_one p)

/-- The short complex `F_p ⟶ F_{p+1} ⟶ ⊕_{ind x = p + 1} ℳ` of the index filtration, whose second
map restricts to the generators of index `p + 1`. -/
@[expose, simps]
noncomputable def indexShortComplex (p : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{max uP uM} R) ℤ) :=
  ShortComplex.mk (m.indexCochainComplexMap hM hm (Int.le_add_one le_rfl))
    (m.indexCochainComplexProj hM hm (p + 1)) (m.indexCochainComplexMap_comp_proj hM hm p)

/-- The restriction to the generators of index `p` is surjective in each degree: a family on
those generators extends by zero. -/
theorem surjective_indexCochainComplexProj_f (p n : ℤ) :
    Function.Surjective ((m.indexCochainComplexProj hM hm p).f n) := by
  intro g
  set g' := (rowFiniteIndexGradedPieceComplexXEquiv hM p n g : {x // ind x = p} →₀ M)
  have hg := (mem_rowFiniteTotalGrading_iff ℳ _).mp
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n g).2
  have hf : g'.extendDomain ∈ rowFiniteIndexGrading ℳ ind p n := by
    refine mem_rowFiniteIndexGrading_iff.mpr ⟨fun x hx ↦ ?_, fun x ↦ ?_⟩
    · simp [Finsupp.extendDomain_apply, hx.ne']
    · by_cases hx : ind x = p
      · simpa [Finsupp.extendDomain_apply, hx] using hg ⟨x, hx⟩
      · simp [Finsupp.extendDomain_apply, hx]
  refine ⟨(m.indexCochainComplexXEquiv hM hm p n).symm ⟨_, hf⟩,
    (rowFiniteIndexGradedPieceComplexXEquiv hM p n).injective (Subtype.ext ?_)⟩
  ext x
  simp [g', Finsupp.extendDomain_apply, x.2]

/-- A vector of `F_{p+1}` vanishing on the generators of index `p + 1` comes from `F_p`. -/
theorem exists_indexCochainComplexMap_f_eq (p n : ℤ)
    (g : (m.indexCochainComplex hM hm (p + 1)).X n)
    (hg : ((m.indexCochainComplexProj hM hm (p + 1)).f n) g = 0) :
    ∃ f, ((m.indexCochainComplexMap hM hm (Int.le_add_one le_rfl)).f n) f = g := by
  have h0 := congrArg (fun z ↦ (rowFiniteIndexGradedPieceComplexXEquiv hM (p + 1) n z :
    {x // ind x = p + 1} →₀ M)) hg
  simp only [indexCochainComplexProj_f_apply, map_zero, ZeroMemClass.coe_zero] at h0
  have hker := LinearMap.mem_ker.mpr h0
  rw [ker_rowFiniteIndexProjection, add_sub_cancel_right] at hker
  exact LinearMap.mem_range.mp <| (mem_range_gradedCochainComplexInclusion_f_iff _ n g).mpr
    (mem_rowFiniteIndexGrading_iff.mpr ⟨(mem_rowFiniteIndexFiltration_iff ind).mp hker,
      (mem_rowFiniteIndexGrading_iff.mp (m.indexCochainComplexXEquiv hM hm (p + 1) n g).2).2⟩)

/-- **The graded pieces of the index filtration.** The sequence
`F_p ⟶ F_{p+1} ⟶ ⊕_{ind x = p + 1} ℳ` is short exact: the quotient `F_{p+1} / F_p` is the complex
of families of coefficients on the generators of index `p + 1`. -/
theorem indexShortComplex_shortExact (p : ℤ) : (m.indexShortComplex hM hm p).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    ShortComplex.ShortExact.mk'
      ((ShortComplex.moduleCat_exact_iff _).mpr (m.exists_indexCochainComplexMap_f_eq hM hm p n))
      ((ModuleCat.mono_iff_injective _).mpr
        (m.injective_indexCochainComplexMap_f hM hm (Int.le_add_one le_rfl) n))
      ((ModuleCat.epi_iff_surjective _).mpr
        (m.surjective_indexCochainComplexProj_f hM hm (p + 1) n))

/-- Restriction to the generators of index `p + 1` is a cokernel of the inclusion
`F_p ⟶ F_{p+1}`. -/
noncomputable def indexCochainComplexProjIsCokernel (p : ℤ) :
    IsColimit (CokernelCofork.ofπ (m.indexCochainComplexProj hM hm (p + 1))
      (m.indexCochainComplexMap_comp_proj hM hm p)) :=
  (m.indexShortComplex_shortExact hM hm p).gIsCokernel

/-! ### The index spectral sequence -/

/-- The index filtration of the row-finite coefficient complex, extended to `EInt` by zero and
the whole complex. -/
noncomputable abbrev indexFiltrationFunctor : EInt ⥤ CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  CochainComplex.filtrationFunctor (m.indexSubobject hM hm) (m.indexSubobject_mono hM hm)

/-- The **index spectral sequence** of a row-finite twisted complex: the spectral sequence of its
index filtration. On its first page, numbered `2`, the object at `(p, q)` is the cohomology in
degree `p + q` of the graded piece of index `q + 1`
(`RowFiniteTwistingCocycle.indexSpectralSequenceFirstPageXIso`). -/
noncomputable abbrev indexSpectralSequence :=
  CochainComplex.spectralSequence (m.indexFiltrationFunctor hM hm)

/-- The step `p` of `indexFiltrationFunctor` is the subcomplex `F_p`. -/
noncomputable def indexFiltrationFunctorObjIso (p : ℤ) :
    (m.indexFiltrationFunctor hM hm).obj p ≅ m.indexCochainComplex hM hm p :=
  CochainComplex.filtrationFunctorObjIsoOfEqMk _ _ (m.indexCochainComplexι hM hm)
    (m.indexSubobject_eq_mk hM hm) p

/-- The identification of a step of `indexFiltrationFunctor` with `F_p` is compatible with the
inclusions into the coefficient complex. -/
@[reassoc (attr := simp)]
theorem indexFiltrationFunctorObjIso_hom_comp_ι (p : ℤ) :
    (m.indexFiltrationFunctorObjIso hM hm p).hom ≫ m.indexCochainComplexι hM hm p =
      (CochainComplex.filtrationFunctorObjIso _ _ p).hom ≫
        (CochainComplex.filtrationEInt (m.indexSubobject hM hm) p).arrow :=
  CochainComplex.filtrationFunctorObjIsoOfEqMk_hom_comp _ _ (m.indexCochainComplexι hM hm)
    (m.indexSubobject_eq_mk hM hm) p

/-- The transition map `F_p ⟶ F_{p+1}` of `indexFiltrationFunctor` is the inclusion of
subcomplexes `indexCochainComplexMap`. -/
@[reassoc]
theorem indexFiltrationFunctor_map_objIso_hom (p : ℤ) :
    (m.indexFiltrationFunctor hM hm).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : p = p) rfl)) ≫
      (m.indexFiltrationFunctorObjIso hM hm (p + 1)).hom =
    (m.indexFiltrationFunctorObjIso hM hm p).hom ≫
      m.indexCochainComplexMap hM hm (Int.le_add_one le_rfl) :=
  CochainComplex.filtrationFunctor_map_comp_objIsoOfEqMk_hom _ _ (m.indexCochainComplexι hM hm)
    (m.indexSubobject_eq_mk hM hm) p _ (m.indexCochainComplexMap_ι hM hm (Int.le_add_one le_rfl))

/-- The graded piece `F_{p+1} / F_p` of the index filtration, the cokernel of the transition map
of `indexFiltrationFunctor`, is the complex of families of coefficients on the generators of
index `p + 1`. -/
noncomputable def indexCokernelIso (p : ℤ) :
    cokernel ((m.indexFiltrationFunctor hM hm).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : p = p) rfl))) ≅
      rowFiniteIndexGradedPieceComplex ind hM (p + 1) :=
  CochainComplex.cokernelFiltrationFunctorMapIsoOfIsColimit _ _ (m.indexCochainComplexι hM hm)
    (m.indexSubobject_eq_mk hM hm) p _ (m.indexCochainComplexMap_ι hM hm (Int.le_add_one le_rfl))
    _ _ (m.indexCochainComplexProjIsCokernel hM hm p)

/-- The graded-piece isomorphism identifies the cokernel projection with restriction to the
generators of index `p + 1`. -/
@[reassoc (attr := simp)]
theorem cokernel_π_comp_indexCokernelIso_hom (p : ℤ) :
    cokernel.π ((m.indexFiltrationFunctor hM hm).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : p = p) rfl))) ≫
      (m.indexCokernelIso hM hm p).hom =
    (m.indexFiltrationFunctorObjIso hM hm (p + 1)).hom ≫
      m.indexCochainComplexProj hM hm (p + 1) :=
  CochainComplex.π_cokernelFiltrationFunctorMapIsoOfIsColimit_hom _ _ (m.indexCochainComplexι hM hm)
    (m.indexSubobject_eq_mk hM hm) p _ (m.indexCochainComplexMap_ι hM hm (Int.le_add_one le_rfl))
    _ _ (m.indexCochainComplexProjIsCokernel hM hm p)

/-- **The first page of the index spectral sequence.** Its object at `(p, q)`, on page `2` in
Mathlib's numbering, is the cohomology in degree `p + q` of the complex of families of
coefficients on the generators of index `q + 1`. -/
noncomputable def indexSpectralSequenceFirstPageXIso (pq : ℤ × ℤ) :
    ((m.indexSpectralSequence hM hm).page 2).X pq ≅
      (rowFiniteIndexGradedPieceComplex ind hM (pq.2 + 1)).homology (pq.1 + pq.2) :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
    (HomologicalComplex.homologyFunctor _ _ _).mapIso (m.indexCokernelIso hM hm pq.2)

/-- The first-page isomorphism is the generic identification with the cokernel, followed by the
isomorphism on cohomology induced by `indexCokernelIso`. -/
theorem indexSpectralSequenceFirstPageXIso_eq (pq : ℤ × ℤ) :
    m.indexSpectralSequenceFirstPageXIso hM hm pq =
      CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
        (HomologicalComplex.homologyFunctor _ _ _).mapIso (m.indexCokernelIso hM hm pq.2) := by
  apply Iso.ext
  rfl

/-! ### Convergence -/

/-- **The filtration of the cohomology of a row-finite twisted complex is exhaustive**: every
class lies in the image of the cohomology of some stage of the index filtration. -/
theorem exists_mem_range_indexAbutmentFiltrationι {n : ℤ}
    (x : (CochainComplex.spectralObject (m.indexFiltrationFunctor hM hm)).abutment n) :
    ∃ q, x ∈ LinearMap.range
      ((CochainComplex.spectralObject (m.indexFiltrationFunctor hM hm)).abutmentFiltrationι
        q n).hom :=
  CochainComplex.exists_mem_range_filtrationAbutmentFiltrationι _ _
    (m.exists_mem_range_indexSubobject_arrow_f hM hm n) x

/-- Below every generator index, the filtration of the cohomology of the twisted complex
vanishes. -/
theorem isZero_indexAbutmentFiltration {a : ℤ} (ha : ∀ x, a < ind x) (n : ℤ) :
    IsZero ((CochainComplex.spectralObject (m.indexFiltrationFunctor hM hm)).abutmentFiltration
      a n) :=
  CochainComplex.isZero_filtrationAbutmentFiltration _ _ (m.indexSubobject_eq_bot hM hm ha) n

/-- For cohomologically nonpositive coefficients, the graded piece `F_{i+1} / F_i` of the index
filtration vanishes in each degree `k` with `0 < k + i + 1`. -/
theorem isZero_cokernel_indexSubobject_X (hℳ : ∀ k, 0 < k → ℳ k = ⊥) {i k : ℤ}
    (hik : 0 < k + (i + 1)) :
    IsZero ((cokernel (Subobject.ofLE (m.indexSubobject hM hm i) (m.indexSubobject hM hm (i + 1))
      (m.indexSubobject_mono hM hm (Int.le_add_one le_rfl)))).X k) := by
  -- The generic cokernel comparison is stated for the extension of the filtration to `EInt`,
  -- whose values at integers agree with the filtration only up to the equation
  -- `CochainComplex.filtrationEInt_coe`.
  have key : ∀ (S T : Subobject (m.coefficientCochainComplex hM))
      (_ : S = m.indexSubobject hM hm i) (_ : T = m.indexSubobject hM hm (i + 1)) (h : S ≤ T),
      IsZero ((cokernel (Subobject.ofLE S T h)).X k) →
        IsZero ((cokernel (Subobject.ofLE (m.indexSubobject hM hm i)
          (m.indexSubobject hM hm (i + 1))
          (m.indexSubobject_mono hM hm (Int.le_add_one le_rfl)))).X k) := by
    rintro S T rfl rfl h hST
    exact hST
  refine key _ _ (CochainComplex.filtrationEInt_coe _ i)
    (CochainComplex.filtrationEInt_coe _ (i + 1))
    (CochainComplex.monotone_filtrationEInt _ (m.indexSubobject_mono hM hm)
      (leOfHom (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : i = i) rfl)))) ?_
  refine IsZero.of_iso (isZero_rowFiniteIndexGradedPieceComplex_X hM hℳ hik)
    ((HomologicalComplex.eval _ _ k).mapIso
      ((CochainComplex.cokernelFiltrationFunctorMapIso (m.indexSubobject hM hm)
        (m.indexSubobject_mono hM hm)
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : i = i) rfl))).symm ≪≫
      m.indexCokernelIso hM hm i))

/-- **Strong convergence of the index spectral sequence.** Suppose that the coefficients are
cohomologically nonpositive and that every generator has index greater than `a`. Then, on every
page `r ≥ 2` with `q - r + 2 ≤ a` and `2 ≤ p + 2q + r`, the object at `(p, q)` is the graded piece
`F_{q+1} H^{p+q} / F_q H^{p+q}` of the filtration of the cohomology of the twisted complex. -/
noncomputable def indexSpectralSequencePageXIsoGraded (hℳ : ∀ k, 0 < k → ℳ k = ⊥) {a : ℤ}
    (ha : ∀ x, a < ind x) (r : ℤ) (hr : 2 ≤ r) (pq : ℤ × ℤ) (hra : pq.2 - r + 2 ≤ a)
    (hrb : 2 ≤ pq.1 + 2 * pq.2 + r) :
    ((m.indexSpectralSequence hM hm).page r).X pq ≅
      cokernel ((CochainComplex.spectralObject
        (m.indexFiltrationFunctor hM hm)).abutmentFiltrationMap pq.2 (pq.1 + pq.2)) :=
  CochainComplex.filtrationSpectralSequencePageXIsoGradedOfExhaustive (m.indexSubobject hM hm)
    (m.indexSubobject_mono hM hm) r hr pq (m.exists_mem_range_indexSubobject_arrow_f hM hm _)
    (Subobject.isZero_homology_of_eq_bot _ (le_bot_iff.mp ((m.indexSubobject_mono hM hm hra).trans
      (m.indexSubobject_eq_bot hM hm ha).le)) _)
    fun i hi ↦ ShortComplex.isZero_homology_of_isZero_X₂ _
      (m.isZero_cokernel_indexSubobject_X hM hm hℳ (i := i) (k := pq.1 + pq.2 - 1) (by omega))

end RowFiniteTwistingCocycle

end TauCeti
