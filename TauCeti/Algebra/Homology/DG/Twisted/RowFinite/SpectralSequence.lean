/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Filtration
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive

/-!
# The index spectral sequence of a row-finite twisted complex

Let `m` be a row-finite twisting cocycle on an arbitrary graded set of generators `P`, and let
`ℳ` be a DG right module. The **index filtration** `F_p` of the coefficient complex `P →₀ M`
consists of the finite-support vectors carried by generators of index at most `p`. When the
cocycle is one-sided (`m x y = 0` whenever `ind x ≤ ind y`, automatic over a cohomologically
nonpositive algebra by `TwistingCocycle.one_sided_of_nonpos`), the twisted differential preserves
it: the coefficient differential keeps the generator, and every twisting term strictly lowers its
index.

This file builds the spectral sequence of this filtration, whose stages and graded pieces are
constructed in `TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Filtration`, extending the finite
construction `TwistingCocycle.indexSpectralSequence` to arbitrary generator sets.

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

namespace RowFiniteTwistingCocycle

variable (m : RowFiniteTwistingCocycle 𝒜 dA P ind) (hM : IsDGRightModule hA ℳ dM)
  (hm : ∀ x y, ind x ≤ ind y → m.m x y = 0)
include hm

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
