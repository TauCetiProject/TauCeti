/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.CoefficientFiltration
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive

/-!
# The index spectral sequence of a row-finite twisted complex

The index filtration of the twisted complex `M ⊗ ⟨P⟩` of a one-sided row-finite twisting cocycle
(`TauCeti.RowFiniteTwistingCocycle.indexSubobject`) gives a spectral sequence. Its first page is
the cohomology of the graded pieces, which are the twisted complexes of the zero cocycle on the
generators of a fixed index.

The generator set may be infinite, with unbounded indices, so the filtration need not be finite.
It is exhaustive in every degree, hence so is the induced filtration of the abutment `H^n`. It
vanishes below a lower bound for the indices, hence so does the filtration of the abutment.
Exhaustiveness (`TauCeti.RowFiniteTwistingCocycle.exists_mem_range_indexSubobject_arrow_f`)
supplies the exhaustiveness hypotheses of the convergence results of
`TauCeti.Algebra.Homology.SpectralSequence.Filtered.Exhaustive`. Strong convergence and the
comparison theorem there also need vanishing hypotheses that arbitrary coefficients and
unbounded indices do not provide: the cohomology of the graded pieces `F_{i+1} / F_i` must vanish
in the relevant degrees for all large `i`, and that of the stages `F_i` for all small `i` (for
instance when the stages are zero below a lower bound for the indices).

## Main definitions

* `TauCeti.RowFiniteTwistingCocycle.indexSpectralSequence`: the spectral sequence of the index
  filtration.
* `TauCeti.RowFiniteTwistingCocycle.indexCokernelIso`: the graded piece `F_{p+1} / F_p` is the
  twisted complex of the zero cocycle on the generators of index `p + 1`.

## Main results

* `TauCeti.RowFiniteTwistingCocycle.indexSpectralSequenceFirstPageXIso`: the first page of the
  index spectral sequence.
* `TauCeti.RowFiniteTwistingCocycle.exists_mem_range_indexAbutmentFiltrationι`: the filtration
  of the abutment is exhaustive.
* `TauCeti.RowFiniteTwistingCocycle.isZero_indexAbutmentFiltration`: the filtration of the
  abutment vanishes below all generator indices.

## Implementation notes

This module adapts the finite construction of `TauCeti.Algebra.Homology.DG.Twisted.FirstPage`
to row-finite cocycles: `indexFiltrationFunctorObjIso`, `indexCokernelIso` and
`indexSpectralSequenceFirstPageXIso` follow `TwistingCocycle.twistedIndexFiltrationFunctorObjIso`,
`TwistingCocycle.twistedIndexCokernelIso` and `TwistingCocycle.indexSpectralSequenceFirstPageXIso`
there.

The pages are numbered as in Mathlib's `CochainComplex.spectralSequence`: the first page `E₁` is
`page 2`, and its object at `(p, q)` is the cohomology in total degree `p + q` of the graded
piece of index `q + 1`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 4.
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

/-- The index filtration, extended to `EInt` by zero and the whole twisted complex. -/
abbrev indexFiltrationFunctor : EInt ⥤ CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  CochainComplex.filtrationFunctor (m.indexSubobject hm hM) (m.indexSubobject_mono hm hM)

/-- The **index spectral sequence** of a row-finite twisted complex: the spectral sequence of its
index filtration. On its first page, numbered `2`, the object at `(p, q)` is the cohomology
`H^{p+q}(F_{q+1} / F_q)` of a graded piece of the index filtration
(`TauCeti.RowFiniteTwistingCocycle.indexSpectralSequenceFirstPageXIso`). -/
abbrev indexSpectralSequence :=
  CochainComplex.spectralSequence (m.indexFiltrationFunctor hm hM)

/-! ### The first page -/

/-- The step `p` of `indexFiltrationFunctor` is the subcomplex `F_p`. -/
def indexFiltrationFunctorObjIso (p : ℤ) :
    (m.indexFiltrationFunctor hm hM).obj p ≅ m.indexCochainComplex hm hM p :=
  CochainComplex.filtrationFunctorObjIso _ _ p ≪≫
    eqToIso (congrArg (fun S : Subobject (m.coefficientCochainComplex hM) ↦
      (S : CochainComplex (ModuleCat.{max uP uM} R) ℤ))
      ((CochainComplex.filtrationEInt_coe _ p).trans (m.indexSubobject_eq_mk hm hM p))) ≪≫
    Subobject.underlyingIso (m.indexCochainComplexι hm hM p)

/-- The identification of a step of `indexFiltrationFunctor` with `F_p` is compatible with the
inclusions into the twisted complex. -/
@[reassoc (attr := simp)]
theorem indexFiltrationFunctorObjIso_hom_comp_ι (p : ℤ) :
    (m.indexFiltrationFunctorObjIso hm hM p).hom ≫ m.indexCochainComplexι hm hM p =
      (CochainComplex.filtrationFunctorObjIso _ _ p).hom ≫
        (CochainComplex.filtrationEInt (m.indexSubobject hm hM) p).arrow := by
  simp only [indexFiltrationFunctorObjIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    Subobject.underlyingIso_hom_comp_eq_mk]
  exact congrArg _ (Subobject.arrow_congr _ _
    ((CochainComplex.filtrationEInt_coe _ p).trans (m.indexSubobject_eq_mk hm hM p)))

/-- The transition map `F_p ⟶ F_{p+1}` of `indexFiltrationFunctor` is the inclusion
`indexCochainComplexMap`. -/
@[reassoc]
theorem indexFiltrationFunctor_map_objIso_hom (p : ℤ) :
    (m.indexFiltrationFunctor hm hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : p = p) rfl)) ≫
      (m.indexFiltrationFunctorObjIso hm hM (p + 1)).hom =
    (m.indexFiltrationFunctorObjIso hm hM p).hom ≫
      m.indexCochainComplexMap hm hM (Int.le_add_one le_rfl) := by
  rw [← cancel_mono (m.indexCochainComplexι hm hM (p + 1))]
  simp only [Category.assoc, indexFiltrationFunctorObjIso_hom_comp_ι, indexCochainComplexMap_ι]
  rw [← Category.assoc, CochainComplex.filtrationFunctor_map_comp_objIso_hom]
  simp

/-- The graded piece `F_{p+1} / F_p` of the index filtration, the cokernel of the transition map
of `indexFiltrationFunctor`, is the twisted complex of the zero cocycle on the generators of
index `p + 1`. -/
def indexCokernelIso (p : ℤ) :
    cokernel ((m.indexFiltrationFunctor hm hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : p = p) rfl))) ≅
      RowFiniteTwistingCocycle.coefficientCochainComplex
        (0 : RowFiniteTwistingCocycle 𝒜 dA {x // ind x = p + 1} fun x ↦ ind x) hM :=
  cokernel.mapIso _ (m.indexCochainComplexMap hm hM (Int.le_add_one le_rfl))
      (m.indexFiltrationFunctorObjIso hm hM p) (m.indexFiltrationFunctorObjIso hm hM (p + 1))
      (m.indexFiltrationFunctor_map_objIso_hom hm hM p) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      (m.shortExact_indexCochainComplexMap_proj hm hM p).gIsCokernel

/-- The graded-piece isomorphism identifies the cokernel projection with restriction to the
generators of index `p + 1`. -/
@[reassoc (attr := simp)]
theorem cokernel_π_comp_indexCokernelIso_hom (p : ℤ) :
    cokernel.π ((m.indexFiltrationFunctor hm hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : p = p) rfl))) ≫
      (m.indexCokernelIso hm hM p).hom =
    (m.indexFiltrationFunctorObjIso hm hM (p + 1)).hom ≫
      m.indexCochainComplexProj hm hM (p + 1) := by
  rw [indexCokernelIso, Iso.trans_hom, ← Category.assoc, cokernel.mapIso_hom, cokernel.π_desc,
    Category.assoc]
  congr 1
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (m.shortExact_indexCochainComplexMap_proj hm hM p).gIsCokernel WalkingParallelPair.one

/-- **The first page of the index spectral sequence.** Its object at `(p, q)`, on page `2` in
Mathlib's numbering, is the cohomology `H^{p+q}` of the twisted complex of the zero cocycle on
the generators of index `q + 1`. -/
def indexSpectralSequenceFirstPageXIso (pq : ℤ × ℤ) :
    ((m.indexSpectralSequence hm hM).page 2).X pq ≅
      (RowFiniteTwistingCocycle.coefficientCochainComplex
        (0 : RowFiniteTwistingCocycle 𝒜 dA {x // ind x = pq.2 + 1} fun x ↦ ind x) hM).homology
          (pq.1 + pq.2) :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
    (HomologicalComplex.homologyFunctor _ _ _).mapIso (m.indexCokernelIso hm hM pq.2)

/-- The first-page isomorphism is the generic identification with the cokernel, followed by the
isomorphism on cohomology induced by `indexCokernelIso`. -/
theorem indexSpectralSequenceFirstPageXIso_eq (pq : ℤ × ℤ) :
    m.indexSpectralSequenceFirstPageXIso hm hM pq =
      CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
        (HomologicalComplex.homologyFunctor _ _ _).mapIso (m.indexCokernelIso hm hM pq.2) :=
  (rfl)

/-! ### The filtration of the abutment -/

/-- **The filtration of the abutment is exhaustive.** Every class of `H^n` of the twisted complex
lies in some step of the filtration induced by the index filtration, without a bound on the
generator indices. -/
theorem exists_mem_range_indexAbutmentFiltrationι (n : ℤ)
    (x : (CochainComplex.spectralObject (m.indexFiltrationFunctor hm hM)).abutment n) :
    ∃ q, x ∈ LinearMap.range
      ((CochainComplex.spectralObject (m.indexFiltrationFunctor hm hM)).abutmentFiltrationι
        q n).hom :=
  CochainComplex.exists_mem_range_filtrationAbutmentFiltrationι _ _
    (m.exists_mem_range_indexSubobject_arrow_f hm hM n) x

/-- Below all generator indices the filtration of the abutment vanishes. -/
theorem isZero_indexAbutmentFiltration {p : ℤ} (hp : ∀ x, p < ind x) (n : ℤ) :
    IsZero ((CochainComplex.spectralObject (m.indexFiltrationFunctor hm hM)).abutmentFiltration
      p n) :=
  CochainComplex.isZero_filtrationAbutmentFiltration _ _ (m.indexSubobject_eq_bot hm hM hp) n

end RowFiniteTwistingCocycle

end TauCeti
