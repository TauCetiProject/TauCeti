/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Filtration
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject
public import Mathlib.Algebra.Category.ModuleCat.Abelian

import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The graded pieces and first page of the twisted index filtration

The canonical index filtration of the twisted cochain complex has graded pieces given by the
zero twisting cocycle on generators of a fixed index. Restriction to those generators exhibits
a short exact sequence of cochain complexes. Its cokernel identifies the first page of the
filtered spectral sequence with the cohomology of that zero-cocycle complex.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definition 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 4.
-/

public section

open CategoryTheory Limits MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P : Type uP} [Fintype P] {ind : P → ℤ}
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ]

namespace TwistingCocycle

variable (m : TwistingCocycle 𝒜 d P ind) (dM : M →ₗ[R] M) (hM : IsDGRightModule h ℳ dM)

/-- The canonical index filtration, extended to `EInt` by zero and the whole complex. -/
noncomputable abbrev twistedIndexFiltrationFunctor :
    EInt ⥤ CochainComplex (ModuleCat.{max uP uM} R) ℤ :=
  CochainComplex.filtrationFunctor (m.twistedIndexSubobject hM) (m.twistedIndexSubobject_mono hM)

/-! ### The graded pieces of the index filtration -/

/-- The restriction `F_p ⟶ ℳ ⊗ ⟨P_p⟩` from the `p`th step of the index filtration to the twisted
complex of the zero cocycle on the generators `P_p` of index `p`. -/
noncomputable def twistedIndexCochainComplexProj (p : ℤ) :
    m.twistedIndexCochainComplex hM p ⟶
      (0 : TwistingCocycle 𝒜 d {x // ind x = p} fun x ↦ ind x).twistedCochainComplex dM hM where
  f n := ModuleCat.ofHom
    ((twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM
        n).symm.toLinearMap ∘ₗ
      ((LinearMap.funLeft R M Subtype.val).restrict fun f hf ↦ by
        rw [mem_twistedTotalGrading_iff]
        exact fun x ↦ (mem_twistedTotalGrading_iff.mp
          (twistedIndexGrading_le_twistedTotalGrading p n hf)) x) ∘ₗ
        (m.twistedIndexCochainComplexXEquiv hM p n).toLinearMap)
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine ModuleCat.hom_ext (LinearMap.ext fun f ↦
      (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM
        (i + 1)).injective (Subtype.ext ?_))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      twistedCochainComplexXEquiv_d, twistedIndexCochainComplexXEquiv_d, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, LinearMap.restrict_apply]
    exact twistedDifferential_funLeft_val m.m m.one_sided dM
      (mem_twistedIndexGrading_iff.mp (m.twistedIndexCochainComplexXEquiv hM p i f).2).1

@[simp]
theorem twistedIndexCochainComplexProj_f_apply (p n : ℤ)
    (f : (m.twistedIndexCochainComplex hM p).X n) :
    (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM n
        (((m.twistedIndexCochainComplexProj dM hM p).f n).hom f) : {x // ind x = p} → M) =
      LinearMap.funLeft R M Subtype.val (m.twistedIndexCochainComplexXEquiv hM p n f) := by
  simp [twistedIndexCochainComplexProj]

@[reassoc (attr := simp)]
theorem twistedIndexMap_comp_proj (p : ℤ) :
    m.twistedIndexCochainComplexMap hM (Int.le_add_one le_rfl) ≫
      m.twistedIndexCochainComplexProj dM hM (p + 1) = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ ModuleCat.hom_ext (LinearMap.ext fun f ↦
    (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0)
      hM n).injective (Subtype.ext ?_))
  funext x
  simpa using (mem_twistedIndexGrading_iff.mp
    (m.twistedIndexCochainComplexXEquiv hM p n f).2).1 x (x.2.symm ▸ lt_add_one p)

/-- The short complex `F_p ⟶ F_{p+1} ⟶ ℳ ⊗ ⟨P_{p+1}⟩` of the index filtration, whose second map
restricts to the generators of index `p + 1`. -/
noncomputable def twistedIndexShortComplex (p : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{max uP uM} R) ℤ) :=
  ShortComplex.mk (m.twistedIndexCochainComplexMap hM (Int.le_add_one le_rfl))
    (m.twistedIndexCochainComplexProj dM hM (p + 1))
    (m.twistedIndexMap_comp_proj dM hM p)

@[simp]
theorem twistedIndexShortComplex_X₁ (p : ℤ) :
    (m.twistedIndexShortComplex dM hM p).X₁ = m.twistedIndexCochainComplex hM p := by
  rw [twistedIndexShortComplex]

@[simp]
theorem twistedIndexShortComplex_X₂ (p : ℤ) :
    (m.twistedIndexShortComplex dM hM p).X₂ = m.twistedIndexCochainComplex hM (p + 1) := by
  rw [twistedIndexShortComplex]

@[simp]
theorem twistedIndexShortComplex_X₃ (p : ℤ) :
    (m.twistedIndexShortComplex dM hM p).X₃ =
      (0 : TwistingCocycle 𝒜 d {x // ind x = p + 1} fun x ↦ ind x).twistedCochainComplex dM hM := by
  rw [twistedIndexShortComplex]

/-- The first map in `twistedIndexShortComplex` is the inclusion `F_p ⟶ F_{p+1}`. -/
@[simp]
theorem twistedIndexShortComplex_f (p : ℤ) :
    HEq (m.twistedIndexShortComplex dM hM p).f
      (m.twistedIndexCochainComplexMap hM (p := p) (q := p + 1)
        (Int.le_add_one le_rfl)) := by
  unfold twistedIndexShortComplex
  rfl

/-- The second map in `twistedIndexShortComplex` is restriction to the generators of index
`p + 1`. -/
@[simp]
theorem twistedIndexShortComplex_g (p : ℤ) :
    HEq (m.twistedIndexShortComplex dM hM p).g
      (m.twistedIndexCochainComplexProj dM hM (p + 1)) := by
  unfold twistedIndexShortComplex
  rfl

/-- The restriction `F_p ⟶ ℳ ⊗ ⟨P_p⟩` is surjective in each degree: a function on the generators
of index `p` extends by zero to a function supported on the generators of index at most `p`. -/
theorem surjective_twistedIndexCochainComplexProj_f (p n : ℤ) :
    Function.Surjective ((m.twistedIndexCochainComplexProj dM hM p).f n) := by
  intro g
  have hg := mem_twistedTotalGrading_iff.mp (twistedCochainComplexXEquiv
    (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM n g).2
  have hf : (fun x ↦ if hx : ind x = p then
      (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM
        n g : {x // ind x = p} → M) ⟨x, hx⟩ else 0) ∈ twistedIndexGrading ℳ ind p n := by
    refine mem_twistedIndexGrading_iff.mpr
      ⟨fun x hx ↦ dite_eq_right_iff.mpr fun hx' ↦ absurd hx' hx.ne',
        fun x ↦ ?_⟩
    split_ifs with hx
    · exact hg ⟨x, hx⟩
    · exact zero_mem _
  refine ⟨(m.twistedIndexCochainComplexXEquiv hM p n).symm ⟨_, hf⟩,
    (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0) (TwistingCocycle.twisting 0) hM
      n).injective (Subtype.ext ?_)⟩
  funext y
  simp [y.2]

/-- An element of `F_{p+1}` whose restriction to the generators of index `p + 1` vanishes comes
from `F_p`. -/
theorem exists_twistedIndexCochainComplexMap_f_eq (p n : ℤ)
    (g : (m.twistedIndexCochainComplex hM (p + 1)).X n)
    (hg : ((m.twistedIndexCochainComplexProj dM hM (p + 1)).f n) g = 0) :
    ∃ f, ((m.twistedIndexCochainComplexMap hM (Int.le_add_one le_rfl)).f n) f = g := by
  have hg' := congrArg (fun x ↦ (twistedCochainComplexXEquiv (TwistingCocycle.mem_graded 0)
    (TwistingCocycle.twisting 0) hM n x : {x // ind x = p + 1} → M)) hg
  simp only [twistedIndexCochainComplexProj_f_apply, map_zero, ZeroMemClass.coe_zero] at hg'
  have hmem :=
    mem_twistedIndexGrading_iff.mp (m.twistedIndexCochainComplexXEquiv hM (p + 1) n g).2
  have hp : (m.twistedIndexCochainComplexXEquiv hM (p + 1) n g : P → M) ∈
      twistedIndexGrading ℳ ind p n := by
    refine mem_twistedIndexGrading_iff.mpr ⟨fun x hx ↦ ?_, hmem.2⟩
    rcases (Int.add_one_le_iff.mpr hx).eq_or_lt with hx' | hx'
    · simpa using congrFun hg' ⟨x, hx'.symm⟩
    · exact hmem.1 x hx'
  refine ⟨(m.twistedIndexCochainComplexXEquiv hM p n).symm ⟨_, hp⟩,
    (m.twistedIndexCochainComplexXEquiv hM (p + 1) n).injective (Subtype.ext ?_)⟩
  simp

/-- **The graded pieces of the index filtration.** The sequence
`F_p ⟶ F_{p+1} ⟶ ℳ ⊗ ⟨P_{p+1}⟩` is short exact: the quotient `F_{p+1} / F_p` is the twisted complex
of the zero cocycle on the generators of index `p + 1`. -/
theorem twistedIndexShortComplex_shortExact (p : ℤ) :
    (m.twistedIndexShortComplex dM hM p).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun n ↦
    ShortComplex.ShortExact.mk'
      ((ShortComplex.moduleCat_exact_iff _).mpr
        (m.exists_twistedIndexCochainComplexMap_f_eq dM hM p n))
      ((ModuleCat.mono_iff_injective _).mpr
        (m.injective_twistedIndexCochainComplexMap_f hM (Int.le_add_one le_rfl) n))
      ((ModuleCat.epi_iff_surjective _).mpr
        (m.surjective_twistedIndexCochainComplexProj_f dM hM (p + 1) n))

/-- Restriction to the generators of index `p + 1` is a cokernel of the inclusion
`F_p ⟶ F_{p+1}`. -/
noncomputable def twistedIndexCochainComplexProjIsCokernel (p : ℤ) :
    IsColimit (CokernelCofork.ofπ (m.twistedIndexCochainComplexProj dM hM (p + 1))
      (m.twistedIndexMap_comp_proj dM hM p)) :=
  (m.twistedIndexShortComplex_shortExact dM hM p).gIsCokernel

/-! ### The first page of the index spectral sequence -/

/-- The step `p` of `twistedIndexFiltrationFunctor` is the subcomplex `F_p`. -/
noncomputable def twistedIndexFiltrationFunctorObjIso (p : ℤ) :
    (m.twistedIndexFiltrationFunctor dM hM).obj p ≅ m.twistedIndexCochainComplex hM p :=
  CochainComplex.filtrationFunctorObjIso _ _ p ≪≫
    eqToIso (congrArg (fun S : Subobject (m.twistedCochainComplex dM hM) ↦
      (S : CochainComplex (ModuleCat.{max uP uM} R) ℤ))
      ((CochainComplex.filtrationEInt_coe _ p).trans (m.twistedIndexSubobject_eq_mk hM p))) ≪≫
    Subobject.underlyingIso (m.twistedIndexCochainComplexι hM p)

/-- The identification of a step of `twistedIndexFiltrationFunctor` with `F_p` is compatible with
the inclusions into the twisted complex. -/
@[reassoc (attr := simp)]
theorem twistedIndexFiltrationFunctorObjIso_hom_comp_indexFiltrationι (p : ℤ) :
    (m.twistedIndexFiltrationFunctorObjIso dM hM p).hom ≫ m.twistedIndexCochainComplexι hM p =
      (CochainComplex.filtrationFunctorObjIso _ _ p).hom ≫
        (CochainComplex.filtrationEInt (m.twistedIndexSubobject hM) p).arrow := by
  simp only [twistedIndexFiltrationFunctorObjIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
    Subobject.underlyingIso_hom_comp_eq_mk]
  exact congrArg _ (Subobject.arrow_congr _ _
    ((CochainComplex.filtrationEInt_coe _ p).trans (m.twistedIndexSubobject_eq_mk hM p)))

/-- The transition map `F_p ⟶ F_{p+1}` of `twistedIndexFiltrationFunctor` is the inclusion of
subcomplexes `twistedIndexCochainComplexMap`. -/
@[reassoc]
theorem twistedIndexFiltrationFunctor_map_objIso_hom (p : ℤ) :
    (m.twistedIndexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : p = p) rfl)) ≫
      (m.twistedIndexFiltrationFunctorObjIso dM hM (p + 1)).hom =
    (m.twistedIndexFiltrationFunctorObjIso dM hM p).hom ≫
      m.twistedIndexCochainComplexMap hM (Int.le_add_one le_rfl) := by
  rw [← cancel_mono (m.twistedIndexCochainComplexι hM (p + 1))]
  simp only [Category.assoc, twistedIndexFiltrationFunctorObjIso_hom_comp_indexFiltrationι,
    twistedIndexCochainComplexMap_ι]
  rw [← Category.assoc, CochainComplex.filtrationFunctor_map_comp_objIso_hom]
  simp

/-- The graded piece `F_{p+1} / F_p` of the index filtration, the cokernel of the transition map of
`twistedIndexFiltrationFunctor`, is the twisted complex of the zero cocycle on generators of
index `p + 1`. -/
noncomputable def twistedIndexCokernelIso (p : ℤ) :
    cokernel ((m.twistedIndexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : p = p) rfl))) ≅
      (0 : TwistingCocycle 𝒜 d {x // ind x = p + 1} fun x ↦ ind x).twistedCochainComplex dM hM :=
  cokernel.mapIso _ (m.twistedIndexCochainComplexMap hM (Int.le_add_one le_rfl))
      (m.twistedIndexFiltrationFunctorObjIso dM hM p)
      (m.twistedIndexFiltrationFunctorObjIso dM hM (p + 1))
      (m.twistedIndexFiltrationFunctor_map_objIso_hom dM hM p) ≪≫
    (colimit.isColimit _).coconePointUniqueUpToIso
      (m.twistedIndexCochainComplexProjIsCokernel dM hM p)

/-- The graded-piece isomorphism identifies the cokernel projection with restriction to the
generators of index `p + 1`. -/
@[reassoc (attr := simp)]
theorem cokernel_π_comp_twistedIndexCokernelIso_hom (p : ℤ) :
    cokernel.π ((m.twistedIndexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : p = p) rfl))) ≫
      (m.twistedIndexCokernelIso dM hM p).hom =
    (m.twistedIndexFiltrationFunctorObjIso dM hM (p + 1)).hom ≫
      m.twistedIndexCochainComplexProj dM hM (p + 1) := by
  rw [twistedIndexCokernelIso, Iso.trans_hom, ← Category.assoc, cokernel.mapIso_hom,
    cokernel.π_desc, Category.assoc]
  congr 1
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (colimit.isColimit _)
    (m.twistedIndexCochainComplexProjIsCokernel dM hM p) WalkingParallelPair.one

/-- **The first page of the index spectral sequence.** Its object at `(p, q)`, on page `2` in
Mathlib's numbering, is the cohomology `H^{p+q}` of the twisted complex `ℳ ⊗ ⟨P_{q+1}⟩` of the zero
cocycle on the generators of index `q + 1`. -/
noncomputable def indexSpectralSequenceFirstPageXIso (pq : ℤ × ℤ) :
    ((CochainComplex.spectralSequence (m.twistedIndexFiltrationFunctor dM hM)).page 2).X pq ≅
      ((0 : TwistingCocycle 𝒜 d {x // ind x = pq.2 + 1} fun x ↦ ind x).twistedCochainComplex dM
        hM).homology (pq.1 + pq.2) :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
    (HomologicalComplex.homologyFunctor _ _ _).mapIso (m.twistedIndexCokernelIso dM hM pq.2)

/-- The first-page isomorphism is the generic identification with the cokernel, followed by the
isomorphism on cohomology induced by `twistedIndexCokernelIso`. -/
theorem indexSpectralSequenceFirstPageXIso_eq (pq : ℤ × ℤ) :
    m.indexSpectralSequenceFirstPageXIso dM hM pq =
      CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq pq.2 (pq.2 + 1) rfl rfl _ rfl ≪≫
        (HomologicalComplex.homologyFunctor _ _ _).mapIso
          (m.twistedIndexCokernelIso dM hM pq.2) := by
  apply Iso.ext
  rfl

end TwistingCocycle

end TauCeti
