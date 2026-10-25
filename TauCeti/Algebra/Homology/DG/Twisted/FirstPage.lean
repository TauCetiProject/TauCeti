/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Filtration
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.SpectralObject


/-!
# The first page of the twisted index filtration

The canonical index filtration of the twisted cochain complex has graded pieces given by the
zero twisting cocycle on generators of a fixed index. The projection and short exact sequence
are constructed in `Twisted.Filtration`. Their cokernel identifies the first page of the filtered
spectral sequence with the cohomology of that zero-cocycle complex.

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

/-- The graded piece `F_p / F_q`, for `q + 1 = p`, with the indices given by an equation: the
cokernel of the transition map `F_q ⟶ F_p` of the functor of the index filtration is the
graded piece of index `p`. -/
noncomputable def twistedIndexCokernelIsoOfEq (q p : ℤ) (hqp : q + 1 = p) :
    cokernel ((m.twistedIndexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) hqp.symm))) ≅
      (0 : TwistingCocycle 𝒜 d {x : P // ind x = p} fun x ↦ ind x).twistedCochainComplex dM hM := by
  subst hqp
  exact m.twistedIndexCokernelIso dM hM q

/-- With the standard indices, `twistedIndexCokernelIsoOfEq` is `twistedIndexCokernelIso`. -/
theorem twistedIndexCokernelIsoOfEq_self (q : ℤ) :
    m.twistedIndexCokernelIsoOfEq dM hM q (q + 1) rfl = m.twistedIndexCokernelIso dM hM q :=
  -- The equality `q + 1 = q + 1` is `rfl`, so the transport in the definition reduces.
  (rfl)

/-- The graded-piece isomorphism identifies the cokernel projection with restriction to the
generators of index `p`. -/
@[reassoc (attr := simp)]
theorem cokernel_π_comp_twistedIndexCokernelIsoOfEq_hom (q p : ℤ) (hqp : q + 1 = p) :
    cokernel.π ((m.twistedIndexFiltrationFunctor dM hM).map
        (homOfLE (CochainComplex.coe_le_coe_of_eq_add_one (rfl : q = q) hqp.symm))) ≫
      (m.twistedIndexCokernelIsoOfEq dM hM q p hqp).hom =
    (m.twistedIndexFiltrationFunctorObjIso dM hM p).hom ≫
      m.twistedIndexCochainComplexProj dM hM p := by
  subst hqp
  exact m.cokernel_π_comp_twistedIndexCokernelIso_hom dM hM q

/-- **The first page of the index spectral sequence**, with the indices `q`, `q + 1` and `p + q`
given by equations, as in `CochainComplex.spectralSequenceFirstPageXIsoCokernel`: the object at
`(p, q)` is the cohomology in degree `p + q` of the graded piece of index `q + 1`. -/
noncomputable def indexSpectralSequenceFirstPageXIsoOfEq (pq : ℤ × ℤ) (i₁ i₂ : ℤ)
    (hi₁ : i₁ = pq.2) (hi₂ : i₂ = pq.2 + 1) (n : ℤ) (hn : n = pq.1 + pq.2) :
    ((CochainComplex.spectralSequence (m.twistedIndexFiltrationFunctor dM hM)).page 2).X pq ≅
      ((0 : TwistingCocycle 𝒜 d {x : P // ind x = i₂} fun x ↦ ind x).twistedCochainComplex dM
        hM).homology n :=
  CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq i₁ i₂ hi₁ hi₂ n hn ≪≫
    HomologicalComplex.homologyMapIso (m.twistedIndexCokernelIsoOfEq dM hM i₁ i₂ (by omega)) n

/-- `indexSpectralSequenceFirstPageXIsoOfEq` is the generic identification with the cokernel,
followed by the isomorphism on cohomology induced by `twistedIndexCokernelIsoOfEq`. -/
theorem indexSpectralSequenceFirstPageXIsoOfEq_eq (pq : ℤ × ℤ) (i₁ i₂ : ℤ) (hi₁ : i₁ = pq.2)
    (hi₂ : i₂ = pq.2 + 1) (n : ℤ) (hn : n = pq.1 + pq.2) :
    m.indexSpectralSequenceFirstPageXIsoOfEq dM hM pq i₁ i₂ hi₁ hi₂ n hn =
      CochainComplex.spectralSequenceFirstPageXIsoCokernel _ pq i₁ i₂ hi₁ hi₂ n hn ≪≫
        HomologicalComplex.homologyMapIso
          (m.twistedIndexCokernelIsoOfEq dM hM i₁ i₂ (by omega)) n :=
  -- The first page isomorphism is defined as this composite.
  (rfl)

/-- With the standard indices, `indexSpectralSequenceFirstPageXIsoOfEq` is
`indexSpectralSequenceFirstPageXIso`. -/
theorem indexSpectralSequenceFirstPageXIsoOfEq_self (pq : ℤ × ℤ) :
    m.indexSpectralSequenceFirstPageXIsoOfEq dM hM pq pq.2 (pq.2 + 1) rfl rfl (pq.1 + pq.2) rfl =
      m.indexSpectralSequenceFirstPageXIso dM hM pq :=
  (m.indexSpectralSequenceFirstPageXIso_eq dM hM pq).symm

end TwistingCocycle

end TauCeti
