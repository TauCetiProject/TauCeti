/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Equivalence
public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.SpectralSequence
public import TauCeti.Algebra.Homology.ModuleCat.Subobject
public import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality

/-!
# Row-finite continuation maps and the index spectral sequence

Let `ν` be a row-finite continuation cocycle from a one-sided row-finite twisting cocycle `mP` on
`(P, indP)` to a one-sided row-finite twisting cocycle `mQ` on `(Q, indQ)`, over arbitrary graded
sets of generators. Its coefficient continuation map `P →₀ M → Q →₀ M` sends the coefficient `α`
at `x` to the coefficients `α · ν x y` at the generators `y`. It therefore preserves the index
filtrations `F_p`, the finite-support vectors carried by generators of index at most `p`, as soon as
`ν x y = 0` whenever `indP x < indQ y`. This holds automatically when the algebra is concentrated
in cohomological degrees `≤ 0`, since `ν x y` has degree `indQ y - indP x`
(`RowFiniteContinuationCocycle.ν_eq_zero_of_lt_of_nonpos`); this is the situation of the cubical
chains on a loop space.

The continuation map is then a morphism of filtered complexes, and so induces a morphism of the
row-finite index spectral sequences (`RowFiniteTwistingCocycle.indexSpectralSequence`), compatibly
with the identity cocycle and with composition of continuation cocycles. This extends
`TauCeti.ContinuationCocycle.indexSpectralSequenceMap` from finite to arbitrary generator sets.

## Main definitions

* `TauCeti.RowFiniteContinuationCocycle.indexFiltrationMap`: the morphism of filtered complexes
  induced by a row-finite continuation cocycle.
* `TauCeti.RowFiniteContinuationCocycle.indexSpectralSequenceMap`: the induced morphism of index
  spectral sequences.

## Main results

* `TauCeti.RowFiniteContinuationCocycle.coefficientMap_mem_rowFiniteIndexFiltration`: the
  coefficient continuation map preserves the index filtration.
* `TauCeti.RowFiniteContinuationCocycle.indexSpectralSequenceMap_refl`,
  `TauCeti.RowFiniteContinuationCocycle.indexSpectralSequenceMap_comp`: functoriality.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Definitions 1.10 and 3.38.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapter 3 and Section 4.2.
-/

public section

open CategoryTheory

namespace TauCeti

universe uR uA uM uP

namespace RowFiniteContinuationCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 d}
  {P Q S : Type uP} {indP : P → ℤ} {indQ : Q → ℤ} {indS : S → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 d P indP} {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}
  {mS : RowFiniteTwistingCocycle 𝒜 d S indS}

/-- A row-finite continuation cocycle with no entries strictly increasing the index sends
coefficient vectors carried by generators of index at most `p` to coefficient vectors carried by
generators of index at most `p`. -/
theorem coefficientMap_mem_rowFiniteIndexFiltration (ν : RowFiniteContinuationCocycle mP mQ)
    (hν : ∀ x y, indP x < indQ y → ν.ν x y = 0) {p : ℤ} {f : P →₀ M}
    (hf : f ∈ rowFiniteIndexFiltration (R := R) indP p) :
    ν.coefficientMap f ∈ rowFiniteIndexFiltration (R := R) indQ p := by
  rw [mem_rowFiniteIndexFiltration_iff] at hf ⊢
  intro y hy
  conv_lhs => rw [← Finsupp.sum_single f]
  rw [map_finsuppSum, Finsupp.sum_apply]
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  dsimp only
  rw [coefficientMap_single_apply]
  by_cases hx : p < indP x
  · rw [hf x hx, smul_zero]
  · rw [hν x y (by omega), MulOpposite.op_zero, zero_smul]

variable {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  (hM : IsDGRightModule hA ℳ dM) (hmP : ∀ x y, indP x ≤ indP y → mP.m x y = 0)
  (hmQ : ∀ x y, indQ x ≤ indQ y → mQ.m x y = 0) (hmS : ∀ x y, indS x ≤ indS y → mS.m x y = 0)

/-- A row-finite continuation cocycle with no entries strictly increasing the index sends each
stage of the index filtration into the corresponding stage. -/
theorem factors_indexSubobject (ν : RowFiniteContinuationCocycle mP mQ)
    (hν : ∀ x y, indP x < indQ y → ν.ν x y = 0) (p : ℤ) :
    (mQ.indexSubobject hM hmQ p).Factors
      ((mP.indexSubobject hM hmP p).arrow ≫ ν.continuationHom hM) := by
  refine Subobject.factors_of_forall_mem_range _ _ fun n x ↦ ?_
  rw [mQ.mem_range_indexSubobject_arrow_f_iff hM hmQ, HomologicalComplex.comp_f,
    ModuleCat.hom_comp, LinearMap.comp_apply, continuationHom_f_apply]
  refine (mem_rowFiniteIndexFiltration_iff indQ).1
    (ν.coefficientMap_mem_rowFiniteIndexFiltration hν
      ((mem_rowFiniteIndexFiltration_iff indP).2 ?_))
  exact (mP.mem_range_indexSubobject_arrow_f_iff hM hmP p n _).1 ⟨x, rfl⟩

/-- **The morphism of filtered complexes of a row-finite continuation cocycle** with no entries
strictly increasing the index: the coefficient continuation map, as a morphism between the
functors of the index filtrations. -/
noncomputable def indexFiltrationMap (ν : RowFiniteContinuationCocycle mP mQ)
    (hν : ∀ x y, indP x < indQ y → ν.ν x y = 0) :
    mP.indexFiltrationFunctor hM hmP ⟶ mQ.indexFiltrationFunctor hM hmQ :=
  CochainComplex.filtrationFunctorMap _ _ (ν.continuationHom hM)
    (ν.factors_indexSubobject hM hmP hmQ hν)

/-- The components of `indexFiltrationMap` are restrictions of the continuation map. -/
@[reassoc (attr := simp)]
theorem indexFiltrationMap_app_comp (ν : RowFiniteContinuationCocycle mP mQ)
    (hν : ∀ x y, indP x < indQ y → ν.ν x y = 0) (a : EInt) :
    (ν.indexFiltrationMap hM hmP hmQ hν).app a ≫
        (CochainComplex.filtrationFunctorObjIso _ _ a).hom ≫
          (CochainComplex.filtrationEInt (mQ.indexSubobject hM hmQ) a).arrow =
      (CochainComplex.filtrationFunctorObjIso _ _ a).hom ≫
        (CochainComplex.filtrationEInt (mP.indexSubobject hM hmP) a).arrow ≫
          ν.continuationHom hM :=
  CochainComplex.filtrationFunctorMap_app_comp _ _ a

/-- The identity continuation cocycle induces the identity of the filtered complex. -/
@[simp]
theorem indexFiltrationMap_refl (hν : ∀ x y, indP x < indP y → (refl mP hA).ν x y = 0) :
    (refl mP hA).indexFiltrationMap hM hmP hmP hν = 𝟙 _ := by
  rw [indexFiltrationMap, CochainComplex.filtrationFunctorMap_congr (continuationHom_refl hM),
    CochainComplex.filtrationFunctorMap_id]

/-- A composite of row-finite continuation cocycles induces the composite of the morphisms of
filtered complexes. -/
@[simp]
theorem indexFiltrationMap_comp (ν : RowFiniteContinuationCocycle mP mQ)
    (μ : RowFiniteContinuationCocycle mQ mS) (hν : ∀ x y, indP x < indQ y → ν.ν x y = 0)
    (hμ : ∀ x y, indQ x < indS y → μ.ν x y = 0)
    (hνμ : ∀ x y, indP x < indS y → (ν.comp μ hA).ν x y = 0) :
    (ν.comp μ hA).indexFiltrationMap hM hmP hmS hνμ =
      ν.indexFiltrationMap hM hmP hmQ hν ≫ μ.indexFiltrationMap hM hmQ hmS hμ := by
  rw [indexFiltrationMap, CochainComplex.filtrationFunctorMap_congr (continuationHom_comp ν μ hM),
    CochainComplex.filtrationFunctorMap_comp _ _ (ν.factors_indexSubobject hM hmP hmQ hν)
      (μ.factors_indexSubobject hM hmQ hmS hμ)]
  rfl

/-- **The morphism of index spectral sequences of a row-finite continuation cocycle** with no
entries strictly increasing the index: the morphism of spectral sequences induced by its morphism
of filtered complexes. -/
noncomputable def indexSpectralSequenceMap (ν : RowFiniteContinuationCocycle mP mQ)
    (hν : ∀ x y, indP x < indQ y → ν.ν x y = 0) :
    mP.indexSpectralSequence hM hmP ⟶ mQ.indexSpectralSequence hM hmQ :=
  Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (CochainComplex.spectralObjectMap (ν.indexFiltrationMap hM hmP hmQ hν))

/-- `indexSpectralSequenceMap` is the morphism of spectral sequences of `indexFiltrationMap`. -/
theorem indexSpectralSequenceMap_eq (ν : RowFiniteContinuationCocycle mP mQ)
    (hν : ∀ x y, indP x < indQ y → ν.ν x y = 0) :
    ν.indexSpectralSequenceMap hM hmP hmQ hν =
      Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
        (CochainComplex.spectralObjectMap (ν.indexFiltrationMap hM hmP hmQ hν)) :=
  (rfl)

/-- The identity continuation cocycle induces the identity of the index spectral sequence. -/
@[simp]
theorem indexSpectralSequenceMap_refl (hν : ∀ x y, indP x < indP y → (refl mP hA).ν x y = 0) :
    (refl mP hA).indexSpectralSequenceMap hM hmP hmP hν = 𝟙 _ := by
  rw [indexSpectralSequenceMap_eq, indexFiltrationMap_refl, CochainComplex.spectralObjectMap_id,
    Abelian.SpectralObject.spectralSequenceMap_id]

/-- A composite of row-finite continuation cocycles induces the composite of the morphisms of
index spectral sequences. -/
@[simp]
theorem indexSpectralSequenceMap_comp (ν : RowFiniteContinuationCocycle mP mQ)
    (μ : RowFiniteContinuationCocycle mQ mS) (hν : ∀ x y, indP x < indQ y → ν.ν x y = 0)
    (hμ : ∀ x y, indQ x < indS y → μ.ν x y = 0)
    (hνμ : ∀ x y, indP x < indS y → (ν.comp μ hA).ν x y = 0) :
    (ν.comp μ hA).indexSpectralSequenceMap hM hmP hmS hνμ =
      ν.indexSpectralSequenceMap hM hmP hmQ hν ≫ μ.indexSpectralSequenceMap hM hmQ hmS hμ := by
  rw [indexSpectralSequenceMap_eq, indexFiltrationMap_comp hM hmP hmQ hmS ν μ hν hμ,
    CochainComplex.spectralObjectMap_comp, Abelian.SpectralObject.spectralSequenceMap_comp]
  rfl

end RowFiniteContinuationCocycle

end TauCeti
