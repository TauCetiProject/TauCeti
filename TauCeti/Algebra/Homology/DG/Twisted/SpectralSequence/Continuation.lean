/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Equivalence
public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence
public import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality

/-!
# Continuation maps and the index spectral sequence

Let `ν` be a continuation cocycle from a twisting cocycle `mP` on `(P, ind)` to a twisting cocycle
`mQ` on `(Q, indQ)`.  Its continuation map `ℳ ⊗ ⟨P⟩ → ℳ ⊗ ⟨Q⟩` sends `α ⊗ x` to
`Σ_y (α · ν x y) ⊗ y`, so it preserves the index filtrations `F_p = ⊕_{ind x ≤ p} ℳ ⊗ ⟨x⟩` as
soon as `ν x y = 0` whenever `ind x < indQ y`.  This holds automatically when the algebra is
concentrated in cohomological degrees `≤ 0`, since `ν x y` has degree `indQ y - ind x`
(`ContinuationCocycle.ν_eq_zero_of_lt_of_nonpos`); this is the situation of the cubical chains
on a loop space.

The continuation map is then a morphism of filtered complexes, and so induces a morphism of the
index spectral sequences (`TauCeti.TwistingCocycle.indexSpectralSequence`), compatibly with the
Kronecker cocycle and with composition of continuation cocycles.

## Main definitions

* `TauCeti.ContinuationCocycle.indexFiltrationMap`: the morphism of filtered complexes induced by
  a continuation cocycle.
* `TauCeti.ContinuationCocycle.indexSpectralSequenceMap`: the induced morphism of index spectral
  sequences.

## Main results

* `TauCeti.ContinuationCocycle.indexFiltrationMap_refl`, `indexFiltrationMap_comp`: functoriality at
  the level of filtered complexes.
* `TauCeti.ContinuationCocycle.indexSpectralSequenceMap_refl`,
  `TauCeti.ContinuationCocycle.indexSpectralSequenceMap_comp`: functoriality.

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

namespace ContinuationCocycle

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P Q S : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} {indS : S → ℤ} [Fintype P] [Fintype Q]
  [Fintype S] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {mS : TwistingCocycle 𝒜 d S indS}

variable (hM : IsDGRightModule h ℳ dM)

/-- **The morphism of filtered complexes of a continuation cocycle**: for a continuation cocycle
with no entries strictly increasing the index, the continuation map as a morphism between the
functors of the index filtrations. -/
noncomputable def indexFiltrationMap (ν : ContinuationCocycle mP mQ)
    (hν : ∀ x y, ind x < indQ y → ν.ν x y = 0) :
    CochainComplex.filtrationFunctor (mP.twistedIndexSubobject hM)
        (mP.twistedIndexSubobject_mono hM) ⟶
      CochainComplex.filtrationFunctor (mQ.twistedIndexSubobject hM)
        (mQ.twistedIndexSubobject_mono hM) :=
  CochainComplex.filtrationFunctorMap _ _ (ν.continuationHom hM)
    (ν.factors_twistedIndexSubobject hM hν)

/-- The components of `indexFiltrationMap` are restrictions of the continuation map. -/
@[reassoc (attr := simp)]
theorem indexFiltrationMap_app_comp (ν : ContinuationCocycle mP mQ)
    (hν : ∀ x y, ind x < indQ y → ν.ν x y = 0) (a : EInt) :
    (ν.indexFiltrationMap hM hν).app a ≫
        (CochainComplex.filtrationFunctorObjIso _ _ a).hom ≫
          (CochainComplex.filtrationEInt (mQ.twistedIndexSubobject hM) a).arrow =
      (CochainComplex.filtrationFunctorObjIso _ _ a).hom ≫
        (CochainComplex.filtrationEInt (mP.twistedIndexSubobject hM) a).arrow ≫
          ν.continuationHom hM :=
  CochainComplex.filtrationFunctorMap_app_comp _ _ a

/-- The Kronecker continuation cocycle induces the identity of the filtered complex. -/
@[simp]
theorem indexFiltrationMap_refl [DecidableEq P]
    (hν : ∀ x y, ind x < ind y → (refl h.map_one_eq_zero mP).ν x y = 0) :
    (refl h.map_one_eq_zero mP).indexFiltrationMap hM hν = 𝟙 _ := by
  rw [indexFiltrationMap, CochainComplex.filtrationFunctorMap_congr (continuationHom_refl hM),
    CochainComplex.filtrationFunctorMap_id]

/-- A composite of continuation cocycles induces the composite of the morphisms of filtered
complexes. -/
@[simp]
theorem indexFiltrationMap_comp (ν₁ : ContinuationCocycle mP mQ)
    (ν₂ : ContinuationCocycle mQ mS) (hν₁ : ∀ x y, ind x < indQ y → ν₁.ν x y = 0)
    (hν₂ : ∀ x y, indQ x < indS y → ν₂.ν x y = 0)
    (hν : ∀ x y, ind x < indS y → (ν₁.comp h ν₂).ν x y = 0) :
    (ν₁.comp h ν₂).indexFiltrationMap hM hν =
      ν₁.indexFiltrationMap hM hν₁ ≫ ν₂.indexFiltrationMap hM hν₂ := by
  rw [indexFiltrationMap, CochainComplex.filtrationFunctorMap_congr (continuationHom_comp ν₁ ν₂ hM),
    CochainComplex.filtrationFunctorMap_comp _ _ (ν₁.factors_twistedIndexSubobject hM hν₁)
      (ν₂.factors_twistedIndexSubobject hM hν₂)]
  rfl

/-- **The morphism of index spectral sequences of a continuation cocycle** with no entries
strictly increasing the index: the morphism of spectral sequences induced by its morphism of
filtered complexes. -/
noncomputable def indexSpectralSequenceMap (ν : ContinuationCocycle mP mQ)
    (hν : ∀ x y, ind x < indQ y → ν.ν x y = 0) :
    mP.indexSpectralSequence dM hM ⟶ mQ.indexSpectralSequence dM hM :=
  Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
    (CochainComplex.spectralObjectMap (ν.indexFiltrationMap hM hν))

/-- `indexSpectralSequenceMap` is the morphism of spectral sequences of `indexFiltrationMap`. -/
theorem indexSpectralSequenceMap_eq (ν : ContinuationCocycle mP mQ)
    (hν : ∀ x y, ind x < indQ y → ν.ν x y = 0) :
    ν.indexSpectralSequenceMap hM hν =
      Abelian.SpectralObject.spectralSequenceMap Abelian.SpectralObject.coreE₂Cohomological
        (CochainComplex.spectralObjectMap (ν.indexFiltrationMap hM hν)) :=
  (rfl)

/-- The Kronecker continuation cocycle induces the identity of the index spectral sequence. -/
@[simp]
theorem indexSpectralSequenceMap_refl [DecidableEq P]
    (hν : ∀ x y, ind x < ind y → (refl h.map_one_eq_zero mP).ν x y = 0) :
    (refl h.map_one_eq_zero mP).indexSpectralSequenceMap hM hν = 𝟙 _ := by
  rw [indexSpectralSequenceMap_eq, indexFiltrationMap_refl, CochainComplex.spectralObjectMap_id,
    Abelian.SpectralObject.spectralSequenceMap_id]

/-- A composite of continuation cocycles induces the composite of the morphisms of index spectral
sequences. -/
@[simp]
theorem indexSpectralSequenceMap_comp (ν₁ : ContinuationCocycle mP mQ)
    (ν₂ : ContinuationCocycle mQ mS) (hν₁ : ∀ x y, ind x < indQ y → ν₁.ν x y = 0)
    (hν₂ : ∀ x y, indQ x < indS y → ν₂.ν x y = 0)
    (hν : ∀ x y, ind x < indS y → (ν₁.comp h ν₂).ν x y = 0) :
    (ν₁.comp h ν₂).indexSpectralSequenceMap hM hν =
      ν₁.indexSpectralSequenceMap hM hν₁ ≫ ν₂.indexSpectralSequenceMap hM hν₂ := by
  rw [indexSpectralSequenceMap_eq, indexFiltrationMap_comp hM ν₁ ν₂ hν₁ hν₂,
    CochainComplex.spectralObjectMap_comp, Abelian.SpectralObject.spectralSequenceMap_comp]
  rfl

end ContinuationCocycle

end TauCeti
