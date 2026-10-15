/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Equivalence
public import TauCeti.Algebra.Homology.DG.Twisted.Filtration
public import TauCeti.Algebra.Homology.SpectralObject.SpectralSequenceMap
public import TauCeti.Algebra.Homology.SpectralSequence.Filtered.Naturality
import TauCeti.Algebra.Homology.ModuleCat.Subobject

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
index spectral sequences of `TauCeti.Algebra.Homology.DG.Twisted.Filtration`, compatibly with the
Kronecker cocycle and with composition of continuation cocycles.

## Main definitions

* `TauCeti.ContinuationCocycle.indexFiltrationMap`: the morphism of filtered complexes induced by
  a continuation cocycle.
* `TauCeti.ContinuationCocycle.indexSpectralSequenceMap`: the induced morphism of index spectral
  sequences.

## Main results

* `TauCeti.continuationMap_mem_indexFiltrationSubmodule`: a matrix with no entries strictly
  increasing the index preserves the index filtration.
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

section Matrix

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommSemiring R] [Semiring A]
  [AddCommMonoid M] [Module R M] [Module Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {P Q : Type uP} [Fintype P] {ind : P → ℤ} {indQ : Q → ℤ}

/-- The continuation map of a matrix with no entries strictly increasing the index preserves the
index filtration. -/
theorem continuationMap_mem_indexFiltrationSubmodule (ν : P → Q → A)
    (hν : ∀ x y, ind x < indQ y → ν x y = 0) {p : ℤ} {f : P → M}
    (hf : f ∈ indexFiltrationSubmodule (R := R) ind p) :
    continuationMap R M ν f ∈ indexFiltrationSubmodule (R := R) indQ p := by
  rw [mem_indexFiltrationSubmodule_iff] at hf ⊢
  intro y hy
  rw [continuationMap_apply]
  refine Finset.sum_eq_zero fun x _ ↦ ?_
  rcases le_or_gt (ind x) p with hx | hx
  · rw [hν x y (hx.trans_lt hy), MulOpposite.op_zero, zero_smul]
  · rw [hf x hx, smul_zero]

end Matrix

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

section Vanishing

omit [GradedAlgebra 𝒜] in
/-- Over an algebra concentrated in cohomological degrees `≤ 0`, a continuation cocycle has no
entries strictly increasing the index: `ν x y` has degree `indQ y - ind x`. -/
theorem ν_eq_zero_of_lt_of_nonpos (ν : ContinuationCocycle mP mQ) (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥)
    {x : P} {y : Q} (hxy : ind x < indQ y) : ν.ν x y = 0 := by
  have hν := ν.mem_graded x y
  rw [h𝒜 _ (by omega)] at hν
  exact (Submodule.mem_bot R).1 hν

/-- The Kronecker continuation cocycle has no entries strictly increasing the index. -/
theorem refl_ν_eq_zero_of_lt [DecidableEq P] (hd : d 1 = 0) (m : TwistingCocycle 𝒜 d P ind)
    {x y : P} (hxy : ind x < ind y) : (refl hd m).ν x y = 0 := by
  rw [refl_ν, Matrix.one_apply_ne fun hxy' ↦ (hxy' ▸ hxy).false]

/-- A composite of continuation cocycles with no entries strictly increasing the index has no
such entries. -/
theorem comp_ν_eq_zero_of_lt (ν₁ : ContinuationCocycle mP mQ) (ν₂ : ContinuationCocycle mQ mS)
    (hν₁ : ∀ x y, ind x < indQ y → ν₁.ν x y = 0) (hν₂ : ∀ x y, indQ x < indS y → ν₂.ν x y = 0)
    {x : P} {y : S} (hxy : ind x < indS y) : (ν₁.comp h ν₂).ν x y = 0 := by
  rw [comp_ν, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun z _ ↦ ?_
  rcases lt_or_ge (ind x) (indQ z) with hz | hz
  · rw [Matrix.of_apply, hν₁ x z hz, zero_mul]
  · rw [Matrix.of_apply, Matrix.of_apply, hν₂ z y (hz.trans_lt hxy), mul_zero]

end Vanishing

variable (hM : IsDGRightModule h ℳ dM)

/-- A continuation cocycle with no entries strictly increasing the index sends each piece of the
index filtration into the corresponding piece. -/
theorem factors_indexFiltration (ν : ContinuationCocycle mP mQ)
    (hν : ∀ x y, ind x < indQ y → ν.ν x y = 0) (p : ℤ) :
    (mQ.indexFiltration dM hM p).Factors
      ((mP.indexFiltration dM hM p).arrow ≫ ν.continuationHom hM) := by
  refine HomologicalComplex.factors_of_forall_mem_range _ _ fun n x ↦ ?_
  rw [mQ.mem_range_indexFiltration_arrow_f_iff, HomologicalComplex.comp_f, ModuleCat.hom_comp,
    LinearMap.comp_apply, continuationHom_f_apply]
  refine mem_indexFiltrationSubmodule_iff.1
    (continuationMap_mem_indexFiltrationSubmodule ν.ν hν (mem_indexFiltrationSubmodule_iff.2 ?_))
  exact (mP.mem_range_indexFiltration_arrow_f_iff dM hM p n _).1 ⟨x, rfl⟩

/-- **The morphism of filtered complexes of a continuation cocycle**: for a continuation cocycle
with no entries strictly increasing the index, the continuation map as a morphism between the
functors of the index filtrations. -/
noncomputable def indexFiltrationMap (ν : ContinuationCocycle mP mQ)
    (hν : ∀ x y, ind x < indQ y → ν.ν x y = 0) :
    CochainComplex.filtrationFunctor (mP.indexFiltration dM hM)
        (mP.monotone_indexFiltration dM hM) ⟶
      CochainComplex.filtrationFunctor (mQ.indexFiltration dM hM)
        (mQ.monotone_indexFiltration dM hM) :=
  CochainComplex.filtrationFunctorMap _ _ (ν.continuationHom hM) (ν.factors_indexFiltration hM hν)

/-- The components of `indexFiltrationMap` are restrictions of the continuation map. -/
@[reassoc (attr := simp)]
theorem indexFiltrationMap_app_comp (ν : ContinuationCocycle mP mQ)
    (hν : ∀ x y, ind x < indQ y → ν.ν x y = 0) (a : EInt) :
    (ν.indexFiltrationMap hM hν).app a ≫
        (CochainComplex.filtrationFunctorObjIso _ _ a).hom ≫
          (CochainComplex.filtrationEInt (mQ.indexFiltration dM hM) a).arrow =
      (CochainComplex.filtrationFunctorObjIso _ _ a).hom ≫
        (CochainComplex.filtrationEInt (mP.indexFiltration dM hM) a).arrow ≫
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
    CochainComplex.filtrationFunctorMap_comp _ _ (ν₁.factors_indexFiltration hM hν₁)
      (ν₂.factors_indexFiltration hM hν₂)]
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
