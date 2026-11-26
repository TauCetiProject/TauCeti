/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.DirectLimit
public import TauCeti.Algebra.Homology.DG.Twisted.SpectralSequence.Continuation
public import TauCeti.Algebra.Homology.SpectralSequence.Colimit
public import TauCeti.Algebra.Homology.SpectralSequence.Reindex

/-!
# The index spectral sequence of a continuation system and its direct limit

Let `S` be a continuation system over a preorder `ι` (`TauCeti.ContinuationSystem`): twisting
cocycles `m i` with continuation cocycles `ν : m i → m j` for `i ≤ j`, which compose only up to
parametrized cocycles. Each twisted complex carries its index spectral sequence
(`TauCeti.TwistingCocycle.indexSpectralSequence`), and each continuation cocycle a morphism of
index spectral sequences (`TauCeti.ContinuationCocycle.indexSpectralSequenceMap`), as soon as the
continuation cocycles do not raise the index.

Suppose that the algebra is concentrated in cohomological degrees `≤ 0`, as the cubical chains on
a loop space are. Then no continuation cocycle raises the index, and the homotopies given by the
parametrized cocycles raise the index filtration by at most one, so homotopic continuation cocycles
induce the same morphisms from the second page `E₂` on
(`TauCeti.ParametrizedCocycle.indexSpectralSequenceMap_hom_eq`). On the first page they need not.
Read from `E₂` on (page `3` in Mathlib's numbering, through
`CategoryTheory.SpectralSequence.reindex` with no page shift), they induce the same morphism of
spectral sequences (`TauCeti.ParametrizedCocycle.reindexMap_indexSpectralSequenceMap_eq`). So the
index spectral sequences of the system, read from `E₂` on, form a functor on `ι`
(`TauCeti.ContinuationSystem.indexSpectralSequenceFunctor`). This is the spectral sequence
counterpart of the cohomology functor `TauCeti.ContinuationSystem.homologyFunctor`, whose maps are
also only functorial up to these homotopies.

When colimits of shape `ι` of modules exist and are exact, as filtered colimits are, spectral
sequences have colimits of shape `ι`, computed page by page
(`CategoryTheory.SpectralSequence.hasColimitsOfShape`). Each term of the colimit of the index
spectral sequences of the system, from `E₂` on, is the colimit over `ι` of the corresponding terms
of the index spectral sequences (`TauCeti.ContinuationSystem.isColimitPageXMapCocone`). For a
system of Floer complexes of Hamiltonians of increasing slopes, with coefficients in a DG local
system `𝓕`, this colimit is the spectral sequence of symplectic homology with DG coefficients of
Barraud–Damian–Humilière–Oancea (Theorem 3.49(i)). The `E₂` term of each index spectral sequence
is the homology of its classical complex
(`TauCeti.TwistingCocycle.indexSpectralSequenceSecondPageXIso`); the maps between these `E₂` terms
are not compared here with the classical continuation maps, and the convergence of the colimit
(Theorem 3.49(ii)) is not treated.

For a constant continuation system the functor has identity maps
(`TauCeti.ContinuationSystem.indexSpectralSequenceFunctor_const_map`).

## Main definitions

* `TauCeti.ContinuationSystem.indexSpectralSequenceFunctor`: the index spectral sequences of a
  continuation system from `E₂` on, as a functor on `ι`.
* `TauCeti.ContinuationSystem.indexSpectralSequenceFunctorObjPageXIso`: its terms are those of the
  index spectral sequences.

## Main results

* `TauCeti.ParametrizedCocycle.reindexMap_indexSpectralSequenceMap_eq`: homotopic continuation
  cocycles induce the same morphism of index spectral sequences from `E₂` on.
* `TauCeti.ContinuationSystem.indexSpectralSequenceFunctor_map_hom_f`: the maps of the functor are
  those of the continuation cocycles.
* `TauCeti.ContinuationSystem.isColimitPageXMapCocone`: from `E₂` on, a term of a page of the
  colimit of the functor is the colimit of the corresponding terms.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Theorem 3.49 and its proof.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press, 1994,
  Theorem 2.6.15 (filtered colimits of modules are exact).
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe w uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}

namespace ParametrizedCocycle

variable {h : IsDGAlgebra 𝒜 d} {P Q : Type uP} [Fintype P] [Fintype Q] {ind : P → ℤ}
  {indQ : Q → ℤ} {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {ν₀ ν₁ : ContinuationCocycle mP mQ}

/-- **Homotopic continuation cocycles induce the same morphism of index spectral sequences from
`E₂` on**: over an algebra concentrated in degrees `≤ 0`, continuation cocycles joined by a
parametrized cocycle induce the same morphism once the first pages are dropped. -/
theorem reindexMap_indexSpectralSequenceMap_eq (η : ParametrizedCocycle ν₀ ν₁)
    (hM : IsDGRightModule h ℳ dM) (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥) :
    SpectralSequence.reindexMap (c' := fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))
        (r₀' := 3) 0 (Equiv.refl _) (fun _ _ _ ↦ by simp) (by lia)
        (ν₀.indexSpectralSequenceMap hM fun _ _ ↦ ν₀.ν_eq_zero_of_lt_of_nonpos h𝒜) =
      SpectralSequence.reindexMap (c' := fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ))
        (r₀' := 3) 0 (Equiv.refl _) (fun _ _ _ ↦ by simp) (by lia)
        (ν₁.indexSpectralSequenceMap hM fun _ _ ↦ ν₁.ν_eq_zero_of_lt_of_nonpos h𝒜) :=
  SpectralSequence.reindexMap_congr _ _ _ _ fun r _ ↦ η.indexSpectralSequenceMap_hom_eq hM _ _
    (fun _ _ ↦ η.h_eq_zero_of_add_one_lt_of_nonpos h𝒜) (r + 0) (by lia)

end ParametrizedCocycle

namespace ContinuationSystem

variable {h : IsDGAlgebra 𝒜 d} {ι : Type w} [Preorder ι]
  (S : ContinuationSystem.{w, uR, uA, uP} 𝒜 d h ι) (hM : IsDGRightModule h ℳ dM)
  (h𝒜 : ∀ n, 0 < n → 𝒜 n = ⊥)

/-- **The index spectral sequences of a continuation system**, from the second page `E₂` on (page
`3` in Mathlib's numbering), as a functor on `ι`: `i` goes to the index spectral sequence of the
twisted complex of `m i` with its first page dropped, and `i ≤ j` to the morphism induced by the
continuation cocycle `ν`. It is a functor because, over an algebra concentrated in degrees `≤ 0`,
homotopic continuation cocycles induce the same morphisms from `E₂` on. The body is exposed
because the statements of `indexSpectralSequenceFunctor_map` and
`indexSpectralSequenceFunctor_const_map` only typecheck by unfolding its values. -/
@[expose]
noncomputable def indexSpectralSequenceFunctor :
    ι ⥤ CohomologicalSpectralSequence (ModuleCat.{max uP uM} R) 3 where
  obj i := ((S.m i).indexSpectralSequence dM hM).reindex 0 (Equiv.refl _) (fun _ _ _ ↦ by simp)
    (by lia)
  map g := SpectralSequence.reindexMap 0 (Equiv.refl _) (fun _ _ _ ↦ by simp) (by lia)
    ((S.ν (leOfHom g)).indexSpectralSequenceMap hM fun _ _ ↦
      (S.ν (leOfHom g)).ν_eq_zero_of_lt_of_nonpos h𝒜)
  map_id i := by
    obtain ⟨η⟩ := S.nonempty_refl i
    rw [← η.reindexMap_indexSpectralSequenceMap_eq hM h𝒜,
      ContinuationCocycle.indexSpectralSequenceMap_refl]
    exact (SpectralSequence.reindexFunctor _ _ 3 0 (Equiv.refl _) (fun _ _ _ ↦ by simp)
      (by lia)).map_id _
  map_comp g g' := by
    obtain ⟨η⟩ := S.nonempty_comp (leOfHom g) (leOfHom g')
    rw [← η.reindexMap_indexSpectralSequenceMap_eq hM h𝒜,
      ContinuationCocycle.indexSpectralSequenceMap_comp hM _ _
        (fun _ _ ↦ ContinuationCocycle.ν_eq_zero_of_lt_of_nonpos _ h𝒜)
        (fun _ _ ↦ ContinuationCocycle.ν_eq_zero_of_lt_of_nonpos _ h𝒜)]
    exact (SpectralSequence.reindexFunctor _ _ 3 0 (Equiv.refl _) (fun _ _ _ ↦ by simp)
      (by lia)).map_comp _ _

/-- The value of `indexSpectralSequenceFunctor` at `i` is the index spectral sequence of `m i`
from `E₂` on. -/
@[simp]
theorem indexSpectralSequenceFunctor_obj (i : ι) :
    (S.indexSpectralSequenceFunctor hM h𝒜).obj i =
      ((S.m i).indexSpectralSequence dM hM).reindex (r₀' := 3) 0 (Equiv.refl _)
        (fun _ _ _ ↦ by simp) (by lia) :=
  (rfl)

/-- The maps of `indexSpectralSequenceFunctor` are the morphisms of index spectral sequences of the
continuation cocycles, with their first pages dropped. -/
@[simp]
theorem indexSpectralSequenceFunctor_map {i j : ι} (g : i ⟶ j) :
    (S.indexSpectralSequenceFunctor hM h𝒜).map g =
      SpectralSequence.reindexMap (r₀' := 3) 0 (Equiv.refl _) (fun _ _ _ ↦ by simp) (by lia)
        ((S.ν (leOfHom g)).indexSpectralSequenceMap hM fun _ _ ↦
          (S.ν (leOfHom g)).ν_eq_zero_of_lt_of_nonpos h𝒜) :=
  (rfl)

/-- A term of a page of `indexSpectralSequenceFunctor` at `i` is the corresponding term of the
index spectral sequence of `m i`. -/
noncomputable def indexSpectralSequenceFunctorObjPageXIso (i : ι) (r : ℤ) (hr : 3 ≤ r)
    (pq : ℤ × ℤ) :
    (((S.indexSpectralSequenceFunctor hM h𝒜).obj i).page r).X pq ≅
      (((S.m i).indexSpectralSequence dM hM).page r).X pq :=
  ((S.m i).indexSpectralSequence dM hM).reindexPageXIso 0 (Equiv.refl _) (fun _ _ _ ↦ by simp)
    (by lia) r r hr (by lia) pq pq rfl

/-- **The maps of `indexSpectralSequenceFunctor` are those of the continuation cocycles**: on the
terms of the pages, identified with those of the index spectral sequences by
`indexSpectralSequenceFunctorObjPageXIso`, the map of `i ≤ j` is the morphism of index spectral
sequences of `ν`. -/
@[reassoc]
theorem indexSpectralSequenceFunctor_map_hom_f {i j : ι} (g : i ⟶ j) (r : ℤ) (hr : 3 ≤ r)
    (pq : ℤ × ℤ) :
    (((S.indexSpectralSequenceFunctor hM h𝒜).map g).hom r).f pq ≫
        (S.indexSpectralSequenceFunctorObjPageXIso hM h𝒜 j r hr pq).hom =
      (S.indexSpectralSequenceFunctorObjPageXIso hM h𝒜 i r hr pq).hom ≫
        (((S.ν (leOfHom g)).indexSpectralSequenceMap hM fun _ _ ↦
          (S.ν (leOfHom g)).ν_eq_zero_of_lt_of_nonpos h𝒜).hom r).f pq :=
  SpectralSequence.reindexMap_hom_f_comp_reindexPageXIso_hom 0 (Equiv.refl _)
    (fun _ _ _ ↦ by simp) (by lia) _ r r hr (by lia) pq pq rfl

section Const

variable {P : Type uP} [Fintype P] [DecidableEq P] {ind : P → ℤ} (m : TwistingCocycle 𝒜 d P ind)

/-- The index spectral sequence functor of a constant continuation system has identity maps. -/
theorem indexSpectralSequenceFunctor_const_map {i j : ι} (g : i ⟶ j) :
    ((const h ι m).indexSpectralSequenceFunctor hM h𝒜).map g = 𝟙 _ := by
  rw [indexSpectralSequenceFunctor_map]
  refine (congrArg (SpectralSequence.reindexMap (r₀' := 3) 0 (Equiv.refl _) (fun _ _ _ ↦ by simp)
    (by lia)) (ContinuationCocycle.indexSpectralSequenceMap_refl (mP := m) hM fun _ _ ↦
      ContinuationCocycle.ν_eq_zero_of_lt_of_nonpos _ h𝒜)).trans ?_
  exact (SpectralSequence.reindexFunctor _ _ 3 0 (Equiv.refl _) (fun _ _ _ ↦ by simp)
    (by lia)).map_id _

end Const

/-! ### The direct limit -/

section Colimit

variable [HasColimitsOfShape ι (ModuleCat.{max uP uM} R)]
  [HasExactColimitsOfShape ι (ModuleCat.{max uP uM} R)]

/-- **The terms of the colimit spectral sequence are the colimits of the terms**: from `E₂` on,
the term at `pq` on page `r` of the colimit of `indexSpectralSequenceFunctor` is the colimit over
`ι` of the terms at `pq` on page `r` of the index spectral sequences of the system, through the
maps into the colimit. -/
noncomputable def isColimitPageXMapCocone (r : ℤ) (hr : 3 ≤ r) (pq : ℤ × ℤ) :
    IsColimit ((SpectralSequence.pageFunctor (ModuleCat.{max uP uM} R) _ 3 r hr ⋙
      HomologicalComplex.eval (ModuleCat.{max uP uM} R) _ pq).mapCocone
        (colimit.cocone (S.indexSpectralSequenceFunctor hM h𝒜))) :=
  -- Instance search gets stuck on the universe constraints of the instances of `ModuleCat` when
  -- looking for this instance, so it is supplied by hand.
  haveI := SpectralSequence.preservesColimitsOfShape_pageFunctor (C := ModuleCat.{max uP uM} R)
    (c := fun r ↦ ComplexShape.up' (⟨r, 1 - r⟩ : ℤ × ℤ)) (r₀ := 3) (J := ι) r hr
  isColimitOfPreserves _ (colimit.isColimit _)

end Colimit

end ContinuationSystem

end TauCeti
