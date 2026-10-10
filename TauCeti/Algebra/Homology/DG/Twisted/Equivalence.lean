/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.Homotopy
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Homologous twisting cocycles give homotopy equivalent twisted complexes

This file bundles the continuation maps and the chain homotopies of
`TauCeti.Algebra.Homology.DG.Twisted.Continuation` and
`TauCeti.Algebra.Homology.DG.Twisted.Homotopy` as morphisms and homotopies of the cochain
complexes `TwistingCocycle.twistedCochainComplex`, and deduces that homologous twisting cocycles
(the source's §1.4, Definitions 1.10 and 1.11) give homotopy equivalent twisted complexes.

Fix a differential graded algebra `(𝒜, d)`, a differential graded right module `(ℳ, dM)` and
twisting cocycles `mP` on `(P, ind)` and `mQ` on `(Q, indQ)`.

## Main definitions

* `TauCeti.ContinuationCocycle.continuationHom ν hM`: the continuation map of a continuation
  cocycle `ν : mP → mQ` as a morphism of cochain complexes.
* `TauCeti.ParametrizedCocycle.homotopy η hM`: the homotopy between the morphisms of two
  continuation cocycles induced by a parametrized cocycle `η`.
* `TauCeti.Homologous h mP mQ`: continuation cocycles `ν : mP → mQ`, `ν' : mQ → mP` whose two
  composites are joined to the Kronecker cocycles by parametrized cocycles.
* `TauCeti.Homologous.homotopyEquiv`: the homotopy equivalence of the twisted complexes of any
  differential graded right module induced by homologous twisting cocycles.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.4, Definitions 1.10 and 1.11.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, Chapters 3–4.
-/

public section

open CategoryTheory MulOpposite

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM}
  [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M] [Module R M]
  {P Q S : Type uP} {ind : P → ℤ} {indQ : Q → ℤ} {indS : S → ℤ} [Fintype P] [Fintype Q]
  [Fintype S] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {h : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  {mP : TwistingCocycle 𝒜 d P ind} {mQ : TwistingCocycle 𝒜 d Q indQ}
  {mS : TwistingCocycle 𝒜 d S indS}

/-! ### Morphisms between terms of the twisted complexes -/

section Components

variable (mP mQ) in
/-- A linear map `Φ : (P → M) → (Q → M)` which sends total degree `i` into total degree `j`, as a
morphism between the degree-`i` term of the twisted complex of `mP` and the degree-`j` term of
the twisted complex of `mQ`. -/
noncomputable def termHom (hM : IsDGRightModule h ℳ dM) (Φ : (P → M) →ₗ[R] (Q → M)) (i j : ℤ)
    (hΦ : ∀ f ∈ twistedTotalGrading ℳ ind i, Φ f ∈ twistedTotalGrading ℳ indQ j) :
    (mP.twistedCochainComplex dM hM).X i ⟶ (mQ.twistedCochainComplex dM hM).X j :=
  ModuleCat.ofHom
    ((twistedCochainComplexXEquiv mQ.mem_graded mQ.twisting hM j).symm.toLinearMap ∘ₗ
      Φ.restrict hΦ ∘ₗ (twistedCochainComplexXEquiv mP.mem_graded mP.twisting hM i).toLinearMap)

variable (mP mQ) in
@[simp]
theorem termHom_apply (hM : IsDGRightModule h ℳ dM) (Φ : (P → M) →ₗ[R] (Q → M)) (i j : ℤ)
    (hΦ : ∀ f ∈ twistedTotalGrading ℳ ind i, Φ f ∈ twistedTotalGrading ℳ indQ j)
    (x : (mP.twistedCochainComplex dM hM).X i) :
    (twistedCochainComplexXEquiv mQ.mem_graded mQ.twisting hM j
        ((termHom mP mQ hM Φ i j hΦ).hom x) : Q → M) =
      Φ (twistedCochainComplexXEquiv mP.mem_graded mP.twisting hM i x : P → M) := by
  simp [termHom]

/-- Two morphisms between terms of twisted complexes are equal when they agree on the underlying
functions. -/
theorem termHom_ext {hM : IsDGRightModule h ℳ dM} {i j : ℤ}
    {a b : (mP.twistedCochainComplex dM hM).X i ⟶ (mQ.twistedCochainComplex dM hM).X j}
    (hab : ∀ x, (twistedCochainComplexXEquiv mQ.mem_graded mQ.twisting hM j (a.hom x) : Q → M) =
      twistedCochainComplexXEquiv mQ.mem_graded mQ.twisting hM j (b.hom x)) : a = b := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  exact (twistedCochainComplexXEquiv mQ.mem_graded mQ.twisting hM j).injective
    (Subtype.ext (hab x))

end Components

/-! ### The morphism of a continuation cocycle -/

namespace ContinuationCocycle

/-- The continuation map of a continuation cocycle `ν : mP → mQ`, as a morphism of cochain
complexes between the twisted complexes of a differential graded right module. -/
noncomputable def continuationHom (ν : ContinuationCocycle mP mQ) (hM : IsDGRightModule h ℳ dM) :
    mP.twistedCochainComplex dM hM ⟶ mQ.twistedCochainComplex dM hM where
  f n := termHom mP mQ hM (continuationMap R M ν.ν) n n fun _ hf ↦
    ν.continuationMap_mem_twistedTotalGrading hf
  comm' i j hij := by
    obtain rfl : i + 1 = j := hij
    refine termHom_ext fun x ↦ ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, twistedCochainComplexXEquiv_d,
      termHom_apply]
    exact (ν.continuationMap_twistedDifferential hM _).symm

@[simp]
theorem continuationHom_f_apply (ν : ContinuationCocycle mP mQ) (hM : IsDGRightModule h ℳ dM)
    (n : ℤ) (x : (mP.twistedCochainComplex dM hM).X n) :
    (twistedCochainComplexXEquiv mQ.mem_graded mQ.twisting hM n
        (((ν.continuationHom hM).f n).hom x) : Q → M) =
      continuationMap R M ν.ν
        (twistedCochainComplexXEquiv mP.mem_graded mP.twisting hM n x : P → M) :=
  termHom_apply mP mQ hM _ n n _ x

/-- The Kronecker continuation cocycle induces the identity morphism. -/
@[simp]
theorem continuationHom_refl [DecidableEq P] (hM : IsDGRightModule h ℳ dM) :
    (refl h.map_one_eq_zero mP).continuationHom hM = 𝟙 (mP.twistedCochainComplex dM hM) := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ termHom_ext fun x ↦ ?_
  rw [continuationHom_f_apply, continuationMap_refl]
  rfl

/-- The composite of continuation cocycles induces the composite of the morphisms. -/
@[simp]
theorem continuationHom_comp (ν₁ : ContinuationCocycle mP mQ) (ν₂ : ContinuationCocycle mQ mS)
    (hM : IsDGRightModule h ℳ dM) :
    (ν₁.comp h ν₂).continuationHom hM = ν₁.continuationHom hM ≫ ν₂.continuationHom hM := by
  refine HomologicalComplex.hom_ext _ _ fun n ↦ termHom_ext fun x ↦ ?_
  rw [continuationHom_f_apply, continuationMap_comp]
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    continuationHom_f_apply]

end ContinuationCocycle

/-! ### The homotopy of a parametrized cocycle -/

namespace ParametrizedCocycle

variable {ν₀ ν₁ : ContinuationCocycle mP mQ}

/-- A parametrized cocycle `η` between continuation cocycles `ν₀` and `ν₁` is a homotopy between
their morphisms of twisted complexes, whose component `X i ⟶ X (i - 1)` is the homotopy map. -/
noncomputable def homotopy (η : ParametrizedCocycle ν₀ ν₁) (hM : IsDGRightModule h ℳ dM) :
    Homotopy (ν₁.continuationHom hM) (ν₀.continuationHom hM) where
  hom i j :=
    if hij : j + 1 = i then
      termHom mP mQ hM (homotopyMap η.h ℳ) i j fun f hf ↦ by
        have hj : i - 1 = j := by omega
        have := η.homotopyMap_mem_twistedTotalGrading hf
        rwa [hj] at this
    else 0
  zero i j hij := by
    have hij' : ¬ j + 1 = i := by simpa using hij
    simp only [hij', dite_false]
  comm i := by
    -- Write `i = n + 1`, so that both differentials are in the form `d n (n + 1)`.
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    have hnext : (ComplexShape.up ℤ).Rel (n + 1) (n + 1 + 1) := rfl
    have hprev : (ComplexShape.up ℤ).Rel n (n + 1) := rfl
    rw [dNext_eq _ hnext, prevD_eq _ hprev]
    simp only [dite_true]
    refine termHom_ext fun x ↦ ?_
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add, LinearMap.add_apply,
      map_add, Submodule.coe_add, termHom_apply, twistedCochainComplexXEquiv_d,
      ContinuationCocycle.continuationHom_f_apply]
    exact (sub_eq_iff_eq_add.mp (η.homotopyMap_twistedDifferential hM _)).trans (by abel)

/-- The component `X (j + 1) ⟶ X j` of the homotopy of a parametrized cocycle is its homotopy
map. -/
@[simp]
theorem homotopy_hom_apply (η : ParametrizedCocycle ν₀ ν₁) (hM : IsDGRightModule h ℳ dM) (j : ℤ)
    (x : (mP.twistedCochainComplex dM hM).X (j + 1)) :
    (twistedCochainComplexXEquiv mQ.mem_graded mQ.twisting hM j
        (((η.homotopy hM).hom (j + 1) j).hom x) : Q → M) =
      homotopyMap η.h ℳ (twistedCochainComplexXEquiv mP.mem_graded mP.twisting hM (j + 1) x :
        P → M) := by
  simp only [homotopy, dite_true, termHom_apply]

/-- The components of the homotopy of a parametrized cocycle vanish outside adjacent degrees. -/
theorem homotopy_hom_eq_zero (η : ParametrizedCocycle ν₀ ν₁) (hM : IsDGRightModule h ℳ dM)
    {i j : ℤ} (hij : j + 1 ≠ i) : (η.homotopy hM).hom i j = 0 := by
  simp only [homotopy, hij, dite_false]

end ParametrizedCocycle

/-! ### Homologous twisting cocycles -/

/-- Two twisting cocycles `mP` and `mQ` are **homologous** when there are continuation cocycles
`ν : mP → mQ` and `ν' : mQ → mP` whose two composites are joined to the Kronecker cocycles by
parametrized cocycles. -/
structure Homologous [DecidableEq P] [DecidableEq Q] (h : IsDGAlgebra 𝒜 d)
    (mP : TwistingCocycle 𝒜 d P ind) (mQ : TwistingCocycle 𝒜 d Q indQ) where
  /-- The continuation cocycle from `mP` to `mQ`. -/
  ν : ContinuationCocycle mP mQ
  /-- The continuation cocycle from `mQ` to `mP`. -/
  ν' : ContinuationCocycle mQ mP
  /-- The composite `ν ν'` is homotopic to the Kronecker cocycle of `mP`. -/
  homP : ParametrizedCocycle (ContinuationCocycle.refl h.map_one_eq_zero mP) (ν.comp h ν')
  /-- The composite `ν' ν` is homotopic to the Kronecker cocycle of `mQ`. -/
  homQ : ParametrizedCocycle (ContinuationCocycle.refl h.map_one_eq_zero mQ) (ν'.comp h ν)

namespace Homologous

variable [DecidableEq P] [DecidableEq Q]

/-- **Homologous twisting cocycles give homotopy equivalent twisted complexes**: for every
differential graded right module `(ℳ, dM)`, the twisted complexes of `mP` and `mQ` are
homotopy equivalent. -/
noncomputable def homotopyEquiv (H : Homologous h mP mQ) (hM : IsDGRightModule h ℳ dM) :
    HomotopyEquiv (mP.twistedCochainComplex dM hM) (mQ.twistedCochainComplex dM hM) where
  hom := H.ν.continuationHom hM
  inv := H.ν'.continuationHom hM
  homotopyHomInvId := by
    have := H.homP.homotopy hM
    rwa [ContinuationCocycle.continuationHom_refl,
      ContinuationCocycle.continuationHom_comp] at this
  homotopyInvHomId := by
    have := H.homQ.homotopy hM
    rwa [ContinuationCocycle.continuationHom_refl,
      ContinuationCocycle.continuationHom_comp] at this

@[simp]
theorem homotopyEquiv_hom (H : Homologous h mP mQ) (hM : IsDGRightModule h ℳ dM) :
    (H.homotopyEquiv hM).hom = H.ν.continuationHom hM :=
  (rfl)

@[simp]
theorem homotopyEquiv_inv (H : Homologous h mP mQ) (hM : IsDGRightModule h ℳ dM) :
    (H.homotopyEquiv hM).inv = H.ν'.continuationHom hM :=
  (rfl)

end Homologous

end TauCeti
