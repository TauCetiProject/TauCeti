/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DG.Twisted.RowFinite.Homotopy

/-!
# Homologous row-finite twisting cocycles give homotopy equivalent complexes

This file bundles the coefficient continuation maps and coefficient homotopies of row-finite
continuation and parametrized cocycles as morphisms and homotopies of the coefficient complexes
`RowFiniteTwistingCocycle.coefficientCochainComplex`. It deduces that homologous row-finite
twisting cocycles give homotopy equivalent twisted complexes with coefficients in every DG right
module. The generator sets are arbitrary graded sets; no finiteness, one-sidedness or
boundedness hypothesis is used.

This is the row-finite form of `TauCeti.Homologous.homotopyEquiv`. Its typical use is the
comparison of twisted complexes built from different choices, such as different attaching
data of the cells of a CW complex.

## Main definitions

* `TauCeti.RowFiniteContinuationCocycle.continuationHom ν hM`: the coefficient continuation map
  of a row-finite continuation cocycle as a morphism of coefficient complexes.
* `TauCeti.RowFiniteParametrizedCocycle.homotopy η hM`: the homotopy between the morphisms of two
  row-finite continuation cocycles induced by a row-finite parametrized cocycle.
* `TauCeti.RowFiniteHomologous hA mP mQ`: row-finite continuation cocycles in both directions
  whose two composites are joined to the identity cocycles by parametrized cocycles.
* `TauCeti.RowFiniteHomologous.homotopyEquiv`: the induced homotopy equivalence of coefficient
  complexes.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, Section 1.4, Definitions 1.10 and 1.11.
* B. Keller, *Deriving DG categories*, Section 6.1.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti

universe uR uA uM uP

variable {R : Type uR} {A : Type uA} {M : Type uM} [CommRing R] [Ring A] [Algebra R A]
  [AddCommGroup M] [Module R M] [Module Aᵐᵒᵖ M] [IsScalarTower R Aᵐᵒᵖ M]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A} {hA : IsDGAlgebra 𝒜 d}
  {ℳ : ℤ → Submodule R M} [DirectSum.Decomposition ℳ]
  [SetLike.GradedSMul (InternalGrading.ofDecomposition 𝒜).opposite.piece ℳ] {dM : M →ₗ[R] M}
  {P Q S : Type uP} {indP : P → ℤ} {indQ : Q → ℤ} {indS : S → ℤ}
  {mP : RowFiniteTwistingCocycle 𝒜 d P indP} {mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ}
  {mS : RowFiniteTwistingCocycle 𝒜 d S indS}

open RowFiniteTwistingCocycle

/-! ### The morphism of a continuation cocycle -/

namespace RowFiniteContinuationCocycle

/-- The coefficient continuation map of a row-finite continuation cocycle, as a morphism of the
coefficient complexes of a DG right module. -/
def continuationHom (ν : RowFiniteContinuationCocycle mP mQ) (hM : IsDGRightModule hA ℳ dM) :
    mP.coefficientCochainComplex hM ⟶ mQ.coefficientCochainComplex hM :=
  coefficientCochainComplexHom hM ν.coefficientMap
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦ by
      simpa only [add_zero] using ν.coefficientMap_mem_totalGrading hf)
    (LinearMap.ext fun f ↦ ν.coefficientMap_differential hM f)

/-- The components of the morphism of a continuation cocycle are its coefficient map. -/
@[simp]
theorem continuationHom_f_apply (ν : RowFiniteContinuationCocycle mP mQ)
    (hM : IsDGRightModule hA ℳ dM) (n : ℤ) (x : (mP.coefficientCochainComplex hM).X n) :
    (mQ.coefficientCochainComplexXEquiv hM n (((ν.continuationHom hM).f n).hom x) : Q →₀ M) =
      ν.coefficientMap (mP.coefficientCochainComplexXEquiv hM n x) :=
  coefficientCochainComplexXEquiv_coefficientCochainComplexHom_f_apply hM _ _ _ n x

/-- The identity continuation cocycle induces the identity morphism. -/
@[simp]
theorem continuationHom_refl (hM : IsDGRightModule hA ℳ dM) :
    (refl mP hA).continuationHom hM = 𝟙 (mP.coefficientCochainComplex hM) :=
  coefficientCochainComplex_hom_ext hM fun n x ↦ by
    rw [continuationHom_f_apply, coefficientMap_refl, LinearMap.id_apply,
      HomologicalComplex.id_f, ModuleCat.hom_id, LinearMap.id_apply]

/-- The composite of continuation cocycles induces the composite of the morphisms. -/
@[simp]
theorem continuationHom_comp (ν : RowFiniteContinuationCocycle mP mQ)
    (μ : RowFiniteContinuationCocycle mQ mS) (hM : IsDGRightModule hA ℳ dM) :
    (ν.comp μ hA).continuationHom hM = ν.continuationHom hM ≫ μ.continuationHom hM :=
  coefficientCochainComplex_hom_ext hM fun n x ↦ by
    rw [continuationHom_f_apply, coefficientMap_comp, HomologicalComplex.comp_f,
      ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply, continuationHom_f_apply,
      continuationHom_f_apply]

end RowFiniteContinuationCocycle

/-! ### The homotopy of a parametrized cocycle -/

namespace RowFiniteParametrizedCocycle

variable {ν₀ ν₁ : RowFiniteContinuationCocycle mP mQ}

/-- A row-finite parametrized cocycle between continuation cocycles `ν₀` and `ν₁` is a homotopy
between their morphisms of coefficient complexes, whose components are the coefficient
homotopy. -/
def homotopy (η : RowFiniteParametrizedCocycle ν₀ ν₁) (hM : IsDGRightModule hA ℳ dM) :
    Homotopy (ν₁.continuationHom hM) (ν₀.continuationHom hM) :=
  coefficientCochainComplexHomotopy hM _ _ _ _ (η.coefficientHomotopy ℳ)
    (LinearMap.isHomogeneous_def.mpr fun _ _ hf ↦ by
      simpa only [sub_eq_add_neg] using η.coefficientHomotopy_mem_totalGrading hf)
    (LinearMap.ext fun f ↦ by
      rw [LinearMap.add_apply, LinearMap.add_apply, LinearMap.comp_apply, LinearMap.comp_apply,
        η.coefficientHomotopy_differential hM, sub_add_cancel])

/-- The component `X (j + 1) ⟶ X j` of the homotopy of a parametrized cocycle is its coefficient
homotopy. -/
@[simp]
theorem homotopy_hom_apply (η : RowFiniteParametrizedCocycle ν₀ ν₁)
    (hM : IsDGRightModule hA ℳ dM) (j : ℤ) (x : (mP.coefficientCochainComplex hM).X (j + 1)) :
    (mQ.coefficientCochainComplexXEquiv hM j (((η.homotopy hM).hom (j + 1) j).hom x) : Q →₀ M) =
      η.coefficientHomotopy ℳ (mP.coefficientCochainComplexXEquiv hM (j + 1) x) :=
  coefficientCochainComplexXEquiv_coefficientCochainComplexHomotopy_hom_apply hM _ _ _ _ _ _ _
    (j + 1) j (by omega) x

end RowFiniteParametrizedCocycle

/-! ### Homologous row-finite twisting cocycles -/

/-- Two row-finite twisting cocycles `mP` and `mQ` are **homologous** when there are
continuation cocycles `ν : mP → mQ` and `ν' : mQ → mP` whose two composites are joined to the
identity cocycles by parametrized cocycles. -/
structure RowFiniteHomologous (hA : IsDGAlgebra 𝒜 d) (mP : RowFiniteTwistingCocycle 𝒜 d P indP)
    (mQ : RowFiniteTwistingCocycle 𝒜 d Q indQ) where
  /-- The continuation cocycle from `mP` to `mQ`. -/
  ν : RowFiniteContinuationCocycle mP mQ
  /-- The continuation cocycle from `mQ` to `mP`. -/
  ν' : RowFiniteContinuationCocycle mQ mP
  /-- The composite `ν ν'` is homotopic to the identity cocycle of `mP`. -/
  homP : RowFiniteParametrizedCocycle (RowFiniteContinuationCocycle.refl mP hA) (ν.comp ν' hA)
  /-- The composite `ν' ν` is homotopic to the identity cocycle of `mQ`. -/
  homQ : RowFiniteParametrizedCocycle (RowFiniteContinuationCocycle.refl mQ hA) (ν'.comp ν hA)

namespace RowFiniteHomologous

/-- **Homologous row-finite twisting cocycles give homotopy equivalent twisted complexes**: for
every DG right module, the coefficient complexes of `mP` and `mQ` are homotopy equivalent. -/
def homotopyEquiv (H : RowFiniteHomologous hA mP mQ) (hM : IsDGRightModule hA ℳ dM) :
    HomotopyEquiv (mP.coefficientCochainComplex hM) (mQ.coefficientCochainComplex hM) where
  hom := H.ν.continuationHom hM
  inv := H.ν'.continuationHom hM
  homotopyHomInvId := by
    have := H.homP.homotopy hM
    rwa [RowFiniteContinuationCocycle.continuationHom_refl,
      RowFiniteContinuationCocycle.continuationHom_comp] at this
  homotopyInvHomId := by
    have := H.homQ.homotopy hM
    rwa [RowFiniteContinuationCocycle.continuationHom_refl,
      RowFiniteContinuationCocycle.continuationHom_comp] at this

@[simp]
theorem homotopyEquiv_hom (H : RowFiniteHomologous hA mP mQ) (hM : IsDGRightModule hA ℳ dM) :
    (H.homotopyEquiv hM).hom = H.ν.continuationHom hM :=
  (rfl)

@[simp]
theorem homotopyEquiv_inv (H : RowFiniteHomologous hA mP mQ) (hM : IsDGRightModule hA ℳ dM) :
    (H.homotopyEquiv hM).inv = H.ν'.continuationHom hM :=
  (rfl)

end RowFiniteHomologous

end TauCeti
