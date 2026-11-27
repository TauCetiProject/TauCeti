/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Computing the homology of complexes of modules from the cycles

The homology of a short complex `X₁ ⟶ X₂ ⟶ X₃` of modules is the quotient of the cycles `ker g` by
the boundaries `im f` (`CategoryTheory.ShortComplex.moduleCatHomologyIso`). So to identify the
homology with a module `N`, it suffices to give a surjective linear map from the cycles onto `N`
whose kernel consists exactly of the boundaries
(`CategoryTheory.ShortComplex.nonempty_linearEquiv_homology_of_surjective`). For a homological
complex of modules this computes the homology in degree `j` from the cycles of `j` and the
boundaries coming from the previous degree
(`HomologicalComplex.nonempty_linearEquiv_homology_of_surjective`). This is how the homology of an
explicit complex, for instance a finite model given by its differentials in chosen bases, is
computed degree by degree.
-/

public section

open CategoryTheory

namespace CategoryTheory.ShortComplex

variable {R : Type*} [Ring R] (S : ShortComplex (ModuleCat R)) {N : Type*} [AddCommGroup N]
  [Module R N]

/-- **Computing the homology of a short complex of modules.** If a surjective linear map `ψ` from
the cycles onto a module `N` vanishes exactly on the boundaries, then the homology is isomorphic
to `N`. -/
theorem nonempty_linearEquiv_homology_of_surjective (ψ : LinearMap.ker S.g.hom →ₗ[R] N)
    (hψ : Function.Surjective ψ) (hker : ∀ c, ψ c = 0 ↔ ∃ y, S.f.hom y = c) :
    Nonempty (S.homology ≃ₗ[R] N) := by
  have h : LinearMap.range S.moduleCatToCycles = LinearMap.ker ψ := by
    ext c
    rw [LinearMap.mem_ker, hker]
    exact ⟨fun ⟨y, hy⟩ ↦ ⟨y, congrArg Subtype.val hy⟩, fun ⟨y, hy⟩ ↦ ⟨y, Subtype.ext hy⟩⟩
  exact ⟨S.moduleCatHomologyIso.toLinearEquiv ≪≫ₗ Submodule.quotEquivOfEq _ _ h ≪≫ₗ
    ψ.quotKerEquivOfSurjective hψ⟩

end CategoryTheory.ShortComplex

namespace HomologicalComplex

variable {R : Type*} [Ring R] {ι : Type*} {c : ComplexShape ι}
  (K : HomologicalComplex (ModuleCat R) c) {N : Type*} [AddCommGroup N] [Module R N]

/-- **Computing the homology of a complex of modules in degree `j`.** If a surjective linear map
`ψ` from the cycles `ker (d j k)`, for `k` the next degree, onto a module `N` vanishes exactly on
the image of `d i j`, for `i` the previous degree, then the homology in degree `j` is isomorphic to
`N`. -/
theorem nonempty_linearEquiv_homology_of_surjective {i j k : ι} (hi : c.prev j = i)
    (hk : c.next j = k) (ψ : LinearMap.ker (K.d j k).hom →ₗ[R] N) (hψ : Function.Surjective ψ)
    (hker : ∀ z, ψ z = 0 ↔ ∃ y, (K.d i j).hom y = z) :
    Nonempty (K.homology j ≃ₗ[R] N) :=
  let ⟨e⟩ := (K.sc' i j k).nonempty_linearEquiv_homology_of_surjective ψ hψ hker
  ⟨(K.homologyIsoSc' i j k hi hk).toLinearEquiv ≪≫ₗ e⟩

end HomologicalComplex
