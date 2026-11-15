/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.LayerTateModule.Decomposition
import TauCeti.RepresentationTheory.Homological.GroupCohomology.ProjectiveKernel

/-!
# Cohomology of the tame-frame relation module

The tame-frame relation-module surjection on a finite Galois layer has a free rank-one kernel.
Its comparison with the p-adic completion of the units therefore induces an isomorphism on group
cohomology in every positive degree. The target is the Galois representation used by the existing
cohomology computations of the p-adic completion of units.

## Main result

* `AlgEquiv.exists_relationModule_surjective_isIso_groupCohomology`: the relation-module
  surjection has free rank-one kernel and induces an isomorphism in every positive degree.
  Degree two is the cohomological compatibility in the proof of NSW (7.4.1).

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of
  (7.4.1).
-/

public section

open CategoryTheory TauCeti

namespace AlgEquiv

variable {p : ℕ} [Fact p.Prime] {L K : Type} [Field L] [Field K] [Algebra K L]

local notation "Λ" => MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)

/-- **The relation-module surjection on cohomology** (the comparison of `H²(G, R^ab(p))` with
`H²(G, A(L))` in the proof of NSW (7.4.1)). Let `L/K` be a finite Galois extension of `p`-adic
fields with group `G` and `N = [K : ℚ_p]`. Let `σ, τ` generate
`G`, with the order of `τ` prime to `p`. Then for every generating family `g` of `G` of size
`N + 2` there is a surjection `β` from the relation module of `g` onto `A(L)` with kernel
isomorphic to `ℤ_p[G]`, and `β` induces an isomorphism `Hⁿ⁺¹(G, R) ≅ Hⁿ⁺¹(G, A(L))` for every
`n`. -/
theorem exists_relationModule_surjective_isIso_groupCohomology [Algebra ℚ_[p] L]
    [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K] [IsScalarTower ℚ_[p] K L] [IsGalois K L]
    (σ τ : L ≃ₐ[K] L) (hgen : Subgroup.closure {σ, τ} = ⊤)
    (hτ : ¬ p ∣ orderOf τ) {g : Fin (Module.finrank ℚ_[p] K + 2) → L ≃ₐ[K] L}
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    ∃ β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[Λ]
        Additive (padicCompletionUnits p L),
      Function.Surjective β ∧ Nonempty (LinearMap.ker β ≃ₗ[Λ] Λ) ∧
      ∀ n : ℕ, IsIso ((groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) (n + 1)).map
        (Rep.ofModuleMonoidAlgebra.map (ModuleCat.ofHom β) ≫
          (Rep.unitIso (Rep.of (padicCompletionUnitsRepresentation p L K))).inv)) := by
  have : FiniteDimensional K L := .right ℚ_[p] K L
  obtain ⟨β, hβ, ⟨eβ⟩⟩ := TauCeti.exists_relationModule_surjective_of_tameFrame σ τ hgen hτ hg
  have : Module.Projective Λ (LinearMap.ker β) := .of_equiv eβ.symm
  refine ⟨β, hβ, ⟨eβ⟩, fun n ↦ ?_⟩
  -- The comparison map is that of `β`, followed by the identification of the representation of
  -- the `ℤ_p[G]`-module `A(L)` with its Galois representation. The objects of the two factors
  -- are only defeq to the ones `Functor.map_comp` and instance search expect, so both are named.
  rw [(groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) (n + 1)).map_comp
    (Rep.ofModuleMonoidAlgebra.map (ModuleCat.ofHom β))
    (Rep.unitIso (Rep.of (padicCompletionUnitsRepresentation p L K))).inv]
  exact IsIso.comp_isIso'
    (TauCeti.groupCohomology.isIso_map_of_surjective_of_projective_ker β hβ n)
    ((groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) (n + 1)).mapIso
      (Rep.unitIso (Rep.of (padicCompletionUnitsRepresentation p L K))).symm).isIso_hom


end AlgEquiv
