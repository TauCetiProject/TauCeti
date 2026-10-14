/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.LayerTateModule.Decomposition
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ProjectiveKernel

/-!
# Cohomology of the tame-frame relation module

This file packages the degree-two cohomological compatibility of the tame-frame relation-module
surjection on a finite Galois layer.

## Main result

* `TauCeti.exists_relationModule_surjective_of_tameFrame_h2Iso`: the tame-frame relation-module
  surjection has free rank-one kernel and induces an isomorphism on second group cohomology.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of
  (7.4.1).
-/

public section

namespace TauCeti

open CategoryTheory _root_.Rep

variable {p : ℕ} [Fact p.Prime]

/-- The tame-frame relation-module surjection induces an isomorphism on degree-two group
cohomology. -/
theorem exists_relationModule_surjective_of_tameFrame_h2Iso
    {L K : Type} [Field L] [Field K] [Algebra K L]
    [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K]
    [IsScalarTower ℚ_[p] K L] [IsGalois K L]
    (σ τ : L ≃ₐ[K] L)
    (hgen : Subgroup.closure {σ, τ} = ⊤) (hτ : ¬ p ∣ orderOf τ)
    {g : Fin (Module.finrank ℚ_[p] K + 2) → L ≃ₐ[K] L}
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    ∃ β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[
        MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive (padicCompletionUnits p L),
      Function.Surjective β ∧
        Nonempty (LinearMap.ker β ≃ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
          MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) ∧
        IsIso ((_root_.groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) 2).map
          (ofModuleMonoidAlgebra.map (ModuleCat.ofHom β))) := by
  obtain ⟨β, hβ, hker⟩ := exists_relationModule_surjective_of_tameFrame σ τ hgen hτ hg
  obtain ⟨e⟩ := hker
  let Λ := MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)
  let _ : Module.Projective Λ (LinearMap.ker β) := Module.Projective.of_equiv e.symm
  have := Module.Finite.right ℚ_[p] K L
  have hmap := groupCohomology.isIso_map_of_surjective_of_projective_ker β hβ 1
  exact ⟨β, hβ, ⟨e⟩, hmap⟩

end TauCeti
