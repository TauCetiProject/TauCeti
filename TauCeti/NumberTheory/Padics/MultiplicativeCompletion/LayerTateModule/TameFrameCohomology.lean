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

For a finite Galois layer of `p`-adic fields, the relation-module surjection onto the completed
multiplicative module has a free rank-one kernel over the group algebra. This kernel is
projective, so the coefficient map induces an isomorphism on group cohomology in every positive
degree. Its degree-two instance compares the extension classes used to pass from the tame layer to
finite quotients of the absolute Galois group.

## Main result

* `TauCeti.exists_relationModule_surjective_of_tameFrame_h2Iso`: chooses the tame-frame relation
  module surjection together with its kernel identification and the induced degree-two cohomology
  isomorphism.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of
  (7.4.1).
-/

public section

namespace TauCeti

open CategoryTheory _root_.Rep

variable {p : ℕ} [Fact p.Prime] {L K : Type} [Field L] [Field K] [Algebra K L]

/-- Let `L/K` be a finite Galois extension of `p`-adic fields with group `G`, and
`N = [K : ℚ_p]`. If `σ, τ` generate `G` and the order of `τ` is prime to `p`, then for every
generating family `g` of `G` of size `N + 2` there is a surjective `ℤ_p[G]`-linear map from the
relation module of `g` onto the `p`-adic completion `A(L)` of `Lˣ` whose kernel is isomorphic to
`ℤ_p[G]`, and whose induced map on degree-two group cohomology is an isomorphism. -/
theorem exists_relationModule_surjective_of_tameFrame_h2Iso
    [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K]
    [IsScalarTower ℚ_[p] K L] [IsGalois K L]
    (σ τ : L ≃ₐ[K] L) (hgen : Subgroup.closure {σ, τ} = ⊤) (hτ : ¬ p ∣ orderOf τ)
    {g : Fin (Module.finrank ℚ_[p] K + 2) → L ≃ₐ[K] L}
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    ∃ β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[
        MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Additive (padicCompletionUnits p L),
      Function.Surjective β ∧
        Nonempty (LinearMap.ker β ≃ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
          MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) ∧
        IsIso ((_root_.groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) 2).map
          (ofModuleMonoidAlgebra.map (ModuleCat.ofHom β))) := by
  obtain ⟨β, hβ, ⟨e⟩⟩ := exists_relationModule_surjective_of_tameFrame σ τ hgen hτ hg
  have := Module.Finite.right ℚ_[p] K L
  have : Module.Projective (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) (LinearMap.ker β) :=
    .of_equiv e.symm
  exact ⟨β, hβ, ⟨e⟩, groupCohomology.isIso_map_of_surjective_of_projective_ker β hβ 1⟩

end TauCeti
