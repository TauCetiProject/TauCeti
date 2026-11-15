/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Decomposition
public import TauCeti.RepresentationTheory.Homological.GroupCohomology.ProjectiveKernel

/-!
# Cohomology of the tame-frame relation module

For a finite Galois layer, the relation-module surjection onto the completed multiplicative module
has a free rank-one kernel over the group algebra. This kernel is projective, so the coefficient
map induces an isomorphism on group cohomology in every positive degree. Its degree-two instance
compares the extension classes used to pass from the tame layer to finite quotients of the absolute
Galois group.

## Main result

* `TauCeti.exists_relationModule_surjective_of_tameFrame_h2Iso_of_exact`: given projective
  presentations of a Tate module, chooses the tame-frame relation-module surjection together with
  its kernel identification and the induced degree-two cohomology isomorphism.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of
  (7.4.1).
-/

public section

namespace TauCeti

open CategoryTheory _root_.Rep

variable {p : ℕ} [Fact p.Prime] {L : Type} [Field L] {K : Type} [Field K] [Algebra K L]

/-- There is a surjective tame-frame relation-module map to the completed multiplicative module
whose kernel is isomorphic to the free rank-one group-algebra module, and whose induced map on
degree-two group cohomology is an isomorphism. -/
theorem exists_relationModule_surjective_of_tameFrame_h2Iso_of_exact
    [Algebra ℚ_[p] L] [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K]
    [IsScalarTower ℚ_[p] K L] [IsGalois K L]
    {Y P₀ P₁ : Type*} [AddCommGroup Y]
    [Module (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) Y]
    [AddCommGroup P₀] [Module (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) P₀]
    [Module.Finite (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) P₀]
    [Module.Projective (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) P₀]
    [AddCommGroup P₁] [Module (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) P₁]
    [Module.Finite (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) P₁]
    [Module.Projective (MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)) P₁]
    {d : P₁ →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] P₀}
    {ρ : P₀ →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Y}
    (hdρ : Function.Exact d ρ) (hd : Function.Injective d) (hρ : Function.Surjective ρ)
    {ι : Additive ↑(padicCompletionUnits p L) →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)] Y}
    {π : Y →ₗ[MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)]
      RingHom.ker (MonoidAlgebra.augmentation ℤ_[p] (L ≃ₐ[K] L))}
    (hιπ : Function.Exact ι π) (hι : Function.Injective ι) (hπ : Function.Surjective π)
    (h : Finite (pPowerRootsOfUnity p L)) (σ τ : L ≃ₐ[K] L)
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
  obtain ⟨β, hβ, hker⟩ := exists_relationModule_surjective_of_tameFrame_of_exact
    hdρ hd hρ hιπ hι hπ h σ τ hgen hτ hg
  obtain ⟨e⟩ := hker
  let Λ := MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)
  let _ : Module.Projective Λ (LinearMap.ker β) := Module.Projective.of_equiv e.symm
  have := Module.Finite.right ℚ_[p] K L
  have hmap := groupCohomology.isIso_map_of_surjective_of_projective_ker β hβ 1
  exact ⟨β, hβ, ⟨e⟩, hmap⟩

end TauCeti
