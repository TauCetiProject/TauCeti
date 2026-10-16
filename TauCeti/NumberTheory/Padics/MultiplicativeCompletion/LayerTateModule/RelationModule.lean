/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.LayerTateModule.Basic
public import TauCeti.Algebra.MonoidAlgebra.RelationModule.Basic
import TauCeti.NumberTheory.LocalField.FiniteExtension.Basic
import TauCeti.NumberTheory.LocalField.RootsOfUnity.Basic
import TauCeti.NumberTheory.Padics.MultiplicativeCompletion.Decomposition
import TauCeti.RepresentationTheory.Homological.GroupCohomology.ProjectiveKernel

/-!
# The relation-module surjection of a tame layer on cohomology

Let `L/K` be a finite Galois extension of `p`-adic fields with group `G = Gal(L/K)`, let
`N = [K : ℚ_p]`, and let `A(L)` be the `p`-adic completion of `Lˣ`. When `G` has a generating
pair `σ, τ` with `τ` of order prime to `p`, a Tate module `Y` of the layer gives, for every
generating family `g` of `G` of size `N + 2`, a surjection `β : R → A(L)` from the relation module
`R` of `g` with kernel `ℤ_p[G]` (`TauCeti.exists_relationModule_surjective_of_tameFrame`). By
Lyndon's theorem (`TauCeti.freeProfiniteGroup.abelianizationProPEquivRelationModule`) `R` is the
module `R^ab(p)` of the presentation of `G` on `g`, so this is the integral sequence
`0 → ℤ_p[G] → R^ab(p) → A(L) → 0` of the proof of NSW (7.4.1).

This file shows that `β` induces an isomorphism `Hⁿ(G, R) ≅ Hⁿ(G, A(L))` in every positive degree:
its kernel `ℤ_p[G]` is free, so has no cohomology in positive degrees, and the long exact sequence
does the rest (`TauCeti.groupCohomology.isIso_map_of_surjective_of_projective_ker`). In degree two
this identifies `H²(G, R^ab(p))` with `H²(G, A(L))`, which is cyclic of order the `p`-part of
`#G` (`TauCeti.exists_zmultiples_eq_top_groupCohomology_two_padicCompletionUnits`). This is the
comparison through which `β` is matched with the classes of the group extensions
`F ⧸ ⁅R, R⁆R(p) → G` and `G_K ⧸ ⁅G_L, G_L⁆G_L(p) → G` when it is lifted to a homomorphism between
them.

The cohomology of `A(L)` is that of its Galois representation `padicCompletionUnitsRepresentation`,
the representation the cohomology computations of `A(L)` are stated for, identified with the
representation of the `ℤ_p[G]`-module `A(L)` by `Rep.unitIso`; the cohomology of `R` is that of the
representation attached to the `ℤ_p[G]`-module `R`.

## Main results

* `TauCeti.LayerTateModule.exists_relationModule_surjective_isIso_groupCohomology`: on a layer
  with a generating tame frame, the relation module of every generating family of size `N + 2`
  maps onto `A(L)` with kernel `ℤ_p[G]`, by a map inducing isomorphisms on group cohomology in
  every positive degree.

## References

* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., proof of (7.4.1).
-/

public section

open CategoryTheory

namespace TauCeti.LayerTateModule

variable {p : ℕ} [Fact p.Prime] {L K : Type} [Field L] [Field K] [Algebra K L]

local notation "Λ" => MonoidAlgebra ℤ_[p] (L ≃ₐ[K] L)

/-- **The relation-module surjection on cohomology** (the comparison of `H²(G, R^ab(p))` with
`H²(G, A(L))` in the proof of NSW (7.4.1)). Let `L/K` be a finite Galois extension of `p`-adic
fields with group `G`, `N = [K : ℚ_p]`, and `Y` a Tate module of the layer. Let `σ, τ` generate
`G`, with the order of `τ` prime to `p`. Then for every generating family `g` of `G` of size
`N + 2` there is a surjection `β` from the relation module of `g` onto `A(L)` with kernel
isomorphic to `ℤ_p[G]`, and `β` induces an isomorphism `Hⁿ⁺¹(G, R) ≅ Hⁿ⁺¹(G, A(L))` for every
`n`. -/
theorem exists_relationModule_surjective_isIso_groupCohomology [Algebra ℚ_[p] L]
    [Module.Finite ℚ_[p] L] [Algebra ℚ_[p] K] [IsScalarTower ℚ_[p] K L] [IsGalois K L]
    (Y : LayerTateModule p L K) (σ τ : L ≃ₐ[K] L) (hgen : Subgroup.closure {σ, τ} = ⊤)
    (hτ : ¬ p ∣ orderOf τ) {g : Fin (Module.finrank ℚ_[p] K + 2) → L ≃ₐ[K] L}
    (hg : Subgroup.closure (Set.range g) = ⊤) :
    ∃ β : MonoidAlgebra.relationModule ℤ_[p] (L ≃ₐ[K] L) g →ₗ[Λ]
        Additive (padicCompletionUnits p L),
      Function.Surjective β ∧ Nonempty (LinearMap.ker β ≃ₗ[Λ] Λ) ∧
      ∀ n : ℕ, IsIso ((groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) (n + 1)).map
        (Rep.ofModuleMonoidAlgebra.map (ModuleCat.ofHom β) ≫
          (Rep.unitIso (Rep.of (padicCompletionUnitsRepresentation p L K))).inv)) := by
  have : FiniteDimensional K L := .right ℚ_[p] K L
  -- `p`-power roots of unity of `L` are finite: give `L` its local-field structure.
  let _ := finiteExtensionValuativeRel ℚ_[p] L
  let _ := finiteExtensionNormedFieldTopology ℚ_[p] L
  have := finiteExtension_isNonarchimedeanLocalField ℚ_[p] L
  have hpL : (p : L) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[p] L)]
    exact (map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  -- The resolution `0 → ker f → ℤ_p[G]^m → Y → 0`; its kernel is finitely generated because
  -- `ℤ_p[G]` is a finite `ℤ_p`-algebra.
  obtain ⟨m, f, hf, hker⟩ := Y.projdim
  have : IsNoetherian Λ (Fin m → Λ) := isNoetherian_of_tower ℤ_[p] inferInstance
  obtain ⟨β, hβ, ⟨eβ⟩⟩ := exists_relationModule_surjective_of_tameFrame
    f.exact_subtype_ker_map (LinearMap.ker f).injective_subtype hf Y.exact_ι_π Y.ι_injective
    Y.π_surjective (finite_pPowerRootsOfUnity hpL) σ τ hgen hτ hg
  have : Module.Projective Λ (LinearMap.ker β) := .of_equiv eβ.symm
  refine ⟨β, hβ, ⟨eβ⟩, fun n ↦ ?_⟩
  -- The comparison map is that of `β`, followed by the identification of the representation of
  -- the `ℤ_p[G]`-module `A(L)` with its Galois representation. The objects of the two factors
  -- are only defeq to the ones `Functor.map_comp` and instance search expect, so both are named.
  rw [(groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) (n + 1)).map_comp
    (Rep.ofModuleMonoidAlgebra.map (ModuleCat.ofHom β))
    (Rep.unitIso (Rep.of (padicCompletionUnitsRepresentation p L K))).inv]
  exact IsIso.comp_isIso' (groupCohomology.isIso_map_of_surjective_of_projective_ker β hβ n)
    ((groupCohomology.functor ℤ_[p] (L ≃ₐ[K] L) (n + 1)).mapIso
      (Rep.unitIso (Rep.of (padicCompletionUnitsRepresentation p L K))).symm).isIso_hom

end TauCeti.LayerTateModule
