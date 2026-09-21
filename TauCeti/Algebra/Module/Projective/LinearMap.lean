/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.FiniteDimensional

/-!
# Hom spaces out of a projective module

Let `k` be a field and `A` a `k`-algebra. For a projective `A`-module `P` the functor
`Hom_A(P, -)` is exact, so when `P` and the targets are finite-dimensional over `k` the dimension
`dim_k Hom_A(P, -)` is additive across a submodule and its quotient.

## Main results

* `TauCeti.finrank_linearMap_quotient_add_finrank_linearMap`: additivity of `dim_k Hom_A(P, -)`
  for a projective `P`.
-/

public section

namespace TauCeti

variable {k A P M : Type*} [Field k] [Ring A] [Algebra k A]
  [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P] [FiniteDimensional k P]
  [Module.Projective A P]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M] [FiniteDimensional k M]

variable (k P) in
/-- **`dim_k Hom_A(P, -)` is additive**, for `P` projective and finite-dimensional over `k`: the
functor `Hom_A(P, -)` is exact, so a submodule and its quotient split the dimension of the hom
space out of `P`. -/
theorem finrank_linearMap_quotient_add_finrank_linearMap (N : Submodule A M) :
    Module.finrank k (P →ₗ[A] M ⧸ N) + Module.finrank k (P →ₗ[A] N)
      = Module.finrank k (P →ₗ[A] M) := by
  have : FiniteDimensional k N :=
    Module.Finite.of_injective ((N.subtype).restrictScalars k) N.injective_subtype
  have : FiniteDimensional k (M ⧸ N) :=
    Module.Finite.of_surjective ((N.mkQ).restrictScalars k) N.mkQ_surjective
  set α : (P →ₗ[A] N) →ₗ[k] (P →ₗ[A] M) := LinearMap.compRight k N.subtype with hα
  set β : (P →ₗ[A] M) →ₗ[k] (P →ₗ[A] M ⧸ N) := LinearMap.compRight k N.mkQ with hβ
  have hβsurj : Function.Surjective β := fun g =>
    (Module.projective_lifting_property N.mkQ g N.mkQ_surjective).imp fun _ h => h
  have hαinj : Function.Injective α := fun g g' h =>
    LinearMap.ext fun p => Subtype.ext (DFunLike.congr_fun h p)
  have hker : LinearMap.ker β = LinearMap.range α := by
    ext g
    refine ⟨fun hg => ?_, ?_⟩
    · have hmem : ∀ p, g p ∈ N := fun p =>
        (Submodule.Quotient.mk_eq_zero N).mp (DFunLike.congr_fun hg p)
      exact ⟨g.codRestrict N hmem, by ext p; simp [hα]⟩
    · rintro ⟨g', rfl⟩
      ext p
      simp [hα, hβ]
  have h1 := LinearMap.finrank_range_add_finrank_ker β
  rw [hker, LinearMap.range_eq_top.mpr hβsurj, Submodule.topEquiv.finrank_eq,
    ← (LinearEquiv.ofInjective α hαinj).finrank_eq] at h1
  exact h1

end TauCeti
