/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Smooth.NoetherianDescent
import Mathlib.RingTheory.Smooth.Flat

/-!
# Finite étale algebras have models of finite type

Mathlib's `Algebra.Etale.exists_subalgebra_fg` shows that an étale `A`-algebra `B` is the base
change `A ⊗[A₀] B₀` of an étale algebra `B₀` over an `R`-subalgebra `A₀` of `A` of finite type.
This file shows that when `B` is moreover finite over `A`, the model can be chosen finite étale.

Starting from an étale model `B₀` over `A₀`, the images `1 ⊗ y` of finitely many generators `y`
of `B₀` are integral over `A`, so they satisfy monic equations over `A`. Adjoining the finitely
many coefficients of these equations to `A₀` gives a larger subalgebra `A₁` of finite type, and
the equations already hold in `A₁ ⊗[A₀] B₀`: since `B₀` is flat over `A₀`, the map
`A₁ ⊗[A₀] B₀ → A ⊗[A₀] B₀` is injective. Hence `A₁ ⊗[A₀] B₀` is a finite étale model of `B`.

These models reduce statements about finite étale algebras over arbitrary rings to statements
over rings of finite type over `R`, for example their descent along directed colimits of rings.

## Main results

* `Algebra.Etale.exists_subalgebra_fg_of_finite`: a finite étale `A`-algebra is the base change of
  a finite étale algebra over an `R`-subalgebra of `A` of finite type.

## References

* [Stacks Project, Lemma 10.143.3 (8)](https://stacks.math.columbia.edu/tag/00U2) for the étale
  case.
-/

public section

universe u

open TensorProduct Polynomial

namespace Algebra.Etale

variable (R : Type*) [CommRing R] (A : Type u) (B : Type*) [CommRing A] [Algebra R A]
  [CommRing B] [Algebra A B]

/-- Let `A` be an `R`-algebra. If `B` is a finite étale `A`-algebra, there exists an
`R`-subalgebra of finite type `A₀` of `A` and a finite étale `A₀`-algebra `B₀` such that
`B ≃ₐ A ⊗[A₀] B₀`. -/
theorem exists_subalgebra_fg_of_finite [Etale A B] [Module.Finite A B] :
    ∃ (A₀ : Subalgebra R A) (B₀ : Type u) (_ : CommRing B₀) (_ : Algebra A₀ B₀),
      A₀.FG ∧ Etale A₀ B₀ ∧ Module.Finite A₀ B₀ ∧ Nonempty (B ≃ₐ[A] A ⊗[A₀] B₀) := by
  classical
  obtain ⟨A₀, B₀, _, _, hA₀, _, ⟨e⟩⟩ := exists_subalgebra_fg R A B
  obtain ⟨t, ht⟩ := (FiniteType.out : (⊤ : Subalgebra A₀ B₀).FG)
  -- The images of the generators of `B₀` are integral over `A`.
  have : Module.Finite A (A ⊗[A₀] B₀) := .equiv e.toLinearEquiv
  choose p hpm hp using fun y : t ↦ IsIntegral.isIntegral (R := A) ((1 : A) ⊗ₜ[A₀] (y : B₀))
  -- Adjoin the coefficients of their equations to `A₀`.
  let A₁ : Subalgebra R A := A₀ ⊔ adjoin R (Finset.univ.biUnion fun y ↦ (p y).coeffs : Set A)
  have hle : A₀ ≤ A₁ := le_sup_left
  let : Algebra A₀ A₁ := (Subalgebra.inclusion hle).toAlgebra
  have : IsScalarTower A₀ A₁ A := .of_algebraMap_eq fun _ ↦ rfl
  -- Each equation lifts to a monic polynomial over `A₁`.
  have hq (y : t) : ∃ q : A₁[X], q.map (algebraMap A₁ A) = p y ∧ q.Monic := by
    refine (lifts_and_natDegree_eq_and_monic ((lifts_iff_coeff_lifts _).2 fun n ↦ ?_)
      (hpm y)).imp fun _ h ↦ ⟨h.1, h.2.2⟩
    by_cases hn : (p y).coeff n = 0
    · exact ⟨0, by simp [hn]⟩
    refine ⟨⟨_, le_sup_right (a := A₀) (subset_adjoin ?_)⟩, rfl⟩
    exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨y, Finset.mem_univ _, coeff_mem_coeffs hn⟩)
  choose q hqp hqm using hq
  -- Since `B₀` is flat over `A₀`, the equations already hold over `A₁`.
  let Φ := Algebra.TensorProduct.map (ofId A₁ A) (.id A₀ B₀)
  have hΦ₁ (a : A₁) (b : B₀) : Φ (a ⊗ₜ b) = (a : A) ⊗ₜ b := Algebra.TensorProduct.map_tmul ..
  -- As an `A₀`-linear map, `Φ` is by definition `rTensor B₀` of the inclusion `A₁ → A`.
  have hΦ : Function.Injective Φ :=
    Module.Flat.rTensor_preserves_injective_linearMap (M := B₀)
      ((ofId A₁ A).toLinearMap.restrictScalars A₀) Subtype.val_injective
  have hint (y : t) : IsIntegral A₁ ((1 : A₁) ⊗ₜ[A₀] (y : B₀)) := by
    refine ⟨q y, hqm y, hΦ ?_⟩
    rw [← aeval_def, ← aeval_algHom_apply, hΦ₁]
    simpa [← aeval_def, ← hqp] using hp y
  have : Module.Finite A₁ (A₁ ⊗[A₀] B₀) := by
    refine ⟨?_⟩
    rw [← Algebra.top_toSubmodule, ← TensorProduct.adjoin_one_tmul_image_eq_top (A := A₁) _ ht]
    exact fg_adjoin_of_finite (t.finite_toSet.image _) (by simpa using fun y hy ↦ hint ⟨y, hy⟩)
  exact ⟨A₁, A₁ ⊗[A₀] B₀, inferInstance, inferInstance,
    hA₀.sup (Subalgebra.fg_adjoin_finset _), inferInstance, inferInstance,
    ⟨e.trans (TensorProduct.cancelBaseChange A₀ A₁ A A B₀).symm⟩⟩

end Algebra.Etale
