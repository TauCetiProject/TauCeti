/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Commute.Hom
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-!
# Intertwiners of linear automorphisms

A linear map `f : V →ₗ[K] W` **intertwines** automorphisms `a` of `V` and `b` of `W` when
`f ∘ a = b ∘ f`. This is the heterogeneous form of `SemiconjBy`: source and target live in
different modules, so the relation is not a statement inside one monoid and Mathlib's
`SemiconjBy` API does not apply to it.

## Main declarations

* `LinearMap.GeneralLinearGroup.commute_ofLinearEquiv_iff`: conversion from linear equivalences
  to the general linear group preserves and reflects commutation.
* `LinearMap.GeneralLinearGroup.comp_inv_eq_inv_comp_iff`: a linear map intertwines two
  automorphisms if and only if it intertwines their inverses.
-/

public section

namespace LinearMap.GeneralLinearGroup

universe u v w

variable {K : Type u} {V : Type v} {W : Type w}
variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W]

/-- Two linear equivalences commute if and only if their images in the general linear group
commute. -/
theorem commute_ofLinearEquiv_iff (f g : V ≃ₗ[K] V) :
    Commute (ofLinearEquiv f) (ofLinearEquiv g) ↔ Commute f g :=
  commute_map_iff (generalLinearEquiv K V).symm.injective

/-- **Intertwining passes to inverses.** A linear map `f` intertwines the automorphisms `a⁻¹`
and `b⁻¹` if and only if it intertwines `a` and `b`. -/
@[simp]
theorem comp_inv_eq_inv_comp_iff {f : V →ₗ[K] W} {a : GeneralLinearGroup K V}
    {b : GeneralLinearGroup K W} : f ∘ₗ ↑a⁻¹ = ↑b⁻¹ ∘ₗ f ↔ f ∘ₗ a = b ∘ₗ f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> ext x
  · simpa [← Module.End.mul_apply] using
      congr((b : Module.End K W) ($h ((a : Module.End K V) x))).symm
  · simpa [← Module.End.mul_apply] using
      congr((↑b⁻¹ : Module.End K W) ($h ((↑a⁻¹ : Module.End K V) x))).symm

end LinearMap.GeneralLinearGroup
