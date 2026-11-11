/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

/-!
# Restricting an orthogonal map to an invariant submodule

An orthogonal automorphism `g` of a quadratic module that maps a submodule `W` onto itself
restricts to an orthogonal automorphism of `W` for the restricted form. Over a commutative ring in
which `2` is invertible, the orthogonal complement of an invariant submodule is again invariant, so
`g` also restricts to `W^⊥`; the case `W = K ∙ a` with `g a = a` is the restriction step of the
dimension induction in the Cartan--Dieudonné theorem.

## Main definitions

* `TauCeti.QuadraticMap.orthogonalGroup.restrict`: the restriction of an orthogonal map to a
  submodule it maps onto itself, as an element of the orthogonal group of the restricted form.

## Main results

* `TauCeti.QuadraticMap.orthogonalGroup.coe_restrict_apply`: the restriction acts as the original
  map.
* `TauCeti.QuadraticMap.orthogonalGroup.restrict_one`, `restrict_mul`, `restrict_inv`: the
  restriction respects the group operations.
* `TauCeti.QuadraticMap.isIsometry_associated_of_mem_orthogonalGroup`: an orthogonal map is an
  isometry of the associated bilinear form.
* `TauCeti.QuadraticMap.map_orthogonal_of_mem_orthogonalGroup`: an orthogonal map mapping `W` onto
  itself maps the orthogonal complement of `W` onto itself.
-/

public section

open QuadraticMap

namespace TauCeti.QuadraticMap

universe u v w

section Restrict

variable {R : Type u} {M : Type v} {N : Type w} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] {Q : QuadraticMap R M N} {W : Submodule R M}

/-- The restriction of an orthogonal map `g` to a submodule `W` with `W.map g = W`, as an
orthogonal map of the restricted form. -/
def orthogonalGroup.restrict (g : orthogonalGroup Q) (hW : W.map (g : M ≃ₗ[R] M).toLinearMap = W) :
    orthogonalGroup (Q.restrict W) :=
  ⟨(g : M ≃ₗ[R] M).ofSubmodules W W hW,
    mem_orthogonalGroup_iff.mpr fun u ↦ by
      simp only [QuadraticMap.restrict_apply, LinearEquiv.ofSubmodules_apply]
      exact map_app_of_mem_orthogonalGroup g.2 u⟩

@[simp]
theorem orthogonalGroup.coe_restrict_apply (g : orthogonalGroup Q)
    (hW : W.map (g : M ≃ₗ[R] M).toLinearMap = W) (u : W) :
    ((orthogonalGroup.restrict g hW : W ≃ₗ[R] W) u : M) = (g : M ≃ₗ[R] M) u :=
  LinearEquiv.ofSubmodules_apply _ _ _

@[simp]
theorem orthogonalGroup.restrict_one
    (hW : W.map ((1 : orthogonalGroup Q) : M ≃ₗ[R] M).toLinearMap = W) :
    orthogonalGroup.restrict (1 : orthogonalGroup Q) hW = 1 :=
  Subtype.ext (LinearEquiv.ext fun _ ↦ rfl)

theorem orthogonalGroup.restrict_mul (g h : orthogonalGroup Q)
    (hg : W.map (g : M ≃ₗ[R] M).toLinearMap = W) (hh : W.map (h : M ≃ₗ[R] M).toLinearMap = W)
    (hgh : W.map ((g * h : orthogonalGroup Q) : M ≃ₗ[R] M).toLinearMap = W) :
    orthogonalGroup.restrict (g * h) hgh =
      orthogonalGroup.restrict g hg * orthogonalGroup.restrict h hh :=
  Subtype.ext (LinearEquiv.ext fun _ ↦ rfl)

theorem orthogonalGroup.restrict_inv (g : orthogonalGroup Q)
    (hg : W.map (g : M ≃ₗ[R] M).toLinearMap = W)
    (hg' : W.map ((g⁻¹ : orthogonalGroup Q) : M ≃ₗ[R] M).toLinearMap = W) :
    orthogonalGroup.restrict g⁻¹ hg' = (orthogonalGroup.restrict g hg)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left (Subtype.ext (LinearEquiv.ext fun u ↦ Subtype.ext ?_))
  simp

end Restrict

section Orthogonal

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M] [Invertible (2 : R)]
  {Q : QuadraticForm R M} {g : M ≃ₗ[R] M}

/-- An orthogonal map is an isometry of the associated bilinear form. -/
theorem isIsometry_associated_of_mem_orthogonalGroup (hg : g ∈ orthogonalGroup Q) :
    BilinForm.IsIsometry (QuadraticMap.associated Q) g.toLinearMap :=
  BilinForm.isIsometry_iff.mpr fun x y ↦ by
    simp only [QuadraticMap.associated_apply, ← map_add, LinearEquiv.coe_coe,
      map_app_of_mem_orthogonalGroup hg]

/-- An orthogonal map mapping `W` onto itself maps the orthogonal complement of `W` onto itself. -/
theorem map_orthogonal_of_mem_orthogonalGroup (hg : g ∈ orthogonalGroup Q) {W : Submodule R M}
    (hW : W.map g.toLinearMap = W) :
    (LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) W).map g.toLinearMap =
      LinearMap.BilinForm.orthogonal (QuadraticMap.associated Q) W :=
  ((isIsometry_associated_of_mem_orthogonalGroup hg).map_orthogonal g.surjective W).trans
    (by rw [hW])

end Orthogonal

end TauCeti.QuadraticMap
