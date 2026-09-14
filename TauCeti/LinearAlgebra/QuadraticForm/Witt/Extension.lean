/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation

/-!
# Witt's extension theorem

Over a field in which `2` is invertible, an isometry between two subspaces of a
finite-dimensional quadratic space on which the form restricts nondegenerately extends to an
isometry of the whole space. This is Witt's extension theorem, and the transitivity statement it
is usually used through: the isometries of a quadratic space carry a subspace with a
nondegenerate restriction onto any subspace isometric to it.

The argument is Witt cancellation applied to an orthogonal decomposition. A subspace `U` with a
nondegenerate restriction is complementary to its orthogonal complement
(`QuadraticMap.isCompl_orthogonal_of_restrict_nondegenerate`), so the form is isometric to
`Q|U ⊥ Q|Uᗮ` (`QuadraticMap.IsometryEquiv.prodRestrictOrthogonal`). Two such decompositions with
isometric first summands may be cancelled (`TauCeti.equivalent_of_equivalent_prod`), which leaves
the complements isometric; pairing the given isometry with an isometry of the complements extends
it to the whole space. The ambient form is *not* assumed nondegenerate: only the restrictions to
the two subspaces are, and that is exactly what the decomposition and the cancellation need.

## Main results

* `QuadraticMap.equivalent_restrict_orthogonal_of_equivalent_restrict`: isometric subspaces with
  nondegenerate restrictions have isometric orthogonal complements.
* `QuadraticMap.exists_isometryEquiv_apply_eq_of_isometryEquiv_restrict`: **Witt's extension
  theorem**, an isometry between such subspaces is the restriction of an isometry of the ambient
  form.
* `QuadraticMap.exists_isometryEquiv_map_eq_of_equivalent_restrict`: an isometry of the ambient
  form carries one such subspace onto the other.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §4 (Witt's
  extension theorem).
-/

public section

namespace QuadraticMap

universe u v

variable {K : Type u} {V : Type v} [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {U₁ U₂ : Submodule K V}

/-- **Witt's theorem on complements.** Two subspaces of a finite-dimensional quadratic space on
which the form restricts to isometric nondegenerate forms have isometric orthogonal complements.
The ambient form is not assumed nondegenerate. -/
theorem equivalent_restrict_orthogonal_of_equivalent_restrict
    (h₁ : (Q.restrict U₁).Nondegenerate)
    (h : (Q.restrict U₁).Equivalent (Q.restrict U₂)) :
    (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin U₁)).Equivalent
      (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin U₂)) := by
  obtain ⟨e⟩ := h
  have h₂ : (Q.restrict U₂).Nondegenerate := e.nondegenerate h₁
  -- Cancel the common summand `Q.restrict U₂` from the two orthogonal decompositions of `Q`,
  -- the first one transported along `e`.
  refine TauCeti.equivalent_of_equivalent_prod h₂
    (Equivalent.trans (Equivalent.prod ⟨e.symm⟩ (Equivalent.refl _)) ?_)
  exact Equivalent.trans
    ⟨IsometryEquiv.prodRestrictOrthogonal Q U₁
      (isCompl_orthogonal_of_restrict_nondegenerate Q h₁)⟩
    ⟨(IsometryEquiv.prodRestrictOrthogonal Q U₂
      (isCompl_orthogonal_of_restrict_nondegenerate Q h₂)).symm⟩

/-- **Witt's extension theorem.** An isometry between two subspaces of a finite-dimensional
quadratic space on which the form restricts nondegenerately is the restriction of an isometry of
the whole space. The ambient form is not assumed nondegenerate. -/
theorem exists_isometryEquiv_apply_eq_of_isometryEquiv_restrict
    (h₁ : (Q.restrict U₁).Nondegenerate)
    (e : (Q.restrict U₁).IsometryEquiv (Q.restrict U₂)) :
    ∃ f : Q.IsometryEquiv Q, ∀ u : U₁, f (u : V) = (e u : V) := by
  have h₂ : (Q.restrict U₂).Nondegenerate := e.nondegenerate h₁
  obtain ⟨g⟩ := equivalent_restrict_orthogonal_of_equivalent_restrict h₁ ⟨e⟩
  let φ₁ := IsometryEquiv.prodRestrictOrthogonal Q U₁
    (isCompl_orthogonal_of_restrict_nondegenerate Q h₁)
  let φ₂ := IsometryEquiv.prodRestrictOrthogonal Q U₂
    (isCompl_orthogonal_of_restrict_nondegenerate Q h₂)
  refine ⟨φ₁.symm.trans ((e.prod g).trans φ₂), fun u => ?_⟩
  have hu : φ₁.symm (u : V) = (u, 0) := by
    rw [IsometryEquiv.symm_apply_eq]
    simp [φ₁]
  simp [hu, φ₂]

/-- The isometries of a finite-dimensional quadratic space act transitively on the subspaces
carrying a given isometry class of nondegenerate restriction: if the form restricts to isometric
nondegenerate forms on `U₁` and `U₂`, some isometry of the whole space carries `U₁` onto `U₂`. -/
theorem exists_isometryEquiv_map_eq_of_equivalent_restrict
    (h₁ : (Q.restrict U₁).Nondegenerate)
    (h : (Q.restrict U₁).Equivalent (Q.restrict U₂)) :
    ∃ f : Q.IsometryEquiv Q, U₁.map (f : V ≃ₗ[K] V).toLinearMap = U₂ := by
  obtain ⟨e⟩ := h
  obtain ⟨f, hf⟩ := exists_isometryEquiv_apply_eq_of_isometryEquiv_restrict h₁ e
  refine ⟨f, le_antisymm ?_ fun v hv => ⟨(e.symm ⟨v, hv⟩ : V), (e.symm ⟨v, hv⟩).2, ?_⟩⟩
  · rintro _ ⟨u, hu, rfl⟩
    simp [hf ⟨u, hu⟩, (e ⟨u, hu⟩).2]
  · simpa using hf (e.symm ⟨v, hv⟩)

end QuadraticMap
