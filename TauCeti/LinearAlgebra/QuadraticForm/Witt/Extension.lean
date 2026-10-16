/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.QuadraticForm.Witt.Cancellation

/-!
# Witt's extension theorem

An isometry between two regular subspaces of a finite-dimensional quadratic space extends to an
isometry of the whole space.  The construction splits the ambient space as each subspace
orthogonally summed with its orthogonal complement.  Witt cancellation identifies the two
complements, and the two isometries then combine across these decompositions.  In fact the ambient
form itself need not be regular; regularity of the two subspaces is exactly what the proof uses.

This is Witt's extension theorem in the form used by the local classification and transfer theory
of quadratic forms.  The subspaces are required to be regular: without that hypothesis they need
not split off as orthogonal summands.

## Main results

* `QuadraticMap.IsometryEquiv.exists_extension`: Witt's extension theorem.
* `QuadraticMap.IsometryEquiv.extension`: a chosen extension, with the simplification theorem
  `QuadraticMap.IsometryEquiv.extension_apply` on the original subspace.
* `QuadraticMap.IsRepresentedBy.exists_equivalent_prod`: a regular form represented by a regular
  form splits off as an orthogonal summand with a regular complement.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Graduate Studies in Mathematics 67,
  American Mathematical Society (2005), Chapter I, Theorem 4.9.
-/

public section

noncomputable section

namespace QuadraticMap

universe u v

variable {K : Type u} [Field K] [Invertible (2 : K)]
  {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {W W' : Submodule K V}

/-- **Witt's extension theorem** (Lam I.4.9). An isometry between regular subspaces of a
finite-dimensional quadratic space extends to an isometry of the whole space. No regularity
hypothesis on the ambient form is needed. -/
theorem IsometryEquiv.exists_extension (f : (Q.restrict W).IsometryEquiv (Q.restrict W'))
    (hW : (Q.restrict W).Nondegenerate) :
    ∃ e : Q.IsometryEquiv Q, ∀ x : W, e (x : V) = (f x : V) := by
  have hW' : (Q.restrict W').Nondegenerate := f.nondegenerate_iff.mp hW
  let P := LinearMap.BilinForm.orthogonal Q.polarBilin W
  let P' := LinearMap.BilinForm.orthogonal Q.polarBilin W'
  have hcomp : IsCompl W P := hW.isCompl_orthogonal
  have hcomp' : IsCompl W' P' := hW'.isCompl_orthogonal
  let d : ((Q.restrict W).prod (Q.restrict P)).IsometryEquiv Q :=
    IsometryEquiv.prodRestrictOrthogonal Q W hcomp
  let d' : ((Q.restrict W').prod (Q.restrict P')).IsometryEquiv Q :=
    IsometryEquiv.prodRestrictOrthogonal Q W' hcomp'
  have hprod : ((Q.restrict W').prod (Q.restrict P)).Equivalent
      ((Q.restrict W').prod (Q.restrict P')) :=
    ⟨(f.symm.prod (IsometryEquiv.refl _)).trans (d.trans d'.symm)⟩
  obtain ⟨g⟩ : (Q.restrict P).Equivalent (Q.restrict P') :=
    TauCeti.equivalent_of_equivalent_prod hW' hprod
  refine ⟨d.symm.trans ((f.prod g).trans d'), fun x => ?_⟩
  rw [IsometryEquiv.trans_apply, IsometryEquiv.trans_apply]
  have hd : d.symm (x : V) = (x, 0) := by
    rw [IsometryEquiv.prodRestrictOrthogonal_symm_apply]
    have hx := Submodule.prodEquivOfIsCompl_symm_apply_left (p := W) (q := P) hcomp x
    rw [Submodule.prodEquivOfIsCompl_symm_apply] at hx
    exact hx
  rw [hd]
  have hfg : (f.prod g) (x, 0) = (f x, 0) := by
    apply Prod.ext
    · rfl
    · exact map_zero g
  rw [hfg]
  -- Expose the orthogonal-decomposition factor so its application lemma applies.
  change IsometryEquiv.prodRestrictOrthogonal Q W' hcomp' (f x, 0) = (f x : V)
  rw [IsometryEquiv.prodRestrictOrthogonal_apply]
  simp

/-- A chosen ambient isometry extending an isometry between two regular subspaces. -/
def IsometryEquiv.extension (f : (Q.restrict W).IsometryEquiv (Q.restrict W'))
    (hW : (Q.restrict W).Nondegenerate) : Q.IsometryEquiv Q :=
  (f.exists_extension hW).choose

/-- Witt's chosen extension agrees with the original isometry on its source subspace. -/
@[simp]
theorem IsometryEquiv.extension_apply (f : (Q.restrict W).IsometryEquiv (Q.restrict W'))
    (hW : (Q.restrict W).Nondegenerate) (x : W) :
    f.extension hW (x : V) = (f x : V) :=
  (f.exists_extension hW).choose_spec x

/-- **A represented regular form splits off.** If a regular form `Q₁` is represented by a regular
form `Q` on a finite-dimensional space, then `Q ≅ Q₁ ⊥ Q|_P` for a subspace `P` on which `Q` is
regular, namely the orthogonal complement of the image of `Q₁`. -/
theorem IsRepresentedBy.exists_equivalent_prod {V₁ : Type*} [AddCommGroup V₁] [Module K V₁]
    {Q₁ : QuadraticForm K V₁} (h : Q₁.IsRepresentedBy Q) (hQ₁ : Q₁.Nondegenerate)
    (hQ : Q.Nondegenerate) :
    ∃ P : Submodule K V, (Q.restrict P).Nondegenerate ∧ Q.Equivalent (Q₁.prod (Q.restrict P)) := by
  obtain ⟨f, hf, hfQ⟩ := (isRepresentedBy_iff Q₁ Q).mp h
  let e : Q₁.IsometryEquiv (Q.restrict (LinearMap.range f)) :=
    { toLinearEquiv := LinearEquiv.ofInjective f hf
      map_app' := hfQ }
  have hW := e.nondegenerate_iff.mp hQ₁
  exact ⟨_, hQ.nondegenerate_restrict_orthogonal hW,
    ⟨(IsometryEquiv.prodRestrictOrthogonal Q _ hW.isCompl_orthogonal).symm.trans
      (e.symm.prod (IsometryEquiv.refl _))⟩⟩

end QuadraticMap

end
