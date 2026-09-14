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

* `QuadraticMap.Nondegenerate.isCompl_orthogonal`: a regular subspace splits off orthogonally.
* `QuadraticMap.Nondegenerate.restrict_orthogonal`: its orthogonal complement is regular when the
  ambient quadratic form is regular.
* `QuadraticMap.IsometryEquiv.exists_extension`: Witt's extension theorem.
* `QuadraticMap.IsometryEquiv.extension`: a chosen extension, with the simplification theorem
  `QuadraticMap.IsometryEquiv.extension_apply` on the original subspace.

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

/-- A subspace on which a quadratic form restricts nondegenerately is complementary to its
orthogonal complement. -/
theorem Nondegenerate.isCompl_orthogonal (hW : (Q.restrict W).Nondegenerate) :
    IsCompl W (LinearMap.BilinForm.orthogonal Q.polarBilin W) := by
  apply LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate
    Q.polarBilin_isSymm.isRefl
  have hpolar := nondegenerate_polar_iff.mpr hW
  rwa [polarBilin_restrict] at hpolar

/-- In a regular finite-dimensional quadratic space, the orthogonal complement of a regular
subspace is regular. -/
theorem Nondegenerate.restrict_orthogonal (hQ : Q.Nondegenerate)
    (hW : (Q.restrict W).Nondegenerate) :
    (Q.restrict (LinearMap.BilinForm.orthogonal Q.polarBilin W)).Nondegenerate := by
  have hB : Q.polarBilin.Nondegenerate := nondegenerate_polar_iff.mpr hQ
  have hBsymm : Q.polarBilin.IsRefl := Q.polarBilin_isSymm.isRefl
  have hcomp : IsCompl W (LinearMap.BilinForm.orthogonal Q.polarBilin W) :=
    hW.isCompl_orthogonal
  apply nondegenerate_polar_iff.mp
  rw [polarBilin_restrict]
  exact
    (LinearMap.BilinForm.restrict_nondegenerate_iff_isCompl_orthogonal
      (B := Q.polarBilin) hBsymm).mpr (by
      rw [LinearMap.BilinForm.orthogonal_orthogonal hB hBsymm]
      exact hcomp.symm)

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
  have hd : d.symm (x : V) = (x, 0) := by
    rw [IsometryEquiv.prodRestrictOrthogonal_symm_apply]
    have hx := Submodule.prodEquivOfIsCompl_symm_apply_left (p := W) (q := P) hcomp x
    rw [Submodule.prodEquivOfIsCompl_symm_apply] at hx
    exact hx
  -- Read the composite isometry through its three explicit factors.
  change d' ((f.prod g) (d.symm (x : V))) = (f x : V)
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

end QuadraticMap

end
