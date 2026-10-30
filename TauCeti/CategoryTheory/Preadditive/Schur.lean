/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Schur
public import TauCeti.CategoryTheory.Linear.Endomorphism

/-!
# Endomorphisms of a simple object are scalars

Let `k` be an algebraically closed field and `X` a simple object of a `k`-linear preadditive
category with kernels, whose endomorphisms form a finite-dimensional `k`-vector space. Schur's
lemma (`CategoryTheory.endomorphism_simple_eq_smul_id`) says that every endomorphism of `X` is a
scalar multiple `c • 𝟙 X` of the identity. We package this as a `k`-algebra isomorphism
`TauCeti.endAlgEquivOfSimple k X : End X ≃ₐ[k] k`, the inverse of the structure map
`algebraMap k (End X)`, which sends `c` to `c • 𝟙 X`.

Applied to a simple monoidal unit, this identifies the scalars `𝟙_ C ⟶ 𝟙_ C` of a fusion
category with elements of `k`, which is how traces and dimensions are read as numbers.

The finite-dimensionality assumption cannot be dropped: finite-dimensional vector spaces over
the rational function field `k(t)`, viewed as a `k`-linear category, have a simple unit whose
endomorphism algebra is `k(t)`.

## Main declarations

* `TauCeti.endAlgEquivOfSimple`: the isomorphism `End X ≃ₐ[k] k`, whose inverse is
  `algebraMap k (End X)` by `TauCeti.endAlgEquivOfSimple_symm_apply`;
* `TauCeti.endAlgEquivOfSimple_smul_id`: every endomorphism `f` is `endAlgEquivOfSimple k X f`
  times the identity, and `TauCeti.endAlgEquivOfSimple_apply_eq_iff` characterizes the scalar;
* `CategoryTheory.End.of_id`, `CategoryTheory.End.of_comp`, … of
  `TauCeti.CategoryTheory.Linear.Endomorphism` are `simp` lemmas pushing `End.of` inside
  expressions built from morphisms `f : X ⟶ X`, after which `map_mul`, `map_add`, … let `simp`
  compute scalars of composites, sums and multiples.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], for Schur's lemma
-/

public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace TauCeti

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [HasKernels C]

/-- The structure map `k → End X` of a simple object `X` with finite-dimensional endomorphisms
over an algebraically closed field is bijective: this is Schur's lemma. -/
theorem bijective_algebraMap_end_of_simple (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)] :
    Function.Bijective (algebraMap k (End X)) := by
  refine ⟨(algebraMap k (End X)).injective, fun f ↦ ?_⟩
  obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k f.asHom
  exact ⟨c, End.ext (by simpa [Algebra.algebraMap_eq_smul_one] using hc)⟩

/-- **Schur's lemma** as an identification of algebras: the endomorphisms of a simple object `X`
with finite-dimensional endomorphisms over an algebraically closed field `k` are the scalars
`k`. This is the inverse of the structure map `algebraMap k (End X)`, `c ↦ c • 𝟙 X`. -/
noncomputable def endAlgEquivOfSimple (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)] :
    End X ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (End X)) <| by
    rw [show ⇑(Algebra.ofId k (End X)) = algebraMap k (End X) from funext (Algebra.ofId_apply _)]
    exact bijective_algebraMap_end_of_simple k X).symm

variable {k}
variable {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]

/-- The inverse of `endAlgEquivOfSimple` is the structure map `algebraMap k (End X)`. -/
@[simp]
theorem endAlgEquivOfSimple_symm_apply (c : k) :
    (endAlgEquivOfSimple k X).symm c = algebraMap k (End X) c := by
  rw [endAlgEquivOfSimple, AlgEquiv.symm_symm, AlgEquiv.ofBijective_apply, Algebra.ofId_apply]

/-- Every endomorphism of a simple object is its scalar times the identity. -/
@[simp]
theorem endAlgEquivOfSimple_smul_id (f : End X) : endAlgEquivOfSimple k X f • 𝟙 X = f.asHom := by
  rw [← End.algebraMap_asHom, ← endAlgEquivOfSimple_symm_apply, AlgEquiv.symm_apply_apply]

/-- The scalar of an endomorphism `f` is the unique `c` with `f = c • 𝟙 X`. -/
theorem endAlgEquivOfSimple_apply_eq_iff (f : End X) (c : k) :
    endAlgEquivOfSimple k X f = c ↔ f.asHom = c • 𝟙 X := by
  rw [← AlgEquiv.eq_symm_apply, End.ext_iff, endAlgEquivOfSimple_symm_apply, End.algebraMap_asHom]

end TauCeti
