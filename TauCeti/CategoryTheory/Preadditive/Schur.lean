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

Let `k` be a field and `X` an object of a `k`-linear preadditive category with nontrivial
endomorphism ring whose structure map `algebraMap k (End X)` is surjective (in particular, a
simple object over an algebraically closed field `k`, with kernels and finite-dimensional
endomorphisms, by Schur's lemma `CategoryTheory.endomorphism_simple_eq_smul_id`). We package this
as a `k`-algebra isomorphism `TauCeti.endAlgEquivOfSurjective` (specialized to
`TauCeti.endAlgEquivOfSimple k X : End X ≃ₐ[k] k`), the inverse of `algebraMap k (End X)`, which
sends `c` to `c • 𝟙 X`.

Applied to a simple monoidal unit, this identifies the scalars `𝟙_ C ⟶ 𝟙_ C` of a fusion
category with elements of `k`, which is how traces and dimensions are read as numbers.

The finite-dimensionality assumption in the algebraically closed case cannot be dropped:
finite-dimensional vector spaces over the rational function field `k(t)`, viewed as a `k`-linear
category, have a simple unit whose endomorphism algebra is `k(t)`.

## Main declarations

* `TauCeti.endAlgEquivOfSurjective`: the isomorphism `End X ≃ₐ[k] k` whenever `End X` is
  nontrivial and `algebraMap k (End X)` is surjective, with
  `TauCeti.endAlgEquivOfSurjective_smul_id` and `TauCeti.endAlgEquivOfSurjective_apply_eq_iff`;
* `TauCeti.endAlgEquivOfSimple`: the algebraically closed simple specialization `End X ≃ₐ[k] k`,
  whose inverse is `algebraMap k (End X)` by `TauCeti.endAlgEquivOfSimple_symm_apply` and
  `TauCeti.algebraMap_endAlgEquivOfSimple`;
* `TauCeti.endAlgEquivOfSimple_smul_id`: every endomorphism `f` is `endAlgEquivOfSimple k X f`
  times the identity, and `TauCeti.endAlgEquivOfSimple_apply_eq_iff` characterizes the scalar;
* `CategoryTheory.End.of_id`, `CategoryTheory.End.of_comp`, … of
  `TauCeti.CategoryTheory.Linear.Endomorphism` are `simp` lemmas pushing `End.of` inside
  expressions built from morphisms `f : X ⟶ X`, after which `map_mul`, `map_add`, … let `simp`
  compute scalars of composites, sums and multiples;
* `TauCeti.homPairing`: the composition pairing `(S ⟶ X) × (X ⟶ S) → k` of a simple object `S`,
  with `f ≫ g = homPairing k S X f g • 𝟙 S` by `TauCeti.homPairing_smul_id`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor categories*][egno15], for Schur's lemma
-/

public section

open CategoryTheory CategoryTheory.Limits

universe w v u

namespace TauCeti

section Surjective

variable (k : Type w) [Field k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C]

/-- If the structure map `k → End X` of a nontrivial endomorphism algebra over a field `k` is
surjective, it is bijective. -/
theorem bijective_algebraMap_end_of_surjective (X : C) [Nontrivial (End X)]
    (hsurj : Function.Surjective (algebraMap k (End X))) :
    Function.Bijective (algebraMap k (End X)) :=
  ⟨(algebraMap k (End X)).injective, hsurj⟩

/-- Packaging scalar endomorphisms as an algebra isomorphism: if `End X` is nontrivial and
`algebraMap k (End X)` is surjective, then `End X` is isomorphic as a `k`-algebra to `k`. -/
noncomputable def endAlgEquivOfSurjective (X : C) [Nontrivial (End X)]
    (hsurj : Function.Surjective (algebraMap k (End X))) : End X ≃ₐ[k] k :=
  (AlgEquiv.ofBijective (Algebra.ofId k (End X)) <| by
    rw [show ⇑(Algebra.ofId k (End X)) = algebraMap k (End X) from funext (Algebra.ofId_apply _)]
    exact bijective_algebraMap_end_of_surjective k X hsurj).symm

variable {k}
variable {X : C} [Nontrivial (End X)] {hsurj : Function.Surjective (algebraMap k (End X))}

/-- The inverse of `endAlgEquivOfSurjective` is the structure map `algebraMap k (End X)`. -/
@[simp]
theorem endAlgEquivOfSurjective_symm_apply (c : k) :
    (endAlgEquivOfSurjective k X hsurj).symm c = algebraMap k (End X) c := by
  rw [endAlgEquivOfSurjective, AlgEquiv.symm_symm, AlgEquiv.ofBijective_apply, Algebra.ofId_apply]

/-- The structure map `algebraMap k (End X)` sends the scalar of an endomorphism `f` back to
`f`. -/
theorem algebraMap_endAlgEquivOfSurjective (f : End X) :
    algebraMap k (End X) (endAlgEquivOfSurjective k X hsurj f) = f := by
  rw [← endAlgEquivOfSurjective_symm_apply (hsurj := hsurj), AlgEquiv.symm_apply_apply]

/-- Every endomorphism of an object with scalar endomorphisms is its scalar times the identity. -/
@[simp]
theorem endAlgEquivOfSurjective_smul_id (f : End X) :
    endAlgEquivOfSurjective k X hsurj f • 𝟙 X = f.asHom := by
  rw [← End.algebraMap_asHom, algebraMap_endAlgEquivOfSurjective]

/-- The scalar of an endomorphism `f` is the unique `c` with `f = c • 𝟙 X`. -/
theorem endAlgEquivOfSurjective_apply_eq_iff (f : End X) (c : k) :
    endAlgEquivOfSurjective k X hsurj f = c ↔ f.asHom = c • 𝟙 X := by
  rw [← AlgEquiv.eq_symm_apply, End.ext_iff, endAlgEquivOfSurjective_symm_apply,
    End.algebraMap_asHom]

end Surjective

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [HasKernels C]

/-- The structure map `k → End X` of a simple object `X` with finite-dimensional endomorphisms
over an algebraically closed field is bijective: this is Schur's lemma. -/
theorem bijective_algebraMap_end_of_simple (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)] :
    Function.Bijective (algebraMap k (End X)) :=
  bijective_algebraMap_end_of_surjective k X fun f ↦ by
    obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k f.asHom
    exact ⟨c, End.ext (by simpa [Algebra.algebraMap_eq_smul_one] using hc)⟩

/-- **Schur's lemma** as an identification of algebras: the endomorphisms of a simple object `X`
with finite-dimensional endomorphisms over an algebraically closed field `k` are the scalars
`k`. This is the inverse of the structure map `algebraMap k (End X)`, `c ↦ c • 𝟙 X`. -/
noncomputable def endAlgEquivOfSimple (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)] :
    End X ≃ₐ[k] k :=
  endAlgEquivOfSurjective k X (bijective_algebraMap_end_of_simple k X).surjective

section Scalar

variable {k}
variable {X : C} [Simple X] [FiniteDimensional k (X ⟶ X)]

/-- The inverse of `endAlgEquivOfSimple` is the structure map `algebraMap k (End X)`. -/
@[simp]
theorem endAlgEquivOfSimple_symm_apply (c : k) :
    (endAlgEquivOfSimple k X).symm c = algebraMap k (End X) c :=
  endAlgEquivOfSurjective_symm_apply c

/-- The structure map `algebraMap k (End X)` sends the scalar of an endomorphism `f` back to
`f`. -/
theorem algebraMap_endAlgEquivOfSimple (f : End X) :
    algebraMap k (End X) (endAlgEquivOfSimple k X f) = f :=
  algebraMap_endAlgEquivOfSurjective f

/-- Every endomorphism of a simple object is its scalar times the identity. -/
@[simp]
theorem endAlgEquivOfSimple_smul_id (f : End X) : endAlgEquivOfSimple k X f • 𝟙 X = f.asHom :=
  endAlgEquivOfSurjective_smul_id f

/-- The scalar of an endomorphism `f` is the unique `c` with `f = c • 𝟙 X`. -/
theorem endAlgEquivOfSimple_apply_eq_iff (f : End X) (c : k) :
    endAlgEquivOfSimple k X f = c ↔ f.asHom = c • 𝟙 X :=
  endAlgEquivOfSurjective_apply_eq_iff f c

end Scalar

section Pairing

/-- The composition pairing between morphisms out of and into a simple object `S`: the scalar
`homPairing k S X f g` is the one with `f ≫ g = homPairing k S X f g • 𝟙 S`, which exists by
Schur's lemma. -/
noncomputable def homPairing (S X : C) [Simple S] [FiniteDimensional k (S ⟶ S)] :
    (S ⟶ X) →ₗ[k] (X ⟶ S) →ₗ[k] k :=
  LinearMap.mk₂ k (fun f g ↦ endAlgEquivOfSimple k S (End.of (f ≫ g)))
    (fun f f' g ↦ by simp) (fun c f g ↦ by simp) (fun f g g' ↦ by simp) (fun c f g ↦ by simp)

variable {k} {S X : C} [Simple S] [FiniteDimensional k (S ⟶ S)]

/-- The composition pairing is the scalar of the composite given by Schur's lemma. -/
theorem homPairing_apply (f : S ⟶ X) (g : X ⟶ S) :
    homPairing k S X f g = endAlgEquivOfSimple k S (End.of (f ≫ g)) := (rfl)

/-- The composite of a morphism out of a simple object with a morphism back is the scalar given
by the composition pairing. -/
@[simp]
theorem homPairing_smul_id (f : S ⟶ X) (g : X ⟶ S) : homPairing k S X f g • 𝟙 S = f ≫ g :=
  endAlgEquivOfSimple_smul_id (End.of (f ≫ g))

/-- The composition pairing takes the value `c` exactly when the composite is `c • 𝟙 S`. -/
theorem homPairing_eq_iff (f : S ⟶ X) (g : X ⟶ S) (c : k) :
    homPairing k S X f g = c ↔ f ≫ g = c • 𝟙 S :=
  endAlgEquivOfSimple_apply_eq_iff (End.of (f ≫ g)) c

/-- A morphism between the two objects can be moved across the composition pairing. -/
theorem homPairing_comp (f : S ⟶ X) {Y : C} (h : X ⟶ Y) (g : Y ⟶ S) :
    homPairing k S Y (f ≫ h) g = homPairing k S X f (h ≫ g) := by
  rw [homPairing_apply, homPairing_apply, Category.assoc]

end Pairing

end TauCeti
