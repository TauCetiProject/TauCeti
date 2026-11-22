/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Schur
public import TauCeti.CategoryTheory.Linear.Endomorphism
public import TauCeti.CategoryTheory.Simple.ScalarEndomorphism

/-!
# Endomorphisms of a simple object are scalars

Let `k` be an algebraically closed field and `X` a simple object of a `k`-linear preadditive
category with kernels, whose endomorphisms form a finite-dimensional `k`-vector space. Schur's
lemma (`CategoryTheory.endomorphism_simple_eq_smul_id`) says that every endomorphism of `X` is a
scalar multiple `c • 𝟙 X` of the identity. We package this as a `k`-algebra isomorphism
`TauCeti.endAlgEquivOfSimple k X : End X ≃ₐ[k] k`, the inverse of `algebraMap k (End X)`, which
sends `c` to `c • 𝟙 X` (specializing `TauCeti.endAlgEquivOfSurjective` from
`TauCeti.CategoryTheory.Linear.Endomorphism`). We also provide the typeclass
`TauCeti.HasScalarSimpleEnd` recording that every simple object has scalar endomorphisms, with an
instance derived from Schur's lemma.

Applied to a simple monoidal unit, this identifies the scalars `𝟙_ C ⟶ 𝟙_ C` of a fusion
category with elements of `k`, which is how traces and dimensions are read as numbers.

The finite-dimensionality assumption in the algebraically closed case cannot be dropped:
finite-dimensional vector spaces over the rational function field `k(t)`, viewed as a `k`-linear
category, have a simple unit whose endomorphism algebra is `k(t)`.

## Main declarations

* `TauCeti.endAlgEquivOfSimple`: the algebraically closed simple specialization `End X ≃ₐ[k] k`,
  whose inverse is `algebraMap k (End X)` by `TauCeti.endAlgEquivOfSimple_symm_apply` and
  `TauCeti.algebraMap_endAlgEquivOfSimple`;
* `TauCeti.endAlgEquivOfSimple_smul_id`: every endomorphism `f` is `endAlgEquivOfSimple k X f`
  times the identity, and `TauCeti.endAlgEquivOfSimple_apply_eq_iff` characterizes the scalar;
* `TauCeti.HasScalarSimpleEnd`: typeclass asserting that `algebraMap k (End X)` is surjective for
  every simple object `X`, instantiated automatically over algebraically closed fields when simple
  endomorphism spaces are finite-dimensional;
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

variable (k : Type w) [Field k] [IsAlgClosed k]
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear k C] [HasKernels C]

/-- The structure map `k → End X` of a simple object `X` with finite-dimensional endomorphisms
over an algebraically closed field is bijective: this is Schur's lemma. -/
theorem bijective_algebraMap_end_of_simple (X : C) [Simple X] [FiniteDimensional k (X ⟶ X)] :
    Function.Bijective (algebraMap k (End X)) :=
  bijective_algebraMap_end_of_surjective k X fun f ↦ by
    obtain ⟨c, hc⟩ := endomorphism_simple_eq_smul_id k f.asHom
    exact ⟨c, End.ext (by simpa [Algebra.algebraMap_eq_smul_one] using hc)⟩

/-- Over an algebraically closed field, a category whose endomorphism spaces are
finite-dimensional has scalar simple endomorphisms (Schur's lemma). -/
instance instHasScalarSimpleEnd [∀ X : C, FiniteDimensional k (X ⟶ X)] :
    HasScalarSimpleEnd k C where
  surjective_algebraMap X := (bijective_algebraMap_end_of_simple k X).surjective

/-- Over an algebraically closed field, if every simple object has finite-dimensional endomorphisms,
the category has scalar simple endomorphisms (Schur's lemma). -/
theorem HasScalarSimpleEnd.of_simple
    (hfin : ∀ (X : C) [Simple X], FiniteDimensional k (X ⟶ X)) :
    HasScalarSimpleEnd k C where
  surjective_algebraMap X :=
    let := hfin X
    (bijective_algebraMap_end_of_simple k X).surjective

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
@[simp]
theorem algebraMap_endAlgEquivOfSimple (f : End X) :
    algebraMap k (End X) (endAlgEquivOfSimple k X f) = f :=
  algebraMap_endAlgEquivOfSurjective f

/-- Evaluating `endAlgEquivOfSimple` on `algebraMap k (End X) c` recovers `c`. -/
theorem endAlgEquivOfSimple_algebraMap (c : k) :
    endAlgEquivOfSimple k X (algebraMap k (End X) c) = c := by simp

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
