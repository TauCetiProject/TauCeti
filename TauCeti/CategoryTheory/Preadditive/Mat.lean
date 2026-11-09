/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.Mat

/-!
# Monomial isomorphisms in the matrix category

An object of `Mat_ C` is a finite family `M.X : M.ι → C` of objects of a preadditive category
`C`, and a morphism is a matrix of morphisms of `C`. Given an equivalence `e : M.ι ≃ N.ι` of index
types and isomorphisms `φ i : M.X i ≅ N.X (e i)`, the matrix whose only nonzero entries are the
`φ i`, placed at the positions `(i, e i)`, is an isomorphism `M ≅ N`: a *monomial* matrix, the
categorical form of a permutation matrix with invertible entries. These isomorphisms relabel the
summands of an object, and they compose and invert like their index equivalences.

The structure isomorphisms of the monoidal structure on `Mat_ C`
(`CategoryTheory.Mat_.instMonoidalCategory`) are monomial: the associator lies over
`Equiv.prodAssoc` and the unitors over `Equiv.punitProd` and `Equiv.prodPUnit`.

Composing a matrix with a monomial isomorphism on the side where the equivalence is applied only
permutes and rescales its entries: `Mat_.isoOfEquiv_hom_comp_apply` and
`Mat_.comp_isoOfEquiv_inv_apply` compute these composites without any `eqToHom`.

## Main declarations

* `CategoryTheory.Mat_.isoOfEquiv e φ`: the monomial isomorphism `M ≅ N` determined by
  `e : M.ι ≃ N.ι` and `φ i : M.X i ≅ N.X (e i)`.
* `CategoryTheory.Mat_.isoOfEquiv_refl`, `CategoryTheory.Mat_.isoOfEquiv_trans`,
  `CategoryTheory.Mat_.isoOfEquiv_symm`: monomial isomorphisms over the identity, a composite and
  an inverse equivalence.

The file also records the entries of the zero matrix (`Mat_.zero_apply`) and of the one-by-one
matrices `(Mat_.embedding C).map f` (`Mat_.embedding_map_apply`), with the indices typed as those of
the one-term families `(Mat_.embedding C).obj X`, whose index types are singletons.
-/

public section

open CategoryTheory

noncomputable section

namespace CategoryTheory.Mat_

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]

@[simp]
theorem zero_apply {M N : Mat_ C} (i : M.ι) (j : N.ι) : (0 : M ⟶ N) i j = 0 := rfl

/-- A one-term family is indexed by a singleton. -/
instance (X : C) : Unique ((embedding C).obj X).ι := inferInstanceAs (Unique PUnit)

/-- The entry of a one-by-one matrix, with the indices typed as those of the one-term families.
Mathlib's `Mat_.embedding_map` types the indices by the unfolded structure instead, so `simp` does
not apply it to indices of type `((embedding C).obj X).ι`. -/
@[simp]
theorem embedding_map_apply {X Y : C} (f : X ⟶ Y) (i : ((embedding C).obj X).ι)
    (j : ((embedding C).obj Y).ι) : (embedding C).map f i j = f :=
  rfl

open scoped Classical in
/-- The matrix of `Mat_.isoOfEquiv e φ`. -/
private def homOfEquiv {M N : Mat_ C} (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) : M ⟶ N :=
  fun i j ↦ if h : e i = j then (φ i).hom ≫ eqToHom (congrArg N.X h) else 0

open scoped Classical in
/-- The matrix of the inverse of `Mat_.isoOfEquiv e φ`. -/
private def invOfEquiv {M N : Mat_ C} (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) : N ⟶ M :=
  fun j i ↦ if h : e i = j then eqToHom (congrArg N.X h.symm) ≫ (φ i).inv else 0

/-- The **monomial isomorphism** `M ≅ N` determined by an equivalence `e : M.ι ≃ N.ι` of index types
and isomorphisms `φ i : M.X i ≅ N.X (e i)`: its matrix has the entry `φ i` at the position
`(i, e i)` and zeros elsewhere. -/
def isoOfEquiv {M N : Mat_ C} (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) : M ≅ N where
  hom := homOfEquiv e φ
  inv := invOfEquiv e φ
  hom_inv_id := by
    ext i i'
    rw [Mat_.comp_apply,
      Finset.sum_eq_single (e i) (fun j _ hj ↦ by simp [homOfEquiv, Ne.symm hj]) (by simp)]
    by_cases h : i = i'
    · subst h
      simp [homOfEquiv, invOfEquiv]
    · simp [homOfEquiv, invOfEquiv, h, Ne.symm h]
  inv_hom_id := by
    ext j j'
    rw [Mat_.comp_apply, Finset.sum_eq_single (e.symm j) (fun i _ hi ↦ by
      simp [invOfEquiv, show e i ≠ j from fun h ↦ hi (by simp [← h])]) (by simp)]
    by_cases h : j = j'
    · subst h
      simp [homOfEquiv, invOfEquiv]
    · simp [homOfEquiv, invOfEquiv, h]

variable {M N P : Mat_ C}

open scoped Classical in
theorem isoOfEquiv_hom_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (i : M.ι) (j : N.ι) :
    (isoOfEquiv e φ).hom i j = if h : e i = j then (φ i).hom ≫ eqToHom (congrArg N.X h) else 0 :=
  (rfl)

open scoped Classical in
theorem isoOfEquiv_inv_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (j : N.ι) (i : M.ι) :
    (isoOfEquiv e φ).inv j i =
      if h : e i = j then eqToHom (congrArg N.X h.symm) ≫ (φ i).inv else 0 :=
  (rfl)

@[simp]
theorem isoOfEquiv_hom_apply_self (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (i : M.ι) :
    (isoOfEquiv e φ).hom i (e i) = (φ i).hom := by
  simp [isoOfEquiv_hom_apply]

@[simp]
theorem isoOfEquiv_inv_apply_self (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (i : M.ι) :
    (isoOfEquiv e φ).inv (e i) i = (φ i).inv := by
  simp [isoOfEquiv_inv_apply]

/-- Precomposing with a monomial isomorphism moves the rows along the equivalence and multiplies
them by the entries. -/
theorem isoOfEquiv_hom_comp_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (g : N ⟶ P)
    (i : M.ι) (k : P.ι) : ((isoOfEquiv e φ).hom ≫ g) i k = (φ i).hom ≫ g (e i) k := by
  rw [comp_apply, Finset.sum_eq_single (e i)]
  · simp
  · intro j _ hj
    simp [isoOfEquiv_hom_apply, Ne.symm hj]
  · simp

/-- Postcomposing with the inverse of a monomial isomorphism moves the columns along the
equivalence and multiplies them by the inverse entries. -/
theorem comp_isoOfEquiv_inv_apply (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (f : P ⟶ N)
    (k : P.ι) (i : M.ι) : (f ≫ (isoOfEquiv e φ).inv) k i = f k (e i) ≫ (φ i).inv := by
  rw [comp_apply, Finset.sum_eq_single (e i)]
  · simp
  · intro j _ hj
    simp [isoOfEquiv_inv_apply, Ne.symm hj]
  · simp

/-- The monomial isomorphism over the identity equivalence with identity entries is the identity
isomorphism. -/
@[simp]
theorem isoOfEquiv_refl (M : Mat_ C) : isoOfEquiv (Equiv.refl M.ι) (fun _ ↦ Iso.refl _) =
    Iso.refl M := by
  ext i j
  rw [isoOfEquiv_hom_apply (Equiv.refl _) (fun _ ↦ Iso.refl _)]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-- Monomial isomorphisms compose along the composite equivalence, with composite entries. -/
theorem isoOfEquiv_trans (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) (e' : N.ι ≃ P.ι)
    (ψ : ∀ j, N.X j ≅ P.X (e' j)) :
    isoOfEquiv e φ ≪≫ isoOfEquiv e' ψ = isoOfEquiv (e.trans e') fun i ↦ φ i ≪≫ ψ (e i) := by
  ext i k
  rw [Iso.trans_hom, isoOfEquiv_hom_comp_apply, isoOfEquiv_hom_apply, isoOfEquiv_hom_apply]
  by_cases h : e' (e i) = k
  · subst h
    simp
  · simp [h]

/-- The inverse of a monomial isomorphism is monomial over the inverse equivalence. -/
theorem isoOfEquiv_symm (e : M.ι ≃ N.ι) (φ : ∀ i, M.X i ≅ N.X (e i)) :
    (isoOfEquiv e φ).symm =
      isoOfEquiv e.symm fun j ↦ eqToIso (congrArg N.X (e.apply_symm_apply j).symm) ≪≫
        (φ (e.symm j)).symm := by
  ext j i
  by_cases h : e i = j
  · subst h
    simp [isoOfEquiv_hom_apply, isoOfEquiv_inv_apply]
  · simp [isoOfEquiv_hom_apply, isoOfEquiv_inv_apply, h, e.symm_apply_eq, Ne.symm h]

end CategoryTheory.Mat_
