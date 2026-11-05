/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.ObjectProperty.Orthogonal
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Orthogonals of shift closures

In a preadditive category with a shift by `ℤ`, the condition that every map from `X` to every
shift `Y⟦n⟧` vanishes describes the left orthogonal of the shifts of `Y`
(`CategoryTheory.ObjectProperty.leftOrthogonal_shiftClosure_singleton_iff`). Symmetrically, the
right orthogonal of the shifts of the objects satisfying `P` consists of the `Y` such that every
map from such an object to every shift of `Y` vanishes
(`CategoryTheory.ObjectProperty.rightOrthogonal_shiftClosure_iff`). In a pretriangulated category
both are triangulated subcategories, by Mathlib's `CategoryTheory.Triangulated.Orthogonal`, and in
a derived category they express the vanishing of derived `Hom` complexes, since `Hom(X, Y⟦n⟧)` is
the `n`-th cohomology of `RHom(X, Y)`.

Both descriptions rest on `CategoryTheory.forall_shift_hom_eq_zero_iff`: every map `X⟦a⟧ ⟶ Y`
vanishes if and only if every map `X ⟶ Y⟦b⟧` does, where `a + b = 0`.
-/

public section

namespace CategoryTheory

variable {D : Type*} [Category* D] [HasShift D ℤ] [Preadditive D]

/-- Every map `X⟦a⟧ ⟶ Y` vanishes if and only if every map `X ⟶ Y⟦b⟧` does, where `a + b = 0`. -/
lemma forall_shift_hom_eq_zero_iff [∀ n : ℤ, (shiftFunctor D n).Additive] (X Y : D) {a b : ℤ}
    (h : a + b = 0) : (∀ φ : X⟦a⟧ ⟶ Y, φ = 0) ↔ ∀ φ : X ⟶ Y⟦b⟧, φ = 0 := by
  let e : Y⟦b⟧⟦a⟧ ≅ Y := (shiftFunctorCompIsoId D b a (by omega)).app Y
  constructor
  · intro H ψ
    apply (shiftFunctor D a).map_injective
    rw [Functor.map_zero, ← cancel_mono e.hom, Limits.zero_comp]
    exact H _
  · intro H φ
    obtain ⟨ψ, hψ⟩ := (shiftFunctor D a).map_surjective (φ ≫ e.inv)
    rw [← cancel_mono e.inv, Limits.zero_comp, ← hψ, H ψ, Functor.map_zero]

namespace ObjectProperty

/-- An object lies in the left orthogonal of the shifts of `Y` if and only if every map from it to
every shift of `Y` vanishes. -/
lemma leftOrthogonal_shiftClosure_singleton_iff (X Y : D) :
    ((singleton Y).shiftClosure ℤ).leftOrthogonal X ↔ ∀ (n : ℤ) (φ : X ⟶ Y⟦n⟧), φ = 0 := by
  refine ⟨fun h n φ ↦ h φ ⟨Y, n, Iso.refl _, by simp⟩, ?_⟩
  rintro h Z φ ⟨_, n, e, ⟨⟩⟩
  rw [← cancel_mono e.hom, Limits.zero_comp]
  exact h n _

/-- An object lies in the right orthogonal of the shifts of the objects satisfying `P` if and only
if every map from such an object to every shift of it vanishes. -/
lemma rightOrthogonal_shiftClosure_iff [∀ n : ℤ, (shiftFunctor D n).Additive]
    (P : ObjectProperty D) (Y : D) :
    (P.shiftClosure ℤ).rightOrthogonal Y ↔ ∀ X, P X → ∀ (n : ℤ) (φ : X ⟶ Y⟦n⟧), φ = 0 := by
  refine ⟨fun h X hX n ↦ (forall_shift_hom_eq_zero_iff X Y (neg_add_cancel n)).1
    fun ψ ↦ h ψ ⟨X, -n, Iso.refl _, hX⟩, ?_⟩
  rintro h Z φ ⟨X, a, e, hX⟩
  rw [← cancel_epi e.inv, Limits.comp_zero]
  exact (forall_shift_hom_eq_zero_iff X Y (add_neg_cancel a)).2 (h X hX (-a)) _

end ObjectProperty

end CategoryTheory
