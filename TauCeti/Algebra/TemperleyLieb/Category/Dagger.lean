/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.TemperleyLieb.Category.Symmetry
public import TauCeti.CategoryTheory.Dagger.Basic

/-!
# The vertical reflection dagger on the linear Temperley–Lieb category

* `TauCeti.TLCat.instDaggerCategory` and `TauCeti.TLCat.instDaggerPreadditive` give the additive
  vertical reflection dagger. The instances on Mathlib's `CategoryTheory.End` then make each
  endomorphism algebra a star ring.

The dagger uses `TauCeti.TLCat.verticalReflectHom`, which fixes the coefficients and
reverses composition by `TauCeti.TLCat.verticalReflectHom_comp`.

## References

* J. Chen, *The Temperley–Lieb categories and skein modules*, arXiv:1502.06845,
  Definition 2.1.5 for the underlying reflection of diagrams.
-/

public section

open CategoryTheory

namespace TauCeti.TLCat

variable {R : Type*} [CommRing R] {δ : R}

/-- Turning diagrams upside down is an identity-on-objects contravariant involution. -/
noncomputable instance instDaggerCategory : DaggerCategory (TLCat R δ) where
  dagger := fun {X Y} => verticalReflectHom X.as Y.as
  dagger_id X := verticalReflectHom_id X.as
  dagger_comp f g := verticalReflectHom_comp f g
  dagger_dagger f := verticalReflectHom_verticalReflectHom _ _ f

/-- Simplify the dagger to linear vertical reflection so the diagram-basis and linear-map
simp lemmas apply. -/
@[simp]
theorem dagger_eq_verticalReflectHom {n m : ℕ} (f : (of n : TLCat R δ) ⟶ of m) :
    dagger f = verticalReflectHom n m f := (rfl)

/-- Vertical reflection is additive, so composition and the dagger give a star ring on each
endomorphism algebra. -/
instance instDaggerPreadditive : DaggerPreadditive (TLCat R δ) where
  dagger_add {X Y} f g := (verticalReflectHom X.as Y.as).map_add f g

/-- Vertical reflection leaves scalars unchanged. -/
theorem dagger_smul_eq_smul_dagger {X Y : TLCat R δ} (r : R) (f : X ⟶ Y) :
    dagger (r • f) = r • dagger f :=
  (verticalReflectHom X.as Y.as).map_smul r f

/-- With trivial scalar star, vertical reflection is compatible with the scalar involution. -/
instance instDaggerLinear [Star R] [TrivialStar R] : DaggerLinear R (TLCat R δ) where
  dagger_smul r f := by rw [star_trivial, dagger_smul_eq_smul_dagger]

/-- The diagram algebra star commutes with multiplication by any coefficient. -/
@[simp]
theorem star_smul_end (X : TLCat R δ) (r : R) (x : End X) :
    star (r • x) = r • star x := by
  ext
  simp only [End.star_asHom, End.smul_asHom, dagger_smul_eq_smul_dagger]

end TauCeti.TLCat
