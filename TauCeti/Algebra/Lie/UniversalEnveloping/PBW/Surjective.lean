/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Quotient
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Ordered

/-!
# PBW filtrations under surjective Lie maps

A surjective homomorphism of Lie algebras sends every word in the target generators to the image
of a word of the same length in the source generators. Consequently the induced homomorphism of
universal enveloping algebras maps each PBW filtration step *onto* the corresponding target step.
This strengthens the filtration-preserving inclusion to the equality needed for quotients.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_eq_of_surjective`: a surjective Lie map
  maps every PBW filtration step onto the target step.
* `TauCeti.UniversalEnvelopingAlgebra.mapFiltration_surjective_of_surjective`: the induced linear
  map between filtration steps is surjective.
* `TauCeti.UniversalEnvelopingAlgebra.map_mkQ_pbwFiltration`: specialization to a quotient by a
  Lie ideal.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.Algebra

universe u v w

variable (R : Type u) [CommRing R]
variable {L : Type v} {M : Type w}
variable [LieRing L] [LieAlgebra R L]
variable [LieRing M] [LieAlgebra R M]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- A surjective Lie homomorphism maps each PBW filtration step onto the corresponding target
step. Surjectivity is needed only on the Lie generators; the generic word-filtration theorem then
lifts target words without requiring a Lie-homomorphic section. -/
theorem map_pbwFiltration_eq_of_surjective (f : LieHom R L M) (hf : Function.Surjective f)
    (k : ℕ) :
    (pbwFiltration R L k).map (map R f).toLinearMap = pbwFiltration R M k := by
  rw [pbwFiltration_def, pbwFiltration_def]
  apply map_wordFiltration_eq_of_surjective
    (_root_.UniversalEnvelopingAlgebra.ι R : LieHom R L _).toLinearMap
    f.toLinearMap hf (map R f)
    (_root_.UniversalEnvelopingAlgebra.ι R : LieHom R M _).toLinearMap _ k
  ext x
  exact map_ι R f x

/-- A surjective Lie homomorphism also maps the step immediately preceding each PBW degree onto
the corresponding preceding step. -/
theorem map_pbwFiltrationPrevious_eq_of_surjective (f : LieHom R L M)
    (hf : Function.Surjective f) (k : ℕ) :
    (pbwFiltrationPrevious R L k).map (map R f).toLinearMap =
      pbwFiltrationPrevious R M k := by
  cases k with
  | zero => simp
  | succ k => simpa using map_pbwFiltration_eq_of_surjective R f hf k

/-- The map between corresponding PBW filtration steps induced by a surjective Lie homomorphism
is surjective. -/
theorem mapFiltration_surjective_of_surjective (f : LieHom R L M)
    (hf : Function.Surjective f) (k : ℕ) :
    Function.Surjective (mapFiltration R f k) := by
  let hmaps : Set.MapsTo (map R f) (pbwFiltration R L k) (pbwFiltration R M k) :=
    fun _ hx ↦ map_mem_pbwFiltration R f hx
  have hrestrict : (mapFiltration R f k : pbwFiltration R L k → pbwFiltration R M k) =
      hmaps.restrict (map R f) (pbwFiltration R L k) (pbwFiltration R M k) := by
    funext x
    apply Subtype.ext
    exact mapFiltration_apply R f k x
  rw [hrestrict, hmaps.restrict_surjective_iff]
  exact Submodule.surjOn_iff_le_map.mpr
    (map_pbwFiltration_eq_of_surjective R f hf k).ge

section Quotient

variable (I : LieIdeal R L)

/-- The enveloping-algebra map induced by a Lie quotient maps each PBW filtration step onto the
corresponding filtration step of the quotient enveloping algebra. -/
@[simp]
theorem map_mkQ_pbwFiltration (k : ℕ) :
    (pbwFiltration R L k).map (map R I.mkQ).toLinearMap =
      pbwFiltration R (L ⧸ I) k :=
  map_pbwFiltration_eq_of_surjective R I.mkQ I.mkQ_surjective k

/-- The linear map on each PBW filtration step induced by a Lie quotient is surjective. -/
theorem mapFiltration_mkQ_surjective (k : ℕ) :
    Function.Surjective (mapFiltration R I.mkQ k) :=
  mapFiltration_surjective_of_surjective R I.mkQ I.mkQ_surjective k

end Quotient

end TauCeti.UniversalEnvelopingAlgebra
