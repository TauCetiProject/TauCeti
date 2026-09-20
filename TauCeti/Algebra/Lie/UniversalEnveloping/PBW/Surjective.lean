/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Quotient
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Functoriality
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Ordered

/-!
# PBW filtrations under surjective Lie maps

A surjective homomorphism of Lie algebras sends every word in the target generators to the image
of a word of the same length in the source generators. Consequently the induced homomorphism of
universal enveloping algebras maps each PBW filtration step *onto* the corresponding target step.
This strengthens the filtration-preserving inclusion to the equality needed for quotients.

The ordered-monomial API is compatible with arbitrary Lie maps: applying the induced enveloping
map to an ordered monomial applies the Lie map to each of its factors, and hence maps the span of
the source monomials exactly onto the span of the corresponding target monomials. Together these
facts let quotient arguments retain both the degree bound and the chosen monomial normalization.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.map_pbwFiltration_eq_of_surjective`: a surjective Lie map
  maps every PBW filtration step onto the target step.
* `TauCeti.UniversalEnvelopingAlgebra.mapFiltration_surjective_of_surjective`: the induced linear
  map between filtration steps is surjective.
* `TauCeti.UniversalEnvelopingAlgebra.map_pbwMonomial`: induced maps act factorwise on PBW
  monomials.
* `TauCeti.UniversalEnvelopingAlgebra.map_span_orderedPBWMonomials`: the corresponding ordered
  monomial spans map exactly onto one another.
* `TauCeti.UniversalEnvelopingAlgebra.map_mkQ_pbwFiltration`: specialization to a quotient by a
  Lie ideal.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Chapter V, §17.
* N. Bourbaki, *Lie Groups and Lie Algebras*, Chapter I, §2.7.
-/

public section

namespace TauCeti.UniversalEnvelopingAlgebra

open TauCeti.Algebra

universe u v w x

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
  intro y
  have heq := map_pbwFiltration_eq_of_surjective R f hf k
  have hy : (y : _root_.UniversalEnvelopingAlgebra R M) ∈
      (pbwFiltration R L k).map (map R f).toLinearMap := heq.symm ▸ y.property
  obtain ⟨x, hx, hxy⟩ := hy
  refine ⟨⟨x, hx⟩, ?_⟩
  apply Subtype.ext
  simpa only [mapFiltration_apply, AlgHom.toLinearMap_apply] using hxy

variable {ι : Type x}

/-- An induced enveloping-algebra map applies the Lie homomorphism to every factor of a PBW
monomial. -/
@[simp]
theorem map_pbwMonomial (f : LieHom R L M) (e : ι → L) (word : List ι) :
    map R f (pbwMonomial R L e word) = pbwMonomial R M (fun i ↦ f (e i)) word := by
  rw [pbwMonomial_def, pbwMonomial_def, map_list_prod]
  apply congrArg List.prod
  simp only [List.map_map]
  apply List.map_congr_left
  intro i _
  exact map_ι R f (e i)

variable [LE ι]

/-- An induced enveloping-algebra map sends the ordered monomials in a family exactly to the
ordered monomials in its image family. This statement does not require the Lie map or the family
to be surjective. -/
theorem image_orderedPBWMonomials (f : LieHom R L M) (e : ι → L) (k : ℕ) :
    (map R f).toLinearMap '' orderedPBWMonomials R L e k =
      orderedPBWMonomials R M (fun i ↦ f (e i)) k := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    rw [mem_orderedPBWMonomials_iff] at hb ⊢
    obtain ⟨word, hordered, hlength, rfl⟩ := hb
    exact ⟨word, hordered, hlength, (map_pbwMonomial R f e word).symm⟩
  · rw [mem_orderedPBWMonomials_iff]
    rintro ⟨word, hordered, hlength, rfl⟩
    have hsource : pbwMonomial R L e word ∈ orderedPBWMonomials R L e k :=
      (mem_orderedPBWMonomials_iff R L e).2 ⟨word, hordered, hlength, rfl⟩
    exact ⟨pbwMonomial R L e word, hsource, map_pbwMonomial R f e word⟩

/-- The induced enveloping-algebra map carries the span of the ordered monomials in a family
onto the span of the corresponding ordered monomials in its image family. -/
theorem map_span_orderedPBWMonomials (f : LieHom R L M) (e : ι → L) (k : ℕ) :
    (Submodule.span R (orderedPBWMonomials R L e k)).map (map R f).toLinearMap =
      Submodule.span R (orderedPBWMonomials R M (fun i ↦ f (e i)) k) := by
  rw [Submodule.map_span, image_orderedPBWMonomials R f e k]

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
