/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.ModCat.Flat.Basic
public import TauCeti.CategoryTheory.Preadditive.ModCat.Purity
import TauCeti.CategoryTheory.Preadditive.ModCat.Flat.Factorization

/-!
# Purity and flatness of modules over preadditive categories

Every epimorphism onto a flat module is pure, and a pure quotient of a flat module is flat.
The proofs use the finite-free factorization criterion. See B. Stenström,
*Purity in functor categories*, §2, Lemma 8, for the flatness criterion.
-/

public section

universe v u

open CategoryTheory

namespace TauCeti.ModCat

variable {C : Type u} [Category.{v} C] [Preadditive C]
variable {L M : ModCat.{v} C}

/-- Every epimorphism onto a flat module is pure. -/
theorem Flat.isPureEpi [M.Flat] (p : L ⟶ M) [Epi p] : IsPureEpi p where
  lift {_} hP f := by
    obtain ⟨Q, hQ, a, b, hab⟩ := Flat.exists_factorization_of_isFinitelyPresentedFunctor hP f
    have := projective_of_isFiniteFree hQ
    obtain ⟨b', hb'⟩ := Projective.factors b p
    exact ⟨a ≫ b', by simp [hb', hab]⟩

/-- A pure quotient of a flat module is flat. -/
theorem IsPureEpi.flat {p : L ⟶ M} (hp : IsPureEpi p) [L.Flat] : M.Flat := by
  apply flat_iff_forall_exists_factorization.mpr
  intro P hP f
  obtain ⟨g, hg⟩ := hp.lift hP f
  obtain ⟨Q, hQ, a, b, hab⟩ := Flat.exists_factorization_of_isFinitelyPresentedFunctor hP g
  exact ⟨Q, hQ, a, b ≫ p, by simp [← Category.assoc, hab, hg]⟩

end TauCeti.ModCat
