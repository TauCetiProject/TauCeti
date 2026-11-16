/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import TauCeti.Algebra.Homology.LinearYoneda

/-!
# Chain maps from K-projective complexes

A morphism in the derived category from a K-projective complex can be represented by a
chain map. This is the chain-level form of Mathlib's
`CochainComplex.IsKProjective.Qh_map_bijective`, and lets one form mapping cones of derived
morphisms using specified projective models.

A quasi-isomorphism between `ℕ`-graded chain complexes of projective objects is a chain homotopy
equivalence (Mathlib's `ChainComplex.quasiIso_iff_of_projective`). So the contravariant functor
`Hom(-, Y)` takes it to a cochain homotopy equivalence, and in particular to a quasi-isomorphism
(`ChainComplex.homotopyEquivalences_linearYonedaFunctor_map_of_projective`,
`ChainComplex.quasiIso_linearYonedaFunctor_map_of_projective`). This is how a map of spaces
inducing isomorphisms on homology with projective chain coefficients is seen to induce
isomorphisms on cohomology with values in every coefficient object.
-/

public section

open CategoryTheory DerivedCategory

namespace CochainComplex.IsKProjective

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- Every derived morphism from a K-projective complex is represented by a chain map. -/
theorem Q_map_surjective (K L : CochainComplex C ℤ) [K.IsKProjective] :
    Function.Surjective (Q.map : (K ⟶ L) → (Q.obj K ⟶ Q.obj L)) := by
  intro f
  obtain ⟨g, hg⟩ := (Qh_map_bijective K ((HomotopyCategory.quotient _ _).obj L)).surjective
    ((quotientCompQhIso C).hom.app K ≫ f ≫ (quotientCompQhIso C).inv.app L)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨g, ?_⟩
  rw [← cancel_epi ((quotientCompQhIso C).hom.app K),
    ← quotientCompQhIso_hom_naturality, hg]
  simp

end CochainComplex.IsKProjective

namespace ChainComplex

open HomologicalComplex

variable {C : Type*} [Category* C] [Abelian C] {K L : ChainComplex C ℕ}
  [∀ n, Projective (K.X n)] [∀ n, Projective (L.X n)]

/-- A quasi-isomorphism `φ : K ⟶ L` of `ℕ`-graded chain complexes of projective objects induces a
cochain homotopy equivalence `Hom(L, Y) ⟶ Hom(K, Y)` by precomposition, for every object `Y`. -/
theorem homotopyEquivalences_linearYonedaFunctor_map_of_projective (φ : K ⟶ L) [QuasiIso φ]
    (k : Type*) [Ring k] [Linear k C] (Y : C) :
    homotopyEquivalences _ _ ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) := by
  obtain ⟨e, he⟩ := (quasiIso_iff_of_projective φ).1 ‹_›
  exact ⟨e.linearYonedaFunctorMap k Y, by rw [HomotopyEquiv.linearYonedaFunctorMap_hom, he]⟩

/-- A quasi-isomorphism `φ : K ⟶ L` of `ℕ`-graded chain complexes of projective objects induces a
quasi-isomorphism `Hom(L, Y) ⟶ Hom(K, Y)` by precomposition, for every object `Y`. -/
theorem quasiIso_linearYonedaFunctor_map_of_projective (φ : K ⟶ L) [QuasiIso φ]
    (k : Type*) [Ring k] [Linear k C] (Y : C) :
    QuasiIso ((TauCeti.ChainComplex.linearYonedaFunctor k Y).map φ.op) :=
  homotopyEquivalences_le_quasiIso _ _ _
    (homotopyEquivalences_linearYonedaFunctor_map_of_projective φ k Y)

end ChainComplex
