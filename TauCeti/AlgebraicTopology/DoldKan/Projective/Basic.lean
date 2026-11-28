/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.DoldKan.Equivalence
public import TauCeti.AlgebraicTopology.DoldKan.Retract
import TauCeti.CategoryTheory.Preadditive.Projective.Basic

/-!
# Projectivity across the Dold–Kan correspondence

In an idempotent-complete preadditive category with finite coproducts (and in an abelian
category), the Dold–Kan functors `Γ` and `N` preserve and reflect degreewise projectivity: a
simplicial object `X` is degreewise projective if and only if its normalized chain complex
`Idempotents.DoldKan.N.obj X` (or `normalizedMooreComplex A |>.obj X` in the abelian case) is
degreewise projective.

## Main definitions and results

* `AlgebraicTopology.DoldKan.Γ₀.projective_obj`,
  `CategoryTheory.Idempotents.DoldKan.Γ.projective_obj`,
  `CategoryTheory.Abelian.DoldKan.Γ.projective_obj`: `Γ` sends degreewise projective chain
  complexes to degreewise projective simplicial objects.
* `CategoryTheory.Idempotents.DoldKan.N.projective_X`,
  `AlgebraicTopology.normalizedMooreComplex.projective_X`: normalized chains of a degreewise
  projective simplicial object are degreewise projective.
* `CategoryTheory.SimplicialObject.projective_iff_N_projective`,
  `CategoryTheory.SimplicialObject.projective_iff_normalizedMooreComplex_projective`: `X` is
  degreewise projective iff its normalized chain complex / Moore complex is degreewise projective.

## References

* A. Dold and D. Puppe, *Homologie nicht-additiver Funktoren. Anwendungen*, Ann. Inst. Fourier 11
  (1961), 201–312, §3.
* C. A. Weibel, *An Introduction to Homological Algebra*, Cambridge University Press (1994), §8.4.
-/

public noncomputable section

universe v u

open CategoryTheory Limits Opposite AlgebraicTopology AlgebraicTopology.DoldKan
open scoped Simplicial DoldKan

namespace AlgebraicTopology.DoldKan

instance Γ₀.projective_obj {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
    (K : ChainComplex C ℕ) [∀ n, Projective (K.X n)] (Δ : SimplexCategoryᵒᵖ) :
    Projective ((Γ₀.obj K).obj Δ) := by
  have : ∀ A : SimplicialObject.Splitting.IndexSet Δ, Projective (Γ₀.Obj.summand K Δ A) :=
    fun A ↦ inferInstanceAs (Projective (K.X A.1.unop.len))
  exact Projective.of_isColimit_cofan (coproductIsCoproduct _)

end AlgebraicTopology.DoldKan

namespace CategoryTheory.Idempotents.DoldKan

section Projective

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasFiniteCoproducts C]
  [IsIdempotentComplete C]

instance Γ.projective_obj (K : ChainComplex C ℕ) [∀ n, Projective (K.X n)]
    (Δ : SimplexCategoryᵒᵖ) : Projective ((Γ.obj K).obj Δ) :=
  inferInstanceAs (Projective ((Γ₀.obj K).obj Δ))

instance N.projective_X (X : SimplicialObject C) [∀ n, Projective (X _⦋n⦌)] (n : ℕ) :
    Projective ((N.obj X).X n) :=
  (((retractN (C := C)).map ((evaluation _ _).obj X)).map
    (HomologicalComplex.eval _ _ n)).projective (p := inferInstanceAs (Projective (X _⦋n⦌)))

end Projective

end CategoryTheory.Idempotents.DoldKan

namespace CategoryTheory.Abelian.DoldKan

instance Γ.projective_obj {A : Type u} [Category.{v} A] [Abelian A]
    (K : ChainComplex A ℕ) [∀ n, Projective (K.X n)] (Δ : SimplexCategoryᵒᵖ) :
    Projective ((Γ.obj K).obj Δ) :=
  inferInstanceAs (Projective ((Idempotents.DoldKan.Γ.obj K).obj Δ))

end CategoryTheory.Abelian.DoldKan

namespace AlgebraicTopology

instance normalizedMooreComplex.projective_X {A : Type u} [Category.{v} A] [Abelian A]
    (X : SimplicialObject A) [∀ n, Projective (X _⦋n⦌)] (n : ℕ) :
    Projective (((normalizedMooreComplex A).obj X).X n) := by
  change Projective ((Abelian.DoldKan.N.obj X).X n)
  exact Projective.of_iso
    (HomologicalComplex.Hom.isoApp ((Abelian.DoldKan.comparisonN (A := A)).symm.app X) n)
    inferInstance

end AlgebraicTopology

namespace CategoryTheory.SimplicialObject

/-- In an idempotent-complete preadditive category with finite coproducts, a simplicial object `X`
is degreewise projective if and only if its normalized chain complex `Idempotents.DoldKan.N.obj X`
is degreewise projective. -/
theorem projective_iff_N_projective {C : Type u} [Category.{v} C] [Preadditive C]
    [HasFiniteCoproducts C] [IsIdempotentComplete C] (X : SimplicialObject C) :
    (∀ n : ℕ, Projective (X _⦋n⦌)) ↔ ∀ n : ℕ, Projective ((Idempotents.DoldKan.N.obj X).X n) := by
  refine ⟨fun _ n ↦ inferInstance, fun _ n ↦ Projective.of_iso
    (((Idempotents.DoldKan.ε (C := C)).symm.app X).app (op ⦋n⦌))
    (inferInstanceAs (Projective
      ((Idempotents.DoldKan.Γ.obj (Idempotents.DoldKan.N.obj X)).obj (op ⦋n⦌))))⟩

/-- In an abelian category, a simplicial object `X` is degreewise projective if and only if its
normalized Moore complex `(normalizedMooreComplex A).obj X` is degreewise projective. -/
theorem projective_iff_normalizedMooreComplex_projective {A : Type u} [Category.{v} A] [Abelian A]
    (X : SimplicialObject A) :
    (∀ n : ℕ, Projective (X _⦋n⦌)) ↔
      ∀ n : ℕ, Projective (((normalizedMooreComplex A).obj X).X n) := by
  rw [projective_iff_N_projective]
  change _ ↔ ∀ n : ℕ, Projective ((Abelian.DoldKan.N.obj X).X n)
  refine ⟨fun h n ↦ Projective.of_iso
      (HomologicalComplex.Hom.isoApp ((Abelian.DoldKan.comparisonN (A := A)).symm.app X) n) (h n),
    fun h n ↦ Projective.of_iso
      (HomologicalComplex.Hom.isoApp ((Abelian.DoldKan.comparisonN (A := A)).app X) n) (h n)⟩

end CategoryTheory.SimplicialObject
