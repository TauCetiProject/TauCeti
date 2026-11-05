/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Kronecker
public import TauCeti.Algebra.Homology.Monoidal.Cup
public import TauCeti.Algebra.Homology.Monoidal.Homology.Cross

/-!
# The Kronecker pairing of cross products

Let `A` and `B` be chain complexes in a `k`-linear abelian monoidal category, and let
`μ : M ⊗ N ⟶ P` be a pairing of coefficient objects.  A class `a ∈ Hᵖ(Hom(A, M))` and a class
`b ∈ H^q(Hom(B, N))` have the cross product `a × b ∈ Hⁿ(Hom(A ⊗ B, P))`, `n = p + q`: the cup
product `TauCeti.ChainComplex.cup` along the identity diagonal of `A ⊗ B`, represented by the
tensor product of cocycles.  Homology classes `x ∈ Hₚ(A)` and `y ∈ H_q(B)` have the cross product
`x × y ∈ Hₙ(A ⊗ B)` (`HomologicalComplex.homologyCross`).  The Kronecker pairing of the two cross
products is the product of the Kronecker pairings:

`⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)`,

with no sign (`ChainComplex.homologyCross_comp_kronecker_cup`), and
`⟨a × b, x × y⟩ = 0` when `x` has degree `p' ≠ p`
(`ChainComplex.homologyCross_comp_kronecker_cup_of_ne`): the tensor product of cocycles
vanishes on the summands `A_{p'} ⊗ B_{q'}` with `p' ≠ p`.  These two identities say that, under
the Kronecker maps, the cohomology cross product is the dual of the homology Künneth map, which is
how the Künneth theorem for cohomology over a field is deduced from the Künneth theorem for
homology.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 3.2, the cross product in cohomology, and Section 3.B, the cross product in homology.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory HomologicalComplex TauCeti.ChainComplex

namespace ChainComplex

variable {C : Type*} [Category* C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  {k : Type*} [CommRing k] [Linear k C] [MonoidalLinear k C]
  (A B : ChainComplex C ℕ) [A.HasTensor B] {M N P : C} (μ : M ⊗ N ⟶ P)

/-- The cross product of cohomology classes of `Hom(A, M)` and `Hom(B, N)` is represented by the
tensor product of cocycles: the Kronecker image of the cup product along the identity diagonal,
precomposed with the class of a cycle, is the tensor product of cochains on that cycle. -/
private lemma homologyπ_kronecker_cup (p q n : ℕ) (h : p + q = n)
    (φ : (A.linearYonedaObj k M).cycles p) (ψ : (B.linearYonedaObj k N).cycles q) :
    (HomologicalComplex.tensorObj A B).homologyπ n ≫
        kronecker k (HomologicalComplex.tensorObj A B) P n
          (cup k (𝟙 (HomologicalComplex.tensorObj A B)) μ p q n h
            ((A.linearYonedaObj k M).homologyπ p φ) ((B.linearYonedaObj k N).homologyπ q ψ)) =
      (HomologicalComplex.tensorObj A B).iCycles n ≫
        tensorCochain μ ((A.linearYonedaObj k M).iCycles p φ)
          ((B.linearYonedaObj k N).iCycles q ψ) n := by
  rw [cup_homologyπ, kronecker_homologyπ, iCycles_cupCycles]
  exact congrArg _ ((cupCochain_apply _ μ p q n h _ _).trans (Category.id_comp _))

variable (p q : ℕ) [PreservesColimitsOfShape WalkingParallelPair (tensorLeft (A.homology p))]
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight (B.cycles q))]
  [PreservesColimitsOfShape WalkingParallelPair
    (tensorRight (B.X ((ComplexShape.down ℕ).prev q)))]

/-- **The Kronecker pairing of cross products**, `⟨a × b, x × y⟩ = μ (⟨a, x⟩ ⊗ ⟨b, y⟩)`: the
Kronecker image of the cross product `a × b ∈ Hⁿ(Hom(A ⊗ B, P))`, the cup product along the
identity diagonal, restricted along the homology cross product
`Hₚ(A) ⊗ H_q(B) ⟶ Hₙ(A ⊗ B)`, is the tensor product of the Kronecker images of `a` and `b`
followed by the pairing `μ`. -/
lemma homologyCross_comp_kronecker_cup (n : ℕ) (h : p + q = n)
    (a : (A.linearYonedaObj k M).homology p) (b : (B.linearYonedaObj k N).homology q) :
    homologyCross A B p q n h ≫
        kronecker k (HomologicalComplex.tensorObj A B) P n
          (cup k (𝟙 (HomologicalComplex.tensorObj A B)) μ p q n h a b) =
      (kronecker k A M p a ⊗ₘ kronecker k B N q b) ≫ μ := by
  obtain ⟨φ, rfl⟩ := moduleCat_homologyπ_surjective _ p a
  obtain ⟨ψ, rfl⟩ := moduleCat_homologyπ_surjective _ q b
  ext
  rw [homologyπ_tensorHom_homologyCross_assoc, homologyπ_kronecker_cup, cyclesCross_iCycles_assoc,
    tensorHom_comp_tensorHom_assoc, kronecker_homologyπ, kronecker_homologyπ]
  exact (congrArg (_ ≫ ·) (ιTensorObj_tensorCochain μ _ _ n h)).trans
    (tensorHom_comp_tensorHom_assoc _ _ _ _ _)

/-- **The Kronecker pairing of cross products of different degrees vanishes**: for `p' ≠ p`, the
Kronecker image of the cross product `a × b ∈ Hⁿ(Hom(A ⊗ B, P))` of classes of degrees `p'` and
`q'` vanishes on the image of the homology cross product `Hₚ(A) ⊗ H_q(B) ⟶ Hₙ(A ⊗ B)`. -/
lemma homologyCross_comp_kronecker_cup_of_ne {p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n)
    (hp : p ≠ p') (a : (A.linearYonedaObj k M).homology p')
    (b : (B.linearYonedaObj k N).homology q') :
    homologyCross A B p q n h ≫
        kronecker k (HomologicalComplex.tensorObj A B) P n
          (cup k (𝟙 (HomologicalComplex.tensorObj A B)) μ p' q' n h' a b) = 0 := by
  obtain ⟨φ, rfl⟩ := moduleCat_homologyπ_surjective _ p' a
  obtain ⟨ψ, rfl⟩ := moduleCat_homologyπ_surjective _ q' b
  ext
  rw [homologyπ_tensorHom_homologyCross_assoc, homologyπ_kronecker_cup, cyclesCross_iCycles_assoc,
    comp_zero]
  exact (congrArg (_ ≫ ·) (ιTensorObj_tensorCochain_of_ne_left μ _ _ h hp)).trans comp_zero

end ChainComplex
