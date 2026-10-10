/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.ReducedRelative
public import Mathlib.Topology.Homotopy.Contractible

/-!
# Singular homology of contractible spaces

A contractible space has the singular homology of a point: its homology vanishes in every positive
degree, and its reduced homology vanishes in every degree. Consequently, the reduced connecting
morphism of a pair is an isomorphism whenever its ambient space is contractible. For
`TauCeti.diskBoundaryPair n`, this identifies the relative homology of a disk modulo its boundary
with the reduced homology of the boundary sphere.  Dually, the quotient map
`Hₖ₊₁(X) ⟶ Hₖ₊₁(X, A)` is an isomorphism whenever the subspace is contractible; for a point this is
`TauCeti.singularHomologyIsoOfSubsetSingleton : Hₖ₊₁(X) ≅ Hₖ₊₁(X, {x})`.

Coefficients are an object `R` of an abelian category with coproducts, as everywhere in relative
singular homology.

The results follow Hatcher, *Algebraic Topology*, Section 2.1: the vanishing of reduced homology
for contractible spaces after Corollary 2.11 and Example 2.23 for the disk and its boundary sphere.
-/

public section

noncomputable section

open CategoryTheory Limits AlgebraicTopology

universe w v u

namespace TauCeti

section Contractible

variable {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Preadditive C]
  [CategoryWithHomology C] (R : C)

/-- **The positive-degree singular homology of a contractible space vanishes.**  The identity of
a contractible space is homotopic to a map factoring through a point, whose positive-degree
homology vanishes. -/
theorem isZero_singularHomologyFunctor_of_contractibleSpace (X : TopCat.{w})
    [ContractibleSpace X] {n : ℕ} (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj X) := by
  obtain ⟨x, ⟨H⟩⟩ := id_nullhomotopic X
  let pt : TopCat.{w} := TopCat.of PUnit
  let p : X ⟶ pt := TopCat.ofHom (ContinuousMap.const X PUnit.unit)
  let s : pt ⟶ X := TopCat.ofHom (ContinuousMap.const pt x)
  have hpt : IsZero (((singularHomologyFunctor C n).obj R).obj pt) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R pt hn
  have hid : ((singularHomologyFunctor C n).obj R).map (p ≫ s) = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_id]
    -- The underlying continuous maps of `p ≫ s` and `𝟙 X` are `ContinuousMap.const X x` and
    -- `ContinuousMap.id X` by definition, so `H.symm` is a homotopy between them.
    exact TopCat.Homotopy.congr_homologyMap_singularChainComplexFunctor (f := p ≫ s) (g := 𝟙 X)
      H.symm R n
  rw [IsZero.iff_id_eq_zero, ← hid, CategoryTheory.Functor.map_comp, hpt.eq_of_src
    (((singularHomologyFunctor C n).obj R).map s) 0, comp_zero]

variable [HasKernels C]

/-- **The reduced singular homology of a contractible space vanishes in every degree.** -/
theorem isZero_reducedSingularHomologyFunctor_of_contractibleSpace (X : TopCat.{w})
    [ContractibleSpace X] (n : ℕ) :
    IsZero ((reducedSingularHomologyFunctor R n).obj X) := by
  cases n with
  | zero => exact isZero_reducedSingularHomologyFunctor_zero R X
  | succ n =>
    exact (isZero_singularHomologyFunctor_of_contractibleSpace R X n.succ_ne_zero).of_iso
      ((reducedSingularHomologySuccIso R n).app X)

end Contractible

end TauCeti

namespace TopPair

open TauCeti

variable {A : Type u} [Category.{v} A] [HasCoproducts.{w} A] [Abelian A] (P : TopPair.{w}) (R : A)

/-- The reduced connecting morphism of a pair with contractible ambient space is an isomorphism
in every degree. -/
instance isIso_reducedSingularHomologyδ_of_contractibleSpace [ContractibleSpace P.fst] (k : ℕ) :
    IsIso (P.reducedSingularHomologyδ R k) :=
  P.isIso_reducedSingularHomologyδ R
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R P.fst (k + 1))
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R P.fst k)

/-- If the subspace of a pair is contractible, the quotient map `Hₖ₊₁(X) ⟶ Hₖ₊₁(X, A)` is an
isomorphism. -/
instance isIso_singularHomologyπ_of_contractibleSpace [ContractibleSpace P.snd] (k : ℕ) :
    IsIso (P.singularHomologyπ R (k + 1)) :=
  P.isIso_singularHomologyπ R
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R P.snd (k + 1))
    (isZero_reducedSingularHomologyFunctor_of_contractibleSpace R P.snd k)

end TopPair

namespace TauCeti

variable {X : Type w} [TopologicalSpace X]
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C] (R : C) (n : ℕ)

/-- **Relative homology modulo a point**: since a point is contractible, the quotient map
`Hₙ₊₁(X; R) ⟶ Hₙ₊₁(X, {x}; R)` is an isomorphism
(`TopPair.isIso_singularHomologyπ_of_contractibleSpace`). -/
def singularHomologyIsoOfSubsetSingleton (x : X) :
    ((singularHomologyFunctor C (n + 1)).obj R).obj (TopCat.of X) ≅
      (TopPair.ofSubset ({x} : Set (TopCat.of X))).singularHomology R (n + 1) :=
  @asIso _ _ _ _ ((TopPair.ofSubset ({x} : Set (TopCat.of X))).singularHomologyπ R (n + 1)) <|
    -- Instance search does not see through the subspace of `TopPair.ofSubset`, so the
    -- contractibility of the point is supplied explicitly.
    @TopPair.isIso_singularHomologyπ_of_contractibleSpace _ _ _ _
      (TopPair.ofSubset ({x} : Set (TopCat.of X))) R
      (inferInstanceAs (ContractibleSpace ({x} : Set X))) n

-- Not `@[simp]`: the source of the quotient map is the homology of the singular simplicial set,
-- which agrees with `((singularHomologyFunctor C (n + 1)).obj R).obj (TopCat.of X)` only up to
-- unfolding, so rewriting with this lemma inside composites leaves ill-typed motives.
lemma singularHomologyIsoOfSubsetSingleton_hom (x : X) :
    (singularHomologyIsoOfSubsetSingleton R n x).hom =
      (TopPair.ofSubset ({x} : Set (TopCat.of X))).singularHomologyπ R (n + 1) :=
  (rfl)

end TauCeti
