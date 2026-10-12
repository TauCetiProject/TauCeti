/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Radical
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# The basis of a path algebra truncated by path length

The quotient of a path algebra by the span of paths of length at least `n` has precisely the
shorter paths as a basis. When the vertex type is finite, this gives a concrete basis for the
quotient by the `n`th power of the arrow ideal. It is useful for calculations with bound quivers,
including the radical-square-zero presentation of the preprojective algebra of `A₂`.

The construction follows the path-basis description of truncated quiver algebras in
Assem--Simson--Skowroński, *Elements of the Representation Theory of Associative Algebras I*,
Chapter II.
-/

public section

namespace TauCeti

open PathAlgebra

universe u v w

section Coordinates

variable (k : Type w) (Q : Type u) [Semiring k] [Quiver.{v} Q]

/-- Paths of length strictly less than `n`. -/
abbrev ShortPath (n : ℕ) := {p : Quiver.TotalPath Q // p.2.2.length < n}

/-- The coordinates of a path-algebra element on paths shorter than `n`. -/
noncomputable def shortPathCoords (n : ℕ) :
    pathAlgebra k Q →ₗ[k] ShortPath Q n →₀ k :=
  (Finsupp.lsubtypeDomain {p : Quiver.TotalPath Q | p.2.2.length < n}).comp
    (pathAlgebraBasis k Q).repr.toLinearMap

/-- Reading the coordinate of a short path agrees with the path-basis coordinate. -/
@[simp]
theorem shortPathCoords_apply (n : ℕ) (x : pathAlgebra k Q) (p : ShortPath Q n) :
    shortPathCoords k Q n x p = (pathAlgebraBasis k Q).repr x p.1 := by
  rfl

/-- The coordinate map kills exactly the span of paths of length at least `n`. -/
theorem ker_shortPathCoords (n : ℕ) :
    LinearMap.ker (shortPathCoords k Q n) = pathSpan k Q n := by
  ext x
  rw [LinearMap.mem_ker, mem_pathSpan_iff, shortPathCoords, LinearMap.comp_apply,
    Finsupp.lsubtypeDomain_apply, Finsupp.subtypeDomain_eq_zero_iff']
  constructor
  · intro hx p hp
    by_contra hn
    exact hp (hx p (Nat.lt_of_not_ge hn))
  · intro hx p hp
    by_contra hn
    exact hp.not_ge (hx p hn)

/-- Every collection of coefficients on short paths extends to a path-algebra element. -/
theorem shortPathCoords_surjective (n : ℕ) :
    Function.Surjective (shortPathCoords k Q n) := by
  intro y
  let e : ShortPath Q n ↪ Quiver.TotalPath Q := Function.Embedding.subtype _
  refine ⟨(pathAlgebraBasis k Q).repr.symm (Finsupp.embDomain e y), ?_⟩
  apply Finsupp.ext
  intro p
  rw [shortPathCoords_apply, LinearEquiv.apply_symm_apply]
  exact Finsupp.embDomain_apply_self e y p

end Coordinates

section LengthFiltration

variable (k : Type w) (Q : Type u) [Ring k] [Quiver.{v} Q]

/-- The quotient by the length filtration is the free module on short paths. -/
noncomputable def truncatedPathEquiv (n : ℕ) :
    (pathAlgebra k Q ⧸ pathSpan k Q n) ≃ₗ[k] ShortPath Q n →₀ k :=
  (Submodule.quotEquivOfEq _ _ (ker_shortPathCoords k Q n).symm).trans
    ((shortPathCoords k Q n).quotKerEquivOfSurjective
      (shortPathCoords_surjective k Q n))

/-- The equivalence reads the short-path coordinates of a quotient representative. -/
@[simp]
theorem truncatedPathEquiv_mk (n : ℕ) (x : pathAlgebra k Q) :
    truncatedPathEquiv k Q n (Submodule.Quotient.mk x) = shortPathCoords k Q n x := by
  simp [truncatedPathEquiv]

end LengthFiltration

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q]

section ArrowIdeal

variable [Finite Q]

/-- The quotient by an arrow-ideal power is linearly equivalent to the free module on paths
shorter than that power. -/
noncomputable def arrowIdealQuotientEquiv (n : ℕ) :
    (pathAlgebra k Q ⧸ arrowIdeal k Q ^ n) ≃ₗ[k] ShortPath Q n →₀ k :=
  ((Submodule.Quotient.restrictScalarsEquiv k (arrowIdeal k Q ^ n)).symm.trans
    (Submodule.quotEquivOfEq _ _ (restrictScalars_arrowIdeal_pow k Q n))).trans
      (truncatedPathEquiv k Q n)

/-- The quotient equivalence reads the coefficients of every short path. -/
@[simp]
theorem arrowIdealQuotientEquiv_mk (n : ℕ) (x : pathAlgebra k Q) :
    arrowIdealQuotientEquiv k Q n (Ideal.Quotient.mk _ x) = shortPathCoords k Q n x := by
  simp only [← Ideal.Quotient.mk_eq_mk, arrowIdealQuotientEquiv, LinearEquiv.trans_apply,
    Submodule.Quotient.restrictScalarsEquiv_symm_mk, Submodule.quotEquivOfEq_mk,
    truncatedPathEquiv_mk]

/-- The classes of paths shorter than `n` form a basis of the quotient by `R^n`, where `R` is
the arrow ideal. -/
noncomputable def arrowIdealQuotientBasis (n : ℕ) :
    Module.Basis (ShortPath Q n) k (pathAlgebra k Q ⧸ arrowIdeal k Q ^ n) :=
  Finsupp.basisSingleOne.map (arrowIdealQuotientEquiv k Q n).symm

/-- A short path's basis vector is its class in the quotient by `R^n`. -/
@[simp]
theorem arrowIdealQuotientBasis_apply (n : ℕ) (p : ShortPath Q n) :
    arrowIdealQuotientBasis k Q n p = Ideal.Quotient.mk _ (ofPath p.1) := by
  apply (arrowIdealQuotientEquiv k Q n).injective
  apply Finsupp.ext
  intro q
  simp only [arrowIdealQuotientBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    arrowIdealQuotientEquiv_mk, shortPathCoords_apply, ofPath_eq_single,
    pathAlgebraBasis_repr_single, Finsupp.coe_basisSingleOne]
  exact (Finsupp.single_apply_left Subtype.val_injective p q 1).symm

/-- The short-path basis coordinates are exactly the restricted path coordinates. -/
@[simp]
theorem arrowIdealQuotientBasis_repr (n : ℕ)
    (x : pathAlgebra k Q ⧸ arrowIdeal k Q ^ n) :
    (arrowIdealQuotientBasis k Q n).repr x = arrowIdealQuotientEquiv k Q n x := by
  simp [arrowIdealQuotientBasis, Module.Basis.map_repr]

/-- The `finrank` of a truncated path algebra is `Nat.card` of its short paths. When the quiver
has finitely many arrows between any two vertices this is the dimension and the number of short
paths; otherwise both sides may be infinite and hence both equal `0`. -/
theorem finrank_arrowIdealQuotient [Nontrivial k] (n : ℕ) :
    Module.finrank k (pathAlgebra k Q ⧸ arrowIdeal k Q ^ n) = Nat.card (ShortPath Q n) :=
  Module.finrank_eq_nat_card_basis (arrowIdealQuotientBasis k Q n)

variable [∀ a b : Q, Finite (a ⟶ b)]

/-- A finite quiver has finitely many paths below any fixed length. -/
instance (n : ℕ) : Finite (ShortPath Q n) :=
  Set.finite_coe_iff.mpr (Quiver.finite_setOf_length_lt n)

/-- A quotient by an arrow-ideal power is a finite module for a finite quiver. -/
instance (n : ℕ) : Module.Finite k (pathAlgebra k Q ⧸ arrowIdeal k Q ^ n) :=
  Module.Finite.of_basis (arrowIdealQuotientBasis k Q n)

end ArrowIdeal

end TauCeti
