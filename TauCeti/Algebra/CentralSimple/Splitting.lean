/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.Algebra.CentralSimple.Degree` is imported publicly: `TauCeti.Algebra.deg` occurs in the
-- statements below, and it is the separably closed base change
-- `TauCeti.IsSimpleRing.nonempty_algEquiv_matrix_baseChange_of_isSepClosed` proved there that makes
-- a separably closed extension a splitting field. It also re-exports
-- `Mathlib.RingTheory.TensorProduct.Basic` (the `⊗[K]` notation and the algebra structure on
-- `L ⊗[K] A`) and `Mathlib.Algebra.Central.Basic`, which is why neither is imported again here.
public import TauCeti.Algebra.CentralSimple.Degree
-- `TauCeti.Algebra.matrixBaseChangeAlgEquiv` is what splits a matrix algebra, and this module also
-- supplies the `Matrix` type occurring in every statement below.
public import TauCeti.Algebra.Matrix.BaseChange
-- The finite-field matrix presentation, matrix composition, and quaternion and complex-number
-- facts are used only in proofs and examples.
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Matrix.Composition
import Mathlib.RingTheory.Finiteness.Descent
import TauCeti.Algebra.CentralSimple.Wedderburn
import TauCeti.Algebra.Central.Quaternion

/-!
# Splitting fields of a central simple algebra

A field extension `L / K` **splits** a `K`-algebra `A` when the scalar extension `L ⊗[K] A` is a
full matrix algebra over `L`. This file defines that predicate, `TauCeti.Algebra.IsSplittingField`,
gives it its basic API, and settles the two cases that need no additional field theory: a
**separably closed** extension splits every finite-dimensional central simple algebra, and over a
**finite** base field every central simple algebra is already split by the base field itself.

The name is qualified because Mathlib's root-namespace `IsSplittingField` is the unrelated
predicate that a field extension splits a *polynomial*.

## The matrix size

For any `K`-algebra `A` admitting a splitting, the matrix size is forced to be
`TauCeti.Algebra.deg K A`. Scalar extension preserves dimension, and an `n × n` matrix algebra
has dimension `n ^ 2`, so a splitting gives `Module.finrank K A = n ^ 2`. The characteristic
property `TauCeti.Algebra.deg_eq_of_finrank_eq_sq` then identifies the degree with `n`.
Neither centrality nor simplicity is needed for this identification.

The dimension calculation `TauCeti.Algebra.finrank_eq_sq_of_algEquiv_matrix` lives in
`TauCeti/Algebra/Matrix/BaseChange.lean` and also allows extension to a nontrivial commutative
`K`-algebra that need not be a field.

## Main results

* `TauCeti.Algebra.IsSplittingField`: the predicate itself, unfolded by
  `TauCeti.Algebra.isSplittingField_iff`, with the transport
  `TauCeti.Algebra.isSplittingField_congr` along a `K`-algebra isomorphism of `A` and the
  observation `TauCeti.Algebra.isSplittingField_matrix` that a full matrix algebra over `K` is
  split by every extension (by the base change `TauCeti.Algebra.matrixBaseChangeAlgEquiv` of
  `TauCeti/Algebra/Matrix/BaseChange.lean`).
* `TauCeti.Algebra.IsSplittingField.finiteDimensional`: an algebra admitting a splitting field
  is finite-dimensional over its base field.
* `TauCeti.Algebra.IsSplittingField.matrix`: a splitting field for `A` also splits every full
  matrix algebra over `A`.
* `TauCeti.Algebra.IsSplittingField.of_isScalarTower`: every further field extension of a
  splitting field still splits `A`.
* `TauCeti.Algebra.isSplittingField_self_iff`: `A` is split by its own base field exactly when it
  *is* a matrix algebra over it. This is the statement that "split" means what it should.
* `TauCeti.Algebra.finrank_eq_sq_of_algEquiv_matrix` and
  `TauCeti.Algebra.IsSplittingField.nonempty_algEquiv_matrix_deg`: the dimension count and the
  identification of the matrix size with the degree, for any algebra admitting a splitting.
* `TauCeti.Algebra.isSplittingField_of_isSepClosed`: **a separably closed extension splits
  every finite-dimensional central simple algebra**.
* `TauCeti.Algebra.isSplittingField_self_of_finite`: **over a finite field every central simple
  algebra is split by the base field**, so there is nothing to split.

## Implementation notes

`TauCeti.Algebra.IsSplittingField` is stated with `L ⊗[K] A`, the base field on the *left*, because
that is the orientation in which `L ⊗[K] A` carries its `L`-algebra structure by
`Algebra.TensorProduct.leftAlgebra` with no further glue, and it is the orientation of the base
change in `TauCeti/Algebra/CentralSimple/Degree.lean`.

The predicate deliberately asks for nothing of `A` beyond being a `K`-algebra: the elementary
lemmas and the degree-size characterization hold at that generality. A splitting itself implies
finite-dimensionality, by `TauCeti.Algebra.IsSplittingField.finiteDimensional`. Central simplicity
and finite-dimensionality enter as assumptions only in the existence theorems for splitting fields.

Splitting ascends along field towers: if `L` splits `A`, so does every field extension `M` of `L`
(`TauCeti.Algebra.IsSplittingField.of_isScalarTower`), and the matrix size does not change. A
finite separable splitting extension may therefore be enlarged to its normal closure to obtain a
finite Galois splitting extension. Ascent holds for any, possibly noncommutative, `K`-algebra `A`.

## References

P. Gille, T. Szamuely, *Central Simple Algebras and Galois Cohomology*, Section 2.2, and
R. S. Pierce, *Associative Algebras*, GTM 88, Chapter 13.
-/

public section

namespace TauCeti

open scoped TensorProduct

namespace Algebra

/-! ### Splitting fields -/

/-- An extension `L / K` **splits** the `K`-algebra `A` when the scalar extension `L ⊗[K] A` is a
full matrix algebra over `L`.

The matrix size is existentially quantified so that the predicate makes sense for an arbitrary
`K`-algebra. Whenever a splitting exists, its size is forced to be
`TauCeti.Algebra.deg K A` by `TauCeti.Algebra.IsSplittingField.nonempty_algEquiv_matrix_deg`. -/
def IsSplittingField (K A L : Type*) [Field K] [Ring A] [Algebra K A] [Field L] [Algebra K L] :
    Prop :=
  ∃ n : ℕ, Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L)

variable (K : Type*) [Field K] (A : Type*) [Ring A] [Algebra K A]
  (L : Type*) [Field L] [Algebra K L]

/-- **The definition, unfolded**: `L` splits `A` exactly when `L ⊗[K] A` is an `n × n` matrix
algebra over `L` for some `n`.

This is the characterization at the generality the predicate is stated at, and everything below
goes through it rather than through the body; the size is pinned by
`TauCeti.Algebra.isSplittingField_iff_deg`. -/
theorem isSplittingField_iff :
    IsSplittingField K A L ↔ ∃ n : ℕ, Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L) :=
  Iff.rfl

variable {K A L} in
/-- An algebra admitting a splitting field is finite-dimensional over its base field.
This includes the zero algebra: the matrix size of the splitting may be zero. -/
theorem IsSplittingField.finiteDimensional (h : IsSplittingField K A L) :
    FiniteDimensional K A := by
  obtain ⟨n, ⟨e⟩⟩ := (isSplittingField_iff K A L).1 h
  let : Module.Finite L (L ⊗[K] A) := Module.Finite.equiv e.toLinearEquiv.symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat L

/-- Splitting is a property of the isomorphism class of `A`: a `K`-algebra isomorphic to a split
one is split, by the same extension and with the same matrix size. -/
theorem IsSplittingField.of_algEquiv {B : Type*} [Ring B] [Algebra K B] (e : A ≃ₐ[K] B)
    (h : IsSplittingField K A L) : IsSplittingField K B L :=
  (isSplittingField_iff K B L).2 <| ((isSplittingField_iff K A L).1 h).imp fun _ ⟨f⟩ ↦
    ⟨(Algebra.TensorProduct.congr (AlgEquiv.refl (R := L) (A₁ := L)) e).symm.trans f⟩

/-- Splitting transports along a `K`-algebra isomorphism of the algebra being split. -/
theorem isSplittingField_congr {B : Type*} [Ring B] [Algebra K B] (e : A ≃ₐ[K] B) :
    IsSplittingField K A L ↔ IsSplittingField K B L :=
  ⟨IsSplittingField.of_algEquiv K A L e, IsSplittingField.of_algEquiv K B L e.symm⟩

/-- **A full matrix algebra over `K` is split by every extension of `K`**, by
`TauCeti.Algebra.matrixBaseChangeAlgEquiv`. In particular it is split by `K` itself. -/
theorem isSplittingField_matrix (n : ℕ) : IsSplittingField K (Matrix (Fin n) (Fin n) K) L :=
  (isSplittingField_iff K _ L).2 ⟨n, ⟨matrixBaseChangeAlgEquiv K L (Fin n)⟩⟩

/-- If `L` splits a `K`-algebra `A`, then it also splits every full matrix algebra over `A`.

After base change, the given splitting identifies each matrix entry with an `m × m` matrix over
`L`; composing the two matrix indices gives an `(n * m) × (n * m)` matrix over `L`. -/
theorem IsSplittingField.matrix (h : IsSplittingField K A L) (n : ℕ) :
    IsSplittingField K (Matrix (Fin n) (Fin n) A) L := by
  obtain ⟨m, ⟨e⟩⟩ := h
  refine (isSplittingField_iff K _ L).2 ⟨n * m, ⟨?_⟩⟩
  exact (matrixCoeffBaseChangeAlgEquiv K L (Fin n) A).trans <|
    (e.mapMatrix (m := Fin n)).trans <|
      (Matrix.compAlgEquiv (Fin n) (Fin m) L L).trans <|
        Matrix.reindexAlgEquiv L L finProdFinEquiv

/-- **Every further field extension of a splitting field is a splitting field.**

If `L` splits `A` and `M` is a field extension of `L` (compatibly with `K`), then `M ⊗[K] A` is
again a full matrix algebra over `M`, of the same size as `L ⊗[K] A` is over `L`. Use this to
replace a splitting field by any larger field, such as a normal or separable closure of it. -/
theorem IsSplittingField.of_isScalarTower (h : IsSplittingField K A L)
    (M : Type*) [Field M] [Algebra K M] [Algebra L M] [IsScalarTower K L M] :
    IsSplittingField K A M := by
  obtain ⟨n, ⟨e⟩⟩ := (isSplittingField_iff K A L).1 h
  refine (isSplittingField_iff K A M).2 ⟨n, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.baseChangeTowerAlgEquiv K L A M).symm.trans <|
    (Algebra.TensorProduct.congr (AlgEquiv.refl (R := M) (A₁ := M)) e).trans <|
      matrixBaseChangeAlgEquiv L M (Fin n)

/-- **`A` is split by its own base field exactly when it is a matrix algebra over it.** This is the
sanity check on the definition: over `L = K` the scalar extension does nothing, so "split" is
literally "is a matrix algebra". -/
theorem isSplittingField_self_iff :
    IsSplittingField K A K ↔ ∃ n : ℕ, Nonempty (A ≃ₐ[K] Matrix (Fin n) (Fin n) K) :=
  (isSplittingField_iff K A K).trans <| exists_congr fun _ ↦
    ⟨fun ⟨e⟩ ↦ ⟨(Algebra.TensorProduct.lid K A).symm.trans e⟩,
      fun ⟨e⟩ ↦ ⟨(Algebra.TensorProduct.lid K A).trans e⟩⟩

/-- **`L` splits `A` exactly when `L` splits the `L`-algebra `L ⊗[K] A`.**

Both sides say `∃ n, L ⊗[K] A ≃ₐ[L] Mₙ(L)`, the left through
`TauCeti.Algebra.isSplittingField_self_iff` and the right by definition. The lemma exists to move
between the two readings, and so to bring results about a field splitting an algebra over *itself*
to bear on a scalar extension. -/
theorem isSplittingField_baseChange_self_iff :
    IsSplittingField L (L ⊗[K] A) L ↔ IsSplittingField K A L :=
  (isSplittingField_self_iff L (L ⊗[K] A)).trans (isSplittingField_iff K A L).symm

/-- **The matrix size of a splitting is the degree.** Any splitting
`L ⊗[K] A ≃ₐ[L] Matrix (Fin n) (Fin n) L` has `n = TauCeti.Algebra.deg K A`, so the splitting
can always be restated at that size. Centrality, simplicity, and finite-dimensionality need not
be assumed: the splitting itself gives `Module.finrank K A = n ^ 2`. -/
theorem IsSplittingField.nonempty_algEquiv_matrix_deg (h : IsSplittingField K A L) :
    Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin (deg K A)) (Fin (deg K A)) L) := by
  obtain ⟨n, ⟨e⟩⟩ := (isSplittingField_iff K A L).1 h
  rw [deg_eq_of_finrank_eq_sq (finrank_eq_sq_of_algEquiv_matrix K A L e)]
  exact ⟨e⟩

/-- An algebra is split by `L` exactly when `L ⊗[K] A` is the matrix algebra of size its degree. -/
theorem isSplittingField_iff_deg :
    IsSplittingField K A L ↔
      Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin (deg K A)) (Fin (deg K A)) L) :=
  ⟨IsSplittingField.nonempty_algEquiv_matrix_deg K A L,
    fun h ↦ (isSplittingField_iff K A L).2 ⟨deg K A, h⟩⟩

section CentralSimple

variable [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]

/-- **A separably closed extension splits every finite-dimensional central simple algebra.**

This is the base case of the separable splitting theory, and it needs no theory of maximal
subfields: over a separably closed field the Wedderburn division algebra collapses, which is
exactly `TauCeti.IsSimpleRing.nonempty_algEquiv_matrix_baseChange_of_isSepClosed`. Every
finite-dimensional central simple `K`-algebra therefore has a separable splitting field, namely a
separable closure of `K`. -/
theorem isSplittingField_of_isSepClosed [IsSepClosed L] : IsSplittingField K A L :=
  (isSplittingField_iff_deg K A L).2
    (IsSimpleRing.nonempty_algEquiv_matrix_baseChange_of_isSepClosed K L A)

/-- **Over a finite field every central simple algebra is split by the base field.** A finite
central division algebra is its own base field (little Wedderburn), so the Wedderburn presentation
of `A` is already a matrix algebra over `K`; there is nothing left for an extension to split.

Together with `TauCeti.Algebra.isSplittingField_self_iff` this is the algebra-level content of the
triviality of the Brauer group of a finite field. -/
theorem isSplittingField_self_of_finite [Finite K] : IsSplittingField K A K := by
  obtain ⟨n, -, -, he⟩ := IsSimpleRing.exists_algEquiv_matrix_of_finite K A
  exact (isSplittingField_self_iff K A).mpr ⟨n, he⟩

end CentralSimple

/-! ### Worked examples -/

section Examples

-- `_root_.` is needed because `TauCeti.Quaternion` is also a namespace, so a bare
-- `open scoped Quaternion` would open that one and leave the `ℍ[·]` notation out of scope.
open scoped _root_.Quaternion

/-- **`ℂ` splits the real quaternions.** `ℂ` is algebraically closed, so this is
`TauCeti.Algebra.isSplittingField_of_isSepClosed`; all three of `Algebra.IsCentral ℝ ℍ[ℝ]`,
`IsSimpleRing ℍ[ℝ]` and `FiniteDimensional ℝ ℍ[ℝ]` are found by instance search. -/
example : IsSplittingField ℝ ℍ[ℝ] ℂ := isSplittingField_of_isSepClosed ℝ ℍ[ℝ] ℂ

/-- The splitting of `ℍ[ℝ]` by `ℂ` happens at the degree, so it is
`ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ` on the nose. -/
example : Nonempty (ℂ ⊗[ℝ] ℍ[ℝ] ≃ₐ[ℂ] Matrix (Fin 2) (Fin 2) ℂ) := by
  have hdeg : deg ℝ ℍ[ℝ] = 2 :=
    deg_eq_of_finrank_eq_sq (by rw [Quaternion.finrank_eq_four]; norm_num)
  exact hdeg ▸ (isSplittingField_of_isSepClosed ℝ ℍ[ℝ] ℂ).nonempty_algEquiv_matrix_deg ..

/-- **`ℝ` does not split the real quaternions**, so a central simple algebra need not be split by
its own base field and the notion is not vacuous. A splitting over `ℝ` would make `ℍ[ℝ]` a matrix
algebra over `ℝ`, necessarily of size `2` by the dimension count, and a `2 × 2` matrix algebra has
zero divisors while `ℍ[ℝ]` does not. -/
example : ¬ IsSplittingField ℝ ℍ[ℝ] ℝ := by
  have hdeg : deg ℝ ℍ[ℝ] = 2 :=
    deg_eq_of_finrank_eq_sq (by rw [Quaternion.finrank_eq_four]; norm_num)
  rw [isSplittingField_iff_deg, hdeg]
  rintro ⟨e⟩
  exact (Quaternion.isEmpty_algEquiv_matrix ℝ (Fin 2)).elim
    ((Algebra.TensorProduct.lid ℝ ℍ[ℝ]).symm.trans e)

end Examples

end Algebra

end TauCeti
