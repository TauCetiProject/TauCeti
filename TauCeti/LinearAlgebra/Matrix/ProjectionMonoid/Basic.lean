/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.MurrayVonNeumann

/-!
# The projection monoid `V(R)`

Let `R` be a star ring. The *projection monoid* `V(R)` is the set of matrix projections over `R`
of all finite sizes modulo Murray–von Neumann equivalence, with addition induced by block sum and
zero the class of the zero projection. For a C⋆-algebra `A`, this is the monoid `V(A)` whose
Grothendieck group is the operator `K₀`-group of `A` when `A` is unital.

Since Murray–von Neumann equivalence compares matrices of different sizes through rectangular
matrices, the class of a projection does not depend on the size in which it is written: padding by
zero blocks and reindexing do not change it. The class of `p : Matrix m m R` for an arbitrary
finite index type `m` is `TauCeti.ProjectionMonoid.mk p hp`, and two classes are equal exactly when
the projections are Murray–von Neumann equivalent. Cancellation is not assumed and fails in
general: for the bounded operators on an infinite-dimensional separable Hilbert space,
`[1] + [1] = [1]` while `[1] ≠ 0`.

## Main definitions

* `TauCeti.ProjectionMonoid R`: the commutative monoid `V(R)` of matrix projections over `R`
  modulo Murray–von Neumann equivalence.
* `TauCeti.ProjectionMonoid.mk p hp`: the class in `V(R)` of a projection `p : Matrix m m R`
  indexed by any finite type `m`.
* `TauCeti.ProjectionMonoid.lift f hf`: the function out of `V(R)` induced by a function `f` on
  projections in `Matrix (Fin k) (Fin k) R` that is invariant under Murray–von Neumann equivalence.
* `TauCeti.ProjectionMonoid.map f`: the monoid homomorphism `V(R) →+ V(S)` induced entrywise by a
  star ring homomorphism `f : R →⋆ₙ+* S`.

## Main statements

* `TauCeti.ProjectionMonoid.mk_eq_mk_iff`: two matrix projections, of possibly different sizes,
  have the same class exactly when they are Murray–von Neumann equivalent.
* `TauCeti.ProjectionMonoid.mk_eq_mk_iff_fromBlocks`: the same criterion after padding both
  projections by zero blocks to a common size.
* `TauCeti.ProjectionMonoid.mk_reindex` and `TauCeti.ProjectionMonoid.mk_fromBlocks_zero`: the
  class is invariant under reindexing and under padding by a zero block.
* `TauCeti.ProjectionMonoid.mk_fromBlocks`: the class of a block sum is the sum of the classes.
* `TauCeti.ProjectionMonoid.mk_add_of_mul_eq_zero`: `[p + q] = [p] + [q]` for orthogonal
  projections `p` and `q`.
* `TauCeti.ProjectionMonoid.mk_eq_zero_iff`: a projection has class zero exactly when it is zero.
* `TauCeti.ProjectionMonoid.mk_one`: over a unital star ring, the identity matrix of size `n` has
  class `n • [1]`.
* `TauCeti.ProjectionMonoid.mk_add_mk_one_sub`: over a ring, `[p] + [1 - p] = [1]`.
* `TauCeti.ProjectionMonoid.mk_mul_mul_star`: unitary conjugation does not change the class.
* `TauCeti.ProjectionMonoid.map_id` and `TauCeti.ProjectionMonoid.map_comp`: functoriality.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., Cambridge University Press (1998),
  Definitions 5.1.1 and 5.1.2.
* M. Rørdam, F. Larsen and N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*,
  Cambridge University Press (2000), Section 2.3.
-/

public section

open Matrix

namespace TauCeti

variable (R : Type*) [NonUnitalSemiring R] [StarRing R]

/-- A **matrix projection** over `R`: a star projection in the square matrix algebra
`Matrix (Fin n) (Fin n) R` of some finite size `n`. These represent the elements of the projection
monoid `TauCeti.ProjectionMonoid R`. -/
private structure MatrixProjection where
  /-- The size of the matrix. -/
  size : ℕ
  /-- The underlying square matrix. -/
  matrix : Matrix (Fin size) (Fin size) R
  /-- The matrix is a star projection. -/
  isStarProjection : IsStarProjection matrix

/-- Murray–von Neumann equivalence, as a setoid on matrix projections of all sizes. -/
private instance MatrixProjection.setoid : Setoid (MatrixProjection R) where
  r p q := IsMurrayVonNeumannEquivalent p.matrix q.matrix
  iseqv := ⟨fun p ↦ .refl p.isStarProjection, .symm, .trans⟩

/-- The **projection monoid** `V(R)`: matrix projections over `R` of all finite sizes modulo
Murray–von Neumann equivalence. Its addition is induced by block sum, see
`TauCeti.ProjectionMonoid.mk_fromBlocks`. -/
def ProjectionMonoid : Type _ :=
  Quotient (MatrixProjection.setoid R)

namespace ProjectionMonoid

variable {R} {m n : Type*} [Fintype m] [Fintype n]

/-- The class in `V(R)` of a projection `p` in the square matrices indexed by a finite type `m`.
It is computed by transporting `p` along `Fintype.equivFin m`, and does not depend on this choice
(`TauCeti.ProjectionMonoid.mk_reindex`). -/
noncomputable def mk (p : Matrix m m R) (hp : IsStarProjection p) : ProjectionMonoid R :=
  Quotient.mk _ ⟨Fintype.card m, reindex (Fintype.equivFin m) (Fintype.equivFin m) p,
    (hp.isMurrayVonNeumannEquivalent_reindex _).isStarProjection_right⟩

private theorem quotientMk_eq_mk (p : MatrixProjection R) :
    (Quotient.mk _ p : ProjectionMonoid R) = mk p.matrix p.isStarProjection :=
  Quotient.sound (p.isStarProjection.isMurrayVonNeumannEquivalent_reindex _)

/-- **Equality criterion.** Two matrix projections, of possibly different sizes, have the same
class in `V(R)` exactly when they are Murray–von Neumann equivalent. -/
@[simp]
theorem mk_eq_mk_iff {p : Matrix m m R} {q : Matrix n n R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) : mk p hp = mk q hq ↔ IsMurrayVonNeumannEquivalent p q := by
  refine Quotient.eq.trans ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact ((hp.isMurrayVonNeumannEquivalent_reindex _).trans h).trans
      (hq.isMurrayVonNeumannEquivalent_reindex _).symm
  · exact ((hp.isMurrayVonNeumannEquivalent_reindex _).symm.trans h).trans
      (hq.isMurrayVonNeumannEquivalent_reindex _)

/-- Murray–von Neumann equivalent projections have the same class in `V(R)`. -/
theorem mk_eq_mk {p : Matrix m m R} {q : Matrix n n R} (h : IsMurrayVonNeumannEquivalent p q) :
    mk p h.isStarProjection_left = mk q h.isStarProjection_right :=
  (mk_eq_mk_iff _ _).2 h

/-- Every element of `V(R)` is the class of a projection in `Matrix (Fin n) (Fin n) R` for some
`n`. -/
@[elab_as_elim]
theorem ind {motive : ProjectionMonoid R → Prop}
    (mk : ∀ (n : ℕ) (p : Matrix (Fin n) (Fin n) R) (hp : IsStarProjection p), motive (mk p hp))
    (x : ProjectionMonoid R) : motive x :=
  Quotient.ind (fun p ↦ quotientMk_eq_mk p ▸ mk p.size p.matrix p.isStarProjection) x

/-- Every element of `V(R)` is the class of a projection in `Matrix (Fin n) (Fin n) R` for some
`n`. -/
theorem exists_eq_mk (x : ProjectionMonoid R) :
    ∃ (n : ℕ) (p : Matrix (Fin n) (Fin n) R) (hp : IsStarProjection p), x = mk p hp := by
  induction x using ind with
  | mk n p hp => exact ⟨n, p, hp, rfl⟩

/-- The class of a projection does not depend on how its index type is labelled. -/
theorem mk_reindex {p : Matrix m m R} (hp : IsStarProjection p) (e : m ≃ n) :
    mk (reindex e e p) (hp.isMurrayVonNeumannEquivalent_reindex e).isStarProjection_right =
      mk p hp :=
  (mk_eq_mk (hp.isMurrayVonNeumannEquivalent_reindex e)).symm

/-- The class of a projection does not depend on how its index type is labelled. This is
`TauCeti.ProjectionMonoid.mk_reindex` in the `submatrix` form that `simp` produces. -/
@[simp]
theorem mk_submatrix {p : Matrix m m R} (hp : IsStarProjection p) (e : n ≃ m) :
    mk (p.submatrix e e) (hp.isMurrayVonNeumannEquivalent_reindex e.symm).isStarProjection_right =
      mk p hp :=
  mk_reindex hp e.symm

section lift

variable {α : Sort*} (f : ∀ {k : ℕ} (p : Matrix (Fin k) (Fin k) R), IsStarProjection p → α)
  (hf : ∀ {k l : ℕ} {p : Matrix (Fin k) (Fin k) R} {q : Matrix (Fin l) (Fin l) R}
    (hp : IsStarProjection p) (hq : IsStarProjection q), IsMurrayVonNeumannEquivalent p q →
      f p hp = f q hq)

/-- **Universal property.** A function on projections in `Matrix (Fin k) (Fin k) R`, over all sizes
`k`, that takes the same value on Murray–von Neumann equivalent projections induces a function
out of `V(R)`. -/
def lift : ProjectionMonoid R → α :=
  Quotient.lift (fun p ↦ f p.matrix p.isStarProjection) fun _ _ h ↦ hf _ _ h

/-- The function `TauCeti.ProjectionMonoid.lift f hf` sends the class of a projection in
`Matrix (Fin k) (Fin k) R` to its value under `f`. -/
@[simp]
theorem lift_mk {k : ℕ} {p : Matrix (Fin k) (Fin k) R} (hp : IsStarProjection p) :
    lift @f @hf (mk p hp) = f p hp :=
  hf _ _ (hp.isMurrayVonNeumannEquivalent_reindex _).symm

/-- The function `TauCeti.ProjectionMonoid.lift f hf` sends the class of a projection indexed by
any finite type `m` to the value under `f` of any relabelling of it by `Fin k`. -/
theorem lift_mk_of_equiv {p : Matrix m m R} (hp : IsStarProjection p) {k : ℕ} (e : m ≃ Fin k) :
    lift @f @hf (mk p hp) =
      f (reindex e e p) (hp.isMurrayVonNeumannEquivalent_reindex e).isStarProjection_right := by
  rw [← mk_reindex hp e, lift_mk]

/- The statements above write `@f @hf` so that these arguments are not eta-expanded through their
implicit binders; otherwise `rw` and `simp` match `hf` only up to proof irrelevance and leave it
as a side goal. -/

end lift

/-- The zero of `V(R)` is the class of the zero projection. -/
noncomputable instance : Zero (ProjectionMonoid R) :=
  ⟨mk (0 : Matrix (Fin 0) (Fin 0) R) (.zero _)⟩

/-- Unfolds the `Zero` instance. -/
private theorem zero_def :
    (0 : ProjectionMonoid R) = mk (0 : Matrix (Fin 0) (Fin 0) R) (.zero _) :=
  rfl

/-- A matrix projection has class zero exactly when it is the zero matrix. -/
@[simp]
theorem mk_eq_zero_iff {p : Matrix m m R} (hp : IsStarProjection p) : mk p hp = 0 ↔ p = 0 := by
  rw [zero_def, mk_eq_mk_iff]
  exact isMurrayVonNeumannEquivalent_zero_right_iff

/-- The zero matrix of any size has class zero. -/
@[simp]
theorem mk_zero : mk (0 : Matrix m m R) (.zero _) = 0 :=
  (mk_eq_zero_iff _).2 rfl

/-- Over the zero ring every matrix is zero, so `V(R)` has only one element. -/
instance [Subsingleton R] : Subsingleton (ProjectionMonoid R) where
  allEq x y := by
    induction x using ind with | mk _ p hp => ?_
    induction y using ind with | mk _ q hq => ?_
    rw [(mk_eq_zero_iff hp).2 (Matrix.ext fun _ _ ↦ Subsingleton.elim _ _),
      (mk_eq_zero_iff hq).2 (Matrix.ext fun _ _ ↦ Subsingleton.elim _ _)]

/-- The addition of `V(R)`, induced by block sum of representatives. -/
@[no_expose] noncomputable instance : Add (ProjectionMonoid R) where
  add := Quotient.lift₂
    (fun p q ↦ mk (fromBlocks p.matrix 0 0 q.matrix)
      (p.isStarProjection.fromBlocks_zero₁₂_zero₂₁ q.isStarProjection))
    fun _ _ _ _ h₁ h₂ ↦ (mk_eq_mk_iff _ _).2 (h₁.fromBlocks h₂)

/-- Unfolds `TauCeti.ProjectionMonoid.mk`. -/
private theorem mk_def {p : Matrix m m R} (hp : IsStarProjection p) :
    mk p hp = Quotient.mk _ ⟨Fintype.card m, reindex (Fintype.equivFin m) (Fintype.equivFin m) p,
      (hp.isMurrayVonNeumannEquivalent_reindex _).isStarProjection_right⟩ :=
  rfl

/-- Unfolds the `Add` instance on classes of representatives. -/
private theorem quotientMk_add_quotientMk (p q : MatrixProjection R) :
    @HAdd.hAdd (ProjectionMonoid R) (ProjectionMonoid R) _ _ (Quotient.mk _ p) (Quotient.mk _ q) =
      mk (fromBlocks p.matrix 0 0 q.matrix)
        (p.isStarProjection.fromBlocks_zero₁₂_zero₂₁ q.isStarProjection) :=
  rfl

/-- **Additivity.** The class of the block sum `p ⊕ q` is the sum of the classes of `p` and
`q`. -/
@[simp]
theorem mk_fromBlocks {p : Matrix m m R} {q : Matrix n n R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    mk (fromBlocks p 0 0 q) (hp.fromBlocks_zero₁₂_zero₂₁ hq) = mk p hp + mk q hq := by
  rw [mk_def hp, mk_def hq, quotientMk_add_quotientMk]
  exact mk_eq_mk ((hp.isMurrayVonNeumannEquivalent_reindex _).fromBlocks
    (hq.isMurrayVonNeumannEquivalent_reindex _))

/-- **Orthogonal sums.** The class of the sum of orthogonal projections `p` and `q` is the sum of
their classes. -/
theorem mk_add_of_mul_eq_zero {p q : Matrix m m R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) (hpq : p * q = 0) :
    mk (p + q) (hp.add hq hpq) = mk p hp + mk q hq := by
  rw [← mk_fromBlocks, mk_eq_mk_iff]
  have h := (hp.isMurrayVonNeumannEquivalent_fromBlocks_zero (n := m)).add
    (hq.isMurrayVonNeumannEquivalent_zero_fromBlocks (n := m)) hpq
    (by rw [fromBlocks_multiply]; simp)
  simpa only [fromBlocks_add, add_zero, zero_add] using h

/-- **Padding by zero.** Padding a projection by a zero block of any size does not change its
class. -/
theorem mk_fromBlocks_zero {p : Matrix m m R} (hp : IsStarProjection p) :
    mk (fromBlocks p 0 0 (0 : Matrix n n R)) (hp.fromBlocks_zero₁₂_zero₂₁ (.zero _)) =
      mk p hp :=
  ((mk_eq_mk_iff _ _).2 hp.isMurrayVonNeumannEquivalent_fromBlocks_zero).symm

/-- **Padding by zero.** Padding a projection by a zero block of any size does not change its
class. -/
theorem mk_zero_fromBlocks {p : Matrix m m R} (hp : IsStarProjection p) :
    mk (fromBlocks (0 : Matrix n n R) 0 0 p)
      ((IsStarProjection.zero _).fromBlocks_zero₁₂_zero₂₁ hp) = mk p hp :=
  ((mk_eq_mk_iff _ _).2 hp.isMurrayVonNeumannEquivalent_zero_fromBlocks).symm

/-- **Equality criterion at a common size.** Projections `p : Matrix m m R` and `q : Matrix n n R`
have the same class exactly when their paddings `p ⊕ 0` and `0 ⊕ q` by zero blocks, both indexed
by `m ⊕ n`, are Murray–von Neumann equivalent. -/
theorem mk_eq_mk_iff_fromBlocks {p : Matrix m m R} {q : Matrix n n R} (hp : IsStarProjection p)
    (hq : IsStarProjection q) :
    mk p hp = mk q hq ↔
      IsMurrayVonNeumannEquivalent (fromBlocks p 0 0 (0 : Matrix n n R))
        (fromBlocks (0 : Matrix m m R) 0 0 q) := by
  rw [← mk_eq_mk_iff (hp.fromBlocks_zero₁₂_zero₂₁ (.zero _))
    ((IsStarProjection.zero _).fromBlocks_zero₁₂_zero₂₁ hq), mk_fromBlocks_zero,
    mk_zero_fromBlocks]

/-- `V(R)` is a commutative monoid under block sum, with the zero projection as zero. -/
noncomputable instance : AddCommMonoid (ProjectionMonoid R) where
  add_assoc x y z := by
    induction x using ind with | mk _ p hp => ?_
    induction y using ind with | mk _ q hq => ?_
    induction z using ind with | mk _ r hr => ?_
    rw [← mk_fromBlocks, ← mk_fromBlocks, ← mk_fromBlocks, ← mk_fromBlocks, mk_eq_mk_iff]
    exact isMurrayVonNeumannEquivalent_fromBlocks_assoc hp hq hr
  zero_add x := by
    induction x using ind with
    | mk _ p hp => rw [← mk_zero (m := Fin 0), ← mk_fromBlocks, mk_zero_fromBlocks]
  add_zero x := by
    induction x using ind with
    | mk _ p hp => rw [← mk_zero (m := Fin 0), ← mk_fromBlocks, mk_fromBlocks_zero]
  add_comm x y := by
    induction x using ind with | mk _ p hp => ?_
    induction y using ind with | mk _ q hq => ?_
    rw [← mk_fromBlocks, ← mk_fromBlocks, mk_eq_mk_iff]
    exact isMurrayVonNeumannEquivalent_fromBlocks_comm hp hq
  nsmul := nsmulRec

/-- Over a unital star ring, the identity matrix indexed by `m` has class `card m • [1]`, where
`[1]` is the class of the identity matrix of size one. -/
theorem mk_one {A : Type*} [Semiring A] [StarRing A] [DecidableEq m] :
    mk (1 : Matrix m m A) (.one _) =
      Fintype.card m • mk (1 : Matrix (Fin 1) (Fin 1) A) (.one _) := by
  have h (k : ℕ) : mk (1 : Matrix (Fin k) (Fin k) A) (.one _) =
      k • mk (1 : Matrix (Fin 1) (Fin 1) A) (.one _) := by
    induction k with
    | zero => rw [zero_nsmul, mk_eq_zero_iff]; exact Subsingleton.elim _ _
    | succ k ih =>
      have e := (IsStarProjection.one (Matrix (Fin (k + 1)) (Fin (k + 1)) A))
        |>.isMurrayVonNeumannEquivalent_reindex finSumFinEquiv.symm
      rw [reindex_apply, submatrix_one_equiv, ← fromBlocks_one] at e
      rw [succ_nsmul, ← ih, ← mk_fromBlocks]
      exact mk_eq_mk e
  have e := (IsStarProjection.one (Matrix m m A)).isMurrayVonNeumannEquivalent_reindex
    (Fintype.equivFin m)
  rw [reindex_apply, submatrix_one_equiv] at e
  rw [← h]
  exact mk_eq_mk e

/-- Over a ring, the classes of a projection `p` and of its complement `1 - p` add up to the class
of the identity matrix. -/
theorem mk_add_mk_one_sub {A : Type*} [Ring A] [StarRing A] [DecidableEq m] {p : Matrix m m A}
    (hp : IsStarProjection p) :
    mk p hp + mk (1 - p) hp.one_sub = mk (1 : Matrix m m A) (.one _) := by
  rw [← mk_fromBlocks]
  exact mk_eq_mk hp.isMurrayVonNeumannEquivalent_fromBlocks_one_sub

/-- Conjugating a projection by a unitary does not change its class. -/
@[simp]
theorem mk_mul_mul_star {A : Type*} [Semiring A] [StarRing A] [DecidableEq m]
    {p : Matrix m m A} (hp : IsStarProjection p) {u : Matrix m m A} (hu : u ∈ unitary _) :
    mk (u * p * star u) (hp.isMurrayVonNeumannEquivalent_mul_mul_star hu).isStarProjection_right =
      mk p hp :=
  (mk_eq_mk (hp.isMurrayVonNeumannEquivalent_mul_mul_star hu)).symm

section map

variable {S T : Type*} [NonUnitalSemiring S] [StarRing S] [NonUnitalSemiring T] [StarRing T]

/-- The function `V(R) → V(S)` induced entrywise by a star ring homomorphism. -/
private noncomputable def mapFun (f : R →⋆ₙ+* S) : ProjectionMonoid R → ProjectionMonoid S :=
  lift (fun p hp ↦ mk (p.map f) (hp.matrix_map f)) fun _ _ h ↦ (mk_eq_mk_iff _ _).2 (h.map f)

private theorem mapFun_mk (f : R →⋆ₙ+* S) {p : Matrix m m R} (hp : IsStarProjection p) :
    mapFun f (mk p hp) = mk (p.map f) (hp.matrix_map f) := by
  rw [mapFun, ← mk_reindex hp (Fintype.equivFin m), lift_mk]
  exact mk_eq_mk ((hp.isMurrayVonNeumannEquivalent_reindex _).map f).symm

/-- **Functoriality.** A star ring homomorphism `f : R →⋆ₙ+* S`, applied to matrix entries,
induces a monoid homomorphism `V(R) →+ V(S)`. -/
noncomputable def map (f : R →⋆ₙ+* S) : ProjectionMonoid R →+ ProjectionMonoid S where
  toFun := mapFun f
  map_zero' := by
    rw [← mk_zero (m := Fin 0), mapFun_mk, mk_eq_zero_iff, Matrix.map_zero _ (map_zero f)]
  map_add' x y := by
    induction x using ind with | mk _ p hp => ?_
    induction y using ind with | mk _ q hq => ?_
    rw [← mk_fromBlocks, mapFun_mk, mapFun_mk, mapFun_mk, ← mk_fromBlocks]
    simp only [fromBlocks_map, Matrix.map_zero _ (map_zero f)]

/-- The image under `TauCeti.ProjectionMonoid.map f` of the class of `p` is the class of the
entrywise image of `p`. -/
@[simp]
theorem map_mk (f : R →⋆ₙ+* S) {p : Matrix m m R} (hp : IsStarProjection p) :
    map f (mk p hp) = mk (p.map f) (hp.matrix_map f) :=
  mapFun_mk f hp

/-- The identity homomorphism induces the identity of `V(R)`. -/
@[simp]
theorem map_id : map (NonUnitalStarRingHom.id R) = AddMonoidHom.id (ProjectionMonoid R) := by
  ext x
  induction x using ind with
  | mk _ p hp => simp [Matrix.map_id]

/-- The homomorphism induced by a composite is the composite of the induced homomorphisms. -/
theorem map_comp (g : S →⋆ₙ+* T) (f : R →⋆ₙ+* S) :
    map (g.comp f) = (map g).comp (map f) := by
  ext x
  induction x using ind with
  | mk _ p hp => simp [Matrix.map_map]

/-- Applying the homomorphisms induced by `f` and then by `g` on `V` is applying the homomorphism
induced by their composite. -/
theorem map_map (g : S →⋆ₙ+* T) (f : R →⋆ₙ+* S) (x : ProjectionMonoid R) :
    map g (map f x) = map (g.comp f) x := by
  rw [map_comp, AddMonoidHom.comp_apply]

/-- If a star ring homomorphism vanishes, so does the homomorphism it induces on `V`. -/
theorem map_eq_zero_of_forall_eq_zero {f : R →⋆ₙ+* S} (hf : ∀ r, f r = 0)
    (x : ProjectionMonoid R) : map f x = 0 := by
  induction x using ind with
  | mk _ p hp =>
    rw [map_mk, mk_eq_zero_iff]
    ext i j
    exact hf _

end map

end ProjectionMonoid

end TauCeti
