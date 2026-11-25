/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.WordPairing

/-!
# Loop operations of zigzag algebras which are Hochschild coboundaries

Let `Z` be the zigzag algebra of a finite simple graph `G` with no isolated vertex, graded by path
length and regarded as an `A∞` algebra whose only operation is the product
(`TauCeti.zigzagStrictAInfinityAlgebra`). For coefficients `c` on closed walks of `n + 2` darts,
`n ≥ 1`, the operation of arity `n + 2` of the loop deformation
`TauCeti.zigzagLoopAInfinityAlgebra` is a Hochschild cocycle of `Z`. The word pairings of
`TauCeti.RepresentationTheory.Quiver.Zigzag.AInfinity.WordPairing` show that it is not a coboundary
as soon as `∑ w, a w * c w ≠ 0` for weights `a` on words of darts which are anticyclic and satisfy
the signless preprojective relation in every pair of consecutive positions. This file proves the
converse over a field: if every such pairing vanishes on `c`, the loop operation is the Hochschild
differential of a suspended cochain of degree zero concentrated in arity `n + 1`. So the word
pairings detect exactly the Hochschild classes of loop operations. This is a step towards Liu and
Wang's comparison of zigzag Hochschild cohomology with the cyclic quotient of the preprojective
algebra; identifying the weights with functionals on that cyclic quotient, and treating Hochschild
classes other than those of loop operations, is not done here.

## Coordinate cochains

The proof works with the cochains `C_{β, z}(x₀, …) = κ_{β 0}(x₀) ⋯ κ_{β (r-1)}(x_{r-1}) · z`, for
`κ_b` the coordinates in the vertex-arrow-volume basis; loop operations are of this form. When `β`
is a walk of arrows and volume classes, the coboundary of `C_{β, z}` telescopes, as the coordinate
of a product splits off the idempotents at the ends of each slot. The surviving terms give two
families of coboundaries: for a walk `u` and an arrow `b` parallel to it, the sum of the loop
operations of `(u, b.symm)` and its rotation `(b.symm, u)`; and for a closed word with one volume
class `x_v` in a slot, the sum of the loop operations of the words with `x_v` replaced by a
backtrack `d, d.symm` at `v`. These span the relations dual to the two conditions on the weights,
and a linear-algebra duality over a field gives the converse.

## Main results

* `TauCeti.exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_iff`: over a
  field, a loop operation of arity at least three is a Hochschild coboundary exactly when every
  word pairing with anticyclic weights satisfying the signless relations vanishes on it.

## References

* Y. Liu and Z. Wang, *A-infinity deformations of zigzag algebras via Ginzburg dg algebras*,
  https://arxiv.org/abs/2301.06757, Sections 3 and 4, for the comparison of zigzag Hochschild
  cohomology with the cyclic quotient of the preprojective algebra.
* R. S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 4, for the
  quadratic dual of the zigzag algebra.
* J.-L. Loday, *Cyclic Homology*, Chapter 1, for Hochschild chains and cochains and their duality.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver AInfinity ReducedTensorWords

universe u w

/-! ### Words of darts -/

section Words

variable {V : Type u} {G : SimpleGraph V}

/-- A word of darts, extended to the natural numbers by a default dart. -/
private def natExt {m : ℕ} (w : Fin m → G.Dart) (d₀ : G.Dart) (i : ℕ) : G.Dart :=
  if h : i < m then w ⟨i, h⟩ else d₀

/-- Below the length, the extended word reads the word. -/
private theorem natExt_of_lt {m : ℕ} (w : Fin m → G.Dart) (d₀ : G.Dart) {i : ℕ} (h : i < m) :
    natExt w d₀ i = w ⟨i, h⟩ := by
  simp [natExt, h]

/-- At the length, the extended word reads the default dart. -/
private theorem natExt_self {m : ℕ} (w : Fin m → G.Dart) (d₀ : G.Dart) : natExt w d₀ m = d₀ := by
  simp [natExt]

/-- The darts of `natExt u d` below the length of `u` do not depend on the default. -/
private theorem natExt_eq_natExt {m : ℕ} (u : Fin m → G.Dart) (d d' : G.Dart) {i : ℕ}
    (hi : i < m) : natExt u d i = natExt u d' i := by
  rw [natExt_of_lt _ _ hi, natExt_of_lt _ _ hi]

/-- A word of `n + 2` darts read at the natural number `n + 2` gives back its first dart. -/
private theorem natExt_self_eq_natExt_zero {n : ℕ} (w : Fin (n + 2) → G.Dart) :
    natExt w (w 0) (n + 2) = natExt w (w 0) 0 := by
  rw [natExt_self, natExt_of_lt _ _ (by omega), Fin.mk_zero]

/-- A word of darts is closed: each dart starts where the next one, in product order, ends. -/
private def IsClosedWord {N : ℕ} [NeZero N] (w : Fin N → G.Dart) : Prop :=
  ∀ i, (w i).fst = (w (i + 1)).snd

/-- The word `u` with the backtrack `d, d.symm` inserted at the positions `p` and `p + 1`. -/
private def backtrackWord {n : ℕ} (p : Fin (n + 1)) (d : G.Dart) (u : Fin n → G.Dart) :
    Fin (n + 2) → G.Dart :=
  Fin.insertNth p.castSucc d (Fin.insertNth p d.symm u)

/-- A word of darts closes up exactly when its extension to the natural numbers does. -/
private theorem isClosedWord_iff_natExt {N : ℕ} [NeZero N] (w : Fin N → G.Dart) :
    IsClosedWord w ↔ ∀ i < N, (natExt w (w 0) i).fst = (natExt w (w 0) (i + 1)).snd := by
  unfold IsClosedWord
  have hsucc (i : ℕ) (hi : i < N) (hi' : i + 1 < N) : (⟨i, hi⟩ + 1 : Fin N) = ⟨i + 1, hi'⟩ :=
    Fin.ext (by simp [Fin.val_add, Nat.mod_eq_of_lt hi'])
  have hlast (i : ℕ) (hi : i < N) (hi' : i + 1 = N) : (⟨i, hi⟩ + 1 : Fin N) = 0 :=
    Fin.ext (by simp [Fin.val_add, hi'])
  constructor
  · intro h i hi
    rw [natExt_of_lt w _ hi, h ⟨i, hi⟩]
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt hi) with hi' | hi'
    · rw [natExt_of_lt w _ hi', hsucc i hi hi']
    · rw [hlast i hi hi', show natExt w (w 0) (i + 1) = w 0 by
        rw [show i + 1 = N from hi']; exact natExt_self w _]
  · intro h i
    have := h i i.isLt
    rw [natExt_of_lt w _ i.isLt] at this
    rw [this]
    rcases lt_or_eq_of_le (Nat.succ_le_of_lt i.isLt) with hi' | hi'
    · rw [natExt_of_lt w _ hi', ← hsucc i i.isLt hi']
    · rw [show natExt w (w 0) (i + 1) = w 0 by rw [show i + 1 = N from hi']; exact natExt_self w _,
        ← hlast i i.isLt hi']

/-- Closedness is invariant under rotation. -/
private theorem isClosedWord_comp_add_iff {N : ℕ} [NeZero N] (w : Fin N → G.Dart) (c : Fin N) :
    IsClosedWord (fun i ↦ w (i + c)) ↔ IsClosedWord w := by
  simp only [IsClosedWord]
  rw [← (Equiv.subRight c).forall_congr_right]
  simp [add_right_comm]

/-- The extension of a word with a dart appended at the end. -/
private theorem natExt_snoc {m : ℕ} (u : Fin m → G.Dart) (e d₀ : G.Dart) {i : ℕ}
    (hi : i < m + 1) :
    natExt (Fin.snoc u e : Fin (m + 1) → G.Dart) d₀ i = if i < m then natExt u e i else e := by
  rw [natExt_of_lt _ _ hi]
  split_ifs with h
  · rw [natExt_of_lt _ _ h]
    exact Fin.snoc_castSucc (α := fun _ ↦ G.Dart) (i := ⟨i, h⟩) ..
  · rw [show (⟨i, hi⟩ : Fin (m + 1)) = Fin.last m from Fin.ext (by simp; omega)]
    exact Fin.snoc_last (α := fun _ ↦ G.Dart) ..

/-- The extension of a word with a dart prepended at the front. -/
private theorem natExt_cons {m : ℕ} (u : Fin m → G.Dart) (e d₀ : G.Dart) {i : ℕ}
    (hi : i < m + 1) :
    natExt (Fin.cons e u : Fin (m + 1) → G.Dart) d₀ i =
      if i = 0 then e else natExt u e (i - 1) := by
  rw [natExt_of_lt _ _ hi]
  rcases i with _ | i
  · exact Fin.cons_zero (α := fun _ ↦ G.Dart) ..
  · rw [ite_eq_right (Nat.succ_ne_zero i), Nat.add_sub_cancel, natExt_of_lt _ _ (by omega)]
    exact Fin.cons_succ (α := fun _ ↦ G.Dart) (i := ⟨i, by omega⟩) ..

/-- A word closes up exactly when its rotation by one step does. -/
private theorem isClosedWord_snoc_iff {n : ℕ} (u : Fin (n + 1) → G.Dart) (e : G.Dart) :
    IsClosedWord (Fin.snoc u e : Fin (n + 2) → G.Dart) ↔
      IsClosedWord (Fin.cons e u : Fin (n + 2) → G.Dart) := by
  have h : (Fin.snoc u e : Fin (n + 2) → G.Dart) =
      fun i ↦ (Fin.cons e u : Fin (n + 2) → G.Dart) (i + 1) := funext fun i ↦ by
    rw [Fin.snoc_eq_cons_rotate]
    simp only [finRotate_apply]
  rw [h]
  exact isClosedWord_comp_add_iff (Fin.cons e u : Fin (n + 2) → G.Dart) 1

/-- The word with the backtrack `d, d.symm` inserted at the positions `p` and `p + 1`. -/
private theorem natExt_backtrackWord {n : ℕ} (p : Fin (n + 1)) (d : G.Dart)
    (u : Fin n → G.Dart) (d₀ : G.Dart) {i : ℕ} (hi : i < n + 2) :
    natExt (backtrackWord p d u) d₀ i =
      if i < p then natExt u d i else if i = p then d else if i = p + 1 then d.symm
        else natExt u d (i - 2) := by
  rw [natExt_of_lt _ _ hi, backtrackWord]
  rcases lt_trichotomy i p with h | rfl | h
  · rw [Fin.insertNth_apply_below (show (⟨i, hi⟩ : Fin (n + 2)) < p.castSucc from h)]
    simp only [eq_rec_constant, h, ↓reduceIte]
    rw [Fin.insertNth_apply_below (show Fin.castPred ⟨i, hi⟩ _ < p from h), eq_rec_constant,
      natExt_of_lt _ _ (by omega)]
    exact congrArg u (Fin.ext (by simp))
  · rw [show (⟨p, hi⟩ : Fin (n + 2)) = p.castSucc from Fin.ext (by simp), Fin.insertNth_apply_same]
    simp
  · rw [Fin.insertNth_apply_above (show p.castSucc < (⟨i, hi⟩ : Fin (n + 2)) from h)]
    simp only [eq_rec_constant, show ¬ i < p by omega, show i ≠ p by omega, ↓reduceIte]
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
    · rw [show Fin.pred ⟨i, hi⟩ _ = p from Fin.ext (by simp; omega), Fin.insertNth_apply_same,
        ite_eq_left h'.symm]
    · rw [Fin.insertNth_apply_above (show p < Fin.pred ⟨i, hi⟩ _ from
        Fin.lt_def.2 (by simp; omega)), eq_rec_constant, ite_eq_right (by omega),
        natExt_of_lt _ _ (by omega)]
      congr 1

/-- **Closedness of a backtrack insertion only depends on the head of the backtrack.** -/
private theorem isClosedWord_backtrackWord {n : ℕ} (p : Fin (n + 1)) (u : Fin n → G.Dart)
    {d₀ d : G.Dart} (hd : d.snd = d₀.snd) (h : IsClosedWord (backtrackWord p d₀ u)) :
    IsClosedWord (backtrackWord p d u) := by
  set w₀ := backtrackWord p d₀ u
  set w := backtrackWord p d u
  have hW₀ := (isClosedWord_iff_natExt w₀).1 h
  rw [isClosedWord_iff_natExt]
  have hp := p.isLt
  -- The two words agree off the backtrack, up to its head.
  have hsnd : ∀ j ≤ n + 2, j ≠ p + 1 → (natExt w (w 0) j).snd = (natExt w₀ (w₀ 0) j).snd := by
    have key : ∀ j < n + 2, j ≠ p + 1 → (natExt w (w 0) j).snd = (natExt w₀ (w₀ 0) j).snd :=
      fun j hj hjp ↦ by
        rw [natExt_backtrackWord p d u _ hj, natExt_backtrackWord p d₀ u _ hj]
        split_ifs with h₁ h₂
        · rw [natExt_eq_natExt u d d₀ (by omega)]
        · exact hd
        · rw [natExt_eq_natExt u d d₀ (by omega)]
    intro j hj hjp
    rcases lt_or_eq_of_le hj with hj | rfl
    · exact key j hj hjp
    · rw [natExt_self_eq_natExt_zero, natExt_self_eq_natExt_zero]
      exact key 0 (by omega) (by omega)
  have hfst : ∀ j < n + 2, j ≠ p → j ≠ p + 1 →
      (natExt w (w 0) j).fst = (natExt w₀ (w₀ 0) j).fst := fun j hj hjp hjp' ↦ by
    rw [natExt_backtrackWord p d u _ hj, natExt_backtrackWord p d₀ u _ hj]
    split_ifs with h₁
    · rw [natExt_eq_natExt u d d₀ (by omega)]
    · rw [natExt_eq_natExt u d d₀ (by omega)]
  intro i hi
  by_cases hip : i = p
  · subst hip
    rw [natExt_backtrackWord p d u _ hi, natExt_backtrackWord p d u _ (by omega)]
    simp
  by_cases hip' : i = p + 1
  · subst hip'
    have h₁ := hW₀ (p + 1) hi
    rw [natExt_backtrackWord p d₀ u _ hi] at h₁
    rw [natExt_backtrackWord p d u _ hi, hsnd (p + 2) (by omega) (by omega)]
    simp only [show ¬ (p : ℕ) + 1 < p by omega, show (p : ℕ) + 1 ≠ p by omega, ↓reduceIte] at h₁ ⊢
    rw [← h₁]
    simp [hd]
  · rw [hfst i hi hip hip', hW₀ i hi, hsnd (i + 1) (by omega) (by omega)]

/-- The basis index `b` sits in a slot from `t` to `s` of a word, read in product order: it is the
arrow of a dart from `t` to `s`, or the volume class at `s = t`. -/
private def IsSlot (s t : V) : ZigzagBasisIndex G → Prop
  | .inl _ => False
  | .inr (.inl d) => d.snd = s ∧ d.fst = t
  | .inr (.inr v) => v = s ∧ v = t

/-- The sign of the prefix of length `p` of a word of basis indices. -/
private def prefixSign (k : Type*) [CommRing k] (β : ℕ → ZigzagBasisIndex G) (p : ℕ) : k :=
  negOnePowCast k (∑ j ∈ Finset.range p, (zigzagBasisDegree G (β j) - 1))

/-- The word `β` with the slot `p` replaced by the backtrack `d, d.symm`. -/
private def insertBacktrack (β : ℕ → ZigzagBasisIndex G) (p : ℕ) (d : G.Dart) :
    ℕ → ZigzagBasisIndex G := fun i ↦
  if i < p then β i else if i = p then .inr (.inl d) else if i = p + 1 then .inr (.inl d.symm)
    else β (i - 1)

/-- The slot word of a word `W` carrying a backtrack at the positions `p` and `p + 1`: the darts of
`W`, with the backtrack replaced by the volume class at its head `v`. -/
private def relatorWord (W : ℕ → G.Dart) (p : ℕ) (v : V) : ℕ → ZigzagBasisIndex G := fun i ↦
  if i < p then .inr (.inl (W i)) else if i = p then .inr (.inr v) else .inr (.inl (W (i + 1)))

/-- The vertices through which the slot word `relatorWord W p v` passes. -/
private def relatorVertex (W : ℕ → G.Dart) (p : ℕ) : ℕ → V := fun i ↦
  if i ≤ p then (W i).snd else (W (i + 1)).snd

/-- The slot word of a closed word carrying the backtrack `d₀, d₀.symm` at the positions `p` and
`p + 1` is a walk of arrows and one volume class. -/
private theorem isSlot_relatorWord {n p : ℕ} {W : ℕ → G.Dart} {d₀ : G.Dart}
    (hW : ∀ i < n + 2, (W i).fst = (W (i + 1)).snd) (hWp : W p = d₀)
    (hWp' : W (p + 1) = d₀.symm) (hp : p ≤ n) :
    ∀ i ≤ n, IsSlot (relatorVertex W p i) (relatorVertex W p (i + 1)) (relatorWord W p d₀.snd i) :=
  fun i hi ↦ by
    rcases lt_trichotomy i p with h₁ | rfl | h₁
    · simp only [relatorWord, relatorVertex, h₁, ↓reduceIte, h₁.le, show i + 1 ≤ p by omega]
      exact ⟨rfl, hW i (by omega)⟩
    · simp only [relatorWord, relatorVertex, lt_irrefl, ↓reduceIte, le_refl,
        show ¬ i + 1 ≤ i by omega]
      refine ⟨by rw [hWp], ?_⟩
      rw [← hW (i + 1) (by omega), hWp', SimpleGraph.Dart.fst_symm]
    · simp only [relatorWord, relatorVertex, show ¬ i < p by omega, show i ≠ p by omega,
        ↓reduceIte, show ¬ i ≤ p by omega, show ¬ i + 1 ≤ p by omega]
      exact ⟨rfl, hW (i + 1) (by omega)⟩

/-- Replacing the volume slot of the slot word of a backtrack insertion by another backtrack with
the same head gives back the word of that insertion. -/
private theorem insertBacktrack_relatorWord {n : ℕ} (p : Fin (n + 1)) (u : Fin n → G.Dart)
    (d₀ d : G.Dart) {i : ℕ} (hi : i < n + 2) :
    insertBacktrack (relatorWord (natExt (backtrackWord p d₀ u) (backtrackWord p d₀ u 0)) p d₀.snd)
        p d i =
      .inr (.inl (natExt (backtrackWord p d u) (backtrackWord p d u 0) i)) := by
  rw [natExt_backtrackWord p d u _ hi]
  simp only [insertBacktrack, relatorWord]
  rcases lt_trichotomy i p with h₁ | rfl | h₁
  · simp only [h₁, ↓reduceIte]
    rw [natExt_backtrackWord p d₀ u _ hi]
    simp only [h₁, ↓reduceIte]
    rw [natExt_eq_natExt u d₀ d (by omega)]
  · simp
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h₁) with h₂ | h₂
    · subst h₂
      simp
    · simp only [show ¬ i < p by omega, show i ≠ p by omega, show i ≠ p + 1 by omega,
        show ¬ i - 1 < p by omega, show i - 1 ≠ p by omega, ↓reduceIte,
        Nat.sub_add_cancel (show 1 ≤ i by omega)]
      rw [natExt_backtrackWord p d₀ u _ hi]
      simp only [show ¬ i < p by omega, show i ≠ p by omega, show i ≠ p + 1 by omega,
        ↓reduceIte]
      rw [natExt_eq_natExt u d₀ d (by omega)]

/-- The base vertex of the slot word of a backtrack insertion is the base vertex of every backtrack
insertion with the same head. -/
private theorem relatorVertex_zero {n : ℕ} (p : Fin (n + 1)) (u : Fin n → G.Dart) {d₀ d : G.Dart}
    (hd : d.snd = d₀.snd) :
    relatorVertex (natExt (backtrackWord p d₀ u) (backtrackWord p d₀ u 0)) p 0 =
      (backtrackWord p d u 0).snd := by
  simp only [relatorVertex, Nat.zero_le, ↓reduceIte]
  have hw0 : backtrackWord p d u 0 = natExt (backtrackWord p d u) (backtrackWord p d u 0) 0 := by
    rw [natExt_of_lt _ _ (show 0 < n + 2 by omega), Fin.mk_zero]
  rw [hw0, natExt_backtrackWord p d₀ u _ (by omega),
    natExt_backtrackWord p d u _ (by omega)]
  split_ifs with h₁ h₂
  · rw [natExt_eq_natExt u d₀ d (by omega)]
  · exact hd.symm
  all_goals exact (h₂ (by omega)).elim

end Words

/-! ### Coordinates in the vertex-arrow-volume basis -/

section Coordinates

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "κ" => Module.Basis.coord (zigzagBasis k G hns)

/-- On a homogeneous element, a Koszul sign only matters through the degree of the coordinate read
off it. -/
private theorem negOnePowCast_mul_zigzagBasis_coord_of_mem (b : ZigzagBasisIndex G) {e : ℤ}
    (q : ℤ)
    {x : nonisolatedZigzagQuotient k G} (hx : x ∈ zigzagIntegerGrade k G e) :
    negOnePowCast k (q * e) * κ b x = negOnePowCast k (q * zigzagBasisDegree G b) * κ b x := by
  by_cases he : e = zigzagBasisDegree G b
  · rw [he]
  · rw [zigzagBasis_coord_eq_zero_of_mem_zigzagIntegerGrade k G hns b he hx, mul_zero, mul_zero]

end Coordinates

/-! ### Coordinate cochains and their coboundaries -/

section CoordCochain

variable {k : Type w} [CommRing k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j}

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

local notation "κ" => Module.Basis.coord (zigzagBasis k G hns)

local notation "𝔞" d:max => zigzagMk k G (ofArrow (arrow G (SimpleGraph.Dart.adj d)))

variable (hns) in
/-- The cochain of arity `r` which multiplies the `β i`-coordinates of its inputs and scales `z`
by the product. -/
private noncomputable def coordCochain (r : ℕ) (hr : 0 < r) (β : ℕ → ZigzagBasisIndex G)
    (z : nonisolatedZigzagQuotient k G) :
    ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G :=
  PiTensorProduct.lift (((MultilinearMap.mkPiAlgebra k (Fin r) k).compLinearMap
    fun i : Fin r ↦ κ (β i)).smulRight z) ∘ₗ component k _ ⟨r, hr⟩

/-- A coordinate cochain on a word of its own arity. -/
private theorem coordCochain_of_tprod {r : ℕ} (hr : 0 < r) (β : ℕ → ZigzagBasisIndex G)
    (z : nonisolatedZigzagQuotient k G) (y : Fin r → nonisolatedZigzagQuotient k G) :
    coordCochain hns r hr β z (of k _ ⟨r, hr⟩ (PiTensorProduct.tprod k y)) =
      (∏ i : Fin r, κ (β i) (y i)) • z := by
  rw [coordCochain, LinearMap.comp_apply, ReducedTensorWords.component_of]
  simp

/-- A coordinate cochain on the word of the first `r` letters of a natural-indexed family. -/
private theorem coordCochain_of_tprod_nat {r : ℕ} (hr : 0 < r) (β : ℕ → ZigzagBasisIndex G)
    (z : nonisolatedZigzagQuotient k G) (x : ℕ → nonisolatedZigzagQuotient k G) :
    coordCochain hns r hr β z (of k _ ⟨r, hr⟩ (PiTensorProduct.tprod k fun j : Fin r ↦ x j)) =
      (∏ i ∈ Finset.range r, κ (β i) (x i)) • z := by
  rw [coordCochain_of_tprod, Fin.prod_univ_eq_prod_range (fun i ↦ κ (β i) (x i)) r]

/-- A coordinate cochain vanishes on the words of every other length. -/
private theorem coordCochain_of_ne {r : ℕ} (hr : 0 < r) (β : ℕ → ZigzagBasisIndex G)
    (z : nonisolatedZigzagQuotient k G) {m : {m : ℕ // 0 < m}} (hm : m ≠ ⟨r, hr⟩)
    (w : TensorPower k m.val (nonisolatedZigzagQuotient k G)) :
    coordCochain hns r hr β z (of k _ m w) = 0 := by
  simp [coordCochain, component_of_of_ne k _ hm]

/-- A coordinate cochain is concentrated in its arity. -/
private theorem coordCochain_comp_lengthProj {r : ℕ} (hr : 0 < r) (β : ℕ → ZigzagBasisIndex G)
    (z : nonisolatedZigzagQuotient k G) :
    coordCochain hns r hr β z ∘ₗ lengthProj k _ ⟨r, hr⟩ = coordCochain hns r hr β z := by
  refine LinearMap.ext fun w ↦ ?_
  simp only [coordCochain, LinearMap.comp_apply, lengthProj_apply]
  rw [ReducedTensorWords.component_of]

/-- A coordinate cochain of arity `r` only reads the first `r` indices of its word. -/
private theorem coordCochain_congr {r : ℕ} (hr : 0 < r) {β β' : ℕ → ZigzagBasisIndex G}
    (h : ∀ i < r, β i = β' i) (z : nonisolatedZigzagQuotient k G) :
    coordCochain hns r hr β z = coordCochain hns r hr β' z := by
  have : (fun i : Fin r ↦ κ (β i)) = fun i : Fin r ↦ κ (β' i) := funext fun i ↦ by rw [h i i.isLt]
  simp only [coordCochain, this]

/-- A coordinate cochain is homogeneous: its suspended degree `q` is the degree of `z`, shifted,
minus the shifted degrees of the coordinates it reads. -/
private theorem isHomogeneous_coordCochain {r : ℕ} (hr : 0 < r) (β : ℕ → ZigzagBasisIndex G)
    {z : nonisolatedZigzagQuotient k G} {e : ℤ} (hz : z ∈ zigzagIntegerGrade k G e) (q : ℤ)
    (hq : e - 1 = ∑ i ∈ Finset.range r, (zigzagBasisDegree G (β i) - 1) + q) :
    LinearMap.IsHomogeneous (coordCochain hns r hr β z) (gradedPiece ((𝒵).grading.shift 1))
      ((𝒵).grading.shift 1).piece q := by
  rw [LinearMap.isHomogeneous_def]
  intro D w hw
  refine gradedPiece_induction
    (motive := fun w ↦ coordCochain hns r hr β z w ∈ ((𝒵).grading.shift 1).piece (D + q)) hw
    ?_ ?_ ?_
  · intro n hn d x hx hD
    simp only [InternalGrading.shift_piece, zigzagStrictAInfinityAlgebra_grading_piece] at hx ⊢
    by_cases hnr : n = r
    · subst hnr
      rw [coordCochain_of_tprod]
      by_cases hdeg : ∀ i, d i + 1 = zigzagBasisDegree G (β i)
      · refine Submodule.smul_mem _ _ ?_
        convert hz using 2
        have hsum : ∑ i, d i = ∑ i ∈ Finset.range n, (zigzagBasisDegree G (β i) - 1) := by
          rw [← Fin.sum_univ_eq_sum_range (fun i ↦ zigzagBasisDegree G (β i) - 1) n]
          exact Finset.sum_congr rfl fun i _ ↦ by have := hdeg i; omega
        rw [← hD, hsum]
        omega
      · obtain ⟨i, hi⟩ := not_forall.mp hdeg
        rw [Finset.prod_eq_zero (Finset.mem_univ i)
          (zigzagBasis_coord_eq_zero_of_mem_zigzagIntegerGrade k G hns (β i) hi (hx i)), zero_smul]
        exact Submodule.zero_mem _
    · rw [coordCochain_of_ne hr β z fun h ↦ hnr (congrArg Subtype.val h)]
      exact Submodule.zero_mem _
  · intro u v _ _ hu hv
    rw [map_add]
    exact Submodule.add_mem _ hu hv
  · intro a u _ hu
    rw [map_smul]
    exact Submodule.smul_mem _ _ hu

/-- Two cochains concentrated on the words of length `N` agree as soon as they agree on the words
of homogeneous letters. -/
private theorem eq_of_forall_of_tprod {N : ℕ} (hN : 0 < N)
    {F F' : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
      nonisolatedZigzagQuotient k G}
    (hF : F ∘ₗ lengthProj k _ ⟨N, hN⟩ = F) (hF' : F' ∘ₗ lengthProj k _ ⟨N, hN⟩ = F')
    (h : ∀ (x : ℕ → nonisolatedZigzagQuotient k G) (d : ℕ → ℤ),
      (∀ i < N, x i ∈ zigzagIntegerGrade k G (d i)) →
        F (of k _ ⟨N, hN⟩ (PiTensorProduct.tprod k fun j : Fin N ↦ x j)) =
          F' (of k _ ⟨N, hN⟩ (PiTensorProduct.tprod k fun j : Fin N ↦ x j))) :
    F = F' := by
  have hN' : F ∘ₗ of k _ ⟨N, hN⟩ = F' ∘ₗ of k _ ⟨N, hN⟩ := by
    apply InternalGrading.piTensorProduct_ext
      (fun _ ↦ (⟨zigzagIntegerGrade k G, isInternal_zigzagIntegerGrade k G⟩ :
        InternalGrading k (nonisolatedZigzagQuotient k G) ℤ))
    intro q
    have hq := h (fun i ↦ if hi : i < N then (q ⟨i, hi⟩).snd else 0)
      (fun i ↦ if hi : i < N then (q ⟨i, hi⟩).fst else 0) fun i hi ↦ by
        simp only [hi, dite_true]
        exact (q ⟨i, hi⟩).snd.property
    simpa only [LinearMap.comp_apply, Fin.is_lt, dite_true, Fin.eta] using hq
  rw [← hF, ← hF']
  refine linearMap_ext k _ fun m y ↦ ?_
  simp only [LinearMap.comp_apply, lengthProj_apply]
  by_cases hm : m = ⟨N, hN⟩
  · subst hm
    rw [ReducedTensorWords.component_of]
    exact LinearMap.congr_fun hN' _
  · rw [component_of_of_ne k _ hm, map_zero, map_zero, map_zero]

/-- The Taylor map of the strict zigzag algebra is concentrated on the words of length two. -/
private theorem zigzagStrictAInfinityAlgebra_taylor_comp_lengthProj_two :
    (𝒵).taylor ∘ₗ lengthProj k _ ⟨2, two_pos⟩ = (𝒵).taylor :=
  AInfinityAlgebra.IsMinimal.taylor_comp_lengthProj_two isMinimal_zigzagStrictAInfinityAlgebra
    fun _ h ↦ zigzagStrictAInfinityAlgebra_m_eq_zero (by omega)

/-- The coboundary of a coordinate cochain concentrated in one arity is concentrated in the next
one. -/
private theorem hochschildDifferential_coordCochain_comp_lengthProj {n : ℕ}
    (β : ℕ → ZigzagBasisIndex G) (z : nonisolatedZigzagQuotient k G) :
    (𝒵).hochschildDifferential 0 (coordCochain hns (n + 1) n.succ_pos β z) ∘ₗ
        lengthProj k _ ⟨n + 2, by omega⟩ =
      (𝒵).hochschildDifferential 0 (coordCochain hns (n + 1) n.succ_pos β z) :=
  AInfinityAlgebra.hochschildDifferential_comp_lengthProj
    zigzagStrictAInfinityAlgebra_taylor_comp_lengthProj_two 0
    (coordCochain_comp_lengthProj n.succ_pos β z)

/-- The Koszul signs of a prefix of homogeneous letters only matter through the degrees of the
coordinates read off them. -/
private theorem negOnePowCast_sum_mul_prod (β : ℕ → ZigzagBasisIndex G)
    (x : ℕ → nonisolatedZigzagQuotient k G) (d : ℕ → ℤ) {p : ℕ}
    (hx : ∀ i < p, x i ∈ zigzagIntegerGrade k G (d i)) :
    negOnePowCast k (∑ j ∈ Finset.range p, (d j - 1)) * ∏ i ∈ Finset.range p, κ (β i) (x i) =
      negOnePowCast k (∑ j ∈ Finset.range p, (zigzagBasisDegree G (β j) - 1)) *
        ∏ i ∈ Finset.range p, κ (β i) (x i) := by
  induction p with
  | zero => simp
  | succ p ih =>
    have h := negOnePowCast_mul_zigzagBasis_coord_of_mem (k := k) (hns := hns) (β p) 1
      (hx p (by omega))
    simp only [one_mul] at h
    have hsub (a : ℤ) : negOnePowCast k (a - 1) = negOnePowCast k a * negOnePowCast k 1 := by
      rw [sub_eq_add_neg, negOnePowCast_add, negOnePowCast_neg]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.prod_range_succ, negOnePowCast_add,
      negOnePowCast_add, hsub, hsub]
    have ih' := ih fun i hi ↦ hx i (by omega)
    calc _ = (negOnePowCast k (∑ j ∈ Finset.range p, (d j - 1)) *
          ∏ i ∈ Finset.range p, κ (β i) (x i)) * (negOnePowCast k (d p) * κ (β p) (x p)) *
            negOnePowCast k 1 := by ring
      _ = _ := by rw [ih', h]; ring

variable (hns) in
/-- The `q`-th telescoping term of the coboundary of a coordinate cochain of arity `n + 1`: the
coordinates of the word with the idempotent at the `q`-th vertex inserted. -/
private noncomputable def telescopeTerm (β : ℕ → ZigzagBasisIndex G) (vtx : ℕ → V)
    (x : ℕ → nonisolatedZigzagQuotient k G) (n q : ℕ) : k :=
  (∏ i ∈ Finset.range q, κ (β i) (x i)) * κ (.inl (vtx q)) (x q) *
    ∏ i ∈ Finset.Ico q (n + 1), κ (β i) (x (i + 1))

/-- The coordinates of a word with the block at `p` collapsed. -/
private theorem prod_coord_replaceBlock (β : ℕ → ZigzagBasisIndex G)
    (x : ℕ → nonisolatedZigzagQuotient k G) {n p : ℕ} (hp : p < n + 1)
    (e : nonisolatedZigzagQuotient k G) :
    ∏ i ∈ Finset.range (n + 1), κ (β i) (replaceBlock x p 2 e i) =
      (∏ i ∈ Finset.range p, κ (β i) (x i)) * κ (β p) e *
        ∏ i ∈ Finset.Ico (p + 1) (n + 1), κ (β i) (x (i + 1)) := by
  rw [← Finset.prod_range_mul_prod_Ico _ hp.le, Finset.prod_eq_prod_Ico_succ_bot hp,
    replaceBlock_self, ← mul_assoc]
  refine congrArg₂ _ (congrArg₂ _ (Finset.prod_congr rfl fun i hi ↦ ?_) rfl)
    (Finset.prod_congr rfl fun i hi ↦ ?_)
  · rw [replaceBlock_of_lt _ _ _ _ (Finset.mem_range.1 hi)]
  · rw [Finset.mem_Ico] at hi
    rw [replaceBlock_of_gt _ _ _ _ (by omega), show i + 2 - 1 = i + 1 by omega]

/-- The coordinates of a word with a backtrack inserted. -/
private theorem prod_coord_insertBacktrack (β : ℕ → ZigzagBasisIndex G) {n p : ℕ} (hp : p ≤ n)
    (d : G.Dart) (x : ℕ → nonisolatedZigzagQuotient k G) :
    ∏ i ∈ Finset.range (n + 2), κ (insertBacktrack β p d i) (x i) =
      (∏ i ∈ Finset.range p, κ (β i) (x i)) *
        (κ (.inr (.inl d)) (x p) * κ (.inr (.inl d.symm)) (x (p + 1))) *
          ∏ i ∈ Finset.Ico (p + 1) (n + 1), κ (β i) (x (i + 1)) := by
  rw [← Finset.prod_range_mul_prod_Ico _ (show p ≤ n + 2 by omega),
    Finset.prod_eq_prod_Ico_succ_bot (show p < n + 2 by omega),
    Finset.prod_eq_prod_Ico_succ_bot (show p + 1 < n + 2 by omega),
    ← Finset.prod_Ico_add' (fun i ↦ κ (insertBacktrack β p d i) (x i)) (p + 1) (n + 1) 1]
  simp only [insertBacktrack, lt_irrefl, ↓reduceIte, show ¬ p + 1 < p by omega,
    show p + 1 ≠ p by omega]
  rw [mul_assoc, mul_assoc]
  refine congrArg₂ _ (Finset.prod_congr rfl fun i hi ↦ ?_) (congrArg₂ _ rfl
    (congrArg₂ _ rfl (Finset.prod_congr rfl fun i hi ↦ ?_)))
  · simp [Finset.mem_range.1 hi]
  · rw [Finset.mem_Ico] at hi
    simp only [show ¬ i + 1 < p by omega, show i + 1 ≠ p by omega, show i + 1 ≠ p + 1 by omega,
      ↓reduceIte, Nat.add_sub_cancel]

variable (hns) in
/-- The loop cochain of a word of `n + 2` darts. -/
private noncomputable def loopCochain {n : ℕ} (w : Fin (n + 2) → G.Dart) :
    ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G :=
  coordCochain hns (n + 2) (by omega) (fun i ↦ .inr (.inl (natExt w (w 0) i)))
    (zigzagVolume k G (w 0).snd)

variable (k hns) in
/-- The admissible primitives: suspended cochains of degree zero concentrated in arity `n + 1`. -/
private def IsZigzagCoboundary (n : ℕ)
    (F : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
      nonisolatedZigzagQuotient k G) : Prop :=
  ∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k] nonisolatedZigzagQuotient k G,
    LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1)) ((𝒵).grading.shift 1).piece 0 ∧
      φ ∘ₗ lengthProj k _ ⟨n + 1, n.succ_pos⟩ = φ ∧ (𝒵).hochschildDifferential 0 φ = F

/-- Zero is a coboundary. -/
private theorem isZigzagCoboundary_zero (n : ℕ) : IsZigzagCoboundary k hns n 0 :=
  ⟨0, LinearMap.isHomogeneous_zero _ _ _, by simp, AInfinityAlgebra.hochschildDifferential_zero _ _⟩

/-- Coboundaries are closed under addition. -/
private theorem IsZigzagCoboundary.add {n : ℕ} {F F'} (hF : IsZigzagCoboundary k hns n F)
    (hF' : IsZigzagCoboundary k hns n F') : IsZigzagCoboundary k hns n (F + F') := by
  obtain ⟨φ, hφ, hφl, rfl⟩ := hF
  obtain ⟨φ', hφ', hφl', rfl⟩ := hF'
  exact ⟨φ + φ', hφ.add hφ', by rw [LinearMap.add_comp, hφl, hφl'],
    AInfinityAlgebra.hochschildDifferential_add _ _ _ _⟩

/-- Coboundaries are closed under negation. -/
private theorem IsZigzagCoboundary.neg {n : ℕ} {F} (hF : IsZigzagCoboundary k hns n F) :
    IsZigzagCoboundary k hns n (-F) := by
  obtain ⟨φ, hφ, hφl, rfl⟩ := hF
  refine ⟨-φ, hφ.neg, by rw [LinearMap.neg_comp, hφl], ?_⟩
  have h := AInfinityAlgebra.hochschildDifferential_add (𝒵) 0 φ (-φ)
  rw [add_neg_cancel, AInfinityAlgebra.hochschildDifferential_zero] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

/-- Coboundaries are closed under scalar multiplication. -/
private theorem IsZigzagCoboundary.smul {n : ℕ} {F} (hF : IsZigzagCoboundary k hns n F) (r : k) :
    IsZigzagCoboundary k hns n (r • F) := by
  obtain ⟨φ, hφ, hφl, rfl⟩ := hF
  exact ⟨r • φ, hφ.smul r, by rw [LinearMap.smul_comp, hφl],
    AInfinityAlgebra.hochschildDifferential_smul _ _ _ _⟩

/-- **The higher operation of a loop deformation** is, up to the sign of the suspension, the linear
combination of the loop cochains with coefficients `c`. -/
private theorem obstruction_zigzagLoopAInfinityAlgebra_eq {n : ℕ} (hn : 1 ≤ n)
    (c : (Fin (n + 2) → G.Dart) →₀ k) (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    (zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨n + 2, by omega⟩ =
      (((∏ i : Fin (n + 2), ((n + 1 - i : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) : k) •
        Finsupp.linearCombination k (loopCochain hns) c := by
  refine linearMap_ext k _ fun ⟨m, hm₀⟩ y ↦ ?_
  by_cases hm : m = n + 2
  · subst hm
    simp only [AInfinityAlgebra.obstruction_def, LinearMap.comp_apply, LinearMap.sub_apply,
      LinearMap.smul_apply]
    rw [lengthProj_of_self, AInfinityAlgebra.taylor_of_tprod, AInfinityAlgebra.taylor_of_tprod,
      zigzagStrictAInfinityAlgebra_m_eq_zero (by dsimp only; omega), _root_.zero_apply, sub_zero,
      zigzagLoopAInfinityAlgebra_m_eq_linearCombination _ _ (by omega),
      zigzagLoopAInfinityAlgebra_grading_eq_zigzagStrictAInfinityAlgebra_grading,
      Finsupp.linearCombination_apply, Finsupp.linearCombination_apply, Finsupp.sum, Finsupp.sum,
      LinearMap.sum_apply, _root_.sum_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun w _ ↦ ?_
    rw [_root_.smul_apply, LinearMap.smul_apply, zigzagLoopOperation_apply, loopCochain,
      coordCochain_of_tprod]
    simp only [smul_smul]
    congr 1
    simp only [zigzagBasis_coord_koszulTwist zigzagStrictAInfinityAlgebra_grading_piece,
      zigzagBasisDegree_inr_inl, mul_one, Finset.prod_mul_distrib, Units.coe_prod, Int.cast_prod]
    have hsign : ∏ i : Fin (n + 2), negOnePowCast k
        (((⟨n + 2, hm₀⟩ : {m : ℕ // 0 < m}) : ℕ) - 1 - ((i : ℕ) : ℤ)) =
        ∏ i : Fin (n + 2), ((((n + 1 - i : ℕ) : ℤ).negOnePow : ℤ) : k) :=
      Finset.prod_congr rfl fun i _ ↦ by
        rw [negOnePowCast_eq_intCast]
        congr 3
        dsimp only
        omega
    have hcoord : ∏ i : Fin (n + 2), κ (.inr (.inl (w i))) (y i) =
        ∏ i : Fin (n + 2), κ (.inr (.inl (natExt w (w 0) i))) (y i) :=
      Finset.prod_congr rfl fun i _ ↦ by rw [natExt_of_lt _ _ i.isLt]
    rw [hsign, hcoord]
    ring
  · have hm' : (⟨m, hm₀⟩ : {m : ℕ // 0 < m}) ≠ ⟨n + 2, by omega⟩ :=
      fun h ↦ hm (congrArg Subtype.val h)
    simp only [AInfinityAlgebra.obstruction_def, LinearMap.comp_apply, lengthProj_apply,
      component_of_of_ne k _ hm', map_zero, LinearMap.smul_apply, Finsupp.linearCombination_apply,
      Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, loopCochain]
    rw [Finset.sum_eq_zero fun w _ ↦ by rw [coordCochain_of_ne _ _ _ hm', smul_zero], smul_zero]

variable [Fintype G.Dart] [DecidableEq V]

variable (hns) in
/-- The backtrack part of the coordinate of a product at a volume slot. -/
private noncomputable def backtrackTerm (x y : nonisolatedZigzagQuotient k G) :
    ZigzagBasisIndex G → k
  | .inr (.inr v) => ∑ d : G.Dart with d.snd = v, κ (.inr (.inl d)) x * κ (.inr (.inl d.symm)) y
  | _ => 0

/-- The coordinate at a slot of the product of a twisted letter with a letter. -/
private theorem coord_koszulTwist_mul_of_isSlot {s t : V} {b : ZigzagBasisIndex G}
    (hb : IsSlot s t b) (x y : nonisolatedZigzagQuotient k G) :
    κ b ((𝒵).grading.koszulTwist 1 x * y) =
      κ (.inl s) x * κ b y + negOnePowCast k (zigzagBasisDegree G b) * κ b x * κ (.inl t) y -
        backtrackTerm hns x y b := by
  rcases b with i | d | v
  · exact hb.elim
  · obtain ⟨rfl, rfl⟩ := hb
    rw [zigzagBasis_coord_dart_mul]
    simp only [zigzagBasis_coord_koszulTwist zigzagStrictAInfinityAlgebra_grading_piece]
    simp [backtrackTerm]
  · obtain ⟨rfl, rfl⟩ := hb
    rw [zigzagBasis_coord_volume_mul]
    simp only [zigzagBasis_coord_koszulTwist zigzagStrictAInfinityAlgebra_grading_piece,
      zigzagBasisDegree_inl, zigzagBasisDegree_inr_inl, zigzagBasisDegree_inr_inr, backtrackTerm]
    simp [Finset.sum_neg_distrib]
    ring

/-- **The inner terms of the coboundary of a coordinate cochain telescope.** For a word `β` of
arrows and volume classes forming a walk through the vertices `vtx`, the signed sum of the
coordinates of the collapsed words reduces to the two extreme telescoping terms and the backtrack
terms of the volume slots. -/
private theorem sum_prefixSign_mul_prod_coord_replaceBlock {n : ℕ} (β : ℕ → ZigzagBasisIndex G)
    (vtx : ℕ → V) (hβ : ∀ i ≤ n, IsSlot (vtx i) (vtx (i + 1)) (β i))
    (x : ℕ → nonisolatedZigzagQuotient k G) (d : ℕ → ℤ)
    (hx : ∀ i < n + 2, x i ∈ zigzagIntegerGrade k G (d i)) :
    ∑ p ∈ Finset.range (n + 1), negOnePowCast k (∑ j ∈ Finset.range p, (d j - 1)) *
        ∏ i ∈ Finset.range (n + 1),
          κ (β i) (replaceBlock x p 2 ((𝒵).grading.koszulTwist 1 (x p) * x (p + 1)) i) =
      telescopeTerm hns β vtx x n 0 -
        prefixSign k β (n + 1) * telescopeTerm hns β vtx x n (n + 1) -
        ∑ p ∈ Finset.range (n + 1), prefixSign k β p *
          ((∏ i ∈ Finset.range p, κ (β i) (x i)) * backtrackTerm hns (x p) (x (p + 1)) (β p) *
            ∏ i ∈ Finset.Ico (p + 1) (n + 1), κ (β i) (x (i + 1))) := by
  have hterm : ∀ p ∈ Finset.range (n + 1),
      negOnePowCast k (∑ j ∈ Finset.range p, (d j - 1)) *
        ∏ i ∈ Finset.range (n + 1),
          κ (β i) (replaceBlock x p 2 ((𝒵).grading.koszulTwist 1 (x p) * x (p + 1)) i) =
      (prefixSign k β p * telescopeTerm hns β vtx x n p -
          prefixSign k β (p + 1) * telescopeTerm hns β vtx x n (p + 1)) -
        prefixSign k β p *
          ((∏ i ∈ Finset.range p, κ (β i) (x i)) * backtrackTerm hns (x p) (x (p + 1)) (β p) *
            ∏ i ∈ Finset.Ico (p + 1) (n + 1), κ (β i) (x (i + 1))) := by
    intro p hp
    rw [Finset.mem_range] at hp
    have hsign := negOnePowCast_sum_mul_prod (hns := hns) β x d (p := p)
      fun i hi ↦ hx i (by omega)
    have hsucc : prefixSign k β (p + 1) =
        -(prefixSign k β p * negOnePowCast k (zigzagBasisDegree G (β p))) := by
      rw [prefixSign, prefixSign, Finset.sum_range_succ, negOnePowCast_add, sub_eq_add_neg,
        negOnePowCast_add, negOnePowCast_neg, negOnePowCast_one]
      ring
    rw [prod_coord_replaceBlock β x hp, coord_koszulTwist_mul_of_isSlot (hβ p (by omega)),
      telescopeTerm, telescopeTerm, Finset.prod_range_succ, Finset.prod_eq_prod_Ico_succ_bot hp,
      hsucc, prefixSign]
    calc _ = (negOnePowCast k (∑ j ∈ Finset.range p, (d j - 1)) *
          ∏ i ∈ Finset.range p, κ (β i) (x i)) *
          (κ (.inl (vtx p)) (x p) * κ (β p) (x (p + 1)) +
            negOnePowCast k (zigzagBasisDegree G (β p)) * κ (β p) (x p) *
              κ (.inl (vtx (p + 1))) (x (p + 1)) -
            backtrackTerm hns (x p) (x (p + 1)) (β p)) *
          ∏ i ∈ Finset.Ico (p + 1) (n + 1), κ (β i) (x (i + 1)) := by ring
      _ = _ := by rw [hsign]; ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib,
    Finset.sum_range_sub' (fun p ↦ prefixSign k β p * telescopeTerm hns β vtx x n p)]
  simp [prefixSign]

/-- **The coboundary of a coordinate cochain** on a word of homogeneous letters. -/
private theorem hochschildDifferential_coordCochain_apply {n : ℕ} (β : ℕ → ZigzagBasisIndex G)
    (vtx : ℕ → V) (hβ : ∀ i ≤ n, IsSlot (vtx i) (vtx (i + 1)) (β i))
    (z : nonisolatedZigzagQuotient k G) (x : ℕ → nonisolatedZigzagQuotient k G) (d : ℕ → ℤ)
    (hx : ∀ i < n + 2, x i ∈ zigzagIntegerGrade k G (d i)) :
    (𝒵).hochschildDifferential 0 (coordCochain hns (n + 1) n.succ_pos β z)
        (of k _ ⟨n + 2, by omega⟩ (PiTensorProduct.tprod k fun j : Fin (n + 2) ↦ x j)) =
      (∏ i ∈ Finset.range (n + 1), κ (β i) (x i)) •
          ((𝒵).grading.koszulTwist 1 z * x (n + 1)) +
        (∏ i ∈ Finset.range (n + 1), κ (β i) (x (i + 1))) •
          ((𝒵).grading.koszulTwist 1 (x 0) * z) -
        (telescopeTerm hns β vtx x n 0 -
          prefixSign k β (n + 1) * telescopeTerm hns β vtx x n (n + 1) -
          ∑ p ∈ Finset.range (n + 1), prefixSign k β p *
            ((∏ i ∈ Finset.range p, κ (β i) (x i)) * backtrackTerm hns (x p) (x (p + 1)) (β p) *
              ∏ i ∈ Finset.Ico (p + 1) (n + 1), κ (β i) (x (i + 1)))) • z := by
  rw [zigzagStrictAInfinityAlgebra_hochschildDifferential_apply_of_homogeneous _ x d hx,
    ← sum_prefixSign_mul_prod_coord_replaceBlock β vtx hβ x d hx, Finset.sum_smul]
  rw [coordCochain_of_tprod_nat, coordCochain_of_tprod_nat (x := fun j ↦ x (1 + j)),
    Finset.sum_congr rfl fun p _ ↦ by
      rw [coordCochain_of_tprod_nat
        (x := replaceBlock x p 2 ((𝒵).grading.koszulTwist 1 (x p) * x (p + 1)))]]
  simp only [map_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  simp only [add_comm 1]

omit [Fintype G.Dart] [DecidableEq V] in
/-- **Rotation coboundaries.** For a walk `u 0, …, u n` (in product order) and an arrow `b`
parallel to it, the coboundary of the cochain reading the arrow coordinates of `u` and returning
`b` is minus the sum of the loop cochains of the two closed walks obtained by closing `u` up with
`b.symm` at either end. -/
private theorem hochschildDifferential_coordCochain_arrow {n : ℕ} (u : ℕ → G.Dart) (vtx : ℕ → V)
    (hu : ∀ i ≤ n, (u i).snd = vtx i ∧ (u i).fst = vtx (i + 1)) (b : G.Dart)
    (hb₀ : b.snd = vtx 0) (hb₁ : b.fst = vtx (n + 1)) :
    (𝒵).hochschildDifferential 0 (coordCochain hns (n + 1) n.succ_pos (fun i ↦ .inr (.inl (u i)))
        (𝔞 b)) =
      -(coordCochain hns (n + 2) (by omega)
          (fun i ↦ .inr (.inl (if i < n + 1 then u i else b.symm))) (zigzagVolume k G b.snd) +
        coordCochain hns (n + 2) (by omega)
          (fun i ↦ .inr (.inl (if i = 0 then b.symm else u (i - 1))))
          (zigzagVolume k G b.fst)) := by
  classical
  let := Fintype.ofFinite G.Dart
  refine eq_of_forall_of_tprod (N := n + 2) (by omega)
    (hochschildDifferential_coordCochain_comp_lengthProj _ _) ?_ fun x d hx ↦ ?_
  · rw [LinearMap.neg_comp, LinearMap.add_comp, coordCochain_comp_lengthProj,
      coordCochain_comp_lengthProj]
  rw [hochschildDifferential_coordCochain_apply (fun i ↦ .inr (.inl (u i))) vtx
      (fun i hi ↦ hu i hi) _ x d hx,
    LinearMap.neg_apply, LinearMap.add_apply, coordCochain_of_tprod_nat, coordCochain_of_tprod_nat]
  have hR₁ : ∏ i ∈ Finset.range (n + 2),
      κ (.inr (.inl (if i < n + 1 then u i else b.symm))) (x i) =
        (∏ i ∈ Finset.range (n + 1), κ (.inr (.inl (u i))) (x i)) *
          κ (.inr (.inl b.symm)) (x (n + 1)) := by
    rw [Finset.prod_range_succ]
    simp only [lt_irrefl, ↓reduceIte]
    exact congrArg₂ _ (Finset.prod_congr rfl fun i hi ↦ by
      simp only [Finset.mem_range.1 hi, ↓reduceIte]) rfl
  have hR₂ : ∏ i ∈ Finset.range (n + 2),
      κ (.inr (.inl (if i = 0 then b.symm else u (i - 1)))) (x i) =
        (∏ i ∈ Finset.range (n + 1), κ (.inr (.inl (u i))) (x (i + 1))) *
          κ (.inr (.inl b.symm)) (x 0) := by
    rw [Finset.prod_range_succ']
    simp only [↓reduceIte]
    exact congrArg₂ _ (Finset.prod_congr rfl fun i _ ↦ by simp) rfl
  rw [hR₁, hR₂, koszulTwist_one_zigzagMk_ofArrow zigzagStrictAInfinityAlgebra_grading_piece b,
    neg_mul, zigzagMk_ofArrow_mul hns, mul_zigzagMk_ofArrow hns]
  simp only [zigzagBasis_coord_koszulTwist zigzagStrictAInfinityAlgebra_grading_piece]
  simp only [telescopeTerm, prefixSign, backtrackTerm, zigzagBasisDegree_inl,
    zigzagBasisDegree_inr_inl, sub_self, Finset.sum_const_zero, negOnePowCast_zero, mul_zero,
    Finset.range_eq_Ico, Finset.Ico_self, Finset.prod_empty, mul_one, one_mul, zigzagBasis_apply,
    zigzagBasisFun_inr_inl, zigzagBasisFun_inr_inr, ← hb₀, ← hb₁, zero_mul, sub_zero,
    negOnePowCast_one]
  module

/-- **Relator coboundaries.** For a closed word `β` of arrows with a single volume class `x_v` in
the slot `p`, the coboundary of the cochain reading the coordinates of `β` and returning the
volume class at its base is the sum of the loop cochains of the words in which the slot `p` is
replaced by a backtrack `d, d.symm` at `v`. -/
private theorem hochschildDifferential_coordCochain_volume {n p : ℕ} (hp : p ≤ n)
    (β : ℕ → ZigzagBasisIndex G) (vtx : ℕ → V) (hβ : ∀ i ≤ n, IsSlot (vtx i) (vtx (i + 1)) (β i))
    (v : V) (hβp : β p = .inr (.inr v)) (hβa : ∀ i ≤ n, i ≠ p → zigzagBasisDegree G (β i) = 1)
    (hvtx : vtx (n + 1) = vtx 0) :
    (𝒵).hochschildDifferential 0
        (coordCochain hns (n + 1) n.succ_pos β (zigzagVolume k G (vtx 0))) =
      ∑ d : G.Dart with d.snd = v,
        coordCochain hns (n + 2) (by omega) (insertBacktrack β p d) (zigzagVolume k G (vtx 0)) := by
  refine eq_of_forall_of_tprod (N := n + 2) (by omega)
    (hochschildDifferential_coordCochain_comp_lengthProj _ _) ?_ fun x d hx ↦ ?_
  · refine LinearMap.ext fun w ↦ ?_
    simp only [LinearMap.comp_apply, LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun _ _ ↦ LinearMap.congr_fun (coordCochain_comp_lengthProj _ _ _) w
  have hR : (∑ e : G.Dart with e.snd = v,
      coordCochain hns (n + 2) (by omega) (insertBacktrack β p e) (zigzagVolume k G (vtx 0)))
        (of k _ ⟨n + 2, by omega⟩ (PiTensorProduct.tprod k fun j : Fin (n + 2) ↦ x j)) =
      ((∏ i ∈ Finset.range p, κ (β i) (x i)) * backtrackTerm hns (x p) (x (p + 1)) (β p) *
        ∏ i ∈ Finset.Ico (p + 1) (n + 1), κ (β i) (x (i + 1))) • zigzagVolume k G (vtx 0) := by
    rw [LinearMap.sum_apply, hβp, backtrackTerm, Finset.mul_sum, Finset.sum_mul, Finset.sum_smul]
    refine Finset.sum_congr rfl fun e _ ↦ ?_
    rw [coordCochain_of_tprod_nat, prod_coord_insertBacktrack β hp]
  -- Only the volume slot carries a backtrack term.
  have harrow : ∀ i ≤ n, i ≠ p → ∀ y y' : nonisolatedZigzagQuotient k G,
      backtrackTerm hns y y' (β i) = 0 := fun i hi hip y y' ↦ by
    have hdeg := hβa i hi hip
    rcases h : β i with j | e | j <;> rw [h] at hdeg
    · simp only [zigzagBasisDegree_inl, zero_ne_one] at hdeg
    · simp only [backtrackTerm]
    · simp only [zigzagBasisDegree_inr_inr, OfNat.ofNat_ne_one] at hdeg
  have hBT := Finset.sum_eq_single (f := fun q ↦ prefixSign k β q *
      ((∏ i ∈ Finset.range q, κ (β i) (x i)) * backtrackTerm hns (x q) (x (q + 1)) (β q) *
        ∏ i ∈ Finset.Ico (q + 1) (n + 1), κ (β i) (x (i + 1)))) (s := Finset.range (n + 1)) p
    (fun q hq hqp ↦ by rw [harrow q (by simpa [Nat.lt_succ_iff] using hq) hqp, mul_zero, zero_mul,
      mul_zero]) (fun h ↦ absurd (Finset.mem_range.2 (by omega)) h)
  have hsign₀ : prefixSign k β p = 1 := by
    rw [prefixSign, Finset.sum_eq_zero fun j hj ↦ by
      rw [hβa j (by simp at hj; omega) (by simp at hj; omega), sub_self], negOnePowCast_zero]
  have hsign₁ : prefixSign k β (n + 1) = -1 := by
    rw [prefixSign, Finset.sum_eq_single p (fun j hj hjp ↦ by
      rw [hβa j (by simp at hj; omega) hjp, sub_self]) (fun h ↦ absurd (by simp; omega) h), hβp]
    simp [negOnePowCast_one]
  rw [hochschildDifferential_coordCochain_apply β vtx hβ _ x d hx, hR, hBT, hsign₀, hsign₁,
    koszulTwist_one_zigzagVolume zigzagStrictAInfinityAlgebra_grading_piece, zigzagVolume_mul hns,
    mul_zigzagVolume hns, zigzagBasis_coord_koszulTwist zigzagStrictAInfinityAlgebra_grading_piece]
  simp only [telescopeTerm, Finset.range_eq_Ico, Finset.Ico_self, Finset.prod_empty, mul_one,
    hvtx, zigzagBasisDegree_inl, mul_zero, negOnePowCast_zero, one_mul]
  module

omit [Fintype G.Dart] [DecidableEq V] in
/-- **The rotation coboundaries.** For a closed word `(u, e)`, the sum of the loop cochains of the
word and of its rotation `(e, u)` is a coboundary. -/
private theorem isZigzagCoboundary_loopCochain_snoc_add_cons {n : ℕ} (u : Fin (n + 1) → G.Dart)
    (e : G.Dart) (h : IsClosedWord (Fin.snoc u e : Fin (n + 2) → G.Dart)) :
    IsZigzagCoboundary k hns n (loopCochain hns (Fin.snoc u e : Fin (n + 2) → G.Dart) +
      loopCochain hns (Fin.cons e u : Fin (n + 2) → G.Dart)) := by
  classical
  let := Fintype.ofFinite G.Dart
  set U := natExt u e
  have hW := (isClosedWord_iff_natExt _).1 h
  have hWi (i : ℕ) (hi : i < n + 2) :
      natExt (Fin.snoc u e : Fin (n + 2) → G.Dart) ((Fin.snoc u e : Fin (n + 2) → G.Dart) 0) i =
        if i < n + 1 then U i else e := natExt_snoc u e _ hi
  have h0 : (Fin.snoc u e : Fin (n + 2) → G.Dart) 0 = U 0 := by
    have := hWi 0 (by omega)
    rwa [natExt_of_lt _ _ (show 0 < n + 2 by omega), ite_eq_left (by omega), Fin.mk_zero] at this
  have hstep (i : ℕ) (hi : i < n) : (U i).fst = (U (i + 1)).snd := by
    have := hW i (by omega)
    rwa [hWi i (by omega), hWi (i + 1) (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega)] at this
  have hlast : (U n).fst = e.snd := by
    have := hW n (by omega)
    rwa [hWi n (by omega), hWi (n + 1) (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega)] at this
  have hfirst : e.fst = (U 0).snd := by
    have := hW (n + 1) (by omega)
    rwa [hWi (n + 1) (by omega), ite_eq_right (by omega), natExt_self, h0] at this
  let vtx : ℕ → V := fun i ↦ if i ≤ n then (U i).snd else e.snd
  have hu : ∀ i ≤ n, (U i).snd = vtx i ∧ (U i).fst = vtx (i + 1) := fun i hi ↦ by
    refine ⟨by simp [vtx, hi], ?_⟩
    rcases lt_or_eq_of_le hi with hi | rfl
    · simp [vtx, show i + 1 ≤ n by omega, hstep i hi]
    · simp [vtx, hlast]
  have hδ := hochschildDifferential_coordCochain_arrow (k := k) (hns := hns) U vtx hu e.symm
    (by simp [vtx, hfirst]) (by simp [vtx])
  have hC := (show IsZigzagCoboundary k hns n _ from
    ⟨coordCochain hns (n + 1) n.succ_pos (fun i ↦ .inr (.inl (U i))) (𝔞 e.symm),
      isHomogeneous_coordCochain _ _ (zigzagMk_ofArrow_mem_zigzagIntegerGrade_one k G _) 0
        (by simp), coordCochain_comp_lengthProj _ _ _, hδ⟩).neg
  rw [neg_neg] at hC
  convert hC using 2
  · rw [loopCochain, show e.symm.snd = ((Fin.snoc u e : Fin (n + 2) → G.Dart) 0).snd by
      rw [h0]; exact hfirst]
    exact coordCochain_congr _ (fun i hi ↦ by rw [hWi i hi, SimpleGraph.Dart.symm_symm]) _
  · rw [loopCochain]
    refine coordCochain_congr _ (fun i hi ↦ ?_) _
    rw [natExt_cons u e _ hi, SimpleGraph.Dart.symm_symm]

/-- **The relator coboundaries.** If inserting the backtrack `d₀, d₀.symm` at the positions `p` and
`p + 1` of `u` gives a closed word, then the sum of the loop cochains of all the backtrack
insertions with the same head is a coboundary. -/
private theorem isZigzagCoboundary_sum_loopCochain_insertNth {n : ℕ} (p : Fin (n + 1))
    (u : Fin n → G.Dart) (d₀ : G.Dart) (h : IsClosedWord (backtrackWord p d₀ u)) :
    IsZigzagCoboundary k hns n
      (∑ d : G.Dart with d.snd = d₀.snd, loopCochain hns (backtrackWord p d u)) := by
  set w₀ := backtrackWord p d₀ u
  set W₀ := natExt w₀ (w₀ 0)
  have hp := p.isLt
  have hW₀i : ∀ i < n + 2, W₀ i = if i < p then natExt u d₀ i else if i = p then d₀
      else if i = p + 1 then d₀.symm else natExt u d₀ (i - 2) :=
    fun i hi ↦ natExt_backtrackWord p d₀ u _ hi
  have hβ := isSlot_relatorWord (W := W₀) (d₀ := d₀) ((isClosedWord_iff_natExt w₀).1 h)
    (by rw [hW₀i p (by omega)]; simp) (by rw [hW₀i (p + 1) (by omega)]; simp)
    (show (p : ℕ) ≤ n by omega)
  have hδ := hochschildDifferential_coordCochain_volume (k := k) (hns := hns)
    (show (p : ℕ) ≤ n by omega) _ _ hβ d₀.snd (by simp [relatorWord]) (fun i _ hip ↦ by
      simp only [relatorWord, hip, ↓reduceIte]
      split_ifs <;> exact zigzagBasisDegree_inr_inl G _)
    (by simp only [relatorVertex, show ¬ n + 1 ≤ p by omega, Nat.zero_le, ↓reduceIte]
        exact congrArg (·.snd) (natExt_self_eq_natExt_zero w₀))
  refine ⟨coordCochain hns (n + 1) n.succ_pos (relatorWord W₀ p d₀.snd)
      (zigzagVolume k G (relatorVertex W₀ p 0)),
    isHomogeneous_coordCochain _ _ (zigzagVolume_mem_zigzagIntegerGrade_two k G _) 0 ?_,
    coordCochain_comp_lengthProj _ _ _, ?_⟩
  · rw [Finset.sum_eq_single (p : ℕ) (fun j _ hjp ↦ by
      simp only [relatorWord, hjp, ↓reduceIte]
      split_ifs <;> simp) (fun h ↦ absurd (by simp; omega) h)]
    simp [relatorWord]
  rw [hδ]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  rw [loopCochain, relatorVertex_zero p u (Finset.mem_filter.1 hd).2]
  exact coordCochain_congr _ (fun i hi ↦ insertBacktrack_relatorWord p u d₀ d hi) _

variable (k G) in
/-- The relations spanned by rotations and by backtrack insertions among the closed words of
`n + 2` darts. -/
private noncomputable def loopRelations (n : ℕ) : Submodule k ((Fin (n + 2) → G.Dart) →₀ k) :=
  Submodule.span k
    ({c | ∃ (u : Fin (n + 1) → G.Dart) (e : G.Dart),
        IsClosedWord (Fin.snoc u e : Fin (n + 2) → G.Dart) ∧
        c = Finsupp.single (Fin.snoc u e : Fin (n + 2) → G.Dart) 1 +
          Finsupp.single (Fin.cons e u : Fin (n + 2) → G.Dart) 1} ∪
      {c | ∃ (p : Fin (n + 1)) (u : Fin n → G.Dart) (d₀ : G.Dart),
        IsClosedWord (backtrackWord p d₀ u) ∧
        c = ∑ d : G.Dart with d.snd = d₀.snd, Finsupp.single (backtrackWord p d u) 1})

/-- Every relation among closed words gives a coboundary. -/
private theorem isZigzagCoboundary_linearCombination_of_mem_loopRelations {n : ℕ}
    {c : (Fin (n + 2) → G.Dart) →₀ k} (hc : c ∈ loopRelations k G n) :
    IsZigzagCoboundary k hns n (Finsupp.linearCombination k (loopCochain hns) c) := by
  induction hc using Submodule.span_induction with
  | mem c hc =>
    rcases hc with ⟨u, e, h, rfl⟩ | ⟨p, u, d₀, h, rfl⟩
    · simpa only [map_add, Finsupp.linearCombination_single, one_smul] using
        isZigzagCoboundary_loopCochain_snoc_add_cons u e h
    · simpa only [map_sum, Finsupp.linearCombination_single, one_smul] using
        isZigzagCoboundary_sum_loopCochain_insertNth p u d₀ h
  | zero => simpa using isZigzagCoboundary_zero n
  | add c c' _ _ hc hc' => simpa only [map_add] using hc.add hc'
  | smul r c _ hc => simpa only [map_smul] using hc.smul r

end CoordCochain

/-! ### Detection of Hochschild classes by word pairings -/

section Field

variable {k : Type w} [Field k] {V : Type u} {G : SimpleGraph V} [Finite V]
  {hns : ∀ i : V, ∃ j, G.Adj i j} [Fintype G.Dart] [DecidableEq V]

local notation "𝒵" => zigzagStrictAInfinityAlgebra k hns

open scoped Classical in
/-- The weights read off a linear functional on the formal combinations of words: its values on
the closed words, and zero on the other words. -/
private noncomputable def closedWeights {n : ℕ} (f : Module.Dual k ((Fin (n + 2) → G.Dart) →₀ k))
    (w : Fin (n + 2) → G.Dart) : k :=
  if IsClosedWord w then f (Finsupp.single w 1) else 0

omit [Finite V] in
/-- The weights of a functional vanishing on the rotation relations are anticyclic. -/
private theorem closedWeights_snoc {n : ℕ} {f : Module.Dual k ((Fin (n + 2) → G.Dart) →₀ k)}
    (hf : ∀ x ∈ loopRelations k G n, f x = 0) (u : Fin (n + 1) → G.Dart) (e : G.Dart) :
    closedWeights f (Fin.snoc u e) = -closedWeights f (Fin.cons e u) := by
  by_cases hcl : IsClosedWord (Fin.snoc u e : Fin (n + 2) → G.Dart)
  · have hcl' := (isClosedWord_snoc_iff u e).1 hcl
    have := hf _ (Submodule.subset_span (Or.inl ⟨u, e, hcl, rfl⟩))
    rw [map_add] at this
    rw [closedWeights, closedWeights, ite_eq_left hcl, ite_eq_left hcl']
    exact eq_neg_of_add_eq_zero_left this
  · rw [closedWeights, closedWeights, ite_eq_right hcl,
      ite_eq_right (mt (isClosedWord_snoc_iff u e).2 hcl), neg_zero]

omit [Finite V] in
/-- The weights of a functional vanishing on the relator relations satisfy the signless relation
in every pair of consecutive positions. -/
private theorem sum_closedWeights_insertNth {n : ℕ}
    {f : Module.Dual k ((Fin (n + 2) → G.Dart) →₀ k)} (hf : ∀ x ∈ loopRelations k G n, f x = 0)
    (p : Fin (n + 1)) (u : Fin n → G.Dart) (v : V) :
    ∑ d : G.Dart with d.snd = v, closedWeights f (backtrackWord p d u) = 0 := by
  by_cases hex : ∃ d₀ : G.Dart, d₀.snd = v ∧ IsClosedWord (backtrackWord p d₀ u)
  · obtain ⟨d₀, rfl, hcl⟩ := hex
    have := hf _ (Submodule.subset_span (Or.inr ⟨p, u, d₀, hcl, rfl⟩))
    rw [map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [closedWeights,
      ite_eq_left (isClosedWord_backtrackWord p u (Finset.mem_filter.1 hd).2 hcl)]
  · refine Finset.sum_eq_zero fun d hd ↦ ?_
    rw [closedWeights, ite_eq_right fun hcl ↦ hex ⟨d, (Finset.mem_filter.1 hd).2, hcl⟩]

omit [Finite V] in
/-- **Coefficients orthogonal to every word pairing are relations.** If `∑ w, a w * c w = 0` for
all anticyclic weights `a` satisfying the signless relations, then `c`, supported on closed words,
lies in the span of the rotation and relator relations. -/
private theorem mem_loopRelations_of_forall {n : ℕ} {c : (Fin (n + 2) → G.Dart) →₀ k}
    (hc : ∀ w ∈ c.support, IsClosedWord w)
    (h : ∀ a : (Fin (n + 2) → G.Dart) → k,
      (∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u)) →
      (∀ (p : Fin (n + 1)) (u : Fin n → G.Dart) (v : V),
        ∑ d : G.Dart with d.snd = v, a (backtrackWord p d u) = 0) →
      ∑ w, a w * c w = 0) :
    c ∈ loopRelations k G n := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro f hf
  have hf' : ∀ x ∈ loopRelations k G n, f x = 0 := (Submodule.mem_dualAnnihilator f).1 hf
  calc f c = f (c.sum fun w r ↦ Finsupp.single w r) := by rw [Finsupp.sum_single]
    _ = ∑ w ∈ c.support, c w * f (Finsupp.single w 1) := by
        rw [Finsupp.sum, map_sum]
        refine Finset.sum_congr rfl fun w _ ↦ ?_
        rw [← Finsupp.smul_single_one, map_smul, smul_eq_mul]
    _ = ∑ w, closedWeights f w * c w := by
        rw [← Finset.sum_subset (Finset.subset_univ c.support) fun w _ hw ↦ by
          rw [Finsupp.notMem_support_iff.1 hw, mul_zero]]
        refine Finset.sum_congr rfl fun w hw ↦ ?_
        rw [closedWeights, ite_eq_left (hc w hw), mul_comm]
    _ = 0 := h _ (closedWeights_snoc hf') (sum_closedWeights_insertNth hf')

/-- **Loop operations are Hochschild coboundaries exactly when no word pairing detects them.**
Over a field, let `c` be coefficients on closed walks of `n + 2` darts, `n ≥ 1`, so that the
operation of arity `n + 2` of the loop deformation `zigzagLoopAInfinityAlgebra hns c hc` is a
Hochschild cocycle of the strict zigzag algebra. It is the Hochschild differential of a suspended
cochain of degree zero, which may be taken concentrated in arity `n + 1`, if and only if
`∑ w, a w * c w = 0` for all weights `a` on words of `n + 2` darts which are anticyclic and satisfy
the signless relation in every pair of consecutive positions. -/
theorem exists_hochschildDifferential_eq_obstruction_zigzagLoopAInfinityAlgebra_iff {n : ℕ}
    (hn : 1 ≤ n) (c : (Fin (n + 2) → G.Dart) →₀ k)
    (hc : ∀ w ∈ c.support, ∀ i, (w i).fst = (w (i + 1)).snd) :
    (∃ φ : ReducedTensorWords k (nonisolatedZigzagQuotient k G) →ₗ[k]
        nonisolatedZigzagQuotient k G,
      LinearMap.IsHomogeneous φ (gradedPiece ((𝒵).grading.shift 1))
          ((𝒵).grading.shift 1).piece 0 ∧
        φ ∘ₗ lengthProj k _ ⟨n + 1, n.succ_pos⟩ = φ ∧
        (𝒵).hochschildDifferential 0 φ =
          (zigzagLoopAInfinityAlgebra hns c hc).obstruction 𝒵 ⟨n + 2, by omega⟩) ↔
      ∀ a : (Fin (n + 2) → G.Dart) → k,
        (∀ (u : Fin (n + 1) → G.Dart) (e : G.Dart), a (Fin.snoc u e) = -a (Fin.cons e u)) →
        (∀ (p : Fin (n + 1)) (u : Fin n → G.Dart) (v : V),
          ∑ d : G.Dart with d.snd = v,
            a (Fin.insertNth p.castSucc d (Fin.insertNth p d.symm u)) = 0) →
        ∑ w, a w * c w = 0 := by
  constructor
  · rintro ⟨φ, hφ, -, hφc⟩ a hrot hrel
    have h0 := zigzagWordPairing_hochschildDifferential_eq_zero (hns := hns) hrot hrel hφ
    rw [hφc, zigzagWordPairing_obstruction hn] at h0
    exact ((Units.isUnit _).map (Int.castRingHom k)).mul_right_eq_zero.mp h0
  intro h
  obtain ⟨φ, hφ, hφl, hφc⟩ := (isZigzagCoboundary_linearCombination_of_mem_loopRelations
    (hns := hns) (mem_loopRelations_of_forall
      (fun w hw ↦ by simpa only [IsClosedWord] using hc w hw)
      fun a hrot hrel ↦ h a hrot (by simpa only [backtrackWord] using hrel))).smul
      (((∏ i : Fin (n + 2), ((n + 1 - i : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) : k)
  exact ⟨φ, hφ, hφl, by rw [hφc, obstruction_zigzagLoopAInfinityAlgebra_eq hn]⟩

end Field

end TauCeti
