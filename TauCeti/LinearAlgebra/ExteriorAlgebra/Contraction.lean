/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Order.Fin.Tuple

/-!
# Coordinate projections on an exterior algebra

Left multiplication by a basis vector after contraction by its dual coordinate is the projection
onto the exterior basis vectors containing that coordinate. This is the occupation-number
projection used by both scalar detection in Clifford algebras and the matrix-unit construction
from creation and annihilation operators.

Each of the two halves acts on an exterior basis vector by a single coordinate move, up to the
shuffle sign that carries the moved coordinate to the front: contraction erases the coordinate
from the index set, and left multiplication inserts it, each vanishing when the index set is on
the wrong side of that move. Creation after contraction at distinct coordinates therefore
replaces an occupied coordinate with an unoccupied one, with the product of their shuffle signs.

The grade involution is diagonal for the exterior basis as well: it multiplies an exterior
monomial, and so the basis vector indexed by `s`, by the parity of its degree.

The basis vectors of index sets with one or two elements are the corresponding products of the
exterior-algebra generators, in increasing order.
-/

public section

open CliffordAlgebra

namespace TauCeti.ExteriorAlgebra

universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

private theorem contractLeft_ιMulti_eq_zero {n : ℕ}
    (d : Module.Dual R M) (v : Fin n → M) (h : ∀ i, d (v i) = 0) :
    contractLeft (Q := (0 : QuadraticForm R M)) d (ExteriorAlgebra.ιMulti R n v) = 0 := by
  induction n with
  | zero =>
      rw [ExteriorAlgebra.ιMulti_zero_apply]
      exact contractLeft_one (Q := (0 : QuadraticForm R M)) d
  | succ n ih =>
      rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, h 0, zero_smul,
        ih (Matrix.vecTail v) (fun i ↦ h i.succ), mul_zero, sub_zero]

/-- Contracting an exterior-basis vector by a coordinate not in its index set gives zero. -/
@[simp]
private theorem contractLeft_coord_basis_eq_zero_of_not_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∉ s) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) = 0 := by
  rw [ExteriorAlgebra.basis_apply]
  apply contractLeft_ιMulti_eq_zero
  intro j
  simp only [Function.comp_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply]
  split_ifs with h
  · exfalso
    apply hi
    rw [← h]
    have hj := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
      (Set.powersetCard.prodEquiv.symm s).2
      (Set.powersetCard.ofFinEmbEquiv.symm (Set.powersetCard.prodEquiv.symm s).2 j)).mp
      ⟨j, rfl⟩
    exact hj
  · rfl

/-- **The grade involution acts on an exterior monomial by the parity of its degree.** The
monomial is the product of its `n` generators, each of which the involution negates. -/
@[simp]
theorem involute_ιMulti {n : ℕ} (v : Fin n → M) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (ExteriorAlgebra.ιMulti R n v) =
      (-1 : R) ^ n • ExteriorAlgebra.ιMulti R n v := by
  -- Every exterior monomial is the product of the list of its generators.
  have h : ExteriorAlgebra.ιMulti R n v =
      ((List.ofFn v).map (CliffordAlgebra.ι (0 : QuadraticForm R M))).prod := by
    rw [ExteriorAlgebra.ιMulti_apply, List.map_ofFn]
    rfl
  rw [h, CliffordAlgebra.involute_prod_map_ι, List.length_ofFn]

/-- **The grade involution acts on an exterior-basis vector by the parity of its index set.** The
basis vector indexed by `s` is the monomial on `s.card` generators. -/
@[simp]
theorem involute_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (s : Finset I) :
    CliffordAlgebra.involute (Q := (0 : QuadraticForm R M)) (b.ExteriorAlgebra s) =
      (-1 : R) ^ s.card • b.ExteriorAlgebra s := by
  rw [ExteriorAlgebra.basis_apply]
  exact involute_ιMulti _

/-- The shuffle sign for the singleton basis vector indexed by `i` followed by the basis vector
indexed by `s.erase i`. When `i ∈ s`, this is the sign of moving `i` to the front of `s`. -/
def basisEraseSign {I : Type w} [LinearOrder I] (i : I) (s : Finset I) : ℤˣ :=
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I (s.erase i).card := ⟨s.erase i, rfl⟩
  (Set.powersetCard.permOfDisjoint (s := u) (t := t) (by simp [u, t])).sign

/-- The shuffle sign which moves `i` to the front of an ordered exterior monomial is `-1`
raised to the number of indices before `i`. -/
theorem basisEraseSign_eq_neg_one_pow_card_filter_lt {I : Type w} [LinearOrder I]
    (i : I) (s : Finset I) (hi : i ∈ s) :
    basisEraseSign i s = (-1 : ℤˣ) ^ (s.filter (fun j ↦ j < i)).card := by
  classical
  let n := (s.erase i).card
  have hsCard : s.card = n + 1 := by
    simpa [n] using (Finset.card_erase_add_one hi).symm
  -- Enumerate `s` in increasing order. The position `k` of `i` counts precisely the entries
  -- which the shuffle crosses when it moves the singleton `{i}` to the front.
  let e : Fin (n + 1) ↪o I := s.orderEmbOfFin hsCard
  let k : Fin (n + 1) := (s.orderIsoOfFin hsCard).symm ⟨i, hi⟩
  have hek : e k = i := by
    exact congrArg Subtype.val ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨i, hi⟩)
  have hremove : k.removeNth (fun j ↦ e j) =
      (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) := by
    apply Finset.orderEmbOfFin_unique
    · intro j
      exact Finset.mem_erase.mpr ⟨fun h ↦ k.succAbove_ne j (e.injective (h.trans hek.symm)),
        Finset.orderEmbOfFin_mem s hsCard _⟩
    · exact e.strictMono.comp (Fin.strictMono_succAbove k)
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I n := ⟨s.erase i, rfl⟩
  have hdisj : Disjoint u.val t.val := by simp [u, t]
  have hsCard' : s.card = 1 + n := hsCard.trans (Nat.add_comm n 1)
  have hunion : Set.powersetCard.disjUnion hdisj =
      (Set.powersetCard.ofCard (s := s) hsCard' : Set.powersetCard I (1 + n)) := by
    apply Subtype.ext
    simp [u, t, hi]
  let p : Equiv.Perm (Fin (1 + n)) := Set.powersetCard.permOfDisjoint hdisj
  let c : Fin (1 + n) ≃ Fin (n + 1) := finCongr (Nat.add_comm 1 n)
  let p' : Equiv.Perm (Fin (n + 1)) := c.symm.trans (p.trans c)
  -- After reconciling the two cardinality presentations, this shuffle is the inverse cycle
  -- which moves position `k` to the front and shifts the preceding positions one step right.
  have hec : (fun q ↦ e (c q)) =
      (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop := by
    apply Finset.orderEmbOfFin_unique
    · intro q
      have hdval : (Set.powersetCard.disjUnion hdisj).val = s :=
        congrArg Subtype.val hunion
      rw [hdval]
      exact Finset.orderEmbOfFin_mem s hsCard (c q)
    · intro a b hab
      apply e.strictMono
      simpa [c, Fin.ext_iff] using hab
  have hp : p' = k.cycleRange.symm := by
    apply Equiv.ext
    intro j
    apply e.injective
    change e (c (p (c.symm j))) = e (k.cycleRange.symm j)
    have hrhs : e (k.cycleRange.symm j) =
        (Fin.cons (e k) (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j := by
      simpa only [Function.comp_apply] using
        congrFun (Fin.cons_removeNth_eq_comp_cycleRange_symm e k) j |>.symm
    rw [hrhs, hek]
    change e (c (p (c.symm j))) =
      (Fin.cons i (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j
    rw [hremove]
    change (fun q ↦ e (c q)) (p (c.symm j)) = _
    rw [hec]
    let x : (Set.powersetCard.disjUnion hdisj).val :=
      Equiv.Finset.disjUnionEquiv u.val t.val hdisj
        (((Set.powersetCard.orderIsoOfFin u).sumCongr
          (Set.powersetCard.orderIsoOfFin t)) (finSumFinEquiv.symm (c.symm j)))
    have hx : (Set.powersetCard.disjUnion hdisj).val.orderEmbOfFin
        (Set.powersetCard.disjUnion hdisj).prop (p (c.symm j)) = x := by
      have hpApply : p (c.symm j) =
          (Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).symm x := rfl
      rw [hpApply]
      exact congrArg Subtype.val
        ((Set.powersetCard.orderIsoOfFin (Set.powersetCard.disjUnion hdisj)).apply_symm_apply x)
    rw [hx]
    cases j using Fin.cases with
    | zero =>
        have hzero : finSumFinEquiv.symm (c.symm 0) = Sum.inl (0 : Fin 1) := by
          apply finSumFinEquiv.injective
          apply Fin.ext
          rfl
        simp only [x, hzero, Fin.cons_zero]
        change ↑(Equiv.Finset.disjUnionEquiv u.val t.val hdisj
          (Sum.inl ((Set.powersetCard.orderIsoOfFin u) 0))) = i
        rw [Equiv.Finset.disjUnionEquiv_inl]
        dsimp only [Set.powersetCard.orderIsoOfFin, u]
        change Finset.orderEmbOfFin {i} (Finset.card_singleton i) 0 = i
        exact Finset.orderEmbOfFin_singleton i 0
    | succ q =>
        have hsucc : finSumFinEquiv.symm (c.symm q.succ) = Sum.inr q := by
          apply finSumFinEquiv.injective
          rw [finSumFinEquiv.apply_symm_apply]
          apply Fin.ext
          simp [c]
          omega
        simp only [x, hsucc, Fin.cons_succ]
        change ↑(Equiv.Finset.disjUnionEquiv u.val t.val hdisj
          (Sum.inr ((Set.powersetCard.orderIsoOfFin t) q))) =
            (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q
        rw [Equiv.Finset.disjUnionEquiv_inr]
        dsimp only [Set.powersetCard.orderIsoOfFin, t]
        change (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q =
          (s.erase i).orderEmbOfFin (show (s.erase i).card = n from rfl) q
        rfl
  have hsign : Equiv.Perm.sign p' = Equiv.Perm.sign p := by
    simp [p']
  rw [basisEraseSign]
  change Equiv.Perm.sign p = _
  rw [← hsign, hp, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  congr 1
  -- The initial segment below `k` is order-isomorphic to the elements of `s` strictly below `i`,
  -- so its cardinality is the exponent in the claimed sign.
  have himage : Finset.image e (Finset.Iio k) = s.filter (fun j ↦ j < i) := by
    ext x
    simp only [Finset.mem_image, Finset.mem_Iio, Finset.mem_filter]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact ⟨Finset.orderEmbOfFin_mem s hsCard j, hek ▸ e.strictMono hj⟩
    · rintro ⟨hxs, hxi⟩
      let j : Fin (n + 1) := (s.orderIsoOfFin hsCard).symm ⟨x, hxs⟩
      refine ⟨j, ?_, ?_⟩
      · exact e.lt_iff_lt.mp (by simpa [e, j, k] using hxi)
      · exact congrArg Subtype.val ((s.orderIsoOfFin hsCard).apply_symm_apply ⟨x, hxs⟩)
  rw [← Fin.card_Iio k, ← himage, Finset.card_image_of_injective _ e.injective]

/-- The exterior-basis vector indexed by a singleton is the image of the corresponding basis
vector under the exterior-algebra generator. -/
@[simp]
theorem basis_singleton {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) :
    b.ExteriorAlgebra {i} = ExteriorAlgebra.ι R (b i) := by
  let a : Set.powersetCard I 1 :=
    Set.powersetCard.ofCard (s := {i}) (Finset.card_singleton i)
  rw [ExteriorAlgebra.basis_apply_ofCard b (Finset.card_singleton i)]
  rw [ExteriorAlgebra.ιMulti_family]
  rw [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  have hj := (Set.powersetCard.mem_range_ofFinEmbEquiv_symm_iff_mem
    a (Set.powersetCard.ofFinEmbEquiv.symm a 0)).mp ⟨0, rfl⟩
  have hj' : Set.powersetCard.ofFinEmbEquiv.symm a 0 ∈ ({i} : Finset I) := hj
  have heq : Set.powersetCard.ofFinEmbEquiv.symm a 0 = i := Finset.eq_of_mem_singleton hj'
  exact congrArg (fun j ↦ ExteriorAlgebra.ι R (b j)) heq

/-- The exterior-basis vector indexed by a pair `{i, j}` with `i < j` is the product of the two
basis vectors in increasing order. -/
theorem basis_pair {I : Type w} [LinearOrder I] (b : Module.Basis I R M) {i j : I} (hij : i < j) :
    b.ExteriorAlgebra {i, j} = ExteriorAlgebra.ι R (b i) * ExteriorAlgebra.ι R (b j) := by
  have hcard : ({i, j} : Finset I).card = 2 := Finset.card_pair hij.ne
  have hlt := ({i, j} : Finset I).orderEmbOfFin hcard |>.strictMono
    (show (0 : Fin 2) < 1 by decide)
  have h0 := ({i, j} : Finset I).orderEmbOfFin_mem hcard 0
  have h1 := ({i, j} : Finset I).orderEmbOfFin_mem hcard 1
  simp only [Finset.mem_insert, Finset.mem_singleton] at h0 h1
  -- The increasing enumeration of `{i, j}` must list `i` first and `j` second.
  obtain ⟨hi, hj⟩ : ({i, j} : Finset I).orderEmbOfFin hcard 0 = i ∧
      ({i, j} : Finset I).orderEmbOfFin hcard 1 = j := by
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rw [h0, h1] at hlt
    · exact absurd hlt (lt_irrefl _)
    · exact ⟨h0, h1⟩
    · exact absurd hlt (lt_asymm hij)
    · exact absurd hlt (lt_irrefl _)
  rw [ExteriorAlgebra.basis_apply_ofCard b hcard, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_succ_apply,
    ExteriorAlgebra.ιMulti_zero_apply, mul_one]
  simp [Set.powersetCard.ofFinEmbEquiv_symm_apply, Set.powersetCard.ofCard, Matrix.vecTail,
    hi, hj]

/-- Multiplying the basis vector for `i` by the basis vector for `s.erase i` reconstructs the
basis vector for `s`, with the shuffle sign that moves `i` to the front. -/
theorem basis_singleton_mul_basis_erase {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∈ s) :
    b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) =
      basisEraseSign i s • b.ExteriorAlgebra s := by
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t : Set.powersetCard I (s.erase i).card := ⟨s.erase i, rfl⟩
  have hdisj : Disjoint u.val t.val := by simp [u, t]
  have hunion : Set.powersetCard.disjUnion hdisj =
      (Set.powersetCard.ofCard (s := s) (by
        rw [Finset.card_erase_of_mem hi]
        have : 0 < s.card := Finset.card_pos.mpr ⟨i, hi⟩
        omega) : Set.powersetCard I (1 + (s.erase i).card)) := by
    apply Subtype.ext
    simp [Set.powersetCard.disjUnion, u, t, hi]
  have hprod := ExteriorAlgebra.basis_mul_of_disjoint b u t hdisj
  rw [hunion] at hprod
  simpa [basisEraseSign, u, t] using hprod

/-- **Creating a basis coordinate inserts it into the index set**, with the shuffle sign that
moves it to the front; it is zero when the coordinate is already present, since a repeated
generator squares to zero. -/
@[simp]
theorem ι_mul_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    ExteriorAlgebra.ι R (b i) * b.ExteriorAlgebra s =
      if i ∈ s then 0
        else basisEraseSign i (insert i s) • b.ExteriorAlgebra (insert i s) := by
  classical
  rw [← basis_singleton]
  split_ifs with hi
  · exact ExteriorAlgebra.basis_mul_of_not_disjoint b
      (⟨{i}, Finset.card_singleton i⟩ : Set.powersetCard I 1) (⟨s, rfl⟩ : Set.powersetCard I s.card)
      (by simp [hi])
  · have h := basis_singleton_mul_basis_erase b i (insert i s) (Finset.mem_insert_self i s)
    rwa [Finset.erase_insert hi] at h

/-- Contracting an exterior-basis vector erases the contracted coordinate, with the shuffle sign
that moves that coordinate to the front; it is zero when the coordinate is absent. -/
@[simp]
theorem contractLeft_coord_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then basisEraseSign i s • b.ExteriorAlgebra (s.erase i) else 0 := by
  classical
  split_ifs with hi
  · have hprod' := basis_singleton_mul_basis_erase b i s hi
    have hcontract : contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i)
        (b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i)) =
        b.ExteriorAlgebra (s.erase i) := by
      rw [basis_singleton, contractLeft_ι_mul]
      simp only [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
      rw [contractLeft_coord_basis_eq_zero_of_not_mem b i (s.erase i) (by simp),
        mul_zero, sub_zero]
      simp
    rcases Int.units_eq_one_or (basisEraseSign i s) with hsign | hsign
    · rw [hsign, one_smul] at hprod' ⊢
      rw [← hprod']
      exact hcontract
    · have hprodNeg : b.ExteriorAlgebra {i} * b.ExteriorAlgebra (s.erase i) =
          -b.ExteriorAlgebra s := by
        simpa [hsign] using hprod'
      rw [hprodNeg, map_neg] at hcontract
      have h := congrArg Neg.neg hcontract
      simpa [hsign] using h
  · exact contractLeft_coord_basis_eq_zero_of_not_mem b i s hi

/-- Creating an unoccupied coordinate after contracting an occupied one replaces that
coordinate in an exterior-basis vector, with the product of the two shuffle signs. -/
theorem ι_mul_contractLeft_coord_basis_of_not_mem_of_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i j : I) (s : Finset I) (hi : i ∉ s) (hj : j ∈ s) :
    ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord j) (b.ExteriorAlgebra s) =
      (basisEraseSign j s * basisEraseSign i (insert i (s.erase j))) •
        b.ExteriorAlgebra (insert i (s.erase j)) := by
  classical
  simp [contractLeft_coord_basis, ι_mul_basis, hi, hj, mul_smul_comm, smul_smul]

/-- Creation after contraction by a basis coordinate is the projection onto exterior basis
vectors containing that coordinate.

This is not a `simp` lemma because `contractLeft_coord_basis` is the canonical normal form for
the contraction in its left-hand side. -/
theorem ι_mul_contractLeft_coord_basis {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) :
    ExteriorAlgebra.ι R (b i) *
        contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) =
      if i ∈ s then b.ExteriorAlgebra s else 0 := by
  rw [contractLeft_coord_basis]
  split_ifs with hi
  · rw [← basis_singleton]
    rw [mul_smul_comm]
    rw [basis_singleton_mul_basis_erase b i s hi]
    rcases Int.units_eq_one_or (basisEraseSign i s) with hsign | hsign <;> simp [hsign]
  · rw [mul_zero]

end TauCeti.ExteriorAlgebra
