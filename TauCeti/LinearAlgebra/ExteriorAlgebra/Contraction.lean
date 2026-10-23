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
import TauCeti.LinearAlgebra.CliffordAlgebra.Contraction
import TauCeti.LinearAlgebra.ExteriorPower.Basic

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

Every basis vector is the product of the exterior-algebra generators of its index set, in
increasing order; for index sets with one or two elements this is also recorded in the explicit
forms `TauCeti.ExteriorAlgebra.basis_singleton` and `TauCeti.ExteriorAlgebra.basis_pair`.

Independently of a basis, `ExteriorAlgebra.contractLeft_map` states naturality under a linear
map: pull back the contracting functional and then map the contracted element. This follows
from the general quadratic-isometry statement `CliffordAlgebra.contractLeft_map`.

Independently of a basis, the grade involution is the sign `(-1) ^ n` on the `n`-th exterior power,
a contraction carries the `(n + 1)`-th exterior power into the `n`-th, and a vector graded-commutes
with every multivector: `ι m * x = involute x * ι m`.  Together with the graded Leibniz rule
`CliffordAlgebra.contractLeft_mul`, these say that a contraction is an odd derivation of degree
`-1` of the graded-commutative exterior algebra. On a wedge product of vectors it is the alternating
sum of deletions (`TauCeti.ExteriorAlgebra.contractLeft_ιMulti`); this is the differential of the
Koszul complex.

In degree at least the rank, contraction loses no information: if `d m = 1` and
`finrank R M ≤ n`, every `x ∈ ⋀ⁿ M` is `m ∧ (d ⌋ x)`. Hence two forms killed by `d` multiply to
zero once their degrees add up to the rank, and in rank at most four a two-form `x` satisfies
`x ∧ x = 2 x ∧ m ∧ (d ⌋ x)`. This is the algebra behind the splitting of a two-form on a product
`ℝ × Y` along the unit normal of the factor `Y`.

On `M × R`, with `e = (0, 1)`, every element `z` of the exterior algebra splits as `a + e ∧ b`,
where `a` and `b` are the images in `⋀ M` of `z` and of its contraction by the second coordinate
(`ExteriorAlgebra.map_inl_map_fst_add_ι_inr_mul_contractLeft_snd`). This is the
decomposition `⋀ᵏ⁺¹ (M × R) ≅ ⋀ᵏ⁺¹ M ⊕ e ∧ ⋀ᵏ M` used to adjoin one element to a Koszul complex.
-/

public section

open CliffordAlgebra

namespace TauCeti.ExteriorAlgebra

universe u v w

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/-- **An exterior-basis vector is the product of its generators in increasing order**: the basis
vector indexed by `s` is `ι (b i₁) * ⋯ * ι (b iₖ)` for `s.sort = [i₁, …, iₖ]`. -/
theorem _root_.Module.Basis.exteriorAlgebra_eq_prod_map_sort {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (s : Finset I) :
    b.ExteriorAlgebra s = ((s.sort.map b).map (ExteriorAlgebra.ι R)).prod := by
  rw [ExteriorAlgebra.basis_apply_ofCard b rfl, ExteriorAlgebra.ιMulti_family,
    ExteriorAlgebra.ιMulti_apply]
  congr 1
  refine List.ext_getElem (by simp) fun n _ _ ↦ ?_
  simp only [List.getElem_ofFn, Function.comp_apply, List.getElem_map,
    Set.powersetCard.ofFinEmbEquiv_symm_apply, Set.powersetCard.ofCard]
  exact congrArg (fun i ↦ ExteriorAlgebra.ι R (b i)) (Finset.orderEmbOfFin_apply _ _ _)

/-- Contracting an exterior-basis vector by a coordinate not in its index set gives zero. -/
@[simp]
private theorem contractLeft_coord_basis_eq_zero_of_not_mem {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) (s : Finset I) (hi : i ∉ s) :
    contractLeft (Q := (0 : QuadraticForm R M)) (b.coord i) (b.ExteriorAlgebra s) = 0 := by
  rw [b.exteriorAlgebra_eq_prod_map_sort]
  refine contractLeft_prod_map_ι_eq_zero _ fun m hm ↦ ?_
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hm
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply,
    ite_eq_right_iff]
  rintro rfl
  exact absurd ((Finset.mem_sort _).mp hj) hi

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

private def basisEraseSignOfErase {I : Type w} [LinearOrder I]
    (i : I) (t : Finset I) (hi : i ∉ t) : ℤˣ :=
  let u : Set.powersetCard I 1 := ⟨{i}, Finset.card_singleton i⟩
  let t' : Set.powersetCard I t.card := ⟨t, rfl⟩
  (Set.powersetCard.permOfDisjoint (s := u) (t := t') (by simp [u, t', hi])).sign

/-- The shuffle sign for the singleton basis vector indexed by `i` followed by the basis vector
indexed by `s.erase i`. When `i ∈ s`, this is the sign of moving `i` to the front of `s`. -/
def basisEraseSign {I : Type w} [LinearOrder I] (i : I) (s : Finset I) : ℤˣ :=
  basisEraseSignOfErase i (s.erase i) (by simp)

private theorem basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem
    {I : Type w} [LinearOrder I]
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
    -- Unfold the conjugated shuffle so both sides are compared in the increasing enumeration.
    change e (c (p (c.symm j))) = e (k.cycleRange.symm j)
    have hrhs : e (k.cycleRange.symm j) =
        (Fin.cons (e k) (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j := by
      simpa only [Function.comp_apply] using
        congrFun (Fin.cons_removeNth_eq_comp_cycleRange_symm e k) j |>.symm
    rw [hrhs, hek]
    -- The disjoint-union permutation enumerates the singleton first and the erased set second.
    change e (c (p (c.symm j))) =
      (Fin.cons i (k.removeNth (fun q ↦ e q)) : Fin (n + 1) → I) j
    rw [hremove]
    -- Expose the function represented by the increasing enumeration before applying `hec`.
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
        -- Coercing the disjoint-union subtype reveals the singleton entry.
        change ↑(Equiv.Finset.disjUnionEquiv u.val t.val hdisj
          (Sum.inl ((Set.powersetCard.orderIsoOfFin u) 0))) = i
        rw [Equiv.Finset.disjUnionEquiv_inl]
        dsimp only [Set.powersetCard.orderIsoOfFin, u]
        -- The unique increasing enumeration of a singleton is constant at its element.
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
        -- Coercing the right summand reveals the increasing enumeration of `s.erase i`.
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
  -- Unfolding the local permutation exposes the sign computed above.
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

/-- The shuffle sign which moves `i` to the front of an ordered exterior monomial is `-1`
raised to the number of indices before `i`. This formula also applies when `i ∉ s`: inserting
`i` changes neither the erased set defining the shuffle nor the indices strictly below `i`. -/
@[simp]
theorem basisEraseSign_eq_neg_one_pow_card_filter_lt {I : Type w} [LinearOrder I]
    (i : I) (s : Finset I) :
    basisEraseSign i s = (-1 : ℤˣ) ^ (s.filter (fun j ↦ j < i)).card := by
  classical
  by_cases hi : i ∈ s
  · exact basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem i s hi
  · have hsign : basisEraseSign i (insert i s) = basisEraseSign i s := by
      simp [basisEraseSign, hi]
    have hfilter : (insert i s).filter (fun j ↦ j < i) = s.filter (fun j ↦ j < i) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hji' | hjs, hji⟩
        · exact ((ne_of_lt hji) hji').elim
        · exact ⟨hjs, hji⟩
      · exact fun h ↦ ⟨Or.inr h.1, h.2⟩
    rw [← hsign, ← hfilter]
    exact basisEraseSign_eq_neg_one_pow_card_filter_lt_of_mem i (insert i s)
      (Finset.mem_insert_self i s)

/-- The exterior-basis vector indexed by a singleton is the image of the corresponding basis
vector under the exterior-algebra generator. -/
@[simp]
theorem basis_singleton {I : Type w} [LinearOrder I]
    (b : Module.Basis I R M) (i : I) :
    b.ExteriorAlgebra {i} = ExteriorAlgebra.ι R (b i) := by
  simp [b.exteriorAlgebra_eq_prod_map_sort]

/-- The exterior-basis vector indexed by a pair `{i, j}` with `i < j` is the product of the two
basis vectors in increasing order. -/
theorem basis_pair {I : Type w} [LinearOrder I] (b : Module.Basis I R M) {i j : I} (hij : i < j) :
    b.ExteriorAlgebra {i, j} = ExteriorAlgebra.ι R (b i) * ExteriorAlgebra.ι R (b j) := by
  rw [b.exteriorAlgebra_eq_prod_map_sort,
    Finset.sort_insert _ (by simpa using hij.le) (by simpa using hij.ne)]
  simp

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
  simpa [basisEraseSign, basisEraseSignOfErase, u, t] using hprod

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
        rw [hsign] at hprod'
        simpa using hprod'
      rw [hprodNeg, map_neg] at hcontract
      have h := congrArg Neg.neg hcontract
      rw [hsign]
      simpa using h
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
    let n := (s.filter fun j ↦ j < i).card
    have hsignSq : ((-1 : ℤˣ) ^ n) * ((-1 : ℤˣ) ^ n) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    rw [basisEraseSign_eq_neg_one_pow_card_filter_lt, smul_smul, hsignSq, one_smul]
  · rw [mul_zero]

/-! ### Exterior powers under the grade involution and contraction -/

/-- **The grade involution acts on the `n`-th exterior power by `(-1) ^ n`.** -/
theorem involute_of_mem_exteriorPower {n : ℕ} {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    involute (Q := (0 : QuadraticForm R M)) x = (-1 : R) ^ n • x := by
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add, ihx, ihy, smul_add]
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [map_mul, ih, involute_ι, mul_smul_comm, neg_mul, smul_neg, pow_succ', mul_smul,
      neg_one_smul]

/-- Contraction annihilates the zeroth exterior power, the scalars. -/
theorem contractLeft_eq_zero_of_mem_exteriorPower_zero (d : Module.Dual R M)
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^0 M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x = 0 := by
  rw [_root_.ExteriorAlgebra.exteriorPower, pow_zero] at hx
  obtain ⟨r, rfl⟩ := Submodule.mem_one.mp hx
  exact contractLeft_algebraMap (Q := (0 : QuadraticForm R M)) d r

/-- **Contraction lowers the exterior degree by one**: it carries the `(n + 1)`-th exterior power
into the `n`-th. -/
theorem contractLeft_mem_exteriorPower (d : Module.Dual R M) {n : ℕ}
    {x : ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^(n + 1) M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^n M := by
  suffices h : ∀ i (x : ExteriorAlgebra R M) (_ : x ∈ ⋀[R]^i M),
      contractLeft (Q := (0 : QuadraticForm R M)) d x ∈ ⋀[R]^(i - 1) M from h _ x hx
  intro i x hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r => simp
  | add x y i hx hy ihx ihy => rw [map_add]; exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨v, rfl⟩ := hm
    rw [contractLeft_ι_mul, Nat.succ_sub_one]
    refine sub_mem (Submodule.smul_mem _ _ hx) ?_
    rcases i with _ | i
    · rw [contractLeft_eq_zero_of_mem_exteriorPower_zero d hx, mul_zero]
      exact zero_mem _
    · rw [Nat.add_sub_cancel] at ih
      exact ι_mul_mem_exteriorPower v ih

/-- **Contraction of a wedge product of vectors** is the alternating sum of the contractions of
its factors: `d ⌋ (v₀ ∧ ⋯ ∧ vₙ) = ∑ᵢ (-1) ^ i d(vᵢ) v₀ ∧ ⋯ ∧ v̂ᵢ ∧ ⋯ ∧ vₙ`. -/
theorem contractLeft_ιMulti (d : Module.Dual R M) {n : ℕ} (v : Fin (n + 1) → M) :
    contractLeft (Q := (0 : QuadraticForm R M)) d (ExteriorAlgebra.ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ (i : ℕ) * d (v i)) •
        ExteriorAlgebra.ιMulti R n (i.removeNth v) := by
  induction n with
  | zero => simp [Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    have hrem (i : Fin (n + 1)) : ExteriorAlgebra.ιMulti R (n + 1) (i.succ.removeNth v) =
        ExteriorAlgebra.ι R (v 0) *
          ExteriorAlgebra.ιMulti R n (i.removeNth (Matrix.vecTail v)) := by
      rw [ExteriorAlgebra.ιMulti_succ_apply]
      congr 2
      ext j
      simp [Matrix.vecTail, Fin.removeNth_apply, Fin.succ_succAbove_succ]
    rw [ExteriorAlgebra.ιMulti_succ_apply, contractLeft_ι_mul, ih, Fin.sum_univ_succ (n := n + 1),
      Finset.mul_sum]
    simp [hrem, pow_succ, sub_eq_add_neg, Matrix.vecTail, Fin.tail,
      Function.comp_def]

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R : Type*} {M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Contraction against a functional commutes with an exterior-algebra map after pulling
back the functional. -/
theorem contractLeft_map {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N)
    (d : Module.Dual R N) (x : ExteriorAlgebra R M) :
    contractLeft (Q := (0 : QuadraticForm R N)) d (_root_.ExteriorAlgebra.map f x) =
      _root_.ExteriorAlgebra.map f
        (contractLeft (Q := (0 : QuadraticForm R M)) (d ∘ₗ f) x) := by
  -- The exterior-algebra map is the zero-quadratic-form case of the Clifford-algebra map.
  exact CliffordAlgebra.contractLeft_map { f with map_app' := fun _ => rfl } d x

/-- **A vector graded-commutes with every multivector**: moving `ι R m` past `x` applies the grade
involution to `x`. -/
theorem ι_mul_eq_involute_mul (m : M) (x : ExteriorAlgebra R M) :
    ExteriorAlgebra.ι R m * x =
      involute (Q := (0 : QuadraticForm R M)) x * ExteriorAlgebra.ι R m := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes, Algebra.commutes]
  | ι v =>
    rw [involute_ι, neg_mul, eq_neg_iff_add_eq_zero]
    exact ExteriorAlgebra.ι_add_mul_swap m v
  | mul x y hx hy => rw [← mul_assoc, hx, mul_assoc, hy, map_mul, mul_assoc]
  | add x y hx hy => rw [mul_add, hx, hy, map_add, add_mul]

end ExteriorAlgebra

namespace TauCeti.ExteriorAlgebra

open _root_.ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Contraction in degree at least the rank -/

variable [Module.Free R M] [Module.Finite R M]

/-- **A form of degree at least the rank is divisible by any vector `m` with `d m = 1`**: if
`d m = 1` and `finrank R M ≤ n`, then every `x ∈ ⋀ⁿ M` is `m ∧ (d ⌋ x)`. -/
theorem eq_ι_mul_contractLeft_of_finrank_le {d : Module.Dual R M} {m : M} (hdm : d m = 1)
    {n : ℕ} (hn : Module.finrank R M ≤ n) {x : _root_.ExteriorAlgebra R M} (hx : x ∈ ⋀[R]^n M) :
    x = ι R m * contractLeft (Q := (0 : QuadraticForm R M)) d x := by
  -- `m ∧ x` lies above the rank, so it vanishes, and contracting it by `d` gives the claim.
  have h0 : ι R m * x = 0 := ZeroMemClass.coe_eq_zero.mpr <|
    exteriorPower.eq_zero_of_finrank_lt (1 + n) (by omega)
      ⟨_, SetLike.mul_mem_graded (ι_mem_exteriorPower_one m) hx⟩
  have h := congrArg (contractLeft (Q := (0 : QuadraticForm R M)) d) h0
  rwa [contractLeft_ι_mul, hdm, one_smul, map_zero, sub_eq_zero] at h

/-- **Forms killed by a contraction multiply to zero in degree at least the rank**: if `d m = 1`,
the forms `x ∈ ⋀ᵏ M` and `y ∈ ⋀ˡ M` satisfy `d ⌋ x = 0` and `d ⌋ y = 0`, and
`finrank R M ≤ k + l`, then `x ∧ y = 0`. -/
theorem mul_eq_zero_of_contractLeft_eq_zero {d : Module.Dual R M} {m : M} (hdm : d m = 1)
    {k l : ℕ} (hkl : Module.finrank R M ≤ k + l) {x y : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^k M) (hy : y ∈ ⋀[R]^l M)
    (hdx : contractLeft (Q := (0 : QuadraticForm R M)) d x = 0)
    (hdy : contractLeft (Q := (0 : QuadraticForm R M)) d y = 0) : x * y = 0 := by
  rw [eq_ι_mul_contractLeft_of_finrank_le hdm hkl (SetLike.mul_mem_graded hx hy), contractLeft_mul,
    hdx, hdy, zero_mul, mul_zero, add_zero, mul_zero]

/-- **The square of a two-form in rank at most four.** If `d m = 1` and `finrank R M ≤ 4`, a
two-form `x` satisfies `x ∧ x = 2 x ∧ m ∧ (d ⌋ x)`. -/
theorem mul_self_eq_two_smul_mul_ι_mul_contractLeft {d : Module.Dual R M} {m : M}
    (hdm : d m = 1) (h4 : Module.finrank R M ≤ 4) {x : _root_.ExteriorAlgebra R M}
    (hx : x ∈ ⋀[R]^2 M) :
    x * x = 2 • (x * (ι R m * contractLeft (Q := (0 : QuadraticForm R M)) d x)) := by
  -- Write `x = m ∧ a + b` with `a = d ⌋ x`. Then `d ⌋ b = 0`, so `b ∧ b = 0` in rank at most
  -- four; also `(m ∧ a) ∧ (m ∧ a) = 0`, and the two-forms `m ∧ a` and `b` commute.
  -- The contraction `d ⌋ x` is a vector `a`.
  obtain ⟨a, ha⟩ : ∃ a, ι R a = contractLeft (Q := (0 : QuadraticForm R M)) d x :=
    ⟨_, ι_ιInv_of_mem_exteriorPower_one (contractLeft_mem_exteriorPower d (n := 1) hx)⟩
  rw [← ha]
  set g := ι R m * ι R a with hg
  have hgmem : g ∈ ⋀[R]^2 M :=
    SetLike.mul_mem_graded (ι_mem_exteriorPower_one m) (ι_mem_exteriorPower_one a)
  -- The remainder `b = x - m ∧ a` is a two-form killed by `d`.
  set b := x - g with hb
  have hbmem : b ∈ ⋀[R]^2 M := sub_mem hx hgmem
  have hdb : contractLeft (Q := (0 : QuadraticForm R M)) d b = 0 := by
    have hda : contractLeft (Q := (0 : QuadraticForm R M)) d (ι R a) = 0 := by
      rw [ha, contractLeft_contractLeft]
    rw [hb, map_sub, hg, contractLeft_ι_mul, hdm, one_smul, hda, mul_zero, sub_zero, ha,
      sub_self]
  have hbb : b * b = 0 :=
    mul_eq_zero_of_contractLeft_eq_zero hdm (by omega) hbmem hbmem hdb hdb
  have hgg : g * g = 0 := by
    have h := ι_add_mul_swap (R := R) a m
    rw [add_eq_zero_iff_eq_neg] at h
    calc g * g = ι R m * (ι R a * ι R m) * ι R a := by simp only [hg, mul_assoc]
      _ = 0 := by rw [h, mul_neg, ← mul_assoc, ι_sq_zero, zero_mul, neg_zero, zero_mul]
  -- A two-form is fixed by the grade involution, so it commutes with the two-form `g`.
  have hinv : involute (Q := (0 : QuadraticForm R M)) b = b := by
    rw [involute_of_mem_exteriorPower hbmem]
    simp
  have hcomm : g * b = b * g := by
    rw [hg, mul_assoc, ι_mul_eq_involute_mul a b, hinv, ← mul_assoc, ι_mul_eq_involute_mul m b,
      hinv, mul_assoc]
  have hx' : x = b + g := (sub_add_cancel x g).symm
  rw [hx', add_mul, mul_add, mul_add, hbb, hgg, hcomm, add_mul, hgg, two_smul]
  abel

end TauCeti.ExteriorAlgebra

namespace ExteriorAlgebra

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-! ### Splitting off a free coordinate -/

/-- **Splitting off a free coordinate.** In the exterior algebra of `M × R`, with `e = (0, 1)`,
every element `z` is `a + e ∧ b`, where `a` is the image of `z` under `⋀ M × R → ⋀ M → ⋀ (M × R)`
and `b` is the image of the contraction of `z` by the second coordinate. -/
theorem map_inl_map_fst_add_ι_inr_mul_contractLeft_snd (z : ExteriorAlgebra R (M × R)) :
    map (LinearMap.inl R M R) (map (LinearMap.fst R M R) z) +
        ι R (LinearMap.inr R M R 1) * map (LinearMap.inl R M R) (map (LinearMap.fst R M R)
          (contractLeft (Q := (0 : QuadraticForm R (M × R))) (LinearMap.snd R M R) z)) =
      z := by
  induction z using CliffordAlgebra.left_induction with
  | algebraMap r => simp [contractLeft_algebraMap]
  | add z₁ z₂ h₁ h₂ =>
    simp only [map_add, mul_add]
    conv_rhs => rw [← h₁, ← h₂]
    abel
  | ι_mul z m ih =>
    -- Write `m = (m₁, 0) + m₂ e`; then `e ∧ e = 0` and `(m₁, 0) ∧ e = -(e ∧ (m₁, 0))`.
    have hm : ι R m = ι R (LinearMap.inl R M R m.1) + m.2 • ι R (LinearMap.inr R M R 1) := by
      rw [← map_smul, ← map_add]; congr 1; ext <;> simp
    have he := ι_sq_zero (R := R) (LinearMap.inr R M R (1 : R))
    have hc := eq_neg_of_add_eq_zero_right <|
      ι_add_mul_swap (R := R) (LinearMap.inr R M R (1 : R)) (LinearMap.inl R M R m.1)
    -- `left_induction` states the step with `CliffordAlgebra.ι 0`, which is `ι R` by definition.
    change _ = ι R m * z
    rw [contractLeft_ι_mul]
    simp only [map_mul, map_sub, map_smul, map_apply_ι]
    conv_rhs => rw [← ih, hm]
    simp only [add_mul, mul_add, mul_sub, smul_mul_assoc, mul_smul_comm, ← mul_assoc, he, hc,
      smul_zero, add_zero, neg_mul, LinearMap.fst_apply, LinearMap.snd_apply]
    abel

end ExteriorAlgebra
