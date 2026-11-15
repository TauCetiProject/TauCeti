/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Character
import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Cyclic
import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Quaternion

/-!
# Inverse maps, power maps, and homomorphism fusion on numbered conjugacy classes

Given conjugacy-class data `d : TauCeti.ClassData G`, inversion and `n`-th powering of group
elements induce operations on the class indices `Fin d.numClasses`, and any group homomorphism
`φ : H →* G` induces a **class-fusion** map `Fin dH.numClasses → Fin dG.numClasses` sending the
index of a class of `H` to the index of the class of `G` containing its image. Together with
representative orders and centralizer indices, these maps form the column metadata of an ordinary
character table:

* the inverse map `d.invIndex` permutes the class indices involutively, fixing `i` if and only if
  `d.classOf i` is a real conjugacy class, and preserving representative orders, centralizer
  indices, and class sizes;
* the power maps `d.powIndex n` and `d.zpowIndex z` track `C ↦ C ^ n` on `ConjClasses G`, compose
  multiplicatively in the exponent, depend only on the residue of `n` modulo `orderOf (d.rep i)`,
  and permute the class indices bijectively whenever `n` is coprime to every representative order
  (in particular, whenever `n` is coprime to `Nat.card G`);
* the fusion map `dH.fusion dG φ` tracks `ConjClasses.map φ`, composes functorially, commutes with
  inversion and powers, divides representative orders (preserving them when `φ` is injective), and
  evaluates restricted characters `Representation.character (ρ.comp φ)` at the representatives of
  `dH` by reading `ρ.character` along the fused indices in `dG`.

For groups whose class data is certified from explicit conjugating witnesses rather than by brute
enumeration, each index equation (`d.invIndex i = j`, `d.powIndex n i = j`,
`dH.fusion dG φ i = j`) is paired both with its witness-certified rule (`c * rep * c⁻¹ = ...`) and
with a decidability-free `classOf` characterization, as well as transport lemmas across
`TauCeti.ClassData.map`.

## Main definitions

* `TauCeti.ClassData.invIndex`, `TauCeti.ClassData.invEquiv`: the numbered inverse-class map and
  its involutive permutation of `Fin d.numClasses`.
* `TauCeti.ClassData.powIndex`, `TauCeti.ClassData.zpowIndex`: the numbered `ℕ`-power and
  `ℤ`-power maps on `Fin d.numClasses`.
* `TauCeti.ClassData.fusion`: the class-fusion map `Fin dH.numClasses → Fin dG.numClasses` along a
  group homomorphism `φ : H →* G`.

## Main results

* `TauCeti.ClassData.classOf_bijective`: `d.classOf` is a bijection onto `ConjClasses G` without
  assuming decidable conjugacy.
* `TauCeti.ClassData.orderOf_rep_map`, `TauCeti.ClassData.index_centralizer_rep_map`,
  `TauCeti.ClassData.invIndex_map`, `TauCeti.ClassData.powIndex_map`: transport of representative
  orders, centralizer indices, inverse maps, and power maps along `TauCeti.ClassData.map`.
* `TauCeti.ClassData.invIndex_eq_self_iff`: `d.invIndex` fixes `i` if and only if `d.classOf i` is
  a real class (`TauCeti.IsRealClass`).
* `TauCeti.ClassData.bijective_powIndex_of_coprime`,
  `TauCeti.ClassData.bijective_powIndex_of_coprime_card`: coprime power maps permute the numbered
  classes bijectively and preserve class sizes.
* `TauCeti.ClassData.classOf_fusion`, `TauCeti.ClassData.fusion_comp`,
  `TauCeti.ClassData.character_rep_fusion`: compatibility of `fusion` with `ConjClasses.map`,
  composition of homomorphisms, and character restriction.

## References

* J. D. Dixon, *High speed computation of group characters*, Numer. Math. **10** (1967), 446–450.
* I. M. Isaacs, *Character Theory of Finite Groups*, Academic Press (1976).
-/

public section

namespace TauCeti.ClassData

section Invariants

variable {G : Type*} [Group G] (d : ClassData G)

/-- **Distinct indices name distinct conjugacy classes**, without assuming decidable conjugacy. -/
@[simp]
theorem classOf_inj {i j : Fin d.numClasses} : d.classOf i = d.classOf j ↔ i = j := by
  refine ⟨fun h => by_contra fun hne => d.not_isConj_rep hne ?_, congrArg _⟩
  rwa [classOf_eq_mk, classOf_eq_mk, ConjClasses.mk_eq_mk_iff_isConj] at h

/-- `TauCeti.ClassData.classOf` is injective without assuming decidable conjugacy. -/
theorem classOf_injective : Function.Injective d.classOf :=
  fun _ _ => d.classOf_inj.mp

/-- `TauCeti.ClassData.classOf` is surjective without assuming decidable conjugacy. -/
theorem classOf_surjective : Function.Surjective d.classOf := by
  refine ConjClasses.forall_isConj.mpr fun g => ?_
  obtain ⟨x, hx, hxg⟩ := d.exists_isConj g
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  refine ⟨⟨i, hi⟩, ?_⟩
  rw [d.classOf_eq_mk]
  exact ConjClasses.mk_eq_mk_iff_isConj.mpr hxg

/-- **The class numbering is a bijection** onto `ConjClasses G`, without assuming decidable
conjugacy or finiteness. -/
theorem classOf_bijective : Function.Bijective d.classOf :=
  ⟨d.classOf_injective, d.classOf_surjective⟩

/-- Two numbered classes satisfy `d.classOf j = (d.classOf i)⁻¹` if and only if the `j`-th
representative is conjugate to the inverse of the `i`-th. -/
theorem classOf_eq_inv_iff {i j : Fin d.numClasses} :
    d.classOf j = (d.classOf i)⁻¹ ↔ IsConj (d.rep j) (d.rep i)⁻¹ := by
  rw [classOf_eq_mk, classOf_eq_mk, ConjClasses.inv_mk, ConjClasses.mk_eq_mk_iff_isConj]

/-- Two numbered classes satisfy `d.classOf j = d.classOf i ^ n` if and only if the `j`-th
representative is conjugate to the `n`-th power of the `i`-th. -/
theorem classOf_eq_pow_iff {n : ℕ} {i j : Fin d.numClasses} :
    d.classOf j = d.classOf i ^ n ↔ IsConj (d.rep j) (d.rep i ^ n) := by
  rw [classOf_eq_mk, classOf_eq_mk, ConjClasses.mk_pow, ConjClasses.mk_eq_mk_iff_isConj]

/-- For a homomorphism `φ : H →* G`, the `j`-th class of `G` is the image of the `i`-th class of
`H` under `ConjClasses.map φ` if and only if `d.rep j` is conjugate to `φ (dH.rep i)`. -/
theorem classOf_eq_map_iff {H : Type*} [Group H] (dH : ClassData H) (φ : H →* G)
    {i : Fin dH.numClasses} {j : Fin d.numClasses} :
    d.classOf j = ConjClasses.map φ (dH.classOf i) ↔ IsConj (d.rep j) (φ (dH.rep i)) := by
  rw [classOf_eq_mk, classOf_eq_mk, ConjClasses.map_mk, ConjClasses.mk_eq_mk_iff_isConj]

/-- The `Set.ncard` of the `i`-th conjugacy class is the centralizer index of its
representative. -/
@[simp]
theorem ncard_carrier_classOf (i : Fin d.numClasses) :
    (d.classOf i).carrier.ncard = (Subgroup.centralizer {d.rep i}).index := by
  rw [d.classOf_eq_mk, ConjClasses.ncard_carrier_mk]

/-- The `Nat.card` of the `i`-th conjugacy class is the centralizer index of its representative. -/
theorem card_carrier_classOf (i : Fin d.numClasses) :
    Nat.card (d.classOf i).carrier = (Subgroup.centralizer {d.rep i}).index := by
  rw [d.classOf_eq_mk, ConjClasses.card_carrier_mk]

/-- In a finite group, the size of the `i`-th class `Finset` is the centralizer index of its
representative. -/
theorem card_classFinset_eq_index_centralizer [Fintype G]
    [DecidableRel (IsConj : G → G → Prop)] (i : Fin d.numClasses) :
    (d.classFinset i).card = (Subgroup.centralizer {d.rep i}).index := by
  rw [d.card_classFinset, d.card_carrier_classOf]

/-- Every element has the same order as the chosen representative of its conjugacy class. -/
@[simp]
theorem orderOf_rep_index [DecidableRel (IsConj : G → G → Prop)] (g : G) :
    orderOf (d.rep (d.index g)) = orderOf g := by
  by_contra hne
  exact ConjClasses.mk_ne_mk_of_orderOf_ne hne
    (ConjClasses.mk_eq_mk_iff_isConj.mpr (d.isConj_rep_index g))

/-- Every element has the same centralizer index as the chosen representative of its conjugacy
class. -/
@[simp]
theorem index_centralizer_rep_index [DecidableRel (IsConj : G → G → Prop)] (g : G) :
    (Subgroup.centralizer {d.rep (d.index g)}).index = (Subgroup.centralizer {g}).index := by
  rw [← ConjClasses.card_carrier_mk, ← ConjClasses.card_carrier_mk, ← d.classOf_eq_mk,
    d.classOf_index]

end Invariants

/-! ### Transport of representative invariants along a multiplicative equivalence -/

section MapInvariants

variable {G H : Type*} [Group G] [Group H] (e : G ≃* H) (d : ClassData G)

/-- Transporting class data along a multiplicative equivalence preserves the order of each
representative. -/
theorem orderOf_rep_map (i : Fin (d.map e).numClasses) :
    orderOf ((d.map e).rep i) = orderOf (d.rep (Fin.cast (d.numClasses_map e) i)) := by
  rw [rep_map, e.orderOf_eq]

/-- Transporting class data along a multiplicative equivalence preserves the centralizer index of
each representative. -/
theorem index_centralizer_rep_map (i : Fin (d.map e).numClasses) :
    (Subgroup.centralizer {(d.map e).rep i}).index =
      (Subgroup.centralizer {d.rep (Fin.cast (d.numClasses_map e) i)}).index := by
  have hcomap :
      Subgroup.centralizer {(d.map e).rep i} =
        (Subgroup.centralizer {d.rep (Fin.cast (d.numClasses_map e) i)}).comap
          e.symm.toMonoidHom := by
    ext y
    simp only [rep_map, Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_comap,
      MulEquiv.coe_toMonoidHom]
    exact ⟨fun h => by simpa using congrArg e.symm h, fun h => by simpa using congrArg e h⟩
  rw [hcomap]
  exact Subgroup.index_comap_of_surjective _ e.symm.surjective

/-- Transporting class data along a multiplicative equivalence preserves the centralizer order of
each representative. -/
theorem card_centralizer_rep_map (i : Fin (d.map e).numClasses) :
    Nat.card (Subgroup.centralizer {(d.map e).rep i}) =
      Nat.card (Subgroup.centralizer {d.rep (Fin.cast (d.numClasses_map e) i)}) := by
  refine Nat.card_congr
    { toFun := fun ⟨y, hy⟩ => ⟨e.symm y, ?_⟩
      invFun := fun ⟨x, hx⟩ => ⟨e x, ?_⟩
      left_inv := fun ⟨y, _⟩ => Subtype.ext (e.apply_symm_apply y)
      right_inv := fun ⟨x, _⟩ => Subtype.ext (e.symm_apply_apply x) }
  · have hy' : y * e (d.rep (Fin.cast (d.numClasses_map e) i)) =
        e (d.rep (Fin.cast (d.numClasses_map e) i)) * y := by
      simpa only [rep_map] using Subgroup.mem_centralizer_singleton_iff.mp hy
    exact Subgroup.mem_centralizer_singleton_iff.mpr (by simpa using congrArg e.symm hy')
  · have hx' := Subgroup.mem_centralizer_singleton_iff.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff, rep_map]
    simpa using congrArg e hx'

end MapInvariants

/-! ### The numbered inverse-class map -/

section Inv

variable {G : Type*} [Group G] [DecidableRel (IsConj : G → G → Prop)] (d : ClassData G)

/-- **The numbered inverse-class map**: sends class index `i` to the class index of `(d.rep i)⁻¹`.
Exposed so concrete groups evaluate their inverse-class tables in the kernel. -/
@[expose] def invIndex (i : Fin d.numClasses) : Fin d.numClasses :=
  d.index (d.rep i)⁻¹

/-- The `d.invIndex i`-th representative is conjugate to `(d.rep i)⁻¹`. -/
theorem isConj_rep_invIndex (i : Fin d.numClasses) :
    IsConj (d.rep (d.invIndex i)) (d.rep i)⁻¹ :=
  d.isConj_rep_index (d.rep i)⁻¹

/-- `d.invIndex i` equals `j` if and only if `d.rep j` is conjugate to `(d.rep i)⁻¹`. -/
theorem invIndex_eq_iff {i j : Fin d.numClasses} :
    d.invIndex i = j ↔ IsConj (d.rep j) (d.rep i)⁻¹ :=
  d.index_eq_iff

/-- Certify `d.invIndex i = j` directly from an explicit conjugating element `c`. -/
theorem invIndex_eq_of_conj {i j : Fin d.numClasses} (c : G)
    (hc : c * d.rep j * c⁻¹ = (d.rep i)⁻¹) : d.invIndex i = j :=
  d.invIndex_eq_iff.mpr (isConj_iff.mpr ⟨c, hc⟩)

/-- **The inverse-class map tracks element inversion** under `TauCeti.ClassData.index`. -/
@[simp]
theorem invIndex_index (g : G) : d.invIndex (d.index g) = d.index g⁻¹ :=
  d.index_eq_index_iff.mpr (isConj_inv_iff.mpr (d.isConj_rep_index g))

/-- **The inverse-class map tracks inversion on `ConjClasses G`.** -/
@[simp]
theorem classOf_invIndex (i : Fin d.numClasses) :
    d.classOf (d.invIndex i) = (d.classOf i)⁻¹ := by
  rw [invIndex, classOf_index, classOf_eq_mk, ConjClasses.inv_mk]

/-- `TauCeti.ClassData.indexClass` intertwines inversion on `ConjClasses G` with `d.invIndex`. -/
@[simp]
theorem indexClass_inv (C : ConjClasses G) :
    d.indexClass C⁻¹ = d.invIndex (d.indexClass C) := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [ConjClasses.inv_mk, indexClass_mk, indexClass_mk, invIndex_index]

/-- **The numbered inverse-class map is an involution.** -/
@[simp]
theorem invIndex_invIndex (i : Fin d.numClasses) : d.invIndex (d.invIndex i) = i := by
  apply d.classOf_injective
  rw [classOf_invIndex, classOf_invIndex, inv_inv]

/-- `TauCeti.ClassData.invIndex` is involutive. -/
theorem invIndex_involutive : Function.Involutive d.invIndex :=
  d.invIndex_invIndex

/-- `TauCeti.ClassData.invIndex` is a bijection on `Fin d.numClasses`. -/
theorem invIndex_bijective : Function.Bijective d.invIndex :=
  d.invIndex_involutive.bijective

/-- **The inverse-class involution bundled as a permutation** of `Fin d.numClasses`. -/
@[expose] def invEquiv : Equiv.Perm (Fin d.numClasses) where
  toFun := d.invIndex
  invFun := d.invIndex
  left_inv := d.invIndex_invIndex
  right_inv := d.invIndex_invIndex

@[simp]
theorem invEquiv_apply (i : Fin d.numClasses) : d.invEquiv i = d.invIndex i := (rfl)

@[simp]
theorem invEquiv_symm : d.invEquiv.symm = d.invEquiv := (rfl)

/-- **A class index is fixed by `d.invIndex` if and only if the class it names is real.** -/
theorem invIndex_eq_self_iff {i : Fin d.numClasses} :
    d.invIndex i = i ↔ IsRealClass (d.classOf i) := by
  rw [← d.classOf_inj, classOf_invIndex, isRealClass_iff_inv_eq]

/-- A class representative and that of its inverse class have the same element order. -/
@[simp]
theorem orderOf_rep_invIndex (i : Fin d.numClasses) :
    orderOf (d.rep (d.invIndex i)) = orderOf (d.rep i) := by
  rw [invIndex, orderOf_rep_index, orderOf_inv]

/-- A class representative and that of its inverse class have the same centralizer index. -/
@[simp]
theorem index_centralizer_rep_invIndex (i : Fin d.numClasses) :
    (Subgroup.centralizer {d.rep (d.invIndex i)}).index =
      (Subgroup.centralizer {d.rep i}).index := by
  rw [← d.card_carrier_classOf, ← d.card_carrier_classOf, classOf_invIndex,
    ConjClasses.card_carrier_inv]

/-- A numbered class and its inverse class have the same cardinality. -/
@[simp]
theorem card_classFinset_invIndex [Fintype G] (i : Fin d.numClasses) :
    (d.classFinset (d.invIndex i)).card = (d.classFinset i).card := by
  rw [card_classFinset_eq_index_centralizer, card_classFinset_eq_index_centralizer,
    index_centralizer_rep_invIndex]

/-- **Transport of the inverse-class map** across a multiplicative equivalence. -/
@[simp]
theorem invIndex_map {H : Type*} [Group H] [DecidableRel (IsConj : H → H → Prop)]
    (e : G ≃* H) (i : Fin (d.map e).numClasses) :
    (d.map e).invIndex i =
      Fin.cast (d.numClasses_map e).symm (d.invIndex (Fin.cast (d.numClasses_map e) i)) := by
  rw [invIndex, rep_map, index_map_inv, invIndex]

end Inv

/-! ### Numbered power maps -/

section Pow

variable {G : Type*} [Group G] [DecidableRel (IsConj : G → G → Prop)] (d : ClassData G)

/-- **The numbered `n`-th power map**: sends class index `i` to the class index of `d.rep i ^ n`.
Exposed so concrete groups evaluate their power-map tables in the kernel. -/
@[expose] def powIndex (n : ℕ) (i : Fin d.numClasses) : Fin d.numClasses :=
  d.index (d.rep i ^ n)

/-- The `d.powIndex n i`-th representative is conjugate to `d.rep i ^ n`. -/
theorem isConj_rep_powIndex (n : ℕ) (i : Fin d.numClasses) :
    IsConj (d.rep (d.powIndex n i)) (d.rep i ^ n) :=
  d.isConj_rep_index (d.rep i ^ n)

/-- `d.powIndex n i` equals `j` if and only if `d.rep j` is conjugate to `d.rep i ^ n`. -/
theorem powIndex_eq_iff {n : ℕ} {i j : Fin d.numClasses} :
    d.powIndex n i = j ↔ IsConj (d.rep j) (d.rep i ^ n) :=
  d.index_eq_iff

/-- Certify `d.powIndex n i = j` directly from an explicit conjugating element `c`. -/
theorem powIndex_eq_of_conj {n : ℕ} {i j : Fin d.numClasses} (c : G)
    (hc : c * d.rep j * c⁻¹ = d.rep i ^ n) : d.powIndex n i = j :=
  d.powIndex_eq_iff.mpr (isConj_iff.mpr ⟨c, hc⟩)

/-- **The power map tracks element powers** under `TauCeti.ClassData.index`. -/
@[simp]
theorem powIndex_index (n : ℕ) (g : G) : d.powIndex n (d.index g) = d.index (g ^ n) :=
  d.index_eq_index_iff.mpr ((d.isConj_rep_index g).pow n)

/-- **The numbered power map tracks `C ↦ C ^ n` on `ConjClasses G`.** -/
@[simp]
theorem classOf_powIndex (n : ℕ) (i : Fin d.numClasses) :
    d.classOf (d.powIndex n i) = d.classOf i ^ n := by
  rw [powIndex, classOf_index, classOf_eq_mk, ConjClasses.mk_pow]

/-- `TauCeti.ClassData.indexClass` intertwines `C ↦ C ^ n` with `d.powIndex n`. -/
@[simp]
theorem indexClass_pow (C : ConjClasses G) (n : ℕ) :
    d.indexClass (C ^ n) = d.powIndex n (d.indexClass C) := by
  obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
  rw [ConjClasses.mk_pow, indexClass_mk, indexClass_mk, powIndex_index]

/-- The `0`-th power map sends every class index to the index of the identity element. -/
@[simp]
theorem powIndex_zero (i : Fin d.numClasses) : d.powIndex 0 i = d.index 1 := by
  rw [powIndex, pow_zero]

/-- The `1`-st power map is the identity on class indices. -/
@[simp]
theorem powIndex_one (i : Fin d.numClasses) : d.powIndex 1 i = i := by
  rw [powIndex, pow_one, index_rep]

/-- **Iterated power maps compose**: `m`-th powering followed by `n`-th powering is `(m * n)`-th
powering. Oriented to match `ConjClasses.pow_mul`. -/
@[simp]
theorem powIndex_powIndex (m n : ℕ) (i : Fin d.numClasses) :
    d.powIndex n (d.powIndex m i) = d.powIndex (m * n) i := by
  apply d.classOf_injective
  rw [classOf_powIndex, classOf_powIndex, classOf_powIndex, ConjClasses.pow_mul]

/-- Any two power maps commute. -/
theorem powIndex_comm (m n : ℕ) (i : Fin d.numClasses) :
    d.powIndex m (d.powIndex n i) = d.powIndex n (d.powIndex m i) := by
  rw [powIndex_powIndex, powIndex_powIndex, mul_comm]

/-- Power maps commute with the inverse-class map. -/
@[simp]
theorem powIndex_invIndex (n : ℕ) (i : Fin d.numClasses) :
    d.powIndex n (d.invIndex i) = d.invIndex (d.powIndex n i) := by
  rw [invIndex, powIndex_index, inv_pow, ← invIndex_index, ← powIndex]

/-- The order of the `n`-th power class representative, for `n ≠ 0`, is
`orderOf (d.rep i) / gcd (orderOf (d.rep i)) n`. -/
theorem orderOf_rep_powIndex {n : ℕ} (hn : n ≠ 0) (i : Fin d.numClasses) :
    orderOf (d.rep (d.powIndex n i)) = orderOf (d.rep i) / Nat.gcd (orderOf (d.rep i)) n := by
  rw [powIndex, orderOf_rep_index, orderOf_pow' _ hn]

/-- A power coprime to `orderOf (d.rep i)` preserves the representative's element order. -/
theorem orderOf_rep_powIndex_of_coprime {n : ℕ} {i : Fin d.numClasses}
    (hn : (orderOf (d.rep i)).Coprime n) :
    orderOf (d.rep (d.powIndex n i)) = orderOf (d.rep i) := by
  rw [powIndex, orderOf_rep_index, hn.orderOf_pow]

/-- **The `n`-th power of class `i` depends only on `n` modulo `orderOf (d.rep i)`.** For elements
of infinite order (`orderOf (d.rep i) = 0`), congruence modulo `0` is equality and the statement
still holds. -/
theorem powIndex_eq_of_modEq {m n : ℕ} {i : Fin d.numClasses}
    (h : m ≡ n [MOD orderOf (d.rep i)]) : d.powIndex m i = d.powIndex n i := by
  have hpow : d.rep i ^ m = d.rep i ^ n := by
    simpa only [zpow_natCast] using zpow_eq_zpow_iff_modEq.mpr (Int.natCast_modEq_iff.mpr h)
  rw [powIndex, powIndex, hpow]

/-- Raising class `i` to a power coprime to `orderOf (d.rep i)` preserves its centralizer index. -/
theorem index_centralizer_rep_powIndex_of_coprime {n : ℕ} {i : Fin d.numClasses}
    (hn : (orderOf (d.rep i)).Coprime n) :
    (Subgroup.centralizer {d.rep (d.powIndex n i)}).index =
      (Subgroup.centralizer {d.rep i}).index := by
  rw [← d.card_carrier_classOf, ← d.card_carrier_classOf, classOf_powIndex, classOf_eq_mk,
    ConjClasses.mk_pow]
  exact ConjClasses.card_carrier_mk_pow (d.rep i) hn

/-- Raising class `i` to a power coprime to `orderOf (d.rep i)` preserves the cardinality of its
numbered class `Finset`. -/
theorem card_classFinset_powIndex_of_coprime [Fintype G] {n : ℕ} {i : Fin d.numClasses}
    (hn : (orderOf (d.rep i)).Coprime n) :
    (d.classFinset (d.powIndex n i)).card = (d.classFinset i).card := by
  rw [card_classFinset_eq_index_centralizer, card_classFinset_eq_index_centralizer,
    d.index_centralizer_rep_powIndex_of_coprime hn]

/-- **The numbered `ℤ`-power map**: sends class index `i` to the class index of `d.rep i ^ z`,
unifying `powIndex` and `invIndex`. -/
@[expose] def zpowIndex (z : ℤ) (i : Fin d.numClasses) : Fin d.numClasses :=
  d.index (d.rep i ^ z)

/-- The `d.zpowIndex z i`-th representative is conjugate to `d.rep i ^ z`. -/
theorem isConj_rep_zpowIndex (z : ℤ) (i : Fin d.numClasses) :
    IsConj (d.rep (d.zpowIndex z i)) (d.rep i ^ z) :=
  d.isConj_rep_index (d.rep i ^ z)

/-- `d.zpowIndex z i` equals `j` if and only if `d.rep j` is conjugate to `d.rep i ^ z`. -/
theorem zpowIndex_eq_iff {z : ℤ} {i j : Fin d.numClasses} :
    d.zpowIndex z i = j ↔ IsConj (d.rep j) (d.rep i ^ z) :=
  d.index_eq_iff

/-- **The `ℤ`-power map tracks integer powers** under `TauCeti.ClassData.index`. -/
@[simp]
theorem zpowIndex_index (z : ℤ) (g : G) : d.zpowIndex z (d.index g) = d.index (g ^ z) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (d.isConj_rep_index g)
  refine d.index_eq_index_iff.mpr (isConj_iff.mpr ⟨c, ?_⟩)
  simpa only [MulAut.conj_apply, hc] using map_zpow (MulAut.conj c) (d.rep (d.index g)) z

/-- On natural exponents, `zpowIndex` agrees with `powIndex`. -/
@[simp]
theorem zpowIndex_natCast (n : ℕ) (i : Fin d.numClasses) :
    d.zpowIndex (n : ℤ) i = d.powIndex n i := by
  rw [zpowIndex, zpow_natCast, powIndex]

@[simp]
theorem zpowIndex_zero (i : Fin d.numClasses) : d.zpowIndex 0 i = d.index 1 := by
  rw [zpowIndex, zpow_zero]

@[simp]
theorem zpowIndex_one (i : Fin d.numClasses) : d.zpowIndex 1 i = i := by
  rw [zpowIndex, zpow_one, index_rep]

/-- At `-1`, `zpowIndex` is the inverse-class map `d.invIndex`. -/
@[simp]
theorem zpowIndex_neg_one (i : Fin d.numClasses) : d.zpowIndex (-1) i = d.invIndex i := by
  rw [zpowIndex, zpow_neg_one, invIndex]

/-- Negating the integer exponent composes with `d.invIndex`. -/
theorem zpowIndex_neg (z : ℤ) (i : Fin d.numClasses) :
    d.zpowIndex (-z) i = d.invIndex (d.zpowIndex z i) := by
  rw [zpowIndex, zpow_neg, ← invIndex_index, zpowIndex]

/-- Iterated `ℤ`-power maps compose multiplicatively. -/
@[simp]
theorem zpowIndex_zpowIndex (z w : ℤ) (i : Fin d.numClasses) :
    d.zpowIndex w (d.zpowIndex z i) = d.zpowIndex (z * w) i := by
  rw [← d.index_rep i, zpowIndex_index, zpowIndex_index, zpowIndex_index, ← zpow_mul]

/-- The `z`-th integer power of class `i` depends only on `z` modulo `orderOf (d.rep i)`. -/
theorem zpowIndex_eq_of_modEq {z w : ℤ} {i : Fin d.numClasses}
    (h : z ≡ w [ZMOD orderOf (d.rep i)]) : d.zpowIndex z i = d.zpowIndex w i := by
  rw [zpowIndex, zpowIndex, zpow_eq_zpow_iff_modEq.mpr h]

/-- **A power map coprime to every representative order is a bijection** on `Fin d.numClasses`,
without assuming `G` is finite. -/
theorem bijective_powIndex_of_coprime {n : ℕ}
    (hn : ∀ i, (orderOf (d.rep i)).Coprime n) : Function.Bijective (d.powIndex n) := by
  refine Finite.injective_iff_bijective.mp fun i₁ i₂ h => ?_
  have hord : orderOf (d.rep i₁) = orderOf (d.rep i₂) := by
    rw [← d.orderOf_rep_powIndex_of_coprime (hn i₁), h,
      d.orderOf_rep_powIndex_of_coprime (hn i₂)]
  obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_pow_iff.mpr (hn i₁).symm)
  have hz₁ : d.rep i₁ ^ ((n : ℤ) * z) = d.rep i₁ ^ (1 : ℤ) := by
    rw [zpow_mul, zpow_natCast, zpow_one, hz]
  have hz₂ : (d.rep i₂ ^ n) ^ z = d.rep i₂ := by
    rw [← zpow_natCast, ← zpow_mul]
    conv_rhs => rw [← zpow_one (d.rep i₂)]
    rw [zpow_eq_zpow_iff_modEq, ← hord, ← zpow_eq_zpow_iff_modEq]
    exact hz₁
  calc
    i₁ = d.index ((d.rep i₁ ^ n) ^ z) := by rw [hz, d.index_rep]
    _ = d.zpowIndex z (d.powIndex n i₁) := by rw [powIndex, zpowIndex_index]
    _ = d.zpowIndex z (d.powIndex n i₂) := by rw [h]
    _ = d.index ((d.rep i₂ ^ n) ^ z) := by rw [powIndex, zpowIndex_index]
    _ = i₂ := by rw [hz₂, d.index_rep]

/-- **Any power coprime to `Nat.card G` induces a bijection** on `Fin d.numClasses`. For infinite
`G`, `Nat.card G = 0`, so `(Nat.card G).Coprime n` forces `n = 1` and the result still holds. -/
theorem bijective_powIndex_of_coprime_card {n : ℕ}
    (hn : (Nat.card G).Coprime n) : Function.Bijective (d.powIndex n) := by
  cases finite_or_infinite G with
  | inl _ =>
      exact d.bijective_powIndex_of_coprime fun i => hn.of_dvd_left (orderOf_dvd_natCard _)
  | inr _ =>
      have hn1 : n = 1 :=
        (Nat.coprime_zero_left n).mp (by rwa [Nat.card_eq_zero_of_infinite] at hn)
      rw [hn1]
      exact ⟨fun _ _ h => by simpa using h, fun i => ⟨i, d.powIndex_one i⟩⟩

/-- **Transport of the `ℕ`-power map** across a multiplicative equivalence. -/
@[simp]
theorem powIndex_map {H : Type*} [Group H] [DecidableRel (IsConj : H → H → Prop)]
    (e : G ≃* H) (n : ℕ) (i : Fin (d.map e).numClasses) :
    (d.map e).powIndex n i =
      Fin.cast (d.numClasses_map e).symm (d.powIndex n (Fin.cast (d.numClasses_map e) i)) := by
  rw [powIndex, rep_map, index_map_pow, powIndex]

/-- **Transport of the `ℤ`-power map** across a multiplicative equivalence. -/
@[simp]
theorem zpowIndex_map {H : Type*} [Group H] [DecidableRel (IsConj : H → H → Prop)]
    (e : G ≃* H) (z : ℤ) (i : Fin (d.map e).numClasses) :
    (d.map e).zpowIndex z i =
      Fin.cast (d.numClasses_map e).symm (d.zpowIndex z (Fin.cast (d.numClasses_map e) i)) := by
  rw [zpowIndex, rep_map, ← map_zpow, index_map, zpowIndex]

end Pow

/-! ### Subgroup and homomorphism class-fusion maps -/

section Fusion

variable {H G K : Type*} [Group H] [Group G] [Group K]

/-- **The numbered class-fusion map** along a group homomorphism `φ : H →* G`: sends class index
`i` of `dH` to the class index in `dG` of `φ (dH.rep i)`. Only `G` needs decidable conjugacy, and
the body is exposed so subgroup-fusion tables reduce in the kernel. -/
@[expose] def fusion (dH : ClassData H) (dG : ClassData G)
    [DecidableRel (IsConj : G → G → Prop)] (φ : H →* G) (i : Fin dH.numClasses) :
    Fin dG.numClasses :=
  dG.index (φ (dH.rep i))

section TargetDecidable

variable (dH : ClassData H) (dG : ClassData G) [DecidableRel (IsConj : G → G → Prop)]

/-- The representative at the fused index `dH.fusion dG φ i` is conjugate in `G` to
`φ (dH.rep i)`. -/
theorem isConj_rep_fusion (φ : H →* G) (i : Fin dH.numClasses) :
    IsConj (dG.rep (dH.fusion dG φ i)) (φ (dH.rep i)) :=
  dG.isConj_rep_index (φ (dH.rep i))

/-- `dH.fusion dG φ i` equals `j` if and only if `dG.rep j` is conjugate to `φ (dH.rep i)`. -/
theorem fusion_eq_iff {φ : H →* G} {i : Fin dH.numClasses} {j : Fin dG.numClasses} :
    dH.fusion dG φ i = j ↔ IsConj (dG.rep j) (φ (dH.rep i)) :=
  dG.index_eq_iff

/-- **Certify a fusion-table entry** `dH.fusion dG φ i = j` from an explicit conjugator `c : G`. -/
theorem fusion_eq_of_conj {φ : H →* G} {i : Fin dH.numClasses} {j : Fin dG.numClasses}
    (c : G) (hc : c * dG.rep j * c⁻¹ = φ (dH.rep i)) :
    dH.fusion dG φ i = j :=
  (dH.fusion_eq_iff dG).mpr (isConj_iff.mpr ⟨c, hc⟩)

/-- **The numbered fusion map tracks `ConjClasses.map φ`.** -/
@[simp]
theorem classOf_fusion (φ : H →* G) (i : Fin dH.numClasses) :
    dG.classOf (dH.fusion dG φ i) = ConjClasses.map φ (dH.classOf i) := by
  rw [fusion, classOf_index, classOf_eq_mk, ConjClasses.map_mk]

/-- **Functoriality of class fusion**: fusing along `φ` and then along `ψ` is fusing along
`ψ.comp φ`. -/
theorem fusion_comp (dK : ClassData K) [DecidableRel (IsConj : K → K → Prop)]
    (φ : H →* G) (ψ : G →* K) (i : Fin dH.numClasses) :
    dG.fusion dK ψ (dH.fusion dG φ i) = dH.fusion dK (ψ.comp φ) i := by
  apply dK.classOf_injective
  rw [classOf_fusion, classOf_fusion, classOf_fusion, dH.classOf_eq_mk]
  simp only [ConjClasses.map_mk, MonoidHom.comp_apply]

/-- Along a surjective homomorphism, the class-fusion map is surjective. -/
theorem surjective_fusion_of_surjective {φ : H →* G} (hφ : Function.Surjective φ) :
    Function.Surjective (dH.fusion dG φ) := by
  intro j
  obtain ⟨C, hC⟩ := ConjClasses.map_surjective hφ (dG.classOf j)
  obtain ⟨i, rfl⟩ := dH.classOf_surjective C
  exact ⟨i, dG.classOf_injective ((dH.classOf_fusion dG φ i).trans hC)⟩

/-- The element order of a fused class representative in `G` divides the order of the source
representative in `H`. -/
theorem orderOf_rep_fusion_dvd (φ : H →* G) (i : Fin dH.numClasses) :
    orderOf (dG.rep (dH.fusion dG φ i)) ∣ orderOf (dH.rep i) := by
  rw [fusion, dG.orderOf_rep_index]
  exact orderOf_map_dvd φ (dH.rep i)

/-- **Injective homomorphisms (in particular subgroup embeddings `S.subtype`) preserve
representative orders under class fusion.** -/
theorem orderOf_rep_fusion_of_injective {φ : H →* G} (hφ : Function.Injective φ)
    (i : Fin dH.numClasses) :
    orderOf (dG.rep (dH.fusion dG φ i)) = orderOf (dH.rep i) := by
  rw [fusion, dG.orderOf_rep_index, orderOf_injective φ hφ]

/-- **Character restriction along a fusion map**: the character of `ρ.comp φ` at the `i`-th
representative of `dH` equals the character of `ρ` at the fused representative in `dG`. -/
theorem character_rep_fusion {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (φ : H →* G) (ρ : Representation k G V) (i : Fin dH.numClasses) :
    Representation.character (ρ.comp φ) (dH.rep i) =
      ρ.character (dG.rep (dH.fusion dG φ i)) :=
  (dG.character_rep_index ρ (φ (dH.rep i))).symm

/-- Transporting the source class data along `e : K ≃* H` reindexes `fusion` on the left. -/
@[simp]
theorem fusion_map_left (e : K ≃* H) (dK : ClassData K) (φ : H →* G)
    (i : Fin (dK.map e).numClasses) :
    (dK.map e).fusion dG φ i =
      dK.fusion dG (φ.comp (e : K →* H)) (Fin.cast (dK.numClasses_map e) i) := by
  simp [fusion]

/-- Transporting the target class data along `e : G ≃* K` reindexes `fusion` on the right. -/
@[simp]
theorem fusion_map_right [DecidableRel (IsConj : K → K → Prop)] (e : G ≃* K)
    (φ : H →* G) (i : Fin dH.numClasses) :
    dH.fusion (dG.map e) ((e : G →* K).comp φ) i =
      Fin.cast (dG.numClasses_map e).symm (dH.fusion dG φ i) := by
  simp [fusion]

end TargetDecidable

/-- Fusing along the identity homomorphism is the identity on class indices. -/
@[simp]
theorem fusion_id (dG : ClassData G) [DecidableRel (IsConj : G → G → Prop)]
    (i : Fin dG.numClasses) :
    dG.fusion dG (MonoidHom.id G) i = i := by
  rw [fusion, MonoidHom.id_apply, index_rep]

/-- Fusing `dG` into `dG.map e` along `(e : G →* H)` is the canonical `Fin.cast`. -/
@[simp]
theorem fusion_coe_map (dG : ClassData G) [DecidableRel (IsConj : H → H → Prop)]
    (e : G ≃* H) (i : Fin dG.numClasses) :
    dG.fusion (dG.map e) (e : G →* H) i = Fin.cast (dG.numClasses_map e).symm i := by
  classical
  simp [fusion]

section BothDecidable

variable (dH : ClassData H) (dG : ClassData G)
  [DecidableRel (IsConj : H → H → Prop)] [DecidableRel (IsConj : G → G → Prop)]

/-- **Class fusion tracks homomorphisms** under `TauCeti.ClassData.index`. -/
@[simp]
theorem fusion_index (φ : H →* G) (h : H) :
    dH.fusion dG φ (dH.index h) = dG.index (φ h) :=
  dG.index_eq_index_iff.mpr (φ.map_isConj (dH.isConj_rep_index h))

-- Not `@[simp]`: `dH` does not appear on the left-hand side, so `simp` cannot infer it.
/-- `TauCeti.ClassData.indexClass` intertwines `ConjClasses.map φ` with `dH.fusion dG φ`. -/
theorem indexClass_map (φ : H →* G) (C : ConjClasses H) :
    dG.indexClass (ConjClasses.map φ C) = dH.fusion dG φ (dH.indexClass C) := by
  obtain ⟨h, rfl⟩ := ConjClasses.exists_rep C
  rw [ConjClasses.map_mk, indexClass_mk, indexClass_mk, fusion_index]

/-- Class fusion commutes with the inverse-class map. -/
theorem fusion_invIndex (φ : H →* G) (i : Fin dH.numClasses) :
    dH.fusion dG φ (dH.invIndex i) = dG.invIndex (dH.fusion dG φ i) := by
  rw [invIndex, fusion_index, map_inv, ← invIndex_index, ← fusion]

/-- Class fusion commutes with every `ℕ`-power map. -/
theorem fusion_powIndex (φ : H →* G) (n : ℕ) (i : Fin dH.numClasses) :
    dH.fusion dG φ (dH.powIndex n i) = dG.powIndex n (dH.fusion dG φ i) := by
  rw [powIndex, fusion_index, map_pow, ← powIndex_index, ← fusion]

/-- Class fusion commutes with every `ℤ`-power map. -/
theorem fusion_zpowIndex (φ : H →* G) (z : ℤ) (i : Fin dH.numClasses) :
    dH.fusion dG φ (dH.zpowIndex z i) = dG.zpowIndex z (dH.fusion dG φ i) := by
  rw [zpowIndex, fusion_index, map_zpow, ← zpowIndex_index, ← fusion]

end BothDecidable

end Fusion

/-! ### Kernel-evaluated sanity checks -/

section Regression

/-- Embedding of `Multiplicative (ZMod 4)` as the cyclic subgroup `⟨a⟩` of `QuaternionGroup 2`. -/
private def cyclicFourToQuaternionTwo :
    Multiplicative (ZMod 4) →* QuaternionGroup 2 where
  toFun x := QuaternionGroup.a x.toAdd
  map_one' := rfl
  map_mul' x y := by simp [QuaternionGroup.a_mul_a]

/-- Kernel check on `cyclicClassData 4` and `quaternionClassData 2`:
* `cyclicClassData 4` has non-real classes (`invIndex` swaps `1` and `3`), and a proper square map
  (`powIndex 2` sends both `1` and `3` to `2`);
* fusing `cyclicClassData 4` into `quaternionClassData 2` along `cyclicFourToQuaternionTwo`
  collapses the inverse pair `1, 3` into a single real quaternion class of order `4`. -/
private theorem invIndex_powIndex_fusion_cyclicFour_quaternionTwo :
    ((List.finRange (cyclicClassData 4).numClasses).map fun i =>
        ((cyclicClassData 4).invIndex i).val) = [0, 3, 2, 1] ∧
      ((List.finRange (cyclicClassData 4).numClasses).map fun i =>
        ((cyclicClassData 4).powIndex 2 i).val) = [0, 2, 0, 2] ∧
      ((List.finRange (cyclicClassData 4).numClasses).map fun i =>
        ((cyclicClassData 4).fusion (quaternionClassData 2) cyclicFourToQuaternionTwo i).val) =
        [0, 3, 1, 3] := by
  decide

end Regression

end TauCeti.ClassData
