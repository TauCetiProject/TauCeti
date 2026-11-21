/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Inverse and power maps on numbered conjugacy classes

Given conjugacy-class data `d : TauCeti.ClassData G`, inversion and `n`-th powering of group
elements induce operations on the class indices `Fin d.numClasses`. Together with representative
orders and centralizer indices, these maps form the power-map metadata of an ordinary character
table:

* the inverse map `d.invIndex` permutes the class indices involutively, fixing `i` if and only if
  `d.classOf i` is a real conjugacy class, and preserving representative orders, centralizer
  indices, and class sizes;
* the power maps `d.powIndex n` and `d.zpowIndex z` track `C ↦ C ^ n` on `ConjClasses G`, compose
  multiplicatively in the exponent, depend only on the residue of `n` modulo `orderOf (d.rep i)`,
  and permute the class indices bijectively whenever `n` is coprime to every representative order
  (in particular, whenever `n` is coprime to `Nat.card G`).

For groups whose class data is certified from explicit conjugating witnesses rather than by brute
enumeration, each index equation (`d.invIndex i = j`, `d.powIndex n i = j`, `d.zpowIndex z i = j`)
is paired with its witness-certified rule (`c * rep * c⁻¹ = ...`), as well as transport lemmas
across `TauCeti.ClassData.map`.

## Main definitions

* `TauCeti.ClassData.invIndex`: the numbered inverse-class map on `Fin d.numClasses`.
* `TauCeti.ClassData.powIndex`, `TauCeti.ClassData.zpowIndex`: the numbered `ℕ`-power and
  `ℤ`-power maps on `Fin d.numClasses`.

## Main results

* `TauCeti.ClassData.invIndex_map`, `TauCeti.ClassData.powIndex_map`,
  `TauCeti.ClassData.zpowIndex_map`: transport of inverse maps and power maps along
  `TauCeti.ClassData.map`.
* `TauCeti.ClassData.invIndex_eq_self_iff`: `d.invIndex` fixes `i` if and only if `d.classOf i` is
  a real class (`TauCeti.IsRealClass`).
* `TauCeti.ClassData.powIndex_bijective_of_coprime`,
  `TauCeti.ClassData.powIndex_bijective_of_coprime_card`: coprime power maps permute the numbered
  classes bijectively and preserve class sizes.

## References

* J. D. Dixon, *High speed computation of group characters*, Numer. Math. **10** (1967), 446–450.
* I. M. Isaacs, *Character Theory of Finite Groups*, Academic Press (1976).
-/

public section

namespace TauCeti.ClassData

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

/-- Certify `d.zpowIndex z i = j` directly from an explicit conjugating element `c`. -/
theorem zpowIndex_eq_of_conj {z : ℤ} {i j : Fin d.numClasses} (c : G)
    (hc : c * d.rep j * c⁻¹ = d.rep i ^ z) : d.zpowIndex z i = j :=
  d.zpowIndex_eq_iff.mpr (isConj_iff.mpr ⟨c, hc⟩)

/-- **The `ℤ`-power map tracks integer powers** under `TauCeti.ClassData.index`. -/
@[simp]
theorem zpowIndex_index (z : ℤ) (g : G) : d.zpowIndex z (d.index g) = d.index (g ^ z) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp (d.isConj_rep_index g)
  refine d.index_eq_index_iff.mpr (isConj_iff.mpr ⟨c, ?_⟩)
  simpa only [MulAut.conj_apply, hc] using map_zpow (MulAut.conj c) (d.rep (d.index g)) z

/-- **The numbered `ℤ`-power map tracks integer powers** under `TauCeti.ClassData.classOf`. -/
@[simp]
theorem classOf_zpowIndex (z : ℤ) (i : Fin d.numClasses) :
    d.classOf (d.zpowIndex z i) = ConjClasses.mk (d.rep i ^ z) := by
  rw [zpowIndex, classOf_index]

-- There is no `indexClass_zpow` parallel to `indexClass_pow`, as `ConjClasses G` has no `ℤ`-power
-- operation (`Pow (ConjClasses G) ℤ`); on representatives `indexClass_mk` and `zpowIndex_index`
-- already simplify `d.indexClass (ConjClasses.mk (g ^ z))`.

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

/-- Negating the integer exponent composes with `d.invIndex`. -/
@[simp]
theorem zpowIndex_neg (z : ℤ) (i : Fin d.numClasses) :
    d.zpowIndex (-z) i = d.invIndex (d.zpowIndex z i) := by
  rw [zpowIndex, zpow_neg, ← invIndex_index, zpowIndex]

-- Not `@[simp]`: `simp` already reduces the left-hand side via `zpowIndex_neg` and `zpowIndex_one`.
/-- At `-1`, `zpowIndex` is the inverse-class map `d.invIndex`. -/
theorem zpowIndex_neg_one (i : Fin d.numClasses) : d.zpowIndex (-1) i = d.invIndex i := by
  rw [zpowIndex_neg, zpowIndex_one]

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
theorem powIndex_bijective_of_coprime {n : ℕ}
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
theorem powIndex_bijective_of_coprime_card {n : ℕ}
    (hn : (Nat.card G).Coprime n) : Function.Bijective (d.powIndex n) := by
  cases finite_or_infinite G with
  | inl _ =>
      exact d.powIndex_bijective_of_coprime fun i => hn.of_dvd_left (orderOf_dvd_natCard _)
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

end TauCeti.ClassData
