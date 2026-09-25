/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ConjFinite
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.Data.Set.Card
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Inversion and powers of conjugacy classes, and the size of a class

Inversion of a group is compatible with conjugacy: `x` and `y` are conjugate exactly when `x⁻¹` and
`y⁻¹` are (`TauCeti.isConj_inv_iff`). So inversion descends to the conjugacy classes, where it is an
involution, recorded here as an `InvolutiveInv (ConjClasses G)` instance; `C⁻¹` is the class of the
inverses of the members of `C`, and it has the same size as `C`. A class fixed by this involution is
a **real** class (`TauCeti.IsRealClass`).

Powering likewise commutes with conjugation, so for a **monoid** `M` it too descends to the
conjugacy classes: `ConjClasses.pow C j`, written `C ^ j`, is the class of the `j`-th powers of
the members of `C`.

The other fact collected here is that the size of a conjugacy class is the index of the centralizer
of any of its members, and so divides the order of the group: the orbit-stabilizer theorem for the
conjugation action.

## Main statements

* `TauCeti.isConj_inv_iff`: conjugacy is inherited by inverses in both directions.
* `ConjClasses.inv_mk`: the inverse of the class of `g` is the class of `g⁻¹`.
* `TauCeti.IsRealClass`: a class containing an element conjugate to its own inverse, with
  `TauCeti.isRealClass_iff_inv_eq` identifying it with being fixed by inversion.
* `ConjClasses.ncard_carrier_inv` and `ConjClasses.card_carrier_inv`: a conjugacy
  class and its inverse have the same size, in `Set.ncard` and in `Nat.card` form.
* `ConjClasses.ncard_carrier_mk` and `ConjClasses.card_carrier_mk`: the size of a
  conjugacy class is the index of the centralizer of any of its members, in `Set.ncard` and in
  `Nat.card` form.
* `ConjClasses.ncard_carrier_mk_of_mem_center`: the class of a central element is a single
  point.
* `ConjClasses.card_carrier_mul_orderOf_dvd`: the class size times the order of a member
  divides the order of the group, so the quotient below is an exact ratio.
* `ConjClasses.card_div_card_carrier_mul_orderOf_pos`: for a finite group that ratio is positive.
* `ConjClasses.card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf`: that
  quotient equals the order of the centralizer divided by the order of the member.
* `ConjClasses.one_div_orderOf_div_card_div_card_carrier_mul_orderOf`: dividing `1 / orderOf σ`
  by that quotient, in a semifield of characteristic zero, leaves `#C / #G`.
* `ConjClasses.ncard_carrier_mk_eq_card_filter` and
  `ConjClasses.card_carrier_mk_eq_card_filter`: the size of a conjugacy class as the
  cardinality of a `Finset`, which makes it computable.
* `ConjClasses.card_carrier_dvd_card`: the size of a conjugacy class divides the order of
  the group, with `ConjClasses.card_carrier_cast_ne_zero` the consequence that the size of
  a class is nonzero in any semiring where the group order is.
* `ConjClasses.pow`: the power operation itself, with `C ^ j` its notation.
* `ConjClasses.mem_pow_iff`: an element lies in `C ^ j` exactly when it is a
  `j`-th power of a member of `C`, with `ConjClasses.mk_pow` the computation rule.
* `ConjClasses.pow_zero`, `ConjClasses.pow_one` and
  `ConjClasses.pow_mul`: the identity and composition laws for that power.
* `ConjClasses.map_mk`: the computation rule for `ConjClasses.map` on representatives,
  with `ConjClasses.map_pow` the consequence that the power is natural in the monoid.
* `ConjClasses.mk_ne_mk_of_orderOf_ne`: elements of different orders lie in different conjugacy
  classes.

## Implementation notes

The inversion is an instance rather than a plain function so that the notation `C⁻¹`, the
involutivity lemma `inv_inv` and the reindexing equivalence `Equiv.inv` are all available for
conjugacy classes. Powering is instead a named definition `ConjClasses.pow` with a `Pow` instance
delegating to it, so that `C.pow j` and the notation `C ^ j` are the same function;
the lemmas below are all stated in the `^` form. There is still no
multiplication on `ConjClasses M` — `Pow (ConjClasses M) ℕ` is a bare power operation, not the
`npow` field of a monoid structure, and none of the lemmas here presuppose one.

The power operation is used in the Frobenius von Mangoldt fibre, which sums over the classes
`C ^ j`. The private `pow_two_cyclicFour` regression distinguishes this operation from one that
collapses every positive power to the identity: a group of exponent two cannot do so using squares.

The two arithmetic statements concern the quotient `#G / (#C * orderOf σ)`. The first says the
division is exact — `#C` is the index of the centralizer of `σ`, and `orderOf σ` divides that
centralizer's order, so their product divides `#G` — and the second evaluates the quotient as the
centralizer's order over `orderOf σ`. Neither asserts that either side counts anything; a caller
wanting a cardinality interpretation must supply it.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- Conjugacy is inherited by inverses in both directions.

Not `@[simp]`: Mathlib's `isConj_iff` is itself `simp`, so the left-hand side simplifies to
`∃ c, c * x⁻¹ * c⁻¹ = y⁻¹` and the simp normal form linter rejects the pair. -/
theorem isConj_inv_iff {x y : G} : IsConj x⁻¹ y⁻¹ ↔ IsConj x y := by
  simp only [IsConj, SemiconjBy.inv_right_iff]

/-- **Inversion of conjugacy classes.** Inversion of the group respects conjugacy, so it descends
to the conjugacy classes; there it is an involution, because it is one on the group. -/
instance instInvolutiveInvConjClasses : InvolutiveInv (ConjClasses G) where
  inv := Quotient.lift (fun g => ConjClasses.mk g⁻¹) fun _ _ h =>
    ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_inv_iff.mpr h)
  inv_inv C := by
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    exact congrArg ConjClasses.mk (inv_inv g)

end TauCeti

namespace ConjClasses

variable {G : Type*} [Group G]

/-- The inverse of the conjugacy class of `g` is the conjugacy class of `g⁻¹`. -/
@[simp]
theorem inv_mk (g : G) : (ConjClasses.mk g)⁻¹ = ConjClasses.mk g⁻¹ :=
  (rfl)

/-- The class of the identity is its own inverse. -/
@[simp]
theorem inv_one : (1 : ConjClasses G)⁻¹ = 1 := by
  rw [ConjClasses.one_eq_mk_one, inv_mk, _root_.inv_one]

/-- An element lies in the inverse of a conjugacy class exactly when its inverse lies in the
class. -/
@[simp]
theorem mem_carrier_inv_iff {C : ConjClasses G} {x : G} :
    x ∈ (C⁻¹).carrier ↔ x⁻¹ ∈ C.carrier := by
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mem_carrier_iff_mk_eq,
    ← inv_mk, inv_eq_iff_eq_inv]

/-- **A conjugacy class and its inverse have the same size**, inversion of the group restricting to
a bijection between them.

This is the `Set.ncard` form, which is the simp normal form: Mathlib's `Nat.card_coe_set_eq` is
itself `simp`. See `ConjClasses.card_carrier_inv` for the `Nat.card` form. -/
@[simp]
theorem ncard_carrier_inv (C : ConjClasses G) :
    Set.ncard (C⁻¹).carrier = Set.ncard C.carrier :=
  Nat.card_congr ((Equiv.inv G).subtypeEquiv fun _ => mem_carrier_inv_iff)

/-- **A conjugacy class and its inverse have the same size**, in `Nat.card` form.

Not `@[simp]`: Mathlib's `Nat.card_coe_set_eq` is itself `simp`, so the left-hand side simplifies
to `(C⁻¹).carrier.ncard` and the simp normal form linter rejects the pair; that normalized form is
`ConjClasses.ncard_carrier_inv`. -/
theorem card_carrier_inv (C : ConjClasses G) : Nat.card (C⁻¹).carrier = Nat.card C.carrier :=
  ncard_carrier_inv C

/-- **The size of a conjugacy class is the index of the centralizer of any of its members.** The
class is the orbit of `g` under the conjugation action and the centralizer is the stabilizer, so
this is the orbit-stabilizer theorem. -/
theorem ncard_carrier_mk (g : G) :
    (ConjClasses.mk g).carrier.ncard = (Subgroup.centralizer {g}).index := by
  rw [← ConjAct.orbit_eq_carrier_conjClasses, ← MulAction.index_stabilizer,
    Subgroup.centralizer_eq_comap_stabilizer]
  exact ((MulAction.stabilizer (ConjAct G) g).index_comap_of_surjective
    (f := ConjAct.toConjAct.toMonoidHom) ConjAct.toConjAct.surjective).symm

/-- **The conjugacy class of a central element is a single point**: nothing moves it. -/
@[simp]
theorem ncard_carrier_mk_of_mem_center {g : G} (hg : g ∈ Subgroup.center G) :
    (ConjClasses.mk g).carrier.ncard = 1 := by
  rw [ncard_carrier_mk, Subgroup.centralizer_eq_top_iff_subset.mpr
    (Set.singleton_subset_iff.mpr hg), Subgroup.index_top]

/-- **The size of a conjugacy class is the index of the centralizer of any of its members**, in
`Nat.card` form.

Not `@[simp]`: Mathlib's `Nat.card_coe_set_eq` is itself `simp`, so the left-hand side simplifies
to `(ConjClasses.mk g).carrier.ncard` and the simp normal form linter rejects the pair; that
normalized form is `ConjClasses.ncard_carrier_mk`. -/
theorem card_carrier_mk (g : G) :
    Nat.card (ConjClasses.mk g).carrier = (Subgroup.centralizer {g}).index := by
  rw [Nat.card_coe_set_eq, ncard_carrier_mk]

/-- **The size of a conjugacy class as a `Finset` cardinality**: the members of the class of `g`
are the elements of the monoid whose class is that of `g`, so in a finite monoid with decidable
equality the class size is a count that can be evaluated. -/
@[simp]
theorem ncard_carrier_mk_eq_card_filter {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]
    (g : M) :
    (ConjClasses.mk g).carrier.ncard =
      {x ∈ (Finset.univ : Finset M) | ConjClasses.mk x = ConjClasses.mk g}.card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext x
  simp [_root_.ConjClasses.mem_carrier_iff_mk_eq]

/-- The size of a conjugacy class as a computable `Finset` cardinality, in `Nat.card` form.
See `ncard_carrier_mk_eq_card_filter` for the `simp` normal form. -/
theorem card_carrier_mk_eq_card_filter {M : Type*} [Monoid M] [Fintype M] [DecidableEq M]
    (g : M) :
    Nat.card (ConjClasses.mk g).carrier =
      {x ∈ (Finset.univ : Finset M) | ConjClasses.mk x = ConjClasses.mk g}.card := by
  rw [Nat.card_coe_set_eq, ncard_carrier_mk_eq_card_filter]

/-- **The size of a conjugacy class divides the order of the group**, being the index of a
centralizer. -/
theorem card_carrier_dvd_card (C : ConjClasses G) : Nat.card C.carrier ∣ Nat.card G := by
  obtain ⟨x, rfl⟩ := ConjClasses.exists_rep C
  calc Nat.card (ConjClasses.mk x).carrier
      = (Subgroup.centralizer {x}).index := card_carrier_mk x
    _ ∣ Nat.card G := Subgroup.index_dvd_card _

/-- The size of a conjugacy class is nonzero in any semiring in which the order of the group is
nonzero: it divides that order. -/
theorem card_carrier_cast_ne_zero {R : Type*} [Semiring R] (C : ConjClasses G)
    (h : (Nat.card G : R) ≠ 0) : (Nat.card C.carrier : R) ≠ 0 :=
  ne_zero_of_dvd_ne_zero h (Nat.cast_dvd_cast (card_carrier_dvd_card C))

end ConjClasses

namespace TauCeti

variable {G : Type*} [Group G]

/-- **A real conjugacy class**: one containing an element conjugate to its own inverse. -/
def IsRealClass (C : ConjClasses G) : Prop :=
  ∃ g : G, ConjClasses.mk g = C ∧ IsConj g g⁻¹

/-- **A class is real exactly when inversion fixes it.** -/
@[simp]
theorem isRealClass_iff_inv_eq {C : ConjClasses G} : IsRealClass C ↔ C⁻¹ = C := by
  constructor
  · rintro ⟨g, rfl, hg⟩
    rw [ConjClasses.inv_mk, ConjClasses.mk_eq_mk_iff_isConj]
    exact hg.symm
  · intro h
    obtain ⟨g, rfl⟩ := ConjClasses.exists_rep C
    rw [ConjClasses.inv_mk, ConjClasses.mk_eq_mk_iff_isConj] at h
    exact ⟨g, rfl, h.symm⟩

-- Not a `simp` lemma: `isRealClass_iff_inv_eq` and `ConjClasses.inv_mk` already rewrite the
-- left-hand side to `ConjClasses.mk g⁻¹ = ConjClasses.mk g`, so tagging it makes `simpNF` fail.
/-- The class of `g` is real exactly when `g` is conjugate to `g⁻¹`. -/
theorem isRealClass_mk_iff {g : G} : IsRealClass (ConjClasses.mk g) ↔ IsConj g g⁻¹ := by
  rw [isRealClass_iff_inv_eq, ConjClasses.inv_mk, ConjClasses.mk_eq_mk_iff_isConj]
  exact ⟨IsConj.symm, IsConj.symm⟩

end TauCeti

/-! ### The size of a class against the order of a member -/

namespace ConjClasses

/-- **The size of a conjugacy class times the order of a member divides the order of the group.**

For a *finite* group this is what makes `Nat.card G / (Nat.card C.carrier * orderOf σ)` an exact
ratio rather than a truncated division, which
`card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf` then evaluates. No finiteness
is assumed here: for an infinite group `Nat.card G` is `0`, and every natural number divides `0`. -/
theorem card_carrier_mul_orderOf_dvd {G : Type*} [Group G] (C : ConjClasses G) (σ : G)
    (hσ : σ ∈ C.carrier) :
    Nat.card C.carrier * orderOf σ ∣ Nat.card G := by
  rw [mem_carrier_iff_mk_eq] at hσ
  subst hσ
  obtain ⟨k, hk⟩ := (Subgroup.centralizer {σ}).orderOf_dvd_natCard
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  exact ⟨k, by rw [ConjClasses.card_carrier_mk, mul_assoc, ← hk, Subgroup.index_mul_card]⟩

/-- **That quotient is positive.** For a finite group the class size times the order of a member
divides the group order and both are positive, so the ratio `Nat.card G / (#C.carrier * orderOf σ)`
is a positive natural number rather than a truncation to zero.

Finiteness is needed, and not only for convenience: for an infinite `G` every one of
`Nat.card G`, `Nat.card C.carrier` and `orderOf σ` may be `0`, and the quotient is then `0 / 0`. -/
theorem card_div_card_carrier_mul_orderOf_pos {G : Type*} [Group G] [Finite G]
    (C : ConjClasses G) (σ : G) (hσ : σ ∈ C.carrier) :
    0 < Nat.card G / (Nat.card C.carrier * orderOf σ) :=
  have : Nonempty C.carrier := ⟨⟨σ, hσ⟩⟩
  Nat.div_pos (Nat.le_of_dvd Nat.card_pos (C.card_carrier_mul_orderOf_dvd σ hσ))
    (Nat.mul_pos Nat.card_pos (orderOf_pos σ))

/-- **That quotient in closed form.** Dividing the order of the group by the class size times the
order of a member leaves the order of the centralizer divided by that same order.

`hindex` is what lets the centralizer's index cancel from both sides; it holds automatically when
`G` is finite. The statement is an equality of `Nat.div` values, and no more: for a finite `G` both
divisions are exact and it reads as an equality of ratios, but `hindex` alone does not give that.
An infinite abelian group with an element of infinite order satisfies `hindex` while `Nat.card G`,
the centralizer's cardinality and `orderOf σ` are all `0`, and the identity is then `0 / 0`. -/
theorem card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf {G : Type*} [Group G]
    (C : ConjClasses G) (σ : G) (hσ : σ ∈ C.carrier)
    (hindex : (Subgroup.centralizer {σ}).index ≠ 0) :
    Nat.card G / (Nat.card C.carrier * orderOf σ)
      = Nat.card (Subgroup.centralizer {σ}) / orderOf σ := by
  rw [mem_carrier_iff_mk_eq] at hσ
  subst hσ
  rw [ConjClasses.card_carrier_mk, ← Subgroup.index_mul_card (Subgroup.centralizer {σ}),
    Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero hindex)]

/-- **Dividing `1 / orderOf σ` by that quotient leaves `#C / #G`.** Since
`#C.carrier * orderOf σ` divides `#G`, the quotient casts to the exact ratio, and in a semifield of
characteristic zero `(1 / orderOf σ) / (#G / (#C.carrier * orderOf σ)) = #C.carrier / #G`.
For infinite groups both sides vanish because `Nat.card G = 0`. -/
theorem one_div_orderOf_div_card_div_card_carrier_mul_orderOf {G : Type*} [Group G]
    {K : Type*} [Semifield K] [CharZero K] (C : ConjClasses G) (σ : G) (hσ : σ ∈ C.carrier) :
    (1 / orderOf σ : K) / ((Nat.card G / (Nat.card C.carrier * orderOf σ) : ℕ) : K) =
      Nat.card C.carrier / Nat.card G := by
  cases finite_or_infinite G with
  | inl h =>
      have : Nonempty C.carrier := ⟨⟨σ, hσ⟩⟩
      have hC : (Nat.card C.carrier : K) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      have hord : (orderOf σ : K) ≠ 0 := Nat.cast_ne_zero.mpr (orderOf_pos σ).ne'
      rw [Nat.cast_div (C.card_carrier_mul_orderOf_dvd σ hσ)
        (by push_cast; exact mul_ne_zero hC hord)]
      push_cast
      rw [div_div_eq_mul_div, one_div_mul_eq_div, mul_div_cancel_right₀ _ hord]
  | inr h => simp [Nat.card_eq_zero_of_infinite]

end ConjClasses

/-! ### Powers of a conjugacy class -/

namespace ConjClasses

variable {M : Type*} [Monoid M]

/-- **The `j`-th power of a conjugacy class.** Powering respects conjugacy (`IsConj.pow`), so it
descends to the conjugacy classes of a monoid: `C.pow j` is the class of the `j`-th powers of the
members of `C`. The `Pow` instance below spells it `C ^ j`, which is the form every lemma here
is stated in. -/
def pow (C : ConjClasses M) (j : ℕ) : ConjClasses M :=
  Quotient.map (· ^ j) (fun _ _ h ↦ IsConj.pow j h) C

instance instPowNat : Pow (ConjClasses M) ℕ :=
  ⟨ConjClasses.pow⟩

/-- The `j`-th power of the class of `a` is the class of `a ^ j`. -/
@[simp]
theorem mk_pow (a : M) (j : ℕ) : ConjClasses.mk a ^ j = ConjClasses.mk (a ^ j) := by
  -- `pow` is sealed, so this is no longer `rfl`: a theorem exported from this module may only
  -- unfold exposed definitions. Go through `pow`'s equation lemma, after which the statement is
  -- exactly `Quotient`'s computation rule for `Quotient.map`.
  change ConjClasses.pow (ConjClasses.mk a) j = ConjClasses.mk (a ^ j)
  rw [ConjClasses.pow]
  exact Quotient.map_mk _ _ _

/-- An element lies in `C ^ j` exactly when it is a `j`-th power of a member of `C`. -/
@[simp]
theorem mem_pow_iff {C : ConjClasses M} {τ : M} {j : ℕ} :
    τ ∈ (C ^ j).carrier ↔ ∃ σ ∈ C.carrier, σ ^ j = τ := by
  obtain ⟨a, rfl⟩ := ConjClasses.exists_rep C
  simp only [mk_pow, _root_.ConjClasses.mem_carrier_iff_mk_eq,
    _root_.ConjClasses.mk_eq_mk_iff_isConj]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun ⟨σ, ⟨c, hc⟩, hσ⟩ ↦ hσ ▸ ⟨c, hc.pow_right j⟩⟩
  -- Conjugating `a` back by `c` produces a member of `C` whose `j`-th power is `τ`.
  have hσ : SemiconjBy (c : M) (↑c⁻¹ * a * ↑c) a := by
    simp [SemiconjBy, ← mul_assoc]
  refine ⟨↑c⁻¹ * a * ↑c, ⟨c, hσ⟩, ?_⟩
  have h1 : (c : M) * (↑c⁻¹ * a * ↑c) ^ j = a ^ j * ↑c := hσ.pow_right j
  have h2 : (c : M) * τ = a ^ j * ↑c := hc
  exact (Units.mul_right_inj c).mp (h1.trans h2.symm)

/-- The zeroth power of any conjugacy class is the class of `1`. -/
@[simp]
theorem pow_zero (C : ConjClasses M) : C ^ 0 = 1 := by
  obtain ⟨a, rfl⟩ := ConjClasses.exists_rep C
  rw [mk_pow, _root_.pow_zero, ← _root_.ConjClasses.one_eq_mk_one]

/-- The first power of a conjugacy class is the class itself. -/
@[simp]
theorem pow_one (C : ConjClasses M) : C ^ 1 = C := by
  obtain ⟨a, rfl⟩ := ConjClasses.exists_rep C
  rw [mk_pow, _root_.pow_one]

/-- Iterated powers compose: raising `C ^ i` to the `j`-th power gives `C ^ (i * j)`. Tagged
`@[simp]` because the single power is the normal form: it rewrites towards `C ^ (i * j)`, which
is the direction the rest of this API (`pow_zero`, `pow_one`, `mk_pow`) already normalises to.
Note this is the mirror image of Mathlib's root-level `pow_mul`, which orients the equation the
other way for monoid elements. -/
@[simp]
theorem pow_mul (C : ConjClasses M) (i j : ℕ) : (C ^ i) ^ j = C ^ (i * j) := by
  obtain ⟨a, rfl⟩ := ConjClasses.exists_rep C
  rw [mk_pow, mk_pow, mk_pow, _root_.pow_mul]

/-- The image of the class of `a` under `ConjClasses.map f` is the class of `f a`. -/
-- Mathlib defines `ConjClasses.map` as a `Quotient.lift` and provides no computation rule for it,
-- so this reduction is stated here once and every naturality statement below rewrites with it.
@[simp]
theorem map_mk {N : Type*} [Monoid N] (f : M →* N) (a : M) :
    ConjClasses.map f (ConjClasses.mk a) = ConjClasses.mk (f a) := rfl

/-- Powering a conjugacy class is natural in the monoid. -/
@[simp]
theorem map_pow {N : Type*} [Monoid N] (f : M →* N) (C : ConjClasses M) (j : ℕ) :
    ConjClasses.map f (C ^ j) = ConjClasses.map f C ^ j := by
  obtain ⟨a, rfl⟩ := ConjClasses.exists_rep C
  -- Every reduction here is named rather than left to definitional unfolding: `map_mk` computes
  -- the map on representatives, after which `mk_pow` handles both powers and `map_pow` finishes
  -- in `N`.
  rw [mk_pow, map_mk, map_mk, mk_pow, _root_.map_pow]

/-- Elements of different orders lie in different conjugacy classes, even in a monoid. -/
theorem mk_ne_mk_of_orderOf_ne {a b : M} (h : orderOf a ≠ orderOf b) :
    ConjClasses.mk a ≠ ConjClasses.mk b := by
  intro hclasses
  apply h
  rw [orderOf_eq_orderOf_iff]
  intro n
  have hc := ConjClasses.mk_eq_mk_iff_isConj.mp hclasses
  constructor <;> intro hpow
  · simpa only [hpow, isConj_one_right] using hc.pow n
  · simpa only [hpow, isConj_one_right] using hc.symm.pow n

/-- **A nonidentity square in the cyclic group of order four.** The generator has order four, its
class squares to the class of the element of order two, and those two classes are distinct. A group
of exponent two cannot witness this: it has no proper nonidentity square, so it cannot tell a
correct power operation from one that collapses to the identity. -/
private theorem pow_two_cyclicFour :
    orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 ∧
      ConjClasses.mk (Multiplicative.ofAdd (1 : ZMod 4)) ^ 2 =
        ConjClasses.mk (Multiplicative.ofAdd (2 : ZMod 4)) ∧
      ConjClasses.mk (Multiplicative.ofAdd (1 : ZMod 4)) ≠
        ConjClasses.mk (Multiplicative.ofAdd (2 : ZMod 4)) := by
  have horder : orderOf (Multiplicative.ofAdd (1 : ZMod 4)) = 4 := by
    rw [orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]
  have hsquare : Multiplicative.ofAdd (1 : ZMod 4) ^ 2 = Multiplicative.ofAdd (2 : ZMod 4) := by
    rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one]
    norm_cast
  have horderSquare : orderOf (Multiplicative.ofAdd (2 : ZMod 4)) = 2 := by
    rw [← hsquare, orderOf_pow_of_dvd (by decide) (by rw [horder]; decide), horder]
  exact ⟨horder, by rw [mk_pow, hsquare],
    mk_ne_mk_of_orderOf_ne (by rw [horder, horderSquare]; decide)⟩

end ConjClasses
