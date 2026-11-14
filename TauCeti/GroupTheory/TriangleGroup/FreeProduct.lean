/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Equiv.TypeTags
public import Mathlib.Data.ZMod.Basic
public import TauCeti.GroupTheory.Coprod.Abelianization
public import TauCeti.GroupTheory.Coprod.Torsion
public import TauCeti.GroupTheory.Index.TorsionFree
public import TauCeti.GroupTheory.TriangleGroup.Basic

/-!
# Free-product presentation of triangle groups `Δ(a, b, 0)`

When the third exponent of a triangle group is `0`, the relator `z ^ 0 = 1` is vacuous and the
product relation `z * y * x = 1` simply expresses `z = (y * x)⁻¹` in terms of `x` and `y`. What
remains is `⟨x, y | x ^ a, y ^ b⟩`, the free product of two cyclic groups of orders `a` and `b`
(with `0` giving an infinite cyclic factor `Multiplicative (ZMod 0) = Multiplicative ℤ`).

From the isomorphism `TauCeti.TriangleGroup.equivCoprod` we deduce for all `a b : ℕ`:

* the exact generator orders `orderOf (x a b 0) = a` and `orderOf (y a b 0) = b`, and
  `orderOf (z a b 0) = 0` whenever `a ≠ 1` and `b ≠ 1`;
* the abelianization `Additive (Group.Abelianization (TriangleGroup a b 0)) ≃+ ZMod a × ZMod b`;
* the classification of finite-order elements up to conjugacy as powers of `x a b 0` or `y a b 0`;
* for `a, b > 0`, divisibility `Nat.lcm a b ∣ H.index` for every torsion-free subgroup `H`.

## Main definitions

* `TauCeti.TriangleGroup.equivCoprod`: the isomorphism
  `TriangleGroup a b 0 ≃* Multiplicative (ZMod a) ∗ Multiplicative (ZMod b)`.
* `TauCeti.TriangleGroup.abelianizationMulEquivProd`,
  `TauCeti.TriangleGroup.abelianizationAddEquivProd`: the abelianization of `TriangleGroup a b 0`
  as `(ZMod a) × (ZMod b)`.

## Main results

* `TauCeti.TriangleGroup.orderOf_x_zero`, `TauCeti.TriangleGroup.orderOf_y_zero`,
  `TauCeti.TriangleGroup.orderOf_z_zero`: exact orders of the three generators of `Δ(a, b, 0)`.
* `TauCeti.TriangleGroup.isOfFinOrder_iff`, `TauCeti.TriangleGroup.isOfFinOrder_iff_of_neZero`,
  `TauCeti.TriangleGroup.orderOf_eq_iff`: torsion and order classification in `Δ(a, b, 0)`.
* `TauCeti.TriangleGroup.lcm_dvd_index_of_isMulTorsionFree`: `Nat.lcm a b` divides the index of
  every torsion-free subgroup of `Δ(a, b, 0)` when `a, b ≠ 0`.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer, 1977, Chapter IV, §1.
* J.-P. Serre, *Trees*, Springer Monographs in Mathematics, 1980, Chapter I, §4.2.
-/

public section

noncomputable section

open scoped Monoid.Coprod

namespace TauCeti

namespace TriangleGroup

/-! ### Auxiliary cyclic lift for unrestricted `n : ℕ` -/

private def cyclicLift {n : ℕ} {G : Type*} [Group G] (g : G) (hg : g ^ n = 1) :
    Multiplicative (ZMod n) →* G :=
  (ZMod.lift n ⟨zmultiplesHom (Additive G) (.ofMul g), by
    rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hg, ofMul_one]⟩).toMultiplicativeLeft

private theorem cyclicLift_ofAdd_intCast {n : ℕ} {G : Type*} [Group G] (g : G) (hg : g ^ n = 1)
    (k : ℤ) : cyclicLift g hg (.ofAdd (k : ZMod n)) = g ^ k := by
  rw [cyclicLift, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, Function.comp_apply,
    toAdd_ofAdd, ZMod.lift_coe, zmultiplesHom_apply, toMul_zsmul, toMul_ofMul]

private theorem cyclicLift_ofAdd_natCast {n : ℕ} {G : Type*} [Group G] (g : G) (hg : g ^ n = 1)
    (k : ℕ) : cyclicLift g hg (.ofAdd (k : ZMod n)) = g ^ k := by
  rw [← Int.cast_natCast, cyclicLift_ofAdd_intCast, zpow_natCast]

private theorem cyclicLift_ofAdd_one {n : ℕ} {G : Type*} [Group G] (g : G) (hg : g ^ n = 1) :
    cyclicLift g hg (.ofAdd 1) = g := by
  simpa using cyclicLift_ofAdd_intCast g hg 1

/-! ### Isomorphism with `Multiplicative (ZMod a) ∗ Multiplicative (ZMod b)` -/

private def toCoprodHom (a b : ℕ) :
    TriangleGroup a b 0 →* Multiplicative (ZMod a) ∗ Multiplicative (ZMod b) :=
  lift (Monoid.Coprod.inl (.ofAdd 1)) (Monoid.Coprod.inr (.ofAdd 1))
    ((Monoid.Coprod.inl (.ofAdd 1))⁻¹ * (Monoid.Coprod.inr (.ofAdd 1))⁻¹)
    (by rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero, map_one])
    (by rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero, map_one])
    (pow_zero _)
    (by simp [mul_assoc])

private def fromCoprodHom (a b : ℕ) :
    Multiplicative (ZMod a) ∗ Multiplicative (ZMod b) →* TriangleGroup a b 0 :=
  Monoid.Coprod.lift (cyclicLift (x a b 0) (x_pow a b 0)) (cyclicLift (y a b 0) (y_pow a b 0))

/-- **Free-product presentation of `Δ(a, b, 0)`.** For all `a b : ℕ`, `TriangleGroup a b 0` is
isomorphic to the free product `Multiplicative (ZMod a) ∗ Multiplicative (ZMod b)`, sending `x` to
`inl (ofAdd 1)`, `y` to `inr (ofAdd 1)` and `z` to `(inl (ofAdd 1))⁻¹ * (inr (ofAdd 1))⁻¹`. -/
def equivCoprod (a b : ℕ) :
    TriangleGroup a b 0 ≃* Multiplicative (ZMod a) ∗ Multiplicative (ZMod b) :=
  MonoidHom.toMulEquiv (toCoprodHom a b) (fromCoprodHom a b)
    (hom_ext a b 0
      (by simp [toCoprodHom, fromCoprodHom, cyclicLift_ofAdd_one])
      (by simp [toCoprodHom, fromCoprodHom, cyclicLift_ofAdd_one]))
    (Monoid.Coprod.hom_ext
      (MonoidHom.ext fun u ↦ by
        obtain ⟨k, hk⟩ := ZMod.intCast_surjective u.toAdd
        have hu : u = .ofAdd (k : ZMod a) := by rw [hk, ofAdd_toAdd]
        simp only [hu, MonoidHom.comp_apply, MonoidHom.id_apply, fromCoprodHom,
          Monoid.Coprod.lift_apply_inl, cyclicLift_ofAdd_intCast, toCoprodHom, map_zpow, lift_x]
        rw [← map_zpow, ← ofAdd_zsmul, zsmul_one])
      (MonoidHom.ext fun v ↦ by
        obtain ⟨k, hk⟩ := ZMod.intCast_surjective v.toAdd
        have hv : v = .ofAdd (k : ZMod b) := by rw [hk, ofAdd_toAdd]
        simp only [hv, MonoidHom.comp_apply, MonoidHom.id_apply, fromCoprodHom,
          Monoid.Coprod.lift_apply_inr, cyclicLift_ofAdd_intCast, toCoprodHom, map_zpow, lift_y]
        rw [← map_zpow, ← ofAdd_zsmul, zsmul_one]))

@[simp]
theorem equivCoprod_x (a b : ℕ) :
    equivCoprod a b (x a b 0) = Monoid.Coprod.inl (.ofAdd 1) := by
  simp [equivCoprod, toCoprodHom]

@[simp]
theorem equivCoprod_y (a b : ℕ) :
    equivCoprod a b (y a b 0) = Monoid.Coprod.inr (.ofAdd 1) := by
  simp [equivCoprod, toCoprodHom]

@[simp]
theorem equivCoprod_z (a b : ℕ) :
    equivCoprod a b (z a b 0) =
      (Monoid.Coprod.inl (.ofAdd 1))⁻¹ * (Monoid.Coprod.inr (.ofAdd 1))⁻¹ := by
  simp [equivCoprod, toCoprodHom]

@[simp]
theorem equivCoprod_symm_inl_ofAdd_intCast (a b : ℕ) (k : ℤ) :
    (equivCoprod a b).symm (Monoid.Coprod.inl (.ofAdd (k : ZMod a))) = x a b 0 ^ k := by
  simp [equivCoprod, fromCoprodHom, cyclicLift_ofAdd_intCast]

@[simp]
theorem equivCoprod_symm_inr_ofAdd_intCast (a b : ℕ) (k : ℤ) :
    (equivCoprod a b).symm (Monoid.Coprod.inr (.ofAdd (k : ZMod b))) = y a b 0 ^ k := by
  simp [equivCoprod, fromCoprodHom, cyclicLift_ofAdd_intCast]

@[simp]
theorem equivCoprod_symm_inl_ofAdd_natCast (a b : ℕ) (k : ℕ) :
    (equivCoprod a b).symm (Monoid.Coprod.inl (.ofAdd (k : ZMod a))) = x a b 0 ^ k := by
  simp [equivCoprod, fromCoprodHom, cyclicLift_ofAdd_natCast]

@[simp]
theorem equivCoprod_symm_inr_ofAdd_natCast (a b : ℕ) (k : ℕ) :
    (equivCoprod a b).symm (Monoid.Coprod.inr (.ofAdd (k : ZMod b))) = y a b 0 ^ k := by
  simp [equivCoprod, fromCoprodHom, cyclicLift_ofAdd_natCast]

@[simp]
theorem equivCoprod_symm_inl_ofAdd_one (a b : ℕ) :
    (equivCoprod a b).symm (Monoid.Coprod.inl (.ofAdd 1)) = x a b 0 := by
  simp [equivCoprod, fromCoprodHom, cyclicLift_ofAdd_one]

@[simp]
theorem equivCoprod_symm_inr_ofAdd_one (a b : ℕ) :
    (equivCoprod a b).symm (Monoid.Coprod.inr (.ofAdd 1)) = y a b 0 := by
  simp [equivCoprod, fromCoprodHom, cyclicLift_ofAdd_one]

/-! ### Exact orders of the generators -/

private abbrev inlHom (a b : ℕ) :
    Multiplicative (ZMod a) →* Multiplicative (ZMod a) ∗ Multiplicative (ZMod b) :=
  Monoid.Coprod.inl

private abbrev inrHom (a b : ℕ) :
    Multiplicative (ZMod b) →* Multiplicative (ZMod a) ∗ Multiplicative (ZMod b) :=
  Monoid.Coprod.inr

/-- In `Δ(a, b, 0)`, the generator `x` has exact order `a` (equal to `0`, encoding infinite order,
when `a = 0`). -/
@[simp]
theorem orderOf_x_zero (a b : ℕ) : orderOf (x a b 0) = a := by
  have h1 := orderOf_injective (equivCoprod a b).toMonoidHom (equivCoprod a b).injective (x a b 0)
  have h2 := orderOf_injective (inlHom a b) Monoid.Coprod.inl_injective (.ofAdd 1)
  rw [MulEquiv.coe_toMonoidHom, equivCoprod_x] at h1
  rw [← h1, h2, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

/-- In `Δ(a, b, 0)`, the generator `y` has exact order `b` (equal to `0`, encoding infinite order,
when `b = 0`). -/
@[simp]
theorem orderOf_y_zero (a b : ℕ) : orderOf (y a b 0) = b := by
  have h1 := orderOf_injective (equivCoprod a b).toMonoidHom (equivCoprod a b).injective (y a b 0)
  have h2 := orderOf_injective (inrHom a b) Monoid.Coprod.inr_injective (.ofAdd 1)
  rw [MulEquiv.coe_toMonoidHom, equivCoprod_y] at h1
  rw [← h1, h2, orderOf_ofAdd_eq_addOrderOf, ZMod.addOrderOf_one]

private theorem ofAdd_one_inv_ne_one {n : ℕ} (hn : n ≠ 1) :
    (Multiplicative.ofAdd (1 : ZMod n))⁻¹ ≠ 1 := by
  intro h
  have h1 : (1 : ZMod n) = 0 := by simpa using congrArg Multiplicative.toAdd (inv_eq_one.mp h)
  exact hn (ZMod.one_eq_zero_iff.mp h1)

/-- In `Δ(a, b, 0)` with `a ≠ 1` and `b ≠ 1`, the third generator `z = (y * x)⁻¹` has infinite
order (`orderOf = 0`), since under `equivCoprod` it is a product of nonidentity elements from
distinct factors. -/
theorem orderOf_z_zero {a b : ℕ} (ha : a ≠ 1) (hb : b ≠ 1) : orderOf (z a b 0) = 0 := by
  have h1 := orderOf_injective (equivCoprod a b).toMonoidHom (equivCoprod a b).injective (z a b 0)
  rw [MulEquiv.coe_toMonoidHom, equivCoprod_z, ← (inlHom a b).map_inv, ← (inrHom a b).map_inv] at h1
  rw [← h1]
  exact Monoid.Coprod.orderOf_inl_mul_inr_eq_zero
    (ofAdd_one_inv_ne_one ha) (ofAdd_one_inv_ne_one hb)

/-! ### Abelianization -/

/-- **Multiplicative abelianization of `Δ(a, b, 0)`.** The abelianization is isomorphic to
`Multiplicative (ZMod a) × Multiplicative (ZMod b)`, sending the class of `x` to `(ofAdd 1, 1)` and
that of `y` to `(1, ofAdd 1)`. -/
def abelianizationMulEquivProd (a b : ℕ) :
    Group.Abelianization (TriangleGroup a b 0) ≃*
      Multiplicative (ZMod a) × Multiplicative (ZMod b) :=
  ((equivCoprod a b).abelianizationCongr.trans Group.Abelianization.coprodMulEquiv).trans
    (MulEquiv.prodCongr Group.Abelianization.equivOfComm.symm
      Group.Abelianization.equivOfComm.symm)

@[simp]
theorem abelianizationMulEquivProd_of_x (a b : ℕ) :
    abelianizationMulEquivProd a b (Group.Abelianization.of (x a b 0)) = (.ofAdd 1, 1) := by
  simp [abelianizationMulEquivProd]
  rfl

@[simp]
theorem abelianizationMulEquivProd_of_y (a b : ℕ) :
    abelianizationMulEquivProd a b (Group.Abelianization.of (y a b 0)) = (1, .ofAdd 1) := by
  simp [abelianizationMulEquivProd]
  rfl

@[simp]
theorem abelianizationMulEquivProd_of_z (a b : ℕ) :
    abelianizationMulEquivProd a b (Group.Abelianization.of (z a b 0)) =
      ((.ofAdd 1)⁻¹, (.ofAdd 1)⁻¹) := by
  simp [abelianizationMulEquivProd]
  rfl

/-- **Additive abelianization of `Δ(a, b, 0)`.** Written additively, the abelianization of
`TriangleGroup a b 0` is isomorphic to `ZMod a × ZMod b`, sending `x` to `(1, 0)`, `y` to `(0, 1)`
and `z` to `(-1, -1)`. -/
def abelianizationAddEquivProd (a b : ℕ) :
    Additive (Group.Abelianization (TriangleGroup a b 0)) ≃+ ZMod a × ZMod b :=
  MulEquiv.toAdditiveLeft
    ((abelianizationMulEquivProd a b).trans
      (MulEquiv.prodMultiplicative (G := ZMod a) (H := ZMod b)).symm)

@[simp]
theorem abelianizationAddEquivProd_ofMul_of_x (a b : ℕ) :
    abelianizationAddEquivProd a b (.ofMul (Group.Abelianization.of (x a b 0))) = (1, 0) := by
  simp [abelianizationAddEquivProd]

@[simp]
theorem abelianizationAddEquivProd_ofMul_of_y (a b : ℕ) :
    abelianizationAddEquivProd a b (.ofMul (Group.Abelianization.of (y a b 0))) = (0, 1) := by
  simp [abelianizationAddEquivProd]

@[simp]
theorem abelianizationAddEquivProd_ofMul_of_z (a b : ℕ) :
    abelianizationAddEquivProd a b (.ofMul (Group.Abelianization.of (z a b 0))) = (-1, -1) := by
  simp [abelianizationAddEquivProd]

/-- The cardinality of the abelianization of `Δ(a, b, 0)` is `a * b`. -/
@[simp]
theorem natCard_abelianization (a b : ℕ) :
    Nat.card (Group.Abelianization (TriangleGroup a b 0)) = a * b := by
  rw [Nat.card_congr (abelianizationMulEquivProd a b).toEquiv, Nat.card_prod,
    Nat.card_congr Multiplicative.toAdd, Nat.card_congr Multiplicative.toAdd,
    Nat.card_zmod, Nat.card_zmod]

/-! ### Torsion classification and index divisibility -/

private theorem equivCoprod_x_zpow (a b : ℕ) (k : ℤ) :
    equivCoprod a b (x a b 0 ^ k) = Monoid.Coprod.inl (.ofAdd (k : ZMod a)) := by
  rw [map_zpow, equivCoprod_x, ← map_zpow, ← ofAdd_zsmul, zsmul_one]

private theorem equivCoprod_y_zpow (a b : ℕ) (k : ℤ) :
    equivCoprod a b (y a b 0 ^ k) = Monoid.Coprod.inr (.ofAdd (k : ZMod b)) := by
  rw [map_zpow, equivCoprod_y, ← map_zpow, ← ofAdd_zsmul, zsmul_one]

private theorem equivCoprod_x_pow (a b k : ℕ) :
    equivCoprod a b (x a b 0 ^ k) = Monoid.Coprod.inl (.ofAdd (k : ZMod a)) := by
  rw [map_pow, equivCoprod_x, ← map_pow, ← ofAdd_nsmul, nsmul_one]

private theorem equivCoprod_y_pow (a b k : ℕ) :
    equivCoprod a b (y a b 0 ^ k) = Monoid.Coprod.inr (.ofAdd (k : ZMod b)) := by
  rw [map_pow, equivCoprod_y, ← map_pow, ← ofAdd_nsmul, nsmul_one]

/-- An element of `Δ(a, b, 0)` has finite order if and only if it is conjugate to a finite-order
integer power of `x a b 0` or `y a b 0`. -/
theorem isOfFinOrder_iff {a b : ℕ} {g : TriangleGroup a b 0} :
    IsOfFinOrder g ↔
      (∃ k : ℤ, IsOfFinOrder (x a b 0 ^ k) ∧ IsConj g (x a b 0 ^ k)) ∨
        (∃ k : ℤ, IsOfFinOrder (y a b 0 ^ k) ∧ IsConj g (y a b 0 ^ k)) := by
  rw [← (equivCoprod a b).injective.isOfFinOrder_iff (f := (equivCoprod a b).toMonoidHom),
    MulEquiv.coe_toMonoidHom, Monoid.Coprod.isOfFinOrder_iff]
  refine ⟨?_, ?_⟩
  · rintro (⟨u, hu, hconj⟩ | ⟨v, hv, hconj⟩)
    · obtain ⟨k, hk⟩ := ZMod.intCast_surjective u.toAdd
      have hu' : u = .ofAdd (k : ZMod a) := by rw [hk, ofAdd_toAdd]
      subst hu'
      have hc := (equivCoprod a b).symm.toMonoidHom.map_isConj hconj
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        equivCoprod_symm_inl_ofAdd_intCast] at hc
      have hfin : IsOfFinOrder (x a b 0 ^ k) := by
        rw [← equivCoprod_symm_inl_ofAdd_intCast]
        exact (equivCoprod a b).symm.toMonoidHom.isOfFinOrder ((inlHom a b).isOfFinOrder hu)
      exact Or.inl ⟨k, hfin, hc⟩
    · obtain ⟨k, hk⟩ := ZMod.intCast_surjective v.toAdd
      have hv' : v = .ofAdd (k : ZMod b) := by rw [hk, ofAdd_toAdd]
      subst hv'
      have hc := (equivCoprod a b).symm.toMonoidHom.map_isConj hconj
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        equivCoprod_symm_inr_ofAdd_intCast] at hc
      have hfin : IsOfFinOrder (y a b 0 ^ k) := by
        rw [← equivCoprod_symm_inr_ofAdd_intCast]
        exact (equivCoprod a b).symm.toMonoidHom.isOfFinOrder ((inrHom a b).isOfFinOrder hv)
      exact Or.inr ⟨k, hfin, hc⟩
  · rintro (⟨k, hfin, hconj⟩ | ⟨k, hfin, hconj⟩)
    · refine Or.inl ⟨.ofAdd (k : ZMod a), ?_, ?_⟩
      · have h2 : IsOfFinOrder (equivCoprod a b (x a b 0 ^ k)) :=
          (equivCoprod a b).toMonoidHom.isOfFinOrder hfin
        rw [equivCoprod_x_zpow] at h2
        exact (Monoid.Coprod.inl_injective.isOfFinOrder_iff (f := inlHom a b)).mp h2
      · have hc := (equivCoprod a b).toMonoidHom.map_isConj hconj
        rwa [MulEquiv.coe_toMonoidHom, equivCoprod_x_zpow] at hc
    · refine Or.inr ⟨.ofAdd (k : ZMod b), ?_, ?_⟩
      · have h2 : IsOfFinOrder (equivCoprod a b (y a b 0 ^ k)) :=
          (equivCoprod a b).toMonoidHom.isOfFinOrder hfin
        rw [equivCoprod_y_zpow] at h2
        exact (Monoid.Coprod.inr_injective.isOfFinOrder_iff (f := inrHom a b)).mp h2
      · have hc := (equivCoprod a b).toMonoidHom.map_isConj hconj
        rwa [MulEquiv.coe_toMonoidHom, equivCoprod_y_zpow] at hc

/-- When `a` and `b` are nonzero, an element of `Δ(a, b, 0)` has finite order if and only if it is
conjugate to `x a b 0 ^ k` for some `k < a` or to `y a b 0 ^ k` for some `k < b`. -/
theorem isOfFinOrder_iff_of_neZero {a b : ℕ} [NeZero a] [NeZero b] {g : TriangleGroup a b 0} :
    IsOfFinOrder g ↔
      (∃ k < a, IsConj g (x a b 0 ^ k)) ∨ (∃ k < b, IsConj g (y a b 0 ^ k)) := by
  rw [← (equivCoprod a b).injective.isOfFinOrder_iff (f := (equivCoprod a b).toMonoidHom),
    MulEquiv.coe_toMonoidHom, Monoid.Coprod.isOfFinOrder_iff]
  refine ⟨?_, ?_⟩
  · rintro (⟨u, -, hconj⟩ | ⟨v, -, hconj⟩)
    · refine Or.inl ⟨u.toAdd.val, u.toAdd.val_lt, ?_⟩
      have hu : u = .ofAdd (u.toAdd.val : ZMod a) := by simp
      rw [hu] at hconj
      have hc := (equivCoprod a b).symm.toMonoidHom.map_isConj hconj
      rwa [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        equivCoprod_symm_inl_ofAdd_natCast] at hc
    · refine Or.inr ⟨v.toAdd.val, v.toAdd.val_lt, ?_⟩
      have hv : v = .ofAdd (v.toAdd.val : ZMod b) := by simp
      rw [hv] at hconj
      have hc := (equivCoprod a b).symm.toMonoidHom.map_isConj hconj
      rwa [MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
        equivCoprod_symm_inr_ofAdd_natCast] at hc
  · rintro (⟨k, -, hconj⟩ | ⟨k, -, hconj⟩)
    · refine Or.inl ⟨.ofAdd (k : ZMod a), isOfFinOrder_of_finite _, ?_⟩
      have hc := (equivCoprod a b).toMonoidHom.map_isConj hconj
      rwa [MulEquiv.coe_toMonoidHom, equivCoprod_x_pow] at hc
    · refine Or.inr ⟨.ofAdd (k : ZMod b), isOfFinOrder_of_finite _, ?_⟩
      have hc := (equivCoprod a b).toMonoidHom.map_isConj hconj
      rwa [MulEquiv.coe_toMonoidHom, equivCoprod_y_pow] at hc

/-- For `1 < n`, an element of `Δ(a, b, 0)` has order `n` if and only if it is conjugate to an
integer power of `x a b 0` or `y a b 0` of order `n`. -/
theorem orderOf_eq_iff {a b n : ℕ} (hn : 1 < n) {g : TriangleGroup a b 0} :
    orderOf g = n ↔
      (∃ k : ℤ, orderOf (x a b 0 ^ k) = n ∧ IsConj g (x a b 0 ^ k)) ∨
        (∃ k : ℤ, orderOf (y a b 0 ^ k) = n ∧ IsConj g (y a b 0 ^ k)) := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · have hfin : IsOfFinOrder g := orderOf_pos_iff.mp (by omega)
    rcases isOfFinOrder_iff.mp hfin with ⟨k, -, hconj⟩ | ⟨k, -, hconj⟩
    · let ⟨_, hc⟩ := hconj
      exact Or.inl ⟨k, by rw [← hc.orderOf_eq, hg], hconj⟩
    · let ⟨_, hc⟩ := hconj
      exact Or.inr ⟨k, by rw [← hc.orderOf_eq, hg], hconj⟩
  · rintro (⟨k, hk, ⟨_, hc⟩⟩ | ⟨k, hk, ⟨_, hc⟩⟩) <;> rw [hc.orderOf_eq, hk]

/-- When `a` and `b` are nonzero, `Nat.lcm a b` divides the index of every torsion-free subgroup
`H ≤ TriangleGroup a b 0`. -/
theorem lcm_dvd_index_of_isMulTorsionFree {a b : ℕ} [NeZero a] [NeZero b]
    (H : Subgroup (TriangleGroup a b 0)) [IsMulTorsionFree H] :
    Nat.lcm a b ∣ H.index := by
  have hx : IsOfFinOrder (x a b 0) :=
    orderOf_pos_iff.mp (by rw [orderOf_x_zero]; exact Nat.pos_of_ne_zero (NeZero.ne a))
  have hy : IsOfFinOrder (y a b 0) :=
    orderOf_pos_iff.mp (by rw [orderOf_y_zero]; exact Nat.pos_of_ne_zero (NeZero.ne b))
  refine Nat.lcm_dvd ?_ ?_
  · simpa [orderOf_x_zero] using H.orderOf_dvd_index_of_isMulTorsionFree hx
  · simpa [orderOf_y_zero] using H.orderOf_dvd_index_of_isMulTorsionFree hy

end TriangleGroup

end TauCeti
