/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Homomorphisms out of `ℤ/Nℤ` and `(ℤ/Nℤ)²`

For any `N : ℕ` (including `N = 0`), a homomorphism `ℤ/Nℤ →* G` to a group `G` is determined by
the image of `1`, which is an element of `G` killed by `N`, and every such element arises:
`ZMod.lift` descends its powers to `ℤ/Nℤ`. Likewise, for `N ≠ 0` and a commutative group `G`, a
homomorphism `(ℤ/Nℤ)² →* G` is determined by the pair of images of `(1, 0)` and `(0, 1)`, both
killed by `N`. The groups `ℤ/Nℤ` and `(ℤ/Nℤ)²` are written multiplicatively, as
`Multiplicative (ZMod N)` and `Multiplicative (ZMod N × ZMod N)`.

## Main definitions

* `TauCeti.zmodMonoidHomEquiv N G`: the homomorphisms `ℤ/Nℤ →* G` are the elements of `G` killed by
  `N`.
* `TauCeti.zmodProdMonoidHomEquiv N G`: the homomorphisms `(ℤ/Nℤ)² →* G` are the pairs of elements
  of `G` killed by `N`.

## Main results

* `Multiplicative.mem_zpowers_ofAdd_one`: the element `1` generates `ℤ/Nℤ`.
* `TauCeti.ofAdd_one_pow_modulus_eq_one`, `TauCeti.ofAdd_neg_one_ne_one_of_ne_one`: the `N`-th
  power of `ofAdd 1` is `1`, and `ofAdd (-1) ≠ 1` when `N ≠ 1`.
* `TauCeti.zmodMonoidHom_map_ofAdd_intCast`: any homomorphism `Multiplicative (ZMod N) →* G` sends
  `ofAdd (k : ZMod N)` to the `k`-th power of its value at `ofAdd 1`.
* `TauCeti.zmodMonoidHom_ext`: extensionality on the standard generator `ofAdd 1`.
* `TauCeti.zmodMonoidHomEquiv_symm_apply_ofAdd_one`,
  `TauCeti.zmodMonoidHomEquiv_symm_apply_ofAdd_intCast`, `TauCeti.zmodMonoidHomEquiv_symm_apply`:
  inverse evaluation rules on `1`, integer casts (for arbitrary `N`), and residues modulo `N`.
* `TauCeti.zmodProdMonoidHomEquiv_symm_apply`: the homomorphism of `(g, h)` sends `(a, b)` to
  `g ^ a.val * h ^ b.val`.
* `TauCeti.injective_zmod_three_prod_iff`: a homomorphism `(ℤ/3ℤ)² →* G` is injective exactly when
  `(1, 0)`, `(0, 1)`, `(1, 1)` and `(-1, 1)` are not in its kernel.
-/

public section

variable {N : ℕ}

/-- The standard generator `1` of `ℤ/Nℤ`, written multiplicatively, generates the group. -/
theorem Multiplicative.mem_zpowers_ofAdd_one (x : Multiplicative (ZMod N)) :
    x ∈ Subgroup.zpowers (.ofAdd 1) :=
  ⟨x.toAdd.cast, by simp [← ofAdd_zsmul]⟩

namespace TauCeti

/-- The standard generator `ofAdd 1` of `Multiplicative (ZMod N)` has `N`-th power `1`. -/
@[simp]
theorem ofAdd_one_pow_modulus_eq_one : (Multiplicative.ofAdd (1 : ZMod N)) ^ N = 1 := by
  rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero]

/-- For `N ≠ 1`, the inverse generator `ofAdd (-1)` of `Multiplicative (ZMod N)` is nontrivial. -/
theorem ofAdd_neg_one_ne_one_of_ne_one (hN : N ≠ 1) :
    Multiplicative.ofAdd (-1 : ZMod N) ≠ 1 := by
  simp [ZMod.one_eq_zero_iff, hN]

/-- Any homomorphism out of `Multiplicative (ZMod N)` sends `ofAdd (k : ZMod N)` to the `k`-th
power of its value at `ofAdd 1`. -/
theorem zmodMonoidHom_map_ofAdd_intCast {G : Type*} [DivisionMonoid G]
    (φ : Multiplicative (ZMod N) →* G) (k : ℤ) :
    φ (.ofAdd (k : ZMod N)) = φ (.ofAdd 1) ^ k := by
  rw [← zsmul_one k, ofAdd_zsmul, map_zpow]

/-- Two homomorphisms `Multiplicative (ZMod N) →* G` that agree on `ofAdd 1` are equal. -/
@[ext]
theorem zmodMonoidHom_ext {G : Type*} [Monoid G] {φ ψ : Multiplicative (ZMod N) →* G}
    (h : φ (.ofAdd 1) = ψ (.ofAdd 1)) : φ = ψ :=
  MonoidHom.eq_of_eqOn_dense
    (by
      rw [← Subgroup.zpowers_eq_closure, eq_top_iff]
      exact fun x _ ↦ Multiplicative.mem_zpowers_ofAdd_one x)
    (by rintro _ rfl; exact h)

/-- The homomorphism `ℤ/Nℤ →+ G` sending `1` to an element `g` of `G` killed by `N`. -/
private noncomputable def zmodLift {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) :
    ZMod N →+ Additive G :=
  ZMod.lift N ⟨zmultiplesHom _ (.ofMul g), by
    rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hg, ofMul_one]⟩

private theorem zmodLift_one {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) :
    (zmodLift g hg 1).toMul = g := by
  rw [← Int.cast_one, zmodLift, ZMod.lift_coe]
  simp

variable (N) in
/-- **Homomorphisms `ℤ/Nℤ →* G` are the elements of `G` killed by `N`**, through the image of
`1` (valid for all `N : ℕ`, including `N = 0`). -/
noncomputable def zmodMonoidHomEquiv (G : Type*) [Group G] :
    (Multiplicative (ZMod N) →* G) ≃ {g : G // g ^ N = 1} where
  toFun φ := ⟨φ (.ofAdd 1), by
    rw [← map_pow, ofAdd_one_pow_modulus_eq_one, map_one]⟩
  invFun g := (zmodLift g.val g.property).toMultiplicativeLeft
  left_inv φ := by
    ext
    exact zmodLift_one _ _
  right_inv g := Subtype.ext (zmodLift_one _ _)

/-- The element of `G` of a homomorphism `φ : ℤ/Nℤ →* G` is `φ 1`. -/
@[simp]
theorem coe_zmodMonoidHomEquiv_apply {G : Type*} [Group G] (φ : Multiplicative (ZMod N) →* G) :
    (zmodMonoidHomEquiv N G φ : G) = φ (.ofAdd 1) :=
  (rfl)

/-- The homomorphism `ℤ/Nℤ →* G` of an element `g` killed by `N` sends `ofAdd (k : ZMod N)` to
`g ^ k` (valid for all `N : ℕ`, including `N = 0`). -/
@[simp high]
theorem zmodMonoidHomEquiv_symm_apply_ofAdd_intCast {G : Type*} [Group G]
    (g : {g : G // g ^ N = 1}) (k : ℤ) :
    (zmodMonoidHomEquiv N G).symm g (.ofAdd (k : ZMod N)) = g.val ^ k := by
  simp [zmodMonoidHomEquiv, zmodLift]

/-- The homomorphism associated to an element killed by `N` sends `1` to that element,
including when `N = 0` or `N = 1`. -/
@[simp high]
theorem zmodMonoidHomEquiv_symm_apply_ofAdd_one {G : Type*} [Group G]
    (g : {g : G // g ^ N = 1}) : (zmodMonoidHomEquiv N G).symm g (.ofAdd 1) = g.val := by
  simpa using zmodMonoidHomEquiv_symm_apply_ofAdd_intCast g 1

/-- The homomorphism `ℤ/Nℤ →* G` of an element `g` killed by `N` sends `a` to `g ^ a.val`. -/
@[simp]
theorem zmodMonoidHomEquiv_symm_apply {G : Type*} [Group G] [NeZero N] (g : {g : G // g ^ N = 1})
    (a : ZMod N) : (zmodMonoidHomEquiv N G).symm g (.ofAdd a) = g.val ^ a.val := by
  conv_lhs => rw [← ZMod.natCast_zmod_val a, ← Int.cast_natCast]
  rw [zmodMonoidHomEquiv_symm_apply_ofAdd_intCast, zpow_natCast]

section

variable [NeZero N]

private theorem zmodLift_apply {G : Type*} [Group G] (g : G) (hg : g ^ N = 1)
    (a : ZMod N) : (zmodLift g hg a).toMul = g ^ a.val :=
  zmodMonoidHomEquiv_symm_apply ⟨g, hg⟩ a

variable (N) in
/-- **Homomorphisms `(ℤ/Nℤ)² →* G` are the pairs of elements of `G` killed by `N`**, through the
images of `(1, 0)` and `(0, 1)`. -/
noncomputable def zmodProdMonoidHomEquiv (G : Type*) [CommGroup G] :
    (Multiplicative (ZMod N × ZMod N) →* G) ≃ {g : G // g ^ N = 1} × {g : G // g ^ N = 1} where
  toFun φ := (zmodMonoidHomEquiv N G (φ.comp (AddMonoidHom.inl _ _).toMultiplicative),
    zmodMonoidHomEquiv N G (φ.comp (AddMonoidHom.inr _ _).toMultiplicative))
  invFun g := ((zmodLift g.1.val g.1.property).coprod
      (zmodLift g.2.val g.2.property)).toMultiplicativeLeft
  left_inv φ := by
    refine MonoidHom.ext fun z ↦ ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, z = .ofAdd ((a : ZMod N), (b : ZMod N)) :=
      ⟨z.toAdd.1.val, z.toAdd.2.val, by simp⟩
    have hab : ((a : ZMod N), (b : ZMod N)) = a • (1, 0) + b • (0, 1) := by ext <;> simp
    rw [hab, ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow, map_pow]
    simp [zmodMonoidHomEquiv, zmodLift_one]
  right_inv g := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp [zmodMonoidHomEquiv, zmodLift_one]

/-- The first element of `G` of a homomorphism `φ : (ℤ/Nℤ)² →* G` is `φ (1, 0)`. -/
@[simp]
theorem coe_zmodProdMonoidHomEquiv_apply_fst {G : Type*} [CommGroup G]
    (φ : Multiplicative (ZMod N × ZMod N) →* G) :
    ((zmodProdMonoidHomEquiv N G φ).1 : G) = φ (.ofAdd (1, 0)) :=
  (rfl)

/-- The second element of `G` of a homomorphism `φ : (ℤ/Nℤ)² →* G` is `φ (0, 1)`. -/
@[simp]
theorem coe_zmodProdMonoidHomEquiv_apply_snd {G : Type*} [CommGroup G]
    (φ : Multiplicative (ZMod N × ZMod N) →* G) :
    ((zmodProdMonoidHomEquiv N G φ).2 : G) = φ (.ofAdd (0, 1)) :=
  (rfl)

/-- The homomorphism `(ℤ/Nℤ)² →* G` of a pair `(g, h)` of elements killed by `N` sends `(a, b)`
to `g ^ a.val * h ^ b.val`. -/
@[simp]
theorem zmodProdMonoidHomEquiv_symm_apply {G : Type*} [CommGroup G]
    (g : {g : G // g ^ N = 1} × {g : G // g ^ N = 1}) (a b : ZMod N) :
    (zmodProdMonoidHomEquiv N G).symm g (.ofAdd (a, b)) = g.1.val ^ a.val * g.2.val ^ b.val := by
  simp [zmodProdMonoidHomEquiv, zmodLift_apply]

end

/-- **Injectivity on `(ℤ/3ℤ)²`.** A homomorphism `ψ : (ℤ/3ℤ)² →* G` is injective exactly when
`(1, 0)`, `(0, 1)`, `(1, 1)` and `(-1, 1)` are not in its kernel: every nonzero element of
`(ℤ/3ℤ)²` is one of these four or its negative. -/
theorem injective_zmod_three_prod_iff {G : Type*} [Group G]
    (ψ : Multiplicative (ZMod 3 × ZMod 3) →* G) :
    Function.Injective ψ ↔ ψ (.ofAdd (1, 0)) ≠ 1 ∧ ψ (.ofAdd (0, 1)) ≠ 1 ∧
      ψ (.ofAdd (1, 1)) ≠ 1 ∧ ψ (.ofAdd (-1, 1)) ≠ 1 := by
  rw [injective_iff_map_eq_one]
  refine ⟨fun h ↦ ⟨fun e ↦ absurd (h _ e) (by decide), fun e ↦ absurd (h _ e) (by decide),
    fun e ↦ absurd (h _ e) (by decide), fun e ↦ absurd (h _ e) (by decide)⟩,
    fun ⟨h₁, h₂, h₃, h₄⟩ z hz ↦ ?_⟩
  have hp : ∀ p : ZMod 3 × ZMod 3, p = 0 ∨ p = (1, 0) ∨ p = -(1, 0) ∨ p = (0, 1) ∨
      p = -(0, 1) ∨ p = (1, 1) ∨ p = -(1, 1) ∨ p = (-1, 1) ∨ p = -(-1, 1) := by
    decide
  obtain ⟨p, rfl⟩ : ∃ p, Multiplicative.ofAdd p = z := ⟨z.toAdd, rfl⟩
  rcases hp p with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ofAdd_zero
  all_goals first | contradiction | rw [ofAdd_neg, map_inv, inv_eq_one] at hz; contradiction

end TauCeti
