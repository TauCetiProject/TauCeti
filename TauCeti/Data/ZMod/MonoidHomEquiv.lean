/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Homomorphisms out of `ℤ/Nℤ` and `(ℤ/Nℤ)²`

For any `N : ℕ`, a homomorphism `ℤ/Nℤ →* G` to a group `G` is determined by the image of `1`,
which is an element of `G` killed by `N`, and every such element arises: `TauCeti.zmodLift`
descends its powers to `Multiplicative (ZMod N)` (including when `N = 0`, where `ZMod 0 = ℤ`).
When `N ≠ 0`, `TauCeti.zmodMonoidHomEquiv` packages this correspondence as an equivalence, and for
a commutative group `G`, `TauCeti.zmodProdMonoidHomEquiv` similarly identifies homomorphisms
`(ℤ/Nℤ)² →* G` with pairs of elements killed by `N`. The groups `ℤ/Nℤ` and `(ℤ/Nℤ)²` are written
multiplicatively, as `Multiplicative (ZMod N)` and `Multiplicative (ZMod N × ZMod N)`.

## Main definitions

* `TauCeti.zmodLift`: for any `N : ℕ` (including `N = 0`), the homomorphism
  `Multiplicative (ZMod N) →* G` sending `1` to an element `g : G` with `g ^ N = 1`.
* `TauCeti.zmodMonoidHomEquiv G`: the homomorphisms `ℤ/Nℤ →* G` are the elements of `G` killed by
  `N`.
* `TauCeti.zmodProdMonoidHomEquiv G`: the homomorphisms `(ℤ/Nℤ)² →* G` are the pairs of elements of
  `G` killed by `N`.

## Main results

* `Multiplicative.mem_zpowers_ofAdd_one`, `Multiplicative.closure_ofAdd_one`: the element `1`
  generates `ℤ/Nℤ`.
* `TauCeti.zmodLift_ofAdd_intCast`, `TauCeti.zmodLift_ofAdd_natCast`,
  `TauCeti.zmodLift_ofAdd_one`, `TauCeti.zmodLift_ofAdd`: evaluation of `TauCeti.zmodLift` on
  integer casts, natural casts, `1`, and arbitrary elements of `ZMod N` (for `N ≠ 0`).
* `TauCeti.zmodMonoidHomEquiv_symm_apply` and `TauCeti.zmodProdMonoidHomEquiv_symm_apply`: the
  homomorphism of `g` sends `a` to `g ^ a.val`, and that of `(g, h)` sends `(a, b)` to
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

/-- The standard generator `1` of `ℤ/Nℤ`, written multiplicatively, has subgroup closure `⊤`. -/
theorem Multiplicative.closure_ofAdd_one (N : ℕ) :
    Subgroup.closure {(.ofAdd 1 : Multiplicative (ZMod N))} = ⊤ :=
  eq_top_iff.mpr fun x _ ↦
    Subgroup.zpowers_eq_closure (Multiplicative.ofAdd (1 : ZMod N)) ▸
      Multiplicative.mem_zpowers_ofAdd_one x

namespace TauCeti

/-- The homomorphism `Multiplicative (ZMod N) →* G` sending `.ofAdd 1` to an element `g` of `G`
satisfying `g ^ N = 1`. Valid for all `N : ℕ`, including `N = 0` (`ZMod 0 = ℤ`). -/
noncomputable def zmodLift {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) :
    Multiplicative (ZMod N) →* G :=
  (ZMod.lift N ⟨zmultiplesHom (Additive G) (.ofMul g), by
    rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hg, ofMul_one]⟩).toMultiplicativeLeft

/-- `zmodLift g hg` sends the integer cast `k : ZMod N` to `g ^ k`. -/
@[simp]
theorem zmodLift_ofAdd_intCast {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) (k : ℤ) :
    zmodLift g hg (.ofAdd (k : ZMod N)) = g ^ k := by
  rw [zmodLift, AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, Function.comp_apply,
    toAdd_ofAdd, ZMod.lift_coe, zmultiplesHom_apply, toMul_zsmul, toMul_ofMul]

/-- `zmodLift g hg` sends the natural cast `k : ZMod N` to `g ^ k`. -/
@[simp]
theorem zmodLift_ofAdd_natCast {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) (k : ℕ) :
    zmodLift g hg (.ofAdd (k : ZMod N)) = g ^ k := by
  rw [← Int.cast_natCast, zmodLift_ofAdd_intCast, zpow_natCast]

/-- `zmodLift g hg` sends the standard generator `.ofAdd 1` to `g`. -/
@[simp]
theorem zmodLift_ofAdd_one {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) :
    zmodLift g hg (.ofAdd 1) = g := by
  rw [← Nat.cast_one, zmodLift_ofAdd_natCast, pow_one]

/-- For `N ≠ 0`, `zmodLift g hg` sends `.ofAdd a` to `g ^ a.val`.

Not `@[simp]`: it overlaps with `zmodLift_ofAdd_intCast`, `zmodLift_ofAdd_natCast`, and
`zmodLift_ofAdd_one`. -/
theorem zmodLift_ofAdd {G : Type*} [Group G] [NeZero N] (g : G) (hg : g ^ N = 1) (a : ZMod N) :
    zmodLift g hg (.ofAdd a) = g ^ a.val := by
  rw [← zmodLift_ofAdd_natCast, ZMod.natCast_zmod_val]

variable [NeZero N]

variable (N) in
/-- **Homomorphisms `ℤ/Nℤ →* G` are the elements of `G` killed by `N`**, through the image of
`1`. -/
noncomputable def zmodMonoidHomEquiv (G : Type*) [Group G] :
    (Multiplicative (ZMod N) →* G) ≃ {g : G // g ^ N = 1} where
  toFun φ := ⟨φ (.ofAdd 1), by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero, map_one]⟩
  invFun g := zmodLift g.val g.property
  left_inv φ := by
    refine MonoidHom.ext fun z ↦ ?_
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = .ofAdd (k : ZMod N) := ⟨z.toAdd.val, by simp⟩
    rw [zmodLift_ofAdd_natCast, ← map_pow, ← ofAdd_nsmul, nsmul_one]
  right_inv g := Subtype.ext (zmodLift_ofAdd_one g.val g.property)

/-- The element of `G` of a homomorphism `φ : ℤ/Nℤ →* G` is `φ 1`. -/
@[simp]
theorem coe_zmodMonoidHomEquiv_apply {G : Type*} [Group G] (φ : Multiplicative (ZMod N) →* G) :
    (zmodMonoidHomEquiv N G φ : G) = φ (.ofAdd 1) :=
  (rfl)

/-- The homomorphism associated to an element killed by `N` sends `1` to that element,
including when `N = 1`. -/
theorem zmodMonoidHomEquiv_symm_apply_ofAdd_one {G : Type*} [Group G]
    (g : {g : G // g ^ N = 1}) : (zmodMonoidHomEquiv N G).symm g (.ofAdd 1) = g.val := by
  rw [← coe_zmodMonoidHomEquiv_apply, Equiv.apply_symm_apply]

/-- The homomorphism `ℤ/Nℤ →* G` of an element `g` killed by `N` sends `a` to `g ^ a.val`. -/
@[simp]
theorem zmodMonoidHomEquiv_symm_apply {G : Type*} [Group G] (g : {g : G // g ^ N = 1})
    (a : ZMod N) : (zmodMonoidHomEquiv N G).symm g (.ofAdd a) = g.val ^ a.val :=
  zmodLift_ofAdd g.val g.property a

variable (N) in
/-- **Homomorphisms `(ℤ/Nℤ)² →* G` are the pairs of elements of `G` killed by `N`**, through the
images of `(1, 0)` and `(0, 1)`. -/
noncomputable def zmodProdMonoidHomEquiv (G : Type*) [CommGroup G] :
    (Multiplicative (ZMod N × ZMod N) →* G) ≃ {g : G // g ^ N = 1} × {g : G // g ^ N = 1} where
  toFun φ := (zmodMonoidHomEquiv N G (φ.comp (AddMonoidHom.inl _ _).toMultiplicative),
    zmodMonoidHomEquiv N G (φ.comp (AddMonoidHom.inr _ _).toMultiplicative))
  invFun g :=
    ((AddMonoidHom.toMultiplicativeLeft.symm (zmodLift g.1.val g.1.property)).coprod
      (AddMonoidHom.toMultiplicativeLeft.symm (zmodLift g.2.val g.2.property))).toMultiplicativeLeft
  left_inv φ := by
    refine MonoidHom.ext fun z ↦ ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, z = .ofAdd ((a : ZMod N), (b : ZMod N)) :=
      ⟨z.toAdd.1.val, z.toAdd.2.val, by simp⟩
    have hab : ((a : ZMod N), (b : ZMod N)) = a • (1, 0) + b • (0, 1) := by ext <;> simp
    rw [hab, ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow, map_pow]
    simp [zmodMonoidHomEquiv]
  right_inv g := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp [zmodMonoidHomEquiv]

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
  simp [zmodProdMonoidHomEquiv, zmodLift_ofAdd]

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
