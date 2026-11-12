/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Homomorphisms out of `ℤ/Nℤ` and `(ℤ/Nℤ)²`

For `N ≠ 0`, a homomorphism `ℤ/Nℤ →* G` to a group `G` is determined by the image of `1`, which
is an element of `G` killed by `N`, and every such element arises: `ZMod.lift` descends its powers
to `ℤ/Nℤ`. Likewise, for a commutative group `G`, a homomorphism `(ℤ/Nℤ)² →* G` is determined by
the pair of images of `(1, 0)` and `(0, 1)`, both killed by `N`. The groups `ℤ/Nℤ` and `(ℤ/Nℤ)²`
are written multiplicatively, as `Multiplicative (ZMod N)` and `Multiplicative (ZMod N × ZMod N)`.

## Main definitions

* `TauCeti.zmodMonoidHomEquiv G`: the homomorphisms `ℤ/Nℤ →* G` are the elements of `G` killed by
  `N`.
* `TauCeti.zmodProdMonoidHomEquiv G`: the homomorphisms `(ℤ/Nℤ)² →* G` are the pairs of elements of
  `G` killed by `N`.

## Main results

* `Multiplicative.mem_zpowers_ofAdd_one`: the element `1` generates `ℤ/Nℤ`.
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

namespace TauCeti

/-- The homomorphism `ℤ/Nℤ →+ G` sending `1` to an element `g` of `G` killed by `N`. -/
private noncomputable def zmodLift {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) :
    ZMod N →+ Additive G :=
  ZMod.lift N ⟨zmultiplesHom _ (.ofMul g), by
    rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, hg, ofMul_one]⟩

private theorem zmodLift_natCast {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) (k : ℕ) :
    (zmodLift g hg k).toMul = g ^ k := by
  rw [← Int.cast_natCast, zmodLift, ZMod.lift_coe, zmultiplesHom_apply, natCast_zsmul, toMul_nsmul,
    toMul_ofMul]

private theorem zmodLift_one {G : Type*} [Group G] (g : G) (hg : g ^ N = 1) :
    (zmodLift g hg 1).toMul = g := by
  rw [← Nat.cast_one, zmodLift_natCast, pow_one]

private theorem zmodLift_apply {G : Type*} [Group G] [NeZero N] (g : G) (hg : g ^ N = 1)
    (a : ZMod N) : (zmodLift g hg a).toMul = g ^ a.val := by
  rw [← zmodLift_natCast, ZMod.natCast_zmod_val]

variable [NeZero N]

variable (N) in
/-- **Homomorphisms `ℤ/Nℤ →* G` are the elements of `G` killed by `N`**, through the image of
`1`. -/
noncomputable def zmodMonoidHomEquiv (G : Type*) [Group G] :
    (Multiplicative (ZMod N) →* G) ≃ {g : G // g ^ N = 1} where
  toFun φ := ⟨φ (.ofAdd 1), by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero, map_one]⟩
  invFun g := (zmodLift g.1 g.2).toMultiplicativeLeft
  left_inv φ := by
    refine MonoidHom.ext fun z ↦ ?_
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, z = .ofAdd (k : ZMod N) := ⟨z.toAdd.val, by simp⟩
    rw [AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, Function.comp_apply,
      toAdd_ofAdd, zmodLift_natCast, ← map_pow, ← ofAdd_nsmul, nsmul_one]
  right_inv g := by
    refine Subtype.ext ?_
    dsimp only
    rw [AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, Function.comp_apply,
      toAdd_ofAdd, zmodLift_one]

/-- The element of `G` of a homomorphism `φ : ℤ/Nℤ →* G` is `φ 1`. -/
@[simp]
theorem coe_zmodMonoidHomEquiv_apply {G : Type*} [Group G] (φ : Multiplicative (ZMod N) →* G) :
    (zmodMonoidHomEquiv N G φ : G) = φ (.ofAdd 1) :=
  (rfl)

/-- The homomorphism associated to an element killed by `N` sends `1` to that element,
including when `N = 1`. -/
theorem zmodMonoidHomEquiv_symm_apply_ofAdd_one {G : Type*} [Group G]
    (g : {g : G // g ^ N = 1}) : (zmodMonoidHomEquiv N G).symm g (.ofAdd 1) = g.1 := by
  rw [← coe_zmodMonoidHomEquiv_apply, Equiv.apply_symm_apply]

/-- The homomorphism `ℤ/Nℤ →* G` of an element `g` killed by `N` sends `a` to `g ^ a.val`. -/
@[simp]
theorem zmodMonoidHomEquiv_symm_apply {G : Type*} [Group G] (g : {g : G // g ^ N = 1})
    (a : ZMod N) : (zmodMonoidHomEquiv N G).symm g (.ofAdd a) = g.1 ^ a.val :=
  zmodLift_apply _ _ a

variable (N) in
/-- **Homomorphisms `(ℤ/Nℤ)² →* G` are the pairs of elements of `G` killed by `N`**, through the
images of `(1, 0)` and `(0, 1)`. -/
noncomputable def zmodProdMonoidHomEquiv (G : Type*) [CommGroup G] :
    (Multiplicative (ZMod N × ZMod N) →* G) ≃ {g : G // g ^ N = 1} × {g : G // g ^ N = 1} where
  toFun φ := (zmodMonoidHomEquiv N G (φ.comp (AddMonoidHom.inl _ _).toMultiplicative),
    zmodMonoidHomEquiv N G (φ.comp (AddMonoidHom.inr _ _).toMultiplicative))
  invFun g := ((zmodLift g.1.1 g.1.2).coprod (zmodLift g.2.1 g.2.2)).toMultiplicativeLeft
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
    (zmodProdMonoidHomEquiv N G).symm g (.ofAdd (a, b)) = g.1.1 ^ a.val * g.2.1 ^ b.val := by
  simp [zmodProdMonoidHomEquiv, zmodLift_apply]

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
