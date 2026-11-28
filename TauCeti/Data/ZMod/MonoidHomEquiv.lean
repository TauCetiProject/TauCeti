/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Homomorphisms out of `ℤ/Nℤ` and `(ℤ/Nℤ)²`

A homomorphism `ℤ/Nℤ →* G` to a monoid `G` is determined by the image of `1`, which is an element
of `G` killed by `N` (and a unit when `N = 0`), and every such element arises: `ZMod.lift` descends
its powers to `ℤ/Nℤ` (`TauCeti.zmodLift`, valid for all `N : ℕ` including `N = 0`). For `N ≠ 0`
and a group `G`, this gives an equivalence `TauCeti.zmodMonoidHomEquiv G`. Likewise, for `N ≠ 0`
and a commutative group `G`, a homomorphism `(ℤ/Nℤ)² →* G` is determined by the pair of images of
`(1, 0)` and `(0, 1)`, both killed by `N`. The groups `ℤ/Nℤ` and `(ℤ/Nℤ)²` are written
multiplicatively, as `Multiplicative (ZMod N)` and `Multiplicative (ZMod N × ZMod N)`.

## Main definitions

* `TauCeti.zmodLift`: the homomorphism `Multiplicative (ZMod N) →* G` sending `ofAdd 1` to `g`
  when `g ^ N = 1` and `N = 0 → IsUnit g` (for arbitrary `N : ℕ` and any `[Monoid G]`).
* `TauCeti.zmodMonoidHomEquiv G`: the homomorphisms `ℤ/Nℤ →* G` are the elements of `G` killed by
  `N`.
* `TauCeti.zmodProdMonoidHomEquiv G`: the homomorphisms `(ℤ/Nℤ)² →* G` are the pairs of elements of
  `G` killed by `N`.

## Main results

* `Multiplicative.mem_zpowers_ofAdd_one`: the element `1` generates `ℤ/Nℤ`.
* `Multiplicative.ofAdd_one_pow`, `Multiplicative.ofAdd_natCast`,
  `Multiplicative.ofAdd_intCast`: power and cast identities for `ofAdd`.
* `MonoidHom.ext_mzmod`: two monoid homomorphisms out of `Multiplicative (ZMod N)` agreeing on
  `ofAdd 1` are equal (for arbitrary `N : ℕ`).
* `TauCeti.zmodLift_ofAdd_one`, `TauCeti.zmodLift_ofAdd_natCast`,
  `TauCeti.zmodLift_ofAdd_intCast`: evaluation of `zmodLift` at `1` and integer/natural casts.
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

/-- The generator `ofAdd 1` of `Multiplicative (ZMod N)` has `N`-th power `1`. -/
theorem Multiplicative.ofAdd_one_pow :
    (.ofAdd (1 : ZMod N) : Multiplicative (ZMod N)) ^ N = 1 := by
  rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero]

/-- The element `ofAdd (k : ZMod N)` for `k : ℕ` equals `(ofAdd 1) ^ k`. -/
theorem Multiplicative.ofAdd_natCast (k : ℕ) :
    (.ofAdd (k : ZMod N) : Multiplicative (ZMod N)) = (.ofAdd 1) ^ k := by
  rw [← nsmul_one k, ofAdd_nsmul]

/-- The element `ofAdd (k : ZMod N)` for `k : ℤ` equals `(ofAdd 1) ^ k`. -/
theorem Multiplicative.ofAdd_intCast (k : ℤ) :
    (.ofAdd (k : ZMod N) : Multiplicative (ZMod N)) = (.ofAdd 1) ^ k := by
  rw [← zsmul_one k, ofAdd_zsmul]

/-- Two monoid homomorphisms out of `Multiplicative (ZMod N)` that agree on the generator
`ofAdd 1` are equal. -/
theorem MonoidHom.ext_mzmod {G : Type*} [Monoid G] {f g : Multiplicative (ZMod N) →* G}
    (h : f (.ofAdd 1) = g (.ofAdd 1)) : f = g :=
  MonoidHom.eq_of_eqOn_dense
    (by
      rw [← Subgroup.zpowers_eq_closure, eq_top_iff]
      exact fun x _ ↦ Multiplicative.mem_zpowers_ofAdd_one x)
    (by rintro _ rfl; exact h)

namespace TauCeti

/-- The homomorphism `Multiplicative (ZMod N) →* G` sending `ofAdd 1` to an element `g` of a
monoid `G` killed by `N` and invertible when `N = 0` (valid for all `N : ℕ`, including `N = 0`). -/
noncomputable def zmodLift {G : Type*} [Monoid G] (g : G) (hg : g ^ N = 1)
    (hu : N = 0 → IsUnit g) : Multiplicative (ZMod N) →* G :=
  let hunit : IsUnit g := match N, hg, hu with
    | 0, _, hu => hu rfl
    | n + 1, hg, _ => ⟨⟨g, g ^ n, by rw [← pow_succ', hg], by rw [← pow_succ, hg]⟩, rfl⟩
  (Units.coeHom G).comp
    (ZMod.lift N ⟨zmultiplesHom _ (.ofMul hunit.unit), by
      have huN : hunit.unit ^ N = 1 := Units.ext (by simp [hg])
      rw [zmultiplesHom_apply, natCast_zsmul, ← ofMul_pow, huN, ofMul_one]⟩).toMultiplicativeLeft

/-- `zmodLift` sends the generator `ofAdd 1` to `g`. -/
@[simp]
theorem zmodLift_ofAdd_one {G : Type*} [Monoid G] (g : G) (hg : g ^ N = 1)
    (hu : N = 0 → IsUnit g) : zmodLift g hg hu (.ofAdd 1) = g := by
  rw [zmodLift, MonoidHom.coe_comp, Function.comp_apply, Units.coeHom_apply,
    AddMonoidHom.coe_toMultiplicativeLeft, Function.comp_apply, Function.comp_apply, toAdd_ofAdd,
    ← Int.cast_one, ZMod.lift_coe]
  simp

/-- `zmodLift` sends `ofAdd (k : ZMod N)` for `k : ℕ` to `g ^ k`. -/
@[simp]
theorem zmodLift_ofAdd_natCast {G : Type*} [Monoid G] (g : G) (hg : g ^ N = 1)
    (hu : N = 0 → IsUnit g) (k : ℕ) : zmodLift g hg hu (.ofAdd (k : ZMod N)) = g ^ k := by
  rw [Multiplicative.ofAdd_natCast, map_pow, zmodLift_ofAdd_one]

/-- `zmodLift` sends `ofAdd (k : ZMod N)` for `k : ℤ` to `g ^ k`. -/
@[simp]
theorem zmodLift_ofAdd_intCast {G : Type*} [DivisionMonoid G] (g : G) (hg : g ^ N = 1)
    (hu : N = 0 → IsUnit g) (k : ℤ) : zmodLift g hg hu (.ofAdd (k : ZMod N)) = g ^ k := by
  rw [Multiplicative.ofAdd_intCast, map_zpow, zmodLift_ofAdd_one]

variable [NeZero N]

variable (N) in
/-- **Homomorphisms `ℤ/Nℤ →* G` are the elements of `G` killed by `N`**, through the image of
`1`. -/
noncomputable def zmodMonoidHomEquiv (G : Type*) [Group G] :
    (Multiplicative (ZMod N) →* G) ≃ {g : G // g ^ N = 1} where
  toFun φ := ⟨φ (.ofAdd 1), by rw [← map_pow, Multiplicative.ofAdd_one_pow, map_one]⟩
  invFun g := zmodLift g.val g.property (fun _ ↦ Group.isUnit _)
  left_inv φ := by
    -- Retain `[NeZero N]` on this pre-existing equivalence so downstream callers keep their
    -- signatures without out-of-scope edits.
    have _ := ‹NeZero N›
    exact MonoidHom.ext_mzmod (by simp)
  right_inv g := Subtype.ext (zmodLift_ofAdd_one g.val g.property _)

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
    (a : ZMod N) : (zmodMonoidHomEquiv N G).symm g (.ofAdd a) = g.val ^ a.val := by
  nth_rw 1 [← ZMod.natCast_zmod_val a]
  rw [Multiplicative.ofAdd_natCast, map_pow, zmodMonoidHomEquiv_symm_apply_ofAdd_one]

variable (N) in
/-- **Homomorphisms `(ℤ/Nℤ)² →* G` are the pairs of elements of `G` killed by `N`**, through the
images of `(1, 0)` and `(0, 1)`. -/
noncomputable def zmodProdMonoidHomEquiv (G : Type*) [CommGroup G] :
    (Multiplicative (ZMod N × ZMod N) →* G) ≃ {g : G // g ^ N = 1} × {g : G // g ^ N = 1} where
  toFun φ := (zmodMonoidHomEquiv N G (φ.comp (AddMonoidHom.inl _ _).toMultiplicative),
    zmodMonoidHomEquiv N G (φ.comp (AddMonoidHom.inr _ _).toMultiplicative))
  invFun g :=
    ((AddMonoidHom.toMultiplicativeLeft.symm
        (zmodLift g.1.val g.1.property (fun _ ↦ Group.isUnit _))).coprod
      (AddMonoidHom.toMultiplicativeLeft.symm
        (zmodLift g.2.val g.2.property (fun _ ↦ Group.isUnit _)))).toMultiplicativeLeft
  left_inv φ := by
    refine MonoidHom.ext fun z ↦ ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, z = .ofAdd ((a : ZMod N), (b : ZMod N)) :=
      ⟨z.toAdd.1.val, z.toAdd.2.val, by simp⟩
    have hab : ((a : ZMod N), (b : ZMod N)) = a • (1, 0) + b • (0, 1) := by ext <;> simp
    rw [hab, ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow, map_pow]
    simp
  right_inv g := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp

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
  have h1 : (zmodProdMonoidHomEquiv N G).symm g (.ofAdd (1, 0)) = g.1.val := by
    rw [← coe_zmodProdMonoidHomEquiv_apply_fst, Equiv.apply_symm_apply]
  have h2 : (zmodProdMonoidHomEquiv N G).symm g (.ofAdd (0, 1)) = g.2.val := by
    rw [← coe_zmodProdMonoidHomEquiv_apply_snd, Equiv.apply_symm_apply]
  have hab : (a, b) = a.val • (1, 0) + b.val • (0, 1) := by ext <;> simp
  rw [hab, ofAdd_add, ofAdd_nsmul, ofAdd_nsmul, map_mul, map_pow, map_pow, h1, h2]

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
