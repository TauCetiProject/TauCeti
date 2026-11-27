/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Free.BCH
public import TauCeti.Algebra.Lie.LowerCentralSeries

/-!
# The Baker–Campbell–Hausdorff group of a nilpotent Lie algebra

Let `L` be a nilpotent Lie algebra over `ℚ`, of class at most `c`, so that
`lowerCentralSeries ℚ L L c = ⊥`. Evaluating the universal Baker–Campbell–Hausdorff element
`TauCeti.FreeLieAlgebra.bchElement c` of the free nilpotent Lie algebra on two generators at a
pair `(x, y)` gives the BCH product `TauCeti.bch x y`; it does not depend on the bound `c`. This
file proves that the BCH product is a group law on the underlying set of `L`, with identity `0`
and inverse `x ↦ -x`, and packages it as the group `TauCeti.BCHGroup L`, with the identity maps
`BCHGroup.exp : L ≃ BCHGroup L` and `BCHGroup.log` as exponential and logarithm. Lie
homomorphisms preserve the BCH product, so `BCHGroup` is a functor to groups.

Associativity is proved universally. For any Lie algebra `L` over `ℚ`, the image of the BCH
product of two classes of `L ⧸ lowerCentralSeries c` in the truncated enveloping algebra
`U(L) ⧸ U⁺(L) ^ (c + 1)` has as exponential the product of their exponentials
(`TauCeti.exp_lowerCentralQuotientι_bch`). On the free nilpotent Lie algebra on three generators
this map is injective, which gives associativity there; evaluating the three generators at
`x`, `y` and `z` gives associativity everywhere. Through degree two, the BCH elements give
`bch x y = x + y + ½ ⁅x, y⁆` when `⁅x, y⁆` commutes with `x` and `y`, and in particular
`bch x y = x + y` when `⁅x, y⁆ = 0`; these give the identity and inverse laws, the powers
`exp (n • x) = exp x ^ n`, and the commutator formula `exp x * exp y = exp y * exp ⁅x, y⁆ * exp x`.

## Main definitions

* `TauCeti.bch`: the Baker–Campbell–Hausdorff product of a nilpotent Lie algebra over `ℚ`.
* `TauCeti.BCHGroup`: the group structure it defines on the underlying set, with
  `TauCeti.BCHGroup.exp` and `TauCeti.BCHGroup.log`.
* `TauCeti.BCHGroup.map`: the group homomorphism induced by a Lie homomorphism.

## Main results

* `TauCeti.bch_eq_liftQ`: the BCH product is the evaluation of the BCH element of any class
  whose lower central term is killed by the evaluation.
* `LieHom.map_bch`: Lie homomorphisms preserve the BCH product.
* `TauCeti.exp_lowerCentralQuotientι_bch`: in a truncated enveloping algebra, the BCH product
  exponentiates to the product of exponentials.
* `TauCeti.bch_assoc`: the BCH product is associative.
* `TauCeti.bch_eq_of_lie_lie_eq_zero` and `TauCeti.bch_eq_add_of_lie_eq_zero`: the BCH product
  of elements whose bracket commutes with both, and of commuting elements.
* `TauCeti.BCHGroup.exp_mul_exp_eq_exp_mul_exp_lie_mul_exp`: the commutator formula.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1–3*, Springer (1989), Chapter II, §6,
  no. 5, for the group defined by a nilpotent Lie algebra.
* C. Reutenauer, *Free Lie Algebras*, Oxford University Press (1993), §3.1.
-/

public section

namespace TauCeti

section BCH

-- The canonical map into an enveloping algebra is a Lie homomorphism into its commutator Lie
-- algebra.
attribute [local instance 100] LieRing.ofAssociativeRing

local notation "𝔣" => _root_.FreeLieAlgebra ℚ (Fin 2)
local notation "lcs" => LieModule.lowerCentralSeries ℚ

variable {L L' : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing L'] [LieAlgebra ℚ L']

section Product

/-- Changing the class bound does not change the evaluation of the BCH element. -/
private theorem liftQ_bchElement_of_le (φ : 𝔣 →ₗ⁅ℚ⁆ L) {c d : ℕ} (hcd : c ≤ d)
    (hc : lcs 𝔣 𝔣 c ≤ φ.ker) (hd : lcs 𝔣 𝔣 d ≤ φ.ker) :
    LieIdeal.liftQ _ φ hd (FreeLieAlgebra.bchElement d) =
      LieIdeal.liftQ _ φ hc (FreeLieAlgebra.bchElement c) := by
  rw [← FreeLieAlgebra.factor_bchElement hcd, ← LieHom.comp_apply]
  congr 1
  exact LieIdeal.lieHom_qext _ fun z => by simp [LieIdeal.mkQ_apply]

variable [LieRing.IsNilpotent L]

/-- The **Baker–Campbell–Hausdorff product** in a nilpotent Lie algebra over `ℚ`: the evaluation
of the BCH element `bchElement c` at `(x, y)`, for any `c` bounding the nilpotency class. -/
noncomputable def bch (x y : L) : L :=
  LieIdeal.liftQ _ (_root_.FreeLieAlgebra.lift ℚ ![x, y])
    (LieHom.lowerCentralSeries_le_ker _ (LieModule.IsNilpotent.nilpotent ℚ L L).choose_spec)
    (FreeLieAlgebra.bchElement (LieModule.IsNilpotent.nilpotent ℚ L L).choose)

/-- The BCH product is the evaluation at `(x, y)` of the BCH element of any class `c` whose
`c`-th lower central term is killed by the evaluation map. -/
theorem bch_eq_liftQ {c : ℕ} (x y : L)
    (h : lcs 𝔣 𝔣 c ≤ (_root_.FreeLieAlgebra.lift ℚ ![x, y]).ker) :
    bch x y = LieIdeal.liftQ _ _ h (FreeLieAlgebra.bchElement c) := by
  set c₀ := (LieModule.IsNilpotent.nilpotent ℚ L L).choose
  have h₀ := LieHom.lowerCentralSeries_le_ker (_root_.FreeLieAlgebra.lift ℚ ![x, y])
    (LieModule.IsNilpotent.nilpotent ℚ L L).choose_spec
  have hmax : lcs 𝔣 𝔣 (max c c₀) ≤ (_root_.FreeLieAlgebra.lift ℚ ![x, y]).ker :=
    (LieModule.antitone_lowerCentralSeries ℚ 𝔣 𝔣 (le_max_left c c₀)).trans h
  rw [bch, ← liftQ_bchElement_of_le _ (le_max_right c c₀) h₀ hmax,
    liftQ_bchElement_of_le _ (le_max_left c c₀) h hmax]

/-- Lie homomorphisms between nilpotent Lie algebras preserve the BCH product. -/
theorem _root_.LieHom.map_bch [LieRing.IsNilpotent L'] (f : L →ₗ⁅ℚ⁆ L') (x y : L) :
    f (bch x y) = bch (f x) (f y) := by
  obtain ⟨c, hc⟩ := LieModule.IsNilpotent.nilpotent ℚ L L
  have hφ : _root_.FreeLieAlgebra.lift ℚ ![f x, f y] =
      f.comp (_root_.FreeLieAlgebra.lift ℚ ![x, y]) :=
    (FreeLieAlgebra.comp_lift_pair f x y).symm
  have h := LieHom.lowerCentralSeries_le_ker (_root_.FreeLieAlgebra.lift ℚ ![x, y]) hc
  have h' : lcs 𝔣 𝔣 c ≤ (_root_.FreeLieAlgebra.lift ℚ ![f x, f y]).ker := by
    rw [hφ, LieHom.ker_comp]
    exact h.trans (LieHom.ker_le_comap _ _)
  obtain ⟨b, hb⟩ := LieIdeal.surjective_mkQ _ (FreeLieAlgebra.bchElement c)
  rw [bch_eq_liftQ x y h, bch_eq_liftQ _ _ h', ← hb, LieIdeal.mkQ_apply, LieIdeal.liftQ_apply,
    LieIdeal.liftQ_apply, hφ, LieHom.comp_apply]

end Product

section Enveloping

variable (L) in
/-- **The BCH product exponentiates to the product.** For a Lie algebra `L` over `ℚ`, the
exponential of the image of the BCH product of two classes in `L ⧸ lowerCentralSeries c` in the
truncated enveloping algebra `U(L) ⧸ U⁺(L) ^ (c + 1)` is the product of their exponentials. -/
theorem exp_lowerCentralQuotientι_bch (c : ℕ) (x y : L ⧸ LieModule.lowerCentralSeries ℚ L L c) :
    IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ L c (bch x y)) =
      IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ L c x) *
        IsNilpotent.exp (UniversalEnvelopingAlgebra.lowerCentralQuotientι ℚ L c y) := by
  obtain ⟨x, rfl⟩ := LieIdeal.surjective_mkQ _ x
  obtain ⟨y, rfl⟩ := LieIdeal.surjective_mkQ _ y
  obtain ⟨b, hb⟩ := LieIdeal.surjective_mkQ _ (FreeLieAlgebra.bchElement c)
  set f := _root_.FreeLieAlgebra.lift ℚ ![x, y]
  have hf : _root_.FreeLieAlgebra.lift ℚ
      ![(LieIdeal.mkQ (lcs L L c)) x, (LieIdeal.mkQ (lcs L L c)) y] =
      (LieIdeal.mkQ (lcs L L c)).comp f :=
    (FreeLieAlgebra.comp_lift_pair _ x y).symm
  have key := FreeLieAlgebra.exp_lowerCentralQuotientι_bchElement c
  rw [← hb, LieIdeal.mkQ_apply, UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk] at key
  rw [bch_eq_liftQ _ _ (LieHom.lowerCentralSeries_le_ker _
      (lowerCentralSeries_quotient_lowerCentralSeries_eq_bot ℚ L c)), hf, ← hb]
  simp only [LieIdeal.mkQ_apply, LieIdeal.liftQ_apply, LieHom.comp_apply,
    UniversalEnvelopingAlgebra.lowerCentralQuotientι_mk]
  -- Transport `key` along the map of truncated enveloping algebras induced by `f`.
  rw [← UniversalEnvelopingAlgebra.quotientMapₐ_mk_ι ℚ f (c + 1),
    ← (UniversalEnvelopingAlgebra.isNilpotent_mk_ι ℚ 𝔣 c b).map_exp, key, map_mul,
    (UniversalEnvelopingAlgebra.isNilpotent_mk_ι ℚ 𝔣 c _).map_exp,
    (UniversalEnvelopingAlgebra.isNilpotent_mk_ι ℚ 𝔣 c _).map_exp]
  simp [f]

end Enveloping

section Laws

local notation "𝔣₃" => _root_.FreeLieAlgebra ℚ (Fin 3)

/-- The BCH product is associative on a free nilpotent Lie algebra on three generators, where the
truncated enveloping algebra detects Lie elements. -/
private theorem bch_assoc_free (c : ℕ) (x y z : 𝔣₃ ⧸ LieModule.lowerCentralSeries ℚ 𝔣₃ 𝔣₃ c) :
    bch (bch x y) z = bch x (bch y z) := by
  have hnil := UniversalEnvelopingAlgebra.isNilpotent_lowerCentralQuotientι ℚ 𝔣₃ c
  apply FreeLieAlgebra.lowerCentralQuotientι_injective ℚ (Fin 3)
    (UniversalEnvelopingAlgebra.ι_injective ℚ 𝔣₃) c
  rw [← IsNilpotent.log_exp (hnil (bch (bch x y) z)),
    ← IsNilpotent.log_exp (hnil (bch x (bch y z))),
    exp_lowerCentralQuotientι_bch, exp_lowerCentralQuotientι_bch, exp_lowerCentralQuotientι_bch,
    exp_lowerCentralQuotientι_bch, mul_assoc]

/-- **Associativity of the BCH product.** -/
theorem bch_assoc [LieRing.IsNilpotent L] (x y z : L) : bch (bch x y) z = bch x (bch y z) := by
  obtain ⟨c, hc⟩ := LieModule.IsNilpotent.nilpotent ℚ L L
  -- Evaluate the associativity law of the free nilpotent Lie algebra on three generators.
  let g := LieIdeal.liftQ _ (_root_.FreeLieAlgebra.lift ℚ ![x, y, z])
    (LieHom.lowerCentralSeries_le_ker _ hc)
  have hx : g (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0)) = x := by simp [g]
  have hy : g (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1)) = y := by simp [g]
  have hz : g (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 2)) = z := by simp [g]
  rw [← hx, ← hy, ← hz, ← g.map_bch, ← g.map_bch, ← g.map_bch, ← g.map_bch,
    bch_assoc_free]

/-- The BCH product of `x` and `y` is `x + y + ½ ⁅x, y⁆` when `⁅x, y⁆` commutes with `x` and
`y`. -/
theorem bch_eq_of_lie_lie_eq_zero [LieRing.IsNilpotent L] {x y : L} (hx : ⁅x, ⁅x, y⁆⁆ = 0)
    (hy : ⁅y, ⁅x, y⁆⁆ = 0) : bch x y = x + y + (1 / 2 : ℚ) • ⁅x, y⁆ := by
  rw [bch_eq_liftQ x y (FreeLieAlgebra.lowerCentralSeries_two_le_ker_lift hx hy),
    FreeLieAlgebra.bchElement_two, LieIdeal.liftQ_apply]
  simp

/-- The BCH product of two commuting elements is their sum. -/
theorem bch_eq_add_of_lie_eq_zero [LieRing.IsNilpotent L] {x y : L} (h : ⁅x, y⁆ = 0) :
    bch x y = x + y := by
  rw [bch_eq_of_lie_lie_eq_zero (by rw [h, lie_zero]) (by rw [h, lie_zero]), h, smul_zero,
    add_zero]

/-- `0` is a right identity for the BCH product. -/
@[simp]
theorem bch_zero [LieRing.IsNilpotent L] (x : L) : bch x 0 = x := by
  rw [bch_eq_add_of_lie_eq_zero (lie_zero x), add_zero]

/-- `0` is a left identity for the BCH product. -/
@[simp]
theorem zero_bch [LieRing.IsNilpotent L] (x : L) : bch 0 x = x := by
  rw [bch_eq_add_of_lie_eq_zero (zero_lie x), zero_add]

end Laws

end BCH

/-- The **Baker–Campbell–Hausdorff group** of a Lie algebra `L` over `ℚ`: a type synonym for `L`
which, when `L` is nilpotent, is a group under the BCH product `TauCeti.bch`, with identity `0`
and inverse `-x`. The identity maps `BCHGroup.exp : L ≃ BCHGroup L` and
`BCHGroup.log : BCHGroup L ≃ L` are the exponential and the logarithm. -/
@[expose] def BCHGroup (L : Type*) : Type _ := L

namespace BCHGroup

variable {L : Type*}

/-- The exponential `L ≃ BCHGroup L`, the identity on the underlying set. -/
def exp : L ≃ BCHGroup L := Equiv.refl L

/-- The logarithm `BCHGroup L ≃ L`, the identity on the underlying set. -/
def log : BCHGroup L ≃ L := Equiv.refl L

@[simp]
theorem log_exp (x : L) : log (exp x) = x := (rfl)

@[simp]
theorem exp_log (a : BCHGroup L) : exp (log a) = a := (rfl)

@[simp]
theorem exp_symm : (exp : L ≃ BCHGroup L).symm = log := (rfl)

@[simp]
theorem log_symm : (log : BCHGroup L ≃ L).symm = exp := (rfl)

section Ring

variable [LieRing L]

instance : One (BCHGroup L) := ⟨exp 0⟩

instance : Inv (BCHGroup L) := ⟨fun a => exp (-log a)⟩

@[simp]
theorem log_one : log (1 : BCHGroup L) = 0 := (rfl)

@[simp]
theorem log_inv (a : BCHGroup L) : log a⁻¹ = -log a := (rfl)

/-- The identity of the BCH group is the exponential of `0`. -/
@[simp]
theorem exp_zero : exp (0 : L) = 1 :=
  log.injective (by simp)

/-- The inverse in the BCH group is the exponential of the negative. -/
@[simp]
theorem exp_neg (x : L) : exp (-x) = (exp x)⁻¹ :=
  log.injective (by simp)

end Ring

variable [LieRing L] [LieAlgebra ℚ L] [LieRing.IsNilpotent L]
  {L' : Type*} [LieRing L'] [LieAlgebra ℚ L']

noncomputable instance : Mul (BCHGroup L) := ⟨fun a b => exp (bch (log a) (log b))⟩

/-- The logarithm of a product is the BCH product of the logarithms. -/
@[simp]
theorem log_mul (a b : BCHGroup L) : log (a * b) = bch (log a) (log b) := (rfl)

noncomputable instance : Group (BCHGroup L) where
  mul_assoc a b c := log.injective (by simp [bch_assoc])
  one_mul a := log.injective (by simp)
  mul_one a := log.injective (by simp)
  inv_mul_cancel a := log.injective <| by
    rw [log_mul, log_inv, log_one, bch_eq_add_of_lie_eq_zero (by rw [neg_lie, lie_self, neg_zero]),
      neg_add_cancel]

/-- The product of two exponentials is the exponential of their BCH product. -/
theorem exp_mul_exp (x y : L) : exp x * exp y = exp (bch x y) :=
  log.injective (by simp)

/-- Exponentials of commuting elements multiply additively. -/
theorem exp_add_of_lie_eq_zero {x y : L} (h : ⁅x, y⁆ = 0) : exp (x + y) = exp x * exp y := by
  rw [exp_mul_exp, bch_eq_add_of_lie_eq_zero h]

/-- The exponential of `n • x` is the `n`-th power of `exp x`. -/
@[simp]
theorem exp_nsmul (n : ℕ) (x : L) : exp (n • x) = exp x ^ n := by
  induction n with
  | zero => rw [zero_smul, exp_zero, pow_zero]
  | succ n ih =>
    rw [succ_nsmul, exp_add_of_lie_eq_zero (by rw [nsmul_lie, lie_self, smul_zero]), ih, pow_succ]

/-- The exponential of `n • x` is the `n`-th power of `exp x`, for an integer `n`. -/
@[simp]
theorem exp_zsmul (n : ℤ) (x : L) : exp (n • x) = exp x ^ n := by
  cases n with
  | ofNat n => rw [Int.ofNat_eq_natCast, natCast_zsmul, exp_nsmul, zpow_natCast]
  | negSucc n => rw [negSucc_zsmul, exp_neg, exp_nsmul, zpow_negSucc]

/-- The logarithm of a power is the corresponding multiple of the logarithm. -/
@[simp]
theorem log_pow (a : BCHGroup L) (n : ℕ) : log (a ^ n) = n • log a := by
  rw [← exp_log a, ← exp_nsmul, log_exp, log_exp]

/-- The logarithm of an integer power is the corresponding multiple of the logarithm. -/
@[simp]
theorem log_zpow (a : BCHGroup L) (n : ℤ) : log (a ^ n) = n • log a := by
  rw [← exp_log a, ← exp_zsmul, log_exp, log_exp]

/-- The group homomorphism `BCHGroup L →* BCHGroup L'` induced by a Lie algebra homomorphism of
nilpotent Lie algebras: the same map on the underlying sets. -/
noncomputable def map [LieRing.IsNilpotent L'] (f : L →ₗ⁅ℚ⁆ L') : BCHGroup L →* BCHGroup L' where
  toFun a := exp (f (log a))
  map_one' := congrArg exp f.map_zero
  map_mul' a b := congrArg exp (f.map_bch (log a) (log b))

@[simp]
theorem map_exp [LieRing.IsNilpotent L'] (f : L →ₗ⁅ℚ⁆ L') (x : L) :
    map f (exp x) = exp (f x) := (rfl)

@[simp]
theorem log_map [LieRing.IsNilpotent L'] (f : L →ₗ⁅ℚ⁆ L') (a : BCHGroup L) :
    log (map f a) = f (log a) := (rfl)

/-- `BCHGroup.map` sends the identity to the identity. -/
@[simp]
theorem map_id : map (LieHom.id : L →ₗ⁅ℚ⁆ L) = MonoidHom.id (BCHGroup L) := (rfl)

/-- `BCHGroup.map` respects composition of Lie homomorphisms. -/
theorem map_comp {L'' : Type*} [LieRing L''] [LieAlgebra ℚ L''] [LieRing.IsNilpotent L']
    [LieRing.IsNilpotent L''] (g : L' →ₗ⁅ℚ⁆ L'') (f : L →ₗ⁅ℚ⁆ L') :
    map (g.comp f) = (map g).comp (map f) := (rfl)

/-- **The commutator formula.** If `z = ⁅x, y⁆` commutes with `x` and `y`, then
`exp x * exp y = exp y * exp z * exp x`. -/
theorem exp_mul_exp_eq_exp_mul_exp_lie_mul_exp {x y : L} (hx : ⁅x, ⁅x, y⁆⁆ = 0)
    (hy : ⁅y, ⁅x, y⁆⁆ = 0) : exp x * exp y = exp y * exp ⁅x, y⁆ * exp x := by
  have hyx : ⁅y + ⁅x, y⁆, x⁆ = -⁅x, y⁆ := by
    rw [add_lie, ← lie_skew y x, ← lie_skew ⁅x, y⁆ x, hx, neg_zero, add_zero]
  -- The bracket `⁅y + ⁅x, y⁆, x⁆ = -⁅x, y⁆` commutes with `y + ⁅x, y⁆` and with `x`.
  have h₁ : ⁅y + ⁅x, y⁆, ⁅y + ⁅x, y⁆, x⁆⁆ = 0 := by
    rw [hyx, lie_neg, add_lie, hy, lie_self, add_zero, neg_zero]
  have h₂ : ⁅x, ⁅y + ⁅x, y⁆, x⁆⁆ = 0 := by rw [hyx, lie_neg, hx, neg_zero]
  rw [← exp_add_of_lie_eq_zero hy, exp_mul_exp, exp_mul_exp, bch_eq_of_lie_lie_eq_zero hx hy,
    bch_eq_of_lie_lie_eq_zero h₁ h₂, hyx]
  congr 1
  module

end BCHGroup

end TauCeti
