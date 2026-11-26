/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import TauCeti.Algebra.Lie.Free.BCH
public import TauCeti.Algebra.Lie.LowerCentralSeries
public import TauCeti.Algebra.Lie.UniversalEnveloping.Augmentation.Map

/-!
# The Baker–Campbell–Hausdorff group of a nilpotent Lie algebra

Let `L` be a Lie algebra over `ℚ` whose `c`-th lower central term vanishes, that is, of nilpotency
class at most `c`. Evaluating the universal Baker–Campbell–Hausdorff element `bchElement c` of the
free nilpotent Lie algebra on two generators at a pair `(x, y)` of elements of `L`, through the
Lie homomorphism `FreeLieAlgebra.lift ℚ ![x, y]`, gives the Baker–Campbell–Hausdorff product
`TauCeti.LieAlgebra.bch c hc x y`. It does not depend on the class bound `c`, and it is natural
in Lie homomorphisms. This product makes `L` into a group, `TauCeti.BCHGroup L`, with identity
`0` and inverse `x ↦ -x`, in which the exponential `BCHGroup.exp : L → BCHGroup L` and logarithm
`BCHGroup.log` are the identity on underlying sets. Commuting elements multiply by addition, so
`exp (n • x) = exp x ^ n` for every integer `n`, and a Lie homomorphism induces a group
homomorphism `BCHGroup.map`. A Lie subalgebra is a subgroup, a Lie ideal is a normal subgroup, and
the quotient group is the group of the quotient Lie algebra.

Associativity is the substantial point. In the enveloping algebra of the free Lie algebra `F` on
any set, truncated at the `(c + 1)`-st power of the augmentation ideal, the image of
`bch c x y` in the free nilpotent quotient of class `c` is `log (exp x * exp y)`
(`TauCeti.LieAlgebra.exp_lowerCentralQuotientι_bch`). This follows from the defining property of
`bchElement c` by transporting it along the enveloping map of `FreeLieAlgebra.lift ℚ ![x, y]`.
Since the free nilpotent quotient embeds in the truncated enveloping algebra, associativity of the
product of exponentials gives associativity of `bch` in the free nilpotent Lie algebra on three
generators, and naturality transports it to every Lie algebra of class at most `c`.

The construction is stated for Lie algebras over `ℚ`: the product only involves rational scalars.
The comparison with the scalar restriction to `ℚ` of an `R`-Lie algebra, for a commutative
`ℚ`-algebra `R`, is not provided here.

## Main definitions

* `TauCeti.LieAlgebra.bch`: the Baker–Campbell–Hausdorff product in a Lie algebra of class at
  most `c`.
* `TauCeti.BCHGroup`: the group of a nilpotent Lie algebra under the Baker–Campbell–Hausdorff
  product, with `BCHGroup.exp` and `BCHGroup.log`.
* `TauCeti.BCHGroup.map`: the group homomorphism induced by a Lie homomorphism.
* `LieSubalgebra.bchSubgroup`: the subgroup of exponentials of a Lie subalgebra; it is normal for
  a Lie ideal (`LieIdeal.bchSubgroup_normal`).
* `LieIdeal.bchQuotientEquiv`: the quotient by the subgroup of a Lie ideal is the group of the
  quotient Lie algebra.

## Main results

* `TauCeti.LieAlgebra.bch_eq_bch`: the product does not depend on the class bound.
* `TauCeti.LieAlgebra.map_bch`: Lie homomorphisms preserve the product.
* `TauCeti.LieAlgebra.bch_eq_add_of_lie_eq_zero`: commuting elements multiply by addition.
* `TauCeti.LieAlgebra.exp_lowerCentralQuotientι_bch`: in a free nilpotent Lie algebra the
  product is the logarithm of the product of exponentials in the truncated enveloping algebra.
* `TauCeti.LieAlgebra.bch_assoc`: the product is associative.
* `TauCeti.BCHGroup.exp_mul_exp`: `exp x * exp y = exp (bch c hc x y)` for every class bound.
* `TauCeti.BCHGroup.exp_zsmul`: `exp (n • x) = exp x ^ n`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1–3*, Springer (1989), Chapter II, §6.
* C. Reutenauer, *Free Lie Algebras*, Oxford University Press (1993), §3.1.
-/

public section

namespace TauCeti

open LieModule (lowerCentralSeries)
open _root_.TauCeti.UniversalEnvelopingAlgebra

local notation "𝔣" => _root_.FreeLieAlgebra ℚ (Fin 2)

namespace LieAlgebra

variable {L L' : Type*} [LieRing L] [LieAlgebra ℚ L] [LieRing L'] [LieAlgebra ℚ L']

/-- Lie homomorphisms commute with evaluation at a pair: `f` applied to the value of `r` at
`(x, y)` is the value of `r` at `(f x, f y)`. -/
private theorem map_lift_pair (f : L →ₗ⁅ℚ⁆ L') (x y : L) (r : 𝔣) :
    f (_root_.FreeLieAlgebra.lift ℚ ![x, y] r) = _root_.FreeLieAlgebra.lift ℚ ![f x, f y] r := by
  rw [_root_.FreeLieAlgebra.comp_lift_apply]
  congr 2
  ext i
  fin_cases i <;> rfl

/-- The **Baker–Campbell–Hausdorff product** of `x` and `y` in a Lie algebra `L` over `ℚ` of
nilpotency class at most `c`: the value at `(x, y)` of the universal element
`TauCeti.FreeLieAlgebra.bchElement c`, through the Lie homomorphism
`FreeLieAlgebra.lift ℚ ![x, y]`, which factors through the free nilpotent quotient of class `c`
because `lowerCentralSeries ℚ L L c = ⊥`. -/
noncomputable def bch (c : ℕ) (hc : lowerCentralSeries ℚ L L c = ⊥) (x y : L) : L :=
  LieIdeal.liftQ (lowerCentralSeries ℚ 𝔣 𝔣 c) (_root_.FreeLieAlgebra.lift ℚ ![x, y])
    ((_root_.FreeLieAlgebra.lift ℚ ![x, y]).lowerCentralSeries_le_ker hc)
    (FreeLieAlgebra.bchElement c)

/-- The Baker–Campbell–Hausdorff product is the value at `(x, y)` of any representative of the
universal element. -/
theorem bch_eq_lift {c : ℕ} (hc : lowerCentralSeries ℚ L L c = ⊥) {r : 𝔣}
    (hr : LieSubmodule.Quotient.mk r = FreeLieAlgebra.bchElement c) (x y : L) :
    bch c hc x y = _root_.FreeLieAlgebra.lift ℚ ![x, y] r := by
  rw [bch, ← hr, LieIdeal.liftQ_apply]

/-- Lie homomorphisms preserve the Baker–Campbell–Hausdorff product. -/
theorem map_bch {c : ℕ} (f : L →ₗ⁅ℚ⁆ L') (hc : lowerCentralSeries ℚ L L c = ⊥)
    (hc' : lowerCentralSeries ℚ L' L' c = ⊥) (x y : L) :
    f (bch c hc x y) = bch c hc' (f x) (f y) := by
  obtain ⟨r, hr⟩ : ∃ r : 𝔣, LieSubmodule.Quotient.mk r = FreeLieAlgebra.bchElement c := by
    simpa only [LieIdeal.mkQ_apply] using LieIdeal.surjective_mkQ _ (FreeLieAlgebra.bchElement c)
  rw [bch_eq_lift hc hr, bch_eq_lift hc' hr, map_lift_pair]

/-- The Baker–Campbell–Hausdorff product does not change when the class bound is raised. -/
private theorem bch_eq_bch_of_le {c d : ℕ} (h : c ≤ d) (hc : lowerCentralSeries ℚ L L c = ⊥)
    (hd : lowerCentralSeries ℚ L L d = ⊥) (x y : L) : bch c hc x y = bch d hd x y := by
  obtain ⟨r, hr⟩ := LieIdeal.surjective_mkQ _ (FreeLieAlgebra.bchElement d)
  rw [LieIdeal.mkQ_apply] at hr
  have hr' : LieSubmodule.Quotient.mk r = FreeLieAlgebra.bchElement c := by
    rw [← FreeLieAlgebra.factor_bchElement h, ← hr, LieIdeal.factor_apply]
  rw [bch_eq_lift hc hr', bch_eq_lift hd hr]

/-- The Baker–Campbell–Hausdorff product does not depend on the bound on the nilpotency
class. -/
theorem bch_eq_bch {c d : ℕ} (hc : lowerCentralSeries ℚ L L c = ⊥)
    (hd : lowerCentralSeries ℚ L L d = ⊥) (x y : L) : bch c hc x y = bch d hd x y := by
  rcases le_total c d with h | h
  · exact bch_eq_bch_of_le h hc hd x y
  · exact (bch_eq_bch_of_le h hd hc x y).symm

/-- In an abelian Lie algebra, the Baker–Campbell–Hausdorff product is addition. -/
theorem bch_one (hc : lowerCentralSeries ℚ L L 1 = ⊥) (x y : L) : bch 1 hc x y = x + y := by
  rw [bch_eq_lift hc FreeLieAlgebra.bchElement_one.symm]
  simp

/-- The Baker–Campbell–Hausdorff product of commuting elements is their sum. -/
theorem bch_eq_add_of_lie_eq_zero {c : ℕ} (hc : lowerCentralSeries ℚ L L c = ⊥) {x y : L}
    (h : ⁅x, y⁆ = 0) : bch c hc x y = x + y := by
  rcases c with _ | c
  · -- Class zero: `L` is trivial.
    have h0 : ∀ z : L, z = 0 := fun z => by
      have hz : z ∈ lowerCentralSeries ℚ L L 0 := LieSubmodule.mem_top z
      rwa [hc, LieSubmodule.mem_bot] at hz
    rw [h0 (bch 0 hc x y), h0 (x + y)]
  -- The Lie subalgebra generated by `x` and `y` is abelian, so there the product is addition.
  let K := LieSubalgebra.lieSpan ℚ L {x, y}
  have hK : IsLieAbelian K := by
    rw [LieSubalgebra.isLieAbelian_lieSpan_iff]
    rintro a (rfl | rfl) b (rfl | rfl)
    exacts [lie_self _, h, by rw [← lie_skew, h, neg_zero], lie_self _]
  have hK1 : lowerCentralSeries ℚ K K 1 = ⊥ :=
    (LieModule.trivial_iff_lower_central_eq_bot ℚ K K).mp hK
  have hKc : lowerCentralSeries ℚ K K (c + 1) = ⊥ :=
    LieModule.lowerCentralSeries_eq_bot_of_le (by omega) hK1
  have hmap := map_bch K.incl hKc hc ⟨x, LieSubalgebra.subset_lieSpan (by simp)⟩
    ⟨y, LieSubalgebra.subset_lieSpan (by simp)⟩
  rw [bch_eq_bch hKc hK1, bch_one] at hmap
  simpa using hmap.symm

/-- A Lie subalgebra is closed under the Baker–Campbell–Hausdorff product. -/
theorem bch_mem {c : ℕ} (hc : lowerCentralSeries ℚ L L c = ⊥) {K : LieSubalgebra ℚ L} {x y : L}
    (hx : x ∈ K) (hy : y ∈ K) : bch c hc x y ∈ K := by
  have hK : lowerCentralSeries ℚ K K c = ⊥ := le_bot_iff.mp
    ((K.incl.lowerCentralSeries_le_ker hc).trans ((LieHom.ker_eq_bot K.incl).mpr
      Subtype.val_injective).le)
  have h := (bch c hK ⟨x, hx⟩ ⟨y, hy⟩).property
  rwa [← LieSubalgebra.coe_incl, map_bch K.incl hK hc] at h

section Free

variable (S : Type*) (c : ℕ)

local notation "F" => _root_.FreeLieAlgebra ℚ S
local notation "J" =>
  HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ (_root_.UniversalEnvelopingAlgebra ℚ F))
local notation "ι" => _root_.UniversalEnvelopingAlgebra.ι ℚ

/-- In the free nilpotent Lie algebra `F ⧸ lowerCentralSeries c` on any set, the image of the
Baker–Campbell–Hausdorff product in the truncated enveloping algebra `U(F) ⧸ (U⁺) ^ (c + 1)` is
the logarithm of the product of the exponentials of the images of its factors. -/
theorem exp_lowerCentralQuotientι_bch (u v : F ⧸ lowerCentralSeries ℚ F F c) :
    IsNilpotent.exp (lowerCentralQuotientι ℚ F c
        (bch c (lowerCentralSeries_quotient_lowerCentralSeries_eq_bot ℚ F c) u v)) =
      IsNilpotent.exp (lowerCentralQuotientι ℚ F c u) *
        IsNilpotent.exp (lowerCentralQuotientι ℚ F c v) := by
  obtain ⟨x, rfl⟩ := LieIdeal.surjective_mkQ _ u
  obtain ⟨y, rfl⟩ := LieIdeal.surjective_mkQ _ v
  obtain ⟨r, hr⟩ : ∃ r : 𝔣, LieSubmodule.Quotient.mk r = FreeLieAlgebra.bchElement c := by
    simpa only [LieIdeal.mkQ_apply] using LieIdeal.surjective_mkQ _ (FreeLieAlgebra.bchElement c)
  -- The product is the class of `φ r` for `φ = lift ![x, y]`, and `x = φ X`, `y = φ Y`.
  have hφ : bch c (lowerCentralSeries_quotient_lowerCentralSeries_eq_bot ℚ F c)
      (LieSubmodule.Quotient.mk x) (LieSubmodule.Quotient.mk y) =
      LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.lift ℚ ![x, y] r) := by
    rw [bch_eq_lift _ hr]
    simpa only [LieIdeal.mkQ_apply] using (map_lift_pair (LieIdeal.mkQ _) x y r).symm
  -- Transport the defining identity of `bchElement c` along the enveloping map of `φ`.
  have hq : ∀ z : 𝔣, IsNilpotent.exp
      (Ideal.Quotient.mk (J ^ (c + 1)) (ι (_root_.FreeLieAlgebra.lift ℚ ![x, y] z))) =
      Ideal.quotientMapₐ (J ^ (c + 1)) (map ℚ (_root_.FreeLieAlgebra.lift ℚ ![x, y]))
        (augmentation_pow_le_comap_map ℚ _ (c + 1))
        (IsNilpotent.exp (Ideal.Quotient.mk _ (ι z))) := fun z => by
    rw [(isNilpotent_mk_ι ℚ 𝔣 c z).map_exp, Ideal.quotient_map_mkₐ, Ideal.Quotient.mkₐ_eq_mk,
      map_ι]
  -- The factors `x = φ X` and `y = φ Y` are the images of the generators.
  have hx := hq (_root_.FreeLieAlgebra.of ℚ 0)
  have hy := hq (_root_.FreeLieAlgebra.of ℚ 1)
  rw [_root_.FreeLieAlgebra.lift_of_apply, Matrix.cons_val_zero] at hx
  rw [_root_.FreeLieAlgebra.lift_of_apply, Matrix.cons_val_one, Matrix.cons_val_zero] at hy
  -- The defining identity of `bchElement c`, read off on its representative `r`.
  have hr' : IsNilpotent.exp (Ideal.Quotient.mk
      (HopfIdeal.toIdeal (HopfIdeal.augmentation ℚ (_root_.UniversalEnvelopingAlgebra ℚ 𝔣)) ^
        (c + 1)) (ι r)) =
      IsNilpotent.exp (Ideal.Quotient.mk _ (ι (_root_.FreeLieAlgebra.of ℚ (0 : Fin 2)))) *
        IsNilpotent.exp (Ideal.Quotient.mk _ (ι (_root_.FreeLieAlgebra.of ℚ (1 : Fin 2)))) := by
    rw [← lowerCentralQuotientι_mk, hr, FreeLieAlgebra.exp_lowerCentralQuotientι_bchElement]
  simp only [LieIdeal.mkQ_apply, hφ, lowerCentralQuotientι_mk]
  rw [hq, hr', map_mul, ← hx, ← hy]

/-- The Baker–Campbell–Hausdorff product is associative in every free nilpotent Lie algebra. -/
private theorem bch_assoc_free (u v w : F ⧸ lowerCentralSeries ℚ F F c) :
    let h := lowerCentralSeries_quotient_lowerCentralSeries_eq_bot ℚ F c
    bch c h (bch c h u v) w = bch c h u (bch c h v w) := by
  intro h
  apply FreeLieAlgebra.lowerCentralQuotientι_injective ℚ S (ι_injective ℚ F) c
  rw [← IsNilpotent.log_exp (isNilpotent_lowerCentralQuotientι ℚ F c (bch c h (bch c h u v) w)),
    ← IsNilpotent.log_exp (isNilpotent_lowerCentralQuotientι ℚ F c (bch c h u (bch c h v w)))]
  simp only [exp_lowerCentralQuotientι_bch, mul_assoc]

end Free

/-- **Associativity of the Baker–Campbell–Hausdorff product.** -/
theorem bch_assoc {c : ℕ} (hc : lowerCentralSeries ℚ L L c = ⊥) (x y z : L) :
    bch c hc (bch c hc x y) z = bch c hc x (bch c hc y z) := by
  -- Evaluate associativity in the free nilpotent Lie algebra on three generators.
  let ψ := LieIdeal.liftQ (lowerCentralSeries ℚ (_root_.FreeLieAlgebra ℚ (Fin 3)) _ c)
    (_root_.FreeLieAlgebra.lift ℚ ![x, y, z])
    ((_root_.FreeLieAlgebra.lift ℚ ![x, y, z]).lowerCentralSeries_le_ker hc)
  have hψ : ∀ i : Fin 3, ψ (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ i)) =
      ![x, y, z] i := fun i => by simp [ψ]
  have key := congrArg ψ (bch_assoc_free (Fin 3) c
    (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 0))
    (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 1))
    (LieSubmodule.Quotient.mk (_root_.FreeLieAlgebra.of ℚ 2)))
  simp only [map_bch ψ (lowerCentralSeries_quotient_lowerCentralSeries_eq_bot ℚ _ c) hc,
    hψ] at key
  exact key

end LieAlgebra

/-- The **Baker–Campbell–Hausdorff group** of a Lie algebra `L` over `ℚ`: a copy of `L`, which is
a group under the Baker–Campbell–Hausdorff product when `L` is nilpotent. Its elements are the
exponentials `BCHGroup.exp x` of the elements `x` of `L`, and `BCHGroup.log` recovers `x`. -/
@[ext]
structure BCHGroup (L : Type*) where
  /-- The element of the Baker–Campbell–Hausdorff group with logarithm `x`. -/
  exp ::
  /-- The logarithm of an element of the Baker–Campbell–Hausdorff group: its underlying element
  of the Lie algebra. -/
  log : L

namespace BCHGroup

variable {L L' L'' : Type*}

@[simp]
theorem log_exp (x : L) : (exp x).log = x := rfl

@[simp]
theorem exp_log (g : BCHGroup L) : exp g.log = g := rfl

instance [Zero L] : One (BCHGroup L) := ⟨exp 0⟩

instance [Neg L] : Inv (BCHGroup L) := ⟨fun g => exp (-g.log)⟩

@[simp]
theorem exp_zero [Zero L] : exp (0 : L) = 1 := (rfl)

@[simp]
theorem log_one [Zero L] : (1 : BCHGroup L).log = 0 := (rfl)

@[simp]
theorem exp_neg [Neg L] (x : L) : exp (-x) = (exp x)⁻¹ := (rfl)

@[simp]
theorem log_inv [Neg L] (g : BCHGroup L) : g⁻¹.log = -g.log := (rfl)

variable [LieRing L] [LieAlgebra ℚ L] [LieRing.IsNilpotent L]

open LieModule (lowerCentralSeries_nilpotencyLength_eq_bot)
open _root_.TauCeti.LieAlgebra

/-- The product of the Baker–Campbell–Hausdorff group, computed with the nilpotency length of `L`
as class bound; `TauCeti.BCHGroup.exp_mul_exp` allows any other bound. -/
noncomputable instance : Mul (BCHGroup L) :=
  ⟨fun g h => exp (bch _ (lowerCentralSeries_nilpotencyLength_eq_bot ℚ L L) g.log h.log)⟩

/-- The product in the Baker–Campbell–Hausdorff group is the Baker–Campbell–Hausdorff product of
the logarithms, computed with any bound `c` on the nilpotency class. -/
theorem exp_mul_exp {c : ℕ} (hc : lowerCentralSeries ℚ L L c = ⊥) (x y : L) :
    exp x * exp y = exp (bch c hc x y) :=
  congrArg exp (bch_eq_bch _ hc x y)

/-- The logarithm of a product is the Baker–Campbell–Hausdorff product of the logarithms, computed
with any bound `c` on the nilpotency class. -/
theorem log_mul {c : ℕ} (hc : lowerCentralSeries ℚ L L c = ⊥) (g h : BCHGroup L) :
    (g * h).log = bch c hc g.log h.log := by
  rw [← exp_log g, ← exp_log h, exp_mul_exp hc, log_exp, log_exp, log_exp]

/-- The exponentials of commuting elements multiply by addition. -/
theorem exp_add_of_lie_eq_zero {x y : L} (h : ⁅x, y⁆ = 0) : exp (x + y) = exp x * exp y := by
  rw [exp_mul_exp (lowerCentralSeries_nilpotencyLength_eq_bot ℚ L L), bch_eq_add_of_lie_eq_zero _ h]

/-- A nilpotent Lie algebra over `ℚ` is a group under the Baker–Campbell–Hausdorff product, with
identity `exp 0`, inverse `exp x ↦ exp (-x)` and powers `exp x ^ n = exp (n • x)`. -/
noncomputable instance : Group (BCHGroup L) where
  mul_assoc g h k := by
    rw [← exp_log g, ← exp_log h, ← exp_log k]
    simp only [exp_mul_exp (lowerCentralSeries_nilpotencyLength_eq_bot ℚ L L), bch_assoc]
  one_mul g := by
    rw [← exp_log g, ← exp_zero, ← exp_add_of_lie_eq_zero (zero_lie _), zero_add]
  mul_one g := by
    rw [← exp_log g, ← exp_zero, ← exp_add_of_lie_eq_zero (lie_zero _), add_zero]
  inv_mul_cancel g := by
    rw [← exp_log g, ← exp_neg, ← exp_add_of_lie_eq_zero (by rw [neg_lie, lie_self, neg_zero]),
      neg_add_cancel, exp_zero]
  npow n g := exp (n • g.log)
  npow_zero g := congrArg exp (zero_smul ℕ g.log)
  npow_succ n g := (congrArg exp (succ_nsmul g.log n)).trans
    (exp_add_of_lie_eq_zero (by rw [nsmul_lie, lie_self, smul_zero]))
  zpow n g := exp (n • g.log)
  zpow_zero' g := congrArg exp (zero_smul ℤ g.log)
  zpow_succ' n g := (congrArg exp (by rw [Nat.cast_succ, add_zsmul, one_zsmul])).trans
    (exp_add_of_lie_eq_zero (by rw [zsmul_lie, lie_self, smul_zero]))
  zpow_neg' n g := congrArg exp <| by
    rw [negSucc_zsmul]
    exact congrArg Neg.neg (natCast_zsmul g.log n.succ).symm

@[simp]
theorem exp_nsmul (n : ℕ) (x : L) : exp (n • x) = exp x ^ n := (rfl)

@[simp]
theorem exp_zsmul (n : ℤ) (x : L) : exp (n • x) = exp x ^ n := (rfl)

@[simp]
theorem log_pow (n : ℕ) (g : BCHGroup L) : (g ^ n).log = n • g.log := (rfl)

@[simp]
theorem log_zpow (n : ℤ) (g : BCHGroup L) : (g ^ n).log = n • g.log := (rfl)

/-- The exponentials of commuting elements commute. -/
theorem commute_exp_of_lie_eq_zero {x y : L} (h : ⁅x, y⁆ = 0) : Commute (exp x) (exp y) := by
  rw [Commute, SemiconjBy, ← exp_add_of_lie_eq_zero h,
    ← exp_add_of_lie_eq_zero (by rw [← lie_skew, h, neg_zero]), add_comm]

variable [LieRing L'] [LieAlgebra ℚ L'] [LieRing.IsNilpotent L']
variable [LieRing L''] [LieAlgebra ℚ L''] [LieRing.IsNilpotent L'']

/-- The group homomorphism of Baker–Campbell–Hausdorff groups induced by a Lie homomorphism:
`exp x ↦ exp (f x)`. -/
noncomputable def map (f : L →ₗ⁅ℚ⁆ L') : BCHGroup L →* BCHGroup L' where
  toFun g := exp (f g.log)
  map_one' := by rw [log_one, map_zero, exp_zero]
  map_mul' g h := by
    -- Compute both products with a class bound common to `L` and `L'`.
    let c := max (LieModule.nilpotencyLength L L) (LieModule.nilpotencyLength L' L')
    have hc : lowerCentralSeries ℚ L L c = ⊥ := LieModule.lowerCentralSeries_eq_bot_of_le
      (le_max_left _ _) (lowerCentralSeries_nilpotencyLength_eq_bot ℚ L L)
    have hc' : lowerCentralSeries ℚ L' L' c = ⊥ := LieModule.lowerCentralSeries_eq_bot_of_le
      (le_max_right _ _) (lowerCentralSeries_nilpotencyLength_eq_bot ℚ L' L')
    rw [exp_mul_exp hc', ← map_bch f hc hc', log_mul hc]

@[simp]
theorem map_exp (f : L →ₗ⁅ℚ⁆ L') (x : L) : map f (exp x) = exp (f x) := (rfl)

@[simp]
theorem log_map (f : L →ₗ⁅ℚ⁆ L') (g : BCHGroup L) : (map f g).log = f g.log := (rfl)

@[simp]
theorem map_id : map (LieHom.id : L →ₗ⁅ℚ⁆ L) = MonoidHom.id (BCHGroup L) :=
  MonoidHom.ext fun _ => (rfl)

theorem map_comp (g : L' →ₗ⁅ℚ⁆ L'') (f : L →ₗ⁅ℚ⁆ L') : map (g.comp f) = (map g).comp (map f) :=
  MonoidHom.ext fun _ => (rfl)

/-- A surjective Lie homomorphism induces a surjective group homomorphism. -/
theorem map_surjective {f : L →ₗ⁅ℚ⁆ L'} (hf : Function.Surjective f) :
    Function.Surjective (map f) := fun g => by
  obtain ⟨x, hx⟩ := hf g.log
  exact ⟨exp x, by rw [map_exp, hx, exp_log]⟩

/-- The subgroup of the Baker–Campbell–Hausdorff group consisting of the exponentials of the
elements of a Lie subalgebra. -/
def _root_.LieSubalgebra.bchSubgroup (K : LieSubalgebra ℚ L) : Subgroup (BCHGroup L) where
  carrier := {g | g.log ∈ K}
  mul_mem' {g h} hg hh := by
    rw [Set.mem_ofPred_eq, log_mul (lowerCentralSeries_nilpotencyLength_eq_bot ℚ L L)]
    exact bch_mem _ hg hh
  one_mem' := K.zero_mem
  inv_mem' {_} hg := K.neg_mem hg

@[simp]
theorem _root_.LieSubalgebra.mem_bchSubgroup {K : LieSubalgebra ℚ L} {g : BCHGroup L} :
    g ∈ K.bchSubgroup ↔ g.log ∈ K :=
  Iff.rfl

/-- The subgroup of exponentials of a Lie ideal is the kernel of the group homomorphism induced by
the quotient map. -/
theorem ker_map_mkQ (I : LieIdeal ℚ L) :
    (map I.mkQ).ker = (I : LieSubalgebra ℚ L).bchSubgroup := by
  ext g
  rw [MonoidHom.mem_ker, LieSubalgebra.mem_bchSubgroup, ← exp_log g, map_exp, ← exp_zero,
    exp.injEq, LieIdeal.mkQ_apply, log_exp, LieSubmodule.Quotient.mk_eq_zero',
    LieIdeal.mem_toLieSubalgebra]

/-- The exponentials of a Lie ideal form a normal subgroup. -/
instance _root_.LieIdeal.bchSubgroup_normal (I : LieIdeal ℚ L) :
    (I : LieSubalgebra ℚ L).bchSubgroup.Normal :=
  ker_map_mkQ I ▸ MonoidHom.normal_ker _

/-- The quotient of the Baker–Campbell–Hausdorff group by the exponentials of a Lie ideal is the
Baker–Campbell–Hausdorff group of the quotient Lie algebra. -/
noncomputable def _root_.LieIdeal.bchQuotientEquiv (I : LieIdeal ℚ L) :
    BCHGroup L ⧸ (I : LieSubalgebra ℚ L).bchSubgroup ≃* BCHGroup (L ⧸ I) :=
  (QuotientGroup.quotientMulEquivOfEq (ker_map_mkQ I).symm).trans
    (QuotientGroup.quotientKerEquivOfRightInverse _ _
      (Function.rightInverse_surjInv (map_surjective (LieIdeal.surjective_mkQ I))))

@[simp]
theorem _root_.LieIdeal.bchQuotientEquiv_mk (I : LieIdeal ℚ L) (x : L) :
    I.bchQuotientEquiv (exp x : BCHGroup L) = exp (LieSubmodule.Quotient.mk x) := by
  -- The first isomorphism theorem sends the class of `g` to the image of `g`.
  rw [LieIdeal.bchQuotientEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk,
    QuotientGroup.quotientKerEquivOfRightInverse_apply, QuotientGroup.kerLift_mk, map_exp,
    LieIdeal.mkQ_apply]

end BCHGroup

end TauCeti
