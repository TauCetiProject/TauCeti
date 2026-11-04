/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Basic
public import TauCeti.RingTheory.Nilpotent.ChevalleyCommutator
public import TauCeti.RingTheory.Nilpotent.RootString.G2.Basic
public import TauCeti.RingTheory.Nilpotent.RootString.G2.ShortPair
import Mathlib.Algebra.Module.Rat
import Mathlib.GroupTheory.Commutator.Basic

/-!
# Steinberg's Chevalley commutator relations for divided-power one-parameter subgroups

Let `L` be a Lie algebra over `ℚ`, let `ρ` be a ring homomorphism from `U(L)` into a `ℚ`-algebra
`A`, and let `M` be an additive subgroup of an `A`-module `V` preserved by the divided powers of
the relevant root-vector images. Over every commutative ring `R`, `TauCeti.baseChangeExpHom`
attaches to each nilpotent image `ρ(ι e)` a one-parameter subgroup
`Multiplicative R →* (R ⊗[ℤ] M ≃ₗ[R] R ⊗[ℤ] M)`.

This file proves the element-commutator identities, in Steinberg's normalization
`⁅g, h⁆ = g * h * g⁻¹ * h⁻¹` (`commutatorElement`), across all seven positive rank-two root-string
configurations: commuting (`∅`), class two (`{α + β}`), doubly laced (`{α + β, 2α + β}` and
`{α + β, α + 2β}`), and the three type-`G₂` configurations (`{α + β, 2α + β, α + 2β}`,
`{α + β, 2α + β, 3α + β, 3α + 2β}`, and `{α + β, α + 2β, α + 3β, 2α + 3β}`). Every auxiliary
bracket identity needed to cancel the conjugated `E_y(u)` factor from the normal-ordering rules is
deduced from the Jacobi identity in a torsion-free Lie ring.

## Main results

* `TauCeti.dividedPower_zsmul_smul_mem`, `TauCeti.baseChangeExpHom_zsmul`,
  `TauCeti.commute_baseChangeExpHom`, `TauCeti.commutatorElement_baseChangeExpHom_of_commutator_eq`:
  integer scaling, commutation, and class-two commutator law for `baseChangeExpHom`.
* `TauCeti.UniversalEnvelopingAlgebra.zsmul_lie_eq_zero_of_zsmul_lie_eq_two`,
  `zsmul_lie_eq_zero_of_g2_short_pair`, `zsmul_lie_eq_zsmul_of_lie_eq_three_nsmul`: Jacobi
  identities in torsion-free Lie rings eliminating redundant vanishing-bracket assumptions.
* `TauCeti.UniversalEnvelopingAlgebra.commute_baseChangeExpHom_of_lie_eq_zero`,
  `commutatorElement_baseChangeExpHom_of_lie_eq`,
  `commutatorElement_baseChangeExpHom_of_lie_lie_eq`,
  `commutatorElement_baseChangeExpHom_of_lie_lie_rev_eq`,
  `commutatorElement_baseChangeExpHom_of_g2_short_pair`,
  `commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul`,
  `commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul_rev`: Steinberg's Chevalley commutator
  formula across all seven root-string configurations.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

open Multiplicative (ofAdd toAdd)
open TensorProduct
open scoped commutatorElement

namespace TauCeti

universe u v

variable {A : Type*} [Ring A] [Algebra ℚ A]
variable {V : Type u} [AddCommGroup V] [Module A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

/-- An additive subgroup preserved by all divided powers of `x` is preserved by all divided powers
of every integer multiple `c • x`. -/
theorem dividedPower_zsmul_smul_mem (c : ℤ) {x : A} (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M) :
    ∀ n, ∀ v ∈ M, Associative.dividedPower n (c • x) • v ∈ M := fun n v hv => by
  rw [Associative.dividedPower_zsmul, smul_assoc]
  exact zsmul_mem (hM n v hv) _

attribute [local instance high] Algebra.toModule

section BaseChangeHom

variable {R : Type v} [CommRing R]

private theorem toLinearMap_mul {M₁ : Type*} [AddCommMonoid M₁] [Module R M₁]
    (e₁ e₂ : M₁ ≃ₗ[R] M₁) : (e₁ * e₂).toLinearMap = e₁.toLinearMap * e₂.toLinearMap := rfl

variable [Algebra ℤ R]

/-- Rescaling a nilpotent operator by an integer `c` rescales the additive parameter of its
divided-power one-parameter subgroup `baseChangeExpHom` by `c`. -/
theorem baseChangeExpHom_zsmul (c : ℤ) {x : A} (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hcM : ∀ n, ∀ v ∈ M, Associative.dividedPower n (c • x) • v ∈ M)
    (hx : IsNilpotent x) (hc : IsNilpotent (c • x)) (t : Multiplicative R) :
    baseChangeExpHom (c • x) M hcM hc t =
      baseChangeExpHom x M hM hx (ofAdd ((c : R) * toAdd t)) :=
  LinearEquiv.toLinearMap_inj.mp <| by
    rw [baseChangeExpHom_toLinearMap, baseChangeExpHom_toLinearMap, toAdd_ofAdd]
    exact baseChangeExp_zsmul c M hM hcM hx (toAdd t)

/-- Form of `TauCeti.baseChangeExpHom_zsmul` evaluated at `Multiplicative.ofAdd r`. -/
theorem baseChangeExpHom_zsmul_ofAdd (c : ℤ) {x : A} (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hcM : ∀ n, ∀ v ∈ M, Associative.dividedPower n (c • x) • v ∈ M)
    (hx : IsNilpotent x) (hc : IsNilpotent (c • x)) (r : R) :
    baseChangeExpHom (c • x) M hcM hc (ofAdd r) =
      baseChangeExpHom x M hM hx (ofAdd ((c : R) * r)) := by
  simpa only [toAdd_ofAdd] using baseChangeExpHom_zsmul c M hM hcM hx hc (ofAdd r)

/-- One-parameter subgroups attached to commuting nilpotent operators commute. -/
theorem commute_baseChangeExpHom {x y : A} (M : S) (hxy : Commute x y)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (t u : Multiplicative R) :
    Commute (baseChangeExpHom x M hMx hx t) (baseChangeExpHom y M hMy hy u) :=
  LinearEquiv.toLinearMap_inj.mp <| by
    simp only [toLinearMap_mul, baseChangeExpHom_toLinearMap]
    exact commute_baseChangeExp M hxy hMx hMy (toAdd t) (toAdd u)

/-- **Class-two multiplication law for `baseChangeExpHom`.** If `x * y = y * x + z` with `z`
commuting with both `x` and `y`, then `E_x(t) E_y(u) = E_y(u) E_z(t * u) E_x(t)`. -/
theorem baseChangeExpHom_mul_of_commutator_eq {x y z : A} (M : S)
    (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z) (t u : Multiplicative R) :
    baseChangeExpHom x M hMx hx t * baseChangeExpHom y M hMy hy u =
      baseChangeExpHom y M hMy hy u * baseChangeExpHom z M hMz hz (ofAdd (toAdd t * toAdd u)) *
        baseChangeExpHom x M hMx hx t :=
  LinearEquiv.toLinearMap_inj.mp <| by
    simp only [toLinearMap_mul, baseChangeExpHom_toLinearMap, toAdd_ofAdd]
    exact baseChangeExp_mul_baseChangeExp_of_commutator_eq M hxy hxz hyz hx hy hMx hMy hMz
      (toAdd t) (toAdd u)

/-- **Class-two element-commutator relation for `baseChangeExpHom`.** If `x * y = y * x + z` with
`z` commuting with both `x` and `y`, then `⁅E_x(t), E_y(u)⁆ = E_z(t * u)`. -/
theorem commutatorElement_baseChangeExpHom_of_commutator_eq {x y z : A} (M : S)
    (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z) (t u : Multiplicative R) :
    ⁅baseChangeExpHom x M hMx hx t, baseChangeExpHom y M hMy hy u⁆ =
      baseChangeExpHom z M hMz hz (ofAdd (toAdd t * toAdd u)) := by
  rw [commutatorElement_def,
    baseChangeExpHom_mul_of_commutator_eq M hxy hxz hyz hMx hMy hMz hx hy hz t u,
    mul_inv_cancel_right, (commute_baseChangeExpHom M hyz hMy hMz hy hz u _).eq,
    mul_inv_cancel_right]

end BaseChangeHom

end TauCeti

namespace TauCeti.UniversalEnvelopingAlgebra

open _root_.UniversalEnvelopingAlgebra (ι)

section GroupHelpers

private theorem conj_mul_two_cancel {G : Type*} [Group G] {y a b : G}
    (hya : Commute y a) (hyb : Commute y b) : y * a * b * y⁻¹ = a * b := by
  rw [mul_assoc y a b, (hya.mul_right hyb).eq, mul_inv_cancel_right]

private theorem conj_mul_g2_short_pair_cancel {G : Type*} [Group G] {y y' a b s₁ s₂ : G}
    (hy : y * y' = 1) (hay : a * y' = y' * s₁ * a) (hby : Commute b y') (hsy : Commute s₂ y')
    (hsa : Commute s₁ a) (hsb : Commute s₁ b) : y * a * b * s₂ * y' = a * b * (s₁ * s₂) := by
  calc
    y * a * b * s₂ * y' = y * (a * y') * b * s₂ := by
      rw [mul_assoc _ s₂, hsy.eq, ← mul_assoc (y * a * b), mul_assoc (y * a) b y', hby.eq,
        ← mul_assoc (y * a) y' b, mul_assoc y a y']
    _ = a * b * (s₁ * s₂) := by
      rw [hay, ← mul_assoc y (y' * s₁) a, ← mul_assoc y y' s₁, hy, one_mul, hsa.eq,
        mul_assoc a s₁ b, hsb.eq, ← mul_assoc a b s₁, mul_assoc]

private theorem conj_mul_g2_cancel {G : Type*} [Group G] {y y' a b c d : G}
    (hy : y * y' = 1) (hcy : c * y' = y' * d * c) (hdy : Commute d y') (hby : Commute b y')
    (hay : Commute a y') (hdc : Commute d c) : y * a * b * c * d * y' = a * b * c * (d * d) := by
  calc
    y * a * b * c * d * y' = y * a * b * y' * d * c * d := by
      rw [mul_assoc _ d y', hdy.eq, ← mul_assoc (y * a * b * c) y' d, mul_assoc (y * a * b) c y',
        hcy, ← mul_assoc (y * a * b) (y' * d) c, ← mul_assoc (y * a * b) y' d]
    _ = a * b * c * (d * d) := by
      rw [mul_assoc (y * a) b y', hby.eq, ← mul_assoc (y * a) y' b, mul_assoc y a y', hay.eq,
        ← mul_assoc y y' a, hy, one_mul, mul_assoc (a * b) d c, hdc.eq, ← mul_assoc (a * b) c d,
        mul_assoc]

private theorem reorder_g2_rev {G : Type*} [Group G] {a b c d₁ d₂ : G}
    (hba : b * a = a * b * d₂) (hd₁c : Commute d₁ c) (hd₁b : Commute d₁ b)
    (hd₁a : Commute d₁ a) (hca : Commute c a) (hcb : Commute c b) :
    d₁ * (c * (b * a)) = a * b * c * (d₂ * d₁) := by
  calc
    d₁ * (c * (b * a)) = c * a * b * (d₂ * d₁) := by
      rw [← mul_assoc d₁ c, hd₁c.eq, mul_assoc c d₁ (b * a), ← mul_assoc d₁ b a, hd₁b.eq,
        mul_assoc b d₁ a, hd₁a.eq, ← mul_assoc b a d₁, ← mul_assoc c (b * a) d₁, hba,
        ← mul_assoc c (a * b) d₂, ← mul_assoc c a b, mul_assoc (c * a * b) d₂ d₁]
    _ = a * b * c * (d₂ * d₁) := by rw [hca.eq, mul_assoc a c b, hcb.eq, ← mul_assoc a b c]

end GroupHelpers

section Jacobi

variable {L : Type*} [LieRing L] [IsAddTorsionFree L]

/-- In a torsion-free Lie ring, if `⁅x, y⁆ = c • z`, `c • ⁅x, z⁆ = (2 * d) • w`, and
`⁅y, z⁆ = 0`, the Jacobi identity forces `d • ⁅y, w⁆ = 0`. -/
theorem zsmul_lie_eq_zero_of_zsmul_lie_eq_two {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : c • ⁅x, z⁆ = (2 * d) • w) (hyz : ⁅y, z⁆ = 0) :
    d • ⁅y, w⁆ = 0 := by
  refine (IsAddTorsionFree.zsmul_eq_zero_iff_right (n := (2 : ℤ)) (by decide)).mp ?_
  calc
    (2 : ℤ) • (d • ⁅y, w⁆) = ⁅y, (2 * d) • w⁆ := by rw [← mul_zsmul, lie_zsmul]
    _ = c • ⁅y, ⁅x, z⁆⁆ := by rw [← hxz, lie_zsmul]
    _ = c • ⁅⁅y, x⁆, z⁆ + c • ⁅x, ⁅y, z⁆⁆ := by rw [leibniz_lie, smul_add]
    _ = 0 := by rw [← lie_skew y x, hxy, neg_lie, zsmul_lie, lie_self, hyz, lie_zero]; simp

/-- In a Lie ring, if `⁅x, y⁆ = c • z`, `⁅x, w⁆ = 0`, and `d • ⁅y, w⁆ = 0`, the Jacobi identity
gives `(c * d) • ⁅z, w⁆ = 0`. -/
theorem zsmul_lie_eq_zero_of_lie_eq {L : Type*} [LieRing L] {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxw : ⁅x, w⁆ = 0) (hyw : d • ⁅y, w⁆ = 0) :
    (c * d) • ⁅z, w⁆ = 0 := by
  calc
    (c * d) • ⁅z, w⁆ = ⁅c • z, d • w⁆ := by rw [zsmul_lie, lie_zsmul, mul_zsmul]
    _ = 0 := by rw [← hxy, lie_lie, lie_zsmul, hyw, lie_zsmul, hxw, smul_zero, lie_zero, lie_zero,
      sub_self]

/-- In a torsion-free Lie ring, the short-pair bracket hypotheses
`⁅x, y⁆ = (2 * c) • z`, `c • ⁅x, z⁆ = (3 * d) • w`, `c • ⁅z, y⁆ = (3 * a) • s`, and `⁅x, s⁆ = 0`
force `d • ⁅y, w⁆ = 0` by the Jacobi identity. -/
theorem zsmul_lie_eq_zero_of_g2_short_pair {x y z w s : L} {c d a : ℤ}
    (hxy : ⁅x, y⁆ = (2 * c) • z) (hxz : c • ⁅x, z⁆ = (3 * d) • w)
    (hzy : c • ⁅z, y⁆ = (3 * a) • s) (hxs : ⁅x, s⁆ = 0) : d • ⁅y, w⁆ = 0 := by
  refine (IsAddTorsionFree.zsmul_eq_zero_iff_right (n := (3 : ℤ)) (by decide)).mp ?_
  have hyz : c • ⁅y, z⁆ = -((3 * a) • s) := by rw [← lie_skew y z, smul_neg, hzy]
  calc
    (3 : ℤ) • (d • ⁅y, w⁆) = ⁅y, (3 * d) • w⁆ := by rw [← mul_zsmul, lie_zsmul]
    _ = c • ⁅y, ⁅x, z⁆⁆ := by rw [← hxz, lie_zsmul]
    _ = c • ⁅⁅y, x⁆, z⁆ + ⁅x, c • ⁅y, z⁆⁆ := by rw [leibniz_lie, smul_add, lie_zsmul]
    _ = 0 := by
      rw [← lie_skew y x, hxy, neg_lie, zsmul_lie, lie_self, hyz, lie_neg, lie_zsmul, hxs]; simp

/-- In a torsion-free Lie ring, under the type-`G₂` scaled bracket hypotheses
`⁅x, y⁆ = c • z`, `c • ⁅x, z⁆ = (2 * d) • w`, `d • ⁅x, w⁆ = (3 * a) • m`,
`(d * c) • ⁅w, z⁆ = (3 * b) • o`, and `⁅y, z⁆ = 0`, the Jacobi identity gives
`a • ⁅y, m⁆ = b • o`. -/
theorem zsmul_lie_eq_zsmul_of_lie_eq_three_nsmul {x y z w m o : L} {c d a b : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : c • ⁅x, z⁆ = (2 * d) • w)
    (hxw : d • ⁅x, w⁆ = (3 * a) • m) (hwz : (d * c) • ⁅w, z⁆ = (3 * b) • o)
    (hyz : ⁅y, z⁆ = 0) : a • ⁅y, m⁆ = b • o := by
  have hyw := zsmul_lie_eq_zero_of_zsmul_lie_eq_two hxy hxz hyz
  refine ((AddCommute.all _ _).zsmul_right_inj (n := (3 : ℤ)) (by decide)).mp ?_
  calc
    (3 : ℤ) • (a • ⁅y, m⁆) = ⁅y, (3 * a) • m⁆ := by rw [← mul_zsmul, lie_zsmul]
    _ = d • ⁅y, ⁅x, w⁆⁆ := by rw [← hxw, lie_zsmul]
    _ = d • ⁅⁅y, x⁆, w⁆ + ⁅x, d • ⁅y, w⁆⁆ := by rw [leibniz_lie, smul_add, lie_zsmul]
    _ = (d * c) • ⁅w, z⁆ := by
      rw [hyw, lie_zero, add_zero, ← lie_skew y x, hxy, neg_lie, zsmul_lie, ← lie_skew z w,
        smul_neg, smul_neg, smul_neg, neg_neg, mul_zsmul]
    _ = (3 : ℤ) • (b • o) := by rw [hwz, mul_zsmul]

/-- Under the same type-`G₂` hypotheses, `b • ⁅y, o⁆ = 0`. -/
theorem zsmul_lie_fourth_eq_zero_of_lie_eq_three_nsmul {x y z w o : L} {c d b : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : c • ⁅x, z⁆ = (2 * d) • w)
    (hwz : (d * c) • ⁅w, z⁆ = (3 * b) • o) (hyz : ⁅y, z⁆ = 0) : b • ⁅y, o⁆ = 0 := by
  have hyw := zsmul_lie_eq_zero_of_zsmul_lie_eq_two hxy hxz hyz
  refine (IsAddTorsionFree.zsmul_eq_zero_iff_right (n := (3 : ℤ)) (by decide)).mp ?_
  calc
    (3 : ℤ) • (b • ⁅y, o⁆) = ⁅y, (3 * b) • o⁆ := by rw [← mul_zsmul, lie_zsmul]
    _ = (d * c) • ⁅y, ⁅w, z⁆⁆ := by rw [← hwz, lie_zsmul]
    _ = c • ⁅d • ⁅y, w⁆, z⁆ + (d * c) • ⁅w, ⁅y, z⁆⁆ := by
      rw [leibniz_lie, smul_add, zsmul_lie, mul_comm d c, mul_zsmul]
    _ = 0 := by rw [hyw, hyz]; simp

/-- In a torsion-free Lie ring, under the reversed type-`G₂` hypotheses
`c • ⁅z, y⁆ = (2 * d) • w`, `d • ⁅y, w⁆ = (3 * a) • m`, `(d * c) • ⁅z, w⁆ = (3 * b) • o`, and
`⁅y, o⁆ = 0`, the Jacobi identity forces `(a * c) • ⁅m, z⁆ = 0`. -/
theorem zsmul_lie_third_eq_zero_of_lie_eq_three_nsmul_rev {y z w m o : L} {c d a b : ℤ}
    (hzy : c • ⁅z, y⁆ = (2 * d) • w) (hyw : d • ⁅y, w⁆ = (3 * a) • m)
    (hzw : (d * c) • ⁅z, w⁆ = (3 * b) • o) (hyo : ⁅y, o⁆ = 0) : (a * c) • ⁅m, z⁆ = 0 := by
  suffices hzm : (a * c) • ⁅z, m⁆ = 0 by rw [← lie_skew m z, smul_neg, hzm, neg_zero]
  refine (IsAddTorsionFree.zsmul_eq_zero_iff_right (n := (3 : ℤ)) (by decide)).mp ?_
  have h0 : (3 : ℤ) • ((a * c) • ⁅z, m⁆) = c • ⁅z, (3 * a) • m⁆ := by
    rw [lie_zsmul, ← mul_zsmul, ← mul_zsmul]; congr 1; ring
  calc
    (3 : ℤ) • ((a * c) • ⁅z, m⁆) = c • (d • ⁅⁅z, y⁆, w⁆) + c • (d • ⁅y, ⁅z, w⁆⁆) := by
      rw [h0, ← hyw, lie_zsmul, leibniz_lie, smul_add, smul_add]
    _ = d • ⁅c • ⁅z, y⁆, w⁆ + ⁅y, (d * c) • ⁅z, w⁆⁆ := by
      rw [zsmul_lie, lie_zsmul, ← mul_zsmul, ← mul_zsmul, ← mul_zsmul, mul_comm c d]
    _ = 0 := by rw [hzy, zsmul_lie, lie_self, hzw, lie_zsmul, hyo]; simp

end Jacobi

section DividedPowerCommutator

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
variable {A : Type*} [Ring A]
variable {F : Type*} [FunLike F (_root_.UniversalEnvelopingAlgebra ℚ L) A]
  [NonUnitalRingHomClass F (_root_.UniversalEnvelopingAlgebra ℚ L) A]

/-- If `(p * q) • ⁅a, b⁆ = 0`, the integer-scaled images of `a` and `b` commute under any ring
homomorphism out of `U(L)`. -/
theorem commute_zsmul_of_zsmul_lie_eq_zero (ρ : F) {a b : L} {p q : ℤ}
    (hab : (p * q) • ⁅a, b⁆ = 0) : Commute (p • ρ (ι ℚ a)) (q • ρ (ι ℚ b)) := by
  have h := zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq (R := ℚ) ρ
    (p := p) (q := q) (b' := a) (r := 0) (n := 0) (by simpa using hab)
  rw [zero_smul, add_zero] at h; exact h

private theorem comm_zsmul (ρ : F) {a b : L} (p q : ℤ) (h : ⁅a, b⁆ = 0) :
    Commute (p • ρ (ι ℚ a)) (q • ρ (ι ℚ b)) :=
  ((commute_of_lie_eq_zero ρ h).smul_left p).smul_right q

private theorem zsmul_mul_of_lie (ρ : F) {a b c : L} {p q r : ℤ} {n : ℕ}
    (h : (p * q) • ⁅a, b⁆ = (n * r) • c) :
    p • ρ (ι ℚ a) * (q • ρ (ι ℚ b)) = q • ρ (ι ℚ b) * (p • ρ (ι ℚ a)) + n • (r • ρ (ι ℚ c)) :=
  zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ h

variable [Algebra ℚ A] {V : Type*} [AddCommGroup V] [Module A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]

attribute [local instance high] Algebra.toModule

variable {R : Type*} [CommRing R] [Algebra ℤ R]

private theorem inv_exp_ofAdd_eq_zsmul (M : S) {x : A} (c : ℤ)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hcM : ∀ n, ∀ v ∈ M, Associative.dividedPower n (c • x) • v ∈ M)
    (hx : IsNilpotent x) {r s : R} (hrs : -r = (c : R) * s) :
    (baseChangeExpHom x M hM hx (ofAdd r))⁻¹ =
      baseChangeExpHom (c • x) M hcM (hx.smul c) (ofAdd s) := by
  rw [← map_inv, ← ofAdd_neg, baseChangeExpHom_zsmul_ofAdd c M hM hcM hx (hx.smul c), hrs]

private theorem commute_exp_zsmul_right (ρ : F) (M : S) {a b : L} {q : ℤ} (hab : q • ⁅a, b⁆ = 0)
    (hMa : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ a)) • v ∈ M)
    (hMb : ∀ n, ∀ v ∈ M, Associative.dividedPower n (q • ρ (ι ℚ b)) • v ∈ M)
    (ha : IsNilpotent (ρ (ι ℚ a))) (hb : IsNilpotent (q • ρ (ι ℚ b))) (t u : Multiplicative R) :
    Commute (baseChangeExpHom (ρ (ι ℚ a)) M hMa ha t)
      (baseChangeExpHom (q • ρ (ι ℚ b)) M hMb hb u) :=
  commute_baseChangeExpHom M
    (by simpa only [one_zsmul] using
      commute_zsmul_of_zsmul_lie_eq_zero ρ (p := 1) (q := q) (by simpa using hab))
    hMa hMb ha hb t u

/-- **Commuting Chevalley relation for `baseChangeExpHom`.** If `⁅x, y⁆ = 0`, the corresponding
divided-power one-parameter subgroups commute. -/
theorem commute_baseChangeExpHom_of_lie_eq_zero (ρ : F) (M : S) {x y : L} (hxy : ⁅x, y⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ y)) • v ∈ M)
    (hx : IsNilpotent (ρ (ι ℚ x))) (hy : IsNilpotent (ρ (ι ℚ y))) (t u : Multiplicative R) :
    Commute (baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t) (baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u) :=
  commute_baseChangeExpHom M (commute_of_lie_eq_zero ρ hxy) hMx hMy hx hy t u

/-- **Steinberg's class-two Chevalley commutator relation for `baseChangeExpHom`.** If
`⁅x, y⁆ = c • z` with `⁅x, z⁆ = ⁅y, z⁆ = 0`, then `⁅E_x(t), E_y(u)⁆ = E_z(c t u)`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_eq (ρ : F) (M : S) {x y z : L} {c : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : ⁅x, z⁆ = 0) (hyz : ⁅y, z⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ z)) • v ∈ M)
    (hx : IsNilpotent (ρ (ι ℚ x))) (hy : IsNilpotent (ρ (ι ℚ y))) (hz : IsNilpotent (ρ (ι ℚ z)))
    (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t, baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (ι ℚ z)) M hMz hz (ofAdd ((c : R) * (toAdd t * toAdd u))) := by
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  rw [← baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c)]
  exact commutatorElement_baseChangeExpHom_of_commutator_eq M
    (mul_eq_mul_add_zsmul_of_lie_eq ρ hxy) ((commute_of_lie_eq_zero ρ hxz).smul_right c)
    ((commute_of_lie_eq_zero ρ hyz).smul_right c) hMx hMy hMcz hx hy (hz.smul c) t u

/-- **Steinberg's Chevalley commutator relation for the chain `α + β, 2α + β`.** If
`⁅x, y⁆ = c • z` and `⁅x, ⁅x, y⁆⁆ = (2 * d) • w` with `⁅x, w⁆ = ⁅y, z⁆ = 0`, then
`⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(d t² u)`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_lie_eq (ρ : F) (M : S) {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxxy : ⁅x, ⁅x, y⁆⁆ = (2 * d) • w)
    (hxw : ⁅x, w⁆ = 0) (hyz : ⁅y, z⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ w)) • v ∈ M)
    (hx : IsNilpotent (ρ (ι ℚ x))) (hy : IsNilpotent (ρ (ι ℚ y)))
    (hz : IsNilpotent (ρ (ι ℚ z))) (hw : IsNilpotent (ρ (ι ℚ w))) (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t, baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (ι ℚ z)) M hMz hz (ofAdd ((c : R) * (toAdd t * toAdd u))) *
        baseChangeExpHom (ρ (ι ℚ w)) M hMw hw (ofAdd ((d : R) * (toAdd t ^ 2 * toAdd u))) := by
  have _ : HasUniqueDiv L := .of_module_rat L
  have hxz : c • ⁅x, z⁆ = (2 * d) • w := by rw [← lie_zsmul, ← hxy, hxxy]
  have hyw := zsmul_lie_eq_zero_of_zsmul_lie_eq_two hxy hxz hyz
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  have hMdw := dividedPower_zsmul_smul_mem d M hMw
  let tr := toAdd t; let ur := toAdd u
  have hmul :
      baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t * baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u =
        baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u *
          baseChangeExpHom (c • ρ (ι ℚ z)) M hMcz (hz.smul c) (ofAdd (tr * ur)) *
          baseChangeExpHom (d • ρ (ι ℚ w)) M hMdw (hw.smul d) (ofAdd (tr ^ 2 * ur)) *
          baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t :=
    LinearEquiv.toLinearMap_inj.mp <| by
      simp only [toLinearMap_mul, baseChangeExpHom_toLinearMap, toAdd_ofAdd]
      exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul M
        (mul_eq_mul_add_zsmul_of_lie_eq ρ hxy)
        (by simpa only [one_zsmul] using
          zsmul_mul_of_lie ρ (p := 1) (q := c) (r := d) (n := 2) (by simpa using hxz))
        ((commute_of_lie_eq_zero ρ hxw).smul_right d) ((commute_of_lie_eq_zero ρ hyz).smul_right c)
        hx hy (hz.smul c) hMx hMy hMcz hMdw tr ur
  rw [commutatorElement_def, hmul, mul_inv_cancel_right,
    conj_mul_two_cancel
      (commute_baseChangeExpHom M ((commute_of_lie_eq_zero ρ hyz).smul_right c)
        hMy hMcz hy (hz.smul c) u _)
      (commute_exp_zsmul_right ρ M hyw hMy hMdw hy (hw.smul d) u _),
    baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c),
    baseChangeExpHom_zsmul_ofAdd d M hMw hMdw hw (hw.smul d)]

/-- **Steinberg's Chevalley commutator relation for the reversed chain `α + β, α + 2β`.** If
`⁅x, y⁆ = c • z` and `⁅y, ⁅y, x⁆⁆ = (2 * d) • w` with `⁅y, w⁆ = ⁅x, z⁆ = 0`, then
`⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(-d t u²)`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_lie_rev_eq (ρ : F) (M : S)
    {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hyyx : ⁅y, ⁅y, x⁆⁆ = (2 * d) • w)
    (hyw : ⁅y, w⁆ = 0) (hxz : ⁅x, z⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ w)) • v ∈ M)
    (hx : IsNilpotent (ρ (ι ℚ x))) (hy : IsNilpotent (ρ (ι ℚ y)))
    (hz : IsNilpotent (ρ (ι ℚ z))) (hw : IsNilpotent (ρ (ι ℚ w))) (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t, baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (ι ℚ z)) M hMz hz (ofAdd ((c : R) * (toAdd t * toAdd u))) *
        baseChangeExpHom (ρ (ι ℚ w)) M hMw hw (ofAdd ((-d : R) * (toAdd t * toAdd u ^ 2))) := by
  have _ : HasUniqueDiv L := .of_module_rat L
  have hyx : ⁅y, x⁆ = (-c) • z := by rw [← lie_skew y x, hxy, neg_zsmul]
  have hyz : (-c) • ⁅y, z⁆ = (2 * d) • w := by rw [← lie_zsmul, ← hyx, hyyx]
  have hzw : (c * (-d)) • ⁅z, w⁆ = 0 := by
    simpa only [neg_mul_comm] using
      zsmul_lie_eq_zero_of_lie_eq hyx hyw (zsmul_lie_eq_zero_of_zsmul_lie_eq_two hyx hyz hxz)
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  have hMdw := dividedPower_zsmul_smul_mem (-d) M hMw
  rw [← commutatorElement_inv,
    commutatorElement_baseChangeExpHom_of_lie_lie_eq ρ M hyx hyyx hyw hxz
      hMy hMx hMz hMw hy hx hz hw u t,
    mul_inv_rev,
    inv_exp_ofAdd_eq_zsmul M (-d) hMw hMdw hw (s := toAdd t * toAdd u ^ 2) (by push_cast; ring),
    inv_exp_ofAdd_eq_zsmul M c hMz hMcz hz (s := toAdd t * toAdd u) (by push_cast; ring),
    (commute_baseChangeExpHom M (commute_zsmul_of_zsmul_lie_eq_zero ρ hzw).symm
      hMdw hMcz (hw.smul (-d)) (hz.smul c) _ _).eq,
    baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c),
    baseChangeExpHom_zsmul_ofAdd (-d) M hMw hMdw hw (hw.smul (-d)), Int.cast_neg]

/-- **Steinberg's Chevalley commutator relation for the type-`G₂` short pair.** For roots
`α, α + β, 2α + β, 3α + β, 3α + 2β` corresponding to `x, y, z, w, s` with
`⁅x, y⁆ = (2 * c) • z`, `c • ⁅x, z⁆ = (3 * d) • w`, and `c • ⁅z, y⁆ = (3 * a) • s`, the element
commutator is `⁅E_x(t), E_y(u)⁆ = E_z(2c t u) E_w(3d t² u) E_s(-3a t u²)`. -/
theorem commutatorElement_baseChangeExpHom_of_g2_short_pair (ρ : F) (M : S)
    {x y z w s : L} {c d a : ℤ}
    (hxy : ⁅x, y⁆ = (2 * c) • z) (hxz : c • ⁅x, z⁆ = (3 * d) • w) (hzy : c • ⁅z, y⁆ = (3 * a) • s)
    (hxw : ⁅x, w⁆ = 0) (hxs : ⁅x, s⁆ = 0) (hys : ⁅y, s⁆ = 0)
    (hzw : ⁅z, w⁆ = 0) (hzs : ⁅z, s⁆ = 0) (hws : ⁅w, s⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ w)) • v ∈ M)
    (hMs : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ s)) • v ∈ M)
    (hx : IsNilpotent (ρ (ι ℚ x))) (hy : IsNilpotent (ρ (ι ℚ y))) (hz : IsNilpotent (ρ (ι ℚ z)))
    (hw : IsNilpotent (ρ (ι ℚ w))) (hs : IsNilpotent (ρ (ι ℚ s))) (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t, baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (ι ℚ z)) M hMz hz (ofAdd ((c : R) * (2 * toAdd t * toAdd u))) *
        baseChangeExpHom (ρ (ι ℚ w)) M hMw hw (ofAdd ((d : R) * (3 * toAdd t ^ 2 * toAdd u))) *
        baseChangeExpHom (ρ (ι ℚ s)) M hMs hs (ofAdd ((-a : R) * (3 * toAdd t * toAdd u ^ 2))) := by
  have _ : HasUniqueDiv L := .of_module_rat L
  have hyw := zsmul_lie_eq_zero_of_g2_short_pair hxy hxz hzy hxs
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  have hMdw := dividedPower_zsmul_smul_mem d M hMw
  have hMas := dividedPower_zsmul_smul_mem a M hMs
  have hM3as := dividedPower_zsmul_smul_mem (3 * a) M hMs
  let tr := toAdd t; let ur := toAdd u
  have hmul :
      baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t * baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u =
        baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u *
          baseChangeExpHom (c • ρ (ι ℚ z)) M hMcz (hz.smul c) (ofAdd (2 * tr * ur)) *
          baseChangeExpHom (d • ρ (ι ℚ w)) M hMdw (hw.smul d) (ofAdd (3 * tr ^ 2 * ur)) *
          baseChangeExpHom (a • ρ (ι ℚ s)) M hMas (hs.smul a) (ofAdd (3 * tr * ur ^ 2)) *
          baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t :=
    LinearEquiv.toLinearMap_inj.mp <| by
      simp only [toLinearMap_mul, baseChangeExpHom_toLinearMap, toAdd_ofAdd]
      exact baseChangeExp_mul_baseChangeExp_of_g2_short_pair M
        (by simpa only [one_zsmul] using
          zsmul_mul_of_lie ρ (p := 1) (q := 1) (r := c) (n := 2) (by simpa using hxy))
        (by simpa only [one_zsmul] using
          zsmul_mul_of_lie ρ (p := 1) (q := c) (r := d) (n := 3) (by simpa using hxz))
        (by simpa only [one_zsmul] using
          zsmul_mul_of_lie ρ (p := c) (q := 1) (r := a) (n := 3) (by simpa using hzy))
        ((commute_of_lie_eq_zero ρ hxw).smul_right d) ((commute_of_lie_eq_zero ρ hxs).smul_right a)
        ((commute_of_lie_eq_zero ρ hys).smul_right a) (comm_zsmul ρ c d hzw)
        (comm_zsmul ρ c a hzs) (comm_zsmul ρ d a hws) hx hy (hz.smul c) hMx hMy hMcz hMdw hMas tr ur
  have hswap_zy :
      baseChangeExpHom (c • ρ (ι ℚ z)) M hMcz (hz.smul c) (ofAdd (2 * tr * ur)) *
        baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁻¹ =
      baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁻¹ *
        baseChangeExpHom (a • ρ (ι ℚ s)) M hMas (hs.smul a) (ofAdd (-(6 * tr * ur ^ 2))) *
        baseChangeExpHom (c • ρ (ι ℚ z)) M hMcz (hz.smul c) (ofAdd (2 * tr * ur)) := by
    rw [baseChangeExpHom_mul_of_commutator_eq M
        (by simpa only [one_zsmul, one_nsmul, one_mul] using
          zsmul_mul_of_lie ρ (p := c) (q := 1) (r := 3 * a) (n := 1) (by simpa using hzy))
        (comm_zsmul ρ c (3 * a) hzs) ((commute_of_lie_eq_zero ρ hys).smul_right (3 * a))
        hMcz hMy hM3as (hz.smul c) hy (hs.smul (3 * a)) (ofAdd (2 * tr * ur)) u⁻¹,
      baseChangeExpHom_zsmul_ofAdd (3 * a) M hMs hM3as hs (hs.smul (3 * a)),
      baseChangeExpHom_zsmul_ofAdd a M hMs hMas hs (hs.smul a)]
    congr 4; simp only [ur, toAdd_ofAdd, toAdd_inv]; push_cast; ring
  have hy_inv :
      baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u * baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁻¹ = 1 := by
    rw [← (baseChangeExpHom _ M hMy hy).map_mul, mul_inv_cancel, map_one]
  rw [commutatorElement_def, hmul, mul_inv_cancel_right,
    ← _root_.map_inv (baseChangeExpHom (ρ (ι ℚ y)) M hMy hy) u,
    conj_mul_g2_short_pair_cancel hy_inv hswap_zy
      (commute_exp_zsmul_right ρ M hyw hMy hMdw hy (hw.smul d) u⁻¹ _).symm
      (commute_baseChangeExpHom M ((commute_of_lie_eq_zero ρ hys).smul_right a).symm
        hMas hMy (hs.smul a) hy _ u⁻¹)
      (commute_baseChangeExpHom M (comm_zsmul ρ c a hzs).symm hMas hMcz (hs.smul a) (hz.smul c) _ _)
      (commute_baseChangeExpHom M (comm_zsmul ρ d a hws).symm
        hMas hMdw (hs.smul a) (hw.smul d) _ _),
    ← (baseChangeExpHom _ M hMas (hs.smul a)).map_mul, ← ofAdd_add,
    baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c),
    baseChangeExpHom_zsmul_ofAdd d M hMw hMdw hw (hw.smul d),
    baseChangeExpHom_zsmul_ofAdd a M hMs hMas hs (hs.smul a)]
  congr 3; ring

/-- **Steinberg's Chevalley commutator relation in type `G₂` (`α` short, `β` long).** Under the
scaled and vanishing bracket hypotheses of the product straightening rule,
`⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(d t² u) E_m(a t³ u) E_o(2b t³ u²)`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul (ρ : F) (M : S)
    {x y z w m o : L} {c d a b : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : c • ⁅x, z⁆ = (2 * d) • w)
    (hxw : d • ⁅x, w⁆ = (3 * a) • m) (hwz : (d * c) • ⁅w, z⁆ = (3 * b) • o)
    (hxm : ⁅x, m⁆ = 0) (hxo : ⁅x, o⁆ = 0) (hyz : ⁅y, z⁆ = 0)
    (hwm : ⁅w, m⁆ = 0) (hzo : ⁅z, o⁆ = 0) (hwo : ⁅w, o⁆ = 0) (hmo : ⁅m, o⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ w)) • v ∈ M)
    (hMm : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ m)) • v ∈ M)
    (hMo : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ o)) • v ∈ M)
    (hx : IsNilpotent (ρ (ι ℚ x))) (hy : IsNilpotent (ρ (ι ℚ y))) (hz : IsNilpotent (ρ (ι ℚ z)))
    (hw : IsNilpotent (ρ (ι ℚ w))) (hm : IsNilpotent (ρ (ι ℚ m))) (ho : IsNilpotent (ρ (ι ℚ o)))
    (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t, baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (ι ℚ z)) M hMz hz (ofAdd ((c : R) * (toAdd t * toAdd u))) *
        baseChangeExpHom (ρ (ι ℚ w)) M hMw hw (ofAdd ((d : R) * (toAdd t ^ 2 * toAdd u))) *
        baseChangeExpHom (ρ (ι ℚ m)) M hMm hm (ofAdd ((a : R) * (toAdd t ^ 3 * toAdd u))) *
        baseChangeExpHom (ρ (ι ℚ o)) M hMo ho
          (ofAdd (((2 * b : ℤ) : R) * (toAdd t ^ 3 * toAdd u ^ 2))) := by
  have _ : HasUniqueDiv L := .of_module_rat L
  have hyw := zsmul_lie_eq_zero_of_zsmul_lie_eq_two hxy hxz hyz
  have hym := zsmul_lie_eq_zsmul_of_lie_eq_three_nsmul hxy hxz hxw hwz hyz
  have hyo := zsmul_lie_fourth_eq_zero_of_lie_eq_three_nsmul hxy hxz hwz hyz
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  have hMdw := dividedPower_zsmul_smul_mem d M hMw
  have hMam := dividedPower_zsmul_smul_mem a M hMm
  have hMbo := dividedPower_zsmul_smul_mem b M hMo
  have hMnbo := dividedPower_zsmul_smul_mem (-b) M hMo
  let tr := toAdd t; let ur := toAdd u
  have hmul :
      baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t * baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u =
        baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u *
          baseChangeExpHom (c • ρ (ι ℚ z)) M hMcz (hz.smul c) (ofAdd (tr * ur)) *
          baseChangeExpHom (d • ρ (ι ℚ w)) M hMdw (hw.smul d) (ofAdd (tr ^ 2 * ur)) *
          baseChangeExpHom (a • ρ (ι ℚ m)) M hMam (hm.smul a) (ofAdd (tr ^ 3 * ur)) *
          baseChangeExpHom (b • ρ (ι ℚ o)) M hMbo (ho.smul b) (ofAdd (tr ^ 3 * ur ^ 2)) *
          baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t :=
    LinearEquiv.toLinearMap_inj.mp <| by
      simp only [toLinearMap_mul, baseChangeExpHom_toLinearMap, toAdd_ofAdd]
      exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_three_nsmul M
        (mul_eq_mul_add_zsmul_of_lie_eq ρ hxy)
        (by simpa only [one_zsmul] using
          zsmul_mul_of_lie ρ (p := 1) (q := c) (r := d) (n := 2) (by simpa using hxz))
        (by simpa only [one_zsmul] using
          zsmul_mul_of_lie ρ (p := 1) (q := d) (r := a) (n := 3) (by simpa using hxw))
        (by simpa using zsmul_mul_of_lie ρ (p := d) (q := c) (r := b) (n := 3) (by simpa using hwz))
        ((commute_of_lie_eq_zero ρ hxm).smul_right a) ((commute_of_lie_eq_zero ρ hxo).smul_right b)
        ((commute_of_lie_eq_zero ρ hyz).smul_right c) (comm_zsmul ρ d a hwm)
        (comm_zsmul ρ c b hzo) (comm_zsmul ρ d b hwo) (comm_zsmul ρ a b hmo)
        hx hy (hz.smul c) (hw.smul d) hMx hMy hMcz hMdw hMam hMbo tr ur
  have hswap_my :
      baseChangeExpHom (a • ρ (ι ℚ m)) M hMam (hm.smul a) (ofAdd (tr ^ 3 * ur)) *
        baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁻¹ =
      baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁻¹ *
        baseChangeExpHom (b • ρ (ι ℚ o)) M hMbo (ho.smul b) (ofAdd (tr ^ 3 * ur ^ 2)) *
        baseChangeExpHom (a • ρ (ι ℚ m)) M hMam (hm.smul a) (ofAdd (tr ^ 3 * ur)) := by
    have hmy_lie : (a * 1) • ⁅m, y⁆ = ((1 : ℕ) * (-b)) • o := by
      rw [mul_one, ← lie_skew m y, smul_neg, hym]; simp
    have hy_nbo : Commute (ρ (ι ℚ y)) ((-b) • ρ (ι ℚ o)) := by
      simpa only [one_zsmul] using commute_zsmul_of_zsmul_lie_eq_zero ρ (p := 1) (q := -b)
        (by rw [one_mul, neg_zsmul, hyo, neg_zero])
    rw [baseChangeExpHom_mul_of_commutator_eq M
        (by simpa only [one_zsmul, one_nsmul] using zsmul_mul_of_lie ρ hmy_lie)
        (comm_zsmul ρ a (-b) hmo) hy_nbo
        hMam hMy hMnbo (hm.smul a) hy (ho.smul (-b)) (ofAdd (tr ^ 3 * ur)) u⁻¹,
      baseChangeExpHom_zsmul_ofAdd (-b) M hMo hMnbo ho (ho.smul (-b)),
      baseChangeExpHom_zsmul_ofAdd b M hMo hMbo ho (ho.smul b)]
    congr 4; simp only [ur, toAdd_ofAdd, toAdd_inv]; push_cast; ring
  have hy_inv :
      baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u * baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁻¹ = 1 := by
    rw [← (baseChangeExpHom _ M hMy hy).map_mul, mul_inv_cancel, map_one]
  rw [commutatorElement_def, hmul, mul_inv_cancel_right,
    ← _root_.map_inv (baseChangeExpHom (ρ (ι ℚ y)) M hMy hy) u,
    conj_mul_g2_cancel hy_inv hswap_my
      (commute_exp_zsmul_right ρ M hyo hMy hMbo hy (ho.smul b) u⁻¹ _).symm
      (commute_exp_zsmul_right ρ M hyw hMy hMdw hy (hw.smul d) u⁻¹ _).symm
      (commute_baseChangeExpHom M ((commute_of_lie_eq_zero ρ hyz).smul_right c).symm
        hMcz hMy (hz.smul c) hy _ u⁻¹)
      (commute_baseChangeExpHom M (comm_zsmul ρ a b hmo).symm
        hMbo hMam (ho.smul b) (hm.smul a) _ _),
    ← (baseChangeExpHom _ M hMbo (ho.smul b)).map_mul, ← ofAdd_add,
    baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c),
    baseChangeExpHom_zsmul_ofAdd d M hMw hMdw hw (hw.smul d),
    baseChangeExpHom_zsmul_ofAdd a M hMm hMam hm (hm.smul a),
    baseChangeExpHom_zsmul_ofAdd b M hMo hMbo ho (ho.smul b)]
  congr 3; push_cast; ring

/-- **Steinberg's Chevalley commutator relation in type `G₂` (`α` long, `β` short).** For roots
`α, β, α + β, α + 2β, α + 3β, 2α + 3β` corresponding to `x, y, z, w, m, o` with
`⁅x, y⁆ = c • z`, `c • ⁅z, y⁆ = (2 * d) • w`, `d • ⁅y, w⁆ = (3 * a) • m`, and
`(d * c) • ⁅z, w⁆ = (3 * b) • o`, the element commutator is
`⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(-d t u²) E_m(-a t u³) E_o(b t² u³)`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul_rev (ρ : F) (M : S)
    {x y z w m o : L} {c d a b : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hzy : c • ⁅z, y⁆ = (2 * d) • w)
    (hyw : d • ⁅y, w⁆ = (3 * a) • m) (hzw : (d * c) • ⁅z, w⁆ = (3 * b) • o)
    (hym : ⁅y, m⁆ = 0) (hyo : ⁅y, o⁆ = 0) (hxz : ⁅x, z⁆ = 0)
    (hwm : ⁅w, m⁆ = 0) (hzo : ⁅z, o⁆ = 0) (hwo : ⁅w, o⁆ = 0) (hmo : ⁅m, o⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ w)) • v ∈ M)
    (hMm : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ m)) • v ∈ M)
    (hMo : ∀ n, ∀ v ∈ M, Associative.dividedPower n (ρ (ι ℚ o)) • v ∈ M)
    (hx : IsNilpotent (ρ (ι ℚ x))) (hy : IsNilpotent (ρ (ι ℚ y))) (hz : IsNilpotent (ρ (ι ℚ z)))
    (hw : IsNilpotent (ρ (ι ℚ w))) (hm : IsNilpotent (ρ (ι ℚ m))) (ho : IsNilpotent (ρ (ι ℚ o)))
    (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (ι ℚ x)) M hMx hx t, baseChangeExpHom (ρ (ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (ι ℚ z)) M hMz hz (ofAdd ((c : R) * (toAdd t * toAdd u))) *
        baseChangeExpHom (ρ (ι ℚ w)) M hMw hw (ofAdd ((-d : R) * (toAdd t * toAdd u ^ 2))) *
        baseChangeExpHom (ρ (ι ℚ m)) M hMm hm (ofAdd ((-a : R) * (toAdd t * toAdd u ^ 3))) *
        baseChangeExpHom (ρ (ι ℚ o)) M hMo ho (ofAdd ((b : R) * (toAdd t ^ 2 * toAdd u ^ 3))) := by
  have _ : HasUniqueDiv L := .of_module_rat L
  have hyx : ⁅y, x⁆ = (-c) • z := by rw [← lie_skew y x, hxy, neg_zsmul]
  have hyz' : (-c) • ⁅y, z⁆ = (2 * d) • w := by
    rw [← lie_skew y z, smul_neg, neg_zsmul, neg_neg, hzy]
  have hwz' : (d * (-c)) • ⁅w, z⁆ = (3 * b) • o := by
    rw [mul_neg, ← lie_skew w z, smul_neg, neg_zsmul, neg_neg, hzw]
  have hmz := zsmul_lie_third_eq_zero_of_lie_eq_three_nsmul_rev hzy hyw hzw hyo
  let tr := toAdd t; let ur := toAdd u
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  have hMdw := dividedPower_zsmul_smul_mem d M hMw
  have hMam := dividedPower_zsmul_smul_mem a M hMm
  have hMbo := dividedPower_zsmul_smul_mem b M hMo
  have hMn3bo := dividedPower_zsmul_smul_mem (-(3 * b)) M hMo
  have hcomm_ow : ∀ r, Commute
      (baseChangeExpHom (b • ρ (ι ℚ o)) M hMbo (ho.smul b) r)
      (baseChangeExpHom (d • ρ (ι ℚ w)) M hMdw (hw.smul d) (ofAdd (-(tr * ur ^ 2)))) :=
    fun r => commute_baseChangeExpHom M (comm_zsmul ρ d b hwo).symm hMbo hMdw (ho.smul b)
      (hw.smul d) r _
  have hswap_wz :
      baseChangeExpHom (d • ρ (ι ℚ w)) M hMdw (hw.smul d) (ofAdd (-(tr * ur ^ 2))) *
        baseChangeExpHom (c • ρ (ι ℚ z)) M hMcz (hz.smul c) (ofAdd (tr * ur)) =
      baseChangeExpHom (c • ρ (ι ℚ z)) M hMcz (hz.smul c) (ofAdd (tr * ur)) *
        baseChangeExpHom (d • ρ (ι ℚ w)) M hMdw (hw.smul d) (ofAdd (-(tr * ur ^ 2))) *
        baseChangeExpHom (b • ρ (ι ℚ o)) M hMbo (ho.smul b) (ofAdd (3 * (tr ^ 2 * ur ^ 3))) := by
    have hwz_lie : (d * c) • ⁅w, z⁆ = ((1 : ℕ) * (-(3 * b))) • o := by
      rw [← lie_skew w z, smul_neg, hzw]; simp
    have hpar :
        baseChangeExpHom ((-(3 * b)) • ρ (ι ℚ o)) M hMn3bo (ho.smul (-(3 * b)))
            (ofAdd (toAdd (ofAdd (-(tr * ur ^ 2))) * toAdd (ofAdd (tr * ur)))) =
          baseChangeExpHom (b • ρ (ι ℚ o)) M hMbo (ho.smul b) (ofAdd (3 * (tr ^ 2 * ur ^ 3))) := by
      rw [baseChangeExpHom_zsmul_ofAdd (-(3 * b)) M hMo hMn3bo ho (ho.smul (-(3 * b))),
        baseChangeExpHom_zsmul_ofAdd b M hMo hMbo ho (ho.smul b)]
      congr 2; simp only [toAdd_ofAdd]; push_cast; ring
    rw [baseChangeExpHom_mul_of_commutator_eq M
        (by simpa only [one_zsmul, one_nsmul] using zsmul_mul_of_lie ρ hwz_lie)
        (comm_zsmul ρ d (-(3 * b)) hwo) (comm_zsmul ρ c (-(3 * b)) hzo)
        hMdw hMcz hMn3bo (hw.smul d) (hz.smul c) (ho.smul (-(3 * b)))
        (ofAdd (-(tr * ur ^ 2))) (ofAdd (tr * ur)),
      hpar, mul_assoc _ (baseChangeExpHom (b • _) _ _ _ _), (hcomm_ow _).eq, ← mul_assoc]
  rw [← commutatorElement_inv,
    commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul ρ M
      hyx hyz' hyw hwz' hym hyo hxz hwm hzo hwo hmo hMy hMx hMz hMw hMm hMo hy hx hz hw hm ho u t,
    mul_inv_rev, mul_inv_rev, mul_inv_rev,
    inv_exp_ofAdd_eq_zsmul M b hMo hMbo ho (s := (-2 : R) * (tr ^ 2 * ur ^ 3)) (by push_cast; ring),
    inv_exp_ofAdd_eq_zsmul M a hMm hMam hm (s := -(tr * ur ^ 3)) (by ring),
    inv_exp_ofAdd_eq_zsmul M d hMw hMdw hw (s := -(tr * ur ^ 2)) (by ring),
    inv_exp_ofAdd_eq_zsmul M c hMz hMcz hz (s := tr * ur) (by push_cast; ring),
    reorder_g2_rev hswap_wz
      (commute_baseChangeExpHom M (comm_zsmul ρ a b hmo).symm hMbo hMam (ho.smul b) (hm.smul a) _ _)
      (hcomm_ow _)
      (commute_baseChangeExpHom M (comm_zsmul ρ c b hzo).symm hMbo hMcz (ho.smul b) (hz.smul c) _ _)
      (commute_baseChangeExpHom M (commute_zsmul_of_zsmul_lie_eq_zero ρ hmz)
        hMam hMcz (hm.smul a) (hz.smul c) _ _)
      (commute_baseChangeExpHom M (comm_zsmul ρ d a hwm).symm
        hMam hMdw (hm.smul a) (hw.smul d) _ _),
    ← (baseChangeExpHom _ M hMbo (ho.smul b)).map_mul, ← ofAdd_add,
    baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c),
    baseChangeExpHom_zsmul_ofAdd d M hMw hMdw hw (hw.smul d),
    baseChangeExpHom_zsmul_ofAdd a M hMm hMam hm (hm.smul a),
    baseChangeExpHom_zsmul_ofAdd b M hMo hMbo ho (ho.smul b)]
  rw [show (d : R) * -(tr * ur ^ 2) = (-d : R) * (tr * ur ^ 2) by ring,
    show (a : R) * -(tr * ur ^ 3) = (-a : R) * (tr * ur ^ 3) by ring,
    show (b : R) * (3 * (tr ^ 2 * ur ^ 3) + (-2 : R) * (tr ^ 2 * ur ^ 3)) =
      (b : R) * (tr ^ 2 * ur ^ 3) by ring]

end DividedPowerCommutator

end TauCeti.UniversalEnvelopingAlgebra
