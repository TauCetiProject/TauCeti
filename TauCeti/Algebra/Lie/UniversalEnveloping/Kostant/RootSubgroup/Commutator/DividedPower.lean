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
`⁅g, h⁆ = g * h * g⁻¹ * h⁻¹` (`commutatorElement`), for all positive rank-two root-string
configurations:

* commuting root vectors: `Commute (E_x(t)) (E_y(u))`;
* class two (`{α + β}`): `⁅E_x(t), E_y(u)⁆ = E_z(c t u)`;
* length-two chain (`{α + β, 2α + β}`): `⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(d t² u)`;
* reversed length-two chain (`{α + β, α + 2β}`):
  `⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(-d t u²)`;
* type-`G₂` short pair (`{α + β, 2α + β, α + 2β}`):
  `⁅E_x(t), E_y(u)⁆ = E_z(2c t u) E_w(3d t² u) E_s(-3a t u²)`;
* type-`G₂` short--long simple pair (`{α + β, 2α + β, 3α + β, 3α + 2β}`):
  `⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(d t² u) E_m(a t³ u) E_o(2b t³ u²)`;
* type-`G₂` long--short simple pair (`{α + β, α + 2β, α + 3β, 2α + 3β}`):
  `⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(-d t u²) E_m(-a t u³) E_o(b t² u³)`.

Every auxiliary bracket identity needed to cancel the conjugated `E_y(u)` factor from the
underlying normal-ordering identities is deduced from the Jacobi identity in a torsion-free Lie
ring, so none of the theorems requires extra bracket hypotheses beyond those of the product
straightening rules.

## Main results

* `TauCeti.dividedPower_zsmul_smul_mem`, `TauCeti.baseChangeExpHom_zsmul`,
  `TauCeti.commute_baseChangeExpHom`: integer scaling and commutation for `baseChangeExpHom`.
* `TauCeti.UniversalEnvelopingAlgebra.zsmul_lie_eq_zero_of_zsmul_lie_eq_two`,
  `TauCeti.UniversalEnvelopingAlgebra.zsmul_lie_eq_zero_of_g2_short_pair`,
  `TauCeti.UniversalEnvelopingAlgebra.zsmul_lie_eq_zsmul_of_lie_eq_three_nsmul`: Jacobi identities
  in torsion-free Lie rings eliminating redundant vanishing-bracket assumptions.
* `TauCeti.UniversalEnvelopingAlgebra.commute_baseChangeExpHom_of_lie_eq_zero`,
  `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_baseChangeExpHom_of_lie_eq`,
  `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_baseChangeExpHom_of_lie_lie_eq`,
  `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_baseChangeExpHom_of_lie_lie_rev_eq`,
  `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_baseChangeExpHom_of_g2_short_pair`,
  `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul`,
  `TauCeti.UniversalEnvelopingAlgebra.commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul_rev`:
  Steinberg's Chevalley commutator formula across all root-string configurations.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemma 15.
* R. W. Carter, *Simple Groups of Lie Type*, §4.2 and Theorem 5.2.2.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §§25--27.
* J. C. Jantzen, *Representations of Algebraic Groups*, II.1.
-/

public section

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
    ∀ n, ∀ v ∈ M, Associative.dividedPower n (c • x) • v ∈ M := by
  intro n v hv
  rw [Associative.dividedPower_zsmul, smul_assoc]
  exact zsmul_mem (hM n v hv) _

attribute [local instance high] Algebra.toModule

section BaseChangeHom

variable {R : Type v} [CommRing R] [Algebra ℤ R]

/-- Rescaling a nilpotent operator by an integer `c` rescales the additive parameter of its
divided-power one-parameter subgroup `baseChangeExpHom` by `c`. -/
theorem baseChangeExpHom_zsmul (c : ℤ) {x : A} (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hcM : ∀ n, ∀ v ∈ M, Associative.dividedPower n (c • x) • v ∈ M)
    (hx : IsNilpotent x) (hc : IsNilpotent (c • x)) (t : Multiplicative R) :
    baseChangeExpHom (c • x) M hcM hc t =
      baseChangeExpHom x M hM hx (Multiplicative.ofAdd ((c : R) * Multiplicative.toAdd t)) := by
  refine LinearEquiv.toLinearMap_inj.mp ?_
  rw [baseChangeExpHom_toLinearMap, baseChangeExpHom_toLinearMap, toAdd_ofAdd]
  exact baseChangeExp_zsmul c M hM hcM hx (Multiplicative.toAdd t)

/-- Form of `TauCeti.baseChangeExpHom_zsmul` evaluated at `Multiplicative.ofAdd r`. -/
theorem baseChangeExpHom_zsmul_ofAdd (c : ℤ) {x : A} (M : S)
    (hM : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hcM : ∀ n, ∀ v ∈ M, Associative.dividedPower n (c • x) • v ∈ M)
    (hx : IsNilpotent x) (hc : IsNilpotent (c • x)) (r : R) :
    baseChangeExpHom (c • x) M hcM hc (Multiplicative.ofAdd r) =
      baseChangeExpHom x M hM hx (Multiplicative.ofAdd ((c : R) * r)) := by
  simpa only [toAdd_ofAdd] using baseChangeExpHom_zsmul c M hM hcM hx hc (Multiplicative.ofAdd r)

/-- One-parameter subgroups attached to commuting nilpotent operators commute. -/
theorem commute_baseChangeExpHom {x y : A} (M : S) (hxy : Commute x y)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (t u : Multiplicative R) :
    Commute (baseChangeExpHom x M hMx hx t) (baseChangeExpHom y M hMy hy u) := by
  refine LinearEquiv.toLinearMap_inj.mp ?_
  change (baseChangeExpHom x M hMx hx t).toLinearMap *
      (baseChangeExpHom y M hMy hy u).toLinearMap =
    (baseChangeExpHom y M hMy hy u).toLinearMap *
      (baseChangeExpHom x M hMx hx t).toLinearMap
  rw [baseChangeExpHom_toLinearMap, baseChangeExpHom_toLinearMap]
  exact commute_baseChangeExp M hxy hMx hMy (Multiplicative.toAdd t) (Multiplicative.toAdd u)

/-- **Class-two multiplication law for `baseChangeExpHom`.** If `x * y = y * x + z` with `z`
commuting with both `x` and `y`, then `E_x(t) E_y(u) = E_y(u) E_z(t * u) E_x(t)`. -/
theorem baseChangeExpHom_mul_of_commutator_eq {x y z : A} (M : S)
    (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z)
    (t u : Multiplicative R) :
    baseChangeExpHom x M hMx hx t * baseChangeExpHom y M hMy hy u =
      baseChangeExpHom y M hMy hy u *
        baseChangeExpHom z M hMz hz
          (Multiplicative.ofAdd (Multiplicative.toAdd t * Multiplicative.toAdd u)) *
        baseChangeExpHom x M hMx hx t := by
  refine LinearEquiv.toLinearMap_inj.mp ?_
  change (baseChangeExpHom x M hMx hx t).toLinearMap *
      (baseChangeExpHom y M hMy hy u).toLinearMap =
    (baseChangeExpHom y M hMy hy u).toLinearMap *
      (baseChangeExpHom z M hMz hz
        (Multiplicative.ofAdd (Multiplicative.toAdd t * Multiplicative.toAdd u))).toLinearMap *
      (baseChangeExpHom x M hMx hx t).toLinearMap
  rw [baseChangeExpHom_toLinearMap, baseChangeExpHom_toLinearMap,
    baseChangeExpHom_toLinearMap, toAdd_ofAdd]
  exact baseChangeExp_mul_baseChangeExp_of_commutator_eq M hxy hxz hyz hx hy hMx hMy hMz
    (Multiplicative.toAdd t) (Multiplicative.toAdd u)

/-- **Class-two element-commutator relation for `baseChangeExpHom`.** If `x * y = y * x + z` with
`z` commuting with both `x` and `y`, then `⁅E_x(t), E_y(u)⁆ = E_z(t * u)`. -/
theorem commutatorElement_baseChangeExpHom_of_commutator_eq {x y z : A} (M : S)
    (hxy : x * y = y * x + z) (hxz : Commute x z) (hyz : Commute y z)
    (hMx : ∀ n, ∀ v ∈ M, Associative.dividedPower n x • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M, Associative.dividedPower n y • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M, Associative.dividedPower n z • v ∈ M)
    (hx : IsNilpotent x) (hy : IsNilpotent y) (hz : IsNilpotent z)
    (t u : Multiplicative R) :
    ⁅baseChangeExpHom x M hMx hx t, baseChangeExpHom y M hMy hy u⁆ =
      baseChangeExpHom z M hMz hz
        (Multiplicative.ofAdd (Multiplicative.toAdd t * Multiplicative.toAdd u)) := by
  rw [commutatorElement_def,
    baseChangeExpHom_mul_of_commutator_eq M hxy hxz hyz hMx hMy hMz hx hy hz t u,
    mul_inv_cancel_right,
    (commute_baseChangeExpHom M hyz hMy hMz hy hz u _).eq, mul_inv_cancel_right]

end BaseChangeHom

end TauCeti

namespace TauCeti.UniversalEnvelopingAlgebra

section GroupHelpers

private theorem conj_mul_two_cancel {G : Type*} [Group G] {y a b : G}
    (hya : Commute y a) (hyb : Commute y b) :
    y * a * b * y⁻¹ = a * b := by
  rw [mul_assoc y a b, (hya.mul_right hyb).eq, mul_inv_cancel_right]

private theorem conj_mul_g2_short_pair_cancel {G : Type*} [Group G] {y y' a b s₁ s₂ : G}
    (hy : y * y' = 1) (hay : a * y' = y' * s₁ * a) (hby : Commute b y') (hsy : Commute s₂ y')
    (hsa : Commute s₁ a) (hsb : Commute s₁ b) :
    y * a * b * s₂ * y' = a * b * (s₁ * s₂) := by
  calc
    y * a * b * s₂ * y' = y * a * b * (y' * s₂) := by rw [mul_assoc _ s₂, hsy.eq]
    _ = y * (a * y') * b * s₂ := by
      rw [← mul_assoc (y * a * b), mul_assoc (y * a) b y', hby.eq,
        ← mul_assoc (y * a) y' b, mul_assoc y a y']
    _ = s₁ * a * b * s₂ := by
      rw [hay, ← mul_assoc y (y' * s₁) a, ← mul_assoc y y' s₁, hy, one_mul]
    _ = a * b * (s₁ * s₂) := by
      rw [hsa.eq, mul_assoc a s₁ b, hsb.eq, ← mul_assoc a b s₁, mul_assoc]

private theorem conj_mul_g2_cancel {G : Type*} [Group G] {y y' a b c d : G}
    (hy : y * y' = 1) (hcy : c * y' = y' * d * c) (hdy : Commute d y') (hby : Commute b y')
    (hay : Commute a y') (hdc : Commute d c) :
    y * a * b * c * d * y' = a * b * c * (d * d) := by
  calc
    y * a * b * c * d * y' = y * a * b * (c * y') * d := by
      rw [mul_assoc _ d y', hdy.eq, ← mul_assoc (y * a * b * c) y' d,
        mul_assoc (y * a * b) c y']
    _ = y * a * b * y' * d * c * d := by
      rw [hcy, ← mul_assoc (y * a * b) (y' * d) c, ← mul_assoc (y * a * b) y' d]
    _ = a * b * d * c * d := by
      rw [mul_assoc (y * a) b y', hby.eq, ← mul_assoc (y * a) y' b,
        mul_assoc y a y', hay.eq, ← mul_assoc y y' a, hy, one_mul]
    _ = a * b * c * (d * d) := by
      rw [mul_assoc (a * b) d c, hdc.eq, ← mul_assoc (a * b) c d, mul_assoc]

private theorem reorder_g2_rev {G : Type*} [Group G] {a b c d₁ d₂ : G}
    (hba : b * a = a * b * d₂) (hd₁c : Commute d₁ c) (hd₁b : Commute d₁ b)
    (hd₁a : Commute d₁ a) (hca : Commute c a) (hcb : Commute c b) :
    d₁ * (c * (b * a)) = a * b * c * (d₂ * d₁) := by
  calc
    d₁ * (c * (b * a)) = c * (b * a) * d₁ := by
      rw [← mul_assoc d₁ c, hd₁c.eq, mul_assoc c d₁ (b * a), ← mul_assoc d₁ b a,
        hd₁b.eq, mul_assoc b d₁ a, hd₁a.eq, ← mul_assoc b a d₁, ← mul_assoc c (b * a) d₁]
    _ = c * a * b * (d₂ * d₁) := by
      rw [hba, ← mul_assoc c (a * b) d₂, ← mul_assoc c a b, mul_assoc (c * a * b) d₂ d₁]
    _ = a * b * c * (d₂ * d₁) := by
      rw [hca.eq, mul_assoc a c b, hcb.eq, ← mul_assoc a b c]

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
  have hyw' : ⁅y, d • w⁆ = 0 := by rw [lie_zsmul, hyw]
  have hxw' : ⁅x, d • w⁆ = 0 := by rw [lie_zsmul, hxw, smul_zero]
  calc
    (c * d) • ⁅z, w⁆ = ⁅c • z, d • w⁆ := by rw [zsmul_lie, lie_zsmul, mul_zsmul]
    _ = ⁅⁅x, y⁆, d • w⁆ := by rw [hxy]
    _ = 0 := by rw [lie_lie, hyw', hxw', lie_zero, lie_zero, sub_self]

/-- In a torsion-free Lie ring, the short-pair bracket hypotheses
`⁅x, y⁆ = (2 * c) • z`, `c • ⁅x, z⁆ = (3 * d) • w`, `c • ⁅z, y⁆ = (3 * a) • s`, and `⁅x, s⁆ = 0`
force `d • ⁅y, w⁆ = 0` by the Jacobi identity. -/
theorem zsmul_lie_eq_zero_of_g2_short_pair {x y z w s : L} {c d a : ℤ}
    (hxy : ⁅x, y⁆ = (2 * c) • z) (hxz : c • ⁅x, z⁆ = (3 * d) • w)
    (hzy : c • ⁅z, y⁆ = (3 * a) • s) (hxs : ⁅x, s⁆ = 0) :
    d • ⁅y, w⁆ = 0 := by
  refine (IsAddTorsionFree.zsmul_eq_zero_iff_right (n := (3 : ℤ)) (by decide)).mp ?_
  have hyz : c • ⁅y, z⁆ = -((3 * a) • s) := by rw [← lie_skew y z, smul_neg, hzy]
  calc
    (3 : ℤ) • (d • ⁅y, w⁆) = ⁅y, (3 * d) • w⁆ := by rw [← mul_zsmul, lie_zsmul]
    _ = c • ⁅y, ⁅x, z⁆⁆ := by rw [← hxz, lie_zsmul]
    _ = c • ⁅⁅y, x⁆, z⁆ + ⁅x, c • ⁅y, z⁆⁆ := by rw [leibniz_lie, smul_add, lie_zsmul]
    _ = 0 := by
      rw [← lie_skew y x, hxy, neg_lie, zsmul_lie, lie_self, hyz, lie_neg, lie_zsmul, hxs]
      simp

/-- In a torsion-free Lie ring, under the type-`G₂` scaled bracket hypotheses
`⁅x, y⁆ = c • z`, `c • ⁅x, z⁆ = (2 * d) • w`, `d • ⁅x, w⁆ = (3 * a) • m`,
`(d * c) • ⁅w, z⁆ = (3 * b) • o`, and `⁅y, z⁆ = 0`, the Jacobi identity gives
`a • ⁅y, m⁆ = b • o`. -/
theorem zsmul_lie_eq_zsmul_of_lie_eq_three_nsmul {x y z w m o : L} {c d a b : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : c • ⁅x, z⁆ = (2 * d) • w)
    (hxw : d • ⁅x, w⁆ = (3 * a) • m) (hwz : (d * c) • ⁅w, z⁆ = (3 * b) • o)
    (hyz : ⁅y, z⁆ = 0) :
    a • ⁅y, m⁆ = b • o := by
  have hyw : d • ⁅y, w⁆ = 0 := zsmul_lie_eq_zero_of_zsmul_lie_eq_two hxy hxz hyz
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
    (hwz : (d * c) • ⁅w, z⁆ = (3 * b) • o) (hyz : ⁅y, z⁆ = 0) :
    b • ⁅y, o⁆ = 0 := by
  have hyw : d • ⁅y, w⁆ = 0 := zsmul_lie_eq_zero_of_zsmul_lie_eq_two hxy hxz hyz
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
    (hzw : (d * c) • ⁅z, w⁆ = (3 * b) • o) (hyo : ⁅y, o⁆ = 0) :
    (a * c) • ⁅m, z⁆ = 0 := by
  have hzm : (a * c) • ⁅z, m⁆ = 0 := by
    have h1 : d • ⁅c • ⁅z, y⁆, w⁆ = c • (d • ⁅⁅z, y⁆, w⁆) := by
      rw [zsmul_lie, ← mul_zsmul, ← mul_zsmul, mul_comm d c]
    have h2 : ⁅y, (d * c) • ⁅z, w⁆⁆ = c • (d • ⁅y, ⁅z, w⁆⁆) := by
      rw [lie_zsmul, ← mul_zsmul, mul_comm c d]
    refine (IsAddTorsionFree.zsmul_eq_zero_iff_right (n := (3 : ℤ)) (by decide)).mp ?_
    calc
      (3 : ℤ) • ((a * c) • ⁅z, m⁆) = c • ⁅z, (3 * a) • m⁆ := by
        rw [lie_zsmul, ← mul_zsmul, ← mul_zsmul]
        congr 1
        ring
      _ = c • (d • ⁅z, ⁅y, w⁆⁆) := by rw [← hyw, lie_zsmul]
      _ = c • (d • ⁅⁅z, y⁆, w⁆) + c • (d • ⁅y, ⁅z, w⁆⁆) := by rw [leibniz_lie, smul_add, smul_add]
      _ = d • ⁅c • ⁅z, y⁆, w⁆ + ⁅y, (d * c) • ⁅z, w⁆⁆ := by rw [← h1, ← h2]
      _ = 0 := by rw [hzy, zsmul_lie, lie_self, hzw, lie_zsmul, hyo]; simp
  rw [← lie_skew m z, smul_neg, hzm, neg_zero]

end Jacobi

section DividedPowerCommutator

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L]
variable {A : Type*} [Ring A] [Algebra ℚ A]
variable {V : Type*} [AddCommGroup V] [Module A V]
variable {S : Type*} [SetLike S V] [AddSubgroupClass S V]
variable {F : Type*} [FunLike F (_root_.UniversalEnvelopingAlgebra ℚ L) A]
  [NonUnitalRingHomClass F (_root_.UniversalEnvelopingAlgebra ℚ L) A]

attribute [local instance high] Algebra.toModule

omit [Algebra ℚ A] in
/-- If `(p * q) • ⁅a, b⁆ = 0`, the integer-scaled images of `a` and `b` commute under any ring
homomorphism out of `U(L)`. -/
theorem commute_zsmul_of_zsmul_lie_eq_zero (ρ : F) {a b : L} {p q : ℤ}
    (hab : (p * q) • ⁅a, b⁆ = 0) :
    Commute (p • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ a))
      (q • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ b)) := by
  have h := zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq (R := ℚ) ρ
    (p := p) (q := q) (b' := a) (r := 0) (n := 0) (by simpa using hab)
  rw [zero_smul, add_zero] at h
  exact h

variable {R : Type*} [CommRing R] [Algebra ℤ R]

/-- **Commuting Chevalley relation for `baseChangeExpHom`.** If `⁅x, y⁆ = 0`, the corresponding
divided-power one-parameter subgroups commute. -/
theorem commute_baseChangeExpHom_of_lie_eq_zero (ρ : F) (M : S) {x y : L} (hxy : ⁅x, y⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) • v ∈ M)
    (hx : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)))
    (hy : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)))
    (t u : Multiplicative R) :
    Commute
      (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t)
      (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u) :=
  commute_baseChangeExpHom M (commute_of_lie_eq_zero ρ hxy) hMx hMy hx hy t u

/-- **Steinberg's class-two Chevalley commutator relation for `baseChangeExpHom`.** If
`⁅x, y⁆ = c • z` with `⁅x, z⁆ = ⁅y, z⁆ = 0`, then `⁅E_x(t), E_y(u)⁆ = E_z(c t u)`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_eq (ρ : F) (M : S) {x y z : L} {c : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : ⁅x, z⁆ = 0) (hyz : ⁅y, z⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) • v ∈ M)
    (hx : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)))
    (hy : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)))
    (hz : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)))
    (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t,
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMz hz
        (Multiplicative.ofAdd ((c : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u))) := by
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  rw [← baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c)]
  exact commutatorElement_baseChangeExpHom_of_commutator_eq M
    (mul_eq_mul_add_zsmul_of_lie_eq ρ hxy)
    ((commute_of_lie_eq_zero ρ hxz).smul_right c)
    ((commute_of_lie_eq_zero ρ hyz).smul_right c)
    hMx hMy hMcz hx hy (hz.smul c) t u

/-- **Steinberg's Chevalley commutator relation for the chain `α + β, 2α + β`.** If
`⁅x, y⁆ = c • z` and `⁅x, ⁅x, y⁆⁆ = (2 * d) • w` with `⁅x, w⁆ = ⁅y, z⁆ = 0`, then
`⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(d t² u)`. The vanishing of `d • ⁅y, w⁆` follows automatically
from the Jacobi identity. -/
theorem commutatorElement_baseChangeExpHom_of_lie_lie_eq (ρ : F) (M : S) {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxxy : ⁅x, ⁅x, y⁆⁆ = (2 * d) • w)
    (hxw : ⁅x, w⁆ = 0) (hyz : ⁅y, z⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) • v ∈ M)
    (hx : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)))
    (hy : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)))
    (hz : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)))
    (hw : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)))
    (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t,
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMz hz
          (Multiplicative.ofAdd ((c : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u))) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMw hw
          (Multiplicative.ofAdd
            ((d : R) * (Multiplicative.toAdd t ^ 2 * Multiplicative.toAdd u))) := by
  have htf : HasUniqueDiv L := .of_module_rat L
  have hxz : c • ⁅x, z⁆ = (2 * d) • w := by rw [← lie_zsmul, ← hxy, hxxy]
  have hyw : d • ⁅y, w⁆ = 0 := zsmul_lie_eq_zero_of_zsmul_lie_eq_two hxy hxz hyz
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  have hMdw := dividedPower_zsmul_smul_mem d M hMw
  let tr := Multiplicative.toAdd t
  let ur := Multiplicative.toAdd u
  have hmul :
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t *
          baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u =
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u *
          baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
            (Multiplicative.ofAdd (tr * ur)) *
          baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
            (Multiplicative.ofAdd (tr ^ 2 * ur)) *
          baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t := by
    refine LinearEquiv.toLinearMap_inj.mp ?_
    change (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t).toLinearMap *
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u).toLinearMap =
      (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u).toLinearMap *
        (baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (tr * ur))).toLinearMap *
        (baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (tr ^ 2 * ur))).toLinearMap *
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t).toLinearMap
    simp only [baseChangeExpHom_toLinearMap, toAdd_ofAdd]
    have hxz_ring :
        ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
            (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) =
          c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z) *
              ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) +
            2 • (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) := by
      simpa only [one_zsmul, one_mul] using
        zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ (p := 1) (q := c) (r := d) (n := 2)
          (by simpa using hxz)
    exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_two_nsmul M
      (mul_eq_mul_add_zsmul_of_lie_eq ρ hxy) hxz_ring
      ((commute_of_lie_eq_zero ρ hxw).smul_right d)
      ((commute_of_lie_eq_zero ρ hyz).smul_right c)
      hx hy (hz.smul c) hMx hMy hMcz hMdw tr ur
  have hcomm_yz :
      Commute
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u)
        (baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (tr * ur))) :=
    commute_baseChangeExpHom M ((commute_of_lie_eq_zero ρ hyz).smul_right c) hMy hMcz hy
      (hz.smul c) u _
  have hcomm_yw :
      Commute
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u)
        (baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (tr ^ 2 * ur))) := by
    simpa only [one_zsmul] using
      commute_baseChangeExpHom M
        (commute_zsmul_of_zsmul_lie_eq_zero ρ (p := 1) (q := d) (by simpa using hyw))
        (dividedPower_zsmul_smul_mem 1 M hMy) hMdw (hy.smul 1) (hw.smul d) u _
  rw [commutatorElement_def, hmul, mul_inv_cancel_right,
    conj_mul_two_cancel hcomm_yz hcomm_yw,
    baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c),
    baseChangeExpHom_zsmul_ofAdd d M hMw hMdw hw (hw.smul d)]

/-- **Steinberg's Chevalley commutator relation for the reversed chain `α + β, α + 2β`.** If
`⁅x, y⁆ = c • z` and `⁅y, ⁅y, x⁆⁆ = (2 * d) • w` with `⁅y, w⁆ = ⁅x, z⁆ = 0`, then
`⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(-d t u²)`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_lie_rev_eq (ρ : F) (M : S)
    {x y z w : L} {c d : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hyyx : ⁅y, ⁅y, x⁆⁆ = (2 * d) • w)
    (hyw : ⁅y, w⁆ = 0) (hxz : ⁅x, z⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) • v ∈ M)
    (hx : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)))
    (hy : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)))
    (hz : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)))
    (hw : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)))
    (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t,
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMz hz
          (Multiplicative.ofAdd ((c : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u))) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMw hw
          (Multiplicative.ofAdd
            ((-d : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u ^ 2))) := by
  have htf : HasUniqueDiv L := .of_module_rat L
  have hyx : ⁅y, x⁆ = (-c) • z := by rw [← lie_skew y x, hxy, neg_zsmul]
  have hyz : (-c) • ⁅y, z⁆ = (2 * d) • w := by rw [← lie_zsmul, ← hyx, hyyx]
  have hxw_d : d • ⁅x, w⁆ = 0 := zsmul_lie_eq_zero_of_zsmul_lie_eq_two hyx hyz hxz
  have hzw : (c * (-d)) • ⁅z, w⁆ = 0 := by
    have h := zsmul_lie_eq_zero_of_lie_eq hyx hyw hxw_d
    rwa [neg_mul_comm] at h
  have hrev := commutatorElement_baseChangeExpHom_of_lie_lie_eq ρ M hyx hyyx hyw hxz
    hMy hMx hMz hMw hy hx hz hw u t
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  have hMdw := dividedPower_zsmul_smul_mem (-d) M hMw
  have hp_w :
      (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMw hw
          (Multiplicative.ofAdd
            ((d : R) * (Multiplicative.toAdd u ^ 2 * Multiplicative.toAdd t))))⁻¹ =
        baseChangeExpHom ((-d) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw
          (hw.smul (-d))
          (Multiplicative.ofAdd (Multiplicative.toAdd t * Multiplicative.toAdd u ^ 2)) := by
    rw [← map_inv, ← ofAdd_neg,
      baseChangeExpHom_zsmul_ofAdd (-d) M hMw hMdw hw (hw.smul (-d))]
    have harg :
        Multiplicative.ofAdd
            (-((d : R) * (Multiplicative.toAdd u ^ 2 * Multiplicative.toAdd t))) =
          Multiplicative.ofAdd
            (((-d : ℤ) : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u ^ 2)) :=
      congrArg Multiplicative.ofAdd (by push_cast; ring)
    exact congrArg (baseChangeExpHom _ M hMw hw) harg
  have hp_z :
      (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMz hz
          (Multiplicative.ofAdd
            (((-c : ℤ) : R) * (Multiplicative.toAdd u * Multiplicative.toAdd t))))⁻¹ =
        baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (Multiplicative.toAdd t * Multiplicative.toAdd u)) := by
    rw [← map_inv, ← ofAdd_neg,
      baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c)]
    have harg :
        Multiplicative.ofAdd
            (-(((-c : ℤ) : R) * (Multiplicative.toAdd u * Multiplicative.toAdd t))) =
          Multiplicative.ofAdd ((c : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u)) :=
      congrArg Multiplicative.ofAdd (by push_cast; ring)
    exact congrArg (baseChangeExpHom _ M hMz hz) harg
  rw [← commutatorElement_inv, hrev, mul_inv_rev, hp_w, hp_z,
    (commute_baseChangeExpHom M (commute_zsmul_of_zsmul_lie_eq_zero ρ hzw).symm
      hMdw hMcz (hw.smul (-d)) (hz.smul c) _ _).eq,
    baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c),
    baseChangeExpHom_zsmul_ofAdd (-d) M hMw hMdw hw (hw.smul (-d))]
  have harg :
      Multiplicative.ofAdd
          (((-d : ℤ) : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u ^ 2)) =
        Multiplicative.ofAdd ((-d : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u ^ 2)) :=
    congrArg Multiplicative.ofAdd (by push_cast; rfl)
  rw [harg]

/-- **Steinberg's Chevalley commutator relation for the type-`G₂` short pair.** For roots
`α, α + β, 2α + β, 3α + β, 3α + 2β` corresponding to `x, y, z, w, s` with
`⁅x, y⁆ = (2 * c) • z`, `c • ⁅x, z⁆ = (3 * d) • w`, and `c • ⁅z, y⁆ = (3 * a) • s`, the element
commutator is `⁅E_x(t), E_y(u)⁆ = E_z(2c t u) E_w(3d t² u) E_s(-3a t u²)`. -/
theorem commutatorElement_baseChangeExpHom_of_g2_short_pair (ρ : F) (M : S)
    {x y z w s : L} {c d a : ℤ}
    (hxy : ⁅x, y⁆ = (2 * c) • z) (hxz : c • ⁅x, z⁆ = (3 * d) • w)
    (hzy : c • ⁅z, y⁆ = (3 * a) • s)
    (hxw : ⁅x, w⁆ = 0) (hxs : ⁅x, s⁆ = 0) (hys : ⁅y, s⁆ = 0)
    (hzw : ⁅z, w⁆ = 0) (hzs : ⁅z, s⁆ = 0) (hws : ⁅w, s⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) • v ∈ M)
    (hMs : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ s)) • v ∈ M)
    (hx : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)))
    (hy : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)))
    (hz : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)))
    (hw : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)))
    (hs : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ s)))
    (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t,
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMz hz
          (Multiplicative.ofAdd
            ((c : R) * (2 * Multiplicative.toAdd t * Multiplicative.toAdd u))) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMw hw
          (Multiplicative.ofAdd
            ((d : R) * (3 * Multiplicative.toAdd t ^ 2 * Multiplicative.toAdd u))) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ s)) M hMs hs
          (Multiplicative.ofAdd
            ((-a : R) * (3 * Multiplicative.toAdd t * Multiplicative.toAdd u ^ 2))) := by
  have htf : HasUniqueDiv L := .of_module_rat L
  have hyw : d • ⁅y, w⁆ = 0 := zsmul_lie_eq_zero_of_g2_short_pair hxy hxz hzy hxs
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  have hMdw := dividedPower_zsmul_smul_mem d M hMw
  have hMas := dividedPower_zsmul_smul_mem a M hMs
  have hM3as := dividedPower_zsmul_smul_mem (3 * a) M hMs
  let tr := Multiplicative.toAdd t
  let ur := Multiplicative.toAdd u
  have hmul :
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t *
          baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u =
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u *
          baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
            (Multiplicative.ofAdd (2 * tr * ur)) *
          baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
            (Multiplicative.ofAdd (3 * tr ^ 2 * ur)) *
          baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ s)) M hMas (hs.smul a)
            (Multiplicative.ofAdd (3 * tr * ur ^ 2)) *
          baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t := by
    refine LinearEquiv.toLinearMap_inj.mp ?_
    change (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t).toLinearMap *
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u).toLinearMap =
      (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u).toLinearMap *
        (baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (2 * tr * ur))).toLinearMap *
        (baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (3 * tr ^ 2 * ur))).toLinearMap *
        (baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ s)) M hMas (hs.smul a)
          (Multiplicative.ofAdd (3 * tr * ur ^ 2))).toLinearMap *
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t).toLinearMap
    simp only [baseChangeExpHom_toLinearMap, toAdd_ofAdd]
    have hxy_r :
        ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
            ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y) =
          ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y) *
              ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) +
            2 • (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) := by
      simpa only [one_zsmul] using
        zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ (p := 1) (q := 1) (r := c) (n := 2)
          (by simpa using hxy)
    have hxz_r :
        ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
            (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) =
          c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z) *
              ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) +
            3 • (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) := by
      simpa only [one_zsmul] using
        zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ (p := 1) (q := c) (r := d) (n := 3)
          (by simpa using hxz)
    have hzy_r :
        (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) *
            ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y) =
          ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y) *
              (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) +
            3 • (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ s)) := by
      simpa only [one_zsmul] using
        zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ (p := c) (q := 1) (r := a) (n := 3)
          (by simpa using hzy)
    exact baseChangeExp_mul_baseChangeExp_of_g2_short_pair M hxy_r hxz_r hzy_r
      ((commute_of_lie_eq_zero ρ hxw).smul_right d)
      ((commute_of_lie_eq_zero ρ hxs).smul_right a)
      ((commute_of_lie_eq_zero ρ hys).smul_right a)
      (((commute_of_lie_eq_zero ρ hzw).smul_left c).smul_right d)
      (((commute_of_lie_eq_zero ρ hzs).smul_left c).smul_right a)
      (((commute_of_lie_eq_zero ρ hws).smul_left d).smul_right a)
      hx hy (hz.smul c) hMx hMy hMcz hMdw hMas tr ur
  have hcomm_yas :
      Commute
        (baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ s)) M hMas (hs.smul a)
          (Multiplicative.ofAdd (3 * tr * ur ^ 2)))
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁻¹) :=
    commute_baseChangeExpHom M ((commute_of_lie_eq_zero ρ hys).smul_right a).symm
      hMas hMy (hs.smul a) hy _ u⁻¹
  have hcomm_ydw :
      Commute
        (baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (3 * tr ^ 2 * ur)))
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁻¹) := by
    simpa only [one_zsmul] using
      commute_baseChangeExpHom M
        (commute_zsmul_of_zsmul_lie_eq_zero ρ (p := 1) (q := d) (by simpa using hyw)).symm
        hMdw (dividedPower_zsmul_smul_mem 1 M hMy) (hw.smul d) (hy.smul 1) _ u⁻¹
  have hcomm_zas :
      Commute
        (baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ s)) M hMas (hs.smul a)
          (Multiplicative.ofAdd (-(6 * tr * ur ^ 2))))
        (baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (2 * tr * ur))) :=
    commute_baseChangeExpHom M
      (((commute_of_lie_eq_zero ρ hzs).smul_left c).smul_right a).symm
      hMas hMcz (hs.smul a) (hz.smul c) _ _
  have hcomm_was :
      Commute
        (baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ s)) M hMas (hs.smul a)
          (Multiplicative.ofAdd (-(6 * tr * ur ^ 2))))
        (baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (3 * tr ^ 2 * ur))) :=
    commute_baseChangeExpHom M
      (((commute_of_lie_eq_zero ρ hws).smul_left d).smul_right a).symm
      hMas hMdw (hs.smul a) (hw.smul d) _ _
  have hswap_zy :
      baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (2 * tr * ur)) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁻¹ =
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁻¹ *
        baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ s)) M hMas (hs.smul a)
          (Multiplicative.ofAdd (-(6 * tr * ur ^ 2))) *
        baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (2 * tr * ur)) := by
    have hzy_r :
        (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) *
            ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y) =
          ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y) *
              (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) +
            (3 * a) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ s) := by
      simpa only [one_zsmul, one_nsmul, one_mul] using
        zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ (p := c) (q := 1) (r := 3 * a) (n := 1)
          (by simpa using hzy)
    have hstep := baseChangeExpHom_mul_of_commutator_eq M hzy_r
      (((commute_of_lie_eq_zero ρ hzs).smul_left c).smul_right (3 * a))
      ((commute_of_lie_eq_zero ρ hys).smul_right (3 * a))
      hMcz hMy hM3as (hz.smul c) hy (hs.smul (3 * a))
      (Multiplicative.ofAdd (2 * tr * ur)) u⁻¹
    rw [hstep, baseChangeExpHom_zsmul_ofAdd (3 * a) M hMs hM3as hs (hs.smul (3 * a)),
      baseChangeExpHom_zsmul_ofAdd a M hMs hMas hs (hs.smul a)]
    have harg :
        Multiplicative.ofAdd
            (((3 * a : ℤ) : R) *
              (Multiplicative.toAdd (Multiplicative.ofAdd (2 * tr * ur)) *
                Multiplicative.toAdd u⁻¹)) =
          Multiplicative.ofAdd ((a : R) * -(6 * tr * ur ^ 2)) :=
      congrArg Multiplicative.ofAdd (by simp only [toAdd_ofAdd, toAdd_inv]; push_cast; ring)
    rw [harg]
  have hy_inv :
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁻¹ = 1 := by
    rw [← (baseChangeExpHom _ M hMy hy).map_mul, mul_inv_cancel, map_one]
  rw [commutatorElement_def, hmul, mul_inv_cancel_right,
    ← _root_.map_inv (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy) u,
    conj_mul_g2_short_pair_cancel hy_inv hswap_zy hcomm_ydw hcomm_yas hcomm_zas hcomm_was,
    ← (baseChangeExpHom _ M hMas (hs.smul a)).map_mul, ← ofAdd_add,
    baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c),
    baseChangeExpHom_zsmul_ofAdd d M hMw hMdw hw (hw.smul d),
    baseChangeExpHom_zsmul_ofAdd a M hMs hMas hs (hs.smul a)]
  have harg :
      Multiplicative.ofAdd ((a : R) * (-(6 * tr * ur ^ 2) + 3 * tr * ur ^ 2)) =
        Multiplicative.ofAdd ((-a : R) * (3 * tr * ur ^ 2)) :=
    congrArg Multiplicative.ofAdd (by ring)
  rw [harg]

/-- **Steinberg's Chevalley commutator relation in type `G₂` (`α` short, `β` long).** Under the
exact scaled and vanishing bracket hypotheses of the product straightening rule, the element
commutator is
`⁅E_x(t), E_y(u)⁆ = E_z(c t u) E_w(d t² u) E_m(a t³ u) E_o(2b t³ u²)`.
The coefficient `2b` on `E_o` arises because commuting `E_y(-u)` past `E_{a • m}(t³ u)` produces a
second factor `E_{b • o}(t³ u²)` via the Jacobi relation `a • ⁅y, m⁆ = b • o`. -/
theorem commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul (ρ : F) (M : S)
    {x y z w m o : L} {c d a b : ℤ}
    (hxy : ⁅x, y⁆ = c • z) (hxz : c • ⁅x, z⁆ = (2 * d) • w)
    (hxw : d • ⁅x, w⁆ = (3 * a) • m) (hwz : (d * c) • ⁅w, z⁆ = (3 * b) • o)
    (hxm : ⁅x, m⁆ = 0) (hxo : ⁅x, o⁆ = 0) (hyz : ⁅y, z⁆ = 0)
    (hwm : ⁅w, m⁆ = 0) (hzo : ⁅z, o⁆ = 0) (hwo : ⁅w, o⁆ = 0) (hmo : ⁅m, o⁆ = 0)
    (hMx : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) • v ∈ M)
    (hMm : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) • v ∈ M)
    (hMo : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) • v ∈ M)
    (hx : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)))
    (hy : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)))
    (hz : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)))
    (hw : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)))
    (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t,
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMz hz
          (Multiplicative.ofAdd ((c : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u))) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMw hw
          (Multiplicative.ofAdd
            ((d : R) * (Multiplicative.toAdd t ^ 2 * Multiplicative.toAdd u))) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMm hm
          (Multiplicative.ofAdd
            ((a : R) * (Multiplicative.toAdd t ^ 3 * Multiplicative.toAdd u))) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMo ho
          (Multiplicative.ofAdd
            (((2 * b : ℤ) : R) * (Multiplicative.toAdd t ^ 3 * Multiplicative.toAdd u ^ 2))) := by
  have htf : HasUniqueDiv L := .of_module_rat L
  have hyw : d • ⁅y, w⁆ = 0 := zsmul_lie_eq_zero_of_zsmul_lie_eq_two hxy hxz hyz
  have hym : a • ⁅y, m⁆ = b • o := zsmul_lie_eq_zsmul_of_lie_eq_three_nsmul hxy hxz hxw hwz hyz
  have hyo : b • ⁅y, o⁆ = 0 := zsmul_lie_fourth_eq_zero_of_lie_eq_three_nsmul hxy hxz hwz hyz
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  have hMdw := dividedPower_zsmul_smul_mem d M hMw
  have hMam := dividedPower_zsmul_smul_mem a M hMm
  have hMbo := dividedPower_zsmul_smul_mem b M hMo
  have hMnbo := dividedPower_zsmul_smul_mem (-b) M hMo
  let tr := Multiplicative.toAdd t
  let ur := Multiplicative.toAdd u
  have hmul :
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t *
          baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u =
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u *
          baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
            (Multiplicative.ofAdd (tr * ur)) *
          baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
            (Multiplicative.ofAdd (tr ^ 2 * ur)) *
          baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMam (hm.smul a)
            (Multiplicative.ofAdd (tr ^ 3 * ur)) *
          baseChangeExpHom (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMbo (ho.smul b)
            (Multiplicative.ofAdd (tr ^ 3 * ur ^ 2)) *
          baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t := by
    refine LinearEquiv.toLinearMap_inj.mp ?_
    change (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t).toLinearMap *
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u).toLinearMap =
      (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u).toLinearMap *
        (baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (tr * ur))).toLinearMap *
        (baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (tr ^ 2 * ur))).toLinearMap *
        (baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMam (hm.smul a)
          (Multiplicative.ofAdd (tr ^ 3 * ur))).toLinearMap *
        (baseChangeExpHom (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMbo (ho.smul b)
          (Multiplicative.ofAdd (tr ^ 3 * ur ^ 2))).toLinearMap *
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t).toLinearMap
    simp only [baseChangeExpHom_toLinearMap, toAdd_ofAdd]
    have hxz_r :
        ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
            (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) =
          c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z) *
              ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) +
            2 • (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) := by
      simpa only [one_zsmul] using
        zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ (p := 1) (q := c) (r := d) (n := 2)
          (by simpa using hxz)
    have hxw_r :
        ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) *
            (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) =
          d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w) *
              ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x) +
            3 • (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) := by
      simpa only [one_zsmul] using
        zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ (p := 1) (q := d) (r := a) (n := 3)
          (by simpa using hxw)
    have hwz_r :
        (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) *
            (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) =
          c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z) *
              (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) +
            3 • (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) := by
      simpa using
        zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ (p := d) (q := c) (r := b) (n := 3)
          (by simpa using hwz)
    exact baseChangeExp_mul_baseChangeExp_of_commutator_eq_three_nsmul M
      (mul_eq_mul_add_zsmul_of_lie_eq ρ hxy) hxz_r hxw_r hwz_r
      ((commute_of_lie_eq_zero ρ hxm).smul_right a)
      ((commute_of_lie_eq_zero ρ hxo).smul_right b)
      ((commute_of_lie_eq_zero ρ hyz).smul_right c)
      (((commute_of_lie_eq_zero ρ hwm).smul_left d).smul_right a)
      (((commute_of_lie_eq_zero ρ hzo).smul_left c).smul_right b)
      (((commute_of_lie_eq_zero ρ hwo).smul_left d).smul_right b)
      (((commute_of_lie_eq_zero ρ hmo).smul_left a).smul_right b)
      hx hy (hz.smul c) (hw.smul d) hMx hMy hMcz hMdw hMam hMbo tr ur
  have hcomm_ybo :
      Commute
        (baseChangeExpHom (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMbo (ho.smul b)
          (Multiplicative.ofAdd (tr ^ 3 * ur ^ 2)))
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁻¹) := by
    simpa only [one_zsmul] using
      commute_baseChangeExpHom M
        (commute_zsmul_of_zsmul_lie_eq_zero ρ (p := 1) (q := b) (by simpa using hyo)).symm
        hMbo (dividedPower_zsmul_smul_mem 1 M hMy) (ho.smul b) (hy.smul 1) _ u⁻¹
  have hcomm_ydw :
      Commute
        (baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (tr ^ 2 * ur)))
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁻¹) := by
    simpa only [one_zsmul] using
      commute_baseChangeExpHom M
        (commute_zsmul_of_zsmul_lie_eq_zero ρ (p := 1) (q := d) (by simpa using hyw)).symm
        hMdw (dividedPower_zsmul_smul_mem 1 M hMy) (hw.smul d) (hy.smul 1) _ u⁻¹
  have hcomm_ycz :
      Commute
        (baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (tr * ur)))
        (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁻¹) :=
    commute_baseChangeExpHom M ((commute_of_lie_eq_zero ρ hyz).smul_right c).symm
      hMcz hMy (hz.smul c) hy _ u⁻¹
  have hcomm_mbo :
      Commute
        (baseChangeExpHom (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMbo (ho.smul b)
          (Multiplicative.ofAdd (tr ^ 3 * ur ^ 2)))
        (baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMam (hm.smul a)
          (Multiplicative.ofAdd (tr ^ 3 * ur))) :=
    commute_baseChangeExpHom M
      (((commute_of_lie_eq_zero ρ hmo).smul_left a).smul_right b).symm
      hMbo hMam (ho.smul b) (hm.smul a) _ _
  have hswap_my :
      baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMam (hm.smul a)
          (Multiplicative.ofAdd (tr ^ 3 * ur)) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁻¹ =
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁻¹ *
        baseChangeExpHom (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMbo (ho.smul b)
          (Multiplicative.ofAdd (tr ^ 3 * ur ^ 2)) *
        baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMam (hm.smul a)
          (Multiplicative.ofAdd (tr ^ 3 * ur)) := by
    have hmy_lie : (a * 1) • ⁅m, y⁆ = ((1 : ℕ) * (-b)) • o := by
      rw [mul_one, ← lie_skew m y, smul_neg, hym]
      simp
    have hmy_r :
        (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) *
            ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y) =
          ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y) *
              (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) +
            (-b) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o) := by
      simpa only [one_zsmul, one_nsmul] using
        zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ hmy_lie
    have hy_nbo : Commute (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y))
        ((-b) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) := by
      simpa only [one_zsmul] using
        commute_zsmul_of_zsmul_lie_eq_zero ρ (p := 1) (q := -b)
          (by rw [one_mul, neg_zsmul, hyo, neg_zero])
    have hstep := baseChangeExpHom_mul_of_commutator_eq M hmy_r
      (((commute_of_lie_eq_zero ρ hmo).smul_left a).smul_right (-b))
      hy_nbo hMam hMy hMnbo (hm.smul a) hy (ho.smul (-b))
      (Multiplicative.ofAdd (tr ^ 3 * ur)) u⁻¹
    rw [hstep, baseChangeExpHom_zsmul_ofAdd (-b) M hMo hMnbo ho (ho.smul (-b)),
      baseChangeExpHom_zsmul_ofAdd b M hMo hMbo ho (ho.smul b)]
    have harg :
        Multiplicative.ofAdd
            (((-b : ℤ) : R) *
              (Multiplicative.toAdd (Multiplicative.ofAdd (tr ^ 3 * ur)) *
                Multiplicative.toAdd u⁻¹)) =
          Multiplicative.ofAdd ((b : R) * (tr ^ 3 * ur ^ 2)) :=
      congrArg Multiplicative.ofAdd (by simp only [toAdd_ofAdd, toAdd_inv]; push_cast; ring)
    rw [harg]
  have hy_inv :
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁻¹ = 1 := by
    rw [← (baseChangeExpHom _ M hMy hy).map_mul, mul_inv_cancel, map_one]
  rw [commutatorElement_def, hmul, mul_inv_cancel_right,
    ← _root_.map_inv (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy) u,
    conj_mul_g2_cancel hy_inv hswap_my hcomm_ybo hcomm_ydw hcomm_ycz hcomm_mbo,
    ← (baseChangeExpHom _ M hMbo (ho.smul b)).map_mul, ← ofAdd_add,
    baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c),
    baseChangeExpHom_zsmul_ofAdd d M hMw hMdw hw (hw.smul d),
    baseChangeExpHom_zsmul_ofAdd a M hMm hMam hm (hm.smul a),
    baseChangeExpHom_zsmul_ofAdd b M hMo hMbo ho (ho.smul b)]
  have harg :
      Multiplicative.ofAdd ((b : R) * (tr ^ 3 * ur ^ 2 + tr ^ 3 * ur ^ 2)) =
        Multiplicative.ofAdd (((2 * b : ℤ) : R) * (tr ^ 3 * ur ^ 2)) :=
    congrArg Multiplicative.ofAdd (by push_cast; ring)
  rw [harg]

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
    (hMx : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) • v ∈ M)
    (hMy : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) • v ∈ M)
    (hMz : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) • v ∈ M)
    (hMw : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) • v ∈ M)
    (hMm : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) • v ∈ M)
    (hMo : ∀ n, ∀ v ∈ M,
      Associative.dividedPower n (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) • v ∈ M)
    (hx : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)))
    (hy : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)))
    (hz : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)))
    (hw : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)))
    (hm : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)))
    (ho : IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)))
    (t u : Multiplicative R) :
    ⁅baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ x)) M hMx hx t,
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ y)) M hMy hy u⁆ =
      baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMz hz
          (Multiplicative.ofAdd ((c : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u))) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMw hw
          (Multiplicative.ofAdd
            ((-d : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u ^ 2))) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMm hm
          (Multiplicative.ofAdd
            ((-a : R) * (Multiplicative.toAdd t * Multiplicative.toAdd u ^ 3))) *
        baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMo ho
          (Multiplicative.ofAdd
            ((b : R) * (Multiplicative.toAdd t ^ 2 * Multiplicative.toAdd u ^ 3))) := by
  have htf : HasUniqueDiv L := .of_module_rat L
  have hyx : ⁅y, x⁆ = (-c) • z := by rw [← lie_skew y x, hxy, neg_zsmul]
  have hyz' : (-c) • ⁅y, z⁆ = (2 * d) • w := by
    rw [← lie_skew y z, smul_neg, neg_zsmul, neg_neg, hzy]
  have hwz' : (d * (-c)) • ⁅w, z⁆ = (3 * b) • o := by
    rw [mul_neg, ← lie_skew w z, smul_neg, neg_zsmul, neg_neg, hzw]
  have hmz : (a * c) • ⁅m, z⁆ = 0 :=
    zsmul_lie_third_eq_zero_of_lie_eq_three_nsmul_rev hzy hyw hzw hyo
  have hrev := commutatorElement_baseChangeExpHom_of_lie_eq_three_nsmul ρ M
    hyx hyz' hyw hwz' hym hyo hxz hwm hzo hwo hmo
    hMy hMx hMz hMw hMm hMo hy hx hz hw hm ho u t
  let tr := Multiplicative.toAdd t
  let ur := Multiplicative.toAdd u
  have hMcz := dividedPower_zsmul_smul_mem c M hMz
  have hMdw := dividedPower_zsmul_smul_mem d M hMw
  have hMam := dividedPower_zsmul_smul_mem a M hMm
  have hMbo := dividedPower_zsmul_smul_mem b M hMo
  have hMn3bo := dividedPower_zsmul_smul_mem (-(3 * b)) M hMo
  rw [← commutatorElement_inv, hrev, mul_inv_rev, mul_inv_rev, mul_inv_rev]
  have hp_o :
      (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMo ho
          (Multiplicative.ofAdd (((2 * b : ℤ) : R) * (ur ^ 3 * tr ^ 2))))⁻¹ =
        baseChangeExpHom (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMbo (ho.smul b)
          (Multiplicative.ofAdd ((-2 : R) * (tr ^ 2 * ur ^ 3))) := by
    rw [← map_inv, ← ofAdd_neg, baseChangeExpHom_zsmul_ofAdd b M hMo hMbo ho (ho.smul b)]
    congr 2; push_cast; ring
  have hp_m :
      (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMm hm
          (Multiplicative.ofAdd ((a : R) * (ur ^ 3 * tr))))⁻¹ =
        baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMam (hm.smul a)
          (Multiplicative.ofAdd (-(tr * ur ^ 3))) := by
    rw [← map_inv, ← ofAdd_neg, baseChangeExpHom_zsmul_ofAdd a M hMm hMam hm (hm.smul a)]
    congr 2; ring
  have hp_w :
      (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMw hw
          (Multiplicative.ofAdd ((d : R) * (ur ^ 2 * tr))))⁻¹ =
        baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (-(tr * ur ^ 2))) := by
    rw [← map_inv, ← ofAdd_neg, baseChangeExpHom_zsmul_ofAdd d M hMw hMdw hw (hw.smul d)]
    congr 2; ring
  have hp_z :
      (baseChangeExpHom (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMz hz
          (Multiplicative.ofAdd (((-c : ℤ) : R) * (ur * tr))))⁻¹ =
        baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (tr * ur)) := by
    rw [← map_inv, ← ofAdd_neg, baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c)]
    congr 2; push_cast; ring
  rw [hp_o, hp_m, hp_w, hp_z]
  have hcomm_om :
      Commute
        (baseChangeExpHom (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMbo (ho.smul b)
          (Multiplicative.ofAdd ((-2 : R) * (tr ^ 2 * ur ^ 3))))
        (baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMam (hm.smul a)
          (Multiplicative.ofAdd (-(tr * ur ^ 3)))) :=
    commute_baseChangeExpHom M
      (((commute_of_lie_eq_zero ρ hmo).smul_left a).smul_right b).symm
      hMbo hMam (ho.smul b) (hm.smul a) _ _
  have hcomm_ow :
      ∀ r, Commute
        (baseChangeExpHom (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMbo (ho.smul b) r)
        (baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (-(tr * ur ^ 2)))) :=
    fun r => commute_baseChangeExpHom M
      (((commute_of_lie_eq_zero ρ hwo).smul_left d).smul_right b).symm
      hMbo hMdw (ho.smul b) (hw.smul d) r _
  have hcomm_oz :
      Commute
        (baseChangeExpHom (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMbo (ho.smul b)
          (Multiplicative.ofAdd ((-2 : R) * (tr ^ 2 * ur ^ 3))))
        (baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (tr * ur))) :=
    commute_baseChangeExpHom M
      (((commute_of_lie_eq_zero ρ hzo).smul_left c).smul_right b).symm
      hMbo hMcz (ho.smul b) (hz.smul c) _ _
  have hcomm_mz :
      Commute
        (baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMam (hm.smul a)
          (Multiplicative.ofAdd (-(tr * ur ^ 3))))
        (baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (tr * ur))) :=
    commute_baseChangeExpHom M (commute_zsmul_of_zsmul_lie_eq_zero ρ hmz)
      hMam hMcz (hm.smul a) (hz.smul c) _ _
  have hcomm_mw :
      Commute
        (baseChangeExpHom (a • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ m)) M hMam (hm.smul a)
          (Multiplicative.ofAdd (-(tr * ur ^ 3))))
        (baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (-(tr * ur ^ 2)))) :=
    commute_baseChangeExpHom M
      (((commute_of_lie_eq_zero ρ hwm).smul_left d).smul_right a).symm
      hMam hMdw (hm.smul a) (hw.smul d) _ _
  have hswap_wz :
      baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (-(tr * ur ^ 2))) *
        baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (tr * ur)) =
      baseChangeExpHom (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) M hMcz (hz.smul c)
          (Multiplicative.ofAdd (tr * ur)) *
        baseChangeExpHom (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) M hMdw (hw.smul d)
          (Multiplicative.ofAdd (-(tr * ur ^ 2))) *
        baseChangeExpHom (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMbo (ho.smul b)
          (Multiplicative.ofAdd (3 * (tr ^ 2 * ur ^ 3))) := by
    have hwz_lie : (d * c) • ⁅w, z⁆ = ((1 : ℕ) * (-(3 * b))) • o := by
      rw [← lie_skew w z, smul_neg, hzw]
      simp
    have hwz_r :
        (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) *
            (c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z)) =
          c • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ z) *
              (d • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ w)) +
            (-(3 * b)) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o) := by
      simpa only [one_zsmul, one_nsmul] using
        zsmul_mul_zsmul_eq_add_nsmul_of_zsmul_lie_eq ρ hwz_lie
    have hstep := baseChangeExpHom_mul_of_commutator_eq M hwz_r
      (((commute_of_lie_eq_zero ρ hwo).smul_left d).smul_right (-(3 * b)))
      (((commute_of_lie_eq_zero ρ hzo).smul_left c).smul_right (-(3 * b)))
      hMdw hMcz hMn3bo (hw.smul d) (hz.smul c) (ho.smul (-(3 * b)))
      (Multiplicative.ofAdd (-(tr * ur ^ 2))) (Multiplicative.ofAdd (tr * ur))
    have hpar :
        baseChangeExpHom ((-(3 * b)) • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMn3bo
            (ho.smul (-(3 * b)))
            (Multiplicative.ofAdd
              (Multiplicative.toAdd (Multiplicative.ofAdd (-(tr * ur ^ 2))) *
                Multiplicative.toAdd (Multiplicative.ofAdd (tr * ur)))) =
          baseChangeExpHom (b • ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ o)) M hMbo (ho.smul b)
            (Multiplicative.ofAdd (3 * (tr ^ 2 * ur ^ 3))) := by
      rw [baseChangeExpHom_zsmul_ofAdd (-(3 * b)) M hMo hMn3bo ho (ho.smul (-(3 * b))),
        baseChangeExpHom_zsmul_ofAdd b M hMo hMbo ho (ho.smul b)]
      congr 2
      simp only [toAdd_ofAdd]
      push_cast
      ring
    rw [hstep, hpar, mul_assoc _ (baseChangeExpHom (b • _) _ _ _ _),
      (hcomm_ow _).eq, ← mul_assoc]
  rw [reorder_g2_rev hswap_wz hcomm_om (hcomm_ow _) hcomm_oz hcomm_mz hcomm_mw,
    ← (baseChangeExpHom _ M hMbo (ho.smul b)).map_mul, ← ofAdd_add,
    baseChangeExpHom_zsmul_ofAdd c M hMz hMcz hz (hz.smul c),
    baseChangeExpHom_zsmul_ofAdd d M hMw hMdw hw (hw.smul d),
    baseChangeExpHom_zsmul_ofAdd a M hMm hMam hm (hm.smul a),
    baseChangeExpHom_zsmul_ofAdd b M hMo hMbo ho (ho.smul b)]
  have harg_w :
      Multiplicative.ofAdd ((d : R) * -(tr * ur ^ 2)) =
        Multiplicative.ofAdd ((-d : R) * (tr * ur ^ 2)) :=
    congrArg Multiplicative.ofAdd (by ring)
  have harg_m :
      Multiplicative.ofAdd ((a : R) * -(tr * ur ^ 3)) =
        Multiplicative.ofAdd ((-a : R) * (tr * ur ^ 3)) :=
    congrArg Multiplicative.ofAdd (by ring)
  have harg_o :
      Multiplicative.ofAdd ((b : R) * (3 * (tr ^ 2 * ur ^ 3) + (-2 : R) * (tr ^ 2 * ur ^ 3))) =
        Multiplicative.ofAdd ((b : R) * (tr ^ 2 * ur ^ 3)) :=
    congrArg Multiplicative.ofAdd (by ring)
  rw [harg_w, harg_m, harg_o]

end DividedPowerCommutator

end TauCeti.UniversalEnvelopingAlgebra
