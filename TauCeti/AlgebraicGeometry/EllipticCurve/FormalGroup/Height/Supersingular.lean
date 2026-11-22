/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Order
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.FormalSeries.Hom
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.IsElliptic
import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.MulByInt.Degree

/-!
# Formal-group height and supersingularity of elliptic curves at every prime

Let `W` be an elliptic curve over a field `K`, with formal group law `Ê = formalGroup W`.
Using the identification `ord [n]_Ê = deg_i [n]` and nonvanishing `[n]_Ê ≠ 0` (for `n ≠ 0`) from
`TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Order`, when `K` has prime characteristic `p`,
multiplication by `p` has total degree `p²` and factors as `[p] = V ∘ F` with `F` purely
inseparable of degree `p` and `V` of prime degree `p`. Comparing `deg_s [p] * deg_i [p] = p²` with
the Verschiebung criteria of
`TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.RelativeFrobenius.Supersingular` yields the
complete formal-group height stratification at every prime `p` (including `p = 2` and `p = 3`,
Silverman V.3.1):

* `W` is ordinary at `p` if and only if `Ê` has height `1`, equivalently if and only if the
  coefficient of `T ^ (p - 1)` in the invariant differential of `Ê` is nonzero;
* `W` is supersingular at `p` if and only if `Ê` has height `2`, equivalently if and only if its
  height exceeds `1`, equivalently if and only if the coefficient of `T ^ (p - 1)` in the invariant
  differential vanishes;
* the formal group of an elliptic curve in characteristic `p` always has height `1` or `2`
  (never `⊤` and never `≥ 3`).

Because every isogeny `φ : W₁ → W₂` induces a nonzero formal-group homomorphism
`φ.formalGroupHom : FormalGroupHom (formalGroup W₁) (formalGroup W₂)`, formal-group height — and
hence ordinarity and supersingularity — are invariant under arbitrary isogenies. As a separate
application of the order bounds and cuspidal vanishing in
`TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Order`, the family-level truncation of
Landweber height ideals over arbitrary commutative rings is proved in
`TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Height.Bound`.

## Main results

* `TauCeti.Isogeny.order_nsmulSeries_formalGroup_eq`,
  `TauCeti.Isogeny.order_zsmulSeries_formalGroup_eq`, and `TauCeti.Isogeny.height_formalGroup_eq`:
  isogenous elliptic curves have multiplication series of equal order and equal formal-group height.
* `WeierstrassCurve.isOrdinary_iff_height_formalGroup_eq_one` and
  `WeierstrassCurve.isSupersingular_iff_height_formalGroup_eq_two`: an elliptic curve in prime
  characteristic `p` is ordinary iff `height p Ê = 1`, and in arbitrary characteristic `p`
  (prime or zero) is supersingular iff `height p Ê = 2`.
* `WeierstrassCurve.height_formalGroup_eq_one_or_eq_two` and
  `WeierstrassCurve.height_formalGroup_le_two`: the formal group of an elliptic curve in prime
  characteristic `p` has height `1` or `2`.
* `TauCeti.Isogeny.isSupersingular_iff` and `TauCeti.Isogeny.isOrdinary_iff`: supersingularity and
  ordinarity of elliptic curves are invariant under arbitrary isogenies.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.4, IV.7 and V.3.1.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §12.4.
-/

public section

open TauCeti.Isogeny

/-! ### Formal-group height of elliptic curves over fields -/

namespace WeierstrassCurve

section FieldHeight

variable {K : Type*} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]

/-- **For `p ≠ 0`, the formal group of an elliptic curve over a field has finite `p`-height.** -/
theorem height_formalGroup_ne_top {p : ℕ} (hp : p ≠ 0) : (formalGroup W).height p ≠ ⊤ := by
  rw [Ne, FormalGroup.height_eq_top_iff]
  exact W.nsmulSeries_formalGroup_ne_zero hp

/-- **An elliptic curve in characteristic `p` (prime or zero) is supersingular if and only if its
formal group has height `2`** (Silverman V.3.1 in prime characteristic; in characteristic zero,
`p = 0`, neither condition holds since `¬ W.IsSupersingular 0` and `height 0 Ê = ⊤`). -/
theorem isSupersingular_iff_height_formalGroup_eq_two {p : ℕ} [CharP K p] :
    W.IsSupersingular p ↔ (formalGroup W).height p = 2 := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    have : ExpChar K p := .prime hp
    set φ := mulByIntIsogenyOfNeZero W.toAffine (n := p) (mod_cast hp.ne_zero)
    have hdeg : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
      rw [φ.separableDegree_mul_inseparableDegree, degree_mulByIntIsogenyOfNeZero,
        Int.natAbs_natCast]
    rw [W.isSupersingular_iff_separableDegree_mulByIntIsogenyOfNeZero_eq_one p,
      ← Nat.cast_ofNat (R := ℕ∞), FormalGroup.height_eq_natCast_iff,
      W.order_nsmulSeries_formalGroup_of_ne_zero hp.ne_zero, Nat.cast_inj (R := ℕ∞)]
    have hp2 : 0 < p ^ 2 := pow_pos hp.pos 2
    constructor <;> intro h
    · rwa [h, one_mul] at hdeg
    · rw [h] at hdeg
      exact (Nat.mul_eq_right hp2.ne').mp hdeg
  · simp

section CharP

variable {p : ℕ} [hp : Fact p.Prime] [CharP K p]

/-- **An elliptic curve in prime characteristic `p` is ordinary if and only if its formal group has
height `1`** (Silverman V.3.1). -/
theorem isOrdinary_iff_height_formalGroup_eq_one :
    W.IsOrdinary p ↔ (formalGroup W).height p = 1 := by
  have : ExpChar K p := .prime hp.out
  set φ := mulByIntIsogenyOfNeZero W.toAffine (n := p) (mod_cast hp.out.ne_zero)
  have hdeg : φ.separableDegree * φ.inseparableDegree = p ^ 2 := by
    rw [φ.separableDegree_mul_inseparableDegree, degree_mulByIntIsogenyOfNeZero,
      Int.natAbs_natCast]
  rw [W.isOrdinary_iff_separableDegree_mulByIntIsogenyOfNeZero_eq p hp.out,
    ← Nat.cast_one, FormalGroup.height_eq_natCast_iff, pow_one,
    W.order_nsmulSeries_formalGroup_of_ne_zero hp.out.ne_zero, Nat.cast_inj (R := ℕ∞)]
  have hp0 : p ≠ 0 := hp.out.ne_zero
  constructor <;> intro h
  · rw [h, sq] at hdeg
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hp0) hdeg
  · rw [h, sq] at hdeg
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hp0) hdeg

/-- **The formal group of an elliptic curve in prime characteristic `p` has height `1` or `2`.** -/
theorem height_formalGroup_eq_one_or_eq_two :
    (formalGroup W).height p = 1 ∨ (formalGroup W).height p = 2 := by
  by_cases h : W.IsSupersingular p
  · exact Or.inr (W.isSupersingular_iff_height_formalGroup_eq_two.mp h)
  · exact Or.inl (W.isOrdinary_iff_height_formalGroup_eq_one.mp (W.not_isSupersingular.mp h))

/-- **The formal group of an elliptic curve in prime characteristic `p` has height at most `2`.** -/
theorem height_formalGroup_le_two : (formalGroup W).height p ≤ 2 := by
  rcases W.height_formalGroup_eq_one_or_eq_two (p := p) with h | h
  · rw [h]
    exact one_le_two
  · rw [h]

/-- **An elliptic curve in prime characteristic `p` is supersingular if and only if its formal group
has height strictly greater than `1`.** -/
theorem isSupersingular_iff_one_lt_height_formalGroup :
    W.IsSupersingular p ↔ 1 < (formalGroup W).height p := by
  rw [← not_isOrdinary, isOrdinary_iff_height_formalGroup_eq_one,
    (formalGroup W).one_le_height.lt_iff_ne', Ne]

end CharP

section AnyCharP

variable {p : ℕ} [CharP K p]

/-- **Coefficient criterion for ordinarity of an elliptic curve in characteristic `p` (prime or
zero).** In prime characteristic `p`, this is the classical Hasse-invariant criterion: `W` is
ordinary iff the coefficient of `T ^ (p - 1)` in the invariant differential of its formal group is
nonzero (Katz–Mazur §12.4, Silverman IV.4, IV.7 and V.3.1). At `p = 0` (characteristic zero),
`p - 1` is `0` in `ℕ`, so the test evaluates the normalized constant coefficient `1 ≠ 0` and agrees
with the library's characteristic-zero ordinarity convention
(`WeierstrassCurve.isOrdinary_zero`). -/
theorem isOrdinary_iff_coeff_invariantDifferential_formalGroup_ne_zero :
    W.IsOrdinary p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential ≠ 0 := by
  rcases CharP.char_is_prime_or_zero K p with hp | rfl
  · have : Fact p.Prime := ⟨hp⟩
    rw [isOrdinary_iff_height_formalGroup_eq_one, height_formalGroup_eq_one_iff]
  · simp

/-- **Coefficient criterion for supersingularity of an elliptic curve in characteristic `p` (prime
or zero).** In prime characteristic `p`, `W` is supersingular iff the Hasse invariant
`coeff (p - 1) ω` vanishes (Katz–Mazur §12.4, Silverman IV.4, IV.7 and V.3.1). At `p = 0`
(characteristic zero), `p - 1` is `0` in `ℕ`, so the test evaluates the normalized constant
coefficient `1 = 0` and agrees with `WeierstrassCurve.not_isSupersingular_zero`. -/
theorem isSupersingular_iff_coeff_invariantDifferential_formalGroup_eq_zero :
    W.IsSupersingular p ↔ PowerSeries.coeff (p - 1) (formalGroup W).invariantDifferential = 0 := by
  rw [← not_isOrdinary, isOrdinary_iff_coeff_invariantDifferential_formalGroup_ne_zero, not_not]

end AnyCharP

end FieldHeight

end WeierstrassCurve

/-! ### Invariance under arbitrary isogenies -/

namespace TauCeti.Isogeny

open WeierstrassCurve

variable {K : Type*} [Field K] {W₁ W₂ : WeierstrassCurve K} [W₂.IsElliptic]

/-- **Isogenous elliptic curves have `[n]_Ê` series of equal order** (`n : ℕ`). -/
theorem order_nsmulSeries_formalGroup_eq (φ : Isogeny W₁.toAffine W₂.toAffine) (n : ℕ) :
    ((formalGroup W₁).nsmulSeries n).order = ((formalGroup W₂).nsmulSeries n).order := by
  have : W₁.IsElliptic := φ.isElliptic
  exact φ.formalGroupHom.order_nsmulSeries_eq (by simp [φ.formalSeries_ne_zero]) n

/-- **Isogenous elliptic curves have `[n]_Ê` series of equal order** (`n : ℤ`). -/
theorem order_zsmulSeries_formalGroup_eq (φ : Isogeny W₁.toAffine W₂.toAffine) (n : ℤ) :
    ((formalGroup W₁).zsmulSeries n).order = ((formalGroup W₂).zsmulSeries n).order := by
  have : W₁.IsElliptic := φ.isElliptic
  exact φ.formalGroupHom.order_zsmulSeries_eq (by simp [φ.formalSeries_ne_zero]) n

/-- **Isogenous elliptic curves have the same formal-group height.** -/
theorem height_formalGroup_eq (φ : Isogeny W₁.toAffine W₂.toAffine) (p : ℕ) :
    (formalGroup W₁).height p = (formalGroup W₂).height p := by
  have : W₁.IsElliptic := φ.isElliptic
  exact φ.formalGroupHom.height_eq (by simp [φ.formalSeries_ne_zero]) p

/-- **Supersingularity of elliptic curves is invariant under arbitrary isogenies** in exponential
characteristic `p`. -/
theorem isSupersingular_iff (φ : Isogeny W₁.toAffine W₂.toAffine) (p : ℕ) [ExpChar K p] :
    W₁.IsSupersingular p ↔ W₂.IsSupersingular p := by
  -- In characteristic zero (`p = 1`) both curves have trivial `1`-torsion; in prime characteristic
  -- `p` the criterion `isSupersingular_iff_height_formalGroup_eq_two` reduces to
  -- `height_formalGroup_eq`.
  have : W₁.IsElliptic := φ.isElliptic
  rcases ‹ExpChar K p› with _ | ⟨hp⟩
  · simp [WeierstrassCurve.isSupersingular_iff_forall, one_nsmul]
  · have : Fact p.Prime := ⟨hp⟩
    rw [W₁.isSupersingular_iff_height_formalGroup_eq_two,
      W₂.isSupersingular_iff_height_formalGroup_eq_two, φ.height_formalGroup_eq p]

/-- **Ordinarity of elliptic curves is invariant under arbitrary isogenies** in exponential
characteristic `p`. -/
theorem isOrdinary_iff (φ : Isogeny W₁.toAffine W₂.toAffine) (p : ℕ) [ExpChar K p] :
    W₁.IsOrdinary p ↔ W₂.IsOrdinary p := by
  rw [← W₁.not_isSupersingular, ← W₂.not_isSupersingular, φ.isSupersingular_iff p]

end TauCeti.Isogeny

end
