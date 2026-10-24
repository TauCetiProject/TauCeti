/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.FormalGroup.CoordinateChange.NSMul
public import TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Data.Nat.Log
import TauCeti.RingTheory.FormalGroup.NSMul.BaseChange
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# The height of a formal group law

Let `f(T) = a Tⁿ + ⋯` be a homomorphism between one-dimensional formal group laws `F` and `G`
over a commutative ring `R`, so that `f(F(X, Y)) = G(f(X), f(Y))`. Since `F(X, Y) = X + Y + ⋯`
and `G(X, Y) = X + Y + ⋯`, comparing the homogeneous parts of degree `n` gives

  `a (X + Y)ⁿ = a Xⁿ + a Yⁿ`,

so `a` kills every binomial coefficient `n.choose i` with `0 < i < n`, hence their greatest common
divisor `d_n` (`TauCeti.lazardGcd`). Since `d_n` is `p` when `n` is a power of a prime `p` and `1`
otherwise, if `p = 0` in `R` then a nonzero homomorphism has order a power of `p`: the first
nonzero term of `f` has degree `p ^ h`. This applies to multiplication by `p` on a commutative
formal group law: either `[p]_F = 0`, or `[p]_F(T) = a T^(p ^ h) + ⋯` with `a ≠ 0` and `h ≥ 1`,
since the linear coefficient of `[p]_F` is `p = 0`.

Over a field `K` of characteristic `p` this exponent is the **height** of `F`; it is `⊤` when
`[p]_F = 0`, as for the additive formal group law. The multiplicative formal group law has
height one, since `[p](T) = (1 + T) ^ p - 1 = T ^ p`. The height is unchanged by extension of
the base field and by changes of formal coordinate. Over a ring, the leading coefficient of `[p]_F`
need not be a unit, and the exponent no longer measures the height in the usual sense; so the height
is defined over fields.

## Main definitions

* `FormalGroup.height`: the height of a formal group law over a field of characteristic `p`.

## Main results

* `FormalGroup.coeff_mul_lazardGcd_eq_zero_of_le_order`: the coefficient `a` of `Tⁿ` in a
  homomorphism of order at least `n` satisfies `d_n a = 0`.
* `FormalGroup.exists_order_eq_pow_of_natCast_eq_zero`: if `p = 0` in `R`, a nonzero
  homomorphism has order a power of `p`.
* `FormalGroup.exists_order_nsmulSeries_eq_pow`: if `p = 0` in `R`, then `[p]_F` is zero or has
  order `p ^ h` with `h ≥ 1`.
* `FormalGroup.height_eq_top_iff` and `FormalGroup.height_eq_natCast_iff`: `F` has height `⊤`
  exactly when `[p]_F = 0`, and height `h` exactly when `[p]_F` has order `p ^ h`.
* `FormalGroup.one_le_height`: the height is at least one.
* `FormalGroup.height_map`: the height is invariant under extension of the base field.
* `FormalGroup.height_𝔾ₐ` and `FormalGroup.height_𝔾ₘ`: the additive formal group law has height
  `⊤` and the multiplicative one has height `1`.
* `TauCeti.FormalCoordinate.height_smul`: height is independent of the coordinate.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.7.
-/

public section

open MvPowerSeries

namespace FormalGroup

section Hom

variable {R : Type*} [CommRing R] (F G : FormalGroup R)

/-- **The leading term of a formal group homomorphism.** If `f(F(X, Y)) = G(f(X), f(Y))` and `f`
has order at least `n`, then the coefficient `a` of `Tⁿ` in `f` satisfies `d_n a = 0`, where
`d_n` is the greatest common divisor of the binomial coefficients `n.choose i`, `0 < i < n`. -/
theorem coeff_mul_lazardGcd_eq_zero_of_le_order {f : PowerSeries R}
    (hf : PowerSeries.subst F.toPowerSeries f =
      subst (fun i ↦ f.toMvPowerSeries i) G.toPowerSeries)
    {n : ℕ} (hn : n ≤ f.order) : PowerSeries.coeff n f * TauCeti.lazardGcd n = 0 := by
  obtain hn2 | hn2 := lt_or_ge n 2
  · simp [TauCeti.lazardGcd_eq_zero_of_lt_two hn2]
  set a := PowerSeries.coeff n f
  set u : Fin 2 → MvPowerSeries (Fin 2) R := fun i ↦ f.toMvPowerSeries i with hu_def
  have hf₀ : PowerSeries.constantCoeff f = 0 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact PowerSeries.coeff_of_lt_order 0 (lt_of_lt_of_le (by exact_mod_cast (by omega : 0 < n)) hn)
  have hu₀ (i : Fin 2) : constantCoeff (u i) = 0 := by
    simp [u, PowerSeries.toMvPowerSeries_eq_subst,
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero, hf₀]
  have hu : HasSubst u := hasSubst_of_constantCoeff_zero hu₀
  -- the degree-`n` parts of `f(F(X, Y))` and of `f(X)`, `f(Y)`
  have hL :
      homogeneousComponent n (PowerSeries.subst F.toPowerSeries f) = C a * (X 0 + X 1) ^ n := by
    rw [PowerSeries.homogeneousComponent_subst_of_le_order F.zero_constantCoeff hn,
      homogeneousComponent_one_eq_X_add_X F.lin_coeff_X F.lin_coeff_Y, Algebra.algebraMap_self,
      RingHom.id_apply]
  have hU (i : Fin 2) : homogeneousComponent n (u i) = C a * X i ^ n := by
    simp only [hu_def, PowerSeries.toMvPowerSeries_eq_subst]
    rw [PowerSeries.homogeneousComponent_subst_of_le_order (constantCoeff_X i) hn,
      Algebra.algebraMap_self, RingHom.id_apply, homogeneousComponent_one_X]
  -- the terms of `G` of degree at least two contribute nothing in degree `n` to `G(f(X), f(Y))`
  have hR : homogeneousComponent n (subst u G.toPowerSeries) = C a * X 0 ^ n + C a * X 1 ^ n := by
    have hG : G.toPowerSeries = X 0 + X 1 + (G.toPowerSeries - (X 0 + X 1)) := by ring
    have hlt : (n : ℕ∞) < (subst u (G.toPowerSeries - (X 0 + X 1))).order := by
      refine lt_of_lt_of_le ?_ (le_order_subst hu _)
      calc (n : ℕ∞) < n * 2 := by exact_mod_cast (by omega : n < n * 2)
        _ ≤ _ := mul_le_mul' (le_iInf fun i ↦ hn.trans
            (by simpa [u, PowerSeries.toMvPowerSeries_eq_subst] using
              PowerSeries.le_order_subst_left (constantCoeff_X i)))
          (two_le_order_sub_X_add_X G.zero_constantCoeff G.lin_coeff_X G.lin_coeff_Y)
    rw [hG, subst_add hu, subst_add hu, subst_X hu, subst_X hu, map_add, map_add, hU, hU,
      homogeneousComponent_of_lt_order_eq_zero hlt, _root_.add_zero]
  -- hence `a ((X + Y)ⁿ - Xⁿ - Yⁿ) = 0`, which is `(a d_n) C_n = 0` for the Lazard cocycle `C_n`
  have key : (MvPolynomial.C a * ((MvPolynomial.X 0 + MvPolynomial.X 1) ^ n -
      MvPolynomial.X 0 ^ n - MvPolynomial.X 1 ^ n) : MvPolynomial (Fin 2) R) = 0 := by
    rw [← MvPolynomial.coe_eq_zero_iff, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply]
    have := congrArg (homogeneousComponent n) hf
    rw [hL, hR] at this
    simp only [map_mul, map_sub, map_add, map_pow, MvPolynomial.coeToMvPowerSeries.ringHom_apply,
      MvPolynomial.coe_C, MvPolynomial.coe_X]
    linear_combination this
  rw [← TauCeti.lazardGcd_nsmul_lazardCocycle (by omega), MvPolynomial.C_mul',
    ← Nat.cast_smul_eq_nsmul R, smul_smul] at key
  exact (TauCeti.smul_lazardCocycle_eq_zero_iff hn2).mp key

/-- **Homomorphisms of formal group laws in characteristic `p` have order a power of `p`.** If
`p` is a prime with `p = 0` in `R`, and `f ≠ 0` with zero constant coefficient satisfies
`f(F(X, Y)) = G(f(X), f(Y))`, then the first nonzero term of `f` has degree a power of `p`. -/
theorem exists_order_eq_pow_of_natCast_eq_zero {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0)
    {f : PowerSeries R} (hf₀ : PowerSeries.constantCoeff f = 0)
    (hf : PowerSeries.subst F.toPowerSeries f =
      subst (fun i ↦ f.toMvPowerSeries i) G.toPowerSeries)
    (hf0 : f ≠ 0) : ∃ h : ℕ, f.order = (p ^ h : ℕ) := by
  set n := f.order.toNat
  have hn : f.order = n := (ENat.natCast_toNat (PowerSeries.order_eq_top.not.mpr hf0)).symm
  have ha : PowerSeries.coeff n f ≠ 0 := PowerSeries.coeff_order hf0
  have hd := F.coeff_mul_lazardGcd_eq_zero_of_le_order G hf hn.ge
  -- `d_n` is a unit in `R` whenever it is prime to `p`
  have hcoeff (hcop : (TauCeti.lazardGcd n).Coprime p) : PowerSeries.coeff n f = 0 := by
    have : IsCoprime ((TauCeti.lazardGcd n : ℕ) : R) (p : R) := by
      simpa using (Nat.isCoprime_iff_coprime.mpr hcop).intCast (R := R)
    rw [hpR, isCoprime_zero_right] at this
    exact this.mul_left_eq_zero.mp hd
  have hn0 : n ≠ 0 := fun h ↦ ha (by rw [h, PowerSeries.coeff_zero_eq_constantCoeff_apply, hf₀])
  by_cases hn1 : n = 1
  · exact ⟨0, by rw [hn, hn1, pow_zero]⟩
  by_cases hpow : IsPrimePow n
  · have hq := Nat.minFac_prime hn1
    by_cases hqp : n.minFac = p
    · exact ⟨n.factorization p, by rw [hn, ← hqp, hpow.minFac_pow_factorization_eq]⟩
    · have hcop : (TauCeti.lazardGcd n).Coprime p := by
        rw [TauCeti.lazardGcd_eq_minFac_of_isPrimePow hpow]
        exact (Nat.coprime_primes hq hp).mpr hqp
      exact absurd (hcoeff hcop) ha
  · have hcop : (TauCeti.lazardGcd n).Coprime p := by
      rw [TauCeti.lazardGcd_eq_one_of_not_isPrimePow (by omega) hpow]
      exact Nat.coprime_one_left p
    exact absurd (hcoeff hcop) ha

/-- **The `p`-series has order a power of `p`** in characteristic `p`: if `p` is a prime with
`p = 0` in `R` and `F` is commutative, then either `[p]_F = 0` or the first nonzero term of
`[p]_F` has degree `p ^ h` for some `h ≥ 1`. -/
theorem exists_order_nsmulSeries_eq_pow [F.IsComm] {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0)
    (h0 : F.nsmulSeries p ≠ 0) : ∃ h ≠ 0, (F.nsmulSeries p).order = (p ^ h : ℕ) := by
  obtain ⟨h, hh⟩ := F.exists_order_eq_pow_of_natCast_eq_zero F hp hpR
    (F.constantCoeff_nsmulSeries p) (F.subst_toPowerSeries_nsmulSeries p) h0
  refine ⟨h, ?_, hh⟩
  rintro rfl
  -- order one would need a nonzero linear coefficient, but that coefficient is `p = 0`
  rw [pow_zero, PowerSeries.order_eq_nat, coeff_one_nsmulSeries] at hh
  exact hh.1 hpR

end Hom

section Height

variable {K L : Type*} [Field K] [Field L] (F : FormalGroup K) {p : ℕ}

open scoped Classical in
/-- The **height** of a formal group law `F` over a field `K` of characteristic `p`: `⊤` if
multiplication by `p` on `F` is zero, and otherwise the exponent `h` such that the first nonzero
term of `[p]_F(T)` has degree `p ^ h` (see `FormalGroup.height_eq_natCast_iff`). -/
noncomputable def height (p : ℕ) : ℕ∞ :=
  if F.nsmulSeries p = 0 then ⊤ else Nat.log p (F.nsmulSeries p).order.toNat

/-- A formal group law has infinite height exactly when multiplication by `p` is zero. -/
@[simp]
theorem height_eq_top_iff : F.height p = ⊤ ↔ F.nsmulSeries p = 0 := by
  unfold height
  split_ifs with h <;> simp [h]

/-- A commutative formal group law over a field of characteristic `p` has height `h` exactly when
the first nonzero term of `[p]_F(T)` has degree `p ^ h`. -/
theorem height_eq_natCast_iff [hp : Fact p.Prime] [CharP K p] [F.IsComm] {h : ℕ} :
    F.height p = h ↔ (F.nsmulSeries p).order = (p ^ h : ℕ) := by
  constructor
  · intro hh
    have h0 : F.nsmulSeries p ≠ 0 := fun h0 ↦ by simp [F.height_eq_top_iff.mpr h0] at hh
    obtain ⟨k, -, hk⟩ := F.exists_order_nsmulSeries_eq_pow hp.out (CharP.cast_eq_zero K p) h0
    simp only [height, h0, ↓reduceIte, hk, ENat.toNat_natCast, Nat.log_pow hp.out.one_lt,
      Nat.cast_inj] at hh
    rw [hk, hh]
  · intro hh
    have h0 : F.nsmulSeries p ≠ 0 := fun h0 ↦ by
      rw [h0, PowerSeries.order_zero] at hh
      exact ENat.top_ne_natCast _ hh
    simp only [height, h0, ↓reduceIte, hh, ENat.toNat_natCast, Nat.log_pow hp.out.one_lt]

/-- The height of a commutative formal group law over a field of characteristic `p` is at least
one. -/
theorem one_le_height [hp : Fact p.Prime] [CharP K p] [F.IsComm] : 1 ≤ F.height p := by
  by_cases h0 : F.nsmulSeries p = 0
  · simp [F.height_eq_top_iff.mpr h0]
  obtain ⟨k, hk0, hk⟩ := F.exists_order_nsmulSeries_eq_pow hp.out (CharP.cast_eq_zero K p) h0
  rw [(F.height_eq_natCast_iff).mpr hk]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr hk0

/-- The height is invariant under extension of the base field. -/
@[simp]
theorem height_map (φ : K →+* L) (p : ℕ) : (F.map φ).height p = F.height p := by
  have hφ := PowerSeries.map_injective φ φ.injective
  rw [height, height, ← map_nsmulSeries, map_eq_zero_iff _ hφ,
    PowerSeries.order_map_of_injective φ.injective]

/-- The additive formal group law has infinite height. -/
@[simp]
theorem height_𝔾ₐ [CharP K p] : (𝔾ₐ : FormalGroup K).height p = ⊤ := by
  rw [height_eq_top_iff, nsmulSeries_𝔾ₐ, ← map_natCast PowerSeries.C, CharP.cast_eq_zero,
    map_zero, zero_mul]

/-- The multiplicative formal group law has height one. -/
@[simp]
theorem height_𝔾ₘ [Fact p.Prime] [CharP K p] : (𝔾ₘ : FormalGroup K).height p = 1 := by
  have : CharP (PowerSeries K) p :=
    charP_of_injective_algebraMap (algebraMap K (PowerSeries K)).injective p
  rw [← Nat.cast_one, height_eq_natCast_iff, nsmulSeries_𝔾ₘ, add_pow_char, one_pow,
    add_sub_cancel_left, pow_one, PowerSeries.order_X_pow]

end Height

end FormalGroup

namespace TauCeti.FormalCoordinate

/-- Height is unchanged by a change of coordinate, including non-strict coordinates and infinite
height. The identity holds for every index `p` in the definition of height, without additional
characteristic or commutativity hypotheses. -/
@[simp]
theorem height_smul {K : Type*} [Field K] (φ : FormalCoordinate K) (F : FormalGroup K) (p : ℕ) :
    (φ • F).height p = F.height p := by
  unfold FormalGroup.height
  rw [φ.nsmulSeries_smul_eq_zero_iff F p, φ.order_nsmulSeries_smul]

end TauCeti.FormalCoordinate
