/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Different
public import TauCeti.NumberTheory.LocalField.Norm.Basic
public import TauCeti.RingTheory.DedekindDomain.Discriminant.Basic

/-!
# The local discriminant of an extension of local fields

The different `𝔡(L/K)` of Mathlib is an ideal of `𝒪[L]`, the ring of integers of the *upper* field
of an extension `L/K` of nonarchimedean local fields. The discriminant `𝔩(L/K)` of the same
extension is an ideal of the *base* ring `𝒪[K]`: it is the norm image `N_{L/K}(𝔡(L/K))`, which is
Tau Ceti's `relDiscr 𝒪[K] 𝒪[L]`, the relative discriminant of the two rings of integers, and is
built from Mathlib's ideal norm `Ideal.relNorm`. The two ideals live in different rings and are not
to be conflated: `TauCeti.differentExponent` reads the exponent of `𝔡(L/K)` in the maximal ideal
of `𝒪[L]`, and this file adds `TauCeti.discriminantExponent K L`, for `L/K` separable, the
exponent `δ(L/K)` of the maximal ideal of `𝒪[K]` in `𝔩(L/K)`.

`TauCeti.discriminantExponent` is read for `L/K` separable. The trace form of an inseparable
extension is degenerate, so the different ideal, and with it the discriminant ideal, is the zero
ideal, and `multiplicity 𝓂 (⊥ : Ideal 𝒪[K]) = 0` whatever the maximal ideal: an `ℕ`-valued
order of vanishing would there be `0` for every power of the maximal ideal. The definition and
the results below therefore carry `[Algebra.IsSeparable K L]`.

A norm multiplies valuations by the residue degree, by `TauCeti.toAdd_normalizedValuation_norm`, so
`Ideal.relNorm 𝒪[K] 𝓂[L]` is `𝓂[K] ^ f(L/K)`
(`TauCeti.relNorm_maximalIdeal_eq_maximalIdeal_pow`). The discriminant ideal is then
`𝔩(L/K) = 𝓂[K] ^ δ(L/K)`, the ideal form of the product formula `δ(L/K) = f(L/K) · d(L/K)`
(`TauCeti.discriminantExponent_eq_inertiaDegree_mul_differentExponent`). Since for `L/K` separable
`TauCeti.differentExponent` is `0` exactly for unramified extensions, the discriminant inherits the
unramified criterion and the bound `f(L/K) · (e(L/K) - 1) ≤ δ(L/K)`.

## Main definitions

* `TauCeti.discriminantIdeal`: the local discriminant ideal `𝔩(L/K) = N_{L/K}(𝔡(L/K))`, the
  relative discriminant `relDiscr 𝒪[K] 𝒪[L]` of the two rings of integers.
* `TauCeti.discriminantExponent`: the local discriminant exponent `δ(L/K)` of a separable
  extension, the multiplicity of `𝓂[K]` in `𝔩(L/K)`.

## Main results

* `TauCeti.discriminantIdeal_def`, `TauCeti.discriminantExponent_def`: the defining formulas.
* `TauCeti.discriminantExponent_eq_inertiaDegree_mul_differentExponent`: the product formula
  `δ(L/K) = f(L/K) · d(L/K)`.
* `TauCeti.discriminantIdeal_eq_maximalIdeal_pow`: `𝔩(L/K) = 𝓂[K] ^ δ(L/K)`.
* `TauCeti.pow_dvd_discriminantIdeal_iff_le_discriminantExponent`: the characteristic property,
  `𝓂[K] ^ n ∣ 𝔩(L/K) ↔ n ≤ δ(L/K)`.
* `TauCeti.discriminantIdeal_eq_top_iff` and `TauCeti.discriminantExponent_eq_zero_iff`: the
  discriminant is trivial exactly when the extension is unramified.
* `TauCeti.inertiaDegree_mul_ramificationIndex_sub_one_le_discriminantExponent`: the local
  discriminant bound, `f(L/K) · (e(L/K) - 1) ≤ δ(L/K)`.
* `TauCeti.ramificationIndex_sub_one_le_discriminantExponent`: the residue-degree-free form of
  that bound, `e(L/K) - 1 ≤ δ(L/K)`.
* `TauCeti.discriminantExponent_eq_inertiaDegree_mul_ramificationIndex_sub_one_iff`: the tame
  value of the discriminant exponent.

## References

* [J.-P. Serre, *Corps Locaux*][serre1968], Chapter III, §6, Proposition 13.
* J. Neukirch, *Algebraic Number Theory*, Chapter II, §8.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing

namespace TauCeti

variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]

/-- The local discriminant ideal `𝔩(L/K) = N_{L/K}(𝔡(L/K))` of an extension `L/K` of
nonarchimedean local fields: the norm image of the different ideal, an ideal of the base ring
`𝒪[K]`. It is not the different ideal `𝔡(L/K)`, which is an ideal of `𝒪[L]`.

It is the relative discriminant `relDiscr 𝒪[K] 𝒪[L]` of the two rings of integers, the same
carrier for any finite extension of Dedekind domains, named here for the local field extension. -/
noncomputable def discriminantIdeal : Ideal 𝒪[K] :=
  relDiscr 𝒪[K] 𝒪[L]

/-- The defining formula of the local discriminant ideal: the relative norm of the different
ideal, in the form of `TauCeti.relDiscr_def`. -/
theorem discriminantIdeal_def :
    discriminantIdeal K L = Ideal.relNorm 𝒪[K] (differentIdeal 𝒪[K] 𝒪[L]) := by
  rw [discriminantIdeal, relDiscr_def]

variable [Algebra.IsSeparable K L]

/-- The local discriminant ideal is the `f(L/K) · d(L/K)`-th power of the maximal ideal of the
base ring, the form in which the norm image of the different is computed before the discriminant
exponent is read off it. -/
private theorem discriminantIdeal_eq_maximalIdeal_pow_mul :
    discriminantIdeal K L = 𝓂[K] ^ (inertiaDegree K L * differentExponent K L) := by
  rw [discriminantIdeal_def, differentIdeal_eq_maximalIdeal_pow (K := K) (L := L),
    map_pow, relNorm_maximalIdeal_eq_maximalIdeal_pow (K := K) (L := L), pow_mul]

/-- The local discriminant ideal of a separable extension of local fields is nonzero, being the
norm of the nonzero different ideal: the norm of an ideal of a Dedekind domain is zero only for the
zero ideal, by `Ideal.relNorm_eq_bot_iff`. -/
theorem discriminantIdeal_ne_bot : discriminantIdeal K L ≠ ⊥ := by
  intro h
  rw [discriminantIdeal_def] at h
  exact differentIdeal_ne_bot (Ideal.relNorm_eq_bot_iff.mp h)

/-- The order of vanishing of the discriminant ideal of a separable extension at the maximal ideal
of the base ring is finite: the maximal ideal of `𝒪[K]` is a prime ideal and the discriminant ideal
is nonzero, by `discriminantIdeal_ne_bot`. -/
private theorem discriminantIdeal_finiteMultiplicity :
    FiniteMultiplicity 𝓂[K] (discriminantIdeal K L) :=
  FiniteMultiplicity.of_prime_left
    (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field 𝒪[K]) inferInstance)
    (discriminantIdeal_ne_bot (K := K) (L := L))

-- The parameters of `discriminantExponent` are spelled out rather than taken from the enclosing
-- `variable`s, so that the separability instance is an argument of the definition itself and
-- `discriminantExponent` cannot be formed at all for an inseparable extension.
/--
The local discriminant exponent `δ(L/K)` of a separable extension `L/K` of nonarchimedean
local fields: the order of vanishing of the discriminant ideal `discriminantIdeal K L` at the
maximal ideal of `𝒪[K]`, the largest `n` with `𝓂[K] ^ n ∣ 𝔩(L/K)`.

The separability hypothesis belongs to the definition and not only to the theorems below. The
trace form of an inseparable extension is degenerate, so the different ideal and with it `𝔩(L/K)`
is the zero ideal, and the multiplicity of a maximal ideal in the zero ideal is `0` whatever that
maximal ideal is: an `ℕ`-valued order of vanishing of `𝔩(L/K)` would then be `0` for every power
of the maximal ideal and carry no information. -/
def discriminantExponent (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
    [Algebra.IsSeparable K L] : ℕ := by
  classical
  exact Nat.find (discriminantIdeal_finiteMultiplicity (K := K) (L := L))

/-- The defining formula of `discriminantExponent`: the order of vanishing of the discriminant
ideal at the maximal ideal of the base ring is its multiplicity. -/
theorem discriminantExponent_def :
    discriminantExponent K L = multiplicity 𝓂[K] (discriminantIdeal K L) := by
  classical
  have hf : FiniteMultiplicity 𝓂[K] (discriminantIdeal K L) :=
    discriminantIdeal_finiteMultiplicity (K := K) (L := L)
  have h : emultiplicity 𝓂[K] (discriminantIdeal K L) = (Nat.find hf : ℕ∞) := by
    rw [emultiplicity, dite_eq_left hf]
  exact (multiplicity_eq_of_emultiplicity_eq_some h).symm

/-- **The product formula for the local discriminant exponent**: `δ(L/K) = f(L/K) · d(L/K)`, for
`L/K` separable. -/
theorem discriminantExponent_eq_inertiaDegree_mul_differentExponent :
    discriminantExponent K L = inertiaDegree K L * differentExponent K L := by
  rw [discriminantExponent_def, discriminantIdeal_eq_maximalIdeal_pow_mul,
    multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field 𝒪[K]) inferInstance)]

/-- **The local discriminant ideal is the `δ(L/K)`-th power of the maximal ideal of `𝒪[K]`**:
`𝔩(L/K) = 𝓂[K] ^ δ(L/K)`, for `L/K` separable. -/
theorem discriminantIdeal_eq_maximalIdeal_pow :
    discriminantIdeal K L = 𝓂[K] ^ discriminantExponent K L := by
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent,
    discriminantIdeal_eq_maximalIdeal_pow_mul]

/-- **The characteristic property of the local discriminant exponent**: the `n`-th power of the
maximal ideal of `𝒪[K]` divides the discriminant ideal exactly when `n ≤ δ(L/K)`. -/
@[simp]
theorem pow_dvd_discriminantIdeal_iff_le_discriminantExponent {n : ℕ} :
    𝓂[K] ^ n ∣ discriminantIdeal K L ↔ n ≤ discriminantExponent K L :=
  (discriminantIdeal_finiteMultiplicity (K := K) (L := L)).pow_dvd_iff_le_multiplicity.trans
    (by rw [← discriminantExponent_def])

/-- **The first half of Dedekind's different theorem, for the discriminant**: the discriminant
exponent is at least `f(L/K) · (e(L/K) - 1)`. -/
theorem inertiaDegree_mul_ramificationIndex_sub_one_le_discriminantExponent :
    inertiaDegree K L * (ramificationIndex K L - 1) ≤ discriminantExponent K L := by
  rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent]
  exact Nat.mul_le_mul_left (inertiaDegree K L)
    (ramificationIndex_sub_one_le_differentExponent K L)

/-- The discriminant exponent is at least `e(L/K) - 1`. -/
theorem ramificationIndex_sub_one_le_discriminantExponent :
    ramificationIndex K L - 1 ≤ discriminantExponent K L := by
  refine Nat.le_of_mul_le_mul_left (c := inertiaDegree K L) ?_
    (inertiaDegree_pos (K := K) (L := L))
  exact (inertiaDegree_mul_ramificationIndex_sub_one_le_discriminantExponent
    (K := K) (L := L)).trans
    (Nat.le_mul_of_pos_left (discriminantExponent K L) (inertiaDegree_pos (K := K) (L := L)))

/-- **Dedekind's different theorem for the discriminant in the tame case**:
`δ(L/K) = f(L/K) · (e(L/K) - 1)` exactly when `L/K` is tamely ramified. -/
@[simp]
theorem discriminantExponent_eq_inertiaDegree_mul_ramificationIndex_sub_one_iff :
    discriminantExponent K L = inertiaDegree K L * (ramificationIndex K L - 1) ↔
      IsTamelyRamified K L := by
  constructor
  · intro h
    have h1 : inertiaDegree K L * differentExponent K L
        = inertiaDegree K L * (ramificationIndex K L - 1) := by
      rw [← h, discriminantExponent_eq_inertiaDegree_mul_differentExponent]
    exact (differentExponent_eq_ramificationIndex_sub_one_iff (K := K) (L := L)).1
      (Nat.mul_left_cancel (inertiaDegree_pos (K := K) (L := L)) h1)
  · intro h
    rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent,
      (differentExponent_eq_ramificationIndex_sub_one_iff (K := K) (L := L)).2 h]

/-- **The local discriminant exponent vanishes exactly for unramified extensions**:
`δ(L/K) = 0` if and only if `L/K` is unramified. -/
@[simp]
theorem discriminantExponent_eq_zero_iff :
    discriminantExponent K L = 0 ↔ IsUnramified K L := by
  constructor
  · intro h
    have h' : inertiaDegree K L * differentExponent K L = 0 := by
      rw [← discriminantExponent_eq_inertiaDegree_mul_differentExponent, h]
    rw [Nat.mul_eq_zero] at h'
    rcases h' with hf | hd
    · exact absurd hf (Nat.ne_of_gt (inertiaDegree_pos (K := K) (L := L)))
    · exact (differentExponent_eq_zero_iff (K := K) (L := L)).1 hd
  · intro h
    rw [discriminantExponent_eq_inertiaDegree_mul_differentExponent,
      (differentExponent_eq_zero_iff (K := K) (L := L)).2 h, Nat.mul_zero]

/-- **The discriminant of a local extension is trivial exactly when the extension is
unramified**: `𝔩(L/K) = 𝒪[K]` if and only if `L/K` is unramified. -/
@[simp]
theorem discriminantIdeal_eq_top_iff : discriminantIdeal K L = ⊤ ↔ IsUnramified K L := by
  rw [← discriminantExponent_eq_zero_iff, discriminantIdeal_eq_maximalIdeal_pow]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, pow_zero, Ideal.one_eq_top]⟩
  by_contra hd
  exact (maximalIdeal.isMaximal 𝒪[K]).ne_top (eq_top_mono (Ideal.pow_le_self hd) h)

end TauCeti
