/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.DirichletCharacter.EulerProduct
public import TauCeti.NumberTheory.IntegralLattice.LocalDensity.Basic
public import TauCeti.NumberTheory.LegendreSymbol.KroneckerSymbol
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The product of the local densities over the good primes

Let `A` be the Gram matrix of a nondegenerate integral lattice `L` of rank `n`, and let `S` be the
set of primes dividing `2 det A`. At a prime `p ∉ S` the local density `α_p(L)`, the limit of the
normalized counts `p^{-r n (n - 1) / 2} · #{X ∈ Mₙ(ℤ/pʳ) : Xᵀ A X ≡ A (mod pʳ)}`, tends to `2` as
`p → ∞`, so the raw product `∏_p α_p(L)⁻¹` diverges to `0`. The factor that enters a mass formula
is the *normalized* density `α_p(L) / 2`. This file evaluates the product of its inverses over
the good primes: writing `ζ^{(S)}(s) = ∏_{q ∈ S} (1 - q⁻ˢ) · ζ(s)` for the zeta function with the
Euler factors at `S` removed,

```text
n = 2m + 1:  ∏_{p ∉ S} (α_p(L) / 2)⁻¹ = ∏_{i=1}^{m} ζ^{(S)}(2i),
n = 2m + 2:  ∏_{p ∉ S} (α_p(L) / 2)⁻¹ = ∏_{i=1}^{m} ζ^{(S)}(2i) · L(m + 1, χ_L),
```

where `χ_L` is the quadratic character `p ↦ ((-1)^{m+1} det A | p)` of the signed determinant,
realized as the Kronecker character of the discriminant `4 (-1)^{m+1} det A`. That character
already vanishes at every prime of `S`, so `L(s, χ_L)` is its own `S`-truncation. The products
converge unconditionally (as `HasProd`), and to nonzero values, in rank `1` and in every rank at
least `3`: in odd rank `2m + 1` every factor is a `ζ(2i)` with `2i ≥ 2`, while in even rank
`2m + 2 ≥ 4` the `L`-value is at `m + 1 ≥ 2`. In rank `1` the product is empty and equals `1`.

In the normalization of Conway and Sloane, whose standard factor `std_p(f)` is `α_p(L)⁻¹`, the
factor `(α_p(L) / 2)⁻¹` is their `2 · std_p(f)` at a good prime.

The statements take the local densities as a family `α` together with the hypothesis that `α p` is
the limit of the normalized counts at every good prime `p`. The limit exists there
(`Matrix.tendsto_localDensityCount_div_of_isUnit_det`), so the hypothesis only names it, and
determines `α p` for every good prime.

## Main results

* `Matrix.hasProd_inv_half_localDensity_of_card_eq_two_mul_add_one`: the odd-rank product.
* `Matrix.hasProd_inv_half_localDensity_of_card_eq_one`: in rank `1` the product is `1`.
* `Matrix.hasProd_inv_half_localDensity_of_card_eq_two_mul_add_two`: the even-rank product, in
  rank at least `4`.
* `Matrix.tprod_inv_half_localDensity_ne_zero_of_card_eq_two_mul_add_one`,
  `Matrix.tprod_inv_half_localDensity_ne_zero_of_card_eq_two_mul_add_two`: the products are
  nonzero.

## References

* C. L. Siegel, *Über die analytische Theorie der quadratischen Formen*, Ann. of Math. 36
  (1935).
* J. H. Conway, N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*, Proc. Roy.
  Soc. London Ser. A 419 (1988), equation (6) and section 12.
-/

public section

open Filter Topology
open scoped LSeries.notation

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The modulus `(2 det A).natAbs` of the good primes is nonzero. -/
private theorem neZero_natAbs_two_mul_det {A : Matrix n n ℤ} (hdet : A.det ≠ 0) :
    NeZero (2 * A.det).natAbs :=
  ⟨Int.natAbs_ne_zero.mpr (mul_ne_zero two_ne_zero hdet)⟩

/-- A prime `p ∤ 2 det A` is odd, and the determinant of `A` is a unit in `ℤ_p`. -/
private theorem ne_two_and_isUnit_det_map {A : Matrix n n ℤ} {p : ℕ} [Fact p.Prime]
    (hp : ¬ p ∣ (2 * A.det).natAbs) :
    p ≠ 2 ∧ IsUnit (A.map (Int.castRingHom ℤ_[p])).det := by
  rw [← Int.natCast_dvd] at hp
  refine ⟨?_, isUnit_det_map_padicInt_iff.mpr fun h => hp (h.mul_left 2)⟩
  rintro rfl
  exact hp (dvd_mul_right _ _)

/-- At an odd prime the Kronecker symbol of `4 (-1)^m det A` is the quadratic character of the
signed determinant of the reduction of `A`, the sign in the even-rank local density. -/
private theorem kroneckerSym_eq_quadraticChar {A : Matrix n n ℤ} {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) (m : ℕ) :
    TauCeti.kroneckerSym (4 * ((-1) ^ m * A.det)) p = quadraticChar (ZMod p)
      ((-1) ^ m * ((A.map (Int.castRingHom ℤ_[p])).map PadicInt.toZMod).det) := by
  have h2 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_ofNat, ne_eq, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    exact fun h => hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)
  have hmap : (A.map (Int.castRingHom ℤ_[p])).map PadicInt.toZMod =
      A.map (Int.castRingHom (ZMod p)) := by
    rw [Matrix.map_map]
    exact congrArg A.map (funext fun k => map_intCast PadicInt.toZMod k)
  rw [TauCeti.kroneckerSym_eq_legendreSym _ p hp, legendreSym.mul,
    show (4 : ℤ) = 2 ^ 2 by norm_num, legendreSym.sq_one' p h2, one_mul, hmap,
    ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  simp [legendreSym]

/-- The `ζ` part of the product: over the primes `p ∤ N`, the product of
`∏_{i=1}^{m} (1 - p^{-2i})⁻¹` is `∏_{i=1}^{m} ζ^{(S)}(2i)`, with `S` the primes dividing `N`. -/
private theorem hasProd_prod_inv_one_sub_cpow (N : ℕ) [NeZero N] (m : ℕ) :
    HasProd (fun p : {p : Nat.Primes // ¬ (p : ℕ) ∣ N} =>
        ∏ i ∈ Finset.range m, (1 - ((p : ℕ) : ℂ) ^ (-((2 * (i + 1) : ℕ) : ℂ)))⁻¹)
      (∏ i ∈ Finset.range m, (∏ q ∈ N.primeFactors, (1 - (q : ℂ) ^ (-((2 * (i + 1) : ℕ) : ℂ)))) *
        riemannZeta ((2 * (i + 1) : ℕ) : ℂ)) := by
  rw [Finset.prod_congr rfl fun i _ => (DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
    (N := N) (Nat.cast_ne_one.mpr (by omega : 2 * (i + 1) ≠ 1))).symm]
  exact hasProd_prod fun i _ => DirichletCharacter.LFunctionTrivChar_eulerProduct_hasProd N
    (by rw [Complex.natCast_re]; exact_mod_cast (by omega : 1 < 2 * (i + 1)))

/-- The `ζ` part of the product is nonzero. -/
private theorem prod_mul_riemannZeta_ne_zero (N : ℕ) [NeZero N] (m : ℕ) :
    (∏ i ∈ Finset.range m, (∏ q ∈ N.primeFactors, (1 - (q : ℂ) ^ (-((2 * (i + 1) : ℕ) : ℂ)))) *
      riemannZeta ((2 * (i + 1) : ℕ) : ℂ)) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  rw [← DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta
    (Nat.cast_ne_one.mpr (by omega : 2 * (i + 1) ≠ 1))]
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _
    (Or.inr (Nat.cast_ne_one.mpr (by omega))) (by rw [Complex.natCast_re]; norm_cast; omega)

variable {A : Matrix n n ℤ}

/-- **The product of the normalized local densities over the good primes, in odd rank.** Let `A`
be a symmetric `(2m + 1) × (2m + 1)` integer matrix with nonzero determinant, and let `α p` be
its local density at every prime `p ∤ 2 det A`. Then the product of `(α p / 2)⁻¹` over those
primes converges to `∏_{i=1}^{m} ζ^{(S)}(2i)`, where `ζ^{(S)}(s) = ∏_{q ∈ S} (1 - q⁻ˢ) · ζ(s)` and
`S` is the set of primes dividing `2 det A`. -/
theorem hasProd_inv_half_localDensity_of_card_eq_two_mul_add_one (hA : Aᵀ = A)
    (hdet : A.det ≠ 0) {m : ℕ} (hn : Fintype.card n = 2 * m + 1) {α : ℕ → ℚ}
    (hα : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ (2 * A.det).natAbs →
      Tendsto (fun r => ((A.map (Int.castRingHom ℤ_[p])).localDensityCount r : ℚ) /
        (p : ℚ) ^ (r * (Fintype.card n).choose 2)) atTop (𝓝 (α p))) :
    HasProd (fun p : {p : Nat.Primes // ¬ (p : ℕ) ∣ (2 * A.det).natAbs} => ((α p : ℂ) / 2)⁻¹)
      (∏ i ∈ Finset.range m, (∏ q ∈ (2 * A.det).natAbs.primeFactors,
        (1 - (q : ℂ) ^ (-((2 * (i + 1) : ℕ) : ℂ)))) * riemannZeta ((2 * (i + 1) : ℕ) : ℂ)) := by
  have := neZero_natAbs_two_mul_det hdet
  convert hasProd_prod_inv_one_sub_cpow (2 * A.det).natAbs m using 1 with p
  funext p
  have : Fact (p : ℕ).Prime := ⟨p.1.prop⟩
  obtain ⟨hp2, hu⟩ := ne_two_and_isUnit_det_map p.prop
  rw [tendsto_nhds_unique (hα p p.prop)
    (tendsto_localDensityCount_div_of_card_eq_two_mul_add_one hp2
      (by rw [← transpose_map, hA]) hu hn)]
  simp only [Complex.cpow_neg, Complex.cpow_natCast, Finset.prod_inv_distrib]
  push_cast
  ring

/-- **The product of the normalized local densities over the good primes is nonzero, in odd
rank.** -/
theorem tprod_inv_half_localDensity_ne_zero_of_card_eq_two_mul_add_one (hA : Aᵀ = A)
    (hdet : A.det ≠ 0) {m : ℕ} (hn : Fintype.card n = 2 * m + 1) {α : ℕ → ℚ}
    (hα : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ (2 * A.det).natAbs →
      Tendsto (fun r => ((A.map (Int.castRingHom ℤ_[p])).localDensityCount r : ℚ) /
        (p : ℚ) ^ (r * (Fintype.card n).choose 2)) atTop (𝓝 (α p))) :
    ∏' p : {p : Nat.Primes // ¬ (p : ℕ) ∣ (2 * A.det).natAbs}, ((α p : ℂ) / 2)⁻¹ ≠ 0 := by
  have := neZero_natAbs_two_mul_det hdet
  rw [(hasProd_inv_half_localDensity_of_card_eq_two_mul_add_one hA hdet hn hα).tprod_eq]
  exact prod_mul_riemannZeta_ne_zero _ m

/-- **The product of the normalized local densities over the good primes, in rank `1`**: every
normalized density `α p / 2` is `1`, and the product is `1`. -/
theorem hasProd_inv_half_localDensity_of_card_eq_one (hA : Aᵀ = A) (hdet : A.det ≠ 0)
    (hn : Fintype.card n = 1) {α : ℕ → ℚ}
    (hα : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ (2 * A.det).natAbs →
      Tendsto (fun r => ((A.map (Int.castRingHom ℤ_[p])).localDensityCount r : ℚ) /
        (p : ℚ) ^ (r * (Fintype.card n).choose 2)) atTop (𝓝 (α p))) :
    HasProd (fun p : {p : Nat.Primes // ¬ (p : ℕ) ∣ (2 * A.det).natAbs} => ((α p : ℂ) / 2)⁻¹)
      1 := by
  simpa using hasProd_inv_half_localDensity_of_card_eq_two_mul_add_one hA hdet (m := 0) hn hα

/-- **The product of the normalized local densities over the good primes, in even rank at
least `4`.** Let `A` be a symmetric `(2m + 2) × (2m + 2)` integer matrix with `m ≥ 1` and nonzero
determinant, and let `α p` be its local density at every prime `p ∤ 2 det A`. Then the product of
`(α p / 2)⁻¹` over those primes converges to `∏_{i=1}^{m} ζ^{(S)}(2i) · L(m + 1, χ_L)`, where
`ζ^{(S)}(s) = ∏_{q ∈ S} (1 - q⁻ˢ) · ζ(s)` for `S` the set of primes dividing `2 det A`, and `χ_L` is
the Kronecker character of `4 (-1)^{m+1} det A`: it vanishes on `S`, and its value at a prime
`p ∉ S` is the Legendre symbol `((-1)^{m+1} det A | p)`. -/
theorem hasProd_inv_half_localDensity_of_card_eq_two_mul_add_two (hA : Aᵀ = A)
    (hdet : A.det ≠ 0) {m : ℕ} (hm : m ≠ 0) (hn : Fintype.card n = 2 * m + 2) {α : ℕ → ℚ}
    (hα : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ (2 * A.det).natAbs →
      Tendsto (fun r => ((A.map (Int.castRingHom ℤ_[p])).localDensityCount r : ℚ) /
        (p : ℚ) ^ (r * (Fintype.card n).choose 2)) atTop (𝓝 (α p))) :
    HasProd (fun p : {p : Nat.Primes // ¬ (p : ℕ) ∣ (2 * A.det).natAbs} => ((α p : ℂ) / 2)⁻¹)
      ((∏ i ∈ Finset.range m, (∏ q ∈ (2 * A.det).natAbs.primeFactors,
        (1 - (q : ℂ) ^ (-((2 * (i + 1) : ℕ) : ℂ)))) * riemannZeta ((2 * (i + 1) : ℕ) : ℂ)) *
        L ↗(TauCeti.kroneckerChar ℂ (4 * ((-1) ^ (m + 1) * A.det))
          (Or.inl (Int.modEq_zero_iff_dvd.mpr (dvd_mul_right 4 _)))
          (mul_ne_zero four_ne_zero (mul_ne_zero (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
            hdet))) ((m + 1 : ℕ) : ℂ)) := by
  have := neZero_natAbs_two_mul_det hdet
  refine ((hasProd_prod_inv_one_sub_cpow (2 * A.det).natAbs m).mul
    (DirichletCharacter.LSeries_eulerProduct_hasProd_subtype _
      (by rw [Complex.natCast_re]; exact_mod_cast (by omega : 1 < m + 1)) fun p hp => ?_)).congr_fun
    fun p => ?_
  · -- The character vanishes at every prime dividing `2 det A`, as such a prime divides
    -- `4 (-1)^{m+1} det A`.
    rw [TauCeti.kroneckerChar_natCast, Int.cast_eq_zero, TauCeti.kroneckerSym_eq_zero_iff]
    intro h
    have hdvd : ((p : ℕ) : ℤ) ∣ 4 * ((-1) ^ (m + 1) * A.det) :=
      (Int.natCast_dvd.mpr (not_not.mp hp)).trans ⟨2 * (-1) ^ (m + 1), by ring⟩
    rw [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_natCast,
      Nat.gcd_eq_right (Int.natCast_dvd.mp hdvd)] at h
    exact p.prop.ne_one h
  have : Fact (p : ℕ).Prime := ⟨p.1.prop⟩
  obtain ⟨hp2, hu⟩ := ne_two_and_isUnit_det_map p.prop
  rw [tendsto_nhds_unique (hα p p.prop)
    (tendsto_localDensityCount_div_of_card_eq_two_mul_add_two hp2
      (by rw [← transpose_map, hA]) hu hn), TauCeti.kroneckerChar_natCast,
    kroneckerSym_eq_quadraticChar hp2]
  simp only [Complex.cpow_neg, Complex.cpow_natCast, Finset.prod_inv_distrib]
  push_cast
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- **The product of the normalized local densities over the good primes is nonzero, in even rank
at least `4`.** -/
theorem tprod_inv_half_localDensity_ne_zero_of_card_eq_two_mul_add_two (hA : Aᵀ = A)
    (hdet : A.det ≠ 0) {m : ℕ} (hm : m ≠ 0) (hn : Fintype.card n = 2 * m + 2) {α : ℕ → ℚ}
    (hα : ∀ (p : ℕ) [Fact p.Prime], ¬ p ∣ (2 * A.det).natAbs →
      Tendsto (fun r => ((A.map (Int.castRingHom ℤ_[p])).localDensityCount r : ℚ) /
        (p : ℚ) ^ (r * (Fintype.card n).choose 2)) atTop (𝓝 (α p))) :
    ∏' p : {p : Nat.Primes // ¬ (p : ℕ) ∣ (2 * A.det).natAbs}, ((α p : ℂ) / 2)⁻¹ ≠ 0 := by
  have := neZero_natAbs_two_mul_det hdet
  rw [(hasProd_inv_half_localDensity_of_card_eq_two_mul_add_two hA hdet hm hn hα).tprod_eq]
  exact mul_ne_zero (prod_mul_riemannZeta_ne_zero _ m)
    (DirichletCharacter.LSeries_ne_zero_of_one_lt_re _
      (by rw [Complex.natCast_re]; exact_mod_cast (by omega : 1 < m + 1)))

end Matrix
