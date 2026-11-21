/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.Basic

import TauCeti.Algebra.Order.GroupWithZero.Pow
import TauCeti.Data.NNRat.CommonDenominator

/-!
# Fractional valuation bounds

Let `A` be a commutative ring, `f, g ∈ A` and `q ∈ ℚ≥0`. The loci `{|f| ≤ |g| ^ q}` and
`{|f| ≥ |g| ^ q}` of the valuation spectrum are defined without adjoining a `q`-th root of `g`:
writing `q = a / b` with `b ≠ 0`,

```text
|f(v)| ≤ |g(v)| ^ q   :⇔   v(f ^ b) ≤ v(g ^ a),
|f(v)| ≥ |g(v)| ^ q   :⇔   v(g ^ a) ≤ v(f ^ b).
```

The conditions do not depend on the fraction chosen, because `x ↦ x ^ n` is strictly increasing
on the totally ordered value monoid of a point; the definitions use the reduced fraction
`q = q.num / q.den`, and `mem_fracPowLE_iff` reads membership off any other one. Thresholds such
as `|p| ^ (1 / 2)` over `ℚ_[p]` or `|ϖ| ^ ε` for a pseudouniformiser `ϖ`, which are not the
absolute value of any element, therefore cut out well-defined sets. These are the radii of
discs and annuli in rigid geometry and the thresholds of the Hasse domains `{|Ha| ≥ |p| ^ ε}`.

The file proves that the conditions depend only on the ratio `q`, computes them for integral and
degenerate exponents, and establishes their behaviour under pullback, monotonicity in `q` where
`|g| ≤ 1`, and the power and product rules.

## Main definitions

* `TauCeti.ValuationSpectrum.fracPowLE f g q`: the set `{v ∈ Spv A | |f(v)| ≤ |g(v)| ^ q}`.
* `TauCeti.ValuationSpectrum.fracPowGE f g q`: the set `{v ∈ Spv A | |f(v)| ≥ |g(v)| ^ q}`.

## Main results

* `TauCeti.ValuationSpectrum.mem_fracPowLE_iff`, `TauCeti.ValuationSpectrum.mem_fracPowGE_iff`:
  membership may be read off any fraction `q = a / b`.
* `TauCeti.ValuationSpectrum.fracPowLE_natCast`, `TauCeti.ValuationSpectrum.fracPowGE_natCast`:
  for an integral exponent `n`, the conditions are `v(f) ≤ v(g ^ n)` and `v(g ^ n) ≤ v(f)`.
* `TauCeti.ValuationSpectrum.comap_preimage_fracPowLE`,
  `TauCeti.ValuationSpectrum.comap_preimage_fracPowGE`: compatibility with pullback.
* `TauCeti.ValuationSpectrum.mem_fracPowLE_of_le`, `TauCeti.ValuationSpectrum.mem_fracPowGE_of_le`:
  where `|g| ≤ 1`, the bound `|f| ≤ |g| ^ q` weakens and `|f| ≥ |g| ^ q` strengthens as `q`
  decreases.
* `TauCeti.ValuationSpectrum.fracPowLE_pow`, `TauCeti.ValuationSpectrum.fracPowGE_pow`: the power
  rule `|f ^ n| ≤ |g| ^ (n q) ↔ |f| ≤ |g| ^ q`.
* `TauCeti.ValuationSpectrum.fracPowLE_inter_fracPowLE_subset`,
  `TauCeti.ValuationSpectrum.fracPowGE_inter_fracPowGE_subset`: the product rule
  `|f| ≤ |g| ^ q ∧ |f'| ≤ |g| ^ q' → |f f'| ≤ |g| ^ (q + q')`.

## References

* C. Birkbeck, B. Heuer and C. Williams, *Overconvergent Hilbert modular forms via perfectoid
  modular varieties*, §2.1.
* P. Scholze, *On torsion in the cohomology of locally symmetric varieties*, Ann. of Math. 182
  (2015), §III.2, Definition III.2.12.
* B. Conrad, *Modular curves and rigid-analytic spaces*, Pure Appl. Math. Q. 2 (2006), §4.1.
-/

public section

open scoped NNRat

namespace TauCeti.ValuationSpectrum

variable {A B : Type*} [CommRing A] [CommRing B]

/-- **The locus `{|f| ≤ |g| ^ q}`**: the points `v ∈ Spv A` with `v(f ^ b) ≤ v(g ^ a)`, where
`q = a / b` is in lowest terms. No root of `g` is adjoined; `mem_fracPowLE_iff` reads the condition
off any fraction representing `q`. -/
def fracPowLE (f g : A) (q : ℚ≥0) : Set (Spv A) :=
  {v | v.toValuativeRel.vle (f ^ q.den) (g ^ q.num)}

/-- **The locus `{|f| ≥ |g| ^ q}`**: the points `v ∈ Spv A` with `v(g ^ a) ≤ v(f ^ b)`, where
`q = a / b` is in lowest terms. No root of `g` is adjoined; `mem_fracPowGE_iff` reads the condition
off any fraction representing `q`. -/
def fracPowGE (f g : A) (q : ℚ≥0) : Set (Spv A) :=
  {v | v.toValuativeRel.vle (g ^ q.num) (f ^ q.den)}

/-- The defining equation of `fracPowLE`, in terms of the reduced fraction `q.num / q.den`. The
definition is not exposed across the module boundary; this equation is how consumers unfold it. -/
theorem fracPowLE_def (f g : A) (q : ℚ≥0) :
    fracPowLE f g q = {v | v.toValuativeRel.vle (f ^ q.den) (g ^ q.num)} := (rfl)

/-- The defining equation of `fracPowGE`, in terms of the reduced fraction `q.num / q.den`. The
definition is not exposed across the module boundary; this equation is how consumers unfold it. -/
theorem fracPowGE_def (f g : A) (q : ℚ≥0) :
    fracPowGE f g q = {v | v.toValuativeRel.vle (g ^ q.num) (f ^ q.den)} := (rfl)

variable {f g : A} {q : ℚ≥0}

/-- Membership in `{|f| ≤ |g| ^ q}`, in terms of the reduced fraction `q = q.num / q.den`:
`v(f ^ q.den) ≤ v(g ^ q.num)`. -/
theorem mem_fracPowLE {v : Spv A} :
    v ∈ fracPowLE f g q ↔ v.toValuativeRel.vle (f ^ q.den) (g ^ q.num) := Iff.rfl

/-- Membership in `{|f| ≥ |g| ^ q}`, in terms of the reduced fraction `q = q.num / q.den`:
`v(g ^ q.num) ≤ v(f ^ q.den)`. -/
theorem mem_fracPowGE {v : Spv A} :
    v ∈ fracPowGE f g q ↔ v.toValuativeRel.vle (g ^ q.num) (f ^ q.den) := Iff.rfl

/-- **Membership in `{|f| ≤ |g| ^ q}` from any fraction**: if `q = a / b` with `b ≠ 0`, then
`v ∈ fracPowLE f g q` exactly when `v(f ^ b) ≤ v(g ^ a)`. -/
theorem mem_fracPowLE_iff {a b : ℕ} (hb : b ≠ 0) (hq : q = a / b) {v : Spv A} :
    v ∈ fracPowLE f g q ↔ v.toValuativeRel.vle (f ^ b) (g ^ a) := by
  rw [mem_fracPowLE, ← valuation_le_iff, ← valuation_le_iff, map_pow, map_pow,
    map_pow, map_pow]
  exact pow_le_pow_iff_of_mul_eq zero_le zero_le hb q.den_ne_zero (mul_comm _ _)
    ((NNRat.eq_div_iff_num_mul_eq_mul_den hb).mp hq)

/-- **Membership in `{|f| ≥ |g| ^ q}` from any fraction**: if `q = a / b` with `b ≠ 0`, then
`v ∈ fracPowGE f g q` exactly when `v(g ^ a) ≤ v(f ^ b)`. -/
theorem mem_fracPowGE_iff {a b : ℕ} (hb : b ≠ 0) (hq : q = a / b) {v : Spv A} :
    v ∈ fracPowGE f g q ↔ v.toValuativeRel.vle (g ^ a) (f ^ b) := by
  rw [mem_fracPowGE, ← valuation_le_iff, ← valuation_le_iff, map_pow, map_pow,
    map_pow, map_pow]
  exact pow_le_pow_iff_of_mul_eq zero_le zero_le hb q.den_ne_zero
    ((NNRat.eq_div_iff_num_mul_eq_mul_den hb).mp hq) (mul_comm _ _)

/-! ### Integral and degenerate exponents -/

variable (f g)

/-- For an integral exponent `n`, the bound `|f| ≤ |g| ^ n` is `v(f) ≤ v(g ^ n)`. -/
@[simp]
theorem fracPowLE_natCast (n : ℕ) :
    fracPowLE f g n = {v | v.toValuativeRel.vle f (g ^ n)} := by
  ext v
  rw [mem_fracPowLE_iff one_ne_zero (div_one _).symm, pow_one, Set.mem_ofPred_eq]

/-- For an integral exponent `n`, the bound `|f| ≥ |g| ^ n` is `v(g ^ n) ≤ v(f)`. -/
@[simp]
theorem fracPowGE_natCast (n : ℕ) :
    fracPowGE f g n = {v | v.toValuativeRel.vle (g ^ n) f} := by
  ext v
  rw [mem_fracPowGE_iff one_ne_zero (div_one _).symm, pow_one, Set.mem_ofPred_eq]

/-- For the exponent `0`, the bound `|f| ≤ |g| ^ 0` is `v(f) ≤ 1`, whatever `g` is. -/
@[simp]
theorem fracPowLE_zero : fracPowLE f g 0 = {v | v.toValuativeRel.vle f 1} := by
  simpa using fracPowLE_natCast f g 0

/-- For the exponent `0`, the bound `|f| ≥ |g| ^ 0` is `1 ≤ v(f)`, whatever `g` is. -/
@[simp]
theorem fracPowGE_zero : fracPowGE f g 0 = {v | v.toValuativeRel.vle 1 f} := by
  simpa using fracPowGE_natCast f g 0

/-- For `g = 0` and a positive exponent, `|f| ≤ |0| ^ q` is the vanishing locus `{v(f) = 0}` of
`f`, i.e. the points whose support contains `f`. -/
@[simp]
theorem fracPowLE_zero_right (hq : q ≠ 0) :
    fracPowLE f 0 q = {v | v.toValuativeRel.vle f 0} := by
  ext v
  rw [mem_fracPowLE, Set.mem_ofPred_eq, zero_pow (NNRat.num_ne_zero.mpr hq),
    vle_pow_zero_iff v f q.den_ne_zero]

/-- For `g = 0` and a positive exponent, `|f| ≥ |0| ^ q` holds everywhere. -/
@[simp]
theorem fracPowGE_zero_right (hq : q ≠ 0) : fracPowGE f 0 q = Set.univ := by
  ext v
  rw [mem_fracPowGE, zero_pow (NNRat.num_ne_zero.mpr hq)]
  exact iff_of_true (v.toValuativeRel.zero_vle _) trivial

variable {f g}

/-- If `g` is off the support of `v` and `v ∈ {|f| ≥ |g| ^ q}`, then `f` is off the support of
`v` too. -/
theorem not_vle_zero_of_mem_fracPowGE {v : Spv A} (hg : ¬ v.toValuativeRel.vle g 0)
    (hv : v ∈ fracPowGE f g q) : ¬ v.toValuativeRel.vle f 0 := fun hf ↦ by
  rw [← mem_supp_iff] at hg
  refine hg (Ideal.IsPrime.mem_of_pow_mem inferInstance q.num ?_)
  rw [mem_supp_iff]
  exact v.toValuativeRel.vle_trans hv ((vle_pow_zero_iff v f q.den_ne_zero).mpr hf)

/-! ### Pullback -/

/-- **Pullback of `{|f| ≤ |g| ^ q}`**: the preimage under `comap φ` is `{|φ f| ≤ |φ g| ^ q}`. -/
@[simp]
theorem comap_preimage_fracPowLE (φ : A →+* B) (f g : A) (q : ℚ≥0) :
    comap φ ⁻¹' fracPowLE f g q = fracPowLE (φ f) (φ g) q := by
  ext v
  simp [mem_fracPowLE]

/-- **Pullback of `{|f| ≥ |g| ^ q}`**: the preimage under `comap φ` is `{|φ f| ≥ |φ g| ^ q}`. -/
@[simp]
theorem comap_preimage_fracPowGE (φ : A →+* B) (f g : A) (q : ℚ≥0) :
    comap φ ⁻¹' fracPowGE f g q = fracPowGE (φ f) (φ g) q := by
  ext v
  simp [mem_fracPowGE]

/-! ### Monotonicity in the exponent -/

/-- **Upper bounds weaken as the exponent decreases** where `|g| ≤ 1`: if `v(g) ≤ 1`,
`|f(v)| ≤ |g(v)| ^ q'` and `q ≤ q'`, then `|f(v)| ≤ |g(v)| ^ q`. -/
theorem mem_fracPowLE_of_le {q' : ℚ≥0} {v : Spv A} (hg : v.toValuativeRel.vle g 1)
    (hq : q ≤ q') (hv : v ∈ fracPowLE f g q') : v ∈ fracPowLE f g q := by
  obtain ⟨h₁, h₂⟩ := NNRat.eq_div_den_mul_den q q'
  have hb := mul_ne_zero q.den_ne_zero q'.den_ne_zero
  rw [mem_fracPowLE_iff hb h₂, ← valuation_le_iff, map_pow, map_pow] at hv
  rw [mem_fracPowLE_iff hb h₁, ← valuation_le_iff, map_pow, map_pow]
  rw [← valuation_le_iff, map_one] at hg
  exact hv.trans (pow_le_pow_of_le_one zero_le hg (NNRat.le_def.mp hq))

/-- **Lower bounds weaken as the exponent increases** where `|g| ≤ 1`: if `v(g) ≤ 1`,
`|f(v)| ≥ |g(v)| ^ q` and `q ≤ q'`, then `|f(v)| ≥ |g(v)| ^ q'`. -/
theorem mem_fracPowGE_of_le {q' : ℚ≥0} {v : Spv A} (hg : v.toValuativeRel.vle g 1)
    (hq : q ≤ q') (hv : v ∈ fracPowGE f g q) : v ∈ fracPowGE f g q' := by
  obtain ⟨h₁, h₂⟩ := NNRat.eq_div_den_mul_den q q'
  have hb := mul_ne_zero q.den_ne_zero q'.den_ne_zero
  rw [mem_fracPowGE_iff hb h₁, ← valuation_le_iff, map_pow, map_pow] at hv
  rw [mem_fracPowGE_iff hb h₂, ← valuation_le_iff, map_pow, map_pow]
  rw [← valuation_le_iff, map_one] at hg
  exact (pow_le_pow_of_le_one zero_le hg (NNRat.le_def.mp hq)).trans hv

/-! ### The power and product rules -/

/-- **The power rule for upper bounds**: for `n ≠ 0`, `|f ^ n| ≤ |g| ^ (n q)` exactly when
`|f| ≤ |g| ^ q`. -/
theorem fracPowLE_pow (f g : A) (q : ℚ≥0) {n : ℕ} (hn : n ≠ 0) :
    fracPowLE (f ^ n) g (n * q) = fracPowLE f g q := by
  ext v
  rw [mem_fracPowLE_iff q.den_ne_zero (q.natCast_mul_eq_div n), mem_fracPowLE,
    pow_right_comm, pow_mul', ← valuation_le_iff, ← valuation_le_iff,
    map_pow v.valuation (f ^ q.den), map_pow v.valuation (g ^ q.num)]
  exact pow_le_pow_iff_left₀ zero_le zero_le hn

/-- **The power rule for lower bounds**: for `n ≠ 0`, `|f ^ n| ≥ |g| ^ (n q)` exactly when
`|f| ≥ |g| ^ q`. -/
theorem fracPowGE_pow (f g : A) (q : ℚ≥0) {n : ℕ} (hn : n ≠ 0) :
    fracPowGE (f ^ n) g (n * q) = fracPowGE f g q := by
  ext v
  rw [mem_fracPowGE_iff q.den_ne_zero (q.natCast_mul_eq_div n), mem_fracPowGE,
    pow_right_comm, pow_mul', ← valuation_le_iff, ← valuation_le_iff,
    map_pow v.valuation (f ^ q.den), map_pow v.valuation (g ^ q.num)]
  exact pow_le_pow_iff_left₀ zero_le zero_le hn

/-- **The product rule for upper bounds**: `|f| ≤ |g| ^ q` and `|f'| ≤ |g| ^ q'` imply
`|f f'| ≤ |g| ^ (q + q')`. -/
theorem fracPowLE_inter_fracPowLE_subset (f f' g : A) (q q' : ℚ≥0) :
    fracPowLE f g q ∩ fracPowLE f' g q' ⊆ fracPowLE (f * f') g (q + q') := by
  rintro v ⟨hv, hv'⟩
  obtain ⟨h₁, h₂⟩ := NNRat.eq_div_den_mul_den q q'
  have hb := mul_ne_zero q.den_ne_zero q'.den_ne_zero
  rw [mem_fracPowLE_iff hb h₁, ← valuation_le_iff] at hv
  rw [mem_fracPowLE_iff hb h₂, ← valuation_le_iff] at hv'
  rw [mem_fracPowLE_iff hb ((NNRat.add_def q q').trans (NNRat.divNat_eq_div _ _)),
    ← valuation_le_iff, mul_pow, pow_add, map_mul, map_mul]
  exact mul_le_mul' hv hv'

/-- **The product rule for lower bounds**: `|f| ≥ |g| ^ q` and `|f'| ≥ |g| ^ q'` imply
`|f f'| ≥ |g| ^ (q + q')`. -/
theorem fracPowGE_inter_fracPowGE_subset (f f' g : A) (q q' : ℚ≥0) :
    fracPowGE f g q ∩ fracPowGE f' g q' ⊆ fracPowGE (f * f') g (q + q') := by
  rintro v ⟨hv, hv'⟩
  obtain ⟨h₁, h₂⟩ := NNRat.eq_div_den_mul_den q q'
  have hb := mul_ne_zero q.den_ne_zero q'.den_ne_zero
  rw [mem_fracPowGE_iff hb h₁, ← valuation_le_iff] at hv
  rw [mem_fracPowGE_iff hb h₂, ← valuation_le_iff] at hv'
  rw [mem_fracPowGE_iff hb ((NNRat.add_def q q').trans (NNRat.divNat_eq_div _ _)),
    ← valuation_le_iff, mul_pow, pow_add, map_mul, map_mul]
  exact mul_le_mul' hv hv'

end TauCeti.ValuationSpectrum

end
