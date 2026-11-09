/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.RationalSubset.Basic
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.FractionalBound

/-!
# Fractional valuation bounds on the adic spectrum

On the adic spectrum `Spa(A, A⁺)` the fractional bounds `{|f| ≤ |g| ^ q}` and `{|f| ≥ |g| ^ q}`
of `TauCeti.ValuationSpectrum.fracPowLE` and `TauCeti.ValuationSpectrum.fracPowGE` are rational
subsets when `g` is a unit: writing `q = a / b` in lowest terms,

```text
{|f| ≤ |g| ^ q} ∩ Spa(A, A⁺) = R({f ^ b, g ^ a} / g ^ a),
{|f| ≥ |g| ^ q} ∩ Spa(A, A⁺) = R({g ^ a, f ^ b} / f ^ b).
```

This is the shape of the Hasse domains `{|Ha| ≥ |p| ^ ε}` and of the discs `{|T| ≤ |ϖ| ^ q}`.

When the threshold `|g| ^ q` is realised by an element, the fractional bound is an ordinary one:
if `c ^ b = g ^ a u` for a unit `u` with `u, u⁻¹ ∈ A⁺`, then `v(u) = 1` on `Spa(A, A⁺)`, and there
`|f| ≤ |g| ^ q` is `v(f) ≤ v(c)` and `|f| ≥ |g| ^ q` is `v(c) ≤ v(f)`. For instance
`c = ϖ ^ (a / b)` in `K(ϖ ^ (1 / b))`, or, in `ℤ_p^cycl` and for `ε` in its value group
`(1 / (p - 1)) ℤ[1 / p]`, a product `c` of powers of the `ζ_{p^n} - 1` with `|c| = |p| ^ ε`. For the
same reason the bounds do not change when `f` is multiplied by such a unit.

## Main results

* `TauCeti.ValuationSpectrum.fracPowLE_inter_spa`, `TauCeti.ValuationSpectrum.fracPowGE_inter_spa`:
  for a unit `g`, the fractional bounds cut out rational subsets of `Spa(A, A⁺)`.
* `TauCeti.ValuationSpectrum.mem_fracPowLE_iff_vle_of_pow_eq`,
  `TauCeti.ValuationSpectrum.mem_fracPowGE_iff_vle_of_pow_eq`: on `Spa(A, A⁺)`, a fractional bound
  whose threshold is realised by an element up to a unit of `A⁺` is an ordinary bound.
* `TauCeti.ValuationSpectrum.fracPowLE_mul_left_inter_spa`,
  `TauCeti.ValuationSpectrum.fracPowGE_mul_left_inter_spa`: on `Spa(A, A⁺)`, the bounds are
  unchanged when `f` is multiplied by a unit of `A⁺`.

## References

* P. Scholze, *On torsion in the cohomology of locally symmetric varieties*, Ann. of Math. 182
  (2015), §III.2, Definition III.2.12.
* C. Birkbeck, B. Heuer and C. Williams, *Overconvergent Hilbert modular forms via perfectoid
  modular varieties*, §2.1.
-/

public section

open scoped NNRat

namespace TauCeti.ValuationSpectrum

variable {A : Type*} [CommRing A] [TopologicalSpace A]

/-- **Fractional upper bounds by a unit are rational**: if `g` is a unit, then on `Spa(A, A⁺)` the
locus `{|f| ≤ |g| ^ q}` is the rational subset `R({f ^ b, g ^ a} / g ^ a)` for `q = a / b` in
lowest terms. -/
theorem fracPowLE_inter_spa [DecidableEq A] (Aplus : Subring A) (f : A) {g : A} (hg : IsUnit g)
    (q : ℚ≥0) :
    fracPowLE f g q ∩ spa Aplus = rationalSubset Aplus {f ^ q.den, g ^ q.num} (g ^ q.num) := by
  have hg' (v : Spv A) : ¬ v.toValuativeRel.vle (g ^ q.num) 0 :=
    @TauCeti.ValuativeRel.not_vle_zero_of_isUnit A _ v.toValuativeRel _ (hg.pow q.num)
  ext v
  simp only [mem_fracPowLE, Set.mem_inter_iff, mem_rationalSubset_iff,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    v.toValuativeRel.vle_refl, hg' v, not_false_eq_true, and_true]
  exact and_comm

/-- **Fractional lower bounds by a unit are rational**: if `g` is a unit, then on `Spa(A, A⁺)` the
locus `{|f| ≥ |g| ^ q}` is the rational subset `R({g ^ a, f ^ b} / f ^ b)` for `q = a / b` in
lowest terms. -/
theorem fracPowGE_inter_spa [DecidableEq A] (Aplus : Subring A) (f : A) {g : A} (hg : IsUnit g)
    (q : ℚ≥0) :
    fracPowGE f g q ∩ spa Aplus = rationalSubset Aplus {g ^ q.num, f ^ q.den} (f ^ q.den) := by
  have hg' (v : Spv A) : ¬ v.toValuativeRel.vle (g ^ q.num) 0 :=
    @TauCeti.ValuativeRel.not_vle_zero_of_isUnit A _ v.toValuativeRel _ (hg.pow q.num)
  ext v
  simp only [mem_fracPowGE, Set.mem_inter_iff, mem_rationalSubset_iff,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    v.toValuativeRel.vle_refl, and_true]
  exact ⟨fun ⟨hv, hspa⟩ ↦ ⟨hspa, hv, fun h ↦ hg' v (v.toValuativeRel.vle_trans hv h)⟩,
    fun ⟨hspa, hv, _⟩ ↦ ⟨hv, hspa⟩⟩

variable {Aplus : Subring A} {v : Spv A} {f g c : A} {q : ℚ≥0} {a b : ℕ}

/-- If `c ^ b = g ^ a u` for a unit `u` with `u, u⁻¹ ∈ A⁺`, then `v(c) ^ b = v(g) ^ a` at every
point of `Spa(A, A⁺)`. -/
private theorem valuation_pow_eq_of_pow_eq (hv : v ∈ spa Aplus) (u : Aˣ) (hu : (u : A) ∈ Aplus)
    (hu' : ((u⁻¹ : Aˣ) : A) ∈ Aplus) (hc : c ^ b = g ^ a * u) :
    v.valuation (c ^ b) = v.valuation (g ^ a) := by
  rw [hc, map_mul, valuation_units_eq_one_of_mem_spa hv u hu hu', mul_one]

/-- **A realised threshold turns a fractional upper bound into an ordinary one**: if
`c ^ b = g ^ a u` for a unit `u` with `u, u⁻¹ ∈ A⁺` and `q = a / b` with `b ≠ 0`, then a point `v`
of `Spa(A, A⁺)` satisfies `|f(v)| ≤ |g(v)| ^ q` exactly when `v(f) ≤ v(c)`. -/
theorem mem_fracPowLE_iff_vle_of_pow_eq (hv : v ∈ spa Aplus) (u : Aˣ) (hu : (u : A) ∈ Aplus)
    (hu' : ((u⁻¹ : Aˣ) : A) ∈ Aplus) (hb : b ≠ 0) (hq : q = a / b) (hc : c ^ b = g ^ a * u) :
    v ∈ fracPowLE f g q ↔ v.toValuativeRel.vle f c := by
  rw [mem_fracPowLE_iff hb hq, ← valuation_le_iff, ← valuation_pow_eq_of_pow_eq hv u hu hu' hc,
    map_pow, map_pow, pow_le_pow_iff_left₀ zero_le zero_le hb, valuation_le_iff]

/-- **A realised threshold turns a fractional lower bound into an ordinary one**: if
`c ^ b = g ^ a u` for a unit `u` with `u, u⁻¹ ∈ A⁺` and `q = a / b` with `b ≠ 0`, then a point `v`
of `Spa(A, A⁺)` satisfies `|f(v)| ≥ |g(v)| ^ q` exactly when `v(c) ≤ v(f)`. -/
theorem mem_fracPowGE_iff_vle_of_pow_eq (hv : v ∈ spa Aplus) (u : Aˣ) (hu : (u : A) ∈ Aplus)
    (hu' : ((u⁻¹ : Aˣ) : A) ∈ Aplus) (hb : b ≠ 0) (hq : q = a / b) (hc : c ^ b = g ^ a * u) :
    v ∈ fracPowGE f g q ↔ v.toValuativeRel.vle c f := by
  rw [mem_fracPowGE_iff hb hq, ← valuation_le_iff, ← valuation_pow_eq_of_pow_eq hv u hu hu' hc,
    map_pow, map_pow, pow_le_pow_iff_left₀ zero_le zero_le hb, valuation_le_iff]

variable (Aplus f g q)

/-- **Fractional upper bounds are invariant under units of `A⁺`**: if `u, u⁻¹ ∈ A⁺`, then on
`Spa(A, A⁺)` the loci `{|u f| ≤ |g| ^ q}` and `{|f| ≤ |g| ^ q}` agree. -/
theorem fracPowLE_mul_left_inter_spa (u : Aˣ) (hu : (u : A) ∈ Aplus)
    (hu' : ((u⁻¹ : Aˣ) : A) ∈ Aplus) :
    fracPowLE (u * f) g q ∩ spa Aplus = fracPowLE f g q ∩ spa Aplus := by
  ext v
  simp only [Set.mem_inter_iff, mem_fracPowLE, and_congr_left_iff]
  intro hv
  rw [← valuation_le_iff, ← valuation_le_iff, mul_pow, map_mul, map_pow v.valuation (u : A),
    valuation_units_eq_one_of_mem_spa hv u hu hu', one_pow, one_mul]

/-- **Fractional lower bounds are invariant under units of `A⁺`**: if `u, u⁻¹ ∈ A⁺`, then on
`Spa(A, A⁺)` the loci `{|u f| ≥ |g| ^ q}` and `{|f| ≥ |g| ^ q}` agree. -/
theorem fracPowGE_mul_left_inter_spa (u : Aˣ) (hu : (u : A) ∈ Aplus)
    (hu' : ((u⁻¹ : Aˣ) : A) ∈ Aplus) :
    fracPowGE (u * f) g q ∩ spa Aplus = fracPowGE f g q ∩ spa Aplus := by
  ext v
  simp only [Set.mem_inter_iff, mem_fracPowGE, and_congr_left_iff]
  intro hv
  rw [← valuation_le_iff, ← valuation_le_iff, mul_pow, map_mul, map_pow v.valuation (u : A),
    valuation_units_eq_one_of_mem_spa hv u hu hu', one_pow, one_mul]

end TauCeti.ValuationSpectrum

end
