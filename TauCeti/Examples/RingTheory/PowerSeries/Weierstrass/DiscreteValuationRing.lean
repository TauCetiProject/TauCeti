/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.IwasawaInvariants
public import TauCeti.RingTheory.Valuation.NormNormalization
public import TauCeti.Topology.Algebra.Valued.NormedValued

/-!
# Weierstrass preparation over the valuation ring of a complete discretely valued field

Let `K` be a complete nonarchimedean normed field whose valuation ring
`O = (NormedField.valuation (K := K)).integer` is a discrete valuation ring, and let `π` be a
uniformiser of `O`. The ring `O` is complete for its maximal ideal
(`Valuation.integer.isAdicComplete_maximalIdeal`), so Weierstrass preparation with a uniformiser
power applies to `O` with no further hypothesis: a nonzero `f ∈ O⟦X⟧` factors as

```text
f = C (π ^ μ(f)) * u * P,    u a unit of O⟦X⟧,    P distinguished of degree λ(f).
```

No finiteness of the residue field is needed. These examples state this factorisation and its
uniqueness for such `O`.

Reading the coefficients in `K` with the real additive valuation `AddValuation.ofNorm b` at the
base `b = ‖π‖⁻¹`, which is the normalised valuation of `O` (`AddValuation.ofNorm_map_eq_addVal`),
the invariants are Newton polygon data: `μ(f)` is the minimum height of the Newton polygon of `f`
and `λ(f)` is the first index at which it is attained.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, second edition, GTM 83, §7.1.
* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, second edition,
  (5.3.1)–(5.3.4).
-/

public section

open PowerSeries IsLocalRing

namespace TauCeti.Examples

variable {K : Type*} [NormedField K] [IsUltrametricDist K]
  [IsDiscreteValuationRing (NormedField.valuation (K := K)).integer]
  {π : (NormedField.valuation (K := K)).integer}

/-- **Weierstrass preparation over the valuation ring of a complete discretely valued field.** A
nonzero `f ∈ O⟦X⟧` is `C (π ^ μ(f))` times a unit times a distinguished polynomial of degree
`λ(f)`. -/
example [CompleteSpace K] (hπ : Irreducible π)
    {f : PowerSeries (NormedField.valuation (K := K)).integer} (hf : f ≠ 0) :
    ∃ (m : ℕ) (P : Polynomial (NormedField.valuation (K := K)).integer)
      (u : (PowerSeries (NormedField.valuation (K := K)).integer)ˣ),
      f.muInvariant = m ∧ P.natDegree = f.lambdaInvariant ∧
        P.IsDistinguishedAt (maximalIdeal (NormedField.valuation (K := K)).integer) ∧
        f = C (π ^ m) * u * P :=
  exists_pow_mul_distinguished_mul_unit hπ hf

/-- The exponent, the unit and the distinguished polynomial of such a factorisation are unique. -/
example (hπ : Irreducible π) {m m' : ℕ}
    {u u' : (PowerSeries (NormedField.valuation (K := K)).integer)ˣ}
    {P P' : Polynomial (NormedField.valuation (K := K)).integer}
    (hP : P.IsDistinguishedAt (maximalIdeal (NormedField.valuation (K := K)).integer))
    (hP' : P'.IsDistinguishedAt (maximalIdeal (NormedField.valuation (K := K)).integer)) :
    C (π ^ m) * u * P = C (π ^ m') * u' * P' ↔ m = m' ∧ u = u' ∧ P = P' :=
  C_pow_mul_unit_mul_inj hπ hP hP'

/-- In the base-`‖π‖⁻¹` normalisation, `μ(f)` is the minimum height of the Newton polygon of `f`
read in `K`. -/
example (hπ : Irreducible π) {b : ℝ} (hb : 1 < b)
    (hπb : ‖algebraMap (NormedField.valuation (K := K)).integer K π‖ = b⁻¹)
    (f : PowerSeries (NormedField.valuation (K := K)).integer) :
    IsLeast (Set.range ((f.map (algebraMap _ K)).newtonPolygon (AddValuation.ofNorm b hb)))
      (f.muInvariant.map ((↑) : ℕ → ℝ)) :=
  isLeast_range_newtonPolygon_map
    (AddValuation.ofNorm_map_eq_addVal _ (Valuation.integer.integers _).norm_algebraMap_le_one hb
      hπ hπb) f

/-- In the base-`‖π‖⁻¹` normalisation, `λ(f)` is the first index at which the Newton polygon of
`f` read in `K` attains its minimum height `μ(f)`. -/
example (hπ : Irreducible π) {b : ℝ} (hb : 1 < b)
    (hπb : ‖algebraMap (NormedField.valuation (K := K)).integer K π‖ = b⁻¹)
    (f : PowerSeries (NormedField.valuation (K := K)).integer) :
    IsLeast {n | (f.map (algebraMap _ K)).newtonPolygon (AddValuation.ofNorm b hb) n =
      f.muInvariant.map ((↑) : ℕ → ℝ)} f.lambdaInvariant :=
  isLeast_setOf_newtonPolygon_map_eq
    (AddValuation.ofNorm_map_eq_addVal _ (Valuation.integer.integers _).norm_algebraMap_le_one hb
      hπ hπb) f

end TauCeti.Examples
