/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Weierstrass.Division
public import TauCeti.RingTheory.PowerSeries.TateAlgebra
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

/-!
# Bounded Weierstrass quotient and remainder

Division by a multiplicatively distinguished series over a complete ultrametric normed
commutative ring gives continuous linear quotient and remainder operators on the algebra of
restricted series. The coefficient norm need not be multiplicative. The quotient has bound
`‖f‖⁻¹` and the remainder has bound one, for the Gauss norm at any positive real radius.

The remainder is represented in the same restricted algebra as the dividend; its coefficients
vanish from the distinguished degree onward, so it is the inclusion of a polynomial.
The decomposition identity and uniqueness characterize both operators, including division in
degree zero. Their values on multiples of the divisor and on lower-degree polynomials provide
normal forms for subsequent preparation and finite-quotient constructions.

## References

* F. Martin, *Overconvergent subanalytic subsets in the framework of Berkovich spaces*,
  J. Eur. Math. Soc. 18 (2016), Proposition 1.27.
* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.1, Theorem 2.
-/

public section

namespace TauCeti.PowerSeries

open scoped Topology

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] [CompleteSpace R]
  {c : ℝ} [Fact (0 < c)] {s : ℕ}

variable {f : PowerSeries.IsRestricted.subring (R := R) c}
  (hf : IsMulDistinguished c s (f : PowerSeries R))

private noncomputable def divisionPair (g : PowerSeries.IsRestricted.subring (R := R) c) :
    PowerSeries.IsRestricted.subring (R := R) c × PowerSeries.IsRestricted.subring (R := R) c :=
  (hf.existsUnique_mul_add_eq_subring (Fact.out : 0 < c) g).exists.choose

private theorem divisionPair_spec (g : PowerSeries.IsRestricted.subring (R := R) c) :
    (∀ n, s ≤ n → ((divisionPair hf g).2 : PowerSeries R).coeff n = 0) ∧
      (divisionPair hf g).1 * f + (divisionPair hf g).2 = g :=
  (hf.existsUnique_mul_add_eq_subring (Fact.out : 0 < c) g).exists.choose_spec

private theorem divisionPair_eq {g q r : PowerSeries.IsRestricted.subring (R := R) c}
    (hr : ∀ n, s ≤ n → (r : PowerSeries R).coeff n = 0) (h : q * f + r = g) :
    divisionPair hf g = (q, r) := by
  obtain ⟨p, -, huniq⟩ := hf.existsUnique_mul_add_eq_subring
    (Fact.out : 0 < c) g
  exact (huniq _ (divisionPair_spec hf g)).trans (huniq _ ⟨hr, h⟩).symm

private theorem norm_divisionPair (g : PowerSeries.IsRestricted.subring (R := R) c) :
    ‖g‖ = max (‖(divisionPair hf g).1‖ * ‖f‖) ‖(divisionPair hf g).2‖ := by
  have h := hf.gaussNorm_mul_add_eq_max (Fact.out : 0 < c)
    (divisionPair hf g).1.2 (divisionPair_spec hf g).1
  rw [mul_comm (f : PowerSeries R),
    mul_comm ((f : PowerSeries R).gaussNorm norm c)] at h
  rw [← norm_eq_gaussNorm, ← norm_eq_gaussNorm, ← norm_eq_gaussNorm] at h
  -- The subring operations coerce to the formal-series operations in the norm identity.
  simpa only [← Subring.coe_mul, ← Subring.coe_add, ← norm_eq_gaussNorm,
    (divisionPair_spec hf g).2] using h

private theorem norm_divisionPair_fst_le (g : PowerSeries.IsRestricted.subring (R := R) c) :
    ‖(divisionPair hf g).1‖ ≤ ‖f‖⁻¹ * ‖g‖ := by
  have hfpos : 0 < ‖f‖ := by
    rw [norm_eq_gaussNorm]
    exact hf.toIsDistinguished.gaussNorm_pos
  rw [inv_mul_eq_div, le_div_iff₀ hfpos, norm_divisionPair hf g]
  exact le_max_left _ _

private theorem norm_divisionPair_snd_le (g : PowerSeries.IsRestricted.subring (R := R) c) :
    ‖(divisionPair hf g).2‖ ≤ ‖g‖ := by
  rw [norm_divisionPair hf g]
  exact le_max_right _ _

private noncomputable def divisionLinearMap :
    PowerSeries.IsRestricted.subring (R := R) c →ₗ[R]
      PowerSeries.IsRestricted.subring (R := R) c ×
        PowerSeries.IsRestricted.subring (R := R) c where
  toFun := divisionPair hf
  map_add' g h := by
    apply divisionPair_eq hf
    · intro n hn
      simp [(divisionPair_spec hf g).1 n hn, (divisionPair_spec hf h).1 n hn]
    · simpa only [Prod.fst_add, Prod.snd_add, add_mul, add_add_add_comm] using
        congrArg₂ (· + ·) (divisionPair_spec hf g).2 (divisionPair_spec hf h).2
  map_smul' a g := by
    apply divisionPair_eq hf
    · intro n hn
      -- Coefficient scalar multiplication is multiplication by the constant series.
      simp [Algebra.smul_def, (divisionPair_spec hf g).1 n hn]
    · simpa only [RingHom.id_apply, smul_mul_assoc, ← smul_add] using
        congrArg (a • ·) (divisionPair_spec hf g).2

/-- The continuous `R`-linear quotient operator for division by `f`.
Its Gauss-norm bound is `‖f‖⁻¹`. -/
noncomputable def weierstrassDiv :
    PowerSeries.IsRestricted.subring (R := R) c →L[R] PowerSeries.IsRestricted.subring (R := R) c :=
  ((LinearMap.fst R _ _).comp (divisionLinearMap hf)).mkContinuous ‖f‖⁻¹
    (norm_divisionPair_fst_le hf)

/-- The continuous `R`-linear remainder operator for division by `f`.
It is contractive and its coefficients vanish in degrees at least `s`. -/
noncomputable def weierstrassMod :
    PowerSeries.IsRestricted.subring (R := R) c →L[R] PowerSeries.IsRestricted.subring (R := R) c :=
  ((LinearMap.snd R _ _).comp (divisionLinearMap hf)).mkContinuous 1
    (fun g ↦ by rw [one_mul]; exact norm_divisionPair_snd_le hf g)

private theorem weierstrassDiv_apply (g : PowerSeries.IsRestricted.subring (R := R) c) :
    weierstrassDiv hf g = (divisionPair hf g).1 := by
  simp only [weierstrassDiv, LinearMap.mkContinuous_apply, LinearMap.comp_apply,
    LinearMap.fst_apply, divisionLinearMap, LinearMap.coe_mk, AddHom.coe_mk]

private theorem weierstrassMod_apply (g : PowerSeries.IsRestricted.subring (R := R) c) :
    weierstrassMod hf g = (divisionPair hf g).2 := by
  simp only [weierstrassMod, LinearMap.mkContinuous_apply, LinearMap.comp_apply,
    LinearMap.snd_apply, divisionLinearMap, LinearMap.coe_mk, AddHom.coe_mk]

/-- The remainder has degree strictly less than the distinguished degree of the divisor. -/
@[simp]
theorem coeff_weierstrassMod (g : PowerSeries.IsRestricted.subring (R := R) c)
    (n : ℕ) (hn : s ≤ n) :
    (weierstrassMod hf g : PowerSeries R).coeff n = 0 := by
  rw [weierstrassMod_apply]
  exact (divisionPair_spec hf g).1 n hn

/-- The quotient and remainder reconstruct the dividend. -/
@[simp]
theorem weierstrassDiv_mul_add_weierstrassMod
    (g : PowerSeries.IsRestricted.subring (R := R) c) :
    weierstrassDiv hf g * f + weierstrassMod hf g = g := by
  rw [weierstrassDiv_apply, weierstrassMod_apply]
  exact (divisionPair_spec hf g).2

/-- The division operators are characterized by the decomposition and the remainder degree bound. -/
theorem weierstrassDiv_eq_and_weierstrassMod_eq
    {g q r : PowerSeries.IsRestricted.subring (R := R) c}
    (hr : ∀ n, s ≤ n → (r : PowerSeries R).coeff n = 0) (h : q * f + r = g) :
    weierstrassDiv hf g = q ∧ weierstrassMod hf g = r := by
  rw [weierstrassDiv_apply, weierstrassMod_apply, divisionPair_eq hf hr h]
  exact ⟨rfl, rfl⟩

/-- No norm cancellation occurs between a multiple of the divisor and the remainder. -/
theorem norm_eq_max_weierstrassDiv_weierstrassMod
    (g : PowerSeries.IsRestricted.subring (R := R) c) :
    ‖g‖ = max (‖weierstrassDiv hf g‖ * ‖f‖) ‖weierstrassMod hf g‖ := by
  rw [weierstrassDiv_apply, weierstrassMod_apply]
  exact norm_divisionPair hf g

/-- The quotient is bounded by the norm of the dividend divided by that of the divisor. -/
theorem norm_weierstrassDiv_le (g : PowerSeries.IsRestricted.subring (R := R) c) :
    ‖weierstrassDiv hf g‖ ≤ ‖g‖ / ‖f‖ := by
  rw [weierstrassDiv_apply, div_eq_inv_mul]
  exact norm_divisionPair_fst_le hf g

/-- The remainder operator is contractive. -/
theorem norm_weierstrassMod_le (g : PowerSeries.IsRestricted.subring (R := R) c) :
    ‖weierstrassMod hf g‖ ≤ ‖g‖ := by
  rw [weierstrassMod_apply]
  exact norm_divisionPair_snd_le hf g

/-- The remainder is the inclusion of its polynomial truncation. -/
theorem polynomialToRestricted_trunc_weierstrassMod
    (g : PowerSeries.IsRestricted.subring (R := R) c) :
    polynomialToRestricted c ((weierstrassMod hf g : PowerSeries R).trunc s) =
      weierstrassMod hf g :=
  polynomialToRestricted_trunc_eq_of_coeff_eq_zero _ (coeff_weierstrassMod hf g)

/-- Dividing a multiple of the divisor recovers its multiplier. -/
@[simp]
theorem weierstrassDiv_mul (q : PowerSeries.IsRestricted.subring (R := R) c) :
    weierstrassDiv hf (q * f) = q :=
  (weierstrassDiv_eq_and_weierstrassMod_eq hf
    (r := 0) (by simp) (by simp)).1

/-- A multiple of the divisor has zero remainder. -/
@[simp]
theorem weierstrassMod_mul (q : PowerSeries.IsRestricted.subring (R := R) c) :
    weierstrassMod hf (q * f) = 0 :=
  (weierstrassDiv_eq_and_weierstrassMod_eq hf
    (q := q) (r := 0) (by simp) (by simp)).2

/-- A polynomial of degree less than the divisor has zero quotient. -/
theorem weierstrassDiv_eq_zero_of_coeff_eq_zero
    {r : PowerSeries.IsRestricted.subring (R := R) c}
    (hr : ∀ n, s ≤ n → (r : PowerSeries R).coeff n = 0) :
    weierstrassDiv hf r = 0 :=
  (weierstrassDiv_eq_and_weierstrassMod_eq hf hr (by simp)).1

/-- The remainder operator fixes polynomials of degree less than the divisor. -/
theorem weierstrassMod_eq_self_of_coeff_eq_zero
    {r : PowerSeries.IsRestricted.subring (R := R) c}
    (hr : ∀ n, s ≤ n → (r : PowerSeries R).coeff n = 0) :
    weierstrassMod hf r = r :=
  (weierstrassDiv_eq_and_weierstrassMod_eq hf (q := 0) hr (by simp)).2

/-- Division in distinguished degree zero has zero remainder. -/
@[simp]
theorem weierstrassMod_eq_zero (hf : IsMulDistinguished c 0 (f : PowerSeries R))
    (g : PowerSeries.IsRestricted.subring (R := R) c) :
    weierstrassMod hf g = 0 := by
  apply Subtype.ext
  ext n
  simp

end TauCeti.PowerSeries
