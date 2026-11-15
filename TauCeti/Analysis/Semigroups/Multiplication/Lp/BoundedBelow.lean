/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Multiplication.Lp.Basic
import TauCeti.Analysis.Semigroups.Generator.ExponentialShift
import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.Shift
import TauCeti.LinearAlgebra.LinearPMap.Basic

/-!
# Multiplication semigroups with multipliers bounded below

A real multiplier `m : ι → ℝ` with lower bound `a` defines the C₀-semigroup
`S(t)x i = exp (-t * m i) * x i` on real ℓᵖ, for `1 ≤ p < ∞`.
Its growth bound is `‖S(t)‖ ≤ exp (-a * t)`, so negative values of `m` are allowed.
The generator has domain exactly `{x | Memℓp (fun i => m i * x i) p}` and acts as `-m`.
For `λ > -a`, the resolvent is multiplication by `(λ + m)⁻¹`.

The construction exponentially shifts the contraction semigroup for `m - a`.
The resulting semigroup is independent of the chosen lower bound. Neither the multiplier
nor its positive part needs to be bounded; only the lower bound and the finite exponent
are required.

## References

K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
Section I.4.c (multiplication semigroups).
-/

public section

noncomputable section

open scoped NNReal ENNReal

namespace TauCeti.Semigroups.StronglyContinuousSemigroup

variable {ι : Type*} {p : ℝ≥0∞} [Fact (1 ≤ p)]

private def shiftedMultiplier (m : ι → ℝ) (a : ℝ) (hm : ∀ i, a ≤ m i) : ι → ℝ≥0 :=
  fun i => ⟨m i - a, sub_nonneg.mpr (hm i)⟩

private theorem shiftedMultiplier_coe (m : ι → ℝ) (a : ℝ) (hm : ∀ i, a ≤ m i) (i : ι) :
    (shiftedMultiplier m a hm i : ℝ) = m i - a := (rfl)

/-- Multiplication by `exp (-t * m)` on real ℓᵖ, for a real multiplier with lower bound `a`.
The multiplier may be unbounded above and may take negative values. -/
def ofLpMultiplication (hp : p ≠ ∞) (m : ι → ℝ) (a : ℝ) (hm : ∀ i, a ≤ m i) :
    StronglyContinuousSemigroup (lp (fun _ : ι => ℝ) p) :=
  (ContractionSemigroup.ofLpMultiplication hp
    (shiftedMultiplier m a hm)).toStronglyContinuousSemigroup.expShift a

/-- Coordinate action of the multiplication semigroup with a real multiplier. -/
@[simp]
theorem ofLpMultiplication_apply_apply_apply (hp : p ≠ ∞) (m : ι → ℝ) (a : ℝ)
    (hm : ∀ i, a ≤ m i) (t : ℝ≥0) (x : lp (fun _ : ι => ℝ) p) (i : ι) :
    ofLpMultiplication hp m a hm t x i = Real.exp (-((t : ℝ) * m i)) * x i := by
  rw [ofLpMultiplication, expShift_apply_apply,
    ContractionSemigroup.toStronglyContinuousSemigroup_apply]
  have h := ContractionSemigroup.ofLpMultiplication_apply_apply_apply hp
    (shiftedMultiplier m a hm) t x i
  simp only [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  rw [h, shiftedMultiplier_coe]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- The multiplication semigroup does not depend on which lower bound is used to construct it. -/
theorem ofLpMultiplication_eq (hp : p ≠ ∞) (m : ι → ℝ) (a b : ℝ)
    (ha : ∀ i, a ≤ m i) (hb : ∀ i, b ≤ m i) :
    ofLpMultiplication hp m a ha = ofLpMultiplication hp m b hb := by
  ext t x i
  simp

/-- A lower bound `a` on the multiplier gives growth exponent `-a` and growth constant one. -/
theorem ofLpMultiplication_hasGrowthBound (hp : p ≠ ∞) (m : ι → ℝ) (a : ℝ)
    (hm : ∀ i, a ≤ m i) : (ofLpMultiplication hp m a hm).HasGrowthBound (-a) 1 := by
  rw [ofLpMultiplication]
  simpa only [zero_sub] using
    (ContractionSemigroup.ofLpMultiplication hp
      (shiftedMultiplier m a hm)).hasGrowthBound.expShift (lambda := a)

/-- The generator acts coordinatewise as multiplication by `-m`. -/
@[simp]
theorem ofLpMultiplication_generator_apply_apply (hp : p ≠ ∞) (m : ι → ℝ) (a : ℝ)
    (hm : ∀ i, a ≤ m i) (x : (ofLpMultiplication hp m a hm).generator.domain) (i : ι) :
    (ofLpMultiplication hp m a hm).generator x i =
      -m i * (x : lp (fun _ : ι => ℝ) p) i := by
  have hgen : (ofLpMultiplication hp m a hm).generator =
      LinearPMap.subScalar (ContractionSemigroup.ofLpMultiplication hp
        (shiftedMultiplier m a hm)).toStronglyContinuousSemigroup.generator a := by
    rw [ofLpMultiplication, generator_expShift]
  rw [LinearPMap.congr_fun hgen x.property (hgen ▸ x.property), LinearPMap.subScalar_apply]
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    ContractionSemigroup.ofLpMultiplication_generator_apply_apply, shiftedMultiplier_coe]
  ring

/-- The generator domain is exactly the vectors whose product with `m` belongs to ℓᵖ.
In particular it is independent of the lower bound used in the construction. -/
@[simp]
theorem ofLpMultiplication_mem_domain_iff (hp : p ≠ ∞) (m : ι → ℝ) (a : ℝ)
    (hm : ∀ i, a ≤ m i) (x : lp (fun _ : ι => ℝ) p) :
    x ∈ (ofLpMultiplication hp m a hm).domain ↔ Memℓp (fun i => m i * x i) p := by
  rw [← generator_domain, ofLpMultiplication, generator_expShift,
    LinearPMap.subScalar_domain, generator_domain,
    ContractionSemigroup.ofLpMultiplication_mem_domain_iff]
  have hx := (lp.memℓp x).const_smul a
  constructor
  · intro h
    convert h.add hx using 1
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, shiftedMultiplier_coe]
    ring
  · intro h
    convert h.sub hx using 1
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, shiftedMultiplier_coe]
    ring

/-- For `λ > -a`, the resolvent of the generator multiplies each coordinate by `(λ + m i)⁻¹`. -/
@[simp]
theorem ofLpMultiplication_generator_resolvent_apply_apply (hp : p ≠ ∞) (m : ι → ℝ)
    (a : ℝ) (hm : ∀ i, a ≤ m i) {c : ℝ} (hc : -a < c)
    (x : lp (fun _ : ι => ℝ) p) (i : ι) :
    LinearPMap.resolvent (ofLpMultiplication hp m a hm).generator c x i =
      (c + m i)⁻¹ * x i := by
  let S := ContractionSemigroup.ofLpMultiplication hp
    (shiftedMultiplier m a hm)
  have hca : 0 < c + a := by linarith
  have hρ := S.toStronglyContinuousSemigroup.mem_resolventSet_generator S.hasGrowthBound hca
  rw [ofLpMultiplication, generator_expShift, LinearPMap.resolvent_subScalar hρ,
    generator_resolvent_eq _ S.hasGrowthBound hca,
    ← ContractionSemigroup.resolvent_eq_stronglyContinuousSemigroup_resolvent]
  rw [ContractionSemigroup.ofLpMultiplication_resolvent_apply_apply,
    shiftedMultiplier_coe]
  congr 2
  ring

/-- The pointwise Laplace resolvent has the same explicit formula above the growth exponent. -/
@[simp]
theorem ofLpMultiplication_resolvent_apply_apply (hp : p ≠ ∞) (m : ι → ℝ) (a : ℝ)
    (hm : ∀ i, a ≤ m i) {c : ℝ} (hc : -a < c) (x : lp (fun _ : ι => ℝ) p) (i : ι) :
    (ofLpMultiplication hp m a hm).resolvent (ofLpMultiplication_hasGrowthBound hp m a hm)
      c hc x i = (c + m i)⁻¹ * x i := by
  rw [← generator_resolvent_eq]
  exact ofLpMultiplication_generator_resolvent_apply_apply hp m a hm hc x i

end TauCeti.Semigroups.StronglyContinuousSemigroup
