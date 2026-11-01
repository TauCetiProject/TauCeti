/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Padics.Complex.Basic
public import TauCeti.Topology.Algebra.Valued.Integer
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.PowerSeries.Evaluation
public import Mathlib.RingTheory.MvPowerSeries.LinearTopology

/-!
# Integral root translation of power series

For a `p`-th root of unity `ζ` in the integers of `ℂ_p`, substitution at
`ζ ^ i * (1 + X) - 1` is defined on every integral power series. Its constant term
is topologically nilpotent but need not be zero, so this is topological evaluation,
not formal substitution. The resulting homomorphism is continuous for the
coefficientwise topologies and is given by a convergent sum of translated monomials.
These translations are the summands in integral root-of-unity averaging.

## References

* J. Rodrigues Jacinto and C. Williams, *An introduction to p-adic L-functions*,
  §3.5.3–5, equations (3-5), (3-6), (3-9).
-/

public section

open scoped Topology NNReal PowerSeries.WithPiTopology
open PowerSeries

namespace TauCeti.IwasawaAveraging

variable (p : ℕ) [Fact p.Prime]

/-- The coefficient inclusion from the p-adic integers into the integers of `ℂ_p`. -/
noncomputable def integralCoefficientMap : ℤ_[p] →+* Valued.integer ℂ_[p] :=
  ((algebraMap ℚ_[p] ℂ_[p]).comp PadicInt.Coe.ringHom).codRestrict _ fun x ↦ by
    rw [Valuation.mem_integer_iff, ← NNReal.coe_le_coe, PadicComplex.valuation_coe]
    simpa using x.norm_le_one

@[simp]
theorem integralCoefficientMap_coe (x : ℤ_[p]) :
    (integralCoefficientMap p x : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (x : ℚ_[p]) := (rfl)

/-- The integral coefficient inclusion is continuous for the induced p-adic topologies. -/
theorem integralCoefficientMap_continuous : Continuous (integralCoefficientMap p) :=
  (continuous_algebraMap ℚ_[p] ℂ_[p] |>.comp continuous_subtype_val).subtype_mk _

/-- Extending integral coefficients to `ℂ_p` loses no information. -/
theorem integralCoefficientMap_injective : Function.Injective (integralCoefficientMap p) := by
  intro x y h
  apply Subtype.ext
  exact (algebraMap ℚ_[p] ℂ_[p]).injective (congrArg Subtype.val h)

/-- The translated constant term of a `p`-th root of unity is topologically nilpotent. -/
theorem isTopologicallyNilpotent_sub_one (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1) :
    IsTopologicallyNilpotent (ζ - 1) := by
  have hres : IsLocalRing.residue _ (ζ - 1) = 0 := by
    apply eq_zero_of_pow_eq_zero (n := p)
    simp only [map_sub, map_one, sub_pow_char, one_pow, ← map_pow, hζ, sub_self]
  have hm := (IsLocalRing.residue_eq_zero_iff (ζ - 1)).1 hres
  have hv := (Valuation.mem_maximalIdeal_iff ℂ_[p] (PadicComplex.valued p).v).1 hm
  have hn : ‖((ζ - 1 : Valued.integer ℂ_[p]) : ℂ_[p])‖ < 1 := by
    rw [← PadicComplex.valuation_coe]
    exact_mod_cast hv
  exact tendsto_subtype_rng.mpr (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hn)

/-- The argument of a root translation is admissible for topological power-series evaluation. -/
theorem hasEval_rootTranslation (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1) (i : ℕ) :
    HasEval (C (ζ ^ i) * (1 + X) - 1 : PowerSeries (Valued.integer ℂ_[p])) := by
  have hi : (ζ ^ i) ^ p = 1 := by rw [← pow_mul, Nat.mul_comm i p, pow_mul, hζ, one_pow]
  apply MvPowerSeries.LinearTopology.isTopologicallyNilpotent_of_constantCoeff
  simpa only [← PowerSeries.constantCoeff_eq, map_sub, map_mul, constantCoeff_C,
    map_add, map_one, constantCoeff_X, add_zero, mul_one] using
    isTopologicallyNilpotent_sub_one p (ζ ^ i) hi

/-- Integral translation `F(X) ↦ F(ζ ^ i * (1 + X) - 1)`, by topological evaluation. -/
noncomputable def rootTranslation (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1) (i : ℕ) :
    PowerSeries ℤ_[p] →+* PowerSeries (Valued.integer ℂ_[p]) :=
  eval₂Hom (φ := C.comp (integralCoefficientMap p))
    (PowerSeries.WithPiTopology.continuous_C.comp (integralCoefficientMap_continuous p))
    (hasEval_rootTranslation p ζ hζ i)

/-- The root translation is topological evaluation at the translated variable. -/
theorem rootTranslation_eq_eval (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1) (i : ℕ)
    (F : PowerSeries ℤ_[p]) :
    rootTranslation p ζ hζ i F =
      eval₂ (C.comp (integralCoefficientMap p)) (C (ζ ^ i) * (1 + X) - 1) F := by
  rw [rootTranslation, coe_eval₂Hom]

/-- Integral root translation is continuous in the coefficientwise p-adic topologies. -/
theorem rootTranslation_continuous (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1) (i : ℕ) :
    Continuous (rootTranslation p ζ hζ i) := by
  simp_rw [funext (rootTranslation_eq_eval p ζ hζ i)]
  exact continuous_eval₂ (φ := C.comp (integralCoefficientMap p))
    (PowerSeries.WithPiTopology.continuous_C.comp
      (integralCoefficientMap_continuous p)) (hasEval_rootTranslation p ζ hζ i)

@[simp]
theorem rootTranslation_polynomial (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1) (i : ℕ)
    (P : Polynomial ℤ_[p]) :
    rootTranslation p ζ hζ i P =
      P.eval₂ (C.comp (integralCoefficientMap p)) (C (ζ ^ i) * (1 + X) - 1) := by
  rw [rootTranslation_eq_eval, eval₂_coe]

@[simp]
theorem rootTranslation_X (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1) (i : ℕ) :
    rootTranslation p ζ hζ i X = C (ζ ^ i) * (1 + X) - 1 := by
  rw [rootTranslation_eq_eval, eval₂_X]

@[simp]
theorem rootTranslation_C (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1) (i : ℕ) (a : ℤ_[p]) :
    rootTranslation p ζ hζ i (C a) = C (integralCoefficientMap p a) := by
  rw [rootTranslation_eq_eval, eval₂_C, RingHom.comp_apply]

@[simp]
theorem rootTranslation_one_add_X_pow (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1) (i n : ℕ) :
    rootTranslation p ζ hζ i ((1 + X) ^ n) = (C (ζ ^ i) * (1 + X)) ^ n := by
  rw [map_pow, map_add, map_one, rootTranslation_X]
  simp

/-- The translated monomial series converges to the integral root translation. -/
theorem rootTranslation_hasSum (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1) (i : ℕ)
    (F : PowerSeries ℤ_[p]) :
    HasSum (fun n ↦ C (integralCoefficientMap p (F.coeff n)) *
      (C (ζ ^ i) * (1 + X) - 1) ^ n) (rootTranslation p ζ hζ i F) := by
  rw [rootTranslation_eq_eval]
  exact hasSum_eval₂ (φ := C.comp (integralCoefficientMap p))
    (PowerSeries.WithPiTopology.continuous_C.comp
      (integralCoefficientMap_continuous p)) (hasEval_rootTranslation p ζ hζ i) F

/-- The zeroth translation is just the coefficient inclusion, on arbitrary integral series. -/
@[simp]
theorem rootTranslation_zeroth (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1)
    (F : PowerSeries ℤ_[p]) :
    rootTranslation p ζ hζ 0 F = PowerSeries.map (integralCoefficientMap p) F := by
  have hmap : Continuous (PowerSeries.map (integralCoefficientMap p)) :=
    continuous_pi fun d ↦ (integralCoefficientMap_continuous p).comp (continuous_apply d)
  have h := eval₂_unique (φ := C.comp (integralCoefficientMap p))
    (PowerSeries.WithPiTopology.continuous_C.comp (integralCoefficientMap_continuous p))
    (hasEval_rootTranslation p ζ hζ 0)
    hmap
    (ε := PowerSeries.map (integralCoefficientMap p)) ?_
  · rw [rootTranslation_eq_eval]
    exact (congrFun h F).symm
  · intro P
    simp only [pow_zero, map_one, one_mul, add_sub_cancel_left]
    rw [← Polynomial.eval₂_map, Polynomial.eval₂_C_X_eq_coe, Polynomial.polynomial_map_coe]

/-! The dyadic translation retains its nonzero constant term and its root-of-unity scalar. -/

example (ζ : Valued.integer ℂ_[p]) (hζ : ζ ^ p = 1) :
    rootTranslation p ζ hζ 0 X = X := by simp

example : rootTranslation 2 (-1) (by norm_num) 1 X =
    (-2 - X : PowerSeries (Valued.integer ℂ_[2])) := by
  simp only [rootTranslation_X, pow_one, map_neg, map_one]
  ring

example : rootTranslation 2 (-1) (by norm_num) 1 ((1 + X) ^ 3) =
    (-(1 + X) ^ 3 : PowerSeries (Valued.integer ℂ_[2])) := by
  simp only [rootTranslation_one_add_X_pow, pow_one, map_neg, map_one]
  ring

end TauCeti.IwasawaAveraging
