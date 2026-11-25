/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.EvalAt
public import TauCeti.RingTheory.PowerSeries.Rescale
public import TauCeti.RingTheory.PowerSeries.TateAlgebra
import TauCeti.Analysis.Normed.Ring.Basic

/-!
# Rescaling restricted univariate power series

Over an ultrametric normed commutative ring `R`, if `0 ≤ s` and `‖u‖ * s ≤ r`, rescaling
`f(X) ↦ f(u X)` (`PowerSeries.IsRestricted.rescale_of_le`) defines an `R`-algebra homomorphism
`TauCeti.PowerSeries.restrictedRescaleAlgHom` between the closed-disc algebras
`IsRestricted.subring r` and `IsRestricted.subring s`. Unlike
`TauCeti.MvPowerSeries.restrictedRescaleEquiv`, which treats isometric rescaling by multiplicative
units at `‖u‖ * s = r`, the scalar `u` here need not be a unit (in particular `u = 0` is allowed)
and `‖u‖ * s` may be strictly smaller than `r`.

At positive radii `restrictedRescaleAlgHom` is contractive for the Gauss norms without requiring
`NormOneClass R` (`TauCeti.PowerSeries.norm_restrictedRescaleAlgHom_le`), hence `1`-Lipschitz and
continuous, and preserves the Gauss norm whenever left multiplication by `u` scales norms on `R`
and `‖u‖ * s = r` (`TauCeti.PowerSeries.norm_restrictedRescaleAlgHom`).

## Main definitions

* `TauCeti.PowerSeries.restrictedRescaleAlgHom`: rescaling `f(X) ↦ f(u X)` as an `R`-algebra
  homomorphism `IsRestricted.subring r →ₐ[R] IsRestricted.subring s` for `0 ≤ s` and
  `‖u‖ * s ≤ r`.

## Main results

* `TauCeti.PowerSeries.restrictedRescaleAlgHom_X`,
  `TauCeti.PowerSeries.restrictedRescaleAlgHom_one`,
  `TauCeti.PowerSeries.restrictedRescaleAlgHom_zero_apply`,
  `TauCeti.PowerSeries.restrictedRescaleAlgHom_restrictedRescaleAlgHom`, and
  `TauCeti.PowerSeries.evalAt_restrictedRescaleAlgHom`: image of `X`, special scales, composition,
  and point evaluation.
* `TauCeti.PowerSeries.norm_restrictedRescaleAlgHom_le`,
  `TauCeti.PowerSeries.norm_restrictedRescaleAlgHom`, and
  `TauCeti.PowerSeries.lipschitzWith_restrictedRescaleAlgHom`: Gauss-norm contractivity, exact
  Gauss-norm preservation for norm-multiplicative scalars, and `1`-Lipschitz continuity at positive
  radii.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.1.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {r s t : ℝ} {u v : R}

/-- Rescaling `f(X) ↦ f(u X)` between closed-disc algebras when `0 ≤ s` and `‖u‖ * s ≤ r`,
bundled as an `R`-algebra homomorphism. -/
noncomputable def restrictedRescaleAlgHom (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r) :
    IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s where
  toFun f := ⟨PowerSeries.rescale u (f : R⟦X⟧), IsRestricted.rescale_of_le f.property hs hsr⟩
  map_one' := Subtype.ext (map_one (PowerSeries.rescale u))
  map_mul' f g := Subtype.ext (map_mul (PowerSeries.rescale u) (f : R⟦X⟧) g)
  map_zero' := Subtype.ext (map_zero (PowerSeries.rescale u))
  map_add' f g := Subtype.ext (map_add (PowerSeries.rescale u) (f : R⟦X⟧) g)
  commutes' a := Subtype.ext (by simp)

/-- `restrictedRescaleAlgHom` acts as `PowerSeries.rescale` on the underlying formal series. -/
@[simp]
theorem coe_restrictedRescaleAlgHom (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r)
    (f : IsRestricted.subring (R := R) r) :
    (restrictedRescaleAlgHom hs hsr f : R⟦X⟧) = PowerSeries.rescale u (f : R⟦X⟧) := (rfl)

/-- `restrictedRescaleAlgHom` multiplies the `n`th coefficient by `u ^ n`. -/
theorem coeff_restrictedRescaleAlgHom (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r)
    (f : IsRestricted.subring (R := R) r) (n : ℕ) :
    coeff n (restrictedRescaleAlgHom hs hsr f : R⟦X⟧) = u ^ n * coeff n (f : R⟦X⟧) := by
  rw [coe_restrictedRescaleAlgHom, coeff_rescale]

/-- `restrictedRescaleAlgHom` sends `X` to `u * X`. -/
@[simp]
theorem restrictedRescaleAlgHom_X (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r) :
    restrictedRescaleAlgHom hs hsr (polynomialToRestricted r Polynomial.X) =
      algebraMap R _ u * polynomialToRestricted s Polynomial.X :=
  Subtype.ext <| PowerSeries.ext fun n ↦ by
    simp [coe_algebraMap_isRestrictedSubring, coeff_C_mul]

/-- Rescaling by `1` at the same radius is the identity. -/
@[simp]
theorem restrictedRescaleAlgHom_one (hr : 0 ≤ r) (h1 : ‖(1 : R)‖ * r ≤ r) :
    restrictedRescaleAlgHom hr h1 = AlgHom.id R (IsRestricted.subring (R := R) r) :=
  AlgHom.ext fun _ ↦ Subtype.ext (by simp)

/-- Rescaling by `1` into a smaller closed disc agrees with `restrictedRadiusHom`. -/
theorem restrictedRescaleAlgHom_one_eq_restrictedRadiusHom (hs : 0 ≤ s) (hsr : s ≤ r)
    (h1 : ‖(1 : R)‖ * s ≤ r) (f : IsRestricted.subring (R := R) r) :
    restrictedRescaleAlgHom hs h1 f = restrictedRadiusHom hs hsr f :=
  Subtype.ext (by simp)

/-- Rescaling by `0` evaluates at the origin. -/
@[simp]
theorem restrictedRescaleAlgHom_zero_apply (hs : 0 ≤ s) (h0 : ‖(0 : R)‖ * s ≤ r)
    (f : IsRestricted.subring (R := R) r) :
    restrictedRescaleAlgHom hs h0 f = algebraMap R _ (constantCoeff (f : R⟦X⟧)) :=
  Subtype.ext (by simp [coe_algebraMap_isRestrictedSubring])

/-- Closed-disc rescaling homomorphisms compose by multiplying their scaling factors. -/
theorem restrictedRescaleAlgHom_comp_restrictedRescaleAlgHom (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r)
    (ht : 0 ≤ t) (hts : ‖v‖ * t ≤ s) (huv : ‖u * v‖ * t ≤ r) :
    (restrictedRescaleAlgHom ht hts).comp (restrictedRescaleAlgHom hs hsr) =
      restrictedRescaleAlgHom ht huv :=
  AlgHom.ext fun _ ↦ Subtype.ext (by simp [PowerSeries.rescale_rescale])

/-- Applying two closed-disc rescaling homomorphisms in turn rescales by the product of their
scales. -/
@[simp]
theorem restrictedRescaleAlgHom_restrictedRescaleAlgHom (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r)
    (ht : 0 ≤ t) (hts : ‖v‖ * t ≤ s) (f : IsRestricted.subring (R := R) r) :
    restrictedRescaleAlgHom ht hts (restrictedRescaleAlgHom hs hsr f) =
      restrictedRescaleAlgHom ht
        ((mul_le_mul_of_nonneg_right (norm_mul_le u v) ht).trans <|
          (mul_assoc ‖u‖ ‖v‖ t).le.trans <|
            (mul_le_mul_of_nonneg_left hts (norm_nonneg u)).trans hsr) f :=
  Subtype.ext (by simp [PowerSeries.rescale_rescale])

/-- Evaluating a rescaled restricted series at `b` evaluates the original series at `u • b`. -/
theorem evalAt_restrictedRescaleAlgHom {A : Type*} [Semiring A] [Algebra R A]
    [TopologicalSpace A] (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r)
    (f : IsRestricted.subring (R := R) r) (b : A) :
    (restrictedRescaleAlgHom hs hsr f : R⟦X⟧).evalAt b = (f : R⟦X⟧).evalAt (u • b) := by
  rw [coe_restrictedRescaleAlgHom, PowerSeries.evalAt_rescale]

section Norm

variable [Fact (0 < r)] [Fact (0 < s)]

/-- Rescaling between positive-radius closed-disc algebras with `‖u‖ * s ≤ r` is contractive for
the Gauss norms, without requiring `NormOneClass R`. -/
theorem norm_restrictedRescaleAlgHom_le (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r)
    (f : IsRestricted.subring (R := R) r) :
    ‖restrictedRescaleAlgHom hs hsr f‖ ≤ ‖f‖ := by
  refine norm_le_iff.mpr fun n ↦ ?_
  rw [coe_restrictedRescaleAlgHom, coeff_rescale]
  calc ‖u ^ n * coeff n (f : R⟦X⟧)‖ * s ^ n
      = ‖coeff n (f : R⟦X⟧) * u ^ n‖ * s ^ n := by rw [mul_comm (u ^ n)]
    _ ≤ (‖coeff n (f : R⟦X⟧)‖ * ‖u‖ ^ n) * s ^ n :=
        mul_le_mul_of_nonneg_right (TauCeti.norm_mul_pow_le _ _ _) (pow_nonneg hs n)
    _ = ‖coeff n (f : R⟦X⟧)‖ * (‖u‖ * s) ^ n := by ring
    _ ≤ ‖coeff n (f : R⟦X⟧)‖ * r ^ n :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hs) hsr n) (norm_nonneg _)
    _ ≤ ‖f‖ := norm_coeff_mul_pow_le f n

/-- Rescaling by a norm-multiplicative scalar `u` between positive-radius closed-disc algebras with
`‖u‖ * s = r` preserves the Gauss norm. Neither invertibility of `u` nor `NormOneClass R` is
needed. -/
theorem norm_restrictedRescaleAlgHom (hu : ∀ x : R, ‖u * x‖ = ‖u‖ * ‖x‖)
    (hs : 0 ≤ s) (hrs : ‖u‖ * s = r) (f : IsRestricted.subring (R := R) r) :
    ‖restrictedRescaleAlgHom hs hrs.le f‖ = ‖f‖ := by
  rw [norm_eq_gaussNorm, norm_eq_gaussNorm, PowerSeries.gaussNorm_eq, PowerSeries.gaussNorm_eq]
  congr 1
  funext n
  rw [coe_restrictedRescaleAlgHom]
  exact _root_.PowerSeries.norm_coeff_rescale_mul_pow (f : R⟦X⟧) hu hrs n

/-- Rescaling between positive-radius closed-disc algebras with `‖u‖ * s ≤ r` is `1`-Lipschitz for
the Gauss norms. -/
theorem lipschitzWith_restrictedRescaleAlgHom (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r) :
    LipschitzWith 1 (restrictedRescaleAlgHom (R := R) hs hsr) := by
  simpa only [Real.toNNReal_one] using
    AddMonoidHomClass.lipschitz_of_bound (restrictedRescaleAlgHom (R := R) hs hsr) 1
      (fun f ↦ by simpa only [one_mul] using norm_restrictedRescaleAlgHom_le hs hsr f)

/-- Rescaling between positive-radius closed-disc algebras with `‖u‖ * s ≤ r` is continuous for
the Gauss norms. -/
@[continuity]
theorem continuous_restrictedRescaleAlgHom (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r) :
    Continuous (restrictedRescaleAlgHom (R := R) hs hsr) :=
  (lipschitzWith_restrictedRescaleAlgHom hs hsr).continuous

end Norm

end TauCeti.PowerSeries
