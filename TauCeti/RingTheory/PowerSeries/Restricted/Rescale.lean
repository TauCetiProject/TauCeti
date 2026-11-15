/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Rescale
public import TauCeti.RingTheory.PowerSeries.TateAlgebra

/-!
# Rescaling restricted univariate power series

Over any normed commutative ring `R`, if `0 ≤ s` and `‖u‖ * s ≤ r`, rescaling `f(X) ↦ f(u X)`
carries power series restricted at radius `r` to power series restricted at radius `s`
(`PowerSeries.IsRestricted.rescale_of_le`). Unlike `TauCeti.MvPowerSeries.restrictedRescaleEquiv`,
which treats isometric rescaling by multiplicative units at `‖u‖ * s = r`, the scalar `u` here
need not be a unit (in particular `u = 0` is allowed) and `‖u‖ * s` may be strictly smaller than
`r`.

Over an ultrametric normed commutative ring, this upgrades to an `R`-algebra homomorphism
`TauCeti.PowerSeries.restrictedRescaleAlgHom` between the closed-disc algebras
`IsRestricted.subring r` and `IsRestricted.subring s`. At positive radii it is contractive for the
Gauss norms without requiring `NormOneClass R`
(`TauCeti.PowerSeries.norm_restrictedRescaleAlgHom_le`), hence `1`-Lipschitz and continuous.

## Main definitions

* `TauCeti.PowerSeries.restrictedRescaleAlgHom`: rescaling `f(X) ↦ f(u X)` as an `R`-algebra
  homomorphism `IsRestricted.subring r →ₐ[R] IsRestricted.subring s` for `0 ≤ s` and
  `‖u‖ * s ≤ r`.

## Main results

* `PowerSeries.IsRestricted.rescale_of_le`: restrictedness at `r` passes to `rescale u f` at `s`
  whenever `0 ≤ s` and `‖u‖ * s ≤ r`.
* `TauCeti.PowerSeries.norm_restrictedRescaleAlgHom_le` and
  `TauCeti.PowerSeries.lipschitzWith_restrictedRescaleAlgHom`: Gauss-norm contractivity and
  `1`-Lipschitz continuity at positive radii.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, Grundlehren 261, §5.1.1.
* P. Colmez, *Fonctions d'une variable p-adique*, Astérisque 330 (2010), §I.4.
-/

public section

namespace PowerSeries

/-- **Rescaling at a bounded radius.** Over any normed commutative ring, if `f` is restricted at
`r`, `0 ≤ s`, and `‖u‖ * s ≤ r`, then `rescale u f` is restricted at `s`. -/
theorem IsRestricted.rescale_of_le {R : Type*} [NormedCommRing R] {r s : ℝ} {u : R} {f : R⟦X⟧}
    (hf : f.IsRestricted r) (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r) :
    (PowerSeries.rescale u f).IsRestricted s := by
  have hus : 0 ≤ ‖u‖ * s := mul_nonneg (norm_nonneg u) hs
  exact (TauCeti.PowerSeries.isRestricted_of_abs_le hf
    (by rw [abs_of_nonneg hus, abs_of_nonneg (hus.trans hsr)]; exact hsr)).rescale

end PowerSeries

namespace TauCeti.PowerSeries

open _root_.PowerSeries

variable {R : Type*} [NormedCommRing R] [IsUltrametricDist R] {r s : ℝ} {u : R}

/-- Rescaling `f(X) ↦ f(u X)` between closed-disc algebras when `0 ≤ s` and `‖u‖ * s ≤ r`,
bundled as an `R`-algebra homomorphism. -/
noncomputable def restrictedRescaleAlgHom (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r) :
    IsRestricted.subring (R := R) r →ₐ[R] IsRestricted.subring (R := R) s where
  toFun f := ⟨PowerSeries.rescale u (f : R⟦X⟧), IsRestricted.rescale_of_le f.2 hs hsr⟩
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

section Norm

variable [Fact (0 < r)] [Fact (0 < s)]

/-- Rescaling between positive-radius closed-disc algebras with `‖u‖ * s ≤ r` is contractive for
the Gauss norms, without requiring `NormOneClass R`. -/
theorem norm_restrictedRescaleAlgHom_le (hs : 0 ≤ s) (hsr : ‖u‖ * s ≤ r)
    (f : IsRestricted.subring (R := R) r) :
    ‖restrictedRescaleAlgHom hs hsr f‖ ≤ ‖f‖ := by
  refine norm_le_iff.mpr fun n ↦ ?_
  rw [coe_restrictedRescaleAlgHom, coeff_rescale]
  rcases eq_or_ne n 0 with rfl | hn
  · simpa using norm_coeff_mul_pow_le f 0
  · have hpow : ‖u ^ n * coeff n (f : R⟦X⟧)‖ ≤ ‖u‖ ^ n * ‖coeff n (f : R⟦X⟧)‖ :=
      (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_right (norm_pow_le' u (Nat.pos_of_ne_zero hn)) (norm_nonneg _))
    calc ‖u ^ n * coeff n (f : R⟦X⟧)‖ * s ^ n
        ≤ (‖u‖ ^ n * ‖coeff n (f : R⟦X⟧)‖) * s ^ n :=
          mul_le_mul_of_nonneg_right hpow (pow_nonneg hs n)
      _ = ‖coeff n (f : R⟦X⟧)‖ * (‖u‖ * s) ^ n := by ring
      _ ≤ ‖coeff n (f : R⟦X⟧)‖ * r ^ n :=
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) hs) hsr n) (norm_nonneg _)
      _ ≤ ‖f‖ := norm_coeff_mul_pow_le f n

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
