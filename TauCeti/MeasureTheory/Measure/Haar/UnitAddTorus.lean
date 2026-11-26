/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The volume on the unit torus

Mathlib states its results on Fourier series on the unit torus `UnitAddTorus d = (ℝ / ℤ)^d`, such
as `UnitAddTorus.orthonormal_mFourier` and the definition of `UnitAddTorus.mFourierCoeff`, for a
file-local measure: the product of the Haar probability measures `AddCircle.haarAddCircle` on the
circle factors. This file records that this product is the global `volume` on the torus, so that
those results can be read for `volume`.

## Main results

* An instance stating that the volume on the unit circle `UnitAddCircle` is a probability measure.
* `TauCeti.UnitAddTorus.volume_eq_pi_haarAddCircle`: the volume on the unit torus is the product of
  the Haar probability measures on its circle factors.
* `TauCeti.UnitAddTorus.mFourierCoeff_eq_integral_volume`: the Fourier coefficients on the unit
  torus are integrals for the volume.
* `TauCeti.UnitAddCircle.map_coe_restrict_Ioc` and `TauCeti.UnitAddTorus.map_coe_restrict_pi_Ioc`:
  an interval of length `n` covers the circle evenly, and a cube of side `n` the torus: Lebesgue
  measure on it, pushed forward, is `n`, or `nᵈ`, times the Haar probability measure.
-/

public section

open MeasureTheory Set UnitAddTorus
open scoped NNReal

namespace TauCeti

/-- The volume on the unit circle `ℝ / ℤ` is a probability measure. -/
instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  ⟨by simp [AddCircle.measure_univ]⟩

namespace UnitAddCircle

/-- **An interval of length `n` covers the circle `n` times**: Lebesgue measure on `(a, a + n]`,
pushed to the circle `ℝ / ℤ`, is `n` times the Haar probability measure. -/
theorem map_coe_restrict_Ioc (a : ℝ) (n : ℕ) :
    (volume.restrict (Ioc a (a + n))).map ((↑) : ℝ → UnitAddCircle) =
      (n : ℝ≥0) • AddCircle.haarAddCircle := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hU : Ioc a (a + ↑(n + 1)) = Ioc a (a + n) ∪ Ioc (a + n) (a + n + 1) := by
      push_cast
      rw [← add_assoc, Ioc_union_Ioc_eq_Ioc (by linarith [n.cast_nonneg (α := ℝ)]) (by linarith)]
    rw [hU, Measure.restrict_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc,
      Measure.map_add _ _ (by fun_prop), ih, (UnitAddCircle.measurePreserving_mk (a + n)).map_eq,
      AddCircle.volume_eq_smul_haarAddCircle, ENNReal.ofReal_one, one_smul]
    push_cast
    rw [add_smul, one_smul]

end UnitAddCircle

namespace UnitAddTorus

variable {d : Type*} [Fintype d]

/-- The volume on the unit torus is the product of the Haar probability measures on its circle
factors. -/
theorem volume_eq_pi_haarAddCircle :
    (volume : Measure (UnitAddTorus d)) = Measure.pi fun _ ↦ AddCircle.haarAddCircle := by
  rw [volume_pi]
  congr 1
  funext
  simp [AddCircle.volume_eq_smul_haarAddCircle]

/-- The Fourier coefficients of `f` are integrals for the volume of the torus. Mathlib defines
`mFourierCoeff` using the Haar probability measure on each circle factor; this is the volume. -/
theorem mFourierCoeff_eq_integral_volume {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : UnitAddTorus d → E) (n : d → ℤ) :
    mFourierCoeff f n = ∫ z, mFourier (-n) z • f z := by
  rw [volume_eq_pi_haarAddCircle]
  -- Mathlib defines `mFourierCoeff` with its file-local normalization
  -- `volume = haarAddCircle` on `UnitAddCircle`, whose product measure is the measure above.
  rfl

/-- **A cube of side `n` covers the torus `nᵈ` times**: Lebesgue measure on `∏ᵢ (aᵢ, aᵢ + n]`,
pushed to the torus `(ℝ / ℤ)ᵈ`, is `nᵈ` times the product of the Haar probability measures on the
circle factors. -/
theorem map_coe_restrict_pi_Ioc (a : d → ℝ) (n : ℕ) :
    ((volume : Measure (d → ℝ)).restrict (univ.pi fun i ↦ Ioc (a i) (a i + n))).map
        (fun x i ↦ (x i : UnitAddCircle)) =
      ((n : ℝ≥0) ^ Fintype.card d) • Measure.pi fun _ : d ↦ AddCircle.haarAddCircle := by
  rw [volume_pi, Measure.restrict_pi_pi, Measure.pi_map_pi (fun _ ↦ by fun_prop)]
  simp_rw [UnitAddCircle.map_coe_restrict_Ioc]
  refine Measure.pi_eq fun s _ ↦ ?_
  simp only [smul_apply, Measure.pi_pi, ENNReal.smul_def, smul_eq_mul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ENNReal.coe_pow]

end UnitAddTorus

end TauCeti
