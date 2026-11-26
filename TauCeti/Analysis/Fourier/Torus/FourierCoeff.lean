/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Fourier.AddCircleMulti
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Fourier coefficients of trigonometric series on the torus

On the unit torus `UnitAddTorus d = (ℝ / ℤ)^d` the Fourier coefficients are linear in the function.
The monomials `mFourier n` are orthonormal, so the Fourier coefficients of the monomial `mFourier n`
are the Kronecker delta at `n`, those of an absolutely convergent trigonometric series
`∑' n, mFourier n • c n` with values in a complex Banach space are its coefficients `c`, and those
of a trigonometric polynomial `∑ n ∈ s, mFourier n • c n` are `c` on `s` and zero elsewhere.
On `Lᵖ(𝕋ᵈ)`, `1 ≤ p ≤ ∞`, for the product of the Haar probability measures on the circle factors,
each Fourier coefficient is a continuous linear functional of norm at most one.

## Main declarations

* `UnitAddTorus.mFourierCoeff_add`, `UnitAddTorus.mFourierCoeff_smul` and
  `UnitAddTorus.mFourierCoeff_zero`: the coefficients are linear in the function.
* `TauCeti.UnitAddTorus.mFourierCoeff_mFourier`: the Fourier coefficients of a monomial.
* `TauCeti.UnitAddTorus.mFourierCoeff_tsum_mFourier_smul`: the Fourier coefficients of an
  absolutely convergent trigonometric series, with the scalar form
  `TauCeti.UnitAddTorus.mFourierCoeff_tsum_smul_mFourier`.
* `TauCeti.UnitAddTorus.mFourierCoeff_sum_mFourier_smul`: the Fourier coefficients of a
  trigonometric polynomial, with the scalar forms
  `TauCeti.UnitAddTorus.mFourierCoeff_sum_mFourier_mul` and
  `TauCeti.UnitAddTorus.mFourierCoeff_sum_mul_mFourier`.
* `TauCeti.UnitAddTorus.mFourierCoeff_congr_ae`: the Fourier coefficients only depend on the
  almost-everywhere class of the function.
* `TauCeti.UnitAddTorus.norm_mFourierCoeff_le_norm`: `‖f̂(n)‖ ≤ ‖f‖` in `Lᵖ(𝕋ᵈ)`, `1 ≤ p ≤ ∞`.
* `TauCeti.UnitAddTorus.mFourierCoeffCLM`: the `n`-th Fourier coefficient as a continuous linear
  functional on `Lᵖ(𝕋ᵈ)`.
-/

public section

open MeasureTheory UnitAddTorus

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace UnitAddTorus

/-- The Fourier coefficients of a sum of integrable functions are the sums of their
coefficients. -/
theorem mFourierCoeff_add {f g : UnitAddTorus d → E} (hf : Integrable f) (hg : Integrable g)
    (n : d → ℤ) : mFourierCoeff (f + g) n = mFourierCoeff f n + mFourierCoeff g n := by
  have hφ (h : UnitAddTorus d → E) (hh : Integrable h) :
      Integrable (fun z ↦ mFourier (-n) z • h z) :=
    hh.bdd_smul 1 (mFourier (-n)).continuous.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z ↦ (norm_mFourier_apply _ z).le)
  simp only [TauCeti.UnitAddTorus.mFourierCoeff_eq_integral_volume, Pi.add_apply, smul_add]
  exact integral_add (hφ f hf) (hφ g hg)

/-- Taking Fourier coefficients commutes with scalar multiplication. -/
@[simp]
theorem mFourierCoeff_smul (c : ℂ) (f : UnitAddTorus d → E) (n : d → ℤ) :
    mFourierCoeff (c • f) n = c • mFourierCoeff f n := by
  simp only [TauCeti.UnitAddTorus.mFourierCoeff_eq_integral_volume, Pi.smul_apply, smul_comm _ c,
    integral_smul]

/-- The Fourier coefficients of the zero function vanish. -/
@[simp]
theorem mFourierCoeff_zero (n : d → ℤ) : mFourierCoeff (0 : UnitAddTorus d → E) n = 0 := by
  simpa using mFourierCoeff_smul (0 : ℂ) (0 : UnitAddTorus d → E) n

end UnitAddTorus

namespace TauCeti.UnitAddTorus

variable [CompleteSpace E]

/-- The Fourier coefficients of the monomial `mFourier n` are those of the Kronecker delta at
`n`. -/
@[simp]
theorem mFourierCoeff_mFourier (n m : d → ℤ) :
    mFourierCoeff (mFourier n) m = (Pi.single n 1 : (d → ℤ) → ℂ) m := by
  have h : mFourierBasis.repr (mFourierBasis n) m = _ := mFourierBasis_repr _ m
  rw [HilbertBasis.repr_self, lp.single_apply, coe_mFourierBasis, mFourierCoeff_toLp] at h
  exact h.symm

/-- The Fourier coefficients of an absolutely convergent trigonometric series
`∑' n, mFourier n • c n` are its coefficients `c`. -/
theorem mFourierCoeff_tsum_mFourier_smul {c : (d → ℤ) → E} (hc : Summable fun n ↦ ‖c n‖)
    (m : d → ℤ) : mFourierCoeff (fun z ↦ ∑' n, mFourier n z • c n) m = c m := by
  classical
  have hint (n : d → ℤ) : Integrable fun z : UnitAddTorus d ↦ mFourier (-m) z •
      (mFourier n z • c n) :=
    (by fun_prop : Continuous fun z : UnitAddTorus d ↦ mFourier (-m) z •
      (mFourier n z • c n)).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hnorm (n : d → ℤ) : ∫ z, ‖mFourier (-m) z • (mFourier n z • c n)‖ = ‖c n‖ := by
    simp [norm_smul, norm_mFourier_apply, probReal_univ]
  have hsum (z : UnitAddTorus d) : Summable fun n ↦ mFourier n z • c n :=
    Summable.of_norm <| by simpa [norm_smul, norm_mFourier_apply] using hc
  have hcoeff (n : d → ℤ) : ∫ z, mFourier (-m) z • (mFourier n z • c n) =
      (Pi.single n 1 : (d → ℤ) → ℂ) m • c n := by
    rw [← mFourierCoeff_mFourier, mFourierCoeff_eq_integral_volume (mFourier n),
      ← integral_smul_const]
    simp_rw [smul_smul, smul_eq_mul]
  calc mFourierCoeff (fun z ↦ ∑' n, mFourier n z • c n) m
      = ∫ z, ∑' n, mFourier (-m) z • (mFourier n z • c n) := by
        rw [mFourierCoeff_eq_integral_volume]
        exact integral_congr_ae (.of_forall fun z ↦ ((hsum z).tsum_const_smul _).symm)
    _ = ∑' n, (Pi.single n 1 : (d → ℤ) → ℂ) m • c n := by
        rw [← integral_tsum_of_summable_integral_norm hint (by simpa only [hnorm] using hc)]
        simp only [hcoeff]
    _ = c m := by
        rw [tsum_eq_single m fun n hn ↦ by simp [Ne.symm hn]]
        simp

/-- The Fourier coefficients of an absolutely convergent scalar trigonometric series
`∑' n, c n • mFourier n` are its coefficients `c`. -/
theorem mFourierCoeff_tsum_smul_mFourier {c : (d → ℤ) → ℂ} (hc : Summable fun n ↦ ‖c n‖)
    (m : d → ℤ) : mFourierCoeff (fun z ↦ ∑' n, c n • mFourier n z) m = c m := by
  simp_rw [smul_eq_mul, mul_comm (c _)]
  simpa only [smul_eq_mul] using mFourierCoeff_tsum_mFourier_smul hc m

/-- The Fourier coefficients of a trigonometric polynomial `∑ n ∈ s, mFourier n • c n` are its
coefficients `c` on `s` and zero elsewhere. -/
@[simp]
theorem mFourierCoeff_sum_mFourier_smul (s : Finset (d → ℤ)) (c : (d → ℤ) → E) (m : d → ℤ) :
    mFourierCoeff (fun x ↦ ∑ n ∈ s, mFourier n x • c n) m = if m ∈ s then c m else 0 := by
  classical
  have h := mFourierCoeff_tsum_mFourier_smul (c := fun n ↦ if n ∈ s then c n else 0)
    (summable_of_ne_finset_zero (s := s) fun n hn ↦ by simp [hn]) m
  have hs (x : UnitAddTorus d) : ∑' n, (if n ∈ s then mFourier n x • c n else 0) =
      ∑ n ∈ s, mFourier n x • c n := by
    rw [tsum_eq_sum (s := s) fun n hn ↦ by simp [hn]]
    exact Finset.sum_congr rfl fun n hn ↦ by simp [hn]
  simpa only [smul_ite, smul_zero, hs] using h

/-- The Fourier coefficients of a scalar trigonometric polynomial `∑ n ∈ s, mFourier n * c n`, the
`simp` normal form of `mFourierCoeff_sum_mFourier_smul` for `E = ℂ`. -/
@[simp]
theorem mFourierCoeff_sum_mFourier_mul (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (m : d → ℤ) :
    mFourierCoeff (fun x ↦ ∑ n ∈ s, mFourier n x * c n) m = if m ∈ s then c m else 0 := by
  simpa only [smul_eq_mul] using mFourierCoeff_sum_mFourier_smul s c m

/-- The Fourier coefficients of a scalar trigonometric polynomial `∑ n ∈ s, c n * mFourier n` are
its coefficients `c` on `s` and zero elsewhere. -/
@[simp]
theorem mFourierCoeff_sum_mul_mFourier (s : Finset (d → ℤ)) (c : (d → ℤ) → ℂ) (m : d → ℤ) :
    mFourierCoeff (fun x ↦ ∑ n ∈ s, c n * mFourier n x) m = if m ∈ s then c m else 0 := by
  simp_rw [mul_comm (c _)]
  exact mFourierCoeff_sum_mFourier_mul s c m

/-! ### Fourier coefficients of `Lᵖ` functions -/

section Lp

open scoped ENNReal

-- Mathlib's monomials `mFourierLp` and Fourier basis `mFourierBasis` live on `Lᵖ` for the
-- product of the Haar probability measures on the circle factors, given by this instance; state
-- the results on that same space.
attribute [local instance 2000] instMeasureSpaceUnitAddCircle

-- The volume for this instance is a probability measure, but Mathlib only records this with a
-- file-local instance, and TauCeti's global instance concerns the volume of the global
-- `AddCircle.measureSpace`, a different instance; without this instance the Fourier coefficients
-- are not bounded by the `Lᵖ` norms, `1 ≤ p`, below.
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Every Fourier coefficient of `f ∈ Lᵖ(𝕋ᵈ)`, `1 ≤ p ≤ ∞`, is bounded by the `Lᵖ` norm of `f`: it
is bounded by the `L¹` norm, and `𝕋ᵈ` has measure one. -/
theorem norm_mFourierCoeff_le_norm {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) (n : d → ℤ) :
    ‖mFourierCoeff f n‖ ≤ ‖f‖ := by
  have h1 : ‖mFourierCoeff f n‖ ≤ (eLpNorm f 1 volume).toReal := by
    refine (norm_integral_le_lintegral_norm _).trans_eq ?_
    rw [eLpNorm_one_eq_lintegral_eNorm (Lp.aestronglyMeasurable f)]
    simp only [smul_eq_mul, norm_mul, norm_mFourier_apply, one_mul, ofReal_norm]
  refine h1.trans ?_
  rw [Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_le_eLpNorm_of_exponent_le Fact.out)

omit [CompleteSpace E] in
/-- The Fourier coefficients of a function on the torus only depend on its almost-everywhere
class for the product of the Haar probability measures on the circle factors. -/
theorem mFourierCoeff_congr_ae {f g : UnitAddTorus d → E} (h : f =ᵐ[volume] g) :
    mFourierCoeff f = mFourierCoeff g :=
  funext fun _ ↦ integral_congr_ae <| .smul (.refl _ _) h

/-- The `n`-th Fourier coefficient on `Lᵖ(𝕋ᵈ)`, `1 ≤ p ≤ ∞`, as a continuous linear functional. -/
noncomputable def mFourierCoeffCLM (p : ℝ≥0∞) [Fact (1 ≤ p)] (n : d → ℤ) :
    Lp ℂ p (volume : Measure (UnitAddTorus d)) →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun f := mFourierCoeff f n
      map_add' f g := by
        -- `mFourierCoeff_add` asks for integrability for the volume of the torus, which is the
        -- product of the Haar measures used here.
        rw [mFourierCoeff_congr_ae (Lp.coeFn_add f g), mFourierCoeff_add
          (by rw [volume_eq_pi_haarAddCircle]; exact (Lp.memLp f).integrable Fact.out)
          (by rw [volume_eq_pi_haarAddCircle]; exact (Lp.memLp g).integrable Fact.out)]
      map_smul' c f := by
        rw [mFourierCoeff_congr_ae (Lp.coeFn_smul c f), mFourierCoeff_smul, RingHom.id_apply,
          smul_eq_mul] }
    1 fun f ↦ by simpa using norm_mFourierCoeff_le_norm f n

@[simp]
theorem mFourierCoeffCLM_apply {p : ℝ≥0∞} [Fact (1 ≤ p)]
    (f : Lp ℂ p (volume : Measure (UnitAddTorus d))) (n : d → ℤ) :
    mFourierCoeffCLM p n f = mFourierCoeff f n := (rfl)

end Lp

end TauCeti.UnitAddTorus
