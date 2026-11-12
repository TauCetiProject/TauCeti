/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Mathlib.MeasureTheory.Measure.Haar.Unique
import TauCeti.Analysis.Fourier.Monomial
import TauCeti.Analysis.Fourier.Torus.Decay
import TauCeti.MeasureTheory.Function.AEEqOfIntegralContinuous
import TauCeti.MeasureTheory.Measure.Haar.UnitAddTorus

/-!
# Uniqueness of Fourier coefficients and convolution with trigonometric polynomials on the torus

On the unit torus `UnitAddTorus d = (ℝ / ℤ)^d` with its volume, the product of the Haar
probability measures of the circle factors, this file proves two facts about the Fourier
coefficients `mFourierCoeff f n = ∫ e_{-n} • f` of an integrable function `f` with values in a
complex Banach space.

*Uniqueness.* An integrable function whose Fourier coefficients all vanish is zero almost
everywhere. Integration against `f` is a continuous linear functional on `C(UnitAddTorus d, ℂ)`
of norm at most `‖f‖₁`; it vanishes on the monomials `mFourier n` by hypothesis, hence on their
uniformly dense span (`UnitAddTorus.span_mFourier_closure_eq_top`) and so on every continuous
function, which forces `f = 0` almost everywhere
(`MeasureTheory.Integrable.ae_eq_zero_of_forall_integral_smul_eq_zero`). This is the
multivariate form of `MeasureTheory.Integrable.ae_eq_zero_of_forall_fourierCoeff_eq_zero`. In
particular an integrable function whose Fourier coefficients vanish outside a finite set `s` is
almost everywhere the trigonometric polynomial `∑ n ∈ s, mFourier n • mFourierCoeff f n`.

*Convolution.* Convolving with a monomial picks out one Fourier coefficient,

`(mFourier n ⋆ f) x = ∫ mFourier n t • f (x - t) dt = mFourier n x • mFourierCoeff f n`,

because `mFourier n (x - t) = mFourier n x * mFourier (-n) t` and the volume is invariant under
`t ↦ x - t`. So convolution with a trigonometric polynomial `∑ n ∈ s, c n • mFourier n` is the
Fourier multiplier with the finitely supported symbol `c`. This is how kernels of de la Vallée
Poussin type reproduce functions whose spectrum lies where their symbol equals one.

## Main declarations

* `TauCeti.UnitAddTorus.ae_eq_zero_of_forall_mFourierCoeff_eq_zero`: uniqueness of Fourier
  coefficients for integrable functions.
* `TauCeti.UnitAddTorus.mFourierCoeff_sum_mFourier_smul`: the Fourier coefficients of a
  trigonometric polynomial.
* `TauCeti.UnitAddTorus.ae_eq_sum_mFourier_smul_mFourierCoeff`: an integrable function with
  finitely many nonzero Fourier coefficients is a trigonometric polynomial.
* `TauCeti.UnitAddTorus.convolution_mFourier_apply`: convolution with a monomial.
* `TauCeti.UnitAddTorus.convolution_sum_smul_mFourier_apply`: convolution with a trigonometric
  polynomial.
-/

public section

open MeasureTheory Set
open scoped Convolution

namespace TauCeti.UnitAddTorus

open _root_.UnitAddTorus

variable {d : Type*} [Fintype d] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {f : UnitAddTorus d → E}

/-- If all Fourier coefficients of an integrable `f` vanish, then the integral of `f` against
every continuous function on the torus vanishes. -/
private theorem integral_smul_eq_zero_of_forall_mFourierCoeff_eq_zero (hf : Integrable f)
    (h : ∀ n, mFourierCoeff f n = 0) (φ : C(UnitAddTorus d, ℂ)) : ∫ t, φ t • f t = 0 := by
  have hint (φ : C(UnitAddTorus d, ℂ)) : Integrable fun t ↦ φ t • f t :=
    hf.bdd_smul ‖φ‖ φ.continuous.aestronglyMeasurable (ae_of_all _ φ.norm_coe_le_norm)
  -- Integration against `f`, as a continuous linear functional on `C(UnitAddTorus d, ℂ)`.
  let L : C(UnitAddTorus d, ℂ) →ₗ[ℂ] E :=
    { toFun := fun φ ↦ ∫ t, φ t • f t
      map_add' := fun φ ψ ↦ by
        simp only [ContinuousMap.add_apply, add_smul]
        exact integral_add (hint φ) (hint ψ)
      map_smul' := fun c φ ↦ by
        simp only [ContinuousMap.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply]
        exact integral_smul c _ }
  let Lc := L.mkContinuous (∫ t, ‖f t‖) fun φ ↦ by
    refine (norm_integral_le_of_norm_le (hf.norm.const_mul ‖φ‖) (ae_of_all _ fun t ↦ ?_)).trans_eq
      (by rw [integral_const_mul, mul_comm])
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (φ.norm_coe_le_norm t) (norm_nonneg _)
  have hLc (φ : C(UnitAddTorus d, ℂ)) : Lc φ = ∫ t, φ t • f t := by
    simp [Lc, L]
  -- It vanishes on the Fourier monomials, hence on their dense span.
  have hspan : Submodule.span ℂ (range (mFourier (d := d))) ≤
      LinearMap.ker (Lc : _ →ₗ[ℂ] E) :=
    Submodule.span_le.2 <| range_subset_iff.2 fun n ↦ LinearMap.mem_ker.2 <| by
      simpa [hLc, mFourierCoeff_eq_integral_volume] using h (-n)
  have htop := Submodule.topologicalClosure_minimal _ hspan Lc.isClosed_ker
  rw [span_mFourier_closure_eq_top, top_le_iff] at htop
  have hφ : φ ∈ LinearMap.ker (Lc : _ →ₗ[ℂ] E) := htop ▸ Submodule.mem_top
  rw [← hLc]
  exact LinearMap.mem_ker.1 hφ

/-- **Uniqueness of Fourier coefficients on the torus.** An integrable function on the torus whose
Fourier coefficients all vanish is zero almost everywhere. -/
theorem ae_eq_zero_of_forall_mFourierCoeff_eq_zero [CompleteSpace E] (hf : Integrable f)
    (h : ∀ n, mFourierCoeff f n = 0) : f =ᵐ[volume] 0 :=
  hf.ae_eq_zero_of_forall_integral_smul_eq_zero fun φ ↦ by
    simpa [Complex.coe_smul] using integral_smul_eq_zero_of_forall_mFourierCoeff_eq_zero hf h
      ⟨fun t ↦ (φ t : ℂ), Complex.continuous_ofReal.comp φ.continuous⟩

/-- The Fourier coefficients of a trigonometric polynomial `∑ n ∈ s, mFourier n • c n` are its
coefficients `c` on `s` and zero elsewhere. -/
@[simp]
theorem mFourierCoeff_sum_mFourier_smul [CompleteSpace E] (s : Finset (d → ℤ))
    (c : (d → ℤ) → E) (m : d → ℤ) :
    mFourierCoeff (fun x ↦ ∑ n ∈ s, mFourier n x • c n) m = if m ∈ s then c m else 0 := by
  have hmono (n : d → ℤ) : Integrable fun z : UnitAddTorus d ↦ mFourier (-m) z •
      (mFourier n z • c n) :=
    (by fun_prop : Continuous fun z : UnitAddTorus d ↦ mFourier (-m) z •
      (mFourier n z • c n)).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hcoeff (n : d → ℤ) : ∫ z, mFourier (-m) z • (mFourier n z • c n) =
      (Pi.single n 1 : (d → ℤ) → ℂ) m • c n := by
    rw [← mFourierCoeff_mFourier, mFourierCoeff_eq_integral_volume (mFourier n),
      ← integral_smul_const]
    simp_rw [smul_smul, smul_eq_mul]
  rw [mFourierCoeff_eq_integral_volume]
  simp only [Finset.smul_sum]
  rw [integral_finsetSum _ fun n _ ↦ hmono n]
  simp only [hcoeff]
  split_ifs with hm
  · rw [Finset.sum_eq_single m (fun n _ hn ↦ by simp [Ne.symm hn]) (fun h ↦ absurd hm h)]
    simp
  · refine Finset.sum_eq_zero fun n hn ↦ ?_
    have hnm : m ≠ n := fun h ↦ hm (h ▸ hn)
    simp [hnm]

/-- An integrable function on the torus whose Fourier coefficients vanish outside a finite set `s`
is almost everywhere the trigonometric polynomial `∑ n ∈ s, mFourier n • mFourierCoeff f n`. -/
theorem ae_eq_sum_mFourier_smul_mFourierCoeff [CompleteSpace E] (hf : Integrable f)
    {s : Finset (d → ℤ)} (hs : ∀ n ∉ s, mFourierCoeff f n = 0) :
    f =ᵐ[volume] fun x ↦ ∑ n ∈ s, mFourier n x • mFourierCoeff f n := by
  set P : UnitAddTorus d → E := fun x ↦ ∑ n ∈ s, mFourier n x • mFourierCoeff f n
  have hPint : Integrable P :=
    integrable_finsetSum _ fun n _ ↦ (by fun_prop : Continuous fun x ↦
      mFourier n x • mFourierCoeff f n).integrable_of_hasCompactSupport (.of_compactSpace _)
  have hsmul {g : UnitAddTorus d → E} (hg : Integrable g) (m : d → ℤ) :
      Integrable fun z ↦ mFourier (-m) z • g z :=
    hg.bdd_smul 1 (mFourier (-m)).continuous.aestronglyMeasurable
      (ae_of_all _ fun z ↦ (norm_mFourier_apply (-m) z).le)
  have hzero := ae_eq_zero_of_forall_mFourierCoeff_eq_zero (hf.sub hPint) fun m ↦ by
    rw [mFourierCoeff_eq_integral_volume]
    simp only [Pi.sub_apply, smul_sub]
    rw [integral_sub (hsmul hf m) (hsmul hPint m), ← mFourierCoeff_eq_integral_volume,
      ← mFourierCoeff_eq_integral_volume, mFourierCoeff_sum_mFourier_smul]
    split_ifs with hm
    · exact sub_self _
    · rw [hs m hm, sub_zero]
  filter_upwards [hzero] with x hx
  simpa [sub_eq_zero] using hx

/-- **Convolution with a Fourier monomial** picks out one Fourier coefficient:
`(mFourier n ⋆ f) x = mFourier n x • mFourierCoeff f n`. -/
theorem convolution_mFourier_apply (n : d → ℤ) (f : UnitAddTorus d → E) (x : UnitAddTorus d) :
    (⇑(mFourier n) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f) x =
      mFourier n x • mFourierCoeff f n := by
  rw [convolution_def, mFourierCoeff_eq_integral_volume, ← integral_smul]
  rw [← integral_sub_left_eq_self _ volume x]
  congr 1 with t
  rw [ContinuousLinearMap.lsmul_apply, sub_sub_cancel, smul_smul, sub_eq_add_neg,
    mFourier_apply_add, mFourier_neg_apply]

/-- **Convolution with a trigonometric polynomial** is the Fourier multiplier with its finitely
supported coefficients: for integrable `f`,
`((∑ n ∈ s, c n • mFourier n) ⋆ f) x = ∑ n ∈ s, c n • mFourier n x • mFourierCoeff f n`. -/
theorem convolution_sum_smul_mFourier_apply (hf : Integrable f) (s : Finset (d → ℤ))
    (c : (d → ℤ) → ℂ) (x : UnitAddTorus d) :
    ((fun t ↦ ∑ n ∈ s, c n * mFourier n t) ⋆[ContinuousLinearMap.lsmul ℂ ℂ, volume] f) x =
      ∑ n ∈ s, c n • mFourier n x • mFourierCoeff f n := by
  have hint (n : d → ℤ) : Integrable fun t ↦ (c n * mFourier n t) • f (x - t) := by
    refine (hf.comp_sub_left x).bdd_smul ‖c n‖ (by fun_prop) (ae_of_all _ fun t ↦ ?_)
    simp [norm_mFourier_apply]
  simp_rw [convolution_def, ContinuousLinearMap.lsmul_apply, Finset.sum_smul]
  rw [integral_finsetSum _ fun n _ ↦ hint n]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  simp_rw [mul_smul]
  rw [integral_smul, ← convolution_mFourier_apply, convolution_def]
  simp

end TauCeti.UnitAddTorus
