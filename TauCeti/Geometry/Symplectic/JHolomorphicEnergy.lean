/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphicLine

/-!
# Pointwise energy density for maps from the standard complex line

This file adds the first pointwise energy-density bookkeeping for the analytic Heegaard Floer
roadmap. For a compatible pair `(ω, J)`, the associated metric is
`g(v, w) = ω(v, J w)`. If a real-linear map `F : ℝ × ℝ → V` is complex-linear, then the
standard energy density
`g(F ∂s, F ∂s) + g(F ∂t, F ∂t)` is twice the symplectic area density
`ω(F ∂s, F ∂t)`.

The statements here are still pointwise linear algebra and Frechet-derivative calculus. They are
the local identities that the later holomorphic-curve energy theory will integrate over strips
or disks.

## Main declarations

* `TauCeti.SymplecticForm.stdComplexLineEnergyDensity`: the metric energy density of a
  real-linear map from the standard complex line.
* `TauCeti.IsComplexLinearMap.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm`:
  for a complex-linear map, energy density is twice symplectic area density.
* `TauCeti.IsJHolomorphicAt.fderiv_stdComplexLineEnergyDensity_eq_two_mul_symplecticForm`:
  the corresponding Frechet-derivative statement for a pointwise `J`-holomorphic map.

The convention follows McDuff--Salamon, *J-holomorphic Curves and Symplectic Topology*,
Section 2.1: for a compatible pair, `g(·, ·) = ω(·, J ·)` and `du(∂t) = J du(∂s)`.
-/

public section

namespace TauCeti

namespace SymplecticForm

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V}
variable {ω : SymplecticForm V}

/-- The pointwise metric energy density of a real-linear map from the standard complex line.

For a compatible pair `(ω, J)`, this is
`g(F ∂s, F ∂s) + g(F ∂t, F ∂t)`, where `g(v,w) = ω(v, J w)`. -/
irreducible_def stdComplexLineEnergyDensity (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) : ℝ :=
  ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) +
    ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag)

attribute [simp] stdComplexLineEnergyDensity_def

/-- The standard pointwise energy density of any real-linear map is nonnegative under tameness. -/
lemma stdComplexLineEnergyDensity_nonneg (hω : ω.Tames J)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    0 ≤ ω.stdComplexLineEnergyDensity J F := by
  rw [stdComplexLineEnergyDensity_def]
  refine add_nonneg ?_ ?_
  · rw [associatedBilinForm_apply]
    by_cases h : F stdComplexLineReal = 0
    · simp [h]
    · exact (hω (F stdComplexLineReal) h).le
  · rw [associatedBilinForm_apply]
    by_cases h : F stdComplexLineImag = 0
    · simp [h]
    · exact (hω (F stdComplexLineImag) h).le

end SymplecticForm

namespace IsComplexLinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {F : (ℝ × ℝ) →ₗ[ℝ] V}

/-- For a complex-linear map out of the standard complex line, the associated-bilinear-form
diagonal of the imaginary-coordinate image equals that of the real-coordinate image. -/
lemma associatedBilinForm_apply_stdComplexLineImag_self_eq
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag) =
      ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) := by
  simpa [AlmostComplexStructure.product_apply_stdComplexLineReal, stdComplexLineImag] using
    hF.associatedBilinForm_apply_apply_self_eq stdComplexLineReal

/-- For a complex-linear map out of the standard complex line, the real-coordinate
associated-bilinear-form diagonal is the symplectic area density of the ordered coordinate
pair. -/
lemma associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) =
      ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  simpa [AlmostComplexStructure.product_apply_stdComplexLineReal, stdComplexLineImag] using
    hF.associatedBilinForm_apply_self_eq_symplecticForm stdComplexLineReal

/-- For a complex-linear map out of the standard complex line, the standard pointwise energy
density is twice the symplectic area density. -/
lemma stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    ω.stdComplexLineEnergyDensity J F =
      2 * ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  rw [SymplecticForm.stdComplexLineEnergyDensity_def,
    hF.associatedBilinForm_apply_stdComplexLineImag_self_eq,
    hF.associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm]
  ring

end IsComplexLinearMap

namespace IsJHolomorphicAt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {f : ℝ × ℝ → V} {x : ℝ × ℝ}

/-- For a pointwise `J`-holomorphic map from the standard complex line, the
associated-bilinear-form diagonal of the `∂t` derivative equals that of the `∂s` derivative. -/
lemma associatedBilinForm_fderiv_stdComplexLineImag_self_eq
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineImag)
        (fderiv ℝ f x stdComplexLineImag) =
      ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineReal)
        (fderiv ℝ f x stdComplexLineReal) :=
  hf.fderiv_isComplexLinear.associatedBilinForm_apply_stdComplexLineImag_self_eq

/-- For a pointwise `J`-holomorphic map from the standard complex line, the `∂s`
associated-bilinear-form diagonal is the symplectic area density `ω(∂s u, ∂t u)`. -/
lemma associatedBilinForm_fderiv_stdComplexLineReal_self_eq_symplecticForm
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineReal)
        (fderiv ℝ f x stdComplexLineReal) =
      ω (fderiv ℝ f x stdComplexLineReal) (fderiv ℝ f x stdComplexLineImag) :=
  hf.fderiv_isComplexLinear.associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm

/-- For a pointwise `J`-holomorphic map from the standard complex line, the derivative's
standard energy density is twice its symplectic area density. -/
lemma fderiv_stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap =
      2 * ω (fderiv ℝ f x stdComplexLineReal) (fderiv ℝ f x stdComplexLineImag) :=
  hf.fderiv_isComplexLinear.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm

/-- The derivative's standard pointwise energy density is nonnegative under tameness. -/
lemma fderiv_stdComplexLineEnergyDensity_nonneg (hω : ω.Tames J) :
    0 ≤ ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap :=
  ω.stdComplexLineEnergyDensity_nonneg hω (fderiv ℝ f x).toLinearMap

end IsJHolomorphicAt

namespace IsJHolomorphicWithinAt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {f : ℝ × ℝ → V} {s : Set (ℝ × ℝ)} {x : ℝ × ℝ}

/-- For a within-set `J`-holomorphic map from the standard complex line, the
associated-bilinear-form diagonal of the `∂t` derivative equals that of the `∂s` derivative,
provided derivatives within the set are unique. -/
lemma associatedBilinForm_fderivWithin_stdComplexLineImag_self_eq
    (hf : IsJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    ω.associatedBilinForm J (fderivWithin ℝ f s x stdComplexLineImag)
        (fderivWithin ℝ f s x stdComplexLineImag) =
      ω.associatedBilinForm J (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineReal) :=
  (hf.fderivWithin_isComplexLinear hs).associatedBilinForm_apply_stdComplexLineImag_self_eq

/-- For a within-set `J`-holomorphic map from the standard complex line, the `∂s`
associated-bilinear-form diagonal is the symplectic area density `ω(∂s u, ∂t u)`,
provided derivatives within the set are unique. -/
lemma associatedBilinForm_fderivWithin_stdComplexLineReal_self_eq_symplecticForm
    (hf : IsJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    ω.associatedBilinForm J (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineReal) =
      ω (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineImag) :=
  by
    have hlin := hf.fderivWithin_isComplexLinear hs
    exact hlin.associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm

/-- For a within-set `J`-holomorphic map from the standard complex line, the derivative's
standard energy density is twice its symplectic area density, provided derivatives within the
set are unique. -/
lemma fderivWithin_stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
    (hf : IsJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap =
      2 * ω (fderivWithin ℝ f s x stdComplexLineReal)
        (fderivWithin ℝ f s x stdComplexLineImag) :=
  (hf.fderivWithin_isComplexLinear hs).stdComplexLineEnergyDensity_eq_two_mul_symplecticForm

/-- The within-set derivative's standard pointwise energy density is nonnegative under tameness. -/
lemma fderivWithin_stdComplexLineEnergyDensity_nonneg (hω : ω.Tames J) :
    0 ≤ ω.stdComplexLineEnergyDensity J (fderivWithin ℝ f s x).toLinearMap :=
  ω.stdComplexLineEnergyDensity_nonneg hω (fderivWithin ℝ f s x).toLinearMap

end IsJHolomorphicWithinAt

end TauCeti
