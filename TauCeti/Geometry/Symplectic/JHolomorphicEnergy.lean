/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Symplectic.CompatibleMetric
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

/-- The pointwise metric energy density of a real-linear map from the standard complex line.

For a compatible pair `(ω, J)`, this is
`g(F ∂s, F ∂s) + g(F ∂t, F ∂t)`, where `g(v,w) = ω(v, J w)`. -/
@[expose]
def stdComplexLineEnergyDensity (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) : ℝ :=
  ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) +
    ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag)

/-- The defining formula for the standard-line energy density. -/
lemma stdComplexLineEnergyDensity_def (ω : SymplecticForm V) (J : AlmostComplexStructure V)
    (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    ω.stdComplexLineEnergyDensity J F =
      ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) +
        ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag) :=
  rfl

end SymplecticForm

namespace IsComplexLinearMap

variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {F : (ℝ × ℝ) →ₗ[ℝ] V}

/-- For a complex-linear map out of the standard complex line, the metric norm-square of the
imaginary-coordinate image equals that of the real-coordinate image. -/
lemma associatedBilinForm_apply_stdComplexLineImag_self_eq
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F)
    (hω : ω.Compatible J) :
    ω.associatedBilinForm J (F stdComplexLineImag) (F stdComplexLineImag) =
      ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) := by
  rw [hF.apply_stdComplexLineImag]
  exact hω.associatedBilinForm_invariant (F stdComplexLineReal) (F stdComplexLineReal)

/-- For a complex-linear map out of the standard complex line, the real-coordinate metric
norm-square is the symplectic area density of the ordered coordinate pair. -/
lemma associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    ω.associatedBilinForm J (F stdComplexLineReal) (F stdComplexLineReal) =
      ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  rw [SymplecticForm.associatedBilinForm_apply, hF.apply_stdComplexLineImag]

/-- For a complex-linear map out of the standard complex line, the standard pointwise energy
density is twice the symplectic area density. -/
lemma stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F)
    (hω : ω.Compatible J) :
    ω.stdComplexLineEnergyDensity J F =
      2 * ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  rw [SymplecticForm.stdComplexLineEnergyDensity_def,
    hF.associatedBilinForm_apply_stdComplexLineImag_self_eq hω,
    hF.associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm]
  ring

/-- The standard pointwise energy density of a complex-linear map is nonnegative under a
compatible pair. -/
lemma stdComplexLineEnergyDensity_nonneg
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F)
    (hω : ω.Compatible J) :
    0 ≤ ω.stdComplexLineEnergyDensity J F := by
  rw [hF.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm hω]
  exact mul_nonneg zero_le_two
    (hF.symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_nonneg hω.tames)

end IsComplexLinearMap

namespace IsJHolomorphicAt

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable {J : AlmostComplexStructure V} {ω : SymplecticForm V}
variable {f : ℝ × ℝ → V} {x : ℝ × ℝ}

/-- For a pointwise `J`-holomorphic map from the standard complex line, the metric norm-square
of the `∂t` derivative equals that of the `∂s` derivative. -/
lemma associatedBilinForm_fderiv_stdComplexLineImag_self_eq
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x)
    (hω : ω.Compatible J) :
    ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineImag)
        (fderiv ℝ f x stdComplexLineImag) =
      ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineReal)
        (fderiv ℝ f x stdComplexLineReal) :=
  hf.fderiv_isComplexLinear.associatedBilinForm_apply_stdComplexLineImag_self_eq hω

/-- For a pointwise `J`-holomorphic map from the standard complex line, the `∂s` metric
norm-square is the symplectic area density `ω(∂s u, ∂t u)`. -/
lemma associatedBilinForm_fderiv_stdComplexLineReal_self_eq_symplecticForm
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x) :
    ω.associatedBilinForm J (fderiv ℝ f x stdComplexLineReal)
        (fderiv ℝ f x stdComplexLineReal) =
      ω (fderiv ℝ f x stdComplexLineReal) (fderiv ℝ f x stdComplexLineImag) :=
  hf.fderiv_isComplexLinear.associatedBilinForm_apply_stdComplexLineReal_self_eq_symplecticForm

/-- For a pointwise `J`-holomorphic map from the standard complex line, the derivative's
standard energy density is twice its symplectic area density. -/
lemma fderiv_stdComplexLineEnergyDensity_eq_two_mul_symplecticForm
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x)
    (hω : ω.Compatible J) :
    ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap =
      2 * ω (fderiv ℝ f x stdComplexLineReal) (fderiv ℝ f x stdComplexLineImag) :=
  hf.fderiv_isComplexLinear.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm hω

/-- The derivative's standard pointwise energy density is nonnegative for a pointwise
`J`-holomorphic map under a compatible pair. -/
lemma fderiv_stdComplexLineEnergyDensity_nonneg
    (hf : IsJHolomorphicAt (AlmostComplexStructure.product ℝ) J f x)
    (hω : ω.Compatible J) :
    0 ≤ ω.stdComplexLineEnergyDensity J (fderiv ℝ f x).toLinearMap :=
  hf.fderiv_isComplexLinear.stdComplexLineEnergyDensity_nonneg hω

end IsJHolomorphicAt

end TauCeti
