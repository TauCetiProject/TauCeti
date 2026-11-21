/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.JHolomorphic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import TauCeti.LinearAlgebra.Determinant.Prod

/-!
# The standard complex line as a source for constant-structure `J`-holomorphic maps

This file records the elementary Cauchy--Riemann bookkeeping for maps whose source is the
standard complex line, represented as `ℝ × ℝ` with the almost complex structure
`AlmostComplexStructure.product ℝ`, `(s, t) ↦ (-t, s)`.

For a real-linear map out of this source, complex-linearity says exactly that the image of the
imaginary coordinate vector is `J` applied to the image of the real coordinate vector. Thus the
linear map, and in particular the Frechet derivative of a constant-structure `J`-holomorphic map
from the standard line, is determined by its `s`-direction.

The area estimates show that, under a taming form, the symplectic area of the ordered pair
`(∂s u, ∂t u)` is nonnegative, and it is positive when `∂s u` is nonzero.
These pointwise linear-algebra statements supply the local calculus for holomorphic-curve
energy and elliptic estimates.

Two calculus facts concern the real Cauchy--Riemann operator `P = ∂s + J ∂t + A` with any
coefficients `J, A : ℝ × ℝ → V →L[ℝ] V`: a function `β(z)` acts as
`P (β ξ) = β P ξ + (∂s β) ξ + J ((∂t β) ξ)`, in particular a cutoff `β(s)` as
`P (β ξ) = β P ξ + β' ξ`, and `P` sends `C¹` maps to continuous maps when `J` and `A` are
continuous.

## Main declarations

* `TauCeti.stdComplexLineReal` and `TauCeti.stdComplexLineImag`: the coordinate vectors
  `(1, 0)` and `(0, 1)` in the standard complex line.
* `TauCeti.equivRealProdCLM_symm_stdComplexLineReal` and
  `TauCeti.equivRealProdCLM_symm_stdComplexLineImag`: under `Complex.equivRealProdCLM` they are
  the complex numbers `1` and `i`; conversely `TauCeti.equivRealProdCLM_one` and
  `TauCeti.equivRealProdCLM_I`.
* `TauCeti.fderiv_comp_equivRealProdCLM_one` and `TauCeti.fderiv_comp_equivRealProdCLM_I`: read
  in the complex coordinate, the derivatives in the directions `1` and `i` are `∂s` and `∂t`.
* `LinearMap.apply_stdComplexLine` and `ContinuousLinearMap.apply_stdComplexLine`: a real-linear
  map is determined by its values on the coordinate vectors.
* `TauCeti.isComplexLinearMap_stdComplexLine_iff`: complex-linearity out of the standard
  complex line is equivalent to the coordinate Cauchy--Riemann equation
  `F (0, 1) = J (F (1, 0))`.
* `TauCeti.IsComplexLinearMap.apply_stdComplexLineImag`: for a complex-linear map
  `F : ℝ × ℝ →ₗ[ℝ] V`, `F (0, 1) = J (F (1, 0))`.
* `TauCeti.IsComplexLinearMap.apply_stdComplexLine`: such an `F` is determined by
  `F (1, 0)`, via `F (s, t) = s • v + t • J v`.
* `TauCeti.IsComplexLinearMap.apply_stdComplexLineImag_eq` and
  `TauCeti.IsComplexLinearMap.det_eq_sq_add_sq`: a complex-linear endomorphism of the standard
  complex line is multiplication by `a + i b`, where `(a, b) = F (1, 0)`; so `F (0, 1) = (-b, a)`
  and `det F = a² + b²`.
* `TauCeti.IsComplexLinearMap.det_nonneg`: such an endomorphism preserves orientation.
* `TauCeti.IsConstStructureJHolomorphicAt.fderiv_stdComplexLineImag` and
  `TauCeti.IsConstStructureJHolomorphicAt.fderiv_stdComplexLine_apply`: the corresponding statements
  for Frechet derivatives of constant-structure `J`-holomorphic maps.
* `TauCeti.IsComplexLinearMap.symplecticForm_apply_apply_*`: nonnegativity and positivity of
  `ω(F v, F (J v))` for a complex-linear map under tameness.
* `TauCeti.IsComplexLinearMap.symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_*`:
  nonnegativity and positivity of `ω(F ∂s, F ∂t)` under tameness.
* `TauCeti.cauchyRiemann_fun_smul`: the Leibniz rule
  `P (β ξ) = β P ξ + (∂s β) ξ + J ((∂t β) ξ)` for `P = ∂s + J ∂t + A`.
* `TauCeti.cauchyRiemann_smul_fst`: its case `P (β ξ) = β P ξ + β' ξ` for a cutoff `β(s)`.
* `TauCeti.continuous_cauchyRiemann`: `P ξ` is continuous for `C¹` maps `ξ` and continuous `J`,
  `A`.

The Cauchy--Riemann sign convention matches McDuff--Salamon, *J-holomorphic Curves and
Symplectic Topology*, Section 2.1: `du ∘ j = J ∘ du`.
-/

public section

namespace TauCeti

/-- The real coordinate vector `(1, 0)` in the standard complex line `ℝ × ℝ`. -/
@[expose]
def stdComplexLineReal : ℝ × ℝ :=
  (1, 0)

/-- The imaginary coordinate vector `(0, 1)` in the standard complex line `ℝ × ℝ`. -/
@[expose]
def stdComplexLineImag : ℝ × ℝ :=
  (0, 1)

/-- The real coordinate vector is the standard pair `(1, 0)`. -/
lemma stdComplexLineReal_eq : stdComplexLineReal = (1, 0) :=
  rfl

/-- The imaginary coordinate vector is the standard pair `(0, 1)`. -/
lemma stdComplexLineImag_eq : stdComplexLineImag = (0, 1) :=
  rfl

@[simp]
lemma stdComplexLineReal_fst : stdComplexLineReal.1 = 1 :=
  rfl

@[simp]
lemma stdComplexLineReal_snd : stdComplexLineReal.2 = 0 :=
  rfl

@[simp]
lemma stdComplexLineImag_fst : stdComplexLineImag.1 = 0 :=
  rfl

@[simp]
lemma stdComplexLineImag_snd : stdComplexLineImag.2 = 1 :=
  rfl

/-- The real coordinate vector of `ℝ × ℝ` is the complex number `1`. -/
@[simp]
lemma equivRealProdCLM_symm_stdComplexLineReal :
    Complex.equivRealProdCLM.symm stdComplexLineReal = 1 := by
  apply Complex.ext <;> simp [stdComplexLineReal_eq]

/-- The imaginary coordinate vector of `ℝ × ℝ` is the complex number `i`. -/
@[simp]
lemma equivRealProdCLM_symm_stdComplexLineImag :
    Complex.equivRealProdCLM.symm stdComplexLineImag = Complex.I := by
  apply Complex.ext <;> simp [stdComplexLineImag_eq]

/-- The complex number `1` is the real coordinate vector of `ℝ × ℝ`. -/
lemma equivRealProdCLM_one : Complex.equivRealProdCLM 1 = stdComplexLineReal := by
  rw [← equivRealProdCLM_symm_stdComplexLineReal, ContinuousLinearEquiv.apply_symm_apply]

/-- The complex number `i` is the imaginary coordinate vector of `ℝ × ℝ`. -/
lemma equivRealProdCLM_I : Complex.equivRealProdCLM Complex.I = stdComplexLineImag := by
  rw [← equivRealProdCLM_symm_stdComplexLineImag, ContinuousLinearEquiv.apply_symm_apply]

/-- In the complex coordinate `Complex.equivRealProdCLM`, the derivative of `u` in the direction
`1` is its derivative `∂s u` in the real coordinate direction. -/
lemma fderiv_comp_equivRealProdCLM_one {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ × ℝ → E) (y : ℂ) :
    fderiv ℝ (u ∘ Complex.equivRealProdCLM) y 1 =
      fderiv ℝ u (Complex.equivRealProdCLM y) stdComplexLineReal := by
  rw [ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, equivRealProdCLM_one]

/-- In the complex coordinate `Complex.equivRealProdCLM`, the derivative of `u` in the direction
`i` is its derivative `∂t u` in the imaginary coordinate direction. -/
lemma fderiv_comp_equivRealProdCLM_I {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (u : ℝ × ℝ → E) (y : ℂ) :
    fderiv ℝ (u ∘ Complex.equivRealProdCLM) y Complex.I =
      fderiv ℝ u (Complex.equivRealProdCLM y) stdComplexLineImag := by
  rw [ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, equivRealProdCLM_I]

lemma AlmostComplexStructure.product_apply_stdComplexLineReal :
    AlmostComplexStructure.product ℝ stdComplexLineReal = stdComplexLineImag :=
  by
    ext <;> simp [stdComplexLineReal, stdComplexLineImag]

lemma AlmostComplexStructure.product_apply_stdComplexLineImag :
    AlmostComplexStructure.product ℝ stdComplexLineImag = -stdComplexLineReal := by
  ext <;> simp [stdComplexLineReal, stdComplexLineImag]

/-- Every vector in `ℝ × ℝ` decomposes in the standard real and imaginary coordinate vectors. -/
lemma stdComplexLine_eq_smul_real_add_smul_imag (z : ℝ × ℝ) :
    z = z.1 • stdComplexLineReal + z.2 • stdComplexLineImag := by
  ext <;> simp [stdComplexLineReal, stdComplexLineImag]

section Linear

variable {U : Type*} [AddCommGroup U] [Module ℝ U]
variable {V : Type*} [AddCommGroup V] [Module ℝ V]
variable {J₀ : AlmostComplexStructure U}
variable {J : AlmostComplexStructure V}

/-- A real-linear map out of `ℝ × ℝ` is determined by its values on the real and imaginary
coordinate vectors. -/
lemma _root_.LinearMap.apply_stdComplexLine (F : (ℝ × ℝ) →ₗ[ℝ] V) (z : ℝ × ℝ) :
    F z = z.1 • F stdComplexLineReal + z.2 • F stdComplexLineImag := by
  simpa only [map_add, map_smul] using
    congrArg F (stdComplexLine_eq_smul_real_add_smul_imag z)

/-- A continuous real-linear map out of `ℝ × ℝ` is determined by its values on the real and
imaginary coordinate vectors. -/
lemma _root_.ContinuousLinearMap.apply_stdComplexLine [TopologicalSpace V]
    (F : (ℝ × ℝ) →L[ℝ] V) (z : ℝ × ℝ) :
    F z = z.1 • F stdComplexLineReal + z.2 • F stdComplexLineImag := by
  simpa only [map_add, map_smul] using
    congrArg F (stdComplexLine_eq_smul_real_add_smul_imag z)

/-- Complex-linearity for a real-linear map out of the standard complex line is exactly the
coordinate Cauchy--Riemann equation `F(0,1) = J(F(1,0))`. -/
lemma isComplexLinearMap_stdComplexLine_iff (F : (ℝ × ℝ) →ₗ[ℝ] V) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F ↔
      F stdComplexLineImag = J (F stdComplexLineReal) := by
  constructor
  · intro hF
    simpa only [AlmostComplexStructure.product_apply_stdComplexLineReal] using
      (isComplexLinearMap_iff_apply (AlmostComplexStructure.product ℝ) J F).mp hF
        stdComplexLineReal
  · intro hF
    rw [isComplexLinearMap_iff_apply]
    intro z
    rw [F.apply_stdComplexLine, F.apply_stdComplexLine z, hF]
    simp [map_add, map_smul, smul_neg, add_comm]

namespace IsComplexLinearMap

variable {F₀ : U →ₗ[ℝ] V}
variable {ω : SymplecticForm V}

/-- Under tameness, the pointwise symplectic area of a complex-linear image of `(v, J₀ v)` is
nonnegative. -/
lemma symplecticForm_apply_apply_nonneg (hF : IsComplexLinearMap J₀ J F₀) (hω : ω.Tames J) (v : U) :
    0 ≤ ω (F₀ v) (F₀ (J₀ v)) := by
  rw [(isComplexLinearMap_iff_apply J₀ J F₀).mp hF v]
  rcases eq_or_ne (F₀ v) 0 with hzero | hne
  · simp [hzero]
  · exact (hω (F₀ v) hne).le

/-- Under tameness, the pointwise symplectic area of a complex-linear image of `(v, J₀ v)` is
positive when the image of `v` is nonzero. -/
lemma symplecticForm_apply_apply_pos (hF : IsComplexLinearMap J₀ J F₀) (hω : ω.Tames J)
    {v : U} (hv : F₀ v ≠ 0) :
    0 < ω (F₀ v) (F₀ (J₀ v)) := by
  rw [(isComplexLinearMap_iff_apply J₀ J F₀).mp hF v]
  exact hω (F₀ v) hv

variable {F : (ℝ × ℝ) →ₗ[ℝ] V}

/-- A real-linear map out of the standard complex line is complex-linear when it satisfies the
coordinate Cauchy--Riemann equation `F(0,1) = J(F(1,0))`. -/
lemma of_apply_stdComplexLineImag (hF : F stdComplexLineImag = J (F stdComplexLineReal)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F :=
  (isComplexLinearMap_stdComplexLine_iff F).mpr hF

/-- For a complex-linear map from the standard complex line, the imaginary coordinate derivative
is `J` applied to the real coordinate derivative. -/
lemma apply_stdComplexLineImag (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    F stdComplexLineImag = J (F stdComplexLineReal) :=
  (isComplexLinearMap_stdComplexLine_iff F).mp hF

/-- The real coordinate derivative is `-J` applied to the imaginary coordinate derivative. -/
lemma apply_stdComplexLineReal (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    F stdComplexLineReal = -J (F stdComplexLineImag) := by
  rw [hF.apply_stdComplexLineImag]
  simp

/-- A complex-linear map out of the standard complex line is determined by its real-coordinate
value: `F (s, t) = s • F(1,0) + t • J(F(1,0))`. -/
lemma apply_stdComplexLine
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (z : ℝ × ℝ) :
    F z = z.1 • F stdComplexLineReal + z.2 • J (F stdComplexLineReal) := by
  rw [F.apply_stdComplexLine z, hF.apply_stdComplexLineImag]

/-- A complex-linear map from the standard complex line is zero exactly when its real-coordinate
value is zero. -/
lemma eq_zero_iff_apply_stdComplexLineReal
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) :
    F = 0 ↔ F stdComplexLineReal = 0 := by
  constructor
  · intro h
    simp [h]
  · intro hreal
    apply LinearMap.ext
    intro z
    rw [hF.apply_stdComplexLine z, hreal]
    simp

/-- The real-coordinate value of a nonzero complex-linear map from the standard complex line is
nonzero. -/
lemma apply_stdComplexLineReal_ne_zero
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hFne : F ≠ 0) :
    F stdComplexLineReal ≠ 0 := by
  exact fun hreal => hFne ((hF.eq_zero_iff_apply_stdComplexLineReal).mpr hreal)

variable {ω : SymplecticForm V}

/-- Under tameness, the pointwise symplectic area of a complex-linear image of the standard
oriented coordinate pair is nonnegative. -/
lemma symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_nonneg
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hω : ω.Tames J) :
    0 ≤ ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  simpa only [AlmostComplexStructure.product_apply_stdComplexLineReal] using
    hF.symplecticForm_apply_apply_nonneg hω stdComplexLineReal

/-- Under tameness, the pointwise symplectic area of a complex-linear image of the standard
oriented coordinate pair is positive if the real-coordinate image is nonzero. -/
lemma symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_pos
    (hF : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J F) (hω : ω.Tames J)
    (hreal : F stdComplexLineReal ≠ 0) :
    0 < ω (F stdComplexLineReal) (F stdComplexLineImag) := by
  simpa only [AlmostComplexStructure.product_apply_stdComplexLineReal] using
    hF.symplecticForm_apply_apply_pos hω hreal

end IsComplexLinearMap

end Linear

namespace IsComplexLinearMap

variable {L : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ}

/-- A complex-linear endomorphism of the standard complex line is multiplication by the complex
number `a + i b`, where `(a, b)` is the image of `(1, 0)`, so it sends `(0, 1)` to `(-b, a)`. -/
lemma apply_stdComplexLineImag_eq
    (hL : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) L) :
    L stdComplexLineImag = (-(L stdComplexLineReal).2, (L stdComplexLineReal).1) := by
  rw [hL.apply_stdComplexLineImag, AlmostComplexStructure.product_apply]

/-- A complex-linear endomorphism of the standard complex line is multiplication by the complex
number `a + i b`, where `(a, b)` is the image of `(1, 0)`, so its determinant is `a² + b²`. -/
lemma det_eq_sq_add_sq
    (hL : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) L) :
    LinearMap.det L = (L stdComplexLineReal).1 ^ 2 + (L stdComplexLineReal).2 ^ 2 := by
  rw [LinearMap.det_finTwoProd, ← stdComplexLineReal_eq, ← stdComplexLineImag_eq,
    hL.apply_stdComplexLineImag_eq]
  ring

/-- A complex-linear endomorphism of the standard complex line preserves orientation. -/
theorem det_nonneg
    (hL : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) L) :
    0 ≤ LinearMap.det L := by
  rw [hL.det_eq_sq_add_sq]
  positivity

end IsComplexLinearMap

namespace IsConstStructureJHolomorphicAt

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J' : AlmostComplexStructure W} {f : ℝ × ℝ → W} {x z : ℝ × ℝ}

/-- For a constant-structure `J`-holomorphic map from the standard complex line, the Frechet
derivative in the imaginary coordinate direction is `J` applied to the derivative in the real
coordinate direction. -/
lemma fderiv_stdComplexLineImag
    (hf : IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J' f x) :
    fderiv ℝ f x stdComplexLineImag = J' (fderiv ℝ f x stdComplexLineReal) :=
  hf.fderiv_isComplexLinear.apply_stdComplexLineImag

/-- The Frechet derivative of a constant-structure `J`-holomorphic map from the standard complex
line is determined by its real-coordinate value. -/
lemma fderiv_stdComplexLine_apply
    (hf : IsConstStructureJHolomorphicAt (AlmostComplexStructure.product ℝ) J' f x) (z : ℝ × ℝ) :
    fderiv ℝ f x z =
      z.1 • fderiv ℝ f x stdComplexLineReal +
        z.2 • J' (fderiv ℝ f x stdComplexLineReal) := by
  exact hf.fderiv_isComplexLinear.apply_stdComplexLine z

end IsConstStructureJHolomorphicAt

namespace IsConstStructureJHolomorphicWithinAt

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
variable {J' : AlmostComplexStructure W} {f : ℝ × ℝ → W} {s : Set (ℝ × ℝ)} {x : ℝ × ℝ}

/-- For a within-set constant-structure `J`-holomorphic map from the standard complex line, the
Frechet derivative within the set sends the imaginary coordinate direction to `J` applied to the
real direction, provided derivatives within the set are unique. -/
lemma fderivWithin_stdComplexLineImag
    (hf : IsConstStructureJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J' f s x)
    (hs : UniqueDiffWithinAt ℝ s x) :
    fderivWithin ℝ f s x stdComplexLineImag =
      J' (fderivWithin ℝ f s x stdComplexLineReal) :=
  (hf.fderivWithin_isComplexLinear hs).apply_stdComplexLineImag

/-- The within-set Frechet derivative of a constant-structure `J`-holomorphic map from the standard
complex line is determined by its real-coordinate value when derivatives within the set are
unique. -/
lemma fderivWithin_stdComplexLine_apply
    (hf : IsConstStructureJHolomorphicWithinAt (AlmostComplexStructure.product ℝ) J' f s x)
    (hs : UniqueDiffWithinAt ℝ s x) (z : ℝ × ℝ) :
    fderivWithin ℝ f s x z =
      z.1 • fderivWithin ℝ f s x stdComplexLineReal +
        z.2 • J' (fderivWithin ℝ f s x stdComplexLineReal) := by
  exact (hf.fderivWithin_isComplexLinear hs).apply_stdComplexLine z

end IsConstStructureJHolomorphicWithinAt

section CauchyRiemann

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **Multiplying by a function.** If `β : ℝ × ℝ → ℝ` and `ξ` are differentiable at `z`, the real
Cauchy–Riemann operator `P = ∂s + J ∂t + A` sends `β ξ` to `β P ξ + (∂s β) ξ + J ((∂t β) ξ)` at
`z`: the leading terms `∂s + J ∂t` differentiate the factor, and the zeroth-order part does not. -/
theorem cauchyRiemann_fun_smul (J A : ℝ × ℝ → V →L[ℝ] V) {ξ : ℝ × ℝ → V} {z : ℝ × ℝ}
    {β : ℝ × ℝ → ℝ} (hβ : DifferentiableAt ℝ β z) (hξ : DifferentiableAt ℝ ξ z) :
    fderiv ℝ (fun w ↦ β w • ξ w) z stdComplexLineReal +
        J z (fderiv ℝ (fun w ↦ β w • ξ w) z stdComplexLineImag) + A z (β z • ξ z) =
      β z • (fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) +
        A z (ξ z)) + fderiv ℝ β z stdComplexLineReal • ξ z +
          J z (fderiv ℝ β z stdComplexLineImag • ξ z) := by
  simp only [fderiv_fun_smul hβ hξ, add_apply, smul_apply, ContinuousLinearMap.smulRight_apply,
    map_add, map_smul]
  module

/-- **Multiplying by a cutoff in `s`.** If `β` has derivative `β'` at `s`, the real Cauchy–Riemann
operator `P = ∂s + J ∂t + A` sends `β(s) ξ` to `β(s) P ξ + β' ξ` at `z = (s, t)`: this is the case
of `cauchyRiemann_fun_smul` for a factor that only depends on `s`. -/
theorem cauchyRiemann_smul_fst (J A : ℝ × ℝ → V →L[ℝ] V) {ξ : ℝ × ℝ → V} {z : ℝ × ℝ}
    {β : ℝ → ℝ} {β' : ℝ} (hβ : HasDerivAt β β' z.1) (hξ : DifferentiableAt ℝ ξ z) :
    fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineReal +
        J z (fderiv ℝ (fun w ↦ β w.1 • ξ w) z stdComplexLineImag) + A z (β z.1 • ξ z) =
      β z.1 • (fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) +
        A z (ξ z)) + β' • ξ z := by
  have hd : HasFDerivAt (fun w : ℝ × ℝ ↦ β w.1) _ z := hβ.hasFDerivAt.comp z hasFDerivAt_fst
  rw [cauchyRiemann_fun_smul J A hd.differentiableAt hξ, hd.fderiv]
  simp [stdComplexLineReal_fst, stdComplexLineImag_fst]

/-- The real Cauchy–Riemann operator `P = ∂s + J ∂t + A` sends a `C¹` map `ξ` to a continuous map
when its coefficients `J` and `A` are continuous. -/
theorem continuous_cauchyRiemann {J A : ℝ × ℝ → V →L[ℝ] V} (hJ : Continuous J)
    (hA : Continuous A) {ξ : ℝ × ℝ → V} (hξ : ContDiff ℝ 1 ξ) :
    Continuous fun z ↦
      fderiv ℝ ξ z stdComplexLineReal + J z (fderiv ℝ ξ z stdComplexLineImag) + A z (ξ z) := by
  have hdξ (v : ℝ × ℝ) : Continuous fun z ↦ fderiv ℝ ξ z v :=
    (hξ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  exact ((hdξ _).add (hJ.clm_apply (hdξ _))).add (hA.clm_apply hξ.continuous)

end CauchyRiemann

end TauCeti
