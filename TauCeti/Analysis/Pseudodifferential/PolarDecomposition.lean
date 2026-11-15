/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Smooth
public import TauCeti.Analysis.Pseudodifferential.Elliptic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import TauCeti.Analysis.InnerProductSpace.OperatorIdentities
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# The polar decomposition of an elliptic homogeneous symbol

Let `a` be an elliptic homogeneous symbol of degree `m` between finite-dimensional complex inner
product spaces `V` and `W`. At every nonzero frequency its value `a (x, ξ)` is invertible, so it
has the polar decomposition `a (x, ξ) = U (x, ξ) |a (x, ξ)|` into a unitary map and a strictly
positive operator, `|T| = √(T† T)` being the modulus of `T` (`ContinuousLinearMap.modulus`) and
`U` its polar factor (`ContinuousLinearMap.polarFactor`). Both factors depend smoothly on
`(x, ξ)` away from the zero frequency, because the square root is smooth on strictly positive
operators in finite dimension, and both are positively homogeneous: `|a|` of degree `m` and `U`
of degree `0`. So they are again homogeneous symbols, `HomogeneousSymbol.modulus` and
`HomogeneousSymbol.polarFactor`, with `a = U ∘ |a|`.

Replacing the modulus by the scalar `‖ξ‖ ^ m` gives the *normalized symbol*
`HomogeneousSymbol.normalize a = ‖ξ‖ ^ m U` of the same degree, which satisfies

`n† n = ‖ξ‖ ^ (2 m)` and `n n† = ‖ξ‖ ^ (2 m)`.

For `m = 1` these are the normalizations `σ† σ = σ σ† = ‖ξ‖²` assumed of the two factors in the
external product of symbols (`TauCeti/Analysis/Pseudodifferential/ExternalProduct.lean`): every
elliptic principal symbol of order `1` is normalized this way without leaving its class. The
straight line from `a` to its normalization stays elliptic, since

`(1 - s) a + s ‖ξ‖ ^ m U = U ((1 - s) |a| + s ‖ξ‖ ^ m)`

and the second factor is a strictly positive operator for `0 ≤ s ≤ 1`
(`HomogeneousSymbol.isElliptic_lineMap_normalize`). Hence the straight line from `a` to its
normalization, which only deforms the positive factor `|a|`, consists of elliptic homogeneous
symbols of degree `m`.

## Main declarations

* `TauCeti.HomogeneousSymbol.modulus`: the modulus `|a| = √(a† a)` of an elliptic symbol, a
  homogeneous symbol of the same degree with strictly positive values at nonzero frequencies.
* `TauCeti.HomogeneousSymbol.polarFactor`: its polar factor, of degree `0`, unitary at nonzero
  frequencies and `0` at the zero frequency, with `HomogeneousSymbol.polarFactor_comp_modulus`:
  `a = U ∘ |a|`.
* `TauCeti.HomogeneousSymbol.normalize`: the normalized symbol `‖ξ‖ ^ m U`, with
  `HomogeneousSymbol.adjoint_comp_coefficient_normalize` and
  `HomogeneousSymbol.coefficient_normalize_comp_adjoint`.
* `TauCeti.HomogeneousSymbol.isElliptic_lineMap_normalize`: the straight line from `a` to its
  normalization consists of elliptic symbols.
* `TauCeti.HomogeneousSymbol.normalize_eq_self`: a symbol with `a† a = ‖ξ‖ ^ (2 m)` is its own
  normalization; `TauCeti.HomogeneousSymbol.adjoint_normalize`: normalization commutes with
  pointwise adjoints.

## References

* M. F. Atiyah, I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. 87 (1968),
  §9.
* M. Reed, B. Simon, *Methods of Modern Mathematical Physics I: Functional Analysis*, revised
  ed., Academic Press (1980), Theorem VI.10.
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [NormedSpace ℝ E] {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {m : ℝ}

/-! ### The modulus -/

section Modulus

variable [FiniteDimensional ℂ V]

/-- Away from the zero frequency, the modulus `p ↦ |a p| = √(a p† a p)` of an elliptic symbol is
smooth: there `a p† a p` is strictly positive, and the square root is smooth on strictly positive
operators in finite dimension. -/
theorem contDiffOn_modulus_coefficient (a : HomogeneousSymbol X E V W m) (ha : a.IsElliptic) :
    ContDiffOn ℝ ∞ (fun p ↦ (a.coefficient p).modulus) {p | p.2 ≠ 0} :=
  ContinuousLinearMap.contDiffOn_modulus.comp a.contDiffOn_coefficient fun p hp ↦
    (isElliptic_iff.mp ha p.1 p.2 hp).injective

/-- The modulus `|a| = √(a† a)` of an elliptic homogeneous symbol `a` of degree `m`: the
homogeneous symbol of degree `m` whose value is the modulus of the value of `a`. -/
noncomputable def modulus (a : HomogeneousSymbol X E V W m) (ha : a.IsElliptic) :
    HomogeneousSymbol X E V V m where
  coefficient p := (a.coefficient p).modulus
  zero_covector x := by simp
  contDiffOn_coefficient := a.contDiffOn_modulus_coefficient ha
  homogeneous x ξ t ht := by
    rw [a.homogeneous x ξ t ht, ← Complex.coe_smul, ContinuousLinearMap.modulus_smul,
      Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg ht.le m)]
    exact Complex.coe_smul _ _

variable (a : HomogeneousSymbol X E V W m) (ha : a.IsElliptic)

@[simp]
theorem coefficient_modulus (p : X × E) :
    (a.modulus ha).coefficient p = (a.coefficient p).modulus :=
  (rfl)

/-- At a nonzero frequency, the modulus of an elliptic symbol is strictly positive. -/
theorem isStrictlyPositive_coefficient_modulus {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    IsStrictlyPositive ((a.modulus ha).coefficient (x, ξ)) :=
  ContinuousLinearMap.isStrictlyPositive_modulus_of_isInvertible (isElliptic_iff.mp ha x ξ hξ)

/-- The modulus of an elliptic symbol is elliptic. -/
theorem isElliptic_modulus : (a.modulus ha).IsElliptic := isElliptic_iff.mpr fun _ _ hξ ↦
  ContinuousLinearMap.isInvertible_iff_isUnit.mpr
    (a.isStrictlyPositive_coefficient_modulus ha hξ).isUnit

/-- The modulus is pointwise self-adjoint. -/
@[simp]
theorem adjoint_modulus : (a.modulus ha).adjoint = a.modulus ha := by
  ext1; funext p; simp

/-- The square of the modulus is the Gram symbol: `|a| ∘ |a| = a† ∘ a`. -/
@[simp]
theorem modulus_comp_modulus : (a.modulus ha).comp (a.modulus ha) = a.adjoint.comp a := by
  ext1; funext p; simp

end Modulus

/-! ### The polar factor -/

section PolarFactor

variable [FiniteDimensional ℂ V]

/-- The polar factor `U` of an elliptic homogeneous symbol `a`: the homogeneous symbol of degree
`0` whose value is the polar factor of the value of `a`. At nonzero frequencies it is unitary and
equal to `a |a|⁻¹`; at the zero frequency it is `0`. -/
noncomputable def polarFactor (a : HomogeneousSymbol X E V W m) (ha : a.IsElliptic) :
    HomogeneousSymbol X E V W 0 where
  coefficient p := (a.coefficient p).polarFactor
  zero_covector x := by simp
  contDiffOn_coefficient :=
    ContinuousLinearMap.contDiffOn_polarFactor.comp a.contDiffOn_coefficient fun p hp ↦
      (isElliptic_iff.mp ha p.1 p.2 hp).injective
  homogeneous x ξ t ht := by
    have h : 0 < t ^ m := Real.rpow_pos_of_pos ht m
    rw [a.homogeneous x ξ t ht, ← Complex.coe_smul, ContinuousLinearMap.polarFactor_smul]
    simp [abs_of_pos h, h.ne']

variable (a : HomogeneousSymbol X E V W m) (ha : a.IsElliptic)

@[simp]
theorem coefficient_polarFactor (p : X × E) :
    (a.polarFactor ha).coefficient p = (a.coefficient p).polarFactor :=
  (rfl)

/-- **Polar decomposition** of an elliptic symbol: `a = U ∘ |a|`. -/
@[simp]
theorem polarFactor_comp_modulus :
    (a.polarFactor ha).comp (a.modulus ha) = a.castDegree (zero_add m).symm := by
  ext1; funext p; simp

/-- At a nonzero frequency, the polar factor of an elliptic symbol is an isometry: `U† U = 1`. -/
theorem adjoint_comp_coefficient_polarFactor {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    ((a.polarFactor ha).coefficient (x, ξ)).adjoint ∘L (a.polarFactor ha).coefficient (x, ξ) =
      1 :=
  ContinuousLinearMap.adjoint_polarFactor_comp_polarFactor_of_injective
    (isElliptic_iff.mp ha x ξ hξ).injective

/-- At a nonzero frequency, the polar factor of an elliptic symbol is a coisometry:
`U U† = 1`. -/
theorem coefficient_polarFactor_comp_adjoint {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (a.polarFactor ha).coefficient (x, ξ) ∘L ((a.polarFactor ha).coefficient (x, ξ)).adjoint =
      1 :=
  ContinuousLinearMap.polarFactor_comp_adjoint_polarFactor_of_denseRange
    (isElliptic_iff.mp ha x ξ hξ).surjective.denseRange

/-- The polar factor of an elliptic symbol is elliptic. -/
theorem isElliptic_polarFactor : (a.polarFactor ha).IsElliptic := isElliptic_iff.mpr fun _ _ hξ ↦
  ContinuousLinearMap.IsInvertible.of_inverse
    (a.coefficient_polarFactor_comp_adjoint ha hξ)
    (a.adjoint_comp_coefficient_polarFactor ha hξ)

end PolarFactor

end HomogeneousSymbol

/-! ### The normalized symbol -/

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [CompleteSpace V] [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W] {m : ℝ}

/-- The normalization `‖ξ‖ ^ m U` of an elliptic homogeneous symbol `a = U ∘ |a|` of degree `m`:
its modulus is replaced by the scalar `‖ξ‖ ^ m`. It is a homogeneous symbol of degree `m` with
`n† n = n n† = ‖ξ‖ ^ (2 m)` at nonzero frequencies. -/
noncomputable def normalize (a : HomogeneousSymbol X E V W m) (ha : a.IsElliptic) :
    HomogeneousSymbol X E V W m :=
  ((normRpow X E W m).comp (a.polarFactor ha)).castDegree (add_zero m)

variable (a : HomogeneousSymbol X E V W m) (ha : a.IsElliptic)

/-- At a nonzero frequency the normalized symbol is `‖ξ‖ ^ m` times the polar factor. -/
@[simp]
theorem coefficient_normalize_of_ne_zero {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (a.normalize ha).coefficient (x, ξ) = ‖ξ‖ ^ m • (a.coefficient (x, ξ)).polarFactor := by
  simp [normalize, hξ]

/-- At a nonzero frequency the normalized symbol satisfies `n† n = ‖ξ‖ ^ (2 m)`. -/
theorem adjoint_comp_coefficient_normalize {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    ((a.normalize ha).coefficient (x, ξ)).adjoint ∘L (a.normalize ha).coefficient (x, ξ) =
      (((‖ξ‖ ^ m) ^ 2 : ℝ) : ℂ) • 1 := by
  have h : (a.coefficient (x, ξ)).polarFactor.adjoint ∘L (a.coefficient (x, ξ)).polarFactor =
      ((1 : ℝ) : ℂ) • 1 := by
    simpa using a.adjoint_comp_coefficient_polarFactor ha (x := x) hξ
  rw [coefficient_normalize_of_ne_zero a ha hξ, ← Complex.coe_smul, ← mul_one ((‖ξ‖ ^ m) ^ 2)]
  exact ContinuousLinearMap.adjoint_ofReal_smul_comp_ofReal_smul h _

/-- At a nonzero frequency the normalized symbol satisfies `n n† = ‖ξ‖ ^ (2 m)`. -/
theorem coefficient_normalize_comp_adjoint {x : X} {ξ : E} (hξ : ξ ≠ 0) :
    (a.normalize ha).coefficient (x, ξ) ∘L ((a.normalize ha).coefficient (x, ξ)).adjoint =
      (((‖ξ‖ ^ m) ^ 2 : ℝ) : ℂ) • 1 := by
  have h : (a.coefficient (x, ξ)).polarFactor ∘L (a.coefficient (x, ξ)).polarFactor.adjoint =
      ((1 : ℝ) : ℂ) • 1 := by
    simpa using a.coefficient_polarFactor_comp_adjoint ha (x := x) hξ
  rw [coefficient_normalize_of_ne_zero a ha hξ, ← Complex.coe_smul, ← mul_one ((‖ξ‖ ^ m) ^ 2)]
  exact ContinuousLinearMap.ofReal_smul_comp_adjoint_ofReal_smul h _

/-- **The straight line to the normalization is elliptic.** For `0 ≤ s ≤ 1`, the symbol
`(1 - s) a + s ‖ξ‖ ^ m U = U ((1 - s) |a| + s ‖ξ‖ ^ m)` is elliptic, since the second factor is
a strictly positive operator at every nonzero frequency. -/
theorem isElliptic_lineMap_normalize {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (AffineMap.lineMap a (a.normalize ha) s).IsElliptic := by
  refine isElliptic_iff.mpr fun x ξ hξ ↦ ?_
  set U := (a.coefficient (x, ξ)).polarFactor
  set P := (a.coefficient (x, ξ)).modulus
  have hP : IsStrictlyPositive P := a.isStrictlyPositive_coefficient_modulus ha hξ
  have hc : 0 < ‖ξ‖ ^ m := Real.rpow_pos_of_pos (norm_pos_iff.mpr hξ) m
  -- The positive factor `(1 - s) |a| + s ‖ξ‖ ^ m` is strictly positive.
  have hQ : IsStrictlyPositive ((1 - s) • P + (s * ‖ξ‖ ^ m) • (1 : V →L[ℂ] V)) := by
    rcases hs.2.lt_or_eq with hs1 | rfl
    · exact IsStrictlyPositive.add_nonneg (hP.smul (sub_pos.mpr hs1))
        (smul_nonneg (mul_nonneg hs.1 hc.le) zero_le_one)
    · simpa using isStrictlyPositive_one.smul hc
  have hdecomp : (AffineMap.lineMap a (a.normalize ha) s).coefficient (x, ξ) =
      U ∘L ((1 - s) • P + (s * ‖ξ‖ ^ m) • (1 : V →L[ℂ] V)) := by
    ext v
    simp [AffineMap.lineMap_apply_module, coefficient_normalize_of_ne_zero a ha hξ, U, P, smul_smul]
  rw [hdecomp]
  exact (isElliptic_iff.mp (a.isElliptic_polarFactor ha) x ξ hξ).comp
    (ContinuousLinearMap.isInvertible_iff_isUnit.mpr hQ.isUnit)

/-- The normalization of an elliptic symbol is elliptic. -/
theorem isElliptic_normalize : (a.normalize ha).IsElliptic := by
  simpa using a.isElliptic_lineMap_normalize ha (s := 1) (by simp)

/-- An elliptic symbol that already satisfies `a† a = ‖ξ‖ ^ (2 m)` at nonzero frequencies is its
own normalization. -/
theorem normalize_eq_self (h : ∀ x ξ, ξ ≠ 0 →
    (a.coefficient (x, ξ)).adjoint ∘L a.coefficient (x, ξ) = (((‖ξ‖ ^ m) ^ 2 : ℝ) : ℂ) • 1) :
    a.normalize ha = a := by
  refine ext_of_ne_zero fun x ξ hξ ↦ ?_
  set A := a.coefficient (x, ξ)
  have hc : ((‖ξ‖ ^ m : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.rpow_pos_of_pos (norm_pos_iff.mpr hξ) m).ne'
  -- The modulus of `A` is `‖ξ‖ ^ m`, so its polar factor is `(‖ξ‖ ^ m)⁻¹ A`.
  have hmod : A.modulus = ((‖ξ‖ ^ m : ℝ) : ℂ) • 1 := by
    refine (ContinuousLinearMap.eq_modulus_iff.mpr
      ⟨ContinuousLinearMap.isPositive_one.smul_of_nonneg
        (RCLike.ofReal_nonneg.mpr (Real.rpow_nonneg (norm_nonneg ξ) m)), ?_⟩).symm
    rw [h x ξ hξ]
    ext v
    simp [sq, mul_smul]
  have hU : A.polarFactor = ((‖ξ‖ ^ m : ℝ) : ℂ)⁻¹ • A := by
    refine (ContinuousLinearMap.eq_polarFactor ?_ fun v hv ↦ ?_).symm
    · rw [hmod]
      ext v
      simp [-Complex.coe_smul, smul_smul, hc]
    · have hv0 : A v = 0 := LinearMap.mem_ker.mp hv
      rw [smul_apply, hv0, smul_zero]
  rw [coefficient_normalize_of_ne_zero a ha hξ, hU, ← Complex.coe_smul, smul_smul,
    mul_inv_cancel₀ hc, one_smul]

/-- Normalization commutes with pointwise adjoints: `(‖ξ‖ ^ m U)† = ‖ξ‖ ^ m U†` is the
normalization of `a†`, whose polar factor is `U†`. -/
theorem adjoint_normalize [FiniteDimensional ℂ W] :
    (a.normalize ha).adjoint = a.adjoint.normalize (isElliptic_adjoint_iff.mpr ha) := by
  refine ext_of_ne_zero fun x ξ hξ ↦ ?_
  simp [coefficient_normalize_of_ne_zero _ _ hξ, ← Complex.coe_smul,
    map_smulₛₗ ContinuousLinearMap.adjoint, ContinuousLinearMap.polarFactor_adjoint]

end HomogeneousSymbol

end TauCeti
