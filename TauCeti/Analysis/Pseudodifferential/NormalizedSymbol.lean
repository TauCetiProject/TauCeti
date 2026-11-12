/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Polar.Smooth
public import TauCeti.Analysis.Pseudodifferential.Elliptic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# The normalized principal symbol

Let `a(x, ξ) : V → W` be a homogeneous symbol of degree `m` between complex inner product spaces,
with `V` finite-dimensional, whose values at nonzero frequencies are injective. Its
**normalization** is the homogeneous symbol of degree `1`

`a♯(x, ξ) = ‖ξ‖ U(x, ξ) = ‖ξ‖ a(x, ξ) (a(x, ξ)† a(x, ξ))^(-1/2)`

(`TauCeti.HomogeneousSymbol.normalize`), where `U(x, ξ)` is the polar factor of `a(x, ξ)`
(`ContinuousLinearMap.polarFactor`). It is smooth away from `ξ = 0` because the polar factor depends
smoothly on an injective operator (`ContinuousLinearMap.contDiffOn_polarFactor`), and homogeneous of
degree `1` because rescaling `a(x, ξ)` by `t ^ m > 0` does not change its polar factor.

The normalization satisfies `a♯† a♯ = ‖ξ‖²` (`adjoint_comp_coefficient_normalize`), and for an
elliptic symbol also `a♯ a♯† = ‖ξ‖²` (`coefficient_normalize_comp_adjoint`). These are the two
normalization identities that the external product of principal symbols assumes of its factors
(`TauCeti.HomogeneousSymbol.adjoint_comp_coefficient_externalProduct`). A symbol of degree `1`
that already satisfies `a† a = ‖ξ‖²` is its own normalization (`normalize_eq_self`), and the
normalization commutes with pointwise adjoints (`adjoint_normalize`).

For an elliptic symbol of degree `1`, the straight line from `a` to `a♯` stays elliptic
(`isElliptic_lineMap_normalize`): writing `a = U |a|` with `|a| = (a† a)^(1/2)`,

`(1 - t) a + t a♯ = U ((1 - t) |a| + t ‖ξ‖)`,

and for `0 ≤ t ≤ 1` the right factor is a strictly positive operator at every nonzero frequency.
This is the homotopy of elliptic principal symbols, through right multiplication by positive
symbols, that joins an elliptic symbol of order `1` to its normalization, as in the reduction of
the index of a product of elliptic operators to that of normalized factors.

## References

* M. F. Atiyah and I. M. Singer, *The index of elliptic operators: I*, Ann. of Math. **87**
  (1968), §9: the product of two elliptic operators, whose symbol is built from the factor
  symbols.
-/

public section

noncomputable section

open scoped ContDiff InnerProduct

namespace TauCeti

namespace HomogeneousSymbol

variable {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [CompleteSpace V] [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [CompleteSpace W] {m : ℝ}

/-- The **normalization** `‖ξ‖ U(x, ξ)` of a homogeneous symbol `a` whose values at nonzero
frequencies are injective, where `U(x, ξ)` is the polar factor of `a(x, ξ)`. It is a homogeneous
symbol of degree `1`; at a nonzero frequency `U = a (a† a)^(-1/2)`. -/
def normalize (a : HomogeneousSymbol X E V W m)
    (ha : ∀ x ξ, ξ ≠ 0 → Function.Injective (a.coefficient (x, ξ))) :
    HomogeneousSymbol X E V W 1 where
  coefficient p := ‖p.2‖ • (a.coefficient p).polarFactor
  zero_covector x := by simp
  contDiffOn_coefficient := by
    have hnorm : ContDiffOn ℝ ∞ (fun p : X × E ↦ ‖p.2‖) {p | p.2 ≠ 0} := fun p hp ↦
      ((contDiffAt_norm ℝ hp).comp p contDiffAt_snd).contDiffWithinAt
    exact hnorm.smul (ContinuousLinearMap.contDiffOn_polarFactor.comp a.contDiffOn_coefficient
      fun p hp ↦ ha p.1 p.2 hp)
  homogeneous x ξ t ht := by
    have hpos : 0 < t ^ m := Real.rpow_pos_of_pos ht m
    have h : (a.coefficient (x, t • ξ)).polarFactor = (a.coefficient (x, ξ)).polarFactor := by
      rw [a.homogeneous x ξ t ht, ← Complex.coe_smul (t ^ m), ContinuousLinearMap.polarFactor_smul]
      simp [Real.norm_of_nonneg hpos.le, hpos.ne']
    simp only [h, norm_smul, Real.norm_of_nonneg ht.le, Real.rpow_one, mul_smul]

variable (a : HomogeneousSymbol X E V W m)
  (ha : ∀ x ξ, ξ ≠ 0 → Function.Injective (a.coefficient (x, ξ)))

@[simp]
theorem coefficient_normalize (p : X × E) :
    (a.normalize ha).coefficient p = ‖p.2‖ • (a.coefficient p).polarFactor :=
  (rfl)

/-- **First normalization identity.** `a♯† a♯ = ‖ξ‖²`. -/
theorem adjoint_comp_coefficient_normalize (x : X) (ξ : E) :
    ((a.normalize ha).coefficient (x, ξ))† ∘L (a.normalize ha).coefficient (x, ξ) =
      ((‖ξ‖ ^ 2 : ℝ) : ℂ) • 1 := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  rw [coefficient_normalize, ← Complex.coe_smul, map_smulₛₗ, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.adjoint_polarFactor_comp_polarFactor_of_injective _ (ha x ξ hξ), smul_smul,
    Complex.conj_ofReal, ← Complex.ofReal_mul, ← sq]

/-- **Second normalization identity.** For an elliptic symbol, `a♯ a♯† = ‖ξ‖²`. -/
theorem coefficient_normalize_comp_adjoint (hell : a.IsElliptic) (x : X) (ξ : E) :
    (a.normalize ha).coefficient (x, ξ) ∘L ((a.normalize ha).coefficient (x, ξ))† =
      ((‖ξ‖ ^ 2 : ℝ) : ℂ) • 1 := by
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp
  rw [coefficient_normalize, ← Complex.coe_smul, map_smulₛₗ, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.polarFactor_comp_adjoint_polarFactor_of_denseRange _
      (isElliptic_iff_bijective.1 hell x ξ hξ).surjective.denseRange,
    smul_smul, Complex.conj_ofReal, ← Complex.ofReal_mul, ← sq]

/-- The normalization of an elliptic symbol is elliptic. -/
theorem isElliptic_normalize (hell : a.IsElliptic) : (a.normalize ha).IsElliptic := by
  refine isElliptic_iff.2 fun x ξ hξ ↦ ?_
  have hn : ((‖ξ‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos (norm_pos_iff.2 hξ) 2).ne'
  refine .of_inverse (g := ((‖ξ‖ ^ 2 : ℝ) : ℂ)⁻¹ • ((a.normalize ha).coefficient (x, ξ))†) ?_ ?_
  · rw [ContinuousLinearMap.comp_smul, coefficient_normalize_comp_adjoint a ha hell, smul_smul,
      inv_mul_cancel₀ hn, one_smul, ContinuousLinearMap.one_def]
  · rw [ContinuousLinearMap.smul_comp, adjoint_comp_coefficient_normalize, smul_smul,
      inv_mul_cancel₀ hn, one_smul, ContinuousLinearMap.one_def]

/-- A symbol of degree `1` that already satisfies `a† a = ‖ξ‖²` is its own normalization. -/
theorem normalize_eq_self (a : HomogeneousSymbol X E V W 1)
    (ha : ∀ x ξ, ξ ≠ 0 → Function.Injective (a.coefficient (x, ξ)))
    (h : ∀ x ξ, (a.coefficient (x, ξ))† ∘L a.coefficient (x, ξ) = ((‖ξ‖ ^ 2 : ℝ) : ℂ) • 1) :
    a.normalize ha = a := by
  refine ext_of_ne_zero fun x ξ hξ ↦ ?_
  set A := a.coefficient (x, ξ)
  have hξ' : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 hξ).ne'
  -- The modulus of `A` is `‖ξ‖`, so its polar factor is `‖ξ‖⁻¹ A`.
  have hmod : A.modulus = ((‖ξ‖ : ℝ) : ℂ) • 1 := by
    refine (ContinuousLinearMap.eq_modulus_iff.2 ⟨ContinuousLinearMap.isPositive_one.smul_of_nonneg
      (RCLike.ofReal_nonneg.2 (norm_nonneg ξ)), ?_⟩).symm
    rw [h]
    ext v
    simp [sq, mul_smul]
  have hU : A.polarFactor = ((‖ξ‖ : ℝ) : ℂ)⁻¹ • A := by
    refine (ContinuousLinearMap.eq_polarFactor ?_ fun v hv ↦ ?_).symm
    · rw [hmod]
      ext v
      simp [-Complex.coe_smul, smul_smul, hξ']
    · rw [smul_apply, show A v = 0 from LinearMap.mem_ker.1 hv, smul_zero]
  rw [coefficient_normalize, hU, ← Complex.coe_smul, smul_smul, mul_inv_cancel₀ hξ', one_smul]

/-- Normalization commutes with pointwise adjoints: `(a♯)† = (a†)♯`. -/
theorem adjoint_normalize [FiniteDimensional ℂ W]
    (ha' : ∀ x ξ, ξ ≠ 0 → Function.Injective (a.adjoint.coefficient (x, ξ))) :
    (a.normalize ha).adjoint = a.adjoint.normalize ha' := by
  ext1
  funext p
  rw [coefficient_adjoint, coefficient_normalize, coefficient_normalize, coefficient_adjoint,
    ContinuousLinearMap.polarFactor_adjoint, ← Complex.coe_smul, ← Complex.coe_smul,
    map_smulₛₗ, Complex.conj_ofReal]

/-- **Homotopy to the normalization.** For an elliptic symbol of degree `1`, every symbol
`(1 - t) a + t a♯` with `0 ≤ t ≤ 1` on the straight line from `a` to its normalization is elliptic.
At a nonzero frequency it is `U ((1 - t) |a| + t ‖ξ‖)`, with `U` the polar factor of `a` and the
right factor strictly positive. -/
theorem isElliptic_lineMap_normalize (a : HomogeneousSymbol X E V W 1) (hell : a.IsElliptic)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (AffineMap.lineMap a (a.normalize hell.injective) t).IsElliptic := by
  refine isElliptic_iff.2 fun x ξ hξ ↦ ?_
  set A := a.coefficient (x, ξ)
  have hinj : Function.Injective A := hell.injective x ξ hξ
  -- The polar factor `U` is unitary, hence invertible.
  have hU : A.polarFactor.IsInvertible :=
    .of_inverse (ContinuousLinearMap.polarFactor_comp_adjoint_polarFactor_of_denseRange A
      (isElliptic_iff_bijective.1 hell x ξ hξ).surjective.denseRange)
      (ContinuousLinearMap.adjoint_polarFactor_comp_polarFactor_of_injective A hinj)
  -- The right factor `P = (1 - t) |A| + t ‖ξ‖` is strictly positive.
  set P : V →L[ℂ] V := (1 - t) • A.modulus + (t * ‖ξ‖) • 1
  have hmod : IsStrictlyPositive A.modulus := IsStrictlyPositive.iff_of_unital.2
    ⟨A.modulus_nonneg, ContinuousLinearMap.isUnit_modulus_iff_injective.2 hinj⟩
  have hP : IsStrictlyPositive P := by
    rcases ht.2.lt_or_eq with ht1 | rfl
    · exact IsStrictlyPositive.add_nonneg (IsStrictlyPositive.smul (sub_pos.2 ht1) hmod)
        (smul_nonneg (mul_nonneg ht.1 (norm_nonneg ξ)) zero_le_one)
    · simpa [P] using isStrictlyPositive_one.smul (norm_pos_iff.2 hξ)
  obtain ⟨u, hu⟩ := hP.isUnit
  have hPinv : P.IsInvertible := ⟨ContinuousLinearEquiv.unitsEquiv ℂ V u, by
    ext v
    rw [← hu]
    exact ContinuousLinearEquiv.unitsEquiv_apply ℂ V u v⟩
  -- Factor the symbol on the line as `U P`.
  have hfac : (AffineMap.lineMap a (a.normalize hell.injective) t).coefficient (x, ξ) =
      A.polarFactor ∘L P := by
    rw [AffineMap.lineMap_apply_module, coefficient_add, coefficient_smul, coefficient_smul]
    simp only [Pi.add_apply, Pi.smul_apply, coefficient_normalize, P,
      ContinuousLinearMap.comp_add, ContinuousLinearMap.comp_smul,
      ContinuousLinearMap.polarFactor_comp_modulus, smul_smul, ContinuousLinearMap.one_def,
      ContinuousLinearMap.comp_id, A]
  rw [hfac]
  exact hU.comp hPinv

end HomogeneousSymbol

end TauCeti
