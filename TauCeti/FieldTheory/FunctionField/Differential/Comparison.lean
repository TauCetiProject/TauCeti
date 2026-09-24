/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Cotrace
public import TauCeti.FieldTheory.FunctionField.Differential.Kaehler
public import TauCeti.FieldTheory.FunctionField.Differential.RatFunc

/-!
# Comparing Kähler and Weil differentials

Let `F / k` be an algebraic function field and let `x ∈ F` be a separating element.  The
embedding `k(X) → F` which sends `X` to `x` carries the normalized Weil differential `dX` of
`k(X)` to a nonzero differential of `F` by cotrace.  This differential, written
`TauCeti.weilDifferentialOfSeparating`, is the Weil-theoretic `dx`.

Assume in addition that `k` is algebraically closed in `F` (`IsIntegrallyClosedIn k F`).  Both
the Kähler and Weil differential spaces are then one-dimensional over `F`.  Sending the Kähler
differential `D k F x` to this cotrace therefore determines an `F`-linear equivalence

`Ω[F⁄k] ≃ₗ[F] weilDifferentialSpace k F`.

For every `y ∈ F`, the equivalence sends `dy` to `(dy/dx) dx`.  This is the linear comparison in
Stichtenoth, Theorem 4.3.2.  Compatibility with local components and residues, and independence
from the separating parameter, remain to be proved.

The divisor of `dx` is explicit: `(dx) = -2 (x)_∞ + Diff(F / k(x))` (Stichtenoth, Remark 4.3.7(c)).
It is the divisor of a cotrace, `Con (η) + Diff(F / k(x))`, where the normalized differential `η` of
`k(x)` has divisor `-2 P_∞`, and the conorm of `P_∞ = (X)_∞` is the pole divisor of `x`.  In
particular `-2 (x)_∞ + Diff(F / k(x))` is a canonical divisor of `F`.

## Main definitions

* `TauCeti.weilDifferentialOfSeparating`: the cotrace of the normalized differential of `k(X)`
  along the embedding `X ↦ x`.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating`: the comparison equivalence
  determined by a separating element.

## Main results

* `TauCeti.weilDifferentialOfSeparating_ne_zero`: `dx` is nonzero.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self`: the comparison sends
  `dx` to its Weil counterpart.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_D`: the comparison sends `dy`
  to `(dy/dx) dx`.
* `TauCeti.weilDifferentialDivisor_weilDifferentialOfSeparating`:
  `(dx) = -2 (x)_∞ + Diff(F / k(x))`, and
  `TauCeti.weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential`, the same
  identity for any finite separable extension of `k(x)`.
* `TauCeti.divisorClass_neg_two_zsmul_poles_add_different_eq_canonicalClass`:
  `-2 (x)_∞ + Diff(F / k(x))` represents the canonical class.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.3, Definition 4.3.1, Theorem 4.3.2 and Remark 4.3.7.
-/

public section

open scoped IntermediateField

namespace TauCeti

open Module KaehlerDifferential

universe u v

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F]
variable {x : F}

/-- The Weil differential `dx` attached to a separating element `x`: the cotrace to `F` of the
normalized differential `dX` on the rational function field, along the embedding `X ↦ x`.

The result belongs to the intrinsic Weil differential space, so the chosen rational-function
algebra structure used in its construction is not exposed in the type. -/
noncomputable def weilDifferentialOfSeparating (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    ↥(weilDifferentialSpace k F) :=
  letI := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
    ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩

/-- The Weil differential attached to `x` is the cotrace of the normalized differential on
`k(X)` under the rational-function algebra structure induced by `X ↦ x`. -/
theorem weilDifferentialOfSeparating_def (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := ratFuncAlgebraOfTranscendental hx
    let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
    let _ := isFunctionField_iff_functionField.mp hF
    let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
    weilDifferentialOfSeparating hF hx =
      weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ := by
  rw [weilDifferentialOfSeparating]

/-- The Weil differential `dx` attached to a separating element is nonzero. -/
theorem weilDifferentialOfSeparating_ne_zero (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    weilDifferentialOfSeparating hF hx ≠ 0 := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  rw [weilDifferentialOfSeparating_def, ne_eq,
    weilDifferentialCotrace_eq_zero_iff, Submodule.mk_eq_zero]
  exact ratFuncWeilDifferential_ne_zero k

/-- The basis of the Weil differential space whose unique vector is the differential `dx`
attached to a separating element. -/
noncomputable def weilDifferentialBasisOfSeparating (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    Basis Unit F ↥(weilDifferentialSpace k F) :=
  let _ := weilDifferentialSpaceModule hF
  FiniteDimensional.basisSingleton Unit (finrank_weilDifferentialSpace hF hex)
    (weilDifferentialOfSeparating hF hx) (weilDifferentialOfSeparating_ne_zero hF hx)

@[simp]
theorem weilDifferentialBasisOfSeparating_apply (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] (i : Unit) :
    letI := weilDifferentialSpaceModule hF
    weilDifferentialBasisOfSeparating hF hex hx i = weilDifferentialOfSeparating hF hx := by
  let _ := weilDifferentialSpaceModule hF
  rw [weilDifferentialBasisOfSeparating]
  exact FiniteDimensional.basisSingleton_apply _ _ _ _ i

/-- **The Kähler–Weil differential comparison for a separating element** (Stichtenoth,
Theorem 4.3.2): the `F`-linear equivalence which sends the Kähler differential `dx` to the
cotrace of the normalized Weil differential `dX` along `k(X) → F`, `X ↦ x`. -/
noncomputable def kaehlerDifferentialEquivWeilDifferentialOfSeparating
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    Ω[F⁄k] ≃ₗ[F] ↥(weilDifferentialSpace k F) :=
  letI := weilDifferentialSpaceModule hF
  (kaehlerBasisOfSeparating hx).equiv (weilDifferentialBasisOfSeparating hF hex hx)
    (Equiv.refl Unit)

/-- The Kähler–Weil comparison sends the differential of the chosen separating element to its
Weil counterpart. -/
@[simp]
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx (D k F x) =
      weilDifferentialOfSeparating hF hx := by
  let _ := weilDifferentialSpaceModule hF
  rw [← kaehlerBasisOfSeparating_apply hx (),
    kaehlerDifferentialEquivWeilDifferentialOfSeparating, Basis.equiv_apply]
  exact weilDifferentialBasisOfSeparating_apply hF hex hx ()

/-- The inverse Kähler–Weil comparison sends the Weil differential attached to the chosen
separating element back to its Kähler differential. -/
@[simp]
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_symm_weilDifferentialOfSeparating
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx).symm
        (weilDifferentialOfSeparating hF hx) = D k F x := by
  let _ := weilDifferentialSpaceModule hF
  apply (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx).injective
  rw [LinearEquiv.apply_symm_apply,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self]

/-- Under the Kähler–Weil comparison determined by `x`, the differential `dy` is
`(dy/dx) dx`. -/
@[simp]
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_D
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] (y : F) :
    letI := weilDifferentialSpaceModule hF
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx (D k F y) =
      derivativeOfSeparating hx y • weilDifferentialOfSeparating hF hx := by
  let := weilDifferentialSpaceModule hF
  rw [← derivativeOfSeparating_smul_D hx y, map_smul,
    kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self]

/-! ### The divisor of `dx` -/

section RatFunc

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [FiniteDimensional (RatFunc k) F] [Algebra.IsSeparable (RatFunc k) F]

/-- The cotrace to `F` of the normalized differential of `k(x)` is nonzero. -/
theorem weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero (hF : IsFunctionField k F) :
    (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
          Module.Dual k ↥(repartitionSpace k F)) ≠ 0 := by
  rw [ne_eq, ZeroMemClass.coe_eq_zero, weilDifferentialCotrace_eq_zero_iff,
    Submodule.mk_eq_zero]
  exact ratFuncWeilDifferential_ne_zero k

/-- **The divisor of `dx`** (Stichtenoth, Remark 4.3.7(c)): for a finite separable extension `F`
of `k(x)` with exact constant field `k`, the cotrace to `F` of the normalized differential `η` of
`k(x)` has divisor `-2 (x)_∞ + Diff(F / k(x))`, where `x` is the image in `F` of the variable of
`k(x)`. -/
@[simp]
theorem weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    weilDifferentialDivisor hF hex
        (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
          ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩).2
        (weilDifferentialCotrace_ratFuncWeilDifferential_ne_zero hF) =
      (-2 : ℤ) • Divisor.poles hF (Units.map (algebraMap (RatFunc k) F : RatFunc k →* F)
          (Units.mk0 RatFunc.X RatFunc.X_ne_zero)) +
        Divisor.different k F (IsFunctionField.ratFunc k) := by
  -- `(Cotr η) = Con (η) + Diff(F / k(x))`, `(η) = -2 P_∞`, and `Con P_∞ = Con (x)_∞ = (x)_∞`.
  rw [weilDifferentialDivisor_weilDifferentialCotrace (IsFunctionField.ratFunc k) hF
    isIntegrallyClosedIn_ratFunc hex _ (by simpa using ratFuncWeilDifferential_ne_zero k),
    weilDifferentialDivisor_ratFuncWeilDifferential, map_zsmul, ← Divisor.poles_X,
    Divisor.conorm_poles k F (IsFunctionField.ratFunc k) hF]

/-- **`-2 (x)_∞ + Diff(F / k(x))` is a canonical divisor** (Stichtenoth, Remark 4.3.7(c)): for a
finite separable extension `F` of `k(x)` with exact constant field `k`, this divisor represents the
canonical class of `F`. -/
@[simp]
theorem divisorClass_neg_two_zsmul_poles_add_different_eq_canonicalClass
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) :
    -(2 • (Place.orderSystem hF).divisorClass
        (Divisor.poles hF (Units.map (algebraMap (RatFunc k) F : RatFunc k →* F)
          (Units.mk0 RatFunc.X RatFunc.X_ne_zero)))) +
      (Place.orderSystem hF).divisorClass
        (Divisor.different k F (IsFunctionField.ratFunc k)) =
      canonicalClass hF hex := by
  calc
    _ = (Place.orderSystem hF).divisorClass
          ((-2 : ℤ) • Divisor.poles hF
            (Units.map (algebraMap (RatFunc k) F : RatFunc k →* F)
              (Units.mk0 RatFunc.X RatFunc.X_ne_zero)) +
            Divisor.different k F (IsFunctionField.ratFunc k)) := by simp; rfl
    _ = canonicalClass hF hex := by
      rw [← weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential hF hex,
        divisorClass_weilDifferentialDivisor]

end RatFunc

/-- **The divisor of `dx`** (Stichtenoth, Remark 4.3.7(c)): for a separating element `x` of `F / k`
with exact constant field `k`, the Weil differential `dx` has divisor `-2 (x)_∞ + Diff(F / k(x))`,
the different being taken along the embedding `k(X) → F`, `X ↦ x`. -/
@[simp]
theorem weilDifferentialDivisor_weilDifferentialOfSeparating (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := ratFuncAlgebraOfTranscendental hx
    letI := isScalarTower_ratFuncAlgebraOfTranscendental hx
    letI := isFunctionField_iff_functionField.mp hF
    letI := isSeparable_ratFuncAlgebraOfTranscendental hx
    weilDifferentialDivisor hF hex (weilDifferentialOfSeparating hF hx).2
        (by simpa using weilDifferentialOfSeparating_ne_zero hF hx) =
      (-2 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero) +
        Divisor.different k F (IsFunctionField.ratFunc k) := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  have hX : Units.map (algebraMap (RatFunc k) F : RatFunc k →* F)
      (Units.mk0 RatFunc.X RatFunc.X_ne_zero) = Units.mk0 x hx.ne_zero :=
    Units.ext (algebraMap_ratFuncAlgebraOfTranscendental_X hx)
  simp_rw [weilDifferentialOfSeparating_def, ← hX]
  exact weilDifferentialDivisor_weilDifferentialCotrace_ratFuncWeilDifferential hF hex

end TauCeti
