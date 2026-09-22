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

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section IV.3, Definition 4.3.1 and Theorem 4.3.2.
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
theorem weilDifferentialOfSeparating_eq_weilDifferentialCotrace (hF : IsFunctionField k F)
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
  rw [weilDifferentialOfSeparating_eq_weilDifferentialCotrace, ne_eq,
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

end TauCeti
