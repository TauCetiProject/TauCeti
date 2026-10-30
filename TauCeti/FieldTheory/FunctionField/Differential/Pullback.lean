/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Independence
public import TauCeti.FieldTheory.IntermediateField.Map

/-!
# Pulling Kähler differentials back along a separable extension

Let `F' / F` be a finite separable extension of algebraic function fields over the same constant
field `k`. Kähler differentials pull back along it by functoriality,
`KaehlerDifferential.map : Ω[F⁄k] → Ω[F'⁄k]`, `z dx ↦ z dx`, while Weil differentials pull back
by the cotrace `Cotr_{F'/F}` (`TauCeti.weilDifferentialCotrace`). This file shows that the
Kähler–Weil comparison of Stichtenoth's Theorem 4.3.2 intertwines the two.

The key case is the differential of a separating element: the cotrace carries the Weil
differential `dx` of `F` to the Weil differential `dx` of `F'`. Indeed `dx` is the cotrace of the
normalized differential of `k(X)` along `X ↦ x`, the map `F → F'` is `k(X)`-linear when `X` acts
on `F'` as the image of `x` (`TauCeti.isScalarTower_ratFuncAlgebraOfTranscendental_algebraMap`),
and the cotrace is transitive in the tower `k(X) ⊆ F ⊆ F'`.

Through the comparison, the divisor of the pulled-back Kähler differential is therefore
`Con (ω) + Diff(F'/F)` (`TauCeti.weilDifferentialDivisor_weilDifferentialCotrace`). This is how
the pullback of the invariant differential along an isogeny of elliptic curves is computed.

## Main results

* `TauCeti.weilDifferentialCotrace_weilDifferentialOfSeparating_algebraMap`: the cotrace from `F`
  to `F'` carries `dx` to `dx`.
* `TauCeti.kaehlerDifferentialEquivWeilDifferentialOfSeparating_map`: the comparison carries the
  pullback `KaehlerDifferential.map k k F F' ω` to the cotrace of the Weil differential attached
  to `ω`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Definition 3.4.5, Proposition 3.4.11 and Theorem 4.3.2.
-/

public section

open scoped IntermediateField

namespace TauCeti

open KaehlerDifferential

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']
  [Algebra F F'] [IsScalarTower k F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F']

/-- **The cotrace carries `dx` to `dx`**: for a finite separable extension `F' / F` of function
fields over `k` and a separating element `x` of `F / k`, the cotrace to `F'` of the Weil
differential `dx` of `F` is the Weil differential of the image of `x` in `F'`. -/
theorem weilDifferentialCotrace_weilDifferentialOfSeparating_algebraMap
    (hF : IsFunctionField k F) (hF' : IsFunctionField k F') {x : F} (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] :
    weilDifferentialCotrace k F' hF hF' (weilDifferentialOfSeparating hF hx) =
      weilDifferentialOfSeparating hF'
        ((transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx) := by
  have hx' := (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx
  -- `k(X)` acts on `F` and on `F'` with `X` acting as `x`, compatibly with `F → F'`.
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  let _ := ratFuncAlgebraOfTranscendental hx'
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx'
  let _ := isFunctionField_iff_functionField.mp hF'
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx'
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental_algebraMap (F' := F') hx
  rw [weilDifferentialOfSeparating_def hF hx, weilDifferentialOfSeparating_def hF' hx',
    weilDifferentialCotrace_weilDifferentialCotrace (k₁ := k) (F₁ := F)]

/-- **The Kähler–Weil comparison intertwines the pullback with the cotrace**: for a finite
separable extension `F' / F` of function fields with exact constant field `k`, the comparison of
`F'` (built from any separating element `y`) applied to the pullback of a Kähler differential `ω`
of `F` is the cotrace of the Weil differential that the comparison of `F` (built from any
separating element `x`) attaches to `ω`. -/
theorem kaehlerDifferentialEquivWeilDifferentialOfSeparating_map (hF : IsFunctionField k F)
    (hF' : IsFunctionField k F') (hex : IsIntegrallyClosedIn k F)
    (hex' : IsIntegrallyClosedIn k F') {x : F} (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] {y : F'} (hy : Transcendental k y) [Algebra.IsSeparable k⟮y⟯ F']
    (ω : Ω[F⁄k]) :
    kaehlerDifferentialEquivWeilDifferentialOfSeparating hF' hex' hy (map k k F F' ω) =
      weilDifferentialCotrace k F' hF hF'
        (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hex hx ω) := by
  let _ := weilDifferentialSpaceModule hF
  let _ := weilDifferentialSpaceModule hF'
  have hx' := (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx
  -- Write `ω = c dx`; both sides are then `c dx`.
  obtain ⟨c, rfl⟩ : ∃ c : F, c • D k F x = ω :=
    ⟨_, by simpa using (kaehlerBasisOfSeparating hx).sum_repr ω⟩
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq hF' hex' hy hx', map_smul, map_D,
    ← algebraMap_smul F', map_smul, kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    map_smul, kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    weilDifferentialCotrace_smul, weilDifferentialCotrace_weilDifferentialOfSeparating_algebraMap]

end TauCeti
