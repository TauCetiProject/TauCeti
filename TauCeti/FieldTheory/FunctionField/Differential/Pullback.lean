/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Differential.Independence
-- Proof-only: a `k`-algebra map out of `k(X)` is determined by the image of `X`.
import TauCeti.FieldTheory.RatFunc.Automorphism

/-!
# Pulling Kähler differentials back along a separable extension

Let `F' / F` be a finite separable extension of algebraic function fields over the same constant
field `k`. Kähler differentials pull back along it by functoriality,
`KaehlerDifferential.map : Ω[F⁄k] → Ω[F'⁄k]`, `z dx ↦ z dx`, while Weil differentials pull back
by the cotrace `Cotr_{F'/F}` (`TauCeti.weilDifferentialCotrace`). This file shows that the
Kähler–Weil comparison of Stichtenoth's Theorem 4.3.2 intertwines the two.

The key case is the differential of a separating element: the cotrace carries the Weil
differential `dx` of `F` to the Weil differential `dx` of `F'`. Indeed `dx` is the cotrace of the
normalized differential of `k(X)` along `X ↦ x`, the embedding of `k(X)` in `F'` through `F` sends
`X` to the image of `x`, and the cotrace is transitive in the tower `k(X) ⊆ F ⊆ F'`.

Through the comparison, the divisor of the pulled-back Kähler differential is therefore
`Con (ω) + Diff(F'/F)` (`TauCeti.weilDifferentialDivisor_weilDifferentialCotrace`). This is how
the pullback of the invariant differential along an isogeny of elliptic curves is computed.

## Main results

* `TauCeti.weilDifferentialOfSeparating_eq_weilDifferentialCotrace`: `dx` is the cotrace of the
  normalized differential of `k(X)` along any `k(X)`-algebra structure in which `X` acts as `x`.
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

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F]

/-- **`dx` along any embedding of `k(X)` sending `X` to `x`**: the Weil differential of a
separating element `x` is the cotrace of the normalized differential of `k(X)` for every
`k(X)`-algebra structure on `F` in which `X` acts as `x`, not only for the structure
`ratFuncAlgebraOfTranscendental` used to define it. -/
theorem weilDifferentialOfSeparating_eq_weilDifferentialCotrace [Algebra (RatFunc k) F]
    [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    [Algebra.IsSeparable (RatFunc k) F] (hF : IsFunctionField k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (hX : algebraMap (RatFunc k) F RatFunc.X = x) :
    weilDifferentialOfSeparating hF hx =
      weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
        ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ := by
  -- Both `k`-algebra maps `k(X) → F` send `X` to `x`, so the two structures agree.
  have h : IsScalarTower.toAlgHom k (RatFunc k) F =
      k⟮x⟯.val.comp (RatFunc.algEquivOfTranscendental x hx).toAlgHom :=
    RatFunc.algHom_ext (by simp [hX, RatFunc.algEquivOfTranscendental_X])
  obtain rfl : ‹Algebra (RatFunc k) F› = ratFuncAlgebraOfTranscendental hx :=
    Algebra.algebra_ext _ _ fun r ↦ by
      rw [algebraMap_ratFuncAlgebraOfTranscendental_apply]
      exact DFunLike.congr_fun h r
  exact weilDifferentialOfSeparating_def hF hx

variable [Algebra k F'] [Algebra F F'] [IsScalarTower k F F'] [FiniteDimensional F F']
  [Algebra.IsSeparable F F']

/-- **The cotrace carries `dx` to `dx`**: for a finite separable extension `F' / F` of function
fields over `k` and a separating element `x` of `F / k`, the cotrace to `F'` of the Weil
differential `dx` of `F` is the Weil differential of the image of `x` in `F'`. The separability
of `F'` over `k⟮x⟯` follows from that of `F'` over `F` and of `F` over `k⟮x⟯`; it is an argument
because the Weil differential of the image of `x` is only defined under it. -/
theorem weilDifferentialCotrace_weilDifferentialOfSeparating_algebraMap
    (hF : IsFunctionField k F) (hF' : IsFunctionField k F') {x : F} (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] [Algebra.IsSeparable k⟮algebraMap F F' x⟯ F'] :
    weilDifferentialCotrace k F' hF hF' (weilDifferentialOfSeparating hF hx) =
      weilDifferentialOfSeparating hF'
        ((transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx) := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  -- `k(X)` acts on `F'` through `F`, with `X` acting as the image of `x`.
  let _ : Algebra (RatFunc k) F' := ((algebraMap F F').comp (algebraMap (RatFunc k) F)).toAlgebra
  let _ : IsScalarTower (RatFunc k) F F' := .of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower k (RatFunc k) F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply (RatFunc k) F F', ← IsScalarTower.algebraMap_apply k,
      ← IsScalarTower.algebraMap_apply k F F']
  let _ : FiniteDimensional (RatFunc k) F' := FiniteDimensional.trans (RatFunc k) F F'
  let _ : Algebra.IsSeparable (RatFunc k) F' := Algebra.IsSeparable.trans (RatFunc k) F F'
  rw [weilDifferentialOfSeparating_def hF hx,
    weilDifferentialCotrace_weilDifferentialCotrace (k₁ := k) (F₁ := F)]
  refine (weilDifferentialOfSeparating_eq_weilDifferentialCotrace hF' _ ?_).symm
  rw [IsScalarTower.algebraMap_apply (RatFunc k) F F', algebraMap_ratFuncAlgebraOfTranscendental_X]

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
  -- `F'` is separable over `k⟮x⟯` through `F`; read this in the structure `X ↦ x` on `F'`.
  have : Algebra.IsSeparable k⟮algebraMap F F' x⟯ F' := by
    let _ := ratFuncAlgebraOfTranscendental hx
    let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
    let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
    let _ : Algebra (RatFunc k) F' :=
      ((algebraMap F F').comp (algebraMap (RatFunc k) F)).toAlgebra
    let _ : IsScalarTower (RatFunc k) F F' := .of_algebraMap_eq fun _ ↦ rfl
    let _ : IsScalarTower k (RatFunc k) F' := .of_algebraMap_eq fun c ↦ by
      rw [IsScalarTower.algebraMap_apply (RatFunc k) F F', ← IsScalarTower.algebraMap_apply k,
        ← IsScalarTower.algebraMap_apply k F F']
    have h := isSeparable_adjoin_algebraMap_X_iff.mpr (Algebra.IsSeparable.trans (RatFunc k) F F')
    rwa [IsScalarTower.algebraMap_apply (RatFunc k) F F',
      algebraMap_ratFuncAlgebraOfTranscendental_X] at h
  -- Write `ω = c dx`; both sides are then `c dx`.
  obtain ⟨c, rfl⟩ : ∃ c : F, c • D k F x = ω :=
    ⟨_, by simpa using (kaehlerBasisOfSeparating hx).sum_repr ω⟩
  rw [kaehlerDifferentialEquivWeilDifferentialOfSeparating_eq hF' hex' hy hx', map_smul, map_D,
    ← algebraMap_smul F', map_smul, kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    map_smul, kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self,
    weilDifferentialCotrace_smul, weilDifferentialCotrace_weilDifferentialOfSeparating_algebraMap]

end TauCeti
