/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Algebraic
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Basis
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.RatFunc
public import TauCeti.FieldTheory.FunctionField.ConstantExtension.Unramified
public import TauCeti.FieldTheory.FunctionField.Differential.Comparison

/-!
# The differential `dx` under a constant field extension

Let `F' = F · k'` be a finite separable constant field extension of an algebraic function field
`F / k`, and let `x` be a separating element of `F / k`. Its image in `F'` is separating for
`F' / k'`. This file proves that the cotrace from `F` to `F'` carries the Weil differential `dx` of
`F` (`TauCeti.weilDifferentialOfSeparating`) to the Weil differential `dx` of `F'`. The key case
is the rational function field: the cotrace from `k(X)` to `k'(X)` carries the canonical
differential `η` of `k(X)` to that of `k'(X)`.

Since the cotrace is injective and `F`-semilinear, identities between Weil differentials of `F`
can be checked after a constant field extension, where more places are rational. This is how the
chain rule `dy = (dy/dx) · dx` is proved over an arbitrary exact constant field
(`TauCeti.weilDifferentialOfSeparating_eq_derivativeOfSeparating_smul`).

## Main results

* `TauCeti.weilDifferentialCotrace_ratFuncWeilDifferential`: the cotrace from `k(X)` to `k'(X)`
  carries `η` to `η'`.
* `TauCeti.weilDifferentialCotrace_weilDifferentialOfSeparating`: the cotrace from `F` to
  `F · k'` carries `dx` to `dx`.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.7.4, Definition 3.4.5, Proposition 3.4.11 and Theorem 4.3.2.
-/

public section

open scoped IntermediateField

namespace TauCeti

/-! ### The rational function field -/

section RatFunc

variable {k k' : Type*} [Field k] [Field k']
variable [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k']
variable [Algebra (RatFunc k) (RatFunc k')] [IsScalarTower k (RatFunc k) (RatFunc k')]

/-- The cotrace of `η` has the divisor `-2 P'_∞`: the extension is unramified with trivial
different, and `P'_∞` is the only place over `P_∞`. -/
private theorem isGreatest_cotrace_ratFuncWeilDifferential
    [FiniteDimensional (RatFunc k) (RatFunc k')] [Algebra.IsSeparable (RatFunc k) (RatFunc k')]
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X)
    {ω : ↥(weilDifferentialSpace k' (RatFunc k'))}
    (hωdef : ω = weilDifferentialCotrace k' (RatFunc k') (IsFunctionField.ratFunc k)
      (IsFunctionField.ratFunc k') ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩) :
    IsGreatest {D : Divisor k' (RatFunc k') |
      (ω : Module.Dual k' ↥(repartitionSpace k' (RatFunc k'))) ∈ weilDifferentialFiltration D}
      ((-2 : ℤ) • AlgebraicGeometry.WeilDivisor.ofPoint (Place.infty k')) := by
  have h := constantCompositum_ratFunc_eq_top (k := k) hX
  subst hωdef
  have hη : (⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
      ↥(weilDifferentialSpace k (RatFunc k))) ≠ 0 := by
    simpa [← Subtype.coe_ne_coe] using ratFuncWeilDifferential_ne_zero k
  have hω : (weilDifferentialCotrace k' (RatFunc k') (IsFunctionField.ratFunc k)
      (IsFunctionField.ratFunc k') ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
      Module.Dual k' ↥(repartitionSpace k' (RatFunc k'))) ≠ 0 := by
    simpa [ZeroMemClass.coe_eq_zero] using hη
  convert isGreatest_weilDifferentialDivisor (IsFunctionField.ratFunc k')
    isIntegrallyClosedIn_ratFunc (SetLike.coe_mem _) hω using 1
  rw [weilDifferentialDivisor_weilDifferentialCotrace (IsFunctionField.ratFunc k)
    (IsFunctionField.ratFunc k') isIntegrallyClosedIn_ratFunc isIntegrallyClosedIn_ratFunc _ hη]
  simp only [weilDifferentialDivisor_ratFuncWeilDifferential]
  ext Q'
  rw [AlgebraicGeometry.WeilDivisor.coeff_add, Divisor.coeff_conorm, Divisor.coeff_different,
    Place.differentExponent_eq_zero_of_constantCompositum_eq_top (k := k) h,
    Place.ramificationIdx_eq_one_of_constantCompositum_eq_top (k := k) h]
  simp only [AlgebraicGeometry.WeilDivisor.coeff_zsmul]
  by_cases hQ : Q' = Place.infty k'
  · rw [hQ, (Place.restrict_ratFunc_eq_infty_iff hX _).mpr rfl]
    simp
  · rw [AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne hQ,
      AlgebraicGeometry.WeilDivisor.coeff_ofPoint_of_ne
        (mt (Place.restrict_ratFunc_eq_infty_iff hX _).mp hQ)]
    simp

/-- The cotrace of `η` is normalised at `P'_∞`: its local component at the place at infinity of
`k'(X)`, evaluated at `X⁻¹`, equals `-1`. -/
private theorem repartitionDualComponent_cotrace_ratFuncWeilDifferential
    [FiniteDimensional (RatFunc k) (RatFunc k')] [Algebra.IsSeparable (RatFunc k) (RatFunc k')]
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X)
    {ω : ↥(weilDifferentialSpace k' (RatFunc k'))}
    (hωdef : ω = weilDifferentialCotrace k' (RatFunc k') (IsFunctionField.ratFunc k)
      (IsFunctionField.ratFunc k') ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩) :
    repartitionDualComponent
      (ω : Module.Dual k' ↥(repartitionSpace k' (RatFunc k'))) (Place.infty k')
      (RatFunc.X : RatFunc k')⁻¹ = -1 := by
  have h := constantCompositum_ratFunc_eq_top (k := k) hX
  subst hωdef
  set c := repartitionDualComponent
    (weilDifferentialCotrace k' (RatFunc k') (IsFunctionField.ratFunc k)
      (IsFunctionField.ratFunc k') ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
      Module.Dual k' ↥(repartitionSpace k' (RatFunc k')))
    (Place.infty k') (RatFunc.X : RatFunc k')⁻¹
  -- After `Tr_{k'/k}`, the local components of `Cotr η` over `P_∞` add up to `η_{P_∞} ∘ Tr`, and
  -- `P'_∞` is alone over `P_∞`; evaluating at `α X⁻¹` gives `Tr (α c) = -Tr α` for every `α`.
  have htr (α : k') : Algebra.trace k k' (α * c) = -Algebra.trace k k' α := by
    have hsum := trace_finsum_repartitionDualComponent_weilDifferentialCotrace
      (IsFunctionField.ratFunc k) (IsFunctionField.ratFunc k')
      ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ (Place.infty k)
      (algebraMap k' (RatFunc k') α * (RatFunc.X : RatFunc k')⁻¹)
    simp_rw [Place.restrict_ratFunc_eq_infty_iff hX] at hsum
    rw [finsum_cond_eq_left, ← Algebra.smul_def, map_smul, smul_eq_mul] at hsum
    have hsmul : α • (RatFunc.X : RatFunc k')⁻¹ =
        (RatFunc.X : RatFunc k)⁻¹ • algebraMap k' (RatFunc k') α := by
      rw [Algebra.smul_def, Algebra.smul_def, map_inv₀, hX, mul_comm]
    -- Rewrite the trace of the component at `α X⁻¹` using the splitting over `P_∞`.
    rw [hsum, hsmul, map_smul,
      trace_algebraMap_of_constantCompositum_eq_top isIntegrallyClosedIn_ratFunc h, smul_eq_mul]
    -- Move `α` back inside to evaluate `η` at `X⁻¹`, where it is `-1`.
    rw [← Algebra.commutes, ← Algebra.smul_def, map_smul,
      repartitionDualComponent_ratFuncWeilDifferential_inv_X, smul_eq_mul, mul_neg_one]
  -- The trace form of `k' / k` is nondegenerate and pairs `c + 1` trivially with every `α`.
  have hpair (α : k') : Algebra.traceForm k k' (c + 1) α = 0 := by
    rw [Algebra.traceForm_apply, mul_comm, mul_add, mul_one, map_add, htr, neg_add_cancel]
  exact eq_neg_of_add_eq_zero_left ((traceForm_nondegenerate k k').1 _ hpair)

/-- **The cotrace of `η` under a constant field extension is `η`**: for a finite separable
extension `k' / k`, the cotrace from `k(X)` to `k'(X)` carries the canonical Weil differential `η`
of `k(X)` to that of `k'(X)`. -/
theorem weilDifferentialCotrace_ratFuncWeilDifferential
    (hX : algebraMap (RatFunc k) (RatFunc k') RatFunc.X = RatFunc.X) :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k)
      (constantCompositum_ratFunc_eq_top hX)
    letI := isSeparable_of_constantCompositum_eq_top (k := k)
      (constantCompositum_ratFunc_eq_top hX)
    weilDifferentialCotrace k' (RatFunc k') (IsFunctionField.ratFunc k)
        (IsFunctionField.ratFunc k') ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ =
      ⟨ratFuncWeilDifferential k', ratFuncWeilDifferential_mem k'⟩ := by
  have h := constantCompositum_ratFunc_eq_top (k := k) hX
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  let := isSeparable_of_constantCompositum_eq_top (k := k) h
  set ω := weilDifferentialCotrace k' (RatFunc k') (IsFunctionField.ratFunc k)
    (IsFunctionField.ratFunc k') ⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩
    with hωdef
  exact Subtype.ext (eq_ratFuncWeilDifferential ω.2
    (isGreatest_cotrace_ratFuncWeilDifferential hX hωdef)
    (repartitionDualComponent_cotrace_ratFuncWeilDifferential hX hωdef))

end RatFunc

/-! ### Separating elements under a constant field extension -/

section ConstantExtension

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F']
variable [Algebra k k'] [Algebra k F] [Algebra k F'] [Algebra k' F'] [Algebra F F']
variable [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **`dx` is stable under constant field extension**: for a finite separable constant field
extension `F' = F · k'` and a separating element `x` of `F / k`, whose image in `F'` is separating
over `k'`, the cotrace to `F'` of the Weil differential `dx` of `F` is the Weil differential `dx`
of `F'`. -/
theorem weilDifferentialCotrace_weilDifferentialOfSeparating [FiniteDimensional k k']
    [Algebra.IsSeparable k k'] (h : constantCompositum F k' F' = ⊤) (hF : IsFunctionField k F)
    {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := finiteDimensional_of_constantCompositum_eq_top (k := k) h
    letI := isSeparable_of_constantCompositum_eq_top (k := k) h
    letI : Algebra.IsSeparable k'⟮algebraMap F F' x⟯ F' := by
      have hsep := isSeparable_adjoin_image_of_constantCompositum_eq_top (k := k) (S := {x}) h
      rwa [Set.image_singleton] at hsep
    weilDifferentialCotrace k' F' hF (hF.of_constantCompositum_eq_top h)
        (weilDifferentialOfSeparating hF hx) =
      weilDifferentialOfSeparating (hF.of_constantCompositum_eq_top h)
        (((transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx).extendScalars
          k') := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  let := isSeparable_of_constantCompositum_eq_top (k := k) h
  have : Algebra.IsSeparable k'⟮algebraMap F F' x⟯ F' := by
    have hsep := isSeparable_adjoin_image_of_constantCompositum_eq_top (k := k) (S := {x}) h
    rwa [Set.image_singleton] at hsep
  have hF' : IsFunctionField k' F' := hF.of_constantCompositum_eq_top h
  have hx' : Transcendental k' (algebraMap F F' x) :=
    ((transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx).extendScalars k'
  rw [weilDifferentialOfSeparating_def, weilDifferentialOfSeparating_def]
  -- The rational function fields `k(X) ⊆ k'(X)`, with `X` acting as `x` on `F` and on `F'`.
  have hX : Transcendental k (RatFunc.X : RatFunc k') := fun h ↦
    RatFunc.transcendental_X (h.tower_top k')
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  let _ := ratFuncAlgebraOfTranscendental hx'
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx'
  let _ := isFunctionField_iff_functionField.mp hF'
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx'
  let _ := ratFuncAlgebraOfTranscendental hX
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hX
  have hXX := algebraMap_ratFuncAlgebraOfTranscendental_X hX
  -- `k(X)` acts on `F'` with `X` acting as `x`, compatibly with `F → F'`; the two routes through
  -- `F` and through `k'(X)` agree, as both are `k`-algebra maps sending `X` to `x`.
  have hxk := (transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx
  let _ := ratFuncAlgebraOfTranscendental hxk
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hxk
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental_algebraMap (F' := F') hx
  let _ : IsScalarTower (RatFunc k) (RatFunc k') F' :=
    isScalarTower_ratFunc_ratFunc_of_transcendental hxk hx' hX
  have hcomp := constantCompositum_ratFunc_eq_top (k := k) (k' := k') hXX
  let _ := finiteDimensional_of_constantCompositum_eq_top (k := k) hcomp
  let _ := isSeparable_of_constantCompositum_eq_top (k := k) hcomp
  rw [weilDifferentialCotrace_weilDifferentialCotrace (k₁ := k) (F₁ := F),
    ← weilDifferentialCotrace_ratFuncWeilDifferential hXX,
    weilDifferentialCotrace_weilDifferentialCotrace (k₁ := k') (F₁ := RatFunc k')]

end ConstantExtension

end TauCeti
