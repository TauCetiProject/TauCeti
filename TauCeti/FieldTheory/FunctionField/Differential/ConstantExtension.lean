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
  have hη : (⟨ratFuncWeilDifferential k, ratFuncWeilDifferential_mem k⟩ :
      ↥(weilDifferentialSpace k (RatFunc k))) ≠ 0 := by
    simpa [← Subtype.coe_ne_coe] using ratFuncWeilDifferential_ne_zero k
  have hω : (ω : Module.Dual k' ↥(repartitionSpace k' (RatFunc k'))) ≠ 0 := by
    simpa [ZeroMemClass.coe_eq_zero, ω] using hη
  refine Subtype.ext (eq_ratFuncWeilDifferential ω.2 ?_ ?_)
  · -- `(Cotr η) = Con (-2 P_∞) + Diff = -2 P'_∞`: the extension is unramified with trivial
    -- different, and `P'_∞` is the only place over `P_∞`.
    convert isGreatest_weilDifferentialDivisor (IsFunctionField.ratFunc k')
      isIntegrallyClosedIn_ratFunc ω.2 hω using 1
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
  · -- After `Tr_{k'/k}`, the local components of `Cotr η` over `P_∞` add up to `η_{P_∞} ∘ Tr`, and
    -- `P'_∞` is alone over `P_∞`; evaluating at `α X⁻¹` gives `Tr (α c) = -Tr α` for every `α`,
    -- where `c` is the value to compute, and the trace form is nondegenerate.
    set c := repartitionDualComponent (ω : Module.Dual k' ↥(repartitionSpace k' (RatFunc k')))
      (Place.infty k') (RatFunc.X : RatFunc k')⁻¹
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
      rw [hsum, hsmul, map_smul,
        trace_algebraMap_of_constantCompositum_eq_top isIntegrallyClosedIn_ratFunc h,
        smul_eq_mul, ← Algebra.commutes, ← Algebra.smul_def, map_smul,
        repartitionDualComponent_ratFuncWeilDifferential_inv_X, smul_eq_mul, mul_neg_one]
    by_contra hne
    obtain ⟨β, hβ⟩ := Algebra.trace_surjective k k' 1
    have h1 := htr (β / (c + 1))
    rw [div_mul_eq_mul_div, eq_neg_iff_add_eq_zero, ← map_add, ← add_div, ← mul_add_one,
      mul_div_assoc, div_self (by rwa [Ne, add_eq_zero_iff_eq_neg]), mul_one, hβ] at h1
    exact one_ne_zero h1

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
    letI := isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top (k := k) (x := x) h
    weilDifferentialCotrace k' F' hF (hF.of_constantCompositum_eq_top h)
        (weilDifferentialOfSeparating hF hx) =
      weilDifferentialOfSeparating (hF.of_constantCompositum_eq_top h)
        (((transcendental_algebraMap_iff (algebraMap F F').injective).mpr hx).extendScalars
          k') := by
  let := finiteDimensional_of_constantCompositum_eq_top (k := k) h
  let := isSeparable_of_constantCompositum_eq_top (k := k) h
  let := isSeparable_adjoin_algebraMap_of_constantCompositum_eq_top (k := k) (x := x) h
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
  -- `k(X)` acts on `F'` through `F`; the two routes through `F` and through `k'(X)` agree, as
  -- both are `k`-algebra maps sending `X` to `x`.
  let _ : Algebra (RatFunc k) F' := ((algebraMap F F').comp (algebraMap (RatFunc k) F)).toAlgebra
  let _ : IsScalarTower (RatFunc k) F F' := .of_algebraMap_eq fun _ ↦ rfl
  let _ : IsScalarTower k (RatFunc k) F' := .of_algebraMap_eq fun c ↦ by
    rw [IsScalarTower.algebraMap_apply (RatFunc k) F F', ← IsScalarTower.algebraMap_apply k,
      ← IsScalarTower.algebraMap_apply k F F']
  let _ : IsScalarTower (RatFunc k) (RatFunc k') F' := .of_algebraMap_eq fun r ↦ by
    -- Both ring maps `k(X) → F'` are determined by their values on `k[X]`.
    refine RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors (Polynomial k))
      (j := algebraMap (RatFunc k) F')
      (k := (algebraMap (RatFunc k') F').comp (algebraMap (RatFunc k) (RatFunc k')))
      (Polynomial.ringHom_ext (fun c ↦ ?_) ?_)) r
    · rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, RatFunc.algebraMap_C,
        ← RatFunc.algebraMap_eq_C, ← IsScalarTower.algebraMap_apply k (RatFunc k) F',
        ← IsScalarTower.algebraMap_apply k (RatFunc k) (RatFunc k'),
        IsScalarTower.algebraMap_apply k k' (RatFunc k'),
        ← IsScalarTower.algebraMap_apply k' (RatFunc k') F',
        ← IsScalarTower.algebraMap_apply k k' F']
    · simp only [RingHom.comp_apply, RatFunc.algebraMap_X]
      rw [hXX, algebraMap_ratFuncAlgebraOfTranscendental_X,
        IsScalarTower.algebraMap_apply (RatFunc k) F F',
        algebraMap_ratFuncAlgebraOfTranscendental_X]
  have hcomp := constantCompositum_ratFunc_eq_top (k := k) (k' := k') hXX
  let _ := finiteDimensional_of_constantCompositum_eq_top (k := k) hcomp
  let _ := isSeparable_of_constantCompositum_eq_top (k := k) hcomp
  rw [weilDifferentialCotrace_weilDifferentialCotrace (k₁ := k) (F₁ := F),
    ← weilDifferentialCotrace_ratFuncWeilDifferential hXX,
    weilDifferentialCotrace_weilDifferentialCotrace (k₁ := k') (F₁ := RatFunc k')]

end ConstantExtension

end TauCeti
