/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Kaehler.Polynomial
public import TauCeti.FieldTheory.FunctionField.SeparablyGenerated
public import TauCeti.FieldTheory.RatFunc.Transcendental
public import TauCeti.RingTheory.Kaehler.BaseChange
public import TauCeti.RingTheory.Kaehler.FormallyEtale

/-!
# One-dimensionality of the Kähler differentials of a function field

Let `k` be a field and `F` a field extension of `k` containing an element `x` that is
transcendental over `k` and *separating*, meaning that `F` is separable algebraic over the
subfield `k(x)` it generates. This file proves that the module of Kähler differentials
`Ω[F⁄k]` is then one-dimensional over `F`, with basis the differential `d x`; every
differential is `(dy/dx) · dx` for a unique scalar.

An algebraic function field of one variable with a separating element is the motivating case:
there `F` is moreover finite over `k(x)`, which the basis construction does not need. Separability
is not cosmetic — it is what the base-change argument runs on — so the general basis results carry
it as a hypothesis. For a one-variable function field over a perfect field, the final theorem also
proves the converse: `x` is separating exactly when `d x` is nonzero.

The proof is the base-change route: `k(x)/k` is a localization of the polynomial ring, whose
differentials are free of rank one on `d X`, and `F/k(x)` is separable, hence formally étale
(`Algebra.FormallyEtale.of_isSeparable`), so `Ω[F⁄k]` is the base change of `Ω[k(x)⁄k]` along
`k(x) → F` by `KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale`.

## Main results

* `TauCeti.kaehlerBasisRatFunc`: `d X` is a basis of `Ω[k(X)⁄k]`.
* `TauCeti.finrank_kaehlerDifferential_eq_one_of_separating`: `dim_F Ω[F⁄k] = 1`.
* `TauCeti.kaehlerBasisOfSeparating`: `d x` is a basis of `Ω[F⁄k]`.
* `TauCeti.derivativeOfSeparating`: differentiation `y ↦ dy/dx` with respect to `x`, as a
  `k`-derivation of `F`, with `TauCeti.derivativeOfSeparating_smul_D` the identity
  `d y = (dy/dx) · dx` and `TauCeti.eq_derivativeOfSeparating` its uniqueness.
* `TauCeti.D_eq_zero_of_isSeparable`: a separable algebraic element has vanishing differential,
  so over a perfect field `TauCeti.transcendental_of_D_ne_zero` reads a nonzero differential as
  transcendence.
* `TauCeti.IsFunctionField.isSeparable_adjoin_iff_D_ne_zero`: the differential criterion for a
  fixed parameter over a perfect field.

## References

The result is Stichtenoth, *Algebraic Function Fields and Codes*, second edition, GTM 254,
§IV.1: the differential module of a function field with a separating element `x` is
one-dimensional with basis `dx`. The proof here is not his — he builds a differential module by
hand from derivations, whereas this file reads the statement off Mathlib's base-change theory of
Kähler differentials.
-/

public section

noncomputable section

namespace TauCeti

open Module Polynomial KaehlerDifferential

open scoped IntermediateField nonZeroDivisors

variable (k : Type*) [Field k]

/-- `d X` is a basis of the module of Kähler differentials of the rational function field
`k(X)` over `k`. -/
def kaehlerBasisRatFunc : Basis Unit (RatFunc k) Ω[RatFunc k⁄k] :=
  haveI : Algebra.FormallyEtale k[X] (RatFunc k) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc k) (k[X])⁰
  kaehlerBasisOfFormallyEtale k k[X] (RatFunc k)
    ((Basis.singleton Unit k[X]).map (KaehlerDifferential.polynomialEquiv k).symm)

@[simp]
theorem kaehlerBasisRatFunc_apply (i : Unit) :
    kaehlerBasisRatFunc k i = D k (RatFunc k) RatFunc.X := by
  have : Algebra.FormallyEtale k[X] (RatFunc k) :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := RatFunc k) (k[X])⁰
  rw [kaehlerBasisRatFunc, kaehlerBasisOfFormallyEtale_apply]
  simp [KaehlerDifferential.map_D, RatFunc.algebraMap_X]

variable {k} {F : Type*} [Field F] [Algebra k F] {x : F}

/-- The differentials of `F` over `k` are free of rank one on `d x`, for `x` a separating
element. This is the whole content of the file; the public statements below are read off it. -/
private theorem exists_basis_unit_D (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    ∃ b : Basis Unit F Ω[F⁄k], b () = D k F x := by
  -- Realize the rational function field inside `F` along `X ↦ x`, and let `F` carry the
  -- resulting `RatFunc k`-algebra structure; it is separable, hence formally étale.
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  have : Algebra.FormallyEtale (RatFunc k) F := .of_isSeparable _ _
  refine ⟨kaehlerBasisOfFormallyEtale k (RatFunc k) F (kaehlerBasisRatFunc k), ?_⟩
  rw [kaehlerBasisOfFormallyEtale_apply, kaehlerBasisRatFunc_apply, KaehlerDifferential.map_D,
    algebraMap_ratFuncAlgebraOfTranscendental_X]

section Separating

variable [Algebra.IsSeparable k⟮x⟯ F] (hx : Transcendental k x)
include hx

/-- The differential of a separating element is nonzero. -/
theorem D_ne_zero_of_separating : D k F x ≠ 0 := by
  obtain ⟨b, hb⟩ := exists_basis_unit_D hx
  exact hb ▸ b.ne_zero ()

/-- **The Kähler differentials of a separably generated extension of transcendence degree one
are one-dimensional**: if `x` is transcendental over `k` and `F` is separable over `k(x)`, then
`Ω[F⁄k]` is a one-dimensional `F`-vector space. -/
theorem finrank_kaehlerDifferential_eq_one_of_separating : finrank F Ω[F⁄k] = 1 := by
  obtain ⟨b, -⟩ := exists_basis_unit_D hx
  simpa using finrank_eq_card_basis b

/-- The differential `d x` of a separating element `x` is a basis of `Ω[F⁄k]`; its coordinate
function sends `d y` to the derivative `dy/dx`. -/
def kaehlerBasisOfSeparating (hx : Transcendental k x) : Basis Unit F Ω[F⁄k] :=
  FiniteDimensional.basisSingleton Unit
    (finrank_kaehlerDifferential_eq_one_of_separating hx) (D k F x) (D_ne_zero_of_separating hx)

@[simp]
theorem kaehlerBasisOfSeparating_apply (i : Unit) : kaehlerBasisOfSeparating hx i = D k F x :=
  FiniteDimensional.basisSingleton_apply _ _ _ _ i

/-- The differential of a separating element spans all of `Ω[F⁄k]`. -/
theorem span_D_eq_top_of_separating : Submodule.span F {D k F x} = ⊤ := by
  have h := (kaehlerBasisOfSeparating hx).span_eq
  rwa [Set.range_unique, kaehlerBasisOfSeparating_apply] at h

/-- **Differentiation with respect to a separating element** `x`: the `k`-derivation of `F`
sending `y` to the coordinate `dy/dx` of `d y` in the basis `d x`. Its derivation structure
supplies the sum and product rules and the vanishing on `k`. -/
def derivativeOfSeparating (hx : Transcendental k x) : Derivation k F F :=
  ((kaehlerBasisOfSeparating hx).coord ()).compDer (D k F)

/-- The defining property of `dy/dx`: it is the coordinate of `d y` in the basis `d x`. -/
@[simp]
theorem derivativeOfSeparating_smul_D (y : F) :
    derivativeOfSeparating hx y • D k F x = D k F y := by
  simpa [derivativeOfSeparating] using (kaehlerBasisOfSeparating hx).sum_repr (D k F y)

/-- `dy/dx` is the only scalar taking `d x` to `d y`. -/
theorem eq_derivativeOfSeparating (y c : F) (hc : c • D k F x = D k F y) :
    c = derivativeOfSeparating hx y :=
  smul_left_injective F (D_ne_zero_of_separating hx)
    (hc.trans (derivativeOfSeparating_smul_D hx y).symm)

@[simp]
theorem derivativeOfSeparating_self : derivativeOfSeparating hx x = 1 :=
  (eq_derivativeOfSeparating hx x 1 (one_smul _ _)).symm

end Separating

/-- A separable algebraic element has vanishing universal differential, so the universal
derivation detects only the inseparable or transcendental part of an extension. -/
theorem D_eq_zero_of_isSeparable (hx : IsSeparable k x) : D k F x = 0 := by
  have hcoeff : aeval x (minpoly k x).derivative ≠ 0 :=
    Separable.aeval_derivative_ne_zero hx (minpoly.aeval k x)
  have hder := (D k F).map_aeval (minpoly k x) x
  rw [minpoly.aeval, map_zero] at hder
  exact (smul_eq_zero.mp hder.symm).resolve_left hcoeff

variable [PerfectField k]

/-- Over a perfect base field, an element with nonzero universal differential is transcendental:
an algebraic element is separable, hence has vanishing differential. -/
theorem transcendental_of_D_ne_zero (hx : D k F x ≠ 0) : Transcendental k x := by
  intro halg
  exact hx (D_eq_zero_of_isSeparable
    (PerfectField.separable_of_irreducible (minpoly.irreducible halg.isIntegral)))

namespace IsFunctionField

/-- An element of a one-variable function field over a perfect field is separating exactly when
its universal differential is nonzero. Both sides fail for an algebraic `x`: its differential
vanishes, while separability of `F / k⟮x⟯` would make the function field algebraic over `k`. -/
@[simp]
theorem isSeparable_adjoin_iff_D_ne_zero (hF : IsFunctionField k F) :
    Algebra.IsSeparable k⟮x⟯ F ↔ D k F x ≠ 0 := by
  by_cases hx : Transcendental k x
  case neg =>
    have halg : IsAlgebraic k x := not_not.mp hx
    have hD : D k F x = 0 := D_eq_zero_of_isSeparable
      (PerfectField.separable_of_irreducible (minpoly.irreducible halg.isIntegral))
    refine iff_of_false (fun hsep ↦ ?_) (not_not.mpr hD)
    let _ := hsep
    let _ : FiniteDimensional k k⟮x⟯ := IntermediateField.adjoin.finiteDimensional halg.isIntegral
    have halgF : Algebra.IsAlgebraic k F := Algebra.IsAlgebraic.trans k k⟮x⟯ F
    obtain ⟨y, hy⟩ := hF.exists_transcendental
    exact hy (halgF.1 y)
  let _ := hF.finiteDimensional_adjoin hx
  have hunr : Algebra.IsSeparable k⟮x⟯ F ↔ Subsingleton Ω[F⁄k⟮x⟯] := by
    rw [← Algebra.FormallyUnramified.iff_isSeparable, Algebra.formallyUnramified_iff]
  have hmap : Subsingleton Ω[F⁄k⟮x⟯] ↔
      (KaehlerDifferential.mapBaseChange k k⟮x⟯ F).range = ⊤ :=
    subsingleton_kaehlerDifferential_iff_range_mapBaseChange_eq_top k k⟮x⟯ F
  have hrange : (KaehlerDifferential.mapBaseChange k k⟮x⟯ F).range =
      Submodule.span F {D k F x} := by
    let x' : k⟮x⟯ := ⟨x, IntermediateField.subset_adjoin k {x} rfl⟩
    have hx'val : algebraMap k⟮x⟯ F x' = x := by
      simpa only [x'] using IntermediateField.algebraMap_apply k⟮x⟯ x'
    have hx' : Transcendental k x' :=
      (Subalgebra.transcendental_iff_transcendental_val
        (S := k⟮x⟯.toSubalgebra)).mpr hx
    have htop : k⟮x'⟯ = ⊤ := by
      apply IntermediateField.lift_injective k⟮x⟯
      rw [IntermediateField.lift_adjoin_simple, IntermediateField.lift_top]
    let e : k⟮x'⟯ ≃ₐ[k] k⟮x⟯ :=
      (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
    let _ : Algebra.IsSeparable k⟮x'⟯ k⟮x⟯ :=
      Algebra.IsSeparable.of_equiv_equiv e.symm.toRingEquiv (RingEquiv.refl k⟮x⟯) (by
        ext z
        simp [e])
    obtain ⟨b, hb⟩ := exists_basis_unit_D hx'
    have hspan : Submodule.span k⟮x⟯ {D k k⟮x⟯ x'} = ⊤ := by
      rw [← hb]
      simpa only [Set.range_unique] using b.span_eq
    rw [range_mapBaseChange_eq_span_singleton k k⟮x⟯ F
      (D k k⟮x⟯ x') hspan, KaehlerDifferential.map_D, hx'val]
  have hdim : finrank F Ω[F⁄k] = 1 := by
    obtain ⟨y, hy, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
    let _ := hsep
    exact finrank_kaehlerDifferential_eq_one_of_separating hy
  have hspan : Submodule.span F {D k F x} = ⊤ ↔ D k F x ≠ 0 :=
    span_singleton_eq_top_iff_ne_zero_of_finrank_eq_one hdim _
  rw [hunr, hmap, hrange, hspan]

end IsFunctionField

end TauCeti
