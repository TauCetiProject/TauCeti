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
public import TauCeti.RingTheory.Kaehler.Separable

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

Over an arbitrary field the one-dimensionality characterizes separable generation: an algebraic
function field has `dim_F Ω[F⁄k] = 1` exactly when it has a separating element, and otherwise
`dim_F Ω[F⁄k] ≥ 2`. Here `Ω[F⁄k]` differs from Stichtenoth's differential module, which sets
`d t = 0` for every non-separating `t` and is one-dimensional by construction; the two agree only
under separable generation. A function field containing an element outside `k` with a `p`-power
in `k` has no separating element, so its Kähler differentials have dimension at least two.

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
* `TauCeti.derivativeOfSeparating_eq_zero_iff`: differentiation kills exactly the constants of
  an exact characteristic-zero function field.
* `Derivation.apply_eq_derivativeOfSeparating_smul`: the chain rule `D y = (dy/dx) • D x` for
  every derivation `D` of `F` over `k`.
* `TauCeti.derivativeOfSeparating_algebraMap`: `dy/dx` is stable under extension of scalars
  `F / k → F' / k'`.
* `TauCeti.IsFunctionField.isSeparable_adjoin_iff_D_ne_zero`: the differential criterion for a
  fixed parameter over a perfect field.
* `TauCeti.nontrivial_kaehlerDifferential`, `TauCeti.finrank_kaehlerDifferential_pos`: an
  essentially finite type field extension that is not algebraic has nonzero Kähler differentials.
* `TauCeti.transcendental_and_isSeparable_adjoin_of_D_ne_zero`: when `dim_F Ω[F⁄k] = 1`, every
  element with nonzero differential is separating.
* `TauCeti.finrank_kaehlerDifferential_eq_one_iff`: `dim_F Ω[F⁄k] = 1` exactly
  when an essentially finite type transcendental extension `F / k` has a separating element.
* `TauCeti.two_le_finrank_kaehlerDifferential_iff`: without a separating element,
  `dim_F Ω[F⁄k] ≥ 2`; `TauCeti.two_le_finrank_kaehlerDifferential_of_pow_mem`
  produces this from an element outside the image of the base field `k` with a `p`-power in it.

## References

The result is Stichtenoth, *Algebraic Function Fields and Codes*, second edition, GTM 254,
§IV.1: the differential module of a function field with a separating element `x` is
one-dimensional with basis `dx`. The proof here is not his — he builds a differential module by
hand from derivations, whereas this file reads the statement off Mathlib's base-change theory of
Kähler differentials.

The characteristic-zero constant-field criterion is used in the Wronskian treatment of
Weierstrass points in D. M. Goldschmidt, *Algebraic Functions and Projective Curves*, GTM 215,
Springer, 2003.
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

/-- The coordinate of `d y` in the basis `d x` is `dy/dx`. -/
@[simp]
theorem kaehlerBasisOfSeparating_repr_D (y : F) :
    (kaehlerBasisOfSeparating hx).repr (D k F y) () = derivativeOfSeparating hx y := by
  simp [derivativeOfSeparating]

/-- `dy/dx` is the only scalar taking `d x` to `d y`. -/
theorem eq_derivativeOfSeparating (y c : F) (hc : c • D k F x = D k F y) :
    c = derivativeOfSeparating hx y :=
  smul_left_injective F (D_ne_zero_of_separating hx)
    (hc.trans (derivativeOfSeparating_smul_D hx y).symm)

@[simp]
theorem derivativeOfSeparating_self : derivativeOfSeparating hx x = 1 :=
  (eq_derivativeOfSeparating hx x 1 (one_smul _ _)).symm

/-- **The chain rule for a separating element**: every `k`-derivation `D` of `F` into an
`F`-module satisfies `D y = (dy/dx) • D x`. In particular a derivation is determined by its value
at `x`. -/
theorem _root_.Derivation.apply_eq_derivativeOfSeparating_smul {M : Type*} [AddCommGroup M]
    [Module F M] [Module k M] [IsScalarTower k F M] (D : Derivation k F M) (y : F) :
    D y = derivativeOfSeparating hx y • D x := by
  rw [← D.liftKaehlerDifferential_comp_D, ← derivativeOfSeparating_smul_D hx y,
    LinearMap.map_smul, D.liftKaehlerDifferential_comp_D]

/-- Differentiating with respect to a translate `x - a` of a separating element is differentiating
with respect to `x`. -/
theorem derivativeOfSeparating_sub_algebraMap {a : k}
    (hxa : Transcendental k (x - algebraMap k F a)) [Algebra.IsSeparable k⟮x - algebraMap k F a⟯ F]
    (y : F) : derivativeOfSeparating hxa y = derivativeOfSeparating hx y := by
  have h1 : derivativeOfSeparating hxa x = 1 := by
    have h := derivativeOfSeparating_self hxa
    rwa [map_sub, Derivation.map_algebraMap, sub_zero] at h
  rw [(derivativeOfSeparating hxa).apply_eq_derivativeOfSeparating_smul hx y, h1, smul_eq_mul,
    mul_one]

/-- The derivative of a separating element `y` with respect to a separating element `x` is
nonzero. -/
theorem derivativeOfSeparating_ne_zero {y : F} (hy : Transcendental k y)
    [Algebra.IsSeparable k⟮y⟯ F] : derivativeOfSeparating hx y ≠ 0 := fun h ↦ by
  have hD := derivativeOfSeparating_smul_D hx y
  rw [h, zero_smul] at hD
  exact D_ne_zero_of_separating hy hD.symm

end Separating

section ExtendScalars

variable {k' F' : Type*} [Field k'] [Field F'] [Algebra k k'] [Algebra k F'] [Algebra k' F']
variable [Algebra F F'] [IsScalarTower k k' F'] [IsScalarTower k F F']

/-- **Derivatives are stable under extension of scalars**: if `x` is separating for `F / k` and its
image is separating for `F' / k'`, then differentiating with respect to `x` commutes with
`F → F'`: `dy/dx` computed in `F'` is the image of `dy/dx` computed in `F`. -/
theorem derivativeOfSeparating_algebraMap {x : F} (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] (hx' : Transcendental k' (algebraMap F F' x))
    [Algebra.IsSeparable k'⟮algebraMap F F' x⟯ F'] (y : F) :
    derivativeOfSeparating hx' (algebraMap F F' y) =
      algebraMap F F' (derivativeOfSeparating hx y) := by
  -- `y ↦ dy/dx` in `F'` restricts to a `k`-derivation `F → F'`, so the chain rule for `x` applies
  -- to it.
  have h := (((derivativeOfSeparating hx').restrictScalars k).compAlgebraMap F)
    |>.apply_eq_derivativeOfSeparating_smul hx y
  simp only [Derivation.compAlgebraMap_apply, Derivation.restrictScalars_apply,
    derivativeOfSeparating_self] at h
  rw [h, Algebra.smul_def, mul_one]

end ExtendScalars

/-- Differentiation with respect to a separating element kills exactly the constants of
an exact characteristic-zero function field. -/
@[simp]
theorem derivativeOfSeparating_eq_zero_iff [CharZero k] [Algebra.IsSeparable k⟮x⟯ F]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) (y : F) :
    derivativeOfSeparating hx y = 0 ↔ ∃ a : k, algebraMap k F a = y := by
  constructor
  · intro hy
    by_cases halg : IsAlgebraic k y
    · let _ := hex
      exact IsIntegrallyClosedIn.isIntegral_iff.mp halg.isIntegral
    · let _ := hF.finiteDimensional_adjoin halg
      have hDy : D k F y = 0 := by
        rw [← derivativeOfSeparating_smul_D hx y, hy, zero_smul]
      exact False.elim (D_ne_zero_of_separating halg hDy)
  · rintro ⟨a, rfl⟩
    exact (derivativeOfSeparating hx).map_algebraMap a

section TranscendentalDimension

variable [Algebra.EssFiniteType k F] [Algebra.Transcendental k F]

/-- **An element with nonzero differential is separating** when the Kähler differentials are
one-dimensional: if `dim_F Ω[F⁄k] = 1` and `d y ≠ 0`, then `y` is transcendental over `k` and
`F / k(y)` is separable. -/
theorem transcendental_and_isSeparable_adjoin_of_D_ne_zero (h : finrank F Ω[F⁄k] = 1) {y : F}
    (hy : D k F y ≠ 0) : Transcendental k y ∧ Algebra.IsSeparable k⟮y⟯ F := by
  -- `d y` spans `Ω[F⁄k]`, so `Ω[F⁄k(y)]` vanishes and `F / k(y)` is separable; `y` is
  -- transcendental, since otherwise `F` would be algebraic over `k`.
  have hrange : (KaehlerDifferential.mapBaseChange k k⟮y⟯ F).range = ⊤ := by
    rw [eq_top_iff, ← (span_singleton_eq_top_iff_ne_zero_of_finrank_eq_one h _).mpr hy,
      Submodule.span_le, Set.singleton_subset_iff]
    refine ⟨1 ⊗ₜ D k k⟮y⟯ (IntermediateField.AdjoinSimple.gen k y), ?_⟩
    simp
  have : Algebra.FormallyUnramified k⟮y⟯ F :=
    ⟨(subsingleton_kaehlerDifferential_iff_range_mapBaseChange_eq_top k k⟮y⟯ F).mpr hrange⟩
  have : Algebra.EssFiniteType k⟮y⟯ F := .of_comp k k⟮y⟯ F
  have := Algebra.FormallyUnramified.isSeparable k⟮y⟯ F
  refine ⟨fun halg ↦ ?_, this⟩
  have : FiniteDimensional k k⟮y⟯ := IntermediateField.adjoin.finiteDimensional halg.isIntegral
  have : Algebra.IsAlgebraic k F := Algebra.IsAlgebraic.trans k k⟮y⟯ F
  exact Algebra.transcendental_iff_not_isAlgebraic.mp ‹_› inferInstance

/-- **The Kähler differentials of an essentially finite type transcendental field extension
are one-dimensional exactly when it admits a single separating element**:
`dim_F Ω[F⁄k] = 1` if and only if
some `x` transcendental over `k` makes `F / k(x)` separable. -/
theorem finrank_kaehlerDifferential_eq_one_iff :
    finrank F Ω[F⁄k] = 1 ↔ ∃ x : F, Transcendental k x ∧ Algebra.IsSeparable k⟮x⟯ F := by
  refine ⟨fun h ↦ ?_, fun ⟨x, hx, _⟩ ↦ finrank_kaehlerDifferential_eq_one_of_separating hx⟩
  -- Some `d y` is nonzero, and such a `y` is separating.
  obtain ⟨y, hy⟩ : ∃ y : F, D k F y ≠ 0 := by
    by_contra! H
    have := nontrivial_kaehlerDifferential (k := k) (F := F)
    refine (top_ne_bot : (⊤ : Submodule F Ω[F⁄k]) ≠ ⊥) ?_
    rw [← KaehlerDifferential.span_range_derivation k F, Submodule.span_eq_bot]
    rintro _ ⟨z, rfl⟩
    exact H z
  exact ⟨y, transcendental_and_isSeparable_adjoin_of_D_ne_zero h hy⟩

/-- **The Kähler differentials jump in dimension without a separating element**: an essentially
finite type transcendental field extension `F / k` has `dim_F Ω[F⁄k] ≥ 2` exactly when no `x`
transcendental over `k` makes `F / k(x)` separable. -/
theorem two_le_finrank_kaehlerDifferential_iff :
    2 ≤ finrank F Ω[F⁄k] ↔ ∀ x : F, Transcendental k x → ¬ Algebra.IsSeparable k⟮x⟯ F := by
  have := finrank_kaehlerDifferential_pos (k := k) (F := F)
  have h2 : 2 ≤ finrank F Ω[F⁄k] ↔ ¬ finrank F Ω[F⁄k] = 1 := by omega
  rw [h2, finrank_kaehlerDifferential_eq_one_iff (k := k) (F := F)]
  simp only [not_exists, not_and]

/-- An element `α` of `F` outside `k` with a power `α ^ q ^ n` in `k`, `q` the exponential
characteristic of `k`, forces `dim_F Ω[F⁄k] ≥ 2`: such an `α` rules out every separating element
(`TauCeti.not_isSeparable_adjoin_of_pow_mem`). For instance `α = t^{1/p}` in `F = 𝔽_p(t^{1/p})(X)`
over `k = 𝔽_p(t)`. -/
theorem two_le_finrank_kaehlerDifferential_of_pow_mem (q : ℕ) [ExpChar k q] {α : F}
    (hα : α ∉ (algebraMap k F).range) {n : ℕ} (hn : α ^ q ^ n ∈ (algebraMap k F).range) :
    2 ≤ finrank F Ω[F⁄k] :=
  (two_le_finrank_kaehlerDifferential_iff (k := k) (F := F)).mpr fun _ hx ↦
    not_isSeparable_adjoin_of_pow_mem q hα hn hx

end TranscendentalDimension

variable [PerfectField k]

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
