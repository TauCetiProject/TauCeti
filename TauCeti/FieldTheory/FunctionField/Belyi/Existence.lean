/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Polynomial
public import TauCeti.FieldTheory.FunctionField.Basic
public import TauCeti.FieldTheory.RatFunc.Transcendental
import TauCeti.FieldTheory.FunctionField.Belyi.Radical
import TauCeti.FieldTheory.FunctionField.Different.Divisor
import TauCeti.FieldTheory.FunctionField.Place.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Tower
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.RatFunc.Automorphism

/-!
# Every curve over an algebraic extension of `ℚ` admits a Belyi map

**Belyi's theorem, existence direction**: let `k` be a field algebraic over `ℚ`, such as a number
field or `ℚ̄`, and let `F / k` be a function field with exact constant field `k`. Then `F` admits a
Belyi map: there is `β ∈ F` transcendental over `k` such that `F / k(β)` is unramified outside
`β = 0`, `β = 1` and `β = ∞`, that is, `F` over `k(t)` with `t ↦ β` is an algebraic Belyi pair.
Moreover `β` can be taken to be `q(x)` for any transcendental `x ∈ F` and a suitable nonconstant
polynomial `q` with rational coefficients.

The proof composes the map `x : F → ℙ¹` with a polynomial. The extension `F / k(x)` is ramified
over only finitely many places (`TauCeti.Place.finite_setOf_ramificationIdx_ne_one`), and at each
of them `x` either has a pole or takes a value algebraic over `k`, hence over `ℚ`. Polynomial
Belyification of algebraic numbers (`TauCeti.exists_polynomial_aeval_mem_criticalValues_subset`)
gives a nonconstant `q ∈ ℚ[X]` carrying these finitely many values into `{0, 1}` and whose
critical values all lie in `{0, 1}`. Then `t = q(x)` works: `k(x) / k(t)` is a Belyi pair
(`TauCeti.IsAlgebraicBelyiPair.of_criticalValues_subset`), and above a place of `k(t)` outside
`0`, `1` and `∞` the function `x` is regular with a value not sent into `{0, 1}`, so `F / k(x)`
is unramified there. Ramification indices multiply in the tower `k(t) ⊆ k(x) ⊆ F`
(`TauCeti.IsAlgebraicBelyiPair.of_isScalarTower`).

## Main results

* `TauCeti.IsAlgebraicBelyiPair.of_isScalarTower`: a finite extension of an algebraic Belyi pair
  that is unramified over the places outside the three marked fibres is an algebraic Belyi pair.
* `TauCeti.IsFunctionField.exists_polynomial_isAlgebraicBelyiPair`: for every transcendental
  `x ∈ F` there is a nonconstant `q ∈ ℚ[X]` such that `t ↦ q(x)` is a Belyi map.
* `TauCeti.IsFunctionField.exists_isAlgebraicBelyiPair`: `F` admits a Belyi map.

## References

* G. V. Belyi, *On Galois extensions of a maximal cyclotomic field*, Izv. Akad. Nauk SSSR
  Ser. Mat. 43 (1979), 267–276.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  §3.
* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, §3.1.
-/

public section

open Polynomial IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [CharZero k] [Field F] [Algebra k F]

namespace IsAlgebraicBelyiPair

variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
  {E : Type*} [Field E] [Algebra k E] [Algebra (RatFunc k) E] [IsScalarTower k (RatFunc k) E]
  [FiniteDimensional (RatFunc k) E] [Algebra E F] [IsScalarTower k E F]
  [IsScalarTower (RatFunc k) E F]

/-- **Composing a Belyi map with a cover unramified over its unmarked fibres**: if `E / k(t)` is an
algebraic Belyi pair and `F / E` is a finite extension, with exact constant field `k`, in which
every place of `F` over a place of `k(t)` other than `t = 0`, `t = 1` and `t = ∞` is unramified
over `E`, then `F / k(t)` is an algebraic Belyi pair. -/
theorem of_isScalarTower (hE : IsAlgebraicBelyiPair k E) (hF : IsIntegrallyClosedIn k F)
    (h : ∀ P : Place k F, P.restrict k (RatFunc k) ∉ Place.zeroOneInfty k →
      Place.ramificationIdx E P = 1) :
    IsAlgebraicBelyiPair k F where
  isIntegrallyClosedIn := hF
  ramificationIdx_eq_one {P} hP := by
    have : Algebra.IsIntegral E F := .tower_top (RatFunc k)
    rw [Place.ramificationIdx_restrict_mul (k₁ := k) (F₁ := E) P, h P hP, one_mul]
    exact hE.ramificationIdx_eq_one (by rwa [Place.restrict_restrict])

end IsAlgebraicBelyiPair

namespace IsFunctionField

/-- A nonconstant polynomial with rational coefficients in a transcendental element is
transcendental. -/
private theorem transcendental_aeval_map {A : Type*} [CommRing A] [Algebra k A] {x : A}
    (hx : Transcendental k x) {q : ℚ[X]} (hq : 0 < q.natDegree) :
    Transcendental k (aeval x (q.map (algebraMap ℚ k))) :=
  hx.aeval _ (by rw [natDegree_map]; exact hq.ne') (mem_nonZeroDivisors_of_ne_zero
    (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (by rwa [natDegree_map]))))

open Classical in
/-- At a place where `x` is regular, the value of `x`, embedded into an algebraic closure of
`k`. -/
private noncomputable def valueAt (x : F) (hF : IsFunctionField k F) (P : Place k F) :
    AlgebraicClosure k :=
  haveI := P.finiteDimensional_residueField hF
  if h : x ∈ P.integers then
    IsAlgClosed.lift (M := AlgebraicClosure k) (R := k) (S := P.ResidueField)
      (IsLocalRing.residue P.integers ⟨x, h⟩)
  else 0

/-- Above a place of `k(t)` other than `0`, `1` and `∞`, where `t` acts as `q(x)`, the function
`x` is regular, and `q` does not send its value into `{0, 1}`. -/
private theorem aeval_valueAt_notMem [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
    [FiniteDimensional (RatFunc k) F] (hF : IsFunctionField k F) {x : F} {q : ℚ[X]}
    (hq : 0 < q.natDegree)
    (hβ : algebraMap (RatFunc k) F RatFunc.X = aeval x (q.map (algebraMap ℚ k)))
    {P : Place k F} (hP : P.restrict k (RatFunc k) ∉ Place.zeroOneInfty k) :
    aeval (valueAt x hF P) q ∉ ({0, 1} : Set (AlgebraicClosure k)) := by
  -- `x` is regular at `P`, since `q(x) = t` is.
  have hX : (RatFunc.X : RatFunc k) ∈ (P.restrict k (RatFunc k)).integers := not_not.mp
    (Place.X_notMem_integers_iff_eq_infty.not.mpr fun h ↦ hP (h ▸ Place.infty_mem_zeroOneInfty))
  have hxP : x ∈ P.integers := P.mem_integers_of_aeval_mem_integers
    (by rw [natDegree_map]; exact hq.ne')
    (hβ ▸ (Place.mem_integers_restrict_iff k (RatFunc k) P _).mp hX)
  -- If the value of `q(x)` at `P` were `0` or `1`, then `t (t - 1)` would vanish at `P`.
  intro hS
  rw [valueAt, dite_eq_left hxP, ← aeval_map_algebraMap k, aeval_algHom_apply] at hS
  set w : P.integers := aeval ⟨x, hxP⟩ (q.map (algebraMap ℚ k))
  have hw : IsLocalRing.residue P.integers (w * (w - 1)) = 0 := by
    rw [map_mul, map_sub, map_one, Place.residue_aeval]
    rcases hS with h | h
    · rw [(map_eq_zero_iff _ (RingHom.injective _)).mp h, zero_mul]
    · rw [(map_eq_one_iff _ (RingHom.injective _)).mp h, sub_self, mul_zero]
  have hw' : ((w * (w - 1) : P.integers) : F) =
      algebraMap (RatFunc k) F (RatFunc.X * (RatFunc.X - 1)) := by
    simp [w, hβ]
  -- But `t (t - 1)` is a unit at the restriction of `P`.
  rw [Place.residue_eq_zero_iff_valuation_lt_one, hw',
    Place.valuation_algebraMap_restrict k (RatFunc k) P,
    Place.valuation_X_mul_X_sub_one_of_notMem_zeroOneInfty hP, one_pow] at hw
  exact hw.false

variable [Algebra.IsAlgebraic ℚ k]

/-- **Belyi's theorem, existence direction, for a given function**: over a field `k` algebraic
over `ℚ`, let `F / k` be a function field with exact constant field `k` and `x ∈ F` transcendental
over `k`. Then there is a nonconstant polynomial `q` with rational coefficients such that `F` is an
algebraic Belyi pair over `k(t)` for every structure in which `t` acts as `q(x)`: the composite of
`x` with `q` is a Belyi map. Such a structure exists, see
`TauCeti.IsFunctionField.exists_isAlgebraicBelyiPair`. -/
theorem exists_polynomial_isAlgebraicBelyiPair (hF : IsFunctionField k F)
    (hc : IsIntegrallyClosedIn k F) {x : F} (hx : Transcendental k x) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧
      ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F],
        algebraMap (RatFunc k) F RatFunc.X = aeval x (q.map (algebraMap ℚ k)) →
          IsAlgebraicBelyiPair k F := by
  classical
  have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  -- Only finitely many places of `F` ramify over `k(x)`.
  have hR := Place.finite_setOf_ramificationIdx_ne_one (k' := k) (F' := F) k k⟮x⟯
    hx.isFunctionField_adjoin
  -- Belyification carries the values of `x` at those places into `{0, 1}`.
  obtain ⟨q, hq0, hqS, hqcrit⟩ := exists_polynomial_aeval_mem_criticalValues_subset.{v}
    (S := hR.toFinset.image (valueAt x hF)) fun s _ ↦
      (Algebra.IsAlgebraic.trans ℚ k (AlgebraicClosure k)).isIntegral.isIntegral s
  refine ⟨q, hq0, fun hβ ↦ ?_⟩
  set q' := q.map (algebraMap ℚ k)
  -- The field `k(x)`, with `t` acting as `q(x)`, is a Belyi pair, and `F` lies over it.
  set y := AdjoinSimple.gen k x
  have hy : k⟮y⟯ = ⊤ := adjoin_adjoinSimple_gen_eq_top x
  have hyt : Transcendental k (aeval y q') := transcendental_aeval_map
    ((transcendental_algebraMap_iff (algebraMap k⟮x⟯ F).injective).mp
      (by rwa [AdjoinSimple.algebraMap_gen])) hq0
  let : Algebra (RatFunc k) k⟮x⟯ := ratFuncAlgebraOfTranscendental hyt
  have : IsScalarTower k (RatFunc k) k⟮x⟯ := isScalarTower_ratFuncAlgebraOfTranscendental hyt
  have hqE : algebraMap (RatFunc k) k⟮x⟯ RatFunc.X = aeval y q' :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hyt
  have : FiniteDimensional (RatFunc k) k⟮x⟯ := finiteDimensional_of_aeval_eq hy hqE
  have : IsScalarTower (RatFunc k) k⟮x⟯ F := by
    have h : IsScalarTower.toAlgHom k (RatFunc k) F =
        (IsScalarTower.toAlgHom k k⟮x⟯ F).comp (IsScalarTower.toAlgHom k (RatFunc k) k⟮x⟯) :=
      RatFunc.algHom_ext (by simp [hβ, hqE, y])
    exact .of_algebraMap_eq fun r ↦ DFunLike.congr_fun h r
  have hE : IsAlgebraicBelyiPair k k⟮x⟯ := .of_criticalValues_subset hy hqE fun L _ _ ↦ by
    let : Algebra ℚ L := ((algebraMap k L).comp (algebraMap ℚ k)).toAlgebra
    have : IsScalarTower ℚ k L := .of_algebraMap_eq fun _ ↦ rfl
    rw [criticalValues_map]
    exact hqcrit L
  -- Above a place of `k(t)` outside `0`, `1` and `∞`, `F` is unramified over `k(x)`.
  exact hE.of_isScalarTower hc fun P hP ↦ by_contra fun hne ↦ aeval_valueAt_notMem hF hq0 hβ hP
    (hqS _ (Finset.mem_image_of_mem _ ((Set.Finite.mem_toFinset _).mpr hne)))

/-- **Belyi's theorem, existence direction**: over a field `k` algebraic over `ℚ`, such as `ℚ̄` or a
number field, every function field `F / k` with exact constant field `k` admits a Belyi map: there
is `β ∈ F` transcendental over `k` such that `F` over `k(t)`, with `t` acting as `β`, is an
algebraic Belyi pair. -/
theorem exists_isAlgebraicBelyiPair (hF : IsFunctionField k F) (hc : IsIntegrallyClosedIn k F) :
    ∃ (β : F) (hβ : Transcendental k β),
      letI := ratFuncAlgebraOfTranscendental hβ
      haveI := isScalarTower_ratFuncAlgebraOfTranscendental hβ
      haveI : FiniteDimensional k⟮β⟯ F := hF.finiteDimensional_adjoin hβ
      haveI := finiteDimensional_ratFuncAlgebraOfTranscendental hβ
      IsAlgebraicBelyiPair k F := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  obtain ⟨q, hq0, h⟩ := hF.exists_polynomial_isAlgebraicBelyiPair hc hx
  have hβ := transcendental_aeval_map hx hq0
  let := ratFuncAlgebraOfTranscendental hβ
  have := isScalarTower_ratFuncAlgebraOfTranscendental hβ
  have : FiniteDimensional k⟮aeval x (q.map (algebraMap ℚ k))⟯ F := hF.finiteDimensional_adjoin hβ
  have := finiteDimensional_ratFuncAlgebraOfTranscendental hβ
  exact ⟨_, hβ, h (algebraMap_ratFuncAlgebraOfTranscendental_X hβ)⟩

end IsFunctionField

end TauCeti
