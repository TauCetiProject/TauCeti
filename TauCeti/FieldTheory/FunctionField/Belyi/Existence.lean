/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Polynomial
public import TauCeti.FieldTheory.FunctionField.Different.Divisor
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.FieldTheory.IntermediateField.Adjoin.Basic
import TauCeti.FieldTheory.RatFunc.Transcendental

/-!
# Every curve over `ℚ̄` admits a Belyi map

This file proves the constructive direction of Belyi's theorem: an algebraic function field `F`
over a field `k` algebraic over `ℚ`, such as `AlgebraicClosure ℚ` or a number field, with exact
constant field `k`, admits a Belyi map. Explicitly, for every `x ∈ F` transcendental over `k`
there is a nonconstant polynomial `q` with rational coefficients such that `F`, regarded as an
extension of `k(t)` through `t ↦ q(x)`, is an algebraic Belyi pair
(`TauCeti.IsFunctionField.exists_polynomial_isAlgebraicBelyiPair`).

The proof follows Belyi's construction. Only finitely many places `P` of `F` are ramified over
`k(x)` (`TauCeti.Place.finite_setOf_one_lt_ramificationIdx`). At each of them where `x` is regular,
the value `x(P)` lies in a finite extension of `k`; embedding these residue fields into an
algebraic closure of `k` gives a finite set of algebraic numbers. Polynomial Belyification
(`TauCeti.exists_polynomial_aeval_mem_criticalValues_subset`) produces `q ∈ ℚ[X]` sending this set
into `{0, 1}` with all critical values in `{0, 1}`. Then the tower `k(t) ⊆ k(x) ⊆ F`, with
`t = q(x)`, is unramified outside `0`, `1` and `∞` on both steps:

* `k(x) / k(t)` is a polynomial map with critical values in `{0, 1}`
  (`TauCeti.IsAlgebraicBelyiPair.of_criticalValues_subset`);
* a place of `F` ramified over `k(x)` lies over `t = ∞` if `x` has a pole there
  (`TauCeti.Place.mem_integers_of_restrict_ne_infty`), and otherwise over `t = q(x(P)) ∈ {0, 1}`
  (`TauCeti.Place.restrict_eq_adicOfIrreducible_X_sub_C_of_aeval_residue_eq`).

Ramification indices multiply in the tower, so `F / k(t)` is unramified outside `0`, `1`, `∞`
(`TauCeti.IsAlgebraicBelyiPair.of_criticalValues_subset_of_restrict_mem_zeroOneInfty`). The degree
of the resulting Belyi map is not controlled.

The hypothesis that `k` is algebraic over `ℚ` is what makes the values `x(P)` algebraic numbers,
to which polynomial Belyification applies. It cannot be dropped: by the other direction of
Belyi's theorem, a curve over `ℂ` admits a Belyi map only if it is defined over `ℚ̄`.

## Main results

* `TauCeti.IsAlgebraicBelyiPair.of_criticalValues_subset_of_restrict_mem_zeroOneInfty`: composing
  with a polynomial Belyi map `t = q(x)` gives a Belyi map when every place ramified over `k(x)`
  lies over `t = 0`, `t = 1` or `t = ∞`.
* `TauCeti.IsFunctionField.exists_polynomial_isAlgebraicBelyiPair`: for every transcendental
  `x ∈ F` there is `q ∈ ℚ[X]` making `t ↦ q(x)` a Belyi map.
* `TauCeti.IsFunctionField.exists_isAlgebraicBelyiPair`: `F` admits a Belyi map.

## References

* G. V. Belyi, *On Galois extensions of a maximal cyclotomic field*, Izv. Akad. Nauk SSSR
  Ser. Mat. 43 (1979), 267–276.
* Bernhard Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004),
  253–265, Theorem 3.3 and Lemmas 3.5 and 3.6.
* Ernesto Girondo and Gabino González-Diez, *Introduction to Compact Riemann Surfaces and
  Dessins d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University
  Press, 2012, §3.1.
-/

public section

open Polynomial IntermediateField

namespace TauCeti

universe u v

variable {k : Type u} {F : Type v} [Field k] [CharZero k] [Field F] [Algebra k F]

/-- **Composing with a polynomial Belyi map.** Let `x ∈ F` and let `F` be an extension of `k(t)`
through `t ↦ q(x)`, for a polynomial `q` whose critical values in every field extension of `k` lie
in `{0, 1}`. If every place of `F` ramified over `k(x)` lies over `t = 0`, `t = 1` or `t = ∞`, and
the constant field of `F` is `k`, then `F` is an algebraic Belyi pair. -/
theorem IsAlgebraicBelyiPair.of_criticalValues_subset_of_restrict_mem_zeroOneInfty
    [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]
    (hk : IsIntegrallyClosedIn k F) {x : F} {q : k[X]}
    (hq : algebraMap (RatFunc k) F RatFunc.X = aeval x q)
    (hcrit : ∀ (L : Type v) [Field L] [Algebra k L], q.criticalValues L ⊆ {0, 1})
    (hram : ∀ P : Place k F, 1 < Place.ramificationIdx k⟮x⟯ P →
      P.restrict k (RatFunc k) ∈ Place.zeroOneInfty k) :
    IsAlgebraicBelyiPair k F := by
  -- `k(x)` contains `k(t)`, and is an algebraic Belyi pair over it.
  have hmem (r : RatFunc k) : algebraMap (RatFunc k) F r ∈ k⟮x⟯ := by
    rw [← coe_algEquivOfTranscendental_algebraMap_X_apply]
    refine adjoin_simple_le_iff.mpr ?_ (SetLike.coe_mem _)
    rw [hq]
    exact algebra_adjoin_le_adjoin k {x} (aeval_mem_adjoin_singleton k x)
  let : Algebra (RatFunc k) k⟮x⟯ := ((algebraMap (RatFunc k) F).codRestrict k⟮x⟯ hmem).toAlgebra
  have : IsScalarTower (RatFunc k) k⟮x⟯ F := .of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower k (RatFunc k) k⟮x⟯ := .of_algebraMap_eq fun c ↦
    Subtype.ext (IsScalarTower.algebraMap_apply k (RatFunc k) F c)
  have : Algebra.IsIntegral k⟮x⟯ F := Algebra.IsIntegral.tower_top (RatFunc k)
  have hq' : algebraMap (RatFunc k) k⟮x⟯ RatFunc.X = aeval (AdjoinSimple.gen k x) q :=
    Subtype.ext (by rw [AdjoinSimple.coe_aeval_gen_apply]; exact hq)
  have := finiteDimensional_of_aeval_eq (adjoin_adjoinSimple_gen_eq_top x) hq'
  have hE : IsAlgebraicBelyiPair k k⟮x⟯ :=
    .of_criticalValues_subset (adjoin_adjoinSimple_gen_eq_top x) hq' hcrit
  -- Ramification indices multiply in the tower `k(t) ⊆ k(x) ⊆ F`, and both steps are unramified.
  refine ⟨hk, fun {P} hP ↦ ?_⟩
  have hPx : ¬ 1 < Place.ramificationIdx k⟮x⟯ P := fun h ↦ hP (hram P h)
  rw [Place.ramificationIdx_restrict_mul (k₁ := k) (F₁ := k⟮x⟯) P,
    le_antisymm (not_lt.mp hPx) (Place.ramificationIdx_pos k⟮x⟯ P), one_mul]
  exact hE.ramificationIdx_eq_one (by rwa [Place.restrict_restrict])

/-- **A curve over `ℚ̄` admits a Belyi map, through any of its functions.** Let `F` be an
algebraic function field over a field `k` algebraic over `ℚ`, with exact constant field `k`, and
let `x ∈ F` be transcendental over `k`. There is a nonconstant polynomial `q` with rational
coefficients such that `F`, as an extension of `k(t)` through `t ↦ q(x)`, is an algebraic Belyi
pair: unramified outside `t = 0`, `t = 1` and `t = ∞`.

Such a `k(t)`-algebra structure on `F` exists and is finite-dimensional; see
`TauCeti.IsFunctionField.exists_isAlgebraicBelyiPair`. -/
theorem IsFunctionField.exists_polynomial_isAlgebraicBelyiPair [Algebra.IsAlgebraic ℚ k]
    (hF : IsFunctionField k F) (hk : IsIntegrallyClosedIn k F) {x : F}
    (hx : Transcendental k x) :
    ∃ q : ℚ[X], 0 < q.natDegree ∧ ∀ [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
      [FiniteDimensional (RatFunc k) F],
      algebraMap (RatFunc k) F RatFunc.X = aeval x (q.map (algebraMap ℚ k)) →
        IsAlgebraicBelyiPair k F := by
  classical
  have : FiniteDimensional k⟮x⟯ F := hF.finiteDimensional_adjoin hx
  -- Only finitely many places of `F` are ramified over `k(x)`.
  have hB := Place.finite_setOf_one_lt_ramificationIdx (k' := k) (F' := F) k k⟮x⟯
    hx.isFunctionField_adjoin
  -- Embed the residue field at each place into an algebraic closure of `k`, and record the value
  -- of `x` there when `x` is regular.
  let φ (P : Place k F) : P.ResidueField →ₐ[k] AlgebraicClosure k :=
    have := P.finiteDimensional_residueField hF
    IsAlgClosed.lift
  let ξ (P : Place k F) : AlgebraicClosure k :=
    if h : x ∈ P.integers then φ P (IsLocalRing.residue P.integers ⟨x, h⟩) else 0
  have : Algebra.IsAlgebraic ℚ (AlgebraicClosure k) :=
    Algebra.IsAlgebraic.trans ℚ k (AlgebraicClosure k)
  -- Polynomial Belyification carries these values into `{0, 1}`.
  obtain ⟨q, hq, hqS, hqcrit⟩ := exists_polynomial_aeval_mem_criticalValues_subset.{v}
    (S := hB.toFinset.image ξ) fun s _ ↦ (Algebra.IsAlgebraic.isAlgebraic s).isIntegral
  refine ⟨q, hq, fun hβ ↦ .of_criticalValues_subset_of_restrict_mem_zeroOneInfty hk hβ
    (fun L _ _ ↦ ?_) fun P hPB ↦ ?_⟩
  · let : Algebra ℚ L := ((algebraMap k L).comp (algebraMap ℚ k)).toAlgebra
    have : IsScalarTower ℚ k L := .of_algebraMap_eq fun _ ↦ rfl
    rw [criticalValues_map]
    exact hqcrit L
  -- A place of `F` ramified over `k(x)` lies over `t = ∞` if `x` has a pole there, and otherwise
  -- over `t = q(x(P))`, which lies in `{0, 1}` as its image in the algebraic closure does.
  by_cases hxP : x ∈ P.integers
  · have hξ : aeval (ξ P) q ∈ ({0, 1} : Set (AlgebraicClosure k)) :=
      hqS _ (Finset.mem_image_of_mem _ (hB.mem_toFinset.mpr hPB))
    rw [show ξ P = φ P (IsLocalRing.residue P.integers ⟨x, hxP⟩) by
        simp only [ξ, hxP, ↓reduceDIte],
      ← aeval_map_algebraMap k, aeval_algHom_apply] at hξ
    obtain ⟨c, hc, hcξ⟩ : ∃ c : k, (c = 0 ∨ c = 1) ∧ aeval (IsLocalRing.residue P.integers
        ⟨x, hxP⟩) (q.map (algebraMap ℚ k)) = algebraMap k P.ResidueField c := by
      rcases hξ with h | h
      · exact ⟨0, .inl rfl, by rw [map_zero]; exact (map_eq_zero_iff _ (φ P).injective).mp h⟩
      · exact ⟨1, .inr rfl, by rw [map_one]; exact (φ P).injective (h.trans (map_one _).symm)⟩
    rw [Place.restrict_eq_adicOfIrreducible_X_sub_C_of_aeval_residue_eq hβ hxP hcξ]
    rcases hc with rfl | rfl
    · simp
    · exact Place.adicOfIrreducible_X_sub_one_mem_zeroOneInfty
  · by_contra hinf
    exact hxP (Place.mem_integers_of_restrict_ne_infty hβ fun h ↦ hinf (h ▸ by simp))

/-- **A curve over `ℚ̄` admits a Belyi map** (Belyi). An algebraic function field `F` over a
field `k` algebraic over `ℚ`, with exact constant field `k`, carries a finite-dimensional
`k(t)`-algebra structure making it an algebraic Belyi pair. -/
theorem IsFunctionField.exists_isAlgebraicBelyiPair [Algebra.IsAlgebraic ℚ k]
    (hF : IsFunctionField k F) (hk : IsIntegrallyClosedIn k F) :
    ∃ (_ : Algebra (RatFunc k) F) (_ : IsScalarTower k (RatFunc k) F)
      (_ : FiniteDimensional (RatFunc k) F), IsAlgebraicBelyiPair k F := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  obtain ⟨q, hq, h⟩ := hF.exists_polynomial_isAlgebraicBelyiPair hk hx
  have hβ : Transcendental k (aeval x (q.map (algebraMap ℚ k))) :=
    hx.aeval _ (by rw [natDegree_map]; exact hq.ne') (mem_nonZeroDivisors_of_ne_zero
      (leadingCoeff_ne_zero.mpr (ne_zero_of_natDegree_gt (by rwa [natDegree_map]))))
  let := ratFuncAlgebraOfTranscendental hβ
  have := isScalarTower_ratFuncAlgebraOfTranscendental hβ
  have := hF.finiteDimensional_adjoin hβ
  have := finiteDimensional_ratFuncAlgebraOfTranscendental hβ
  exact ⟨_, ‹_›, ‹_›, h (algebraMap_ratFuncAlgebraOfTranscendental_X hβ)⟩

end TauCeti
