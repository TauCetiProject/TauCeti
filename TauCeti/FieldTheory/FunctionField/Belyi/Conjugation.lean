/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.FunctionField.Place.Extension.Equiv
public import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Order
import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Galois conjugation of algebraic Belyi pairs

Let `σ : k ≃+* k'` be an isomorphism of fields of characteristic zero, for instance an element of
the absolute Galois group of `ℚ` acting on an algebraic closure. The conjugate of an algebraic
Belyi pair `F / k(t)` along `σ` is the same field `F`, with its structure maps from `k` and from
`k(t)` precomposed with `σ⁻¹` and with the coefficient map of `σ⁻¹`, and with the same
distinguished function `t`. This is the function-field form of base change of a Belyi map along
`σ`. Here a conjugate is described by any field `F'` over `k'(t)` together with a ring isomorphism
`τ : F ≃+* F'` carrying `k(t)` onto `k'(t)` by the coefficient map `RatFunc.mapRingEquiv σ`; for
the conjugate structure on `F` itself, `τ` is the identity.

The coefficient map fixes `t` and `t - 1`, so the bijection it induces between the places of
`k(t)` and those of `k'(t)` fixes each of the three marked places `t = 0`, `t = 1` and `t = ∞`
(`TauCeti.Place.equivOfRingEquiv_mapRingEquiv_markedPlace`); the marked places are
`k`-rational, which is why conjugation preserves them. Consequently conjugation carries algebraic
Belyi pairs to algebraic Belyi pairs (`TauCeti.IsAlgebraicBelyiPair.of_mapRingEquiv`) of the same
degree (`TauCeti.finrank_eq_of_mapRingEquiv`). Place by place, `τ` carries the places of `F` over
the marked place numbered `i` bijectively onto the places of `F'` over the marked place numbered
`i` (`TauCeti.Place.restrict_equivOfRingEquiv_eq_markedPlace_iff`), with the same ramification
indices (`TauCeti.Place.ramificationIdx_equivOfRingEquiv_of_comm`) and residue degrees
(`TauCeti.Place.degree_equivOfRingEquiv`).

Conjugation does not in general preserve the isomorphism class of a Belyi pair: the action of the
absolute Galois group on isomorphism classes, its orbits and stabilizers, and the field of moduli
are built on top of this transport.

## Main results

* `TauCeti.Place.equivOfRingEquiv_mapRingEquiv_markedPlace`: conjugation fixes the marked places.
* `TauCeti.IsAlgebraicBelyiPair.of_mapRingEquiv`: the conjugate of an algebraic Belyi pair is an
  algebraic Belyi pair.
* `TauCeti.finrank_eq_of_mapRingEquiv`: of the same degree.
* `TauCeti.Place.restrict_equivOfRingEquiv_eq_markedPlace_iff`: conjugation keeps the fibres over
  the marked places.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, LMS Student Texts 79, Cambridge University Press, 2012, Chapter 3.
* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265.
-/

public section

open RatFunc

namespace TauCeti

namespace Place

variable {k k' : Type*} [Field k] [Field k'] (σ : k ≃+* k')

/-- **Conjugation fixes the marked places**: the bijection between the places of `k(t)` and
those of `k'(t)` induced by the coefficient map of `σ : k ≃+* k'` carries the marked place
numbered `i` to the marked place numbered `i`. -/
@[simp]
theorem equivOfRingEquiv_mapRingEquiv_markedPlace (i : Fin 3) :
    equivOfRingEquiv σ (RatFunc.mapRingEquiv σ)
      (RatFunc.mapRingEquiv_algebraMap_const σ) (markedPlace k i) = markedPlace k' i := by
  have h0 {P : Place k' (RatFunc k')} (h : 0 < P.ord X) : P = markedPlace k' 0 := by
    rw [markedPlace_zero]
    exact ord_X_pos_iff.mp h
  have h1 {P : Place k' (RatFunc k')} (h : 0 < P.ord (X - C 1)) : P = markedPlace k' 1 := by
    rw [markedPlace_one]
    exact ord_X_sub_C_pos_iff.mp h
  have h2 {P : Place k' (RatFunc k')} (h : P.ord X < 0) : P = markedPlace k' 2 := by
    rw [markedPlace_two]
    exact X_notMem_integers_iff_eq_infty.mp (by rwa [mem_integers_iff_ord_nonneg, not_le])
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · exact h0 (by simp [ord_adicOfIrreducible_X_self])
  · -- `simp` would rewrite `C 1` to `1` inside the polynomial indexing the place, so rewrite.
    refine h1 ?_
    rw [ord_equivOfRingEquiv, RatFunc.mapRingEquiv_symm, map_sub, RatFunc.mapRingEquiv_X,
      RatFunc.mapRingEquiv_C, map_one, markedPlace_one]
    exact ord_X_sub_C_pos_iff.mpr rfl
  · exact h2 (by simp [ord_infty])

/-- **Conjugation preserves the three marked places as a set.** -/
theorem equivOfRingEquiv_mapRingEquiv_mem_zeroOneInfty_iff {P : Place k (RatFunc k)} :
    equivOfRingEquiv σ (RatFunc.mapRingEquiv σ)
      (RatFunc.mapRingEquiv_algebraMap_const σ) P ∈ zeroOneInfty k' ↔
      P ∈ zeroOneInfty k := by
  simp only [← range_markedPlace, Set.mem_range, ← equivOfRingEquiv_mapRingEquiv_markedPlace σ,
    Equiv.apply_eq_iff_eq]

end Place

section Conjugate

variable {k k' F F' : Type*} [Field k] [Field k'] [Field F] [Field F'] [Algebra k F]
  [Algebra k' F'] [Algebra (RatFunc k) F] [Algebra (RatFunc k') F']
  [IsScalarTower k (RatFunc k) F] [IsScalarTower k' (RatFunc k') F']
  (σ : k ≃+* k') (τ : F ≃+* F')
  (hτ : ∀ x, τ (algebraMap (RatFunc k) F x) =
    algebraMap (RatFunc k') F' (RatFunc.mapRingEquiv σ x))

include hτ

/-- An isomorphism `τ : F ≃+* F'` carrying `k(t)` onto `k'(t)` by the coefficient map of `σ`
carries the constants `k` onto `k'` along `σ`. -/
theorem apply_algebraMap_eq_of_mapRingEquiv (c : k) :
    τ (algebraMap k F c) = algebraMap k' F' (σ c) := by
  rw [IsScalarTower.algebraMap_apply k (RatFunc k) F, hτ,
    RatFunc.mapRingEquiv_algebraMap_const, ← IsScalarTower.algebraMap_apply]

/-- **Conjugation keeps the fibres over the marked places**: if `τ : F ≃+* F'` carries `k(t)`
onto `k'(t)` by the coefficient map of `σ`, then a place of `F` lies over the marked place
numbered `i` exactly when its transport along `τ` lies over the marked place numbered `i`. -/
theorem Place.restrict_equivOfRingEquiv_eq_markedPlace_iff [Algebra.IsIntegral (RatFunc k) F]
    [Algebra.IsIntegral (RatFunc k') F'] {P : Place k F} {i : Fin 3} :
    (Place.equivOfRingEquiv σ τ (apply_algebraMap_eq_of_mapRingEquiv σ τ hτ) P).restrict k'
        (RatFunc k') = Place.markedPlace k' i ↔
      P.restrict k (RatFunc k) = Place.markedPlace k i := by
  rw [Place.restrict_equivOfRingEquiv σ τ _ (RatFunc.mapRingEquiv σ) hτ
    (RatFunc.mapRingEquiv_algebraMap_const σ),
    ← Place.equivOfRingEquiv_mapRingEquiv_markedPlace σ i, Equiv.apply_eq_iff_eq]

omit [Algebra k F] [Algebra k' F'] [IsScalarTower k (RatFunc k) F]
  [IsScalarTower k' (RatFunc k') F'] in
/-- **Conjugation keeps the degree**: if `τ : F ≃+* F'` carries `k(t)` onto `k'(t)` by the
coefficient map of `σ`, then the degrees of `F` and `F'` over the rational function fields agree. -/
theorem finrank_eq_of_mapRingEquiv :
    Module.finrank (RatFunc k') F' = Module.finrank (RatFunc k) F :=
  (Algebra.finrank_eq_of_equiv_equiv (RatFunc.mapRingEquiv σ) τ
    (RingHom.ext fun x ↦ (hτ x).symm)).symm

/-- **The Galois conjugate of an algebraic Belyi pair is an algebraic Belyi pair**: if `F` is an
algebraic Belyi pair over `k`, and `τ : F ≃+* F'` carries `k(t)` onto `k'(t)` by the coefficient
map of `σ : k ≃+* k'`, then `F'` is an algebraic Belyi pair over `k'`.

Taking `F' = F` with its structure maps precomposed with `σ⁻¹` and `τ` the identity, this is the
conjugation of a Belyi pair by an automorphism `σ` of the constants. -/
theorem IsAlgebraicBelyiPair.of_mapRingEquiv [CharZero k] [CharZero k']
    [FiniteDimensional (RatFunc k) F] [FiniteDimensional (RatFunc k') F']
    (h : IsAlgebraicBelyiPair k F) : IsAlgebraicBelyiPair k' F' where
  isIntegrallyClosedIn :=
    h.isIntegrallyClosedIn.of_ringEquiv σ τ (apply_algebraMap_eq_of_mapRingEquiv σ τ hτ)
  ramificationIdx_eq_one {P'} hP' := by
    have hk := apply_algebraMap_eq_of_mapRingEquiv σ τ hτ
    obtain ⟨Q, rfl⟩ := (Place.equivOfRingEquiv σ τ hk).surjective P'
    rw [Place.ramificationIdx_equivOfRingEquiv_of_comm σ τ hk _ hτ]
    refine h.ramificationIdx_eq_one fun hQ ↦ hP' ?_
    rwa [Place.restrict_equivOfRingEquiv σ τ hk _ hτ (RatFunc.mapRingEquiv_algebraMap_const σ),
      Place.equivOfRingEquiv_mapRingEquiv_mem_zeroOneInfty_iff]

end Conjugate

end TauCeti
