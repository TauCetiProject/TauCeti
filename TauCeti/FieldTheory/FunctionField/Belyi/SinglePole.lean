/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.FieldTheory.FunctionField.Belyi.Basic
public import TauCeti.FieldTheory.FunctionField.Consequences.FirstPoleNumber
public import TauCeti.FieldTheory.RatFunc.Map
import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree
import TauCeti.FieldTheory.FunctionField.Place.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
import TauCeti.FieldTheory.FunctionField.Place.Extension.Existence
import TauCeti.FieldTheory.FunctionField.Place.Extension.SinglePole

/-!
# A generator of a Belyi pair with a single pole

Let `F / k(t)` be an algebraic Belyi pair over a field `k` of characteristic zero, and let `P` be
a place of `F` lying over a place of `k(t)` other than `t = 0`, `t = 1` and `t = ∞`, with relative
degree one over it, as is the case for a place of degree one. Then `P` is unramified over `k(t)`,
so every `z ∈ F` whose only pole is `P` generates `F` over `k(t)`: `F = k(t, z)`
(`TauCeti.Place.adjoin_simple_eq_top_of_forall_ne_ord_nonneg`). Such functions exist, by
Riemann–Roch: for `n ≥ 2g`, where `g` is the genus of `F`, some function has a pole of order
exactly `n` at `P` and no other pole.

Over an algebraically closed field `k`, such as `ℂ`, every place has degree one, and for every
`a ∈ k` other than `0` and `1` some place of `F` lies over `t = a`. Taking `a` rational, this is the
starting point of Köck's proof that every Belyi pair over `ℂ` is defined over a number field: the
pair is presented as `k(t)[Z] / (μ)` for the minimal polynomial `μ` of such a `z`, and `z` is then
normalized so that automorphisms of `ℂ` fixing the isomorphism class of the pair fix `μ`.

The normalization takes the pole order `m` of `z` at `P` to be the least positive pole number at
`P`. At a place `P` over `t = a` with `a ≠ 0, 1`, the function `t - a` is a uniformizer, because
`P` is unramified over `k(t)`. When `P` is rational, exactly one `z` with poles bounded by `m P`
has Laurent expansion `(t - a) ^ (-m) + ⋯` in `t - a` with constant coefficient `0`, and this `z`
generates `F` over `k(t)`.

The normalization makes `z` invariant. Let `σ` be an automorphism of `k` fixing `a`, for instance
any automorphism when `a` is rational, and let `τ` be a field automorphism of `F` acting on `k(t)`
by the coefficient map of `σ`: an isomorphism of the conjugate pair along `σ` with the pair itself.
If `τ` maps `P` to itself, then it fixes `t - a` and acts on Laurent coefficients at `P` by `σ`,
so it preserves the three conditions pinning `z`, and fixes `z`. Consequently the minimal
polynomial of `z` over `k(t)` is fixed by the coefficient map of `σ`. Over `ℂ`, the automorphisms
`σ` admitting such a `τ` form Köck's group `U(F, t, P)`, and this invariance is the step that
descends the pair to a finite extension of its field of moduli.

## Main results

* `TauCeti.IsAlgebraicBelyiPair.exists_ord_neg_and_adjoin_simple_eq_top`: at every unmarked
  place of relative degree one there is a function with a single pole there generating `F` over
  `k(t)`.
* `TauCeti.IsAlgebraicBelyiPair.exists_restrict_eq_and_adjoin_simple_eq_top`: over an
  algebraically closed field, for every `a ≠ 0, 1` there are a place `P` over `t = a` and a
  function with only pole `P` generating `F` over `k(t)`.
* `TauCeti.IsAlgebraicBelyiPair.ord_algebraMap_X_sub_C`: over an unmarked point `t = a`, the
  function `t - a` is a uniformizer.
* `TauCeti.IsAlgebraicBelyiPair.existsUnique_laurentCoeff_eq_one_and_adjoin_simple_eq_top`: the
  normalized generator with a pole of the first pole order at a rational place over `t = a`.
* `TauCeti.IsAlgebraicBelyiPair.apply_eq_self_of_laurentCoeff_eq_one_of_laurentCoeff_zero_eq_zero`:
  an isomorphism of a conjugate pair with the pair that fixes `P` fixes the normalized generator.
* `TauCeti.IsAlgebraicBelyiPair.map_minpoly_eq_of_laurentCoeff_eq_one_of_laurentCoeff_zero_eq_zero`:
  its minimal polynomial over `k(t)` is then fixed by the coefficient map.

## References

* B. Köck, *Belyi's theorem revisited*, Beiträge zur Algebra und Geometrie 45 (2004), 253–265,
  proof of (2.2) Theorem.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 1.6.6.
-/

public section

open scoped IntermediateField

namespace TauCeti

open AlgebraicGeometry

namespace IsAlgebraicBelyiPair

variable {k F : Type*} [Field k] [CharZero k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FiniteDimensional (RatFunc k) F]

/-- **A Belyi pair has a generator with a single pole at an unmarked place.** Let `F / k(t)` be
an algebraic Belyi pair and `P` a place of `F` with relative degree one over a place of `k(t)` other
than `t = 0`, `t = 1` and `t = ∞`, for instance a place of degree one. Then some `z ∈ F` has a pole
at `P`, no other pole, and generates `F` over `k(t)`. -/
theorem exists_ord_neg_and_adjoin_simple_eq_top (h : IsAlgebraicBelyiPair k F)
    {P : Place k F} (hP : P.restrict k (RatFunc k) ∉ Place.zeroOneInfty k)
    (hf : Place.relativeDegree k (RatFunc k) P = 1) :
    ∃ z : F, P.ord z < 0 ∧ (∀ P' : Place k F, P' ≠ P → 0 ≤ P'.ord z) ∧
      (RatFunc k)⟮z⟯ = ⊤ := by
  -- Riemann–Roch gives a function with a pole of order `2g + 1` at `P` and no other pole.
  obtain ⟨z, -, hz, hreg⟩ := P.exists_ord_eq_neg_and_forall_ne_ord_nonneg
    ((IsFunctionField.ratFunc k).finite_extension (E := F)) h.isIntegrallyClosedIn
    (n := 2 * genus k F + 1) (by omega)
  have hz : P.ord z < 0 := by rw [hz]; omega
  -- Over an unmarked place `P` is unramified, so `z` generates `F` over `k(t)`.
  exact ⟨z, hz, hreg, Place.adjoin_simple_eq_top_of_forall_ne_ord_nonneg
    (IsFunctionField.ratFunc k) (h.ramificationIdx_eq_one hP) hf hz hreg⟩

/-- **A Belyi pair over an algebraically closed field has a generator with a single pole over any
unmarked point.** If `k` is algebraically closed and `a ∈ k` is neither `0` nor `1`, then there
are a place `P` of `F` over `t = a` and a function `z ∈ F` with a pole at `P` and no other pole
which generates `F` over `k(t)`. -/
theorem exists_restrict_eq_and_adjoin_simple_eq_top [IsAlgClosed k]
    (h : IsAlgebraicBelyiPair k F) {a : k} (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) :
    ∃ (P : Place k F) (z : F),
      P.restrict k (RatFunc k) = Place.adicOfIrreducible (Polynomial.irreducible_X_sub_C a) ∧
        P.ord z < 0 ∧ (∀ P' : Place k F, P' ≠ P → 0 ≤ P'.ord z) ∧ (RatFunc k)⟮z⟯ = ⊤ := by
  have hF : IsFunctionField k F := (IsFunctionField.ratFunc k).finite_extension
  obtain ⟨P, hPa⟩ := Place.restrict_surjective_of_finiteDimensional (IsFunctionField.ratFunc k) hF
    (Place.adicOfIrreducible (Polynomial.irreducible_X_sub_C a))
  have hP : P.restrict k (RatFunc k) ∉ Place.zeroOneInfty k := by
    simp only at hPa
    simp [hPa, ha₀, ha₁]
  -- Every place of `F` has degree one, hence relative degree one over `k(t)`.
  have hf : Place.relativeDegree k (RatFunc k) P = 1 := by
    have h := Place.degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) P
    rw [P.degree_eq_one_of_isAlgClosed_of_isFunctionField hF] at h
    exact Nat.eq_one_of_mul_eq_one_left h.symm
  obtain ⟨z, hz⟩ := h.exists_ord_neg_and_adjoin_simple_eq_top hP hf
  exact ⟨P, z, hPa, hz⟩

/-- **`t - a` is a uniformizer over an unmarked point.** At a place `P` of an algebraic Belyi pair
lying over the place `t = a` of `k(t)`, where `a ≠ 0, 1`, the function `t - a` has order one,
since `P` is unramified over `k(t)`. -/
theorem ord_algebraMap_X_sub_C (h : IsAlgebraicBelyiPair k F) {a : k} (ha₀ : a ≠ 0)
    (ha₁ : a ≠ 1) {P : Place k F}
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (Polynomial.irreducible_X_sub_C a)) :
    P.ord (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a)) = 1 := by
  have hP : P.restrict k (RatFunc k) ∉ Place.zeroOneInfty k := by simp [hPa, ha₀, ha₁]
  rw [Place.ord_algebraMap_restrict k (RatFunc k) P, h.ramificationIdx_eq_one hP, hPa,
    Place.ord_adicOfIrreducible_X_sub_C_self, Nat.cast_one, mul_one]

/-- **The normalized generator of a Belyi pair.** Let `P` be a rational place of an algebraic
Belyi pair `F / k(t)` over the place `t = a`, where `a ≠ 0, 1`, and let `m` be the least positive
pole number at `P`. Then exactly one function `z` with poles bounded by `m P` has Laurent expansion
in the uniformizer `t - a` with coefficient `1` at `(t - a) ^ (-m)` and constant coefficient `0`,
and it generates `F` over `k(t)`. -/
theorem existsUnique_laurentCoeff_eq_one_and_adjoin_simple_eq_top (h : IsAlgebraicBelyiPair k F)
    {a : k} (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) {P : Place k F}
    (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (Polynomial.irreducible_X_sub_C a))
    (hP : P.degree = 1) {m : ℕ} (hm : 0 < m) (hpole : P.IsPoleNumber m)
    (hgap : ∀ n, 0 < n → n < m → P.IsGap n) :
    ∃! z, z ∈ riemannRochSpace ((m : ℤ) • WeilDivisor.ofPoint P) ∧
      P.laurentCoeff hP (h.ord_algebraMap_X_sub_C ha₀ ha₁ hPa) (-m) z = 1 ∧
      P.laurentCoeff hP (h.ord_algebraMap_X_sub_C ha₀ ha₁ hPa) 0 z = 0 ∧ (RatFunc k)⟮z⟯ = ⊤ := by
  have ht := h.ord_algebraMap_X_sub_C ha₀ ha₁ hPa
  obtain ⟨z, ⟨hzL, h1, h0⟩, huniq⟩ :=
    Place.existsUnique_laurentCoeff_eq_one_and_laurentCoeff_zero_eq_zero
      ((IsFunctionField.ratFunc k).finite_extension (E := F)) h.isIntegrallyClosedIn hP ht hm
      hpole hgap
  refine ⟨z, ⟨hzL, h1, h0, ?_⟩, fun w ⟨hw, hw1, hw0, _⟩ ↦ huniq w ⟨hw, hw1, hw0⟩⟩
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at h1
  obtain ⟨hzP, hreg⟩ := (mem_riemannRochSpace_zsmul_ofPoint_iff hz0).mp hzL
  -- The coefficient of `(t - a) ^ (-m)` is nonzero, so `z` has a pole of order exactly `m`.
  have hord : P.ord z < 0 :=
    (P.ord_le_of_laurentCoeff_ne_zero hP ht (h1 ▸ one_ne_zero)).trans_lt (by omega)
  have hunmarked : P.restrict k (RatFunc k) ∉ Place.zeroOneInfty k := by simp [hPa, ha₀, ha₁]
  -- A rational place over the rational place `t = a` has relative degree one.
  have hf : Place.relativeDegree k (RatFunc k) P = 1 := by
    have hdeg := Place.degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k) P
    rw [hP] at hdeg
    exact Nat.eq_one_of_mul_eq_one_left hdeg.symm
  exact Place.adjoin_simple_eq_top_of_forall_ne_ord_nonneg (IsFunctionField.ratFunc k)
    (h.ramificationIdx_eq_one hunmarked) hf hord hreg

section Invariance

variable (h : IsAlgebraicBelyiPair k F) {a : k} (ha₀ : a ≠ 0) (ha₁ : a ≠ 1) {P : Place k F}
  (hPa : P.restrict k (RatFunc k) = Place.adicOfIrreducible (Polynomial.irreducible_X_sub_C a))
  (hP : P.degree = 1) {m : ℕ} (hm : 0 < m) (hpole : P.IsPoleNumber m)
  (hgap : ∀ n, 0 < n → n < m → P.IsGap n) {σ : k ≃+* k} (hσa : σ a = a) {τ : F ≃+* F}
  (hτ : ∀ x, τ (algebraMap (RatFunc k) F x) =
    algebraMap (RatFunc k) F (RatFunc.mapRingEquiv σ x))
  (hτP : Place.equivOfRingEquiv σ τ (apply_algebraMap_eq_of_mapRingEquiv σ τ hτ) P = P)
  {z : F} (hz : z ∈ riemannRochSpace ((m : ℤ) • WeilDivisor.ofPoint P))
  (h₁ : P.laurentCoeff hP (h.ord_algebraMap_X_sub_C ha₀ ha₁ hPa) (-m) z = 1)
  (h₀ : P.laurentCoeff hP (h.ord_algebraMap_X_sub_C ha₀ ha₁ hPa) 0 z = 0)
include hm hpole hgap hσa hτP hz h₁ h₀

/-- **Isomorphisms of conjugate pairs fixing `P` fix the normalized generator.** Let `z` be the
normalized generator of an algebraic Belyi pair `F / k(t)` at a rational place `P` over `t = a`,
where `a ≠ 0, 1`
(`TauCeti.IsAlgebraicBelyiPair.existsUnique_laurentCoeff_eq_one_and_adjoin_simple_eq_top`). Let
`σ` be an automorphism of `k` fixing `a`, and `τ` an automorphism of the field `F` acting on
`k(t)` by the coefficient map of `σ`, that is, an isomorphism from the conjugate of the pair along
`σ` to the pair. If `τ` maps `P` to itself, then `τ z = z`. -/
theorem apply_eq_self_of_laurentCoeff_eq_one_of_laurentCoeff_zero_eq_zero : τ z = z := by
  have hτt : τ (algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a)) =
      algebraMap (RatFunc k) F (RatFunc.X - RatFunc.C a) := by
    rw [hτ, map_sub, RatFunc.mapRingEquiv_X, RatFunc.mapRingEquiv_C, hσa]
  exact Place.apply_eq_self_of_laurentCoeff_eq_one_of_laurentCoeff_zero_eq_zero
    ((IsFunctionField.ratFunc k).finite_extension (E := F)) h.isIntegrallyClosedIn hP _ hm hpole
    hgap σ τ _ hτP hτt hz h₁ h₀

/-- **The minimal polynomial of the normalized generator is invariant.** Under the hypotheses of
`TauCeti.IsAlgebraicBelyiPair.apply_eq_self_of_laurentCoeff_eq_one_of_laurentCoeff_zero_eq_zero`,
the coefficient map of `σ` fixes the minimal polynomial of the normalized generator `z` over
`k(t)`. -/
theorem map_minpoly_eq_of_laurentCoeff_eq_one_of_laurentCoeff_zero_eq_zero :
    (minpoly (RatFunc k) z).map (RatFunc.mapRingEquiv σ : RatFunc k →+* RatFunc k) =
      minpoly (RatFunc k) z := by
  rw [minpoly.map_eq_of_equiv_equiv (g := τ) (RingHom.ext fun x ↦ (hτ x).symm),
    h.apply_eq_self_of_laurentCoeff_eq_one_of_laurentCoeff_zero_eq_zero ha₀ ha₁ hPa hP hm hpole
      hgap hσa hτ hτP hz h₁ h₀]

end Invariance

end IsAlgebraicBelyiPair

end TauCeti
