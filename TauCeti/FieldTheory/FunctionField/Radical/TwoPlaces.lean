/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import TauCeti.FieldTheory.FunctionField.Different.Tame
public import TauCeti.FieldTheory.FunctionField.Divisor.Principal
public import TauCeti.FieldTheory.FunctionField.Place.RatFunc.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.Genus
import TauCeti.FieldTheory.FunctionField.Consequences.HighDegree
import TauCeti.FieldTheory.FunctionField.Different.Hurwitz
import TauCeti.FieldTheory.FunctionField.Divisor.Conorm
import TauCeti.FieldTheory.FunctionField.Divisor.RatFunc
import TauCeti.FieldTheory.FunctionField.Place.ConstantField
import TauCeti.FieldTheory.FunctionField.Place.Extension.Degree
import TauCeti.FieldTheory.FunctionField.RiemannRoch.DegreeZero
import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc

/-!
# Tame extensions of genus-zero function fields ramified over two rational places

Let `F / K` be an algebraic function field of genus zero, and let `P₁ ≠ P₂` be two distinct places
of degree one. Let `L / F` be a finite separable extension in which `K` remains the exact constant
field (`IsIntegrallyClosedIn K L`), tamely ramified everywhere and unramified outside `{P₁, P₂}`.

By the Hurwitz genus formula (`TauCeti.hurwitz_genus_formula_geometricDegree`), because every place
is tame the different divisor equals the tame different
`∑_{P'} (e(P' ∣ P) - 1) · P'`, supported above `P₁` and `P₂`. For each `P ∈ {P₁, P₂}`, `deg P = 1`
so `deg P' = f(P' ∣ P)`, and the fundamental inequality `∑_{P' ∣ P} e(P' ∣ P) f(P' ∣ P) ≤ [L : F]`
yields `∑_{P' ∣ P} (e(P' ∣ P) - 1) deg P' ≤ [L : F] - ∑_{P' ∣ P} f(P' ∣ P) ≤ [L : F] - 1`.
Substituting into `2g(L) - 2 = -2 [L : F] + deg Diff(L / F)` forces equality throughout:
`g(L) = 0`, and there are unique places `Q₁ ∣ P₁` and `Q₂ ∣ P₂`, both of degree one and
ramification index `[L : F]`
(`TauCeti.genus_eq_zero_and_unique_places_of_unramified_outside_pair`).

Given any unit `x ∈ Fˣ` with divisor `P₁ - P₂` (for instance `x = RatFunc.X` on `F = RatFunc K`
with `P₁ = 0` and `P₂ = ∞`), Riemann–Roch on the degree-zero divisor `Q₁ - Q₂` of the genus-zero
field `L` shows `ℓ(Q₁ - Q₂) = 1`, so `Q₁ - Q₂` is principal by
`TauCeti.Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero`, producing a unit `z ∈ Lˣ`
with `(z) = Q₁ - Q₂`. When `Q₁` and `Q₂` both have ramification index `n`, `z ^ n` and `x` share
the principal divisor `n(Q₁ - Q₂) = Con(P₁ - P₂)` in `L`, so they differ by a constant `c ∈ Kˣ`
(`TauCeti.exists_pow_eq_mul_of_genus_zero_unique_places`, via
`TauCeti.Divisor.exists_units_algebraMap_mul_of_principal_eq`). Over an algebraically closed field
`K`, rescaling `z` by an `n`-th root of `c` in `K` produces `y ∈ L` with `y ^ n = x`
(`TauCeti.exists_pow_eq_of_genus_zero_unique_places`), specializing to
`y ^ [L : RatFunc K] = RatFunc.X` for tame extensions of `RatFunc K` unramified outside `0` and
`∞` (`TauCeti.exists_pow_eq_X_of_unramified_outside_zero_infty`).

## Main results

* `TauCeti.genus_eq_zero_and_unique_places_of_unramified_outside_pair`: a tame finite separable
  extension of a genus-zero function field unramified outside two rational places has genus zero
  and unique totally ramified rational places above each of them.
* `TauCeti.exists_pow_eq_mul_of_genus_zero_unique_places`: in a genus-zero extension with unique
  rational places `Q₁ ∣ P₁`, `Q₂ ∣ P₂` of common ramification index `n`, any function `x ∈ Fˣ` with
  divisor `P₁ - P₂` satisfies `z ^ n = c · x` for some `z ∈ L` and `c ∈ Kˣ`.
* `TauCeti.exists_pow_eq_of_genus_zero_unique_places`: over an algebraically closed field `K`,
  rescaling yields `y ∈ L` with `y ^ n = x`.
* `TauCeti.exists_pow_eq_X_of_unramified_outside_zero_infty`: over an algebraically closed field
  `K`, every tame finite separable extension `L / RatFunc K` unramified outside `0` and `∞`
  contains an `[L : RatFunc K]`-th root of `RatFunc.X`.

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental (SGA 1)*, Exposé XIII, §2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Theorem 3.4.13 and Corollary 3.5.6.
* T. Szamuely, *Galois Groups and Fundamental Groups*, Example 4.6.12 (2).
-/

public section

open Polynomial

namespace TauCeti

open AlgebraicGeometry

section General

variable {K F L : Type*} [Field K] [Field F] [Field L]
variable [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
variable [FiniteDimensional F L]

/-- **Hurwitz constraint for tame covers unramified outside two rational places.** Let `F / K` be
a genus-zero function field with two distinct degree-one places `P₁ ≠ P₂`. Any finite separable
extension `L / F` with exact constant field `K`, tamely ramified everywhere and unramified outside
`{P₁, P₂}`, has genus zero and unique totally ramified places `Q₁ ∣ P₁` and `Q₂ ∣ P₂`, both of
degree one. -/
theorem genus_eq_zero_and_unique_places_of_unramified_outside_pair
    [Algebra.IsSeparable F L] (hF : IsFunctionField K F) (hexL : IsIntegrallyClosedIn K L)
    (hgF : genus K F = 0) {P₁ P₂ : Place K F} (hne : P₁ ≠ P₂)
    (hP₁ : P₁.degree = 1) (hP₂ : P₂.degree = 1)
    (htame : ∀ P' : Place K L, Place.IsTame K F P')
    (hunram : ∀ P' : Place K L,
      P'.restrict K F ≠ P₁ → P'.restrict K F ≠ P₂ → Place.ramificationIdx F P' = 1) :
    genus K L = 0 ∧
      ∃ Q₁ Q₂ : Place K L,
        (∀ Q : Place K L, Q.restrict K F = P₁ ↔ Q = Q₁) ∧
        (∀ Q : Place K L, Q.restrict K F = P₂ ↔ Q = Q₂) ∧
        Place.ramificationIdx F Q₁ = Module.finrank F L ∧
        Place.ramificationIdx F Q₂ = Module.finrank F L ∧
        Q₁.degree = 1 ∧ Q₂.degree = 1 := by
  classical
  have hL : IsFunctionField K L := hF.finite_extension
  have hexF : IsIntegrallyClosedIn K F := P₁.isIntegrallyClosedIn_of_degree_eq_one hP₁
  obtain ⟨Q₁₀, hQ₁₀⟩ := Place.restrict_surjective_of_finiteDimensional hF hL P₁
  obtain ⟨Q₂₀, hQ₂₀⟩ := Place.restrict_surjective_of_finiteDimensional hF hL P₂
  set n : ℕ := Module.finrank F L
  let S₁ : Finset (Place K L) := (Place.finite_setOf_restrict_eq K F P₁).toFinset
  let S₂ : Finset (Place K L) := (Place.finite_setOf_restrict_eq K F P₂).toFinset
  have hmemS₁ : ∀ P', P' ∈ S₁ ↔ P'.restrict K F = P₁ := fun _ ↦ Set.Finite.mem_toFinset _
  have hmemS₂ : ∀ P', P' ∈ S₂ ↔ P'.restrict K F = P₂ := fun _ ↦ Set.Finite.mem_toFinset _
  have hdisj : Disjoint S₁ S₂ := Finset.disjoint_left.mpr fun P' h1 h2 ↦
    hne (((hmemS₁ P').mp h1).symm.trans ((hmemS₂ P').mp h2))
  -- For `P ∈ {P₁, P₂}` of degree one, each fibre sum satisfies `∑ e · f ≤ n` and `∑ f ≥ card ≥ 1`.
  have hf_sum_ge (S : Finset (Place K L)) (hS : S.Nonempty) :
      S.card ≤ ∑ P' ∈ S, Place.relativeDegree K F P' ∧ 1 ≤ S.card :=
    ⟨by simpa using Finset.sum_le_sum fun P' (_ : P' ∈ S) ↦ Place.one_le_relativeDegree K F P',
      Finset.card_pos.mpr hS⟩
  obtain ⟨hf₁_ge, hcard₁⟩ := hf_sum_ge S₁ ⟨Q₁₀, (hmemS₁ Q₁₀).mpr hQ₁₀⟩
  obtain ⟨hf₂_ge, hcard₂⟩ := hf_sum_ge S₂ ⟨Q₂₀, (hmemS₂ Q₂₀).mpr hQ₂₀⟩
  have hef₁ : ∑ P' ∈ S₁, Place.ramificationIdx F P' * Place.relativeDegree K F P' ≤ n :=
    Place.sum_ramificationIdx_mul_relativeDegree_le_finrank K F P₁ S₁ fun P' h ↦ (hmemS₁ P').mp h
  have hef₂ : ∑ P' ∈ S₂, Place.ramificationIdx F P' * Place.relativeDegree K F P' ≤ n :=
    Place.sum_ramificationIdx_mul_relativeDegree_le_finrank K F P₂ S₂ fun P' h ↦ (hmemS₂ P').mp h
  let Ddiff := Divisor.tameDifferent K L hF
  have hco : ∀ P' : Place K L, Ddiff P' = (Place.ramificationIdx F P' : ℤ) - 1 :=
    fun P' ↦ Divisor.coeff_tameDifferent K L hF P'
  have hsupp : Ddiff.support ⊆ S₁ ∪ S₂ := fun P' hP' ↦ by
    rw [Finset.mem_union, hmemS₁, hmemS₂]
    by_contra! hne'
    exact Finsupp.mem_support_iff.mp hP' (by rw [hco, hunram P' hne'.1 hne'.2]; norm_num)
  have hfibre_sum (P : Place K F) (hP : P.degree = 1) (S : Finset (Place K L))
      (hS : ∀ P' ∈ S, P'.restrict K F = P) :
      ∑ P' ∈ S, Ddiff P' * (P'.degree : ℤ) =
        ((∑ P' ∈ S, Place.ramificationIdx F P' * Place.relativeDegree K F P' : ℕ) : ℤ) -
          (∑ P' ∈ S, Place.relativeDegree K F P' : ℕ) := by
    have hterm : ∀ P' ∈ S, Ddiff P' * (P'.degree : ℤ) =
        (Place.ramificationIdx F P' * Place.relativeDegree K F P' : ℕ) -
          (Place.relativeDegree K F P' : ℕ) := fun P' hP' ↦ by
      have hdeg : P'.degree = Place.relativeDegree K F P' := by
        rw [Place.degree_eq_degree_restrict_mul_relativeDegree K F P', hS P' hP', hP, one_mul]
      rw [hco, hdeg]
      push_cast
      ring
    rw [Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Nat.cast_sum, Nat.cast_sum]
  have hdeg_diff : Divisor.degree Ddiff =
      (((∑ P' ∈ S₁, Place.ramificationIdx F P' * Place.relativeDegree K F P' : ℕ) : ℤ) -
        (∑ P' ∈ S₁, Place.relativeDegree K F P' : ℕ)) +
      (((∑ P' ∈ S₂, Place.ramificationIdx F P' * Place.relativeDegree K F P' : ℕ) : ℤ) -
        (∑ P' ∈ S₂, Place.relativeDegree K F P' : ℕ)) := by
    rw [Divisor.degree_eq_sum_support,
      Finset.sum_subset hsupp (fun _ _ hnot ↦ by simp [Finsupp.notMem_support_iff.mp hnot]),
      Finset.sum_union hdisj,
      hfibre_sum P₁ hP₁ S₁ fun P' h ↦ (hmemS₁ P').mp h,
      hfibre_sum P₂ hP₂ S₂ fun P' h ↦ (hmemS₂ P').mp h]
  have hhurwitz : 2 * (genus K L : ℤ) - 2 = -2 * (n : ℤ) + Divisor.degree Ddiff := by
    have htd : Ddiff = Divisor.different K L hF :=
      (Divisor.tameDifferent_eq_different_iff K L hF).mpr htame
    have hg := hurwitz_genus_formula_geometricDegree hF hL hexF hexL
    rw [geometricDegree_eq_finrank, hgF, ← htd, Nat.cast_zero, mul_zero, zero_sub] at hg
    dsimp only [n]
    linarith
  have hcard₁_eq : S₁.card = 1 := by omega
  have hcard₂_eq : S₂.card = 1 := by omega
  obtain ⟨Q₁, hS₁_eq⟩ := Finset.card_eq_one.mp hcard₁_eq
  obtain ⟨Q₂, hS₂_eq⟩ := Finset.card_eq_one.mp hcard₂_eq
  have hf₁_eq : Place.relativeDegree K F Q₁ = 1 := by
    have : ∑ P' ∈ S₁, Place.relativeDegree K F P' = 1 := by omega
    simpa [hS₁_eq] using this
  have hf₂_eq : Place.relativeDegree K F Q₂ = 1 := by
    have : ∑ P' ∈ S₂, Place.relativeDegree K F P' = 1 := by omega
    simpa [hS₂_eq] using this
  have hef₁_eq : Place.ramificationIdx F Q₁ * Place.relativeDegree K F Q₁ = n := by
    have : ∑ P' ∈ S₁, Place.ramificationIdx F P' * Place.relativeDegree K F P' = n := by omega
    simpa [hS₁_eq] using this
  have hef₂_eq : Place.ramificationIdx F Q₂ * Place.relativeDegree K F Q₂ = n := by
    have : ∑ P' ∈ S₂, Place.ramificationIdx F P' * Place.relativeDegree K F P' = n := by omega
    simpa [hS₂_eq] using this
  refine ⟨by omega, Q₁, Q₂,
    fun Q ↦ by rw [← hmemS₁, hS₁_eq, Finset.mem_singleton],
    fun Q ↦ by rw [← hmemS₂, hS₂_eq, Finset.mem_singleton],
    by simpa [hf₁_eq] using hef₁_eq,
    by simpa [hf₂_eq] using hef₂_eq, ?_, ?_⟩
  · rw [Place.degree_eq_degree_restrict_mul_relativeDegree K F Q₁,
      (hmemS₁ Q₁).mp (hS₁_eq ▸ Finset.mem_singleton_self Q₁), hP₁, hf₁_eq, mul_one]
  · rw [Place.degree_eq_degree_restrict_mul_relativeDegree K F Q₂,
      (hmemS₂ Q₂).mp (hS₂_eq ▸ Finset.mem_singleton_self Q₂), hP₂, hf₂_eq, mul_one]

/-- **Riemann–Roch extraction of a radical generator up to a constant.** Given a genus-zero
extension `L / F` with unique degree-one places `Q₁ ∣ P₁` and `Q₂ ∣ P₂` of common ramification
index `n`, and a unit `x ∈ Fˣ` with divisor `P₁ - P₂`, the degree-zero divisor `Q₁ - Q₂` has
Riemann–Roch dimension one, hence is principal (`(z) = Q₁ - Q₂` for some `z ∈ Lˣ`). Then `z ^ n`
and `algebraMap F L x` share the principal divisor `n(Q₁ - Q₂) = Con(P₁ - P₂)`, so `z ^ n = c · x`
for some constant `c ∈ Kˣ`. -/
theorem exists_pow_eq_mul_of_genus_zero_unique_places
    (hF : IsFunctionField K F) (hgenus : genus K L = 0)
    {P₁ P₂ : Place K F} {x : Fˣ}
    (hx : Divisor.principal hF x = WeilDivisor.ofPoint P₁ - WeilDivisor.ofPoint P₂)
    {Q₁ Q₂ : Place K L} {n : ℕ}
    (hQ₁ : ∀ Q : Place K L, Q.restrict K F = P₁ ↔ Q = Q₁)
    (hQ₂ : ∀ Q : Place K L, Q.restrict K F = P₂ ↔ Q = Q₂)
    (hQ₁_ram : Place.ramificationIdx F Q₁ = n) (hQ₂_ram : Place.ramificationIdx F Q₂ = n)
    (hQ₁_deg : Q₁.degree = 1) (hQ₂_deg : Q₂.degree = 1) :
    ∃ (z : L) (c : Kˣ), z ^ n = algebraMap K L c * algebraMap F L x := by
  have hL : IsFunctionField K L := hF.finite_extension
  have hexL : IsIntegrallyClosedIn K L := Q₁.isIntegrallyClosedIn_of_degree_eq_one hQ₁_deg
  let D : Divisor K L := WeilDivisor.ofPoint Q₁ - WeilDivisor.ofPoint Q₂
  have hdegD : Divisor.degree D = 0 := by
    rw [Divisor.degree_sub, Divisor.degree_ofPoint, Divisor.degree_ofPoint, hQ₁_deg, hQ₂_deg,
      sub_self]
  have hdimD : (Divisor.dim D : ℤ) = 1 := by
    have := Divisor.dim_eq_degree_add_one_sub_genus_of_two_mul_genus_sub_one_le_degree hL hexL
      (D := D) (by rw [hgenus, hdegD]; norm_num)
    omega
  obtain ⟨z, hprin_z⟩ :=
    (Divisor.one_le_dim_iff_exists_principal_eq_of_degree_eq_zero hL hdegD).mp (by omega)
  have hconorm_ofPoint {P : Place K F} {Q₀ : Place K L}
      (hQ₀ : ∀ Q : Place K L, Q.restrict K F = P ↔ Q = Q₀) :
      Divisor.conorm K L (WeilDivisor.ofPoint P) =
        Place.ramificationIdx F Q₀ • WeilDivisor.ofPoint Q₀ := by
    refine WeilDivisor.ext fun Q ↦ ?_
    rw [Divisor.coeff_conorm, WeilDivisor.coeff_nsmul]
    rcases eq_or_ne Q Q₀ with rfl | hne
    · simp [(hQ₀ Q).mpr rfl]
    · simp [WeilDivisor.coeff_ofPoint_of_ne hne,
        WeilDivisor.coeff_ofPoint_of_ne (mt (hQ₀ Q).mp hne)]
  have hdiv_eq : Divisor.principal hL (z ^ n) =
      Divisor.principal hL (Units.map (algebraMap F L : F →* L) x) := by
    rw [← zpow_natCast z n, Divisor.principal_zpow, natCast_zsmul, hprin_z,
      ← Divisor.conorm_principal K L hF hL x, hx, map_sub,
      hconorm_ofPoint hQ₁, hconorm_ofPoint hQ₂, hQ₁_ram, hQ₂_ram, smul_sub]
  obtain ⟨c, hc⟩ := Divisor.exists_units_algebraMap_mul_of_principal_eq hL hexL hdiv_eq
  exact ⟨z, c, by simpa using hc⟩

/-- **Riemann–Roch extraction of an exact `n`-th root over an algebraically closed field.**
Under the hypotheses of `exists_pow_eq_mul_of_genus_zero_unique_places`, if `K` is algebraically
closed then rescaling by an `n`-th root in `K` produces `y ∈ L` with `y ^ n = algebraMap F L x`. -/
theorem exists_pow_eq_of_genus_zero_unique_places [IsAlgClosed K]
    (hF : IsFunctionField K F) (hgenus : genus K L = 0)
    {P₁ P₂ : Place K F} {x : Fˣ}
    (hx : Divisor.principal hF x = WeilDivisor.ofPoint P₁ - WeilDivisor.ofPoint P₂)
    {Q₁ Q₂ : Place K L} {n : ℕ}
    (hQ₁ : ∀ Q : Place K L, Q.restrict K F = P₁ ↔ Q = Q₁)
    (hQ₂ : ∀ Q : Place K L, Q.restrict K F = P₂ ↔ Q = Q₂)
    (hQ₁_ram : Place.ramificationIdx F Q₁ = n) (hQ₂_ram : Place.ramificationIdx F Q₂ = n) :
    ∃ y : L, y ^ n = algebraMap F L x := by
  have hL : IsFunctionField K L := hF.finite_extension
  have hn_pos : 0 < n := hQ₁_ram ▸ Place.ramificationIdx_pos F Q₁
  obtain ⟨z, c, hzc⟩ := exists_pow_eq_mul_of_genus_zero_unique_places hF hgenus hx hQ₁ hQ₂
    hQ₁_ram hQ₂_ram (Q₁.degree_eq_one_of_isAlgClosed_of_isFunctionField hL)
    (Q₂.degree_eq_one_of_isAlgClosed_of_isFunctionField hL)
  obtain ⟨d, hdn⟩ := IsAlgClosed.exists_pow_nat_eq (c : K) hn_pos
  refine ⟨algebraMap K L d⁻¹ * z, ?_⟩
  rw [mul_pow, ← map_pow, inv_pow, hdn, hzc, ← mul_assoc, ← map_mul,
    inv_mul_cancel₀ c.ne_zero, map_one, one_mul]

end General

section RatFunc

variable {K L : Type*} [Field K] [IsAlgClosed K] [Field L] [Algebra K L]
variable [Algebra (RatFunc K) L] [IsScalarTower K (RatFunc K) L] [FiniteDimensional (RatFunc K) L]

/-- **Tame covers of `ℙ¹ \ {0, ∞}` are radical over an algebraically closed field.**
Every finite separable extension `L / RatFunc K` over an algebraically closed field `K` that is
tamely ramified everywhere and unramified outside `0` and `∞` contains an `[L : RatFunc K]`-th
root of `RatFunc.X`. -/
theorem exists_pow_eq_X_of_unramified_outside_zero_infty [Algebra.IsSeparable (RatFunc K) L]
    (htame : ∀ P' : Place K L, Place.IsTame K (RatFunc K) P')
    (hunram : ∀ P' : Place K L,
      P'.restrict K (RatFunc K) ≠ Place.adicOfIrreducible (irreducible_X (R := K)) →
      P'.restrict K (RatFunc K) ≠ Place.infty K → Place.ramificationIdx (RatFunc K) P' = 1) :
    ∃ y : L, y ^ Module.finrank (RatFunc K) L = algebraMap (RatFunc K) L RatFunc.X := by
  have hexL : IsIntegrallyClosedIn K L :=
    algebraicClosure_eq_bot_iff_isIntegrallyClosedIn.mp
      (IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure K L))
  obtain ⟨hgenus, Q₀, Qinf, hQ₀, hQinf, hQ₀_ram, hQinf_ram, -, -⟩ :=
    genus_eq_zero_and_unique_places_of_unramified_outside_pair (IsFunctionField.ratFunc K) hexL
      (genus_ratFunc K) (Place.adicOfIrreducible_ne_infty (irreducible_X (R := K)))
      (by simp) (Place.degree_infty (k := K)) htame hunram
  simpa using exists_pow_eq_of_genus_zero_unique_places (IsFunctionField.ratFunc K) hgenus
    (Divisor.principal_X (k := K)) hQ₀ hQinf hQ₀_ram hQinf_ram

end RatFunc

end TauCeti
