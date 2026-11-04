/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Iterate
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Subst
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Units
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Analysis.Normed.Ring.Units

import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Digits.Lemmas


/-!
# Making a restricted series distinguished in one variable

Let `R` be an ultrametric normed commutative ring with `‖1‖ = 1`, and let `σ` be finite. Separating
the variable `Y = X none` identifies the unit-radius Tate algebra in the variables `Option σ` with
restricted power series in `Y` over the Tate algebra in the variables `σ`
(`MvPowerSeries.restrictedOptionEquiv`). A nonzero series need not be distinguished in `Y` in
this picture: its dominant coefficients may all involve the other variables. This file shows that
an isometric `R`-algebra automorphism of the Tate algebra repairs this. Every nonzero series is
carried to one which is distinguished in `Y`, and whose dominant `Y`-coefficient differs from a
constant of the same norm by less than that norm. Over a complete nonarchimedean field this
dominant coefficient is therefore a unit.

This is the input that Weierstrass division in `Y`, with coefficients in the Tate algebra in the
remaining variables, needs in order to prove that Tate algebras are noetherian.

The automorphism is the triangular substitution

```text
Y ↦ Y,    Xᵢ ↦ Xᵢ + Y ^ (b ^ (k i + 1)),
```

for an enumeration `k : σ ≃ Fin n` and a base `b` exceeding every exponent appearing in a monomial
of maximal coefficient norm. It sends the monomial `X ^ ν` to a polynomial which, as a polynomial in
`Y`, is monic of degree `ν none + ∑ᵢ b ^ (k i + 1) * ν (some i)`. These degrees are base-`b`
expansions, so they differ for the finitely many dominant monomials, and the dominant monomial of
largest degree gives the distinguished coefficient. Any larger base works as well, so a base
exceeding the exponents of the dominant monomials of finitely many nonzero series gives one
automorphism distinguishing all of them at once.

## Main results

* `TauCeti.MvPowerSeries.restrictedTriangularEquiv`: the triangular automorphism, an isometry
  (`TauCeti.MvPowerSeries.norm_restrictedTriangularEquiv`) given by the formal substitution of
  `TauCeti.MvPowerSeries.triangularFamily`.
* `TauCeti.MvPowerSeries.exists_restrictedTriangularEquiv_forall_isDistinguished`: over an
  ultrametric normed commutative ring, one triangular automorphism makes every member of a finite
  family of nonzero series distinguished in `Y`, with dominant coefficient close to a constant of
  the same norm; `TauCeti.MvPowerSeries.exists_restrictedTriangularEquiv_isDistinguished` is the
  case of a single series.
* `TauCeti.MvPowerSeries.exists_restrictedTriangularEquiv_forall_isDistinguished_isUnit` and
  `TauCeti.MvPowerSeries.exists_algEquiv_forall_isDistinguished_isUnit`, with their single-series
  cases `TauCeti.MvPowerSeries.exists_restrictedTriangularEquiv_isDistinguished_isUnit` and
  `TauCeti.MvPowerSeries.exists_algEquiv_isDistinguished_isUnit`: over a complete nonarchimedean
  field, the dominant coefficients are moreover units.
* `TauCeti.MvPowerSeries.isDistinguished_isUnit_of_norm_coeff_lt`: at any radii, a series over
  restricted series is distinguished with a unit coefficient when the constant term of that
  coefficient strictly dominates all other weighted coefficients.

## References

* Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*, §5.2.4.
* The choice of exponents `b ^ (k i + 1)` and the comparison of base-`b` expansions follow the
  proof of Mathlib's Noether normalization lemma, `Mathlib.RingTheory.NoetherNormalization`.
-/

public section

namespace TauCeti.MvPowerSeries

open _root_.MvPowerSeries Filter
open scoped Topology

variable {σ R : Type*} [NormedCommRing R] [IsUltrametricDist R] [NormOneClass R]

local notation "Tate" => IsRestricted.subring (R := R) (fun _ : σ ↦ 1)
local notation "ExtraTate" => IsRestricted.subring (R := R) (fun _ : Option σ ↦ 1)

/-- The triangular family `Y ↦ Y`, `Xᵢ ↦ Xᵢ + u * Y ^ α i`, where `Y` is the variable `none`. -/
noncomputable def triangularFamily (α : σ → ℕ) (u : R) :
    Option σ → MvPolynomial (Option σ) R :=
  fun x ↦ x.elim (MvPolynomial.X none) fun i ↦
    MvPolynomial.X (some i) + MvPolynomial.C u * MvPolynomial.X none ^ α i

omit [IsUltrametricDist R] [NormOneClass R] in
/-- The triangular family fixes the variable `Y = none`. -/
@[simp]
theorem triangularFamily_none (α : σ → ℕ) (u : R) :
    triangularFamily α u none = MvPolynomial.X none := by
  rw [triangularFamily, Option.elim_none]

omit [IsUltrametricDist R] [NormOneClass R] in
/-- The triangular family sends `Xᵢ` to `Xᵢ + u * Y ^ α i`. -/
@[simp]
theorem triangularFamily_some (α : σ → ℕ) (u : R) (i : σ) :
    triangularFamily α u (some i) =
      MvPolynomial.X (some i) + MvPolynomial.C u * MvPolynomial.X none ^ α i := by
  rw [triangularFamily, Option.elim_some]

omit [IsUltrametricDist R] [NormOneClass R] in
/-- For positive exponents the triangular polynomials have no constant term. -/
theorem constantCoeff_triangularFamily {α : σ → ℕ} (hα : ∀ i, α i ≠ 0) (u : R)
    (x : Option σ) : (triangularFamily α u x).constantCoeff = 0 := by
  cases x <;> simp [triangularFamily, hα]

/-- For `‖u‖ ≤ 1` the triangular polynomials have all coefficients of norm at most `1`. -/
theorem norm_coeff_triangularFamily_le {u : R} (hu : ‖u‖ ≤ 1) (α : σ → ℕ)
    (x : Option σ) (t : Option σ →₀ ℕ) : ‖(triangularFamily α u x).coeff t‖ ≤ 1 := by
  classical
  cases x with
  | none =>
    simp only [triangularFamily, Option.elim_none, MvPolynomial.coeff_X]
    split_ifs <;> simp
  | some i =>
    have h : (triangularFamily α u (some i)).coeff t =
        (MvPolynomial.X (some i) : MvPolynomial (Option σ) R).coeff t +
          u * (MvPolynomial.X none ^ α i : MvPolynomial (Option σ) R).coeff t := by
      simp [triangularFamily, MvPolynomial.coeff_C_mul]
    rw [h, MvPolynomial.coeff_X, MvPolynomial.coeff_X_pow]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_) <;>
      split_ifs <;> simp [hu]

omit [IsUltrametricDist R] [NormOneClass R] in
/-- The triangular families for `u` and `v = -u` are inverse to each other under substitution. -/
theorem aeval_triangularFamily (α : σ → ℕ) {u v : R} (huv : u + v = 0) (x : Option σ) :
    MvPolynomial.aeval (triangularFamily α u) (triangularFamily α v x) = MvPolynomial.X x := by
  cases x with
  | none => simp [triangularFamily]
  | some i =>
    simp only [triangularFamily, Option.elim_some, Option.elim_none, map_add, map_mul, map_pow,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
      eq_neg_of_add_eq_zero_right huv, map_neg]
    ring

/-- The triangular automorphism `Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i` of the Tate algebra in the
variables `Option σ`, for positive exponents `α`. -/
noncomputable def restrictedTriangularEquiv [Finite σ] (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) :
    ExtraTate ≃ₐ[R] ExtraTate :=
  restrictedSubstEquiv (triangularFamily α 1) (constantCoeff_triangularFamily hα 1)
    (norm_coeff_triangularFamily_le norm_one.le α) (triangularFamily α (-1))
    (constantCoeff_triangularFamily hα (-1))
    (norm_coeff_triangularFamily_le (by simp : ‖(-1 : R)‖ ≤ 1) α)
    (aeval_triangularFamily α (neg_add_cancel 1)) (aeval_triangularFamily α (add_neg_cancel 1))

/-- The triangular automorphism is the formal substitution of the triangular family. -/
@[simp]
theorem coe_restrictedTriangularEquiv [Finite σ] (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) (f : ExtraTate) :
    (restrictedTriangularEquiv α hα f : MvPowerSeries (Option σ) R) =
      (f : MvPowerSeries (Option σ) R).subst
        fun x ↦ (triangularFamily (R := R) α 1 x : MvPowerSeries (Option σ) R) :=
  coe_restrictedSubstEquiv ..

/-- The triangular automorphism preserves the Gauss norm. -/
@[simp]
theorem norm_restrictedTriangularEquiv [Finite σ] (α : σ → ℕ) (hα : ∀ i, α i ≠ 0)
    (f : ExtraTate) : ‖restrictedTriangularEquiv α hα f‖ = ‖f‖ :=
  norm_restrictedSubstEquiv ..

/-- The `Y`-degree `ν none + ∑ᵢ α i * ν (some i)` of the image of `X ^ ν` under the triangular
substitution. -/
private def triangularDegree (α : σ → ℕ) (ν : Option σ →₀ ℕ) : ℕ :=
  ν.sum fun x n ↦ x.elim 1 α * n

omit [IsUltrametricDist R] [NormOneClass R] in
/-- As a polynomial in `Y`, the image of `X ^ ν` under the triangular substitution is monic of
degree `triangularDegree α ν`. -/
private theorem isMonicOfDegree_optionEquivLeft_prod [Nontrivial R] {α : σ → ℕ}
    (hα : ∀ i, α i ≠ 0)
    (ν : Option σ →₀ ℕ) :
    (MvPolynomial.optionEquivLeft R σ (ν.prod fun x n ↦ triangularFamily α 1 x ^ n)).IsMonicOfDegree
      (triangularDegree α ν) := by
  classical
  have hx (x : Option σ) :
      (MvPolynomial.optionEquivLeft R σ (triangularFamily α 1 x)).IsMonicOfDegree
        (x.elim 1 α) := by
    cases x with
    | none =>
      simpa [triangularFamily, MvPolynomial.optionEquivLeft_X_none] using
        Polynomial.isMonicOfDegree_X (MvPolynomial σ R)
    | some i =>
      simp only [triangularFamily, Option.elim_some, map_add, map_pow,
        MvPolynomial.optionEquivLeft_X_some, MvPolynomial.optionEquivLeft_X_none,
        map_one, one_mul]
      rw [add_comm]
      exact (Polynomial.isMonicOfDegree_X_pow (MvPolynomial σ R) (α i)).add_right
        (by simpa using Nat.pos_of_ne_zero (hα i))
  simp only [Finsupp.prod, map_prod, map_pow, triangularDegree, Finsupp.sum]
  induction ν.support using Finset.induction_on with
  | empty => simp
  | insert x s hxs ih =>
    rw [Finset.prod_insert hxs, Finset.sum_insert hxs]
    exact ((hx x).pow _).mul ih

omit [IsUltrametricDist R] [NormOneClass R] in
open scoped Classical in
/-- The coefficients of the image of `X ^ ν` under the triangular substitution in `Y`-degrees at
least `triangularDegree α ν`: the only nonzero one is the leading coefficient `1` of `Y ^ N`. -/
private theorem coeff_optionElim_prod_triangularFamily [Nontrivial R] {α : σ → ℕ}
    (hα : ∀ i, α i ≠ 0)
    (ν : Option σ →₀ ℕ) (t : σ →₀ ℕ) {m : ℕ} (hm : triangularDegree α ν ≤ m) :
    (ν.prod fun x n ↦ triangularFamily (R := R) α 1 x ^ n).coeff (t.optionElim m) =
      if m = triangularDegree α ν ∧ t = 0 then 1 else 0 := by
  classical
  have hP := isMonicOfDegree_optionEquivLeft_prod (R := R) hα ν
  rw [← MvPolynomial.optionEquivLeft_coeff_some_coeff_none, Finsupp.optionElim_apply_none,
    Finsupp.some_optionElim]
  rcases hm.eq_or_lt with rfl | h
  · rw [← hP.natDegree_eq, hP.monic.coeff_natDegree, MvPolynomial.coeff_one]
    simp [eq_comm]
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.natDegree_eq ▸ h)]
    simp [h.ne']

open scoped Classical in
/-- **The coefficient estimate behind the distinguishing automorphism.** Suppose that every
exponent `d ≠ ν` whose triangular degree is at least that of `ν` has a coefficient of norm at most
`ε`. Then in every `Y`-degree `m` at least the triangular degree of `ν`, the coefficients of the
image of `f` are within `ε` of those of `coeff ν f * Y ^ m`. -/
private theorem norm_coeff_restrictedTriangularEquiv_sub_le [Finite σ] [Nontrivial R] {α : σ → ℕ}
    (hα : ∀ i, α i ≠ 0)
    (f : ExtraTate) (ν : Option σ →₀ ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hν : ∀ d ≠ ν, triangularDegree α ν ≤ triangularDegree α d →
      ‖coeff d (f : MvPowerSeries (Option σ) R)‖ ≤ ε)
    (t : σ →₀ ℕ) {m : ℕ} (hm : triangularDegree α ν ≤ m) :
    ‖coeff (t.optionElim m) (restrictedTriangularEquiv α hα f : MvPowerSeries (Option σ) R) -
      if m = triangularDegree α ν ∧ t = 0 then coeff ν (f : MvPowerSeries (Option σ) R)
        else 0‖ ≤ ε := by
  have h := norm_coeff_subst_coe_sub_le (constantCoeff_triangularFamily hα 1)
    (norm_coeff_triangularFamily_le (by simp) α) (f : MvPowerSeries (Option σ) R) ν
    (t.optionElim m) hε fun d hd hcoeff ↦ hν d hd <| by
      by_contra hlt
      push Not at hlt
      apply hcoeff
      rw [coeff_optionElim_prod_triangularFamily hα d t (hlt.le.trans hm)]
      simp [(hlt.trans_le hm).ne']
  rw [coeff_optionElim_prod_triangularFamily hα ν t hm, mul_ite, mul_one, mul_zero] at h
  simpa using h

omit [IsUltrametricDist R] [NormOneClass R] in
/-- With the exponents `α i = b ^ (k i + 1)`, the triangular degree is a base-`b` expansion, so it
separates exponents whose entries are all below `b`. -/
private theorem triangularDegree_injective {n : ℕ} (k : σ ≃ Fin n) {b : ℕ}
    (hb : 1 < b) {ν ν' : Option σ →₀ ℕ} (hν : ∀ x, ν x < b) (hν' : ∀ x, ν' x < b)
    (h : triangularDegree (fun i ↦ b ^ ((k i : ℕ) + 1)) ν =
      triangularDegree (fun i ↦ b ^ ((k i : ℕ) + 1)) ν') :
    ν = ν' := by
  have : Fintype σ := Fintype.ofEquiv _ k.symm
  let E : Option σ ≃ Fin (n + 1) := (Equiv.optionCongr k).trans (finSuccEquiv n).symm
  have hE (μ : Option σ →₀ ℕ) : triangularDegree (fun i ↦ b ^ ((k i : ℕ) + 1)) μ =
      ∑ j : Fin (n + 1), b ^ (j : ℕ) * μ (E.symm j) := by
    rw [triangularDegree, Finsupp.sum_fintype _ _ (by simp)]
    refine Fintype.sum_equiv E _ (fun j ↦ b ^ (j : ℕ) * μ (E.symm j)) fun x ↦ ?_
    rw [E.symm_apply_apply]
    cases x <;> simp [E]
  -- Base-`b` expansions with digits below `b` are unique.
  have hdigits {m : ℕ} {v w : Fin m → ℕ} (hv : ∀ j, v j < b) (hw : ∀ j, w j < b)
      (h : ∑ j : Fin m, b ^ (j : ℕ) * v j = ∑ j : Fin m, b ^ (j : ℕ) * w j) : v = w := by
    refine List.ofFn_injective (Nat.ofDigits_inj_of_len_eq hb (by simp) (by simpa using hv)
      (by simpa using hw) ?_)
    simpa [Nat.ofDigits_eq_sum_mapIdx, List.mapIdx_eq_ofFn, List.sum_ofFn, mul_comm] using h
  have hv := hdigits (fun j ↦ hν _) (fun j ↦ hν' _) ((hE ν).symm.trans (h.trans (hE ν')))
  ext x
  simpa using congrFun hv (E x)

omit [NormOneClass R] in
/-- **Choice of the triangular exponents.** Let `f` be a nonzero restricted series, `S` the finite
set of its exponents of maximal coefficient norm, and `b > 1` a base exceeding every entry of each
exponent in `S`. For the exponents `α i = b ^ (k i + 1)` there are an exponent `ν` with
`‖coeff ν f‖ = ‖f‖` and some `ε < ‖f‖` such that every other exponent of triangular degree at
least that of `ν` carries a coefficient of norm at most `ε`. -/
private theorem exists_triangularDegree_dominant (f : ExtraTate) (hf : f ≠ 0)
    (S : Finset (Option σ →₀ ℕ))
    (hS : ∀ d, d ∈ S ↔ ‖f‖ ≤ ‖coeff d (f : MvPowerSeries (Option σ) R)‖)
    {n : ℕ} (k : σ ≃ Fin n) {b : ℕ} (hb : 1 < b) (hbS : ∀ d ∈ S, ∀ x, d x < b) :
    ∃ (ν : Option σ →₀ ℕ) (ε : ℝ), 0 ≤ ε ∧ ε < ‖f‖ ∧
      ‖coeff ν (f : MvPowerSeries (Option σ) R)‖ = ‖f‖ ∧
      ∀ d ≠ ν, triangularDegree (fun i ↦ b ^ ((k i : ℕ) + 1)) ν ≤
          triangularDegree (fun i ↦ b ^ ((k i : ℕ) + 1)) d →
        ‖coeff d (f : MvPowerSeries (Option σ) R)‖ ≤ ε := by
  classical
  obtain ⟨d₀, hd₀⟩ := exists_achievesGaussNorm f
  obtain ⟨ε, hε0, hεM, hε⟩ := exists_norm_coeff_mul_prod_gap f hf
  simp only [AchievesGaussNorm, ← norm_eq_gaussNorm, one_pow, Finsupp.prod_fun_one,
    mul_one] at hd₀ hε
  have hle (d) : ‖coeff d (f : MvPowerSeries (Option σ) R)‖ ≤ ‖f‖ := by
    simpa using norm_coeff_mul_prod_le f d
  -- The dominant exponent of largest triangular degree.
  obtain ⟨ν, hνS, hνmax⟩ := S.exists_max_image
    (triangularDegree fun i ↦ b ^ ((k i : ℕ) + 1)) ⟨d₀, (hS d₀).mpr hd₀.ge⟩
  refine ⟨ν, ε, hε0, hεM, le_antisymm (hle ν) ((hS ν).mp hνS), fun d hd hdeg ↦ ?_⟩
  by_cases hdS : d ∈ S
  · exact absurd (triangularDegree_injective k hb (hbS d hdS) (hbS ν hνS)
      (le_antisymm (hνmax d hdS) hdeg)) hd
  · exact hε d (lt_of_not_ge fun h ↦ hdS ((hS d).mpr h))

/-- If a coefficient `a = coeff ν f` of norm `‖f‖` dominates, up to `ε < ‖f‖`, every coefficient
of triangular degree at least that of `ν`, then the triangular automorphism makes `f`
distinguished in `Y`, with dominant coefficient within less than `‖f‖` of the constant `a`. -/
private theorem exists_isDistinguished_of_triangularDegree_dominant [Finite σ] {α : σ → ℕ}
    (hα : ∀ i, α i ≠ 0) (f : ExtraTate) (ν : Option σ →₀ ℕ) {ε : ℝ}
    (hε0 : 0 ≤ ε) (hεM : ε < ‖f‖) (hνM : ‖coeff ν (f : MvPowerSeries (Option σ) R)‖ = ‖f‖)
    (hν : ∀ d ≠ ν, triangularDegree α ν ≤ triangularDegree α d →
      ‖coeff d (f : MvPowerSeries (Option σ) R)‖ ≤ ε) :
    ∃ (s : ℕ) (a : R), ‖a‖ = ‖f‖ ∧
      PowerSeries.IsDistinguished 1 s
        (restrictedOptionEquiv (restrictedTriangularEquiv α hα f) : PowerSeries Tate) ∧
      ‖PowerSeries.coeff s
          (restrictedOptionEquiv (restrictedTriangularEquiv α hα f) : PowerSeries Tate) -
        algebraMap R Tate a‖ < ‖f‖ := by
  classical
  have : Nontrivial R := nontrivial_of_ne (coeff ν (f : MvPowerSeries (Option σ) R)) 0
    fun h ↦ (hε0.trans_lt hεM).ne' (by rw [← hνM, h, norm_zero])
  set a := coeff ν (f : MvPowerSeries (Option σ) R)
  set s := triangularDegree α ν
  set G := restrictedOptionEquiv (restrictedTriangularEquiv α hα f)
  have hG : ‖G‖ = ‖f‖ := by rw [norm_restrictedOptionEquiv, norm_restrictedTriangularEquiv]
  have hGn : (G : PowerSeries Tate).gaussNorm norm 1 = ‖f‖ := by
    rw [← TauCeti.PowerSeries.norm_eq_gaussNorm, hG]
  have hcoeffG (m : ℕ) (t : σ →₀ ℕ) :
      coeff t (PowerSeries.coeff (R := Tate) m (G : PowerSeries Tate) : MvPowerSeries σ R) =
        coeff (t.optionElim m) (restrictedTriangularEquiv α hα f : MvPowerSeries (Option σ) R) := by
    rw [coeff_restrictedOptionEquiv (c := fun _ ↦ 1), coeff_coeff_optionEquivLeft]
  have hcore := norm_coeff_restrictedTriangularEquiv_sub_le hα f ν hε0 hν
  -- Past degree `s` every coefficient has norm at most `ε`.
  have hbeyond (m : ℕ) (hm : s < m) : ‖PowerSeries.coeff m (G : PowerSeries Tate)‖ ≤ ε := by
    rw [norm_le_iff hε0]
    intro t
    have h := hcore t hm.le
    rw [ite_eq_right fun h ↦ hm.ne' h.1, sub_zero, ← hcoeffG] at h
    simpa using h
  -- In degree `s` the coefficient is within `ε` of the constant `a`.
  have hat : ‖PowerSeries.coeff s (G : PowerSeries Tate) - algebraMap R Tate a‖ ≤ ε := by
    rw [norm_le_iff hε0]
    intro t
    have h := hcore t le_rfl
    rw [← hcoeffG] at h
    simpa [coeff_C, ite_and, a, s] using h
  have hCa : ‖algebraMap R Tate a‖ = ‖f‖ := by
    have h : algebraMap R Tate a = ⟨C a, isRestricted_C _ _⟩ :=
      Subtype.ext (coe_algebraMap_isRestrictedSubring _)
    rw [h, norm_C, hνM]
  refine ⟨s, a, hνM,
    PowerSeries.isDistinguished_of_norm_coeff_sub_lt zero_le_one
      (by rw [one_pow, mul_one, hGn, hCa])
      (by rw [one_pow, mul_one, hGn]; exact hat.trans_lt hεM)
      (fun m hm ↦ by rw [one_pow, mul_one, hGn]; exact (hbeyond m hm).trans_lt hεM),
    hat.trans_lt hεM⟩

/-- **Distinguishing automorphisms of Tate algebras, for finitely many series at once.** Over an
ultrametric normed commutative ring with `‖1‖ = 1`, for finite `σ` and a finite family `f` of
nonzero unit-radius restricted series in the variables `Option σ`, a single triangular
automorphism `Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i` carries every member of the family to a series
distinguished in the variable `Y = none`: written as a restricted series in `Y` over the Tate
algebra in the variables `σ`, the image of `f j` is distinguished of some degree `s`, and its
coefficient in degree `s` is within less than `‖f j‖` of a constant `a` with `‖a‖ = ‖f j‖`. -/
theorem exists_restrictedTriangularEquiv_forall_isDistinguished [Finite σ] {ι : Type*} [Finite ι]
    (f : ι → ExtraTate) (hf : ∀ j, f j ≠ 0) :
    ∃ (α : σ → ℕ) (hα : ∀ i, α i ≠ 0), ∀ j, ∃ (s : ℕ) (a : R), ‖a‖ = ‖f j‖ ∧
      PowerSeries.IsDistinguished 1 s
        (restrictedOptionEquiv (restrictedTriangularEquiv α hα (f j)) : PowerSeries Tate) ∧
      ‖PowerSeries.coeff s
          (restrictedOptionEquiv (restrictedTriangularEquiv α hα (f j)) : PowerSeries Tate) -
        algebraMap R Tate a‖ < ‖f j‖ := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  have : Fintype ι := Fintype.ofFinite ι
  -- The exponents of maximal coefficient norm of each member form a finite set `S j`.
  have hSfin (j : ι) : {d | ‖f j‖ ≤ ‖coeff d (f j : MvPowerSeries (Option σ) R)‖}.Finite := by
    have hM : 0 < ‖f j‖ := norm_pos_iff.mpr (hf j)
    have := (isRestricted_one_iff.mp (f j).2).eventually (gt_mem_nhds (half_pos hM))
    exact (by simpa [eventually_cofinite, not_lt] using this :
      {d | ‖f j‖ / 2 ≤ ‖coeff d (f j : MvPowerSeries (Option σ) R)‖}.Finite).subset
        fun d hd ↦ (half_le_self hM.le).trans hd
  set S := fun j ↦ (hSfin j).toFinset
  -- One base `b` exceeding every entry of every exponent in every `S j` serves the whole family.
  set b := Finset.univ.sup (fun j ↦ (S j).sup fun d ↦ Finset.univ.sup d) + 2
  have hb : 1 < b := by omega
  have hbS (j : ι) (d) (hd : d ∈ S j) (x : Option σ) : d x < b := by
    have := ((Finset.le_sup (Finset.mem_univ x)).trans
      (Finset.le_sup (f := fun d : Option σ →₀ ℕ ↦ Finset.univ.sup d) hd)).trans
        (Finset.le_sup (f := fun j ↦ (S j).sup fun d ↦ Finset.univ.sup d) (Finset.mem_univ j))
    omega
  set k := Fintype.equivFin σ
  have hα (i : σ) : b ^ ((k i : ℕ) + 1) ≠ 0 := pow_ne_zero _ (by omega)
  refine ⟨fun i ↦ b ^ ((k i : ℕ) + 1), hα, fun j ↦ ?_⟩
  obtain ⟨ν, ε, hε0, hεM, hνM, hν⟩ := exists_triangularDegree_dominant (f j) (hf j) (S j)
    (fun d ↦ (hSfin j).mem_toFinset) k hb (hbS j)
  exact exists_isDistinguished_of_triangularDegree_dominant hα (f j) ν hε0 hεM hνM hν

/-- **Distinguishing automorphisms of Tate algebras.** Over an ultrametric normed commutative
ring with `‖1‖ = 1`, every nonzero unit-radius restricted series `f` in the variables `Option σ`,
for finite `σ`, is carried by a triangular automorphism `Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i` to a series
distinguished in the variable `Y = none`: written as a restricted series in `Y` over the Tate
algebra in the variables `σ`, its image is distinguished of some degree `s`. Moreover its
coefficient in degree `s` is within less than `‖f‖` of a constant `a` with `‖a‖ = ‖f‖`. -/
theorem exists_restrictedTriangularEquiv_isDistinguished [Finite σ] (f : ExtraTate) (hf : f ≠ 0) :
    ∃ (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) (s : ℕ) (a : R), ‖a‖ = ‖f‖ ∧
      PowerSeries.IsDistinguished 1 s
        (restrictedOptionEquiv (restrictedTriangularEquiv α hα f) : PowerSeries Tate) ∧
      ‖PowerSeries.coeff s
          (restrictedOptionEquiv (restrictedTriangularEquiv α hα f) : PowerSeries Tate) -
        algebraMap R Tate a‖ < ‖f‖ := by
  obtain ⟨α, hα, h⟩ :=
    exists_restrictedTriangularEquiv_forall_isDistinguished (fun _ : Unit ↦ f) fun _ ↦ hf
  exact ⟨α, hα, h ()⟩

/-- **Distinguishing automorphisms of Tate algebras over a field, for finitely many series at
once.** Over a complete nonarchimedean field `K`, for finite `σ` and a finite family `f` of
nonzero elements of the Tate algebra in the variables `Option σ`, a single triangular
automorphism `Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i` carries every `f j` to a series which, as a restricted
series in the variable `Y = none` over the Tate algebra in the variables `σ`, is distinguished of
some degree `s` with a unit coefficient in degree `s`. -/
theorem exists_restrictedTriangularEquiv_forall_isDistinguished_isUnit {K : Type*}
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [Finite σ] {ι : Type*} [Finite ι]
    (f : ι → IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1)) (hf : ∀ j, f j ≠ 0) :
    ∃ (α : σ → ℕ) (hα : ∀ i, α i ≠ 0), ∀ j, ∃ s : ℕ,
      PowerSeries.IsDistinguished 1 s (restrictedOptionEquiv
        (restrictedTriangularEquiv α hα (f j)) :
          PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))) ∧
      IsUnit (PowerSeries.coeff s (restrictedOptionEquiv
        (restrictedTriangularEquiv α hα (f j)) :
          PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)))) := by
  obtain ⟨α, hα, h⟩ := exists_restrictedTriangularEquiv_forall_isDistinguished f hf
  refine ⟨α, hα, fun j ↦ ?_⟩
  obtain ⟨s, a, ha, hd, hclose⟩ := h j
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hf j (norm_eq_zero.mp (by simpa using ha.symm))
  let u : (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))ˣ :=
    Units.map (algebraMap K _).toMonoidHom (Units.mk0 a ha0)
  have hu : ‖((u⁻¹ : (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))ˣ) :
      IsRestricted.subring (R := K) (fun _ : σ ↦ 1))‖⁻¹ = ‖f j‖ := by
    simp [u, norm_algebraMap', ha]
  exact ⟨s, hd, (Units.ofNearby u _ (hu ▸ hclose)).isUnit⟩

/-- **Distinguishing automorphisms of Tate algebras over a field.** Over a complete
nonarchimedean field `K`, every nonzero element `f` of the Tate algebra in the variables
`Option σ`, for finite `σ`, is carried by a triangular automorphism `Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i`
to a series which, as a restricted series in the variable `Y = none` over the Tate algebra in the
variables `σ`, is distinguished of some degree `s` with a unit coefficient in degree `s`. These are
the hypotheses of Weierstrass division and preparation over the Tate algebra in the variables
`σ`. -/
theorem exists_restrictedTriangularEquiv_isDistinguished_isUnit {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Finite σ]
    (f : IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1)) (hf : f ≠ 0) :
    ∃ (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) (s : ℕ),
      PowerSeries.IsDistinguished 1 s (restrictedOptionEquiv
        (restrictedTriangularEquiv α hα f) :
          PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))) ∧
      IsUnit (PowerSeries.coeff s (restrictedOptionEquiv
        (restrictedTriangularEquiv α hα f) :
          PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)))) := by
  obtain ⟨α, hα, h⟩ :=
    exists_restrictedTriangularEquiv_forall_isDistinguished_isUnit (fun _ : Unit ↦ f) fun _ ↦ hf
  exact ⟨α, hα, h ()⟩

/-- **Distinguishing automorphisms of Tate algebras over a field, for finitely many series at
once**, in the form consumed by Weierstrass division: some `K`-algebra automorphism makes every
member of a finite family of nonzero elements distinguished in the variable `none`, each with a
unit coefficient in its distinguished degree. -/
theorem exists_algEquiv_forall_isDistinguished_isUnit {K : Type*} [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] [Finite σ] {ι : Type*} [Finite ι]
    (f : ι → IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1)) (hf : ∀ j, f j ≠ 0) :
    ∃ e : IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1) ≃ₐ[K]
        IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1), ∀ j, ∃ s : ℕ,
      PowerSeries.IsDistinguished 1 s (restrictedOptionEquiv (e (f j)) :
        PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))) ∧
      IsUnit (PowerSeries.coeff s (restrictedOptionEquiv (e (f j)) :
        PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)))) := by
  obtain ⟨α, hα, h⟩ := exists_restrictedTriangularEquiv_forall_isDistinguished_isUnit f hf
  exact ⟨restrictedTriangularEquiv α hα, h⟩

/-- **Distinguishing automorphisms of Tate algebras over a field**, in the form consumed by
Weierstrass division: some `K`-algebra automorphism makes a nonzero element distinguished in the
variable `none`, with a unit coefficient in the distinguished degree. -/
theorem exists_algEquiv_isDistinguished_isUnit {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Finite σ] (f : IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1))
    (hf : f ≠ 0) :
    ∃ (e : IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1) ≃ₐ[K]
        IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1)) (s : ℕ),
      PowerSeries.IsDistinguished 1 s (restrictedOptionEquiv (e f) :
        PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))) ∧
      IsUnit (PowerSeries.coeff s (restrictedOptionEquiv (e f) :
        PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)))) := by
  obtain ⟨e, h⟩ := exists_algEquiv_forall_isDistinguished_isUnit (fun _ : Unit ↦ f) fun _ ↦ hf
  exact ⟨e, h ()⟩

section Field

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- A series over a ring of restricted series is distinguished of degree `s` at radius `r > 0`,
with a unit coefficient in degree `s`, when the constant term `a` of that coefficient strictly
dominates: the other weighted coefficient norms of the coefficient in degree `s` are below `‖a‖`,
and those of the coefficient in every other degree `m`, multiplied by `r ^ m`, are below
`‖a‖ r ^ s`. -/
theorem isDistinguished_isUnit_of_norm_coeff_lt {c : σ → ℝ} [∀ i, Fact (0 < c i)]
    {r : ℝ} (hr : 0 < r) {s : ℕ} {G : PowerSeries (IsRestricted.subring (R := K) c)}
    (h0 : constantCoeff (↑(PowerSeries.coeff s G) : MvPowerSeries σ K) ≠ 0)
    (hs : ∀ t ≠ 0, ‖coeff t (↑(PowerSeries.coeff s G) : MvPowerSeries σ K)‖ * t.prod (c · ^ ·) <
      ‖constantCoeff (↑(PowerSeries.coeff s G) : MvPowerSeries σ K)‖)
    (hm : ∀ m ≠ s, ∀ t, ‖coeff t (↑(PowerSeries.coeff m G) : MvPowerSeries σ K)‖ *
      t.prod (c · ^ ·) * r ^ m < ‖constantCoeff (↑(PowerSeries.coeff s G) : MvPowerSeries σ K)‖ *
        r ^ s) :
    PowerSeries.IsDistinguished r s G ∧ IsUnit (PowerSeries.coeff s G) := by
  set N := ‖constantCoeff (↑(PowerSeries.coeff s G) : MvPowerSeries σ K)‖
  have hGs : ‖PowerSeries.coeff s G‖ = N :=
    norm_eq_norm_constantCoeff_of_norm_coeff_mul_prod_le fun t ht ↦ (hs t ht).le
  have hGm (m : ℕ) (hm' : m ≠ s) : ‖PowerSeries.coeff m G‖ * r ^ m < N * r ^ s := by
    have hrm : 0 < r ^ m := pow_pos hr _
    rw [← lt_div_iff₀ hrm, MvPowerSeries.norm_lt_iff]
    exact fun t ↦ (lt_div_iff₀ hrm).2 (hm m hm' t)
  have hgauss : G.gaussNorm norm r = N * r ^ s := by
    rw [TauCeti.PowerSeries.gaussNorm_eq_of_forall_le fun m ↦ ?_, hGs]
    rcases eq_or_ne m s with rfl | hm'
    · exact le_rfl
    · exact (hGm m hm').le.trans_eq (by rw [hGs])
  exact ⟨⟨by rw [hGs, hgauss], fun m hm' ↦ hgauss ▸ hGm m hm'.ne'⟩,
    (isUnit_iff_constantCoeff_ne_zero_and_norm_coeff_mul_prod_lt _).2 ⟨h0, hs⟩⟩

end Field

end TauCeti.MvPowerSeries
