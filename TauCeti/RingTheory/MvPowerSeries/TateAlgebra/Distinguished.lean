/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Iterate
public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Subst
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.Analysis.Normed.Ring.Units

import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Digits.Lemmas


/-!
# Making a restricted series distinguished in one variable

Let `R` be an ultrametric normed commutative ring with `‖1‖ = 1`, and let `σ` be finite. Separating
the variable `Y = X none` identifies the unit-radius Tate algebra in the variables `Option σ` with
restricted power series in `Y` over the Tate algebra in the variables `σ`
(`TauCeti.Huber.restrictedOptionEquiv`). A nonzero series need not be distinguished in `Y` in
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
largest degree gives the distinguished coefficient.

## Main results

* `TauCeti.MvPowerSeries.exists_algEquiv_isDistinguished`: over an ultrametric normed commutative
  ring, an isometric automorphism makes a nonzero series distinguished in `Y`, with dominant
  coefficient close to a constant of the same norm.
* `TauCeti.MvPowerSeries.exists_algEquiv_isDistinguished_isUnit`: over a complete nonarchimedean
  field, the dominant coefficient is moreover a unit.

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
private noncomputable def triangularFamily (α : σ → ℕ) (u : R) :
    Option σ → MvPolynomial (Option σ) R :=
  fun x ↦ x.elim (MvPolynomial.X none) fun i ↦
    MvPolynomial.X (some i) + MvPolynomial.C u * MvPolynomial.X none ^ α i

omit [IsUltrametricDist R] [NormOneClass R] in
private theorem constantCoeff_triangularFamily {α : σ → ℕ} (hα : ∀ i, α i ≠ 0) (u : R)
    (x : Option σ) : (triangularFamily α u x).constantCoeff = 0 := by
  cases x <;> simp [triangularFamily, hα]

private theorem norm_coeff_triangularFamily_le {u : R} (hu : ‖u‖ ≤ 1) (α : σ → ℕ)
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
private theorem aeval_triangularFamily (α : σ → ℕ) {u v : R} (huv : u + v = 0) (x : Option σ) :
    MvPolynomial.aeval (triangularFamily α u) (triangularFamily α v x) = MvPolynomial.X x := by
  cases x with
  | none => simp [triangularFamily]
  | some i =>
    simp only [triangularFamily, Option.elim_some, Option.elim_none, map_add, map_mul, map_pow,
      MvPolynomial.aeval_X, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
      eq_neg_of_add_eq_zero_right huv, map_neg]
    ring

/-- The triangular automorphism `Y ↦ Y`, `Xᵢ ↦ Xᵢ + Y ^ α i` of the Tate algebra in the
variables `Option σ`. -/
private noncomputable def triangularEquiv [Finite σ] (α : σ → ℕ) (hα : ∀ i, α i ≠ 0) :
    ExtraTate ≃ₐ[R] ExtraTate :=
  restrictedSubstEquiv (triangularFamily α 1) (constantCoeff_triangularFamily hα 1)
    (norm_coeff_triangularFamily_le norm_one.le α) (triangularFamily α (-1))
    (constantCoeff_triangularFamily hα (-1))
    (norm_coeff_triangularFamily_le (by simp : ‖(-1 : R)‖ ≤ 1) α)
    (aeval_triangularFamily α (neg_add_cancel 1)) (aeval_triangularFamily α (add_neg_cancel 1))

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
private theorem norm_coeff_triangularEquiv_sub_le [Finite σ] [Nontrivial R] {α : σ → ℕ}
    (hα : ∀ i, α i ≠ 0)
    (f : ExtraTate) (ν : Option σ →₀ ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hν : ∀ d ≠ ν, triangularDegree α ν ≤ triangularDegree α d →
      ‖coeff d (f : MvPowerSeries (Option σ) R)‖ ≤ ε)
    (t : σ →₀ ℕ) {m : ℕ} (hm : triangularDegree α ν ≤ m) :
    ‖coeff (t.optionElim m) (triangularEquiv α hα f : MvPowerSeries (Option σ) R) -
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
  simpa [triangularEquiv] using h

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
/-- **Choice of the triangular exponents.** For a nonzero restricted series `f` there are
exponents `α` and an exponent `ν` with `‖coeff ν f‖ = ‖f‖` such that every other exponent of
triangular degree at least that of `ν` carries a coefficient of norm at most some `ε < ‖f‖`. -/
private theorem exists_triangularDegree_dominant [Finite σ] (f : ExtraTate) (hf : f ≠ 0) :
    ∃ (α : σ → ℕ) (_ : ∀ i, α i ≠ 0) (ν : Option σ →₀ ℕ) (ε : ℝ), 0 ≤ ε ∧ ε < ‖f‖ ∧
      ‖coeff ν (f : MvPowerSeries (Option σ) R)‖ = ‖f‖ ∧
      ∀ d ≠ ν, triangularDegree α ν ≤ triangularDegree α d →
        ‖coeff d (f : MvPowerSeries (Option σ) R)‖ ≤ ε := by
  classical
  have : Fintype σ := Fintype.ofFinite σ
  obtain ⟨d₀, hd₀⟩ := exists_achievesGaussNorm f
  obtain ⟨ε, hε0, hεM, hε⟩ := exists_norm_coeff_mul_prod_gap f hf
  simp only [AchievesGaussNorm, ← norm_eq_gaussNorm, one_pow, Finsupp.prod_fun_one,
    mul_one] at hd₀ hε
  have hM : 0 < ‖f‖ := norm_pos_iff.mpr hf
  have hle (d) : ‖coeff d (f : MvPowerSeries (Option σ) R)‖ ≤ ‖f‖ := by
    simpa using norm_coeff_mul_prod_le f d
  -- The exponents of the monomials of maximal coefficient norm form a finite nonempty set `S`.
  have hSfin : {d | ‖f‖ ≤ ‖coeff d (f : MvPowerSeries (Option σ) R)‖}.Finite := by
    have := (isRestricted_one_iff.mp f.2).eventually (gt_mem_nhds (half_pos hM))
    exact (by simpa [eventually_cofinite, not_lt] using this :
      {d | ‖f‖ / 2 ≤ ‖coeff d (f : MvPowerSeries (Option σ) R)‖}.Finite).subset
        fun d hd ↦ (half_le_self hM.le).trans hd
  set S := hSfin.toFinset
  have hS : S.Nonempty := ⟨d₀, hSfin.mem_toFinset.mpr hd₀.ge⟩
  -- A base `b` exceeding every entry of an exponent in `S`, and the exponents `b ^ (k i + 1)`.
  set b := S.sup (fun d ↦ Finset.univ.sup d) + 2
  have hb : 1 < b := by omega
  have hbound (d) (hd : d ∈ S) (x : Option σ) : d x < b := by
    have := (Finset.le_sup (Finset.mem_univ x)).trans
      (Finset.le_sup (f := fun d : Option σ →₀ ℕ ↦ Finset.univ.sup d) hd)
    omega
  set k := Fintype.equivFin σ
  set α : σ → ℕ := fun i ↦ b ^ ((k i : ℕ) + 1)
  -- The dominant exponent of largest triangular degree.
  obtain ⟨ν, hνS, hνmax⟩ := S.exists_max_image (triangularDegree α) hS
  refine ⟨α, fun i ↦ pow_ne_zero _ (by omega), ν, ε, hε0, hεM,
    le_antisymm (hle ν) (hSfin.mem_toFinset.mp hνS), fun d hd hdeg ↦ ?_⟩
  by_cases hdS : d ∈ S
  · exact absurd (triangularDegree_injective k hb (hbound d hdS) (hbound ν hνS)
      (le_antisymm (hνmax d hdS) hdeg)) hd
  · exact hε d (lt_of_not_ge fun h ↦ hdS (hSfin.mem_toFinset.mpr h))

/-- **Distinguishing automorphisms of Tate algebras.** Over an ultrametric normed commutative
ring with `‖1‖ = 1`, every nonzero unit-radius restricted series `f` in the variables `Option σ`,
for finite `σ`, is carried by an isometric `R`-algebra automorphism `e` to a series distinguished
in the variable `none`: written as a restricted series in that variable over the Tate algebra in
the variables `σ`, `e f` is distinguished of some degree `s`. Moreover its coefficient in degree `s`
is within less than `‖f‖` of a constant `a` with `‖a‖ = ‖f‖`. -/
theorem exists_algEquiv_isDistinguished [Finite σ] (f : ExtraTate) (hf : f ≠ 0) :
    ∃ (e : ExtraTate ≃ₐ[R] ExtraTate) (s : ℕ) (a : R), (∀ g, ‖e g‖ = ‖g‖) ∧ ‖a‖ = ‖f‖ ∧
      PowerSeries.IsDistinguished 1 s (Huber.restrictedOptionEquiv (e f) : PowerSeries Tate) ∧
      ‖PowerSeries.coeff s (Huber.restrictedOptionEquiv (e f) : PowerSeries Tate) -
        algebraMap R Tate a‖ < ‖f‖ := by
  classical
  obtain ⟨α, hα, ν, ε, hε0, hεM, hνM, hν⟩ := exists_triangularDegree_dominant f hf
  have : Nontrivial R := nontrivial_of_ne (coeff ν (f : MvPowerSeries (Option σ) R)) 0
    fun h ↦ (norm_pos_iff.mpr hf).ne' (by rw [← hνM, h, norm_zero])
  have he (g : ExtraTate) : ‖triangularEquiv α hα g‖ = ‖g‖ := norm_restrictedSubstEquiv ..
  set a := coeff ν (f : MvPowerSeries (Option σ) R)
  set s := triangularDegree α ν
  set G := Huber.restrictedOptionEquiv (triangularEquiv α hα f)
  have hG : ‖G‖ = ‖f‖ := by rw [Huber.norm_restrictedOptionEquiv, he]
  have hGn : (G : PowerSeries Tate).gaussNorm norm 1 = ‖f‖ := by
    rw [← TauCeti.PowerSeries.norm_eq_gaussNorm, hG]
  have hcoeffG (m : ℕ) (t : σ →₀ ℕ) :
      coeff t (PowerSeries.coeff (R := Tate) m (G : PowerSeries Tate) : MvPowerSeries σ R) =
        coeff (t.optionElim m) (triangularEquiv α hα f : MvPowerSeries (Option σ) R) := by
    rw [Huber.coeff_restrictedOptionEquiv, coeff_coeff_optionEquivLeft]
  have hcore := norm_coeff_triangularEquiv_sub_le hα f ν hε0 hν
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
  refine ⟨triangularEquiv α hα, s, a, he, hνM,
    PowerSeries.isDistinguished_of_norm_coeff_sub_lt zero_lt_one
      (by rw [one_pow, mul_one, hGn, hCa])
      (by rw [one_pow, mul_one, hGn]; exact hat.trans_lt hεM)
      (fun m hm ↦ by rw [one_pow, mul_one, hGn]; exact (hbeyond m hm).trans_lt hεM),
    hat.trans_lt hεM⟩

/-- **Distinguishing automorphisms of Tate algebras over a field.** Over a complete
nonarchimedean field `K`, every nonzero element `f` of the Tate algebra in the variables
`Option σ`, for finite `σ`, is carried by a `K`-algebra automorphism to a series which, as a
restricted series in the variable `none` over the Tate algebra in the variables `σ`, is
distinguished of some degree `s` with a unit coefficient in degree `s`. These are the hypotheses
of Weierstrass division and preparation over the Tate algebra in the variables `σ`. -/
theorem exists_algEquiv_isDistinguished_isUnit {K : Type*} [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [Finite σ] (f : IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1))
    (hf : f ≠ 0) :
    ∃ (e : IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1) ≃ₐ[K]
        IsRestricted.subring (R := K) (fun _ : Option σ ↦ 1)) (s : ℕ),
      PowerSeries.IsDistinguished 1 s (Huber.restrictedOptionEquiv (e f) :
        PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))) ∧
      IsUnit (PowerSeries.coeff s (Huber.restrictedOptionEquiv (e f) :
        PowerSeries (IsRestricted.subring (R := K) (fun _ : σ ↦ 1)))) := by
  obtain ⟨e, s, a, -, ha, hd, hclose⟩ := exists_algEquiv_isDistinguished f hf
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hf (norm_eq_zero.mp (by simpa using ha.symm))
  let u : (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))ˣ :=
    Units.map (algebraMap K _).toMonoidHom (Units.mk0 a ha0)
  have hu : ‖((u⁻¹ : (IsRestricted.subring (R := K) (fun _ : σ ↦ 1))ˣ) :
      IsRestricted.subring (R := K) (fun _ : σ ↦ 1))‖⁻¹ = ‖f‖ := by
    simp [u, norm_algebraMap', ha]
  exact ⟨e, s, hd, (Units.ofNearby u _ (hu ▸ hclose)).isUnit⟩

end TauCeti.MvPowerSeries
