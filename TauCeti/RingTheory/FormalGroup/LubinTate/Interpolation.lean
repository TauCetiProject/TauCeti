/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.RingTheory.MvPowerSeries.Expand
import Mathlib.Tactic.LinearCombination
import TauCeti.RingTheory.LocalRing.MaximalIdeal.Basic
import TauCeti.RingTheory.MvPowerSeries.Order
import TauCeti.RingTheory.PowerSeries.Substitution

/-!
# Lubin–Tate series and Lubin–Tate interpolation

Let `O` be a local ring and `π ∈ O`. A *Lubin–Tate series* for `π` and `q`
(`TauCeti.IsLubinTateSeries π q f`) is a power series `f ∈ O⟦X⟧` with zero constant term, linear
coefficient `π`, and reduction `X ^ q` modulo the maximal ideal; the standard example is
`π X + X ^ q` (`TauCeti.isLubinTateSeries_C_mul_X_add_X_pow`). When `O` is a discrete valuation
ring with finite residue field of cardinality `q` and `π` is a uniformizer, these are the series
from which Lubin and Tate build the formal groups of local class field theory.

The basic tool is **Lubin–Tate interpolation** (`TauCeti.exists_lubinTate_interpolation`): for
Lubin–Tate series `f` and `g` for the same `π` and `a₁, …, aₙ ∈ O`, there is a unique series
`H ∈ O⟦X₁, …, Xₙ⟧` with zero constant term and linear part `∑ aᵢ Xᵢ` such that

  `f(H(X₁, …, Xₙ)) = H(g(X₁), …, g(Xₙ))`,

and it is also the only such series with coefficients in the fraction field of `O`. In arity one
this gives the homomorphisms `[a]_(f, g)` between Lubin–Tate formal groups, and in arity two, with
linear part `X + Y` and `f = g`, the Lubin–Tate formal group law itself.

The series is built degree by degree. If `H` solves the equation below degree `r ≥ 2`, then
modifying `H` by a homogeneous `Δ` of degree `r` changes the degree-`r` part of
`f(H) - H(g(X))` by `(π - πʳ) Δ`, because `f` and `g` have linear coefficient `π`. The error is
divisible by `π`: modulo the maximal ideal `f(H) - H(g(X))` reduces to `h ^ q - h(X ^ q)`, where
`h` is the reduction of `H`, and this vanishes since the residue field has `q` elements. As
`π - πʳ` is `π` times a unit, the error can be cancelled. Uniqueness, over any coefficient ring
in which every `π - πʳ` with `r ≥ 2` is regular, is the same computation
(`TauCeti.eq_of_lubinTate_functional_equation`).

## Main definitions

* `TauCeti.IsLubinTateSeries π q f`: `f` is a Lubin–Tate series for `π` and `q`.

## Main results

* `TauCeti.isLubinTateSeries_C_mul_X_add_X_pow`: `π X + X ^ q` is a Lubin–Tate series when `π` is
  in the maximal ideal and `q ≥ 2`.
* `TauCeti.eq_of_lubinTate_functional_equation`: two solutions of `f(H) = H(g(X))` with the same
  linear part are equal, when `f` and `g` have linear coefficient `π` and every `π - πʳ`, `r ≥ 2`,
  is a left-regular element.
* `TauCeti.exists_lubinTate_interpolation`: **Lubin–Tate interpolation**, existence and uniqueness
  over `O` and over its fraction field.

## References

* J. Lubin and J. Tate, *Formal complex multiplication in local fields*, Ann. of Math. 81
  (1965), 380–387, §1, Lemma 1 and the remarks following it.
* J.-P. Serre, *Local class field theory*, in J. W. S. Cassels and A. Fröhlich (eds.),
  *Algebraic Number Theory*, Academic Press (1967), §3.5, Proposition 5.
-/

public section

noncomputable section

open PowerSeries IsLocalRing

namespace TauCeti

section Series

variable {O : Type*} [CommRing O] [IsLocalRing O]

/-- A *Lubin–Tate series* for `π` and `q`: a power series with zero constant coefficient, linear
coefficient `π`, and reduction `X ^ q` modulo the maximal ideal. For a discrete valuation ring with
residue field of cardinality `q` and a uniformizer `π`, these are the series of Lubin and Tate
(LT65, §1, condition (1)). -/
structure IsLubinTateSeries (π : O) (q : ℕ) (f : O⟦X⟧) : Prop where
  /-- A Lubin–Tate series has zero constant coefficient. -/
  constantCoeff_eq_zero : constantCoeff f = 0
  /-- The linear coefficient of a Lubin–Tate series for `π` is `π`. -/
  coeff_one : coeff 1 f = π
  /-- A Lubin–Tate series for `q` reduces to `X ^ q` modulo the maximal ideal. -/
  map_residue : map (residue O) f = X ^ q

/-- A Lubin–Tate series can be substituted into power series. -/
theorem IsLubinTateSeries.hasSubst {π : O} {q : ℕ} {f : O⟦X⟧} (hf : IsLubinTateSeries π q f) :
    HasSubst f :=
  .of_constantCoeff_zero' hf.constantCoeff_eq_zero

/-- `π X + X ^ q` is a Lubin–Tate series for `π` and `q`, when `π` lies in the maximal ideal and
`q ≥ 2`. -/
theorem isLubinTateSeries_C_mul_X_add_X_pow {π : O} (hπ : π ∈ maximalIdeal O) {q : ℕ}
    (hq : 2 ≤ q) : IsLubinTateSeries π q (C π * X + X ^ q) where
  constantCoeff_eq_zero := by simp [zero_pow (by omega : q ≠ 0)]
  coeff_one := by simp [coeff_X_pow]; omega
  map_residue := by simp [(residue_eq_zero_iff π).mpr hπ]

end Series

section Interpolation

variable {σ R : Type*} [CommRing R]

/-- The defect `f(H) - H(g(X₁), g(X₂), …)` of the Lubin–Tate functional equation. -/
private def defect (f g : R⟦X⟧) (H : MvPowerSeries σ R) : MvPowerSeries σ R :=
  f.subst H - H.subst fun i ↦ g.subst (MvPowerSeries.X i)

variable [Finite σ]

/-- **The variation of the defect.** If `H` and `H'` have zero constant coefficient, then in each
degree `m` at most the order of `H' - H`, the defect changes by `(c - dᵐ)` times the change of `H`,
where `c` and `d` are the linear coefficients of `f` and `g`. -/
private theorem coeff_defect_sub_defect (f : R⟦X⟧) {g : R⟦X⟧} (hg₀ : constantCoeff g = 0)
    {H H' : MvPowerSeries σ R} (hH : MvPowerSeries.constantCoeff H = 0)
    (hH' : MvPowerSeries.constantCoeff H' = 0) {e : σ →₀ ℕ}
    (he : (e.degree : ℕ∞) ≤ (H' - H).order) :
    MvPowerSeries.coeff e (defect f g H' - defect f g H) =
      (coeff 1 f - coeff 1 g ^ e.degree) * MvPowerSeries.coeff e (H' - H) := by
  have hf := MvPowerSeries.coeff_subst_sub_subst_of_degree_le (σ := Unit) f
    (a := fun _ ↦ H') (b := fun _ ↦ H) (fun _ ↦ hH') (fun _ ↦ hH) (fun _ ↦ he) le_rfl
  have hg := coeff_subst_subst_X_of_le_order (S := R) hg₀ he
  rw [MvPowerSeries.subst_sub (PowerSeries.hasSubst_subst_X hg₀), Algebra.algebraMap_self,
    RingHom.id_apply] at hg
  rw [Fintype.sum_unique, coeff_coeToMvPowerSeries, ← subst_def, ← subst_def] at hf
  rw [defect, defect, sub_sub_sub_comm, map_sub, hf, hg, sub_mul]

/-- Modulo the maximal ideal the defect vanishes: there both `f(H)` and `H(g(X))` reduce to the
`q`-th power of the reduction of `H`, the second because the residue field has `q` elements. -/
private theorem map_residue_defect {O : Type*} [CommRing O] [IsLocalRing O]
    [Finite (ResidueField O)] {f g : O⟦X⟧}
    (hf : map (residue O) f = X ^ Nat.card (ResidueField O)) (hg₀ : constantCoeff g = 0)
    (hg : map (residue O) g = X ^ Nat.card (ResidueField O)) {H : MvPowerSeries σ O}
    (hH : MvPowerSeries.constantCoeff H = 0) :
    MvPowerSeries.map (residue O) (defect f g H) = 0 := by
  have := Fintype.ofFinite (ResidueField O)
  rw [Nat.card_eq_fintype_card] at hf hg
  have hHs : HasSubst H := .of_constantCoeff_zero hH
  have hHs' : HasSubst (MvPowerSeries.map (residue O) H) := .of_constantCoeff_zero (by simp [hH])
  have hG (i : σ) : MvPowerSeries.map (residue O) (g.subst (MvPowerSeries.X i)) =
      MvPowerSeries.X i ^ Fintype.card (ResidueField O) := by
    rw [PowerSeries.map_subst (.X i), hg, MvPowerSeries.map_X, subst_pow (.X i), subst_X (.X i)]
  rw [defect, map_sub, PowerSeries.map_subst hHs, hf, subst_pow hHs', subst_X hHs',
    MvPowerSeries.map_subst (PowerSeries.hasSubst_subst_X hg₀)]
  simp_rw [hG]
  rw [← FiniteField.MvPowerSeries.expand_card, MvPowerSeries.expand,
    MvPowerSeries.coe_substAlgHom, sub_self]

/-- **Two solutions with the same linear part are equal.** Let `f` and `g` have linear coefficient
`π`, with `g` of zero constant coefficient, and suppose that `π - πʳ` is left-regular for every
`r ≥ 2`. If `H` and `H'` have zero constant coefficient and the same linear coefficients, and both
satisfy `f(H) = H(g(X₁), g(X₂), …)`, then `H = H'`. -/
theorem eq_of_lubinTate_functional_equation {π : R}
    (hπ : ∀ r, 2 ≤ r → IsLeftRegular (π - π ^ r)) {f g : R⟦X⟧} (hf : coeff 1 f = π)
    (hg₀ : constantCoeff g = 0) (hg : coeff 1 g = π) {H H' : MvPowerSeries σ R}
    (hH₀ : MvPowerSeries.constantCoeff H = 0) (hH'₀ : MvPowerSeries.constantCoeff H' = 0)
    (hlin : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) H =
      MvPowerSeries.coeff (Finsupp.single i 1) H')
    (hH : f.subst H = H.subst fun i ↦ g.subst (MvPowerSeries.X i))
    (hH' : f.subst H' = H'.subst fun i ↦ g.subst (MvPowerSeries.X i)) : H = H' := by
  have hd : defect f g H' - defect f g H = 0 := by simp [defect, hH, hH']
  -- by induction on `k`, `H` and `H'` agree below degree `k`
  have key (k : ℕ) : ∀ d : σ →₀ ℕ, d.degree < k → MvPowerSeries.coeff d (H' - H) = 0 := by
    induction k with
    | zero => simp
    | succ k ih =>
      intro d hdk
      rcases (Nat.lt_succ_iff.mp hdk).lt_or_eq with hlt | rfl
      · exact ih d hlt
      rcases lt_or_ge d.degree 2 with h2 | h2
      · rcases (by omega : d.degree = 0 ∨ d.degree = 1) with h0 | h1
        · rw [(Finsupp.degree_eq_zero_iff d).mp h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
            map_sub, hH₀, hH'₀, sub_self]
        · obtain ⟨i, rfl⟩ := (Set.ext_iff.mp Finsupp.range_single_one d).mpr h1
          rw [map_sub, hlin, sub_self]
      · have hle : (d.degree : ℕ∞) ≤ (H' - H).order :=
          MvPowerSeries.le_order fun e he ↦ ih e (by exact_mod_cast he)
        have h := coeff_defect_sub_defect f hg₀ hH₀ hH'₀ hle
        rw [hd, map_zero, hf, hg] at h
        exact (hπ _ h2).mul_left_eq_zero_iff.mp h.symm
  ext d
  exact (sub_eq_zero.mp (key _ d d.degree.lt_succ_self)).symm

/-- The linear series `∑ aᵢ Xᵢ` solves the functional equation below degree two, when `f` and
`g` have zero constant coefficient and the same linear coefficient. -/
private theorem exists_two_le_order_defect {f g : R⟦X⟧} (hf₀ : constantCoeff f = 0)
    (hg₀ : constantCoeff g = 0) (hfg : coeff 1 f = coeff 1 g) (a : σ → R) :
    ∃ L : MvPowerSeries σ R, MvPowerSeries.constantCoeff L = 0 ∧
      (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) L = a i) ∧
      2 ≤ (defect f g L).order := by
  classical
  have := Fintype.ofFinite σ
  let L : MvPowerSeries σ R := ∑ i, MvPowerSeries.C (a i) * MvPowerSeries.X i
  have hL₀ : MvPowerSeries.constantCoeff L = 0 := by simp [L]
  refine ⟨L, hL₀, fun i ↦ by simp [L, MvPowerSeries.coeff_X, Finsupp.single_eq_single_iff],
    MvPowerSeries.nat_le_order (n := 2) fun e he ↦ ?_⟩
  -- compare with the zero series, whose defect vanishes
  have hdef0 : defect f g (0 : MvPowerSeries σ R) = 0 := by
    rw [defect, subst_def, ← Pi.zero_def, MvPowerSeries.subst_zero_of_constantCoeff_zero hf₀,
      ← MvPowerSeries.coe_substAlgHom (PowerSeries.hasSubst_subst_X hg₀), map_zero, sub_zero]
  have hle : (e.degree : ℕ∞) ≤ (L - 0).order := by
    rw [sub_zero]
    exact (MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr hL₀).trans'
      (by exact_mod_cast (by omega : e.degree ≤ 1))
  have h := coeff_defect_sub_defect f hg₀ (map_zero _) hL₀ hle
  rw [hdef0, sub_zero, sub_zero, hfg] at h
  rw [h]
  rcases (by omega : e.degree = 0 ∨ e.degree = 1) with h0 | h1
  · rw [(Finsupp.degree_eq_zero_iff e).mp h0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      hL₀, mul_zero]
  · rw [h1, pow_one, sub_self, zero_mul]

/-- **Passage to the limit.** If the stages `S n` have zero constant coefficient and linear part
`a`, solve the functional equation below degree `n + 2`, and agree with the next stage below
degree `n`, then their limit solves the equation. -/
private theorem exists_defect_eq_zero_of_stages {f g : R⟦X⟧} (hg₀ : constantCoeff g = 0)
    {a : σ → R} {S : ℕ → MvPowerSeries σ R} (h₀ : ∀ n, MvPowerSeries.constantCoeff (S n) = 0)
    (h₁ : ∀ n i, MvPowerSeries.coeff (Finsupp.single i 1) (S n) = a i)
    (hd : ∀ n, ((n + 2 : ℕ) : ℕ∞) ≤ (defect f g (S n)).order)
    (hS : ∀ n : ℕ, (n : ℕ∞) ≤ (S (n + 1) - S n).order) :
    ∃ H : MvPowerSeries σ R, MvPowerSeries.constantCoeff H = 0 ∧
      (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) H = a i) ∧ defect f g H = 0 := by
  obtain ⟨H, hH⟩ := MvPowerSeries.exists_forall_le_order_sub hS
  -- `H` agrees with `S (n + 1)` below degree `n + 1`
  have hagree (n : ℕ) {e : σ →₀ ℕ} (he : e.degree ≤ n) :
      MvPowerSeries.coeff e H = MvPowerSeries.coeff e (S (n + 1)) := by
    rw [← sub_eq_zero, ← map_sub]
    exact MvPowerSeries.coeff_of_lt_order ((hH (n + 1)).trans_lt' (by exact_mod_cast by omega))
  have hH₀ : MvPowerSeries.constantCoeff H = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hagree 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, h₀]
  refine ⟨H, hH₀, fun i ↦ by rw [hagree 1 (by simp), h₁], ?_⟩
  ext e
  have h := coeff_defect_sub_defect f hg₀ (h₀ (e.degree + 1)) hH₀
    ((hH (e.degree + 1)).trans' (by exact_mod_cast e.degree.le_succ))
  rw [map_sub, sub_eq_iff_eq_add, MvPowerSeries.coeff_of_lt_order
    ((hd _).trans_lt' (by exact_mod_cast by omega)), add_zero, map_sub,
    hagree e.degree le_rfl, sub_self, mul_zero] at h
  rw [h, map_zero]

section Existence

variable {O : Type*} [CommRing O] [IsLocalRing O] [Finite (ResidueField O)] {π : O}
  {f g : O⟦X⟧}

/-- One step of the construction: a series `H` solving the functional equation below degree
`n + 2` can be corrected in degree `n + 2` so that it solves it below degree `n + 3`. The
correction is the error divided by `π - π ^ (n + 2)`, which is possible because the error is
divisible by `π` and `π - π ^ (n + 2)` is `π` times a unit. -/
private theorem exists_le_order_defect_add (hπ : maximalIdeal O = Ideal.span {π})
    (hf : IsLubinTateSeries π (Nat.card (ResidueField O)) f)
    (hg : IsLubinTateSeries π (Nat.card (ResidueField O)) g) (n : ℕ) {H : MvPowerSeries σ O}
    (hH : MvPowerSeries.constantCoeff H = 0)
    (hd : ((n + 2 : ℕ) : ℕ∞) ≤ (defect f g H).order) :
    ∃ Δ : MvPowerSeries σ O, ((n + 2 : ℕ) : ℕ∞) ≤ Δ.order ∧
      ((n + 3 : ℕ) : ℕ∞) ≤ (defect f g (H + Δ)).order := by
  have hu := IsLocalRing.isUnit_one_sub_pow_of_mem_maximalIdeal
    (hπ ▸ Ideal.mem_span_singleton_self π) n.add_one_ne_zero
  -- every coefficient of the defect is divisible by `π`
  have hdiv (e : σ →₀ ℕ) : ∃ y, y * π = MvPowerSeries.coeff e (defect f g H) := by
    rw [← Ideal.mem_span_singleton', ← hπ, ← residue_eq_zero_iff, ← MvPowerSeries.coeff_map,
      map_residue_defect hf.map_residue hg.constantCoeff_eq_zero hg.map_residue hH, map_zero]
  choose y hy using hdiv
  -- the correction, homogeneous of degree `n + 2`
  let Δ : MvPowerSeries σ O := fun e ↦ if e.degree = n + 2 then -(y e * ↑hu.unit⁻¹) else 0
  have hΔ (e : σ →₀ ℕ) : MvPowerSeries.coeff e Δ =
      if e.degree = n + 2 then -(y e * ↑hu.unit⁻¹) else 0 :=
    MvPowerSeries.coeff_apply Δ e
  have hΔo : ((n + 2 : ℕ) : ℕ∞) ≤ Δ.order :=
    MvPowerSeries.nat_le_order fun e he ↦ by rw [hΔ, ite_eq_right he.ne]
  refine ⟨Δ, hΔo, MvPowerSeries.nat_le_order fun e he ↦ ?_⟩
  have hΔ₀ := MvPowerSeries.constantCoeff_eq_zero_of_le_order (by simp) hΔo
  have hle : (e.degree : ℕ∞) ≤ (H + Δ - H).order := by
    rw [add_sub_cancel_left]
    exact hΔo.trans' (by exact_mod_cast (by omega : e.degree ≤ n + 2))
  have hv := coeff_defect_sub_defect f hg.constantCoeff_eq_zero hH
    (by rw [map_add, hH, hΔ₀, add_zero]) hle
  rw [map_sub, sub_eq_iff_eq_add, add_sub_cancel_left, hf.coeff_one, hg.coeff_one] at hv
  rw [hv, hΔ]
  rcases (Nat.lt_succ_iff.mp he).lt_or_eq with hlt | heq
  · rw [ite_eq_right hlt.ne, mul_zero, zero_add]
    exact MvPowerSeries.coeff_of_lt_order (hd.trans_lt' (by exact_mod_cast hlt))
  · rw [ite_eq_left heq, heq, ← hy]
    linear_combination (-π * y e) * hu.mul_val_inv

/-- **Existence of the interpolating series** over a local ring whose maximal ideal is generated
by `π` and whose residue field has `q` elements. -/
private theorem exists_defect_eq_zero (hπ : maximalIdeal O = Ideal.span {π})
    (hf : IsLubinTateSeries π (Nat.card (ResidueField O)) f)
    (hg : IsLubinTateSeries π (Nat.card (ResidueField O)) g) (a : σ → O) :
    ∃ H : MvPowerSeries σ O, MvPowerSeries.constantCoeff H = 0 ∧
      (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) H = a i) ∧ defect f g H = 0 := by
  obtain ⟨L, hL₀, hL₁, hL⟩ := exists_two_le_order_defect hf.constantCoeff_eq_zero
    hg.constantCoeff_eq_zero (hf.coeff_one.trans hg.coeff_one.symm) a
  -- the corrections, chosen at every stage
  have step (n : ℕ) (H : MvPowerSeries σ O) : ∃ Δ : MvPowerSeries σ O,
      ((n + 2 : ℕ) : ℕ∞) ≤ Δ.order ∧ (MvPowerSeries.constantCoeff H = 0 →
        ((n + 2 : ℕ) : ℕ∞) ≤ (defect f g H).order →
          ((n + 3 : ℕ) : ℕ∞) ≤ (defect f g (H + Δ)).order) := by
    by_cases h : MvPowerSeries.constantCoeff H = 0 ∧ ((n + 2 : ℕ) : ℕ∞) ≤ (defect f g H).order
    · obtain ⟨Δ, h₁, h₂⟩ := exists_le_order_defect_add hπ hf hg n h.1 h.2
      exact ⟨Δ, h₁, fun _ _ ↦ h₂⟩
    · exact ⟨0, by simp, fun h₁ h₂ ↦ (h ⟨h₁, h₂⟩).elim⟩
  choose Δ hΔ hΔd using step
  obtain ⟨S, hS₀, hS⟩ : ∃ S : ℕ → MvPowerSeries σ O, S 0 = L ∧ ∀ n, S (n + 1) = S n + Δ n (S n) :=
    ⟨fun n ↦ Nat.rec L (fun k Hk ↦ Hk + Δ k Hk) n, rfl, fun _ ↦ rfl⟩
  have hΔ₀ (n : ℕ) (H : MvPowerSeries σ O) : MvPowerSeries.constantCoeff (Δ n H) = 0 :=
    MvPowerSeries.constantCoeff_eq_zero_of_le_order (by simp) (hΔ n H)
  -- the stages keep the linear part and solve the equation in increasing degree
  have hinv (n : ℕ) : MvPowerSeries.constantCoeff (S n) = 0 ∧
      (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) (S n) = a i) ∧
      ((n + 2 : ℕ) : ℕ∞) ≤ (defect f g (S n)).order := by
    induction n with
    | zero => exact hS₀ ▸ ⟨hL₀, hL₁, by simpa using hL⟩
    | succ n ih =>
      refine hS n ▸ ⟨by rw [map_add, ih.1, hΔ₀, add_zero], fun i ↦ ?_, hΔd n _ ih.1 ih.2.2⟩
      rw [map_add, ih.2.1, MvPowerSeries.coeff_of_lt_order ((hΔ n _).trans_lt'
        (by rw [Finsupp.degree_single]; exact_mod_cast (by omega : 1 < n + 2))), add_zero]
  refine exists_defect_eq_zero_of_stages hg.constantCoeff_eq_zero (fun n ↦ (hinv n).1)
    (fun n ↦ (hinv n).2.1) (fun n ↦ (hinv n).2.2) fun n ↦ ?_
  rw [hS, add_sub_cancel_left]
  exact (hΔ n _).trans' (by exact_mod_cast (by omega : n ≤ n + 2))

end Existence

/-- **Lubin–Tate interpolation** (LT65, Lemma 1 and the remarks after it). Let `O` be a discrete
valuation ring with finite residue field of cardinality `q`, `π` a uniformizer, `f` and `g`
Lubin–Tate series for `π` and `q`, and `K` a fraction field of `O`. For every finite family
`(aᵢ)` in `O` there is a unique `H ∈ O⟦Xᵢ⟧` with zero constant term and linear part `∑ aᵢ Xᵢ`
such that `f(H) = H(g(X₁), g(X₂), …)`, and every series over `K` with zero constant term, the same
linear part and the same functional equation for the images of `f` and `g` is the image of `H`.
-/
theorem exists_lubinTate_interpolation {O : Type*} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Finite (ResidueField O)] {π : O} (hπ : Irreducible π)
    {f g : O⟦X⟧} (hf : IsLubinTateSeries π (Nat.card (ResidueField O)) f)
    (hg : IsLubinTateSeries π (Nat.card (ResidueField O)) g)
    (K : Type*) [Field K] [Algebra O K] [IsFractionRing O K] (a : σ → O) :
    ∃ H : MvPowerSeries σ O,
      (MvPowerSeries.constantCoeff H = 0 ∧
        (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) H = a i) ∧
        f.subst H = H.subst fun i ↦ g.subst (MvPowerSeries.X i)) ∧
      (∀ H₁ : MvPowerSeries σ O, MvPowerSeries.constantCoeff H₁ = 0 →
        (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) H₁ = a i) →
        f.subst H₁ = H₁.subst (fun i ↦ g.subst (MvPowerSeries.X i)) → H₁ = H) ∧
      ∀ H' : MvPowerSeries σ K, MvPowerSeries.constantCoeff H' = 0 →
        (∀ i, MvPowerSeries.coeff (Finsupp.single i 1) H' = algebraMap O K (a i)) →
        (f.map (algebraMap O K)).subst H' =
          H'.subst (fun i ↦ (g.map (algebraMap O K)).subst (MvPowerSeries.X i)) →
        H' = MvPowerSeries.map (algebraMap O K) H := by
  have hπm := (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  obtain ⟨H, hH₀, hH₁, hH⟩ := exists_defect_eq_zero hπm hf hg a
  rw [defect, sub_eq_zero] at hH
  have hg₀ := hg.constantCoeff_eq_zero
  -- `π - πʳ = π (1 - πʳ⁻¹)` is a nonzero element of `O` for `r ≥ 2`
  have hne (r : ℕ) (hr : 2 ≤ r) : π - π ^ r ≠ 0 := by
    obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le' hr
    rw [show π - π ^ (s + 2) = π * (1 - π ^ (s + 1)) by ring]
    exact mul_ne_zero hπ.ne_zero
      (IsLocalRing.isUnit_one_sub_pow_of_mem_maximalIdeal
        (hπm ▸ Ideal.mem_span_singleton_self π) s.add_one_ne_zero).ne_zero
  refine ⟨H, ⟨hH₀, hH₁, hH⟩, fun H₁ h₀ h₁ h ↦ ?_, fun H' h₀ h₁ h ↦ ?_⟩
  · exact eq_of_lubinTate_functional_equation
      (fun r hr ↦ IsLeftCancelMulZero.mul_left_cancel_of_ne_zero (hne r hr))
      hf.coeff_one hg₀ hg.coeff_one h₀ hH₀ (fun i ↦ (h₁ i).trans (hH₁ i).symm) h hH
  -- the image of `H` solves the equation over `K`
  have hHK : (f.map (algebraMap O K)).subst (MvPowerSeries.map (algebraMap O K) H) =
      (MvPowerSeries.map (algebraMap O K) H).subst
        fun i ↦ (g.map (algebraMap O K)).subst (MvPowerSeries.X i) := by
    have hmap := congrArg (MvPowerSeries.map (algebraMap O K)) hH
    rw [PowerSeries.map_subst (.of_constantCoeff_zero hH₀),
      MvPowerSeries.map_subst (PowerSeries.hasSubst_subst_X hg₀)] at hmap
    simpa only [PowerSeries.map_subst (.X _), MvPowerSeries.map_X] using hmap
  refine eq_of_lubinTate_functional_equation (π := algebraMap O K π) (fun r hr ↦ ?_)
    (by rw [coeff_map, hf.coeff_one])
    (by rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply,
      hg₀, map_zero])
    (by rw [coeff_map, hg.coeff_one]) h₀ (by simp [hH₀]) (fun i ↦ by simp [h₁, hH₁]) h hHK
  rw [← map_pow, ← map_sub]
  exact IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
    ((map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr (hne r hr))

end Interpolation

end TauCeti
