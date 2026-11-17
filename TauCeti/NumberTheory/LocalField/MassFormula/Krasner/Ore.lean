/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.MassFormula.Eisenstein.Basic
public import TauCeti.NumberTheory.LocalField.NatCastValuation
import Mathlib.Data.ENat.Lattice
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Polynomial.GaussLemma
import TauCeti.Algebra.Polynomial.Degree.Operations
import TauCeti.RingTheory.DiscreteValuationRing.Basic
import TauCeti.RingTheory.Polynomial.Eisenstein.Basic
import TauCeti.RingTheory.Polynomial.Eisenstein.DiscreteValuationRing

/-!
# Ore's conditions and realizability of wild exponents

Let `K` be a nonarchimedean local field with ring of integers `𝒪[K]` and additive valuation
`v_K = IsDiscreteValuationRing.addVal 𝒪[K]`. For a totally ramified extension `L / K` of degree
`n > 0` inside a separable closure, the wild exponent `c(L) = d(L) - n + 1` satisfies **Ore's
conditions**: writing `j = a n + b` with `0 ≤ b < n`, either `b = 0` and `a = v_K(n)`, or `b > 0`,
`v_K(b) ≤ a`, and `a + 1 ≤ v_K(n)` (with `v_K(h) = ⊤` when `(h : K) = 0`). Conversely, every
natural number `j` satisfying Ore's conditions is realized as the wild exponent of some member of
`σ_K(n) = totallyRamifiedOfDegree K n`, in either characteristic.

The link between wild exponents and Eisenstein coefficients is the derivative formula for a monic
Eisenstein polynomial `f ∈ 𝒪[K][X]` of degree `n > 0`. Writing `t_0(f) = n · v_K(n)` and
`t_h(f) = n · (v_K(f_h) - 1 + v_K(h)) + h` for `0 < h < n`, any root `x` of `f` in the separable
closure generates `L = K⟮x⟯ ∈ σ_K(n)` with `c(L) = ⨅ k, t_k(f)`. Because the finite values of
`t_k(f)` lie in distinct residue classes modulo `n`, the infimum equals `j = a n + b` precisely
when `j` satisfies Ore's conditions, `v_K(f_b) = a + 1 - v_K(b)` when `b > 0`, and
`v_K(f_h) ≥ oreCoefficientDepth K n j h` for every `0 < h < n`, where
`oreCoefficientDepth K n j h = max 1 (a + 1 + [h < b] - v_K(h))` (and `1` when `(h : K) = 0`).

This characterization simultaneously yields the forward direction of Ore's realizability theorem,
the explicit trinomial/binomial witnesses `X ^ n + π ^ ν_b X ^ b + π` and `X ^ n - π` for the
converse, and the coefficient-box description of the discriminant strata used in Krasner's count.

## Main definitions

* `TauCeti.IsOreAdmissible K n j`: Ore's admissibility predicate on degree `n` and wild exponent
  `j`.
* `TauCeti.oreCoefficientDepth K n j h`: the coefficient valuation lower bound `ν_h` at index `h`.
* `TauCeti.oreDerivativeTerm K f n k`: the `k`-th term `t_k(f)` in the Eisenstein derivative
  infimum for the wild exponent.

## Main results

* `TauCeti.iInf_oreDerivativeTerm_eq_iff`: exact characterization of
  `⨅ k, oreDerivativeTerm K f n k = j` for a monic Eisenstein polynomial `f` of degree `n > 0`,
  valid over any field with a discrete valuation ring `𝒪[K]`.
* `TauCeti.natCast_wildExponent_adjoin_eq_iInf_of_eisenstein`: for a root `x` of a monic Eisenstein
  polynomial `f`, `c(K⟮x⟯) = ⨅ k, oreDerivativeTerm K f n k`.
* `TauCeti.wildExponent_adjoin_eq_iff_of_eisenstein`: characterization of `(K⟮x⟯).wildExponent = j`
  in terms of Ore admissibility and the valuations of the coefficients of `f`.
* `TauCeti.ore_realizability`: `∃ E ∈ totallyRamifiedOfDegree K n, E.wildExponent = j` if and only
  if `IsOreAdmissible K n j`.

## References

* Ø. Ore, *Bemerkungen zur Theorie der Differente*, Math. Z. **25** (1926), 1–8.
* M. Krasner, *Nombre des extensions d'un degré donné d'un corps 𝔭-adique*, in *Les Tendances
  Géom. en Algèbre et Théorie des Nombres*, Éditions du CNRS, Paris (1966), 143–169.
* S. Pauli and X.-F. Roblot, *On the computation of all extensions of a `p`-adic field of a given
  degree*, Math. Comp. **70** (2001), 1641–1659, Proposition 3.1.
-/

public section
noncomputable section

open ValuativeRel Polynomial IsDiscreteValuationRing
open scoped IntermediateField

namespace TauCeti

section DiscreteValuationRing

variable {K : Type*} [Field K] [ValuativeRel K] [IsDiscreteValuationRing 𝒪[K]]

variable (K) in
/-- **Ore's conditions** on degree `n` and wild exponent `j`: `0 < n` and, writing `j = a n + b`
with `0 ≤ b < n`, either `b = 0` and `a = v_K(n)`, or `b > 0`, `v_K(b) ≤ a`, and
`a + 1 ≤ v_K(n)` in `ℕ∞`, where `v_K(h) = addVal 𝒪[K] (h : 𝒪[K])` takes the value `⊤` when
`(h : K) = 0`. -/
def IsOreAdmissible (n j : ℕ) : Prop :=
  0 < n ∧
    ((j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] (n : 𝒪[K])) ∨
      (0 < j % n ∧ addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) ∧
        ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (n : 𝒪[K])))

/-- Unfolding `IsOreAdmissible`. -/
theorem isOreAdmissible_iff {n j : ℕ} :
    IsOreAdmissible K n j ↔
      0 < n ∧
        ((j % n = 0 ∧ ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] (n : 𝒪[K])) ∨
          (0 < j % n ∧ addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) ∧
            ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (n : 𝒪[K]))) :=
  Iff.rfl

/-- An Ore-admissible degree is positive. -/
theorem IsOreAdmissible.pos {n j : ℕ} (h : IsOreAdmissible K n j) : 0 < n :=
  h.1

/-- No wild exponent is Ore-admissible in degree zero. -/
@[simp]
theorem not_isOreAdmissible_zero (j : ℕ) : ¬ IsOreAdmissible K 0 j :=
  fun h ↦ h.1.false

/-- In degree one, the unique Ore-admissible wild exponent is `0`. -/
@[simp]
theorem isOreAdmissible_one_iff {j : ℕ} : IsOreAdmissible K 1 j ↔ j = 0 := by
  simp [IsOreAdmissible, Nat.mod_one]

/-- Ore's admissibility condition when `n ∣ j` (equivalently `j % n = 0`): for `0 < n`, it holds
precisely when `j / n = v_K(n)`. -/
theorem isOreAdmissible_iff_of_mod_eq_zero {n j : ℕ} (hn : 0 < n) (hmod : j % n = 0) :
    IsOreAdmissible K n j ↔ ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] (n : 𝒪[K]) := by
  simp [IsOreAdmissible, hn, hmod]

/-- Ore's admissibility condition when `0 < j % n`: for `0 < n`, it holds precisely when
`v_K(j % n) ≤ j / n` and `j / n + 1 ≤ v_K(n)`. -/
theorem isOreAdmissible_iff_of_mod_pos {n j : ℕ} (hn : 0 < n) (hmod : 0 < j % n) :
    IsOreAdmissible K n j ↔
      addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) ∧
        ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (n : 𝒪[K]) := by
  simp [IsOreAdmissible, hn, hmod, hmod.ne']

variable (K) in
/-- The coefficient valuation lower bound `ν_h` at index `h` in the Ore discriminant box:
`max 1 (j / n + 1 + [h < j % n] - v_K(h))`, taking the value `1` when `(h : K) = 0` (in particular
at `h = 0`). -/
def oreCoefficientDepth (n j h : ℕ) : ℕ :=
  max 1 ((((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) -
    addVal 𝒪[K] (h : 𝒪[K])).toNat)

/-- Unfolding `oreCoefficientDepth`. -/
theorem oreCoefficientDepth_def (n j h : ℕ) :
    oreCoefficientDepth K n j h =
      max 1 ((((j / n + 1 + if h < j % n then 1 else 0 : ℕ) : ℕ∞) -
        addVal 𝒪[K] (h : 𝒪[K])).toNat) := by
  rw [oreCoefficientDepth]

/-- Every coefficient depth in the Ore discriminant box is at least `1`. -/
theorem one_le_oreCoefficientDepth (n j h : ℕ) : 1 ≤ oreCoefficientDepth K n j h :=
  le_max_left _ _

/-- At index `h = 0`, the coefficient depth is `1`. -/
@[simp]
theorem oreCoefficientDepth_zero (n j : ℕ) : oreCoefficientDepth K n j 0 = 1 := by
  simp [oreCoefficientDepth]

/-- An index `h` vanishing in `K` imposes no derivative constraint, so its depth is `1`. -/
theorem oreCoefficientDepth_eq_one_of_natCast_eq_zero {n j h : ℕ} (hh : (h : K) = 0) :
    oreCoefficientDepth K n j h = 1 := by
  have h𝒪 : (h : 𝒪[K]) = 0 := Subtype.ext (by simpa using hh)
  simp [oreCoefficientDepth, h𝒪]

/-- Upper bound `ν_h ≤ j / n + 1 + [h < j % n]` on each coefficient depth. -/
theorem oreCoefficientDepth_le (n j h : ℕ) :
    oreCoefficientDepth K n j h ≤ j / n + 1 + if h < j % n then 1 else 0 := by
  rw [oreCoefficientDepth]
  refine max_le (Nat.le_trans (Nat.le_add_left 1 _) (Nat.le_add_right _ _)) ?_
  cases hv : addVal 𝒪[K] (h : 𝒪[K]) with
  | top => simp
  | coe v =>
    rw [← ENat.natCast_sub, ENat.toNat_natCast]
    exact Nat.sub_le _ _

/-- When `IsOreAdmissible K n j` and `b = j % n > 0`, the coefficient depth at `b` satisfies
`ν_b + v_K(b) = j / n + 1` in `ℕ∞`. -/
theorem oreCoefficientDepth_mod_add_addVal {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hb : 0 < j % n) :
    (oreCoefficientDepth K n j (j % n) : ℕ∞) + addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) =
      ((j / n + 1 : ℕ) : ℕ∞) := by
  have hle : addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) :=
    ((isOreAdmissible_iff_of_mod_pos hadm.pos hb).1 hadm).1
  cases hv : addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) with
  | top => exact absurd (hv ▸ hle) (not_le_of_gt (ENat.natCast_lt_top _))
  | coe v =>
    rw [hv] at hle
    have hvle : v ≤ j / n := by exact_mod_cast hle
    rw [oreCoefficientDepth, hv]
    simp only [lt_self_iff_false, ↓reduceIte, add_zero, ← ENat.natCast_sub, ENat.toNat_natCast]
    have hmax : max 1 (j / n + 1 - v) = j / n + 1 - v := max_eq_right (by omega)
    rw [hmax]
    exact_mod_cast Nat.sub_add_cancel (by omega : v ≤ j / n + 1)

/-- For an Ore-admissible pair `(n, j)`, the sum of the interior coefficient depths satisfies
`∑_{h=1}^{n-1} ν_h ≤ n + j - 1` when `j % n = 0` and `≤ n + j - 2` when `0 < j % n`, showing that
the exponent in Krasner's formula is always nonnegative. -/
theorem sum_oreCoefficientDepth_le {n j : ℕ} (hadm : IsOreAdmissible K n j) :
    ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤
      n + j - if j % n = 0 then 1 else 2 := by
  have hn := hadm.pos
  have hdiv : j = n * (j / n) + j % n := (Nat.div_add_mod j n).symm
  have hmodlt : j % n < n := Nat.mod_lt j hn
  have hbound : ∑ h ∈ Finset.Ico 1 n, oreCoefficientDepth K n j h ≤
      ∑ h ∈ Finset.Ico 1 n, (j / n + 1 + if h < j % n then 1 else 0) :=
    Finset.sum_le_sum fun h _ ↦ oreCoefficientDepth_le n j h
  rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, smul_eq_mul, Finset.sum_boole,
    Nat.cast_id] at hbound
  have hfilt : (Finset.Ico 1 n).filter (fun h ↦ h < j % n) = Finset.Ico 1 (j % n) := by
    ext h
    simp only [Finset.mem_filter, Finset.mem_Ico]
    omega
  rw [hfilt, Nat.card_Ico] at hbound
  have h1 : (n - 1) * (j / n + 1) = (n - 1) * (j / n) + (n - 1) := by ring
  have h2 : n * (j / n) = (n - 1) * (j / n) + j / n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hn]
  rw [h1] at hbound
  rw [h2] at hdiv
  clear h1 h2
  generalize (n - 1) * (j / n) = P at hbound hdiv
  generalize j / n = q at hbound hdiv
  split_ifs with h0 <;> omega

/-! ### The Eisenstein derivative infimum -/

variable (K) in
/-- The `k`-th term of the derivative infimum for the wild exponent of a monic Eisenstein
polynomial `f` of degree `n`: `t_0(f) = n • v_K(n)` and
`t_h(f) = n • (v_K(f_h) - 1 + v_K(h)) + h` for `0 < h < n`. -/
def oreDerivativeTerm (f : 𝒪[K][X]) (n : ℕ) (k : Fin n) : ℕ∞ :=
  if k.1 = 0 then
    n • addVal 𝒪[K] (n : 𝒪[K])
  else
    n • (addVal 𝒪[K] (f.coeff k.1) - 1 + addVal 𝒪[K] (k.1 : 𝒪[K])) + (k.1 : ℕ)

/-- At index `0`, the derivative infimum term is `n • v_K(n)`. -/
@[simp]
theorem oreDerivativeTerm_zero {n : ℕ} (hn : 0 < n) (f : 𝒪[K][X]) :
    oreDerivativeTerm K f n ⟨0, hn⟩ = n • addVal 𝒪[K] (n : 𝒪[K]) := by
  simp [oreDerivativeTerm]

/-- At a positive index `0 < k < n`, the derivative infimum term is
`n • (v_K(f_k) - 1 + v_K(k)) + k`. -/
theorem oreDerivativeTerm_of_pos {n : ℕ} (f : 𝒪[K][X]) {k : Fin n} (hk : 0 < k.1) :
    oreDerivativeTerm K f n k =
      n • (addVal 𝒪[K] (f.coeff k.1) - 1 + addVal 𝒪[K] (k.1 : 𝒪[K])) + (k.1 : ℕ) := by
  rw [oreDerivativeTerm, ite_eq_right hk.ne']

/-- Every finite value of `oreDerivativeTerm K f n k` is congruent to `k` modulo `n`. -/
private theorem mod_eq_of_oreDerivativeTerm_eq {f : 𝒪[K][X]} {n j : ℕ} {k : Fin n}
    (hk : oreDerivativeTerm K f n k = (j : ℕ∞)) : j % n = k.1 := by
  have hn : n ≠ 0 := (Fin.pos k).ne'
  rw [oreDerivativeTerm] at hk
  split_ifs at hk with h0
  · cases hv : addVal 𝒪[K] (n : 𝒪[K]) with
    | top => simp [hv, hn] at hk
    | coe v =>
      rw [hv, nsmul_eq_mul, ← Nat.cast_mul] at hk
      have hj : n * v = j := by exact_mod_cast hk
      rw [← hj, Nat.mul_mod_right, h0]
  · cases hv : addVal 𝒪[K] (f.coeff k.1) - 1 + addVal 𝒪[K] (k.1 : 𝒪[K]) with
    | top => simp [hv, hn] at hk
    | coe v =>
      rw [hv, nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add] at hk
      have hj : n * v + k.1 = j := by exact_mod_cast hk
      rw [← hj, Nat.mul_add_mod, Nat.mod_eq_of_lt k.isLt]

/-- Equivalence `(j : ℕ∞) ≤ n • x` with `a + 1 ≤ x` when `0 < j % n`. -/
private theorem le_nsmul_iff_of_mod_pos {n j : ℕ} (hn : 0 < n) (hb : 0 < j % n) (x : ℕ∞) :
    (j : ℕ∞) ≤ n • x ↔ ((j / n : ℕ) : ℕ∞) + 1 ≤ x := by
  have hdiv : j = n * (j / n) + j % n := (Nat.div_add_mod j n).symm
  have hlt : j % n < n := Nat.mod_lt j hn
  cases x with
  | top => simp [hn.ne']
  | coe v =>
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_le, Nat.cast_le]
    constructor
    · intro h
      by_contra hltv
      have hv : v ≤ j / n := by omega
      have := Nat.mul_le_mul_left n hv
      omega
    · intro h
      have := Nat.mul_le_mul_left n h
      have hmul : n * (j / n + 1) = n * (j / n) + n := by ring
      omega

/-- Equivalence `(j : ℕ∞) ≤ n • y + h` with `j / n + [h < j % n] ≤ y` for `h < n`. -/
private theorem le_nsmul_add_iff {n j h : ℕ} (hn : 0 < n) (hh : h < n) (y : ℕ∞) :
    (j : ℕ∞) ≤ n • y + (h : ℕ) ↔ ((j / n + if h < j % n then 1 else 0 : ℕ) : ℕ∞) ≤ y := by
  have hdiv : j = n * (j / n) + j % n := (Nat.div_add_mod j n).symm
  have hlt : j % n < n := Nat.mod_lt j hn
  cases y with
  | top => simp [hn.ne']
  | coe v =>
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.cast_le, Nat.cast_le]
    split_ifs with hhb
    · constructor
      · intro hle
        by_contra hltv
        have hv : v ≤ j / n := by omega
        have := Nat.mul_le_mul_left n hv
        omega
      · intro hle
        have := Nat.mul_le_mul_left n hle
        have hmul : n * (j / n + 1) = n * (j / n) + n := by ring
        omega
    · constructor
      · intro hle
        by_contra hltv
        have hv : v + 1 ≤ j / n := by omega
        have := Nat.mul_le_mul_left n hv
        have hmul : n * (v + 1) = n * v + n := by ring
        omega
      · intro hle
        rw [add_zero] at hle
        have := Nat.mul_le_mul_left n hle
        omega

/-- For `1 ≤ c`, the derivative lower bound `(j : ℕ∞) ≤ n • (c - 1 + v_K(h)) + h` is equivalent
to `(oreCoefficientDepth K n j h : ℕ∞) ≤ c`. -/
private theorem le_oreDerivativeTerm_iff {f : 𝒪[K][X]} {n j : ℕ} {k : Fin n} (hk0 : 0 < k.1)
    (hc : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff k.1)) :
    (j : ℕ∞) ≤ oreDerivativeTerm K f n k ↔
      (oreCoefficientDepth K n j k.1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff k.1) := by
  have hn : 0 < n := Nat.lt_trans hk0 k.isLt
  rw [oreDerivativeTerm, ite_eq_right (fun h ↦ absurd h hk0.ne'), le_nsmul_add_iff hn k.isLt]
  set m := j / n + if k.1 < j % n then 1 else 0
  have hm : j / n + 1 + (if k.1 < j % n then 1 else 0) = m + 1 := by
    dsimp only [m]
    split_ifs <;> omega
  rw [oreCoefficientDepth, hm]
  cases hv : addVal 𝒪[K] (k.1 : 𝒪[K]) with
  | top => simp [hc]
  | coe v =>
    cases hcv : addVal 𝒪[K] (f.coeff k.1) with
    | top => simp
    | coe c =>
      rw [hcv] at hc
      have hc1 : 1 ≤ c := by exact_mod_cast hc
      rw [← Nat.cast_one, ← ENat.natCast_sub, ← Nat.cast_add, Nat.cast_le, ← ENat.natCast_sub,
        ENat.toNat_natCast, Nat.cast_le]
      omega

/-- At `k = ⟨j % n, _⟩` with `0 < j % n` and `1 ≤ c`, `oreDerivativeTerm K f n k = j` holds
precisely when `v_K(j % n) ≤ j / n` and `c = oreCoefficientDepth K n j (j % n)`. -/
private theorem oreDerivativeTerm_mod_eq_iff {f : 𝒪[K][X]} {n j : ℕ} (hn : 0 < n)
    (hb : 0 < j % n) (hc : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff (j % n))) :
    oreDerivativeTerm K f n ⟨j % n, Nat.mod_lt j hn⟩ = (j : ℕ∞) ↔
      addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) ≤ ((j / n : ℕ) : ℕ∞) ∧
        addVal 𝒪[K] (f.coeff (j % n)) = (oreCoefficientDepth K n j (j % n) : ℕ∞) := by
  have hdiv : j = n * (j / n) + j % n := (Nat.div_add_mod j n).symm
  rw [oreDerivativeTerm, ite_eq_right (fun h ↦ absurd h hb.ne'), oreCoefficientDepth]
  simp only [lt_self_iff_false, ↓reduceIte, add_zero]
  cases hv : addVal 𝒪[K] ((j % n : ℕ) : 𝒪[K]) with
  | top => simp [hn.ne']
  | coe v =>
    cases hcv : addVal 𝒪[K] (f.coeff (j % n)) with
    | top => simp [hn.ne']
    | coe c =>
      rw [hcv] at hc
      have hc1 : 1 ≤ c := by exact_mod_cast hc
      rw [← Nat.cast_one, ← ENat.natCast_sub, ← Nat.cast_add, nsmul_eq_mul, ← Nat.cast_mul,
        ← Nat.cast_add, ← ENat.natCast_sub, ENat.toNat_natCast, Nat.cast_inj, Nat.cast_le,
        Nat.cast_inj]
      constructor
      · intro h
        have hsum : c - 1 + v = j / n := by nlinarith
        exact ⟨by omega, by omega⟩
      · rintro ⟨hvle, hceq⟩
        have hmax : max 1 (j / n + 1 - v) = j / n + 1 - v := max_eq_right (by omega)
        rw [hmax] at hceq
        have hsum : c - 1 + v = j / n := by omega
        rw [hsum, ← hdiv]

/-- **Master Eisenstein derivative characterization**: for a polynomial `f ∈ 𝒪[K][X]` of positive
degree `n` whose coefficients of degree `1 ≤ h < n` lie in `𝓂[K]` (in particular, any Eisenstein
polynomial of degree `n > 0`), the derivative infimum `⨅ k, oreDerivativeTerm K f n k` equals `j`
if and only if `IsOreAdmissible K n j`, the `b`-th coefficient has exact valuation
`oreCoefficientDepth K n j b` whenever `b = j % n > 0`, and every interior coefficient `f_h`
(`0 < h < n`) has valuation at least `oreCoefficientDepth K n j h`. -/
theorem iInf_oreDerivativeTerm_eq_iff {f : 𝒪[K][X]} {n j : ℕ} (hn : 0 < n)
    (hmem : ∀ h : Fin n, 0 < h.1 → f.coeff h.1 ∈ 𝓂[K]) :
    (⨅ k : Fin n, oreDerivativeTerm K f n k) = (j : ℕ∞) ↔
      IsOreAdmissible K n j ∧
        (0 < j % n →
          addVal 𝒪[K] (f.coeff (j % n)) = (oreCoefficientDepth K n j (j % n) : ℕ∞)) ∧
        (∀ h : Fin n, 0 < h.1 →
          (oreCoefficientDepth K n j h.1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h.1)) := by
  have hc (h : Fin n) (hh : 0 < h.1) : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h.1) := by
    have h1 := TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal.mp
      ((pow_one 𝓂[K]).symm ▸ hmem h hh)
    simpa using h1
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hiInf : (⨅ k : Fin n, oreDerivativeTerm K f n k) = (j : ℕ∞) ↔
      oreDerivativeTerm K f n ⟨j % n, Nat.mod_lt j hn⟩ = (j : ℕ∞) ∧
        ∀ k : Fin n, (j : ℕ∞) ≤ oreDerivativeTerm K f n k := by
    constructor
    · intro h
      obtain ⟨k, hk⟩ := exists_eq_ciInf_of_finite (f := oreDerivativeTerm K f n)
      have hkj : oreDerivativeTerm K f n k = (j : ℕ∞) := hk.trans h
      have hkeq : k = ⟨j % n, Nat.mod_lt j hn⟩ :=
        Fin.ext (mod_eq_of_oreDerivativeTerm_eq hkj).symm
      exact ⟨hkeq ▸ hkj, fun m ↦ h ▸ iInf_le _ m⟩
    · rintro ⟨heq, hle⟩
      exact le_antisymm (iInf_le_of_le ⟨j % n, Nat.mod_lt j hn⟩ heq.le) (le_iInf hle)
  rw [hiInf]
  rcases Nat.eq_zero_or_pos (j % n) with hb0 | hbpos
  · have ht0 : oreDerivativeTerm K f n ⟨j % n, Nat.mod_lt j hn⟩ = (j : ℕ∞) ↔
        ((j / n : ℕ) : ℕ∞) = addVal 𝒪[K] (n : 𝒪[K]) := by
      simp only [oreDerivativeTerm, hb0, ↓reduceIte]
      have hdiv : n * (j / n) = j := by have := Nat.div_add_mod j n; omega
      cases hv : addVal 𝒪[K] (n : 𝒪[K]) with
      | top => simp [hn.ne']
      | coe v =>
        rw [nsmul_eq_mul, ← Nat.cast_mul, Nat.cast_inj, Nat.cast_inj]
        exact ⟨fun h ↦ by nlinarith, fun h ↦ by rw [← h, hdiv]⟩
    rw [isOreAdmissible_iff_of_mod_eq_zero hn hb0, ht0]
    refine ⟨fun ⟨ha, hle⟩ ↦ ⟨ha, fun h ↦ absurd h (by omega), fun h hh ↦
      (le_oreDerivativeTerm_iff hh (hc h hh)).1 (hle h)⟩,
      fun ⟨ha, _, hbounds⟩ ↦ ⟨ha, fun k ↦ ?_⟩⟩
    rcases Nat.eq_zero_or_pos k.1 with hk0 | hkpos
    · have hk : k = ⟨j % n, Nat.mod_lt j hn⟩ := Fin.ext (hk0.trans hb0.symm)
      rw [hk, ht0.2 ha]
    · exact (le_oreDerivativeTerm_iff hkpos (hc k hkpos)).2 (hbounds k hkpos)
  · have htb := oreDerivativeTerm_mod_eq_iff hn hbpos (hc ⟨j % n, Nat.mod_lt j hn⟩ hbpos)
    have ht0 : (j : ℕ∞) ≤ oreDerivativeTerm K f n ⟨0, hn⟩ ↔
        ((j / n : ℕ) : ℕ∞) + 1 ≤ addVal 𝒪[K] (n : 𝒪[K]) := by
      simp only [oreDerivativeTerm, ↓reduceIte]
      exact le_nsmul_iff_of_mod_pos hn hbpos _
    rw [isOreAdmissible_iff_of_mod_pos hn hbpos, htb]
    constructor
    · rintro ⟨⟨hvle, hceq⟩, hle⟩
      exact ⟨⟨hvle, ht0.1 (hle ⟨0, hn⟩)⟩, fun _ ↦ hceq,
        fun h hh ↦ (le_oreDerivativeTerm_iff hh (hc h hh)).1 (hle h)⟩
    · rintro ⟨⟨hvle, hnle⟩, hceq, hbounds⟩
      refine ⟨⟨hvle, hceq hbpos⟩, fun k ↦ ?_⟩
      rcases Nat.eq_zero_or_pos k.1 with hk0 | hkpos
      · have hk : k = ⟨0, hn⟩ := Fin.ext hk0
        rw [hk]
        exact ht0.2 hnle
      · exact (le_oreDerivativeTerm_iff hkpos (hc k hkpos)).2 (hbounds k hkpos)

/-- Finiteness of a single term `oreDerivativeTerm K f n k` is equivalent to nonvanishing of the
corresponding derivative coefficient. -/
private theorem oreDerivativeTerm_ne_top_iff {f : 𝒪[K][X]} {n : ℕ} (hn : 0 < n) (k : Fin n) :
    oreDerivativeTerm K f n k ≠ ⊤ ↔
      if k.1 = 0 then (n : 𝒪[K]) ≠ 0 else f.coeff k.1 * (k.1 : 𝒪[K]) ≠ 0 := by
  rw [oreDerivativeTerm]
  split_ifs with h0
  · cases hv : addVal 𝒪[K] (n : 𝒪[K]) with
    | top =>
      have hzero : (n : 𝒪[K]) = 0 := addVal_eq_top_iff.1 hv
      simp [hn.ne', hzero]
    | coe v =>
      have hnz : (n : 𝒪[K]) ≠ 0 := fun h ↦ by simp [h] at hv
      rw [nsmul_eq_mul, ← Nat.cast_mul]
      exact iff_of_true (ENat.natCast_ne_top _) hnz
  · cases hcv : addVal 𝒪[K] (f.coeff k.1) with
    | top =>
      have hzero : f.coeff k.1 = 0 := addVal_eq_top_iff.1 hcv
      simp [hn.ne', hzero]
    | coe c =>
      have hcnz : f.coeff k.1 ≠ 0 := fun h ↦ by simp [h] at hcv
      cases hkv : addVal 𝒪[K] (k.1 : 𝒪[K]) with
      | top =>
        have hzero : (k.1 : 𝒪[K]) = 0 := addVal_eq_top_iff.1 hkv
        simp [hn.ne', hzero]
      | coe v =>
        have hknz : (k.1 : 𝒪[K]) ≠ 0 := fun h ↦ by simp [h] at hkv
        rw [← Nat.cast_one, ← ENat.natCast_sub, ← Nat.cast_add, nsmul_eq_mul, ← Nat.cast_mul,
          ← Nat.cast_add]
        exact iff_of_true (ENat.natCast_ne_top _) (mul_ne_zero hcnz hknz)

/-- For a monic polynomial `f ∈ 𝒪[K][X]` of positive degree `n`, the derivative of `f` over `K` is
nonzero if and only if the infimum of `oreDerivativeTerm K f n` is finite. -/
theorem derivative_map_ne_zero_iff_iInf_oreDerivativeTerm_ne_top {f : 𝒪[K][X]} {n : ℕ}
    (hfmon : f.Monic) (hdeg : f.natDegree = n) (hn : 0 < n) :
    derivative (f.map (algebraMap 𝒪[K] K)) ≠ 0 ↔
      (⨅ k : Fin n, oreDerivativeTerm K f n k) ≠ ⊤ := by
  conv_rhs => rw [ne_eq, iInf_eq_top]
  push Not
  simp only [oreDerivativeTerm_ne_top_iff hn]
  constructor
  · intro hne
    have hex : ∃ i, (derivative (f.map (algebraMap 𝒪[K] K))).coeff i ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (by ext i; simpa using h i)
    obtain ⟨i, hi⟩ := hex
    rw [coeff_derivative, coeff_map] at hi
    have hilt : i < n := by
      by_contra hge
      have hgt : f.natDegree < i + 1 := by omega
      rw [coeff_eq_zero_of_natDegree_lt hgt, map_zero, zero_mul] at hi
      exact hi rfl
    rcases (Nat.add_one_le_iff.mpr hilt).lt_or_eq with hlt | heq
    · refine ⟨⟨i + 1, hlt⟩, ?_⟩
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      intro hzero
      apply hi
      simpa [map_mul, map_natCast] using congrArg (algebraMap 𝒪[K] K) hzero
    · refine ⟨⟨0, hn⟩, ?_⟩
      simp only [↓reduceIte]
      intro hzero
      apply hi
      have hlead : f.coeff (i + 1) = 1 := by rw [heq, ← hdeg]; exact hfmon.leadingCoeff
      have hnat : ((i + 1 : ℕ) : K) = 0 := by
        rw [heq]
        simpa using congrArg (algebraMap 𝒪[K] K) hzero
      rw [hlead, map_one, one_mul]
      exact_mod_cast hnat
  · rintro ⟨k, hk⟩ hzero
    split_ifs at hk with h0
    · have hcoeff := congrArg (fun p : K[X] ↦ p.coeff (n - 1)) hzero
      rw [coeff_derivative, coeff_zero, coeff_map, Nat.sub_add_cancel hn] at hcoeff
      have hlead : f.coeff n = 1 := by rw [← hdeg]; exact hfmon.leadingCoeff
      rw [hlead, map_one, one_mul] at hcoeff
      have hnK : (n : K) = 0 := by
        rw [← Nat.sub_add_cancel hn, Nat.cast_add, Nat.cast_one]
        exact hcoeff
      exact hk (Subtype.ext (by simpa using hnK))
    · have hkpos : 0 < k.1 := Nat.pos_of_ne_zero h0
      have hcoeff := congrArg (fun p : K[X] ↦ p.coeff (k.1 - 1)) hzero
      rw [coeff_derivative, coeff_zero, coeff_map, Nat.sub_add_cancel hkpos,
        Algebra.algebraMap_ofSubsemiring_apply, ← Nat.cast_one (R := K), ← Nat.cast_add,
        Nat.sub_add_cancel hkpos] at hcoeff
      exact hk (Subtype.ext (by simpa using hcoeff))

end DiscreteValuationRing

/-! ### Local-field specialization and Ore's realizability theorem -/

section LocalField

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- When `(h : K) ≠ 0`, `oreCoefficientDepth` agrees with the explicit formula in terms of
`natCastValuation`. -/
theorem oreCoefficientDepth_of_natCast_ne_zero {n j h : ℕ} (hh : (h : K) ≠ 0) :
    oreCoefficientDepth K n j h =
      max 1 (j / n + 1 + (if h < j % n then 1 else 0) - natCastValuation K h hh) := by
  rw [oreCoefficientDepth, TauCeti.IsDiscreteValuationRing.addVal_natCast K h hh,
    ← ENat.natCast_sub, ENat.toNat_natCast]

/-- When `(n : K) ≠ 0`, every Ore-admissible wild exponent satisfies `j ≤ n * v_K(n)`. -/
theorem IsOreAdmissible.le_mul_natCastValuation {n j : ℕ} (hadm : IsOreAdmissible K n j)
    (hnK : (n : K) ≠ 0) : j ≤ n * natCastValuation K n hnK := by
  have hdiv : j = n * (j / n) + j % n := (Nat.div_add_mod j n).symm
  have hlt : j % n < n := Nat.mod_lt j hadm.pos
  rcases hadm.2 with ⟨hb0, ha⟩ | ⟨_, _, ha⟩
  · rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K n hnK, Nat.cast_inj] at ha
    rw [hdiv, hb0, ha, add_zero]
  · rw [TauCeti.IsDiscreteValuationRing.addVal_natCast K n hnK, ← Nat.cast_one, ← Nat.cast_add,
      Nat.cast_le] at ha
    nlinarith

/-- Cyclic successor permutation on `Fin n`, sending `i` to `(i + 1) % n`. -/
private def finSuccModEquiv {n : ℕ} (hn : 0 < n) : Fin n ≃ Fin n where
  toFun i := ⟨(i.1 + 1) % n, Nat.mod_lt _ hn⟩
  invFun k := if k.1 = 0 then ⟨n - 1, Nat.sub_lt hn zero_lt_one⟩ else ⟨k.1 - 1, by omega⟩
  left_inv i := by
    ext
    rcases (Nat.add_one_le_iff.mpr i.isLt).lt_or_eq with hlt | heq
    · have hmod : (i.1 + 1) % n = i.1 + 1 := Nat.mod_eq_of_lt hlt
      simp [hmod]
    · have hmod : (i.1 + 1) % n = 0 := by rw [heq, Nat.mod_self]
      simp only [hmod, ↓reduceIte]
      omega
  right_inv k := by
    ext
    dsimp only
    split_ifs with h0
    · simp only [h0]
      rw [Nat.sub_add_cancel (by omega : 1 ≤ n), Nat.mod_self]
    · have hkpos : 0 < k.1 := Nat.pos_of_ne_zero h0
      simp [Nat.sub_add_cancel hkpos, Nat.mod_eq_of_lt k.isLt]

/-- For a root `x` in the separable closure of a monic Eisenstein polynomial `f ∈ 𝒪[K][X]` of
positive degree `n`, the wild exponent of `K⟮x⟯` is `⨅ k : Fin n, oreDerivativeTerm K f n k`. -/
theorem natCast_wildExponent_adjoin_eq_iInf_of_eisenstein {f : 𝒪[K][X]} {n : ℕ}
    (hfmon : f.Monic) (hf : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) (hn : 0 < n)
    {x : SeparableClosure K} (hx : aeval x (f.map (algebraMap 𝒪[K] K)) = 0) :
    ((K⟮x⟯).wildExponent : ℕ∞) = ⨅ k : Fin n, oreDerivativeTerm K f n k := by
  have hmem := adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hf hdeg hx
  have hwc := IntermediateField.wildExponent_add_eq_discriminantExponent_add_one hmem
  have hd := natCast_discriminantExponent_adjoin_eq_iInf_of_eisenstein hf hx
  -- Shift by `n` in `ℕ∞` to compare with `discriminantExponent + 1`.
  have hshift : ((K⟮x⟯).wildExponent : ℕ∞) + (n : ℕ) =
      (⨅ k : Fin n, oreDerivativeTerm K f n k) + (n : ℕ) := by
    rw [← Nat.cast_add, hwc, Nat.cast_add, Nat.cast_one, hd]
    subst hdeg
    let σ := finSuccModEquiv hn
    have hterm (i : Fin f.natDegree) :
        f.natDegree • addVal 𝒪[K] (f.coeff (i + 1) * (i + 1)) + (i : ℕ) + 1 =
          oreDerivativeTerm K f f.natDegree (σ i) + (f.natDegree : ℕ) := by
      rcases (Nat.add_one_le_iff.mpr i.isLt).lt_or_eq with hlt | heq
      · have hσ : (σ i).1 = i.1 + 1 := Nat.mod_eq_of_lt hlt
        have hc1 : (1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff (i.1 + 1)) := by
          have h1 := TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal.mp
            ((pow_one 𝓂[K]).symm ▸ hf.mem hlt)
          simpa using h1
        have hsub : 1 + (addVal 𝒪[K] (f.coeff (i.1 + 1)) - 1) =
            addVal 𝒪[K] (f.coeff (i.1 + 1)) := add_tsub_cancel_of_le hc1
        rw [oreDerivativeTerm, ite_eq_right (fun h ↦ by omega), hσ, AddValuation.map_mul,
          ← Nat.cast_add_one]
        conv_lhs => rw [← hsub]
        simp only [nsmul_eq_mul, mul_add, mul_one, Nat.cast_add, Nat.cast_one]
        simp only [add_assoc, add_left_comm, add_comm]
      · have hσ : (σ i).1 = 0 := by simp [σ, finSuccModEquiv, heq]
        have hlead : f.coeff (i.1 + 1) = 1 := by rw [heq]; exact hfmon.leadingCoeff
        simp only [oreDerivativeTerm, hσ, ↓reduceIte]
        rw [hlead, one_mul, ← Nat.cast_add_one, heq, add_assoc, ← Nat.cast_one, ← Nat.cast_add,
          heq]
    rw [ENat.iInf_add, ENat.iInf_add]
    exact Equiv.iInf_congr σ fun i ↦ (hterm i).symm
  exact WithTop.add_right_cancel (ENat.natCast_ne_top n) hshift

/-- Characterization of `(K⟮x⟯).wildExponent = j` for a root `x` of a monic Eisenstein polynomial
`f ∈ 𝒪[K][X]` of degree `n > 0`: it holds if and only if `IsOreAdmissible K n j`, the `j % n`-th
coefficient has exact valuation `oreCoefficientDepth K n j (j % n)` when `0 < j % n`, and every
interior coefficient has valuation at least `oreCoefficientDepth K n j h`. -/
theorem wildExponent_adjoin_eq_iff_of_eisenstein {f : 𝒪[K][X]} {n j : ℕ}
    (hfmon : f.Monic) (hf : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) (hn : 0 < n)
    {x : SeparableClosure K} (hx : aeval x (f.map (algebraMap 𝒪[K] K)) = 0) :
    (K⟮x⟯).wildExponent = j ↔
      IsOreAdmissible K n j ∧
        (0 < j % n →
          addVal 𝒪[K] (f.coeff (j % n)) = (oreCoefficientDepth K n j (j % n) : ℕ∞)) ∧
        (∀ h : Fin n, 0 < h.1 →
          (oreCoefficientDepth K n j h.1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h.1)) := by
  rw [← Nat.cast_inj (R := ℕ∞),
    natCast_wildExponent_adjoin_eq_iInf_of_eisenstein hfmon hf hdeg hn hx,
    iInf_oreDerivativeTerm_eq_iff hn fun h _ ↦ hf.mem (lt_of_lt_of_eq h.isLt hdeg.symm)]

/-- A monic Eisenstein polynomial over `𝒪[K]` of positive degree whose image over `K` has nonzero
derivative is separable over `K` and has a root in `SeparableClosure K`. -/
private theorem exists_root_of_eisenstein_derivative_ne_zero {f : 𝒪[K][X]} {n : ℕ}
    (hfmon : f.Monic) (hf : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n) (hn : 0 < n)
    (hderiv : derivative (f.map (algebraMap 𝒪[K] K)) ≠ 0) :
    ∃ x : SeparableClosure K, aeval x (f.map (algebraMap 𝒪[K] K)) = 0 := by
  have hirr : Irreducible (f.map (algebraMap 𝒪[K] K)) :=
    hfmon.irreducible_iff_irreducible_map_fraction_map.mp
      (hf.irreducible (Ideal.IsMaximal.isPrime inferInstance) hfmon.isPrimitive (hdeg ▸ hn))
  have hsep : (f.map (algebraMap 𝒪[K] K)).Separable :=
    (Polynomial.separable_iff_derivative_ne_zero hirr).mpr hderiv
  set g := (f.map (algebraMap 𝒪[K] K)).map (algebraMap K (SeparableClosure K))
  have hgdeg : g.degree ≠ 0 := by
    rw [Polynomial.degree_map_eq_of_injective (algebraMap K (SeparableClosure K)).injective,
      Polynomial.degree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K),
      Polynomial.degree_eq_natDegree hfmon.ne_zero, hdeg]
    exact_mod_cast hn.ne'
  obtain ⟨x, hx⟩ := IsSepClosed.exists_root g hgdeg hsep.map
  refine ⟨x, ?_⟩
  rw [aeval_def, eval₂_eq_eval_map]
  exact hx

/-- Explicit Eisenstein trinomial `X ^ n + π ^ m * X ^ b + π` for `0 < b < n` and `1 ≤ m`. -/
private theorem trinomial_eisenstein_properties {π : 𝒪[K]} (hπ : Irreducible π)
    {n b m : ℕ} (hb : 0 < b) (hbn : b < n) (hm : 1 ≤ m) :
    let f : 𝒪[K][X] := X ^ n + (C (π ^ m) * X ^ b + C π)
    f.Monic ∧ f.IsEisensteinAt 𝓂[K] ∧ f.natDegree = n ∧
      (∀ i, f.coeff i =
        (if i = n then 1 else 0) + ((if i = b then π ^ m else 0) + (if i = 0 then π else 0))) := by
  intro f
  have hπm : π ∈ 𝓂[K] := hπ.not_isUnit
  have hlt : (C (π ^ m) * X ^ b + C π : 𝒪[K][X]).natDegree < (X ^ n : 𝒪[K][X]).natDegree := by
    rw [natDegree_X_pow]
    refine lt_of_le_of_lt (natDegree_add_le _ _) (max_lt ?_ (by simp [Nat.lt_trans hb hbn]))
    exact lt_of_le_of_lt (natDegree_C_mul_X_pow_le _ _) hbn
  have hfmon : f.Monic := (monic_X_pow n).add_of_left (degree_lt_degree hlt)
  have hdeg : f.natDegree = n := by
    rw [natDegree_add_eq_left_of_natDegree_lt hlt, natDegree_X_pow]
  have hcoeff (i : ℕ) : f.coeff i =
      (if i = n then 1 else 0) + ((if i = b then π ^ m else 0) + (if i = 0 then π else 0)) := by
    simp only [f, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C]
  refine ⟨hfmon, ⟨by rw [hfmon.leadingCoeff]; exact Ideal.one_notMem _, fun {i} hi ↦ ?_, ?_⟩,
    hdeg, hcoeff⟩
  · rw [hdeg] at hi
    rw [hcoeff, ite_eq_right (fun h ↦ absurd h hi.ne), zero_add]
    refine add_mem ?_ ?_
    · split_ifs
      · exact Ideal.pow_mem_of_mem _ hπm m hm
      · exact zero_mem _
    · split_ifs
      · exact hπm
      · exact zero_mem _
  · have hn0 : (0 : ℕ) ≠ n := (Nat.lt_trans hb hbn).ne
    have hb0 : (0 : ℕ) ≠ b := hb.ne
    simp only [hcoeff, hn0, hb0, ↓reduceIte, zero_add]
    rw [TauCeti.IsDiscreteValuationRing.mem_maximalIdeal_pow_iff_le_addVal, addVal_uniformizer hπ]
    simp

/-- Helper: a monic Eisenstein polynomial of degree `n > 0` satisfying the Ore coefficient
conditions for `(n, j)` produces an extension `E ∈ σ_K(n)` with `E.wildExponent = j`. -/
private theorem exists_mem_totallyRamifiedOfDegree_wildExponent_eq_of_eisenstein
    {f : 𝒪[K][X]} {n j : ℕ} (hadm : IsOreAdmissible K n j) (hfmon : f.Monic)
    (hf : f.IsEisensteinAt 𝓂[K]) (hdeg : f.natDegree = n)
    (hmod : 0 < j % n →
      addVal 𝒪[K] (f.coeff (j % n)) = (oreCoefficientDepth K n j (j % n) : ℕ∞))
    (hbounds : ∀ h : Fin n, 0 < h.1 →
      (oreCoefficientDepth K n j h.1 : ℕ∞) ≤ addVal 𝒪[K] (f.coeff h.1)) :
    ∃ E ∈ totallyRamifiedOfDegree K n, E.wildExponent = j := by
  have hn := hadm.pos
  have hiInf : (⨅ k : Fin n, oreDerivativeTerm K f n k) = (j : ℕ∞) :=
    (iInf_oreDerivativeTerm_eq_iff hn fun h _ ↦ hf.mem (lt_of_lt_of_eq h.isLt hdeg.symm)).2
      ⟨hadm, hmod, hbounds⟩
  have hderiv : derivative (f.map (algebraMap 𝒪[K] K)) ≠ 0 :=
    (derivative_map_ne_zero_iff_iInf_oreDerivativeTerm_ne_top hfmon hdeg hn).2
      (hiInf.symm ▸ ENat.natCast_ne_top j)
  obtain ⟨x, hx⟩ := exists_root_of_eisenstein_derivative_ne_zero hfmon hf hdeg hn hderiv
  exact ⟨K⟮x⟯, adjoin_mem_totallyRamifiedOfDegree_of_eisenstein hf hdeg hx,
    (wildExponent_adjoin_eq_iff_of_eisenstein hfmon hf hdeg hn hx).2 ⟨hadm, hmod, hbounds⟩⟩

/-- **Ore's realizability theorem**: a natural number `j` is the wild exponent of some totally
ramified extension `E ∈ σ_K(n)` inside `SeparableClosure K` if and only if `IsOreAdmissible K n j`.
This holds in both mixed and equal characteristic, and for all `n : ℕ` (both sides are false at
`n = 0`). -/
theorem ore_realizability (n j : ℕ) :
    (∃ E ∈ totallyRamifiedOfDegree K n, E.wildExponent = j) ↔ IsOreAdmissible K n j := by
  constructor
  · rintro ⟨E, hE, rfl⟩
    have hn : 0 < n := Nat.pos_of_ne_zero fun h ↦ by
      simp [h, totallyRamifiedOfDegree_zero] at hE
    obtain ⟨f, x, hfmon, hf, hdeg, hx, rfl⟩ :=
      exists_eisenstein_generator_of_mem_totallyRamifiedOfDegree hE
    exact ((wildExponent_adjoin_eq_iff_of_eisenstein hfmon hf hdeg hn hx).1 rfl).1
  · intro hadm
    have hn := hadm.pos
    obtain ⟨π, hπ⟩ := exists_irreducible 𝒪[K]
    rcases Nat.eq_zero_or_pos (j % n) with hb0 | hbpos
    · -- Case `b = 0`: witness `f = X ^ n - C π`.
      refine exists_mem_totallyRamifiedOfDegree_wildExponent_eq_of_eisenstein hadm
        (monic_X_pow_sub_C π hn.ne') (isEisensteinAt_X_pow_sub_C_of_irreducible hπ hn)
        (natDegree_X_pow_sub_C _) (fun h ↦ absurd h (by omega)) fun h hh ↦ ?_
      have hzero : (X ^ n - C π : 𝒪[K][X]).coeff h.1 = 0 := by
        simp [coeff_X_pow, coeff_C, h.isLt.ne, hh.ne']
      rw [hzero]
      simp
    · -- Case `b > 0`: witness `f = X ^ n + (C (π ^ ν_b) * X ^ b + C π)`.
      set b := j % n
      set m := oreCoefficientDepth K n j b
      have hbn : b < n := Nat.mod_lt j hn
      obtain ⟨hfmon, hf, hdeg, hcoeff⟩ :=
        trinomial_eisenstein_properties hπ hbpos hbn (one_le_oreCoefficientDepth (K := K) n j b)
      set f : 𝒪[K][X] := X ^ n + (C (π ^ m) * X ^ b + C π)
      have hcb : addVal 𝒪[K] (f.coeff b) = (m : ℕ∞) := by
        simp only [hcoeff, hbn.ne, hbpos.ne', ↓reduceIte, zero_add, add_zero]
        rw [AddValuation.map_pow, addVal_uniformizer hπ, nsmul_eq_mul, mul_one]
      refine exists_mem_totallyRamifiedOfDegree_wildExponent_eq_of_eisenstein hadm hfmon hf hdeg
        (fun _ ↦ hcb) fun h hh ↦ ?_
      rcases eq_or_ne h.1 b with heq | hne
      · rw [heq, hcb]
      · have hzero : f.coeff h.1 = 0 := by simp [hcoeff, h.isLt.ne, hne, hh.ne']
        simp [hzero]

end LocalField

end TauCeti
