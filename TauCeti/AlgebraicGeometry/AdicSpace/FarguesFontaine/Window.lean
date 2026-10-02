/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.FarguesFontaine.Y
import Mathlib.Data.Int.LeastGreatest
import TauCeti.Algebra.Order.GroupWithZero.Pow
import TauCeti.Data.NNRat.CommonDenominator
import TauCeti.RingTheory.Huber.Adic
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent

/-!
# Frobenius windows in `𝒴 = D(p) ∩ D([ϖ])`

Give the Witt vectors `𝕎 R` the `(p, [ϖ])`-adic topology and let `𝒴 ⊆ Spa(𝕎 R, 𝕎 R)` be the open
subset `D(p) ∩ D([ϖ])` (`TauCeti.FarguesFontaine.spaY`). At a point `v ∈ 𝒴` the *radius*
`κ(v)` is the ratio `log v([ϖ]) / log v(p)`. It is a real number only when `v` has rank one, so it
is never formed here; instead, for a nonnegative rational `q = a / b`, the bounds

```text
q ≤ κ(v)   :⇔   v([ϖ]) ^ b ≤ v(p) ^ a,
κ(v) ≤ q   :⇔   v(p) ^ a ≤ v([ϖ]) ^ b
```

are taken as definitions (`IsRadiusLowerBound`, `IsRadiusUpperBound`), and are independent of
the chosen fraction. With the breakpoint `c = (p + 1) / 2`, which satisfies `1 < c < p`, the
Frobenius windows are, for every integer `n`,

```text
U_n = {v ∈ 𝒴 : p ^ n ≤ κ(v) ≤ c p ^ n},
V_n = {v ∈ 𝒴 : c p ^ n ≤ κ(v) ≤ p ^ (n + 1)}.
```

They are rational subsets of `Spa(𝕎 R, 𝕎 R)` and cover `𝒴`. Since Frobenius multiplies the
radius by `p`, pulling back along it carries `U_n` into `U_(n+1)` and `V_n` into `V_(n+1)`, and
different windows in one family are disjoint. Hence the Frobenius iterates act freely on `𝒴`,
and every window is wandering: it meets none of its Frobenius translates. These are the charts
on which the adic Fargues–Fontaine curve `𝒴 / φ^ℤ` is built.

## Main definitions

* `TauCeti.FarguesFontaine.IsRadiusLowerBound`, `TauCeti.FarguesFontaine.IsRadiusUpperBound` :
  the order-theoretic bounds `q ≤ κ(v)` and `κ(v) ≤ q`.
* `TauCeti.FarguesFontaine.windowU`, `TauCeti.FarguesFontaine.windowV` : the windows `U_n` and
  `V_n`.

## Main results

* `TauCeti.FarguesFontaine.isRadiusLowerBound_iff_of_eq_div` : the lower bound may be read off
  any fraction representing `q`; likewise for the upper bound.
* `TauCeti.FarguesFontaine.isRadiusLowerBound_comap_frobenius_iff` : Frobenius multiplies the
  radius by `p`.
* `TauCeti.FarguesFontaine.exists_isRadiusLowerBound_zpow` : every point of `𝒴` has radius between
  consecutive powers of `p`.
* `TauCeti.FarguesFontaine.iUnion_windowU_union_windowV` : the windows cover `𝒴`.
* `TauCeti.FarguesFontaine.val_preimage_windowU_mem_spaRationalFamily` and its `V` analogue : the
  windows are rational subsets.
* `TauCeti.FarguesFontaine.comap_frobenius_mem_windowU_iff` and its `V` analogue : Frobenius shifts
  the window index by one.
* `TauCeti.FarguesFontaine.disjoint_windowU` and its `V` analogue : distinct windows in one family
  are disjoint.
* `TauCeti.FarguesFontaine.iterate_comap_frobenius_ne` : the Frobenius iterates act freely on `𝒴`.
* `TauCeti.FarguesFontaine.disjoint_image_iterate_comap_frobenius_windowU` and its `V` analogue :
  each window is wandering.

## References

* K. S. Kedlaya, *Sheaves, stacks, and shtukas*, lecture notes, Arizona Winter School 2017,
  §3.1, for the two families of windows; there the breakpoint may be any rational number
  strictly between `1` and `p`, and only `1 < c < p` is used here.
* L. Fargues and J.-M. Fontaine, *Courbes et fibrés vectoriels en théorie de Hodge p-adique*,
  Astérisque 406 (2018).
-/

public section

namespace TauCeti.FarguesFontaine

open TauCeti.ValuationSpectrum _root_.WittVector

variable (p : ℕ) [Fact p.Prime] {R : Type*} [CommRing R]

/-! ### Radius bounds -/

/-- **The lower radius bound `q ≤ κ(v)`** at a point `v` of `Spv (𝕎 R)`: writing `q = a / b` in
lowest terms, `v([ϖ]) ^ b ≤ v(p) ^ a`. Here `κ(v)` stands for the ratio `log v([ϖ]) / log v(p)`,
which is not formed; `isRadiusLowerBound_iff_of_eq_div` reads the bound off any fraction. -/
def IsRadiusLowerBound (ϖ : R) (q : ℚ≥0) (v : Spv (WittVector p R)) : Prop :=
  v.toValuativeRel.vle (teichmuller p ϖ ^ q.den) ((p : WittVector p R) ^ q.num)

/-- **The upper radius bound `κ(v) ≤ q`** at a point `v` of `Spv (𝕎 R)`: writing `q = a / b` in
lowest terms, `v(p) ^ a ≤ v([ϖ]) ^ b`. `isRadiusUpperBound_iff_of_eq_div` reads the bound off any
fraction. -/
def IsRadiusUpperBound (ϖ : R) (q : ℚ≥0) (v : Spv (WittVector p R)) : Prop :=
  v.toValuativeRel.vle ((p : WittVector p R) ^ q.num) (teichmuller p ϖ ^ q.den)

variable {p} {ϖ : R}

/-- **The lower radius bound from any fraction**: if `q = a / b` with `b ≠ 0`, then
`q ≤ κ(v)` exactly when `v([ϖ]) ^ b ≤ v(p) ^ a`. -/
theorem isRadiusLowerBound_iff_of_eq_div {q : ℚ≥0} {a b : ℕ} (hb : b ≠ 0) (hq : q = a / b)
    (v : Spv (WittVector p R)) :
    IsRadiusLowerBound p ϖ q v ↔
      v.toValuativeRel.vle (teichmuller p ϖ ^ b) ((p : WittVector p R) ^ a) := by
  rw [IsRadiusLowerBound, ← valuation_le_iff, ← valuation_le_iff, map_pow, map_pow, map_pow,
    map_pow]
  exact pow_le_pow_iff_of_mul_eq zero_le zero_le hb q.den_ne_zero (mul_comm _ _)
    (NNRat.num_mul_eq_of_eq_div hb hq)

/-- **The upper radius bound from any fraction**: if `q = a / b` with `b ≠ 0`, then
`κ(v) ≤ q` exactly when `v(p) ^ a ≤ v([ϖ]) ^ b`. -/
theorem isRadiusUpperBound_iff_of_eq_div {q : ℚ≥0} {a b : ℕ} (hb : b ≠ 0) (hq : q = a / b)
    (v : Spv (WittVector p R)) :
    IsRadiusUpperBound p ϖ q v ↔
      v.toValuativeRel.vle ((p : WittVector p R) ^ a) (teichmuller p ϖ ^ b) := by
  rw [IsRadiusUpperBound, ← valuation_le_iff, ← valuation_le_iff, map_pow, map_pow, map_pow,
    map_pow]
  exact pow_le_pow_iff_of_mul_eq zero_le zero_le hb q.den_ne_zero
    (NNRat.num_mul_eq_of_eq_div hb hq) (mul_comm _ _)

/-- A point that is not a lower bound `q ≤ κ(v)` satisfies the upper bound `κ(v) ≤ q`, since the
value group is linearly ordered. -/
theorem isRadiusUpperBound_of_not_isRadiusLowerBound {q : ℚ≥0} {v : Spv (WittVector p R)}
    (h : ¬ IsRadiusLowerBound p ϖ q v) : IsRadiusUpperBound p ϖ q v := by
  rw [IsRadiusLowerBound, ← valuation_le_iff, not_le] at h
  rw [IsRadiusUpperBound, ← valuation_le_iff]
  exact h.le

section CharP

variable [CharP R p]

/-- **Frobenius multiplies the radius by `p`, for lower bounds**: `q ≤ κ(φ v)` exactly when
`q / p ≤ κ(v)`. -/
theorem isRadiusLowerBound_comap_frobenius_iff (q : ℚ≥0) (v : Spv (WittVector p R)) :
    IsRadiusLowerBound p ϖ q (comap frobenius v) ↔ IsRadiusLowerBound p ϖ (q / p) v := by
  rw [IsRadiusLowerBound, comap_frobenius_teichmuller_pow_vle_natCast_pow_iff,
    isRadiusLowerBound_iff_of_eq_div (mul_ne_zero (Fact.out : p.Prime).ne_zero q.den_ne_zero)]
  rw [Nat.cast_mul, mul_comm, ← div_div, NNRat.num_div_den]

/-- **Frobenius multiplies the radius by `p`, for upper bounds**: `κ(φ v) ≤ q` exactly when
`κ(v) ≤ q / p`. -/
theorem isRadiusUpperBound_comap_frobenius_iff (q : ℚ≥0) (v : Spv (WittVector p R)) :
    IsRadiusUpperBound p ϖ q (comap frobenius v) ↔ IsRadiusUpperBound p ϖ (q / p) v := by
  rw [IsRadiusUpperBound, comap_frobenius_natCast_pow_vle_teichmuller_pow_iff,
    isRadiusUpperBound_iff_of_eq_div (mul_ne_zero (Fact.out : p.Prime).ne_zero q.den_ne_zero)]
  rw [Nat.cast_mul, mul_comm, ← div_div, NNRat.num_div_den]

end CharP

variable [TopologicalSpace (WittVector p R)]

/-- Every element has valuation at most `1` at a point of `Spa(𝕎 R, 𝕎 R)`. -/
private theorem valuation_le_one {v : Spv (WittVector p R)}
    (hv : v ∈ spa (⊤ : Subring (WittVector p R))) (x : WittVector p R) : v.valuation x ≤ 1 := by
  rw [← map_one v.valuation, valuation_le_iff]
  exact ((mem_spa_iff _ v).mp hv).2 x (Subring.mem_top x)

/-- **Lower radius bounds are closed downwards** on `Spa(𝕎 R, 𝕎 R)`: if `q ≤ κ(v)` and `q' ≤ q`
then `q' ≤ κ(v)`, since `v(p) ≤ 1`. -/
theorem IsRadiusLowerBound.of_le {q q' : ℚ≥0} {v : Spv (WittVector p R)}
    (hv : v ∈ spa (⊤ : Subring (WittVector p R))) (h : IsRadiusLowerBound p ϖ q v)
    (hq : q' ≤ q) : IsRadiusLowerBound p ϖ q' v := by
  obtain ⟨h₁, h₂⟩ := NNRat.eq_div_den_mul_den q q'
  have hb := mul_ne_zero q.den_ne_zero q'.den_ne_zero
  rw [isRadiusLowerBound_iff_of_eq_div hb h₁] at h
  rw [isRadiusLowerBound_iff_of_eq_div hb h₂, ← valuation_le_iff, map_pow, map_pow]
  rw [← valuation_le_iff, map_pow, map_pow] at h
  exact h.trans (pow_le_pow_of_le_one zero_le (valuation_le_one hv _) (NNRat.le_def.mp hq))

/-- **Upper radius bounds are closed upwards** on `Spa(𝕎 R, 𝕎 R)`: if `κ(v) ≤ q` and `q ≤ q'`
then `κ(v) ≤ q'`, since `v(p) ≤ 1`. -/
theorem IsRadiusUpperBound.of_le {q q' : ℚ≥0} {v : Spv (WittVector p R)}
    (hv : v ∈ spa (⊤ : Subring (WittVector p R))) (h : IsRadiusUpperBound p ϖ q v)
    (hq : q ≤ q') : IsRadiusUpperBound p ϖ q' v := by
  obtain ⟨h₁, h₂⟩ := NNRat.eq_div_den_mul_den q q'
  have hb := mul_ne_zero q.den_ne_zero q'.den_ne_zero
  rw [isRadiusUpperBound_iff_of_eq_div hb h₁] at h
  rw [isRadiusUpperBound_iff_of_eq_div hb h₂, ← valuation_le_iff, map_pow, map_pow]
  rw [← valuation_le_iff, map_pow, map_pow] at h
  exact (pow_le_pow_of_le_one zero_le (valuation_le_one hv _) (NNRat.le_def.mp hq)).trans h

variable (p) in
/-- At a point of `𝒴`, the valuation of `p` is nonzero and strictly below `1`: `p` lies off the
support, and it is topologically nilpotent for the `(p, [ϖ])`-adic topology. -/
private theorem valuation_natCast_pos_and_lt_one
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    {v : Spv (WittVector p R)} (hv : v ∈ spaY p ϖ) :
    0 < v.valuation (p : WittVector p R) ∧ v.valuation (p : WittVector p R) < 1 := by
  obtain ⟨hspa, hp, -⟩ := (mem_spaY_iff p ϖ v).mp hv
  refine ⟨zero_lt_iff.mpr fun h ↦ hp ?_, ?_⟩
  · rwa [supp_eq_valuation_supp, Valuation.mem_supp_iff]
  · exact ((isContinuous_def v).mp ((mem_spa_iff _ v).mp hspa).1).lt_one_of_isTopologicallyNilpotent
      (IsAdic.isTopologicallyNilpotent_of_mem hI (Ideal.subset_span (by simp)))

/-- **Separation of radius bounds on `𝒴`**: at a point of `𝒴` with `q ≤ κ(v)`, no `q' < q` is an
upper bound for `κ(v)`. This uses `0 < v(p) < 1`. -/
theorem IsRadiusLowerBound.not_isRadiusUpperBound
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    {q q' : ℚ≥0} {v : Spv (WittVector p R)} (hv : v ∈ spaY p ϖ)
    (h : IsRadiusLowerBound p ϖ q v) (hq : q' < q) : ¬ IsRadiusUpperBound p ϖ q' v := by
  intro h'
  obtain ⟨h₁, h₂⟩ := NNRat.eq_div_den_mul_den q q'
  have hb := mul_ne_zero q.den_ne_zero q'.den_ne_zero
  rw [isRadiusLowerBound_iff_of_eq_div hb h₁, ← valuation_le_iff, map_pow, map_pow] at h
  rw [isRadiusUpperBound_iff_of_eq_div hb h₂, ← valuation_le_iff, map_pow, map_pow] at h'
  obtain ⟨h0, h1⟩ := valuation_natCast_pos_and_lt_one p hI hv
  exact (pow_lt_pow_right_of_lt_one₀ h0 h1 (NNRat.lt_def.mp hq)).not_ge (h'.trans h)

/-- **The radius lies between consecutive powers of `p`**: every point of `𝒴` satisfies
`p ^ n ≤ κ(v) ≤ p ^ (n + 1)` for some integer `n`. -/
theorem exists_isRadiusLowerBound_zpow
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    {v : Spv (WittVector p R)} (hv : v ∈ spaY p ϖ) :
    ∃ n : ℤ, IsRadiusLowerBound p ϖ ((p : ℚ≥0) ^ n) v ∧
      IsRadiusUpperBound p ϖ ((p : ℚ≥0) ^ (n + 1)) v := by
  have hspa := ((mem_spaY_iff p ϖ v).mp hv).1
  have hp : (1 : ℚ≥0) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  obtain ⟨⟨b, hb⟩, ⟨b', hb'⟩⟩ := exists_pow_vlt_of_mem_spaY hI hv 1
  rw [← valuation_lt_iff, map_pow, map_pow, pow_one] at hb hb'
  -- `v([ϖ]) ^ (b + 1) ≤ v(p)` gives the lower bound `p ^ (-(b + 1)) ≤ 1 / (b + 1) ≤ κ(v)`
  have hlow : IsRadiusLowerBound p ϖ ((p : ℚ≥0) ^ (-((b + 1 : ℕ) : ℤ))) v := by
    refine IsRadiusLowerBound.of_le hspa ((isRadiusLowerBound_iff_of_eq_div (a := 1)
      (b := b + 1) b.succ_ne_zero rfl v).mpr ?_) ?_
    · rw [← valuation_le_iff, map_pow, map_pow, pow_succ, pow_one]
      exact (mul_le_of_le_one_right zero_le (valuation_le_one hspa _)).trans hb.le
    · rw [zpow_neg, zpow_natCast, inv_eq_one_div, Nat.cast_one]
      exact one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le)
  -- `v(p) ^ b' < v([ϖ])` excludes the lower bound `b' ≤ κ(v)`, hence `p ^ b' ≤ κ(v)`
  have hhigh : ¬ IsRadiusLowerBound p ϖ ((p : ℚ≥0) ^ (b' : ℤ)) v := fun h ↦ by
    have := (isRadiusLowerBound_iff_of_eq_div (q := (b' : ℚ≥0)) (a := b') (b := 1) one_ne_zero
      (by simp) v).mp (h.of_le hspa (by
        rw [zpow_natCast]; exact_mod_cast (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le))
    rw [← valuation_le_iff, map_pow, map_pow, pow_one] at this
    exact this.not_gt hb'
  obtain ⟨n, hn, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun n : ℤ ↦ IsRadiusLowerBound p ϖ ((p : ℚ≥0) ^ n) v)
    ⟨b', fun z hz ↦ not_lt.mp fun hlt ↦ hhigh
      (hz.of_le hspa (zpow_le_zpow_right₀ hp.le hlt.le))⟩ ⟨_, hlow⟩
  exact ⟨n, hn, isRadiusUpperBound_of_not_isRadiusLowerBound fun h ↦
    (lt_add_one n).not_ge (hmax _ h)⟩

/-! ### The windows -/

variable (p) in
/-- **The window `U_n = {v ∈ 𝒴 : p ^ n ≤ κ(v) ≤ c p ^ n}`**, with the breakpoint
`c = (p + 1) / 2`. -/
def windowU (ϖ : R) (n : ℤ) : Set (Spv (WittVector p R)) :=
  {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ ((p : ℚ≥0) ^ n) v ∧
    IsRadiusUpperBound p ϖ ((p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n) v}

variable (p) in
/-- **The window `V_n = {v ∈ 𝒴 : c p ^ n ≤ κ(v) ≤ p ^ (n + 1)}`**, with the breakpoint
`c = (p + 1) / 2`. -/
def windowV (ϖ : R) (n : ℤ) : Set (Spv (WittVector p R)) :=
  {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ ((p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n) v ∧
    IsRadiusUpperBound p ϖ ((p : ℚ≥0) ^ (n + 1)) v}

/-- Membership in `U_n`: a point of `𝒴` with `p ^ n ≤ κ(v) ≤ c p ^ n`. -/
@[simp]
theorem mem_windowU_iff (n : ℤ) (v : Spv (WittVector p R)) :
    v ∈ windowU p ϖ n ↔ v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ ((p : ℚ≥0) ^ n) v ∧
      IsRadiusUpperBound p ϖ ((p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n) v :=
  Iff.rfl

/-- Membership in `V_n`: a point of `𝒴` with `c p ^ n ≤ κ(v) ≤ p ^ (n + 1)`. -/
@[simp]
theorem mem_windowV_iff (n : ℤ) (v : Spv (WittVector p R)) :
    v ∈ windowV p ϖ n ↔ v ∈ spaY p ϖ ∧
      IsRadiusLowerBound p ϖ ((p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n) v ∧
        IsRadiusUpperBound p ϖ ((p : ℚ≥0) ^ (n + 1)) v :=
  Iff.rfl

/-- `U_n ⊆ 𝒴`. -/
theorem windowU_subset_spaY (n : ℤ) : windowU p ϖ n ⊆ spaY p ϖ := fun _ hv ↦ hv.1

/-- `V_n ⊆ 𝒴`. -/
theorem windowV_subset_spaY (n : ℤ) : windowV p ϖ n ⊆ spaY p ϖ := fun _ hv ↦ hv.1

/-- **The windows cover `𝒴`**: every point of `𝒴` lies in some `U_n` or `V_n`. -/
theorem iUnion_windowU_union_windowV
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) :
    ⋃ n : ℤ, (windowU p ϖ n ∪ windowV p ϖ n) = spaY p ϖ := by
  refine (Set.iUnion_subset fun n ↦
    Set.union_subset (windowU_subset_spaY n) (windowV_subset_spaY n)).antisymm fun v hv ↦ ?_
  obtain ⟨n, hn, hn'⟩ := exists_isRadiusLowerBound_zpow hI hv
  refine Set.mem_iUnion.mpr ⟨n, ?_⟩
  by_cases h : IsRadiusLowerBound p ϖ ((p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n) v
  · exact Or.inr ⟨hv, h, hn'⟩
  · exact Or.inl ⟨hv, hn, isRadiusUpperBound_of_not_isRadiusLowerBound h⟩

section Rational

/-- An ideal whose radical contains `p` and `[ϖ]` is open for the `(p, [ϖ])`-adic topology. -/
private theorem isOpen_of_span_le_radical
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    {J : Ideal (WittVector p R)}
    (hJ : Ideal.span {(p : WittVector p R), teichmuller p ϖ} ≤ J.radical) :
    IsOpen (J : Set (WittVector p R)) := by
  have : IsTopologicalRing (WittVector p R) :=
    hI ▸ (Ideal.span _).nonarchimedean.toIsTopologicalRing
  have hfg : (Ideal.span {(p : WittVector p R), teichmuller p ϖ}).FG := Submodule.fg_span (by simp)
  rwa [(Huber.PairOfDefinition.adic _ hI hfg).isOpen_iff_le_radical,
    Huber.PairOfDefinition.adic_extendedIdealOfDefinition]

/-- The set `{v ∈ 𝒴 : q ≤ κ(v) ≤ q'}`, for `q ≠ 0`, is the intersection of the rational subsets
`R({[ϖ] ^ b, p ^ a} / p ^ a)` and `R({p ^ a', [ϖ] ^ b'} / [ϖ] ^ b')`, where `q = a / b` and
`q' = a' / b'` in lowest terms. -/
private theorem setOf_isRadiusLowerBound_isRadiusUpperBound_eq [DecidableEq (WittVector p R)]
    {q q' : ℚ≥0} (hq : q ≠ 0) :
    {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v} =
      rationalSubset ⊤ {teichmuller p ϖ ^ q.den, (p : WittVector p R) ^ q.num}
          ((p : WittVector p R) ^ q.num) ∩
        rationalSubset ⊤ {(p : WittVector p R) ^ q'.num, teichmuller p ϖ ^ q'.den}
          (teichmuller p ϖ ^ q'.den) := by
  have hsupp {v : Spv (WittVector p R)} {x : WittVector p R} {k : ℕ} (hk : k ≠ 0) :
      ¬ v.toValuativeRel.vle (x ^ k) 0 ↔ x ∉ v.supp := by
    rw [← mem_supp_iff, Ideal.IsPrime.pow_mem_iff_mem inferInstance k (Nat.pos_of_ne_zero hk)]
  ext v
  have h₁ := v.toValuativeRel.vle_refl ((p : WittVector p R) ^ q.num)
  have h₂ := v.toValuativeRel.vle_refl (teichmuller p ϖ ^ q'.den)
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, mem_rationalSubset_iff, mem_spaY_iff,
    Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq,
    hsupp (NNRat.num_ne_zero.mpr hq), hsupp q'.den_ne_zero, IsRadiusLowerBound,
    IsRadiusUpperBound]
  tauto

/-- The set `{v ∈ 𝒴 : q ≤ κ(v) ≤ q'}`, for `q ≠ 0`, is a rational subset of
`Spa(𝕎 R, 𝕎 R)`. -/
private theorem val_preimage_setOf_mem_spaRationalFamily
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) {q q' : ℚ≥0}
    (hq : q ≠ 0) :
    (Subtype.val ⁻¹'
        {v | v ∈ spaY p ϖ ∧ IsRadiusLowerBound p ϖ q v ∧ IsRadiusUpperBound p ϖ q' v} :
        Set (spa (⊤ : Subring (WittVector p R)))) ∈ spaRationalFamily ⊤ := by
  classical
  have : IsTopologicalRing (WittVector p R) :=
    hI ▸ (Ideal.span _).nonarchimedean.toIsTopologicalRing
  -- a numerator set containing a power of `p` and a power of `[ϖ]` spans an open ideal
  have hopen {k l : ℕ} {T : Finset (WittVector p R)} (hk : (p : WittVector p R) ^ k ∈ T)
      (hl : teichmuller p ϖ ^ l ∈ T) :
      IsOpen (Ideal.span (T : Set (WittVector p R)) : Set (WittVector p R)) := by
    refine isOpen_of_span_le_radical hI (Ideal.span_le.mpr ?_)
    rw [Set.insert_subset_iff, Set.singleton_subset_iff]
    exact ⟨Ideal.mem_radical_of_pow_mem (Ideal.le_radical (Ideal.subset_span hk)),
      Ideal.mem_radical_of_pow_mem (Ideal.le_radical (Ideal.subset_span hl))⟩
  have hfg : (Ideal.span {(p : WittVector p R), teichmuller p ϖ}).FG := Submodule.fg_span (by simp)
  rw [setOf_isRadiusLowerBound_isRadiusUpperBound_eq hq, Set.preimage_inter]
  exact inter_mem_spaRationalFamily_of_pairOfDefinition (Huber.PairOfDefinition.adic _ hI hfg)
    (mem_spaRationalFamily_iff.mpr
      ⟨_, _, hopen (k := q.num) (l := q.den) (by simp) (by simp), rfl⟩)
    (mem_spaRationalFamily_iff.mpr
      ⟨_, _, hopen (k := q'.num) (l := q'.den) (by simp) (by simp), rfl⟩)

variable (ϖ) in
/-- **`U_n` is a rational subset** of `Spa(𝕎 R, 𝕎 R)`, for the `(p, [ϖ])`-adic topology. -/
theorem val_preimage_windowU_mem_spaRationalFamily
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) (n : ℤ) :
    (Subtype.val ⁻¹' windowU p ϖ n : Set (spa (⊤ : Subring (WittVector p R)))) ∈
      spaRationalFamily ⊤ :=
  val_preimage_setOf_mem_spaRationalFamily hI
    (zpow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero))

variable (ϖ) in
/-- **`V_n` is a rational subset** of `Spa(𝕎 R, 𝕎 R)`, for the `(p, [ϖ])`-adic topology. -/
theorem val_preimage_windowV_mem_spaRationalFamily
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) (n : ℤ) :
    (Subtype.val ⁻¹' windowV p ϖ n : Set (spa (⊤ : Subring (WittVector p R)))) ∈
      spaRationalFamily ⊤ :=
  val_preimage_setOf_mem_spaRationalFamily hI (mul_ne_zero (by positivity)
    (zpow_ne_zero n (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)))

end Rational

/-! ### Frobenius on the windows -/

/-- The breakpoint `c = (p + 1) / 2` exceeds `1`. -/
private theorem one_lt_breakpoint : (1 : ℚ≥0) < (p + 1 : ℚ≥0) / 2 := by
  rw [lt_div_iff₀ two_pos]
  exact_mod_cast (by have := (Fact.out : p.Prime).two_le; omega : 1 * 2 < p + 1)

/-- The breakpoint `c = (p + 1) / 2` is below `p`. -/
private theorem breakpoint_lt : (p + 1 : ℚ≥0) / 2 < p := by
  rw [div_lt_iff₀ two_pos]
  exact_mod_cast (by have := (Fact.out : p.Prime).two_le; omega : p + 1 < p * 2)

/-- **Disjointness of the `U` windows**: `U_m ∩ U_n = ∅` for `m ≠ n`, because
`c p ^ m < p ^ (m + 1)`. -/
theorem disjoint_windowU (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    {m n : ℤ} (h : m ≠ n) : Disjoint (windowU p ϖ m) (windowU p ϖ n) := by
  wlog hmn : m < n generalizing m n
  · exact (this h.symm (h.lt_or_gt.resolve_left hmn)).symm
  have hp : (1 : ℚ≥0) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine Set.disjoint_left.mpr fun v hm hn ↦ hn.2.1.not_isRadiusUpperBound hI hn.1 ?_ hm.2.2
  calc (p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ m < p * (p : ℚ≥0) ^ m :=
        mul_lt_mul_of_pos_right breakpoint_lt (zpow_pos (zero_lt_one.trans hp) m)
    _ = (p : ℚ≥0) ^ (m + 1) := by rw [zpow_add_one₀ (zero_lt_one.trans hp).ne', mul_comm]
    _ ≤ (p : ℚ≥0) ^ n := zpow_le_zpow_right₀ hp.le (by omega)

/-- **Disjointness of the `V` windows**: `V_m ∩ V_n = ∅` for `m ≠ n`, because
`p ^ (m + 1) < c p ^ (m + 1)`. -/
theorem disjoint_windowV (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    {m n : ℤ} (h : m ≠ n) : Disjoint (windowV p ϖ m) (windowV p ϖ n) := by
  wlog hmn : m < n generalizing m n
  · exact (this h.symm (h.lt_or_gt.resolve_left hmn)).symm
  have hp : (1 : ℚ≥0) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine Set.disjoint_left.mpr fun v hm hn ↦ hn.2.1.not_isRadiusUpperBound hI hn.1 ?_ hm.2.2
  calc (p : ℚ≥0) ^ (m + 1) ≤ (p : ℚ≥0) ^ n := zpow_le_zpow_right₀ hp.le (by omega)
    _ < (p + 1 : ℚ≥0) / 2 * (p : ℚ≥0) ^ n :=
        lt_mul_of_one_lt_left (zpow_pos (zero_lt_one.trans hp) n) one_lt_breakpoint

section CharP

variable [CharP R p]

/-- Dividing `p ^ (n + 1)` by `p`, the arithmetic behind the index shift under Frobenius. -/
private theorem zpow_add_one_div (n : ℤ) : (p : ℚ≥0) ^ (n + 1) / p = (p : ℚ≥0) ^ n := by
  have hp : (p : ℚ≥0) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [zpow_add_one₀ hp, mul_div_cancel_right₀ _ hp]

/-- **Frobenius shifts the `U` windows**: pulling a point of `U_n` back along Frobenius gives a
point of `U_(n+1)`. -/
theorem comap_frobenius_mem_windowU
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    {v : Spv (WittVector p R)} {n : ℤ} (hv : v ∈ windowU p ϖ n) :
    comap frobenius v ∈ windowU p ϖ (n + 1) := by
  obtain ⟨hY, hl, hu⟩ := hv
  refine ⟨comap_frobenius_mem_spaY hI hY, ?_, ?_⟩
  · rwa [isRadiusLowerBound_comap_frobenius_iff, zpow_add_one_div]
  · rwa [isRadiusUpperBound_comap_frobenius_iff, mul_div_assoc, zpow_add_one_div]

/-- **Frobenius shifts the `V` windows**: pulling a point of `V_n` back along Frobenius gives a
point of `V_(n+1)`. -/
theorem comap_frobenius_mem_windowV
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    {v : Spv (WittVector p R)} {n : ℤ} (hv : v ∈ windowV p ϖ n) :
    comap frobenius v ∈ windowV p ϖ (n + 1) := by
  obtain ⟨hY, hl, hu⟩ := hv
  refine ⟨comap_frobenius_mem_spaY hI hY, ?_, ?_⟩
  · rwa [isRadiusLowerBound_comap_frobenius_iff, mul_div_assoc, zpow_add_one_div]
  · rwa [isRadiusUpperBound_comap_frobenius_iff, zpow_add_one_div]

/-- **Frobenius shifts the `U` windows exactly**: for perfect `R`, a point lies in `U_n` exactly
when its pullback along Frobenius lies in `U_(n+1)`. -/
theorem comap_frobenius_mem_windowU_iff [PerfectRing R p]
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (v : Spv (WittVector p R)) (n : ℤ) :
    comap frobenius v ∈ windowU p ϖ (n + 1) ↔ v ∈ windowU p ϖ n := by
  rw [mem_windowU_iff, mem_windowU_iff, comap_frobenius_mem_spaY_iff hI,
    isRadiusLowerBound_comap_frobenius_iff, isRadiusUpperBound_comap_frobenius_iff,
    mul_div_assoc, zpow_add_one_div]

/-- **Frobenius shifts the `V` windows exactly**: for perfect `R`, a point lies in `V_n` exactly
when its pullback along Frobenius lies in `V_(n+1)`. -/
theorem comap_frobenius_mem_windowV_iff [PerfectRing R p]
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    (v : Spv (WittVector p R)) (n : ℤ) :
    comap frobenius v ∈ windowV p ϖ (n + 1) ↔ v ∈ windowV p ϖ n := by
  rw [mem_windowV_iff, mem_windowV_iff, comap_frobenius_mem_spaY_iff hI,
    isRadiusLowerBound_comap_frobenius_iff, isRadiusUpperBound_comap_frobenius_iff,
    mul_div_assoc, zpow_add_one_div, zpow_add_one_div]

/-- Iterating Frobenius `k` times carries `U_n` into `U_(n+k)`. -/
theorem mapsTo_iterate_comap_frobenius_windowU
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) (n : ℤ) (k : ℕ) :
    Set.MapsTo (comap frobenius)^[k] (windowU p ϖ n) (windowU p ϖ (n + k)) := by
  induction k with
  | zero => simpa using Set.mapsTo_id _
  | succ k ih =>
    intro v hv
    rw [Function.iterate_succ_apply', Nat.cast_succ, ← add_assoc]
    exact comap_frobenius_mem_windowU hI (ih hv)

/-- Iterating Frobenius `k` times carries `V_n` into `V_(n+k)`. -/
theorem mapsTo_iterate_comap_frobenius_windowV
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) (n : ℤ) (k : ℕ) :
    Set.MapsTo (comap frobenius)^[k] (windowV p ϖ n) (windowV p ϖ (n + k)) := by
  induction k with
  | zero => simpa using Set.mapsTo_id _
  | succ k ih =>
    intro v hv
    rw [Function.iterate_succ_apply', Nat.cast_succ, ← add_assoc]
    exact comap_frobenius_mem_windowV hI (ih hv)

/-- **The `U` windows are wandering**: a nontrivial Frobenius iterate moves `U_n` off itself. -/
theorem disjoint_image_iterate_comap_frobenius_windowU
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) (n : ℤ) {k : ℕ}
    (hk : k ≠ 0) : Disjoint ((comap frobenius)^[k] '' windowU p ϖ n) (windowU p ϖ n) :=
  (disjoint_windowU hI (by omega)).mono_left
    (mapsTo_iterate_comap_frobenius_windowU hI n k).image_subset

/-- **The `V` windows are wandering**: a nontrivial Frobenius iterate moves `V_n` off itself. -/
theorem disjoint_image_iterate_comap_frobenius_windowV
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ})) (n : ℤ) {k : ℕ}
    (hk : k ≠ 0) : Disjoint ((comap frobenius)^[k] '' windowV p ϖ n) (windowV p ϖ n) :=
  (disjoint_windowV hI (by omega)).mono_left
    (mapsTo_iterate_comap_frobenius_windowV hI n k).image_subset

/-- **Frobenius acts freely on `𝒴`**: no nontrivial Frobenius iterate fixes a point of `𝒴`. -/
theorem iterate_comap_frobenius_ne
    (hI : IsAdic (Ideal.span {(p : WittVector p R), teichmuller p ϖ}))
    {v : Spv (WittVector p R)} (hv : v ∈ spaY p ϖ) {k : ℕ} (hk : k ≠ 0) :
    (comap frobenius)^[k] v ≠ v := by
  rw [← iUnion_windowU_union_windowV hI] at hv
  obtain ⟨n, hn | hn⟩ := Set.mem_iUnion.mp hv
  · exact (disjoint_image_iterate_comap_frobenius_windowU hI n hk).ne_of_mem
      (Set.mem_image_of_mem _ hn) hn
  · exact (disjoint_image_iterate_comap_frobenius_windowV hI n hk).ne_of_mem
      (Set.mem_image_of_mem _ hn) hn

end CharP

end TauCeti.FarguesFontaine
