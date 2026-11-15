/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NewtonPolygon.Normalization
public import TauCeti.NumberTheory.NewtonPolygon.Roots
public import TauCeti.NumberTheory.Padics.Complex.Valuation

/-!
# Newton polygons, slopes, and roots over `ℂ_p` and `ℚ_p`

The field `ℂ_[p]` of `p`-adic complex numbers is algebraically closed and carries both the
rational-valued additive valuation `PadicComplex.addValuation p` (with values in `WithTop ℚ`) and
the real-valued additive valuation `PadicComplex.realValuation p` (with values in `WithTop ℝ`),
both normalised by `v(p) = 1` and recovering the `p`-adic norm through `‖x‖ = p ^ (-v(x))`. On
`ℚ_[p]`, `PadicComplex.realValuation p` restricts to `TauCeti.padicRealValuation p`.

Because every polynomial over `ℂ_[p]` splits into linear factors, the slope-root dictionary and
finite-face ball counts hold unconditionally (without any splitting hypothesis) for every
polynomial in `ℂ_[p][X]`, and after scalar extension `algebraMap ℚ_[p] ℂ_[p]` for every polynomial
in `ℚ_[p][X]`:
* Scalar extension from `(ℚ_[p], TauCeti.padicRealValuation p)` to
  `(ℂ_[p], PadicComplex.realValuation p)` preserves power-series and polynomial Newton polygons
  and polynomial finite slope multisets.
* Changing from base `p` (`PadicComplex.realValuation p`) to base `Real.exp 1` (`-Real.log ‖x‖`)
  scales Newton heights and finite slopes on `ℂ_[p]` by `Real.log p`.
* For every `f : ℂ_[p][X]`, `f.newtonSlopes (PadicComplex.realValuation p)` equals the multiset of
  `-((PadicComplex.addValuation p α).untop₀ : ℝ)` (and of `Real.logb p ‖α‖`) over nonzero roots
  `α ∈ f.roots`; in particular every finite slope is rational.
* For every finite face `(σ, l, u)` of `f.newtonPolygon (PadicComplex.realValuation p)` (or of
  `f.newtonPolygon (TauCeti.padicRealValuation p)` for `f : ℚ_[p][X]`), `l`, `u`, and `u - l`
  count the roots in `ℂ_[p]` in the open ball `‖α‖ < p ^ σ`, closed ball `‖α‖ ≤ p ^ σ`, and sphere
  `‖α‖ = p ^ σ` (and at rational slopes `q : ℚ`, in the valuation regions `-q < v(α)`, `-q ≤ v(α)`,
  and `v(α) = -q`).
* For `n > 0` and `m : ℤ`, `X ^ n - C (p ^ m)` over `ℂ_[p]` has finite slope multiset
  `Multiset.replicate n (-m / n)` (specialising at `n = 3, m = 1` to `X ^ 3 - C p` with three
  slopes equal to `-1 / 3`).

## Main results

* `PowerSeries.newtonPolygon_map_padicComplex`, `Polynomial.newtonPolygon_map_padicComplex`, and
  `Polynomial.newtonSlopes_map_padicComplex`: invariance of Newton polygons and finite slopes from
  `ℚ_[p]` to `ℂ_[p]`.
* `PowerSeries.newtonPolygon_ofNorm_exp_one_padicComplex`,
  `Polynomial.newtonPolygon_ofNorm_exp_one_padicComplex`, and
  `Polynomial.newtonSlopes_ofNorm_exp_one_padicComplex`: base-change scaling by `Real.log p`
  between base `p` and base `Real.exp 1` on `ℂ_[p]`.
* `Polynomial.newtonSlopes_realValuation_eq_map_roots_addValuation`,
  `Polynomial.newtonSlopes_realValuation_eq_map_roots_norm`, and
  `Polynomial.exists_rat_of_mem_newtonSlopes_realValuation`: unconditional slope-root identities
  and rationality of finite slopes over `ℂ_[p]`.
* `Polynomial.card_filter_roots_realValuation_norm_lt`,
  `Polynomial.card_filter_roots_realValuation_norm_le`,
  `Polynomial.card_filter_roots_realValuation_norm_eq`, and their `ℚ_[p] → ℂ_[p]` and rational
  `PadicComplex.addValuation` counterparts: unconditional open-ball, closed-ball, and sphere root
  counts in `ℂ_[p]`.
* `Polynomial.newtonSlopes_X_pow_sub_C_zpow_p`: the finite slopes of `X ^ n - C (p ^ m)` over
  `ℂ_[p]` are `Multiset.replicate n (-(m : ℝ) / n)`.

## References

* N. Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*, second edition,
  Graduate Texts in Mathematics 58, Springer, 1984, Chapter III §4 and Chapter IV §3.
* A. M. Robert, *A Course in p-adic Analysis*, Graduate Texts in Mathematics 198, Springer, 2000,
  Chapter 3 and Chapter 6 §1.
-/

public section

open scoped PowerSeries
open TauCeti

namespace PowerSeries

variable {p : ℕ} [Fact p.Prime]

/-- Extending scalars of a power series from `ℚ_[p]` to `ℂ_[p]` preserves its Newton polygon. -/
@[simp]
theorem newtonPolygon_map_padicComplex (f : ℚ_[p]⟦X⟧) :
    (map (algebraMap ℚ_[p] ℂ_[p]) f).newtonPolygon (PadicComplex.realValuation p) =
      f.newtonPolygon (padicRealValuation p) :=
  f.newtonPolygon_map (padicRealValuation p) (algebraMap ℚ_[p] ℂ_[p])
    PadicComplex.realValuation_algebraMap

/-- Changing from base `p` (`PadicComplex.realValuation p`) to base `Real.exp 1` (`-Real.log ‖x‖`)
multiplies power-series Newton heights on `ℂ_[p]` by `Real.log p`. -/
theorem newtonPolygon_ofNorm_exp_one_padicComplex (f : ℂ_[p]⟦X⟧) :
    f.newtonPolygon (AddValuation.ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 zero_lt_one)) =
      fun n ↦ (f.newtonPolygon (PadicComplex.realValuation p) n).map (Real.log p * ·) := by
  have hp : (1 : ℝ) < p := Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt
  simpa [Real.log_exp] using f.newtonPolygon_eq_map_of_norm_eq_rpow
    (PadicComplex.realValuation p)
    (AddValuation.ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 zero_lt_one))
    hp (Real.one_lt_exp_iff.2 zero_lt_one)
    (fun _ ↦ PadicComplex.norm_eq_rpow_neg_realValuation)
    (fun _ ↦ AddValuation.norm_eq_rpow_neg_ofNorm_of_ne_zero _)

end PowerSeries

namespace Polynomial

variable {p : ℕ} [Fact p.Prime]

/-! ### Scalar extension `ℚ_[p] → ℂ_[p]` and base-change normalisation -/

/-- Extending scalars of a polynomial from `ℚ_[p]` to `ℂ_[p]` preserves its Newton polygon. -/
@[simp]
theorem newtonPolygon_map_padicComplex (f : ℚ_[p][X]) :
    (f.map (algebraMap ℚ_[p] ℂ_[p])).newtonPolygon (PadicComplex.realValuation p) =
      f.newtonPolygon (padicRealValuation p) :=
  f.newtonPolygon_map (padicRealValuation p) (algebraMap ℚ_[p] ℂ_[p])
    PadicComplex.realValuation_algebraMap

/-- Extending scalars of a polynomial from `ℚ_[p]` to `ℂ_[p]` preserves its finite slope
multiset. -/
@[simp]
theorem newtonSlopes_map_padicComplex (f : ℚ_[p][X]) :
    (f.map (algebraMap ℚ_[p] ℂ_[p])).newtonSlopes (PadicComplex.realValuation p) =
      f.newtonSlopes (padicRealValuation p) :=
  f.newtonSlopes_map (padicRealValuation p) (algebraMap ℚ_[p] ℂ_[p])
    PadicComplex.realValuation_algebraMap

/-- Changing from base `p` (`PadicComplex.realValuation p`) to base `Real.exp 1` (`-Real.log ‖x‖`)
multiplies polynomial Newton heights on `ℂ_[p]` by `Real.log p`. -/
theorem newtonPolygon_ofNorm_exp_one_padicComplex (f : ℂ_[p][X]) :
    f.newtonPolygon (AddValuation.ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 zero_lt_one)) =
      fun n ↦ (f.newtonPolygon (PadicComplex.realValuation p) n).map (Real.log p * ·) := by
  simpa [Real.log_exp] using f.newtonPolygon_eq_map_of_norm_eq_rpow
    (PadicComplex.realValuation p)
    (AddValuation.ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 zero_lt_one))
    (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt) (Real.one_lt_exp_iff.2 zero_lt_one)
    (fun _ ↦ PadicComplex.norm_eq_rpow_neg_realValuation)
    (fun _ ↦ AddValuation.norm_eq_rpow_neg_ofNorm_of_ne_zero _)

/-- Changing from base `p` (`PadicComplex.realValuation p`) to base `Real.exp 1` (`-Real.log ‖x‖`)
multiplies every finite polynomial slope on `ℂ_[p]` by `Real.log p`. -/
theorem newtonSlopes_ofNorm_exp_one_padicComplex (f : ℂ_[p][X]) :
    f.newtonSlopes (AddValuation.ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 zero_lt_one)) =
      (f.newtonSlopes (PadicComplex.realValuation p)).map (Real.log p * ·) := by
  simpa [Real.log_exp] using f.newtonSlopes_eq_map_of_norm_eq_rpow
    (PadicComplex.realValuation p)
    (AddValuation.ofNorm (Real.exp 1) (Real.one_lt_exp_iff.2 zero_lt_one))
    (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt) (Real.one_lt_exp_iff.2 zero_lt_one)
    (fun _ ↦ PadicComplex.norm_eq_rpow_neg_realValuation)
    (fun _ ↦ AddValuation.norm_eq_rpow_neg_ofNorm_of_ne_zero _)

/-! ### Unconditional slope-root dictionary and ball counts over `ℂ_[p]` -/

/-- Every polynomial `f : ℂ_[p][X]` splits, so its finite slope multiset equals the multiset of
negated real valuations of its nonzero roots, counted with multiplicity. -/
theorem newtonSlopes_realValuation_eq_map_roots [DecidableEq ℂ_[p]] (f : ℂ_[p][X]) :
    f.newtonSlopes (PadicComplex.realValuation p) =
      (f.roots.filter (· ≠ 0)).map fun α ↦ -(PadicComplex.realValuation p α).untop₀ :=
  newtonSlopes_eq_map_roots (fun _ ↦ (PadicComplex.realValuation p).top_iff.mp)
    (IsAlgClosed.splits f)

/-- For every `f : ℂ_[p][X]`, its finite slope multiset equals the multiset of negated rational
valuations `-((PadicComplex.addValuation p α).untop₀ : ℝ)` of its nonzero roots `α`. -/
theorem newtonSlopes_realValuation_eq_map_roots_addValuation [DecidableEq ℂ_[p]] (f : ℂ_[p][X]) :
    f.newtonSlopes (PadicComplex.realValuation p) =
      (f.roots.filter (· ≠ 0)).map fun α ↦ -((PadicComplex.addValuation p α).untop₀ : ℝ) := by
  rw [newtonSlopes_realValuation_eq_map_roots]
  exact Multiset.map_congr rfl fun α _ ↦ by rw [PadicComplex.untop₀_realValuation]

/-- For every `f : ℂ_[p][X]`, its finite slope multiset equals the multiset of `Real.logb p ‖α‖`
over its nonzero roots `α`, counted with multiplicity. -/
theorem newtonSlopes_realValuation_eq_map_roots_norm [DecidableEq ℂ_[p]] (f : ℂ_[p][X]) :
    f.newtonSlopes (PadicComplex.realValuation p) =
      (f.roots.filter (· ≠ 0)).map fun α ↦ Real.logb p ‖α‖ :=
  newtonSlopes_eq_map_roots_norm (PadicComplex.realValuation p)
    (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
    (fun _ ↦ PadicComplex.norm_eq_rpow_neg_realValuation) (IsAlgClosed.splits f)

/-- **Rationality of finite slopes over `ℂ_[p]`**: every finite slope of any polynomial in
`ℂ_[p][X]` with respect to `PadicComplex.realValuation p` is a rational number. -/
theorem exists_rat_of_mem_newtonSlopes_realValuation {f : ℂ_[p][X]} {s : ℝ}
    (hs : s ∈ f.newtonSlopes (PadicComplex.realValuation p)) : ∃ q : ℚ, s = q := by
  classical
  rw [newtonSlopes_realValuation_eq_map_roots_addValuation] at hs
  obtain ⟨α, -, rfl⟩ := Multiset.mem_map.mp hs
  exact ⟨-(PadicComplex.addValuation p α).untop₀, (Rat.cast_neg _).symm⟩

/-- Over `ℂ_[p]`, every finite slope of `f` equals `m` if and only if every nonzero root of `f` has
norm `p ^ m`. -/
theorem forall_mem_newtonSlopes_realValuation_eq_iff_norm_eq (f : ℂ_[p][X]) {m : ℝ} :
    (∀ s ∈ f.newtonSlopes (PadicComplex.realValuation p), s = m) ↔
      ∀ α ∈ f.roots, α ≠ 0 → ‖α‖ = (p : ℝ) ^ m := by
  simpa [Algebra.algebraMap_self, Polynomial.map_id] using
    forall_mem_newtonSlopes_eq_iff_norm_eq (L := ℂ_[p]) (PadicComplex.realValuation p)
      (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
      (fun _ ↦ PadicComplex.norm_eq_rpow_neg_realValuation)
      (f := f) (by simpa [Algebra.algebraMap_self, Polynomial.map_id] using IsAlgClosed.splits f)

/-- Over `ℂ_[p]`, the left endpoint `l` of the finite face of slope `σ` counts the roots `α` of `f`
in the open ball `‖α‖ < p ^ σ`, counted with multiplicity and including zero. -/
theorem card_filter_roots_realValuation_norm_lt {f : ℂ_[p][X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon (PadicComplex.realValuation p)) σ l u) :
    (f.roots.filter fun α ↦ ‖α‖ < (p : ℝ) ^ σ).card = l :=
  card_filter_roots_norm_lt (PadicComplex.realValuation p)
    (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
    (fun _ ↦ PadicComplex.norm_eq_rpow_neg_realValuation) (IsAlgClosed.splits f) hface

/-- Over `ℂ_[p]`, the right endpoint `u` of the finite face of slope `σ` counts the roots `α` of
`f` in the closed ball `‖α‖ ≤ p ^ σ`, counted with multiplicity and including zero. -/
theorem card_filter_roots_realValuation_norm_le {f : ℂ_[p][X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon (PadicComplex.realValuation p)) σ l u) :
    (f.roots.filter fun α ↦ ‖α‖ ≤ (p : ℝ) ^ σ).card = u :=
  card_filter_roots_norm_le (PadicComplex.realValuation p)
    (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
    (fun _ ↦ PadicComplex.norm_eq_rpow_neg_realValuation) (IsAlgClosed.splits f) hface

/-- Over `ℂ_[p]`, the width `u - l` of the finite face of slope `σ` counts the roots `α` of `f` on
the sphere `‖α‖ = p ^ σ`, counted with multiplicity. -/
theorem card_filter_roots_realValuation_norm_eq {f : ℂ_[p][X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon (PadicComplex.realValuation p)) σ l u) :
    (f.roots.filter fun α ↦ ‖α‖ = (p : ℝ) ^ σ).card = u - l :=
  card_filter_roots_norm_eq (PadicComplex.realValuation p)
    (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
    (fun _ ↦ PadicComplex.norm_eq_rpow_neg_realValuation) (IsAlgClosed.splits f) hface

/-- At a rational slope `q : ℚ`, the left endpoint `l` of the finite face of slope `q` counts the
roots `α` of `f : ℂ_[p][X]` with `-q < PadicComplex.addValuation p α`. -/
theorem card_filter_roots_lt_padicComplexAddValuation {f : ℂ_[p][X]} {q : ℚ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon (PadicComplex.realValuation p)) q l u) :
    (f.roots.filter fun α ↦ ((-q : ℚ) : WithTop ℚ) < PadicComplex.addValuation p α).card = l := by
  rw [← card_filter_roots_lt_addValuation
    (fun _ ↦ (PadicComplex.realValuation p).top_iff.mp) (IsAlgClosed.splits f) hface]
  refine congrArg Multiset.card (Multiset.filter_congr fun α _ ↦ ?_)
  rw [PadicComplex.realValuation_eq_map_addValuation, ← Rat.cast_neg,
    ← WithTop.map_coe ((↑) : ℚ → ℝ) (-q), lt_iff_not_ge, lt_iff_not_ge,
    WithTop.map_le_iff ((↑) : ℚ → ℝ) Rat.cast_le]

/-- At a rational slope `q : ℚ`, the right endpoint `u` of the finite face of slope `q` counts the
roots `α` of `f : ℂ_[p][X]` with `-q ≤ PadicComplex.addValuation p α`. -/
theorem card_filter_roots_le_padicComplexAddValuation {f : ℂ_[p][X]} {q : ℚ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon (PadicComplex.realValuation p)) q l u) :
    (f.roots.filter fun α ↦ ((-q : ℚ) : WithTop ℚ) ≤ PadicComplex.addValuation p α).card = u := by
  rw [← card_filter_roots_le_addValuation
    (fun _ ↦ (PadicComplex.realValuation p).top_iff.mp) (IsAlgClosed.splits f) hface]
  refine congrArg Multiset.card (Multiset.filter_congr fun α _ ↦ ?_)
  rw [PadicComplex.realValuation_eq_map_addValuation, ← Rat.cast_neg,
    ← WithTop.map_coe ((↑) : ℚ → ℝ) (-q), WithTop.map_le_iff ((↑) : ℚ → ℝ) Rat.cast_le]

/-- At a rational slope `q : ℚ`, the width `u - l` of the finite face of slope `q` counts the roots
`α` of `f : ℂ_[p][X]` of rational valuation `PadicComplex.addValuation p α = -q`. -/
theorem card_filter_roots_padicComplexAddValuation_eq {f : ℂ_[p][X]} {q : ℚ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon (PadicComplex.realValuation p)) q l u) :
    (f.roots.filter fun α ↦ PadicComplex.addValuation p α = ((-q : ℚ) : WithTop ℚ)).card =
      u - l := by
  rw [← card_filter_roots_addValuation_eq
    (fun _ ↦ (PadicComplex.realValuation p).top_iff.mp) (IsAlgClosed.splits f) hface]
  refine congrArg Multiset.card (Multiset.filter_congr fun α _ ↦ ?_)
  rw [PadicComplex.realValuation_eq_map_addValuation, ← Rat.cast_neg,
    ← WithTop.map_coe ((↑) : ℚ → ℝ) (-q), (WithTop.map_injective Rat.cast_injective).eq_iff]

/-! ### Unconditional dictionary for `ℚ_[p][X]` via roots in `ℂ_[p]` -/

/-- For every `f : ℚ_[p][X]`, its finite slope multiset with respect to
`TauCeti.padicRealValuation p` equals the multiset of negated rational valuations
`-((PadicComplex.addValuation p α).untop₀ : ℝ)` of its nonzero roots `α` in `ℂ_[p]`. -/
theorem newtonSlopes_padicRealValuation_eq_map_roots_addValuation [DecidableEq ℂ_[p]]
    (f : ℚ_[p][X]) :
    f.newtonSlopes (padicRealValuation p) =
      ((f.map (algebraMap ℚ_[p] ℂ_[p])).roots.filter (· ≠ 0)).map
        fun α ↦ -((PadicComplex.addValuation p α).untop₀ : ℝ) := by
  rw [← newtonSlopes_map_padicComplex, newtonSlopes_realValuation_eq_map_roots_addValuation]

/-- For every `f : ℚ_[p][X]`, its finite slope multiset with respect to
`TauCeti.padicRealValuation p` equals the multiset of `Real.logb p ‖α‖` over its nonzero roots `α`
in `ℂ_[p]`, with no splitting assumption on `f`. -/
theorem newtonSlopes_padicRealValuation_eq_map_roots_norm [DecidableEq ℂ_[p]] (f : ℚ_[p][X]) :
    f.newtonSlopes (padicRealValuation p) =
      ((f.map (algebraMap ℚ_[p] ℂ_[p])).roots.filter (· ≠ 0)).map fun α ↦ Real.logb p ‖α‖ := by
  rw [← newtonSlopes_map_padicComplex, newtonSlopes_realValuation_eq_map_roots_norm]

/-- Every finite slope of any polynomial `f : ℚ_[p][X]` with respect to
`TauCeti.padicRealValuation p` is rational. -/
theorem exists_rat_of_mem_newtonSlopes_padicRealValuation {f : ℚ_[p][X]} {s : ℝ}
    (hs : s ∈ f.newtonSlopes (padicRealValuation p)) : ∃ q : ℚ, s = q := by
  rw [← newtonSlopes_map_padicComplex] at hs
  exact exists_rat_of_mem_newtonSlopes_realValuation hs

/-- For any `f : ℚ_[p][X]`, the left endpoint `l` of the finite face of slope `σ` of
`f.newtonPolygon (padicRealValuation p)` counts the roots `α` of `f` in `ℂ_[p]` in the open ball
`‖α‖ < p ^ σ`, counted with multiplicity and including zero. -/
theorem card_filter_roots_map_padicComplex_norm_lt {f : ℚ_[p][X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon (padicRealValuation p)) σ l u) :
    ((f.map (algebraMap ℚ_[p] ℂ_[p])).roots.filter fun α ↦ ‖α‖ < (p : ℝ) ^ σ).card = l :=
  card_filter_roots_map_norm_lt (padicRealValuation p)
    (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
    (fun _ ↦ norm_eq_rpow_neg_padicRealValuation)
    (IsAlgClosed.splits (f.map (algebraMap ℚ_[p] ℂ_[p]))) hface

/-- For any `f : ℚ_[p][X]`, the right endpoint `u` of the finite face of slope `σ` of
`f.newtonPolygon (padicRealValuation p)` counts the roots `α` of `f` in `ℂ_[p]` in the closed ball
`‖α‖ ≤ p ^ σ`, counted with multiplicity and including zero. -/
theorem card_filter_roots_map_padicComplex_norm_le {f : ℚ_[p][X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon (padicRealValuation p)) σ l u) :
    ((f.map (algebraMap ℚ_[p] ℂ_[p])).roots.filter fun α ↦ ‖α‖ ≤ (p : ℝ) ^ σ).card = u :=
  card_filter_roots_map_norm_le (padicRealValuation p)
    (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
    (fun _ ↦ norm_eq_rpow_neg_padicRealValuation)
    (IsAlgClosed.splits (f.map (algebraMap ℚ_[p] ℂ_[p]))) hface

/-- For any `f : ℚ_[p][X]`, the width `u - l` of the finite face of slope `σ` of
`f.newtonPolygon (padicRealValuation p)` counts the roots `α` of `f` in `ℂ_[p]` on the sphere
`‖α‖ = p ^ σ`, counted with multiplicity. -/
theorem card_filter_roots_map_padicComplex_norm_eq {f : ℚ_[p][X]} {σ : ℝ} {l u : ℕ}
    (hface : IsFiniteFace (f.newtonPolygon (padicRealValuation p)) σ l u) :
    ((f.map (algebraMap ℚ_[p] ℂ_[p])).roots.filter fun α ↦ ‖α‖ = (p : ℝ) ^ σ).card = u - l :=
  card_filter_roots_map_norm_eq (padicRealValuation p)
    (Nat.one_lt_cast.2 (Fact.out : p.Prime).one_lt)
    (fun _ ↦ norm_eq_rpow_neg_padicRealValuation)
    (IsAlgClosed.splits (f.map (algebraMap ℚ_[p] ℂ_[p]))) hface

/-! ### Roots of powers of `p`: `X ^ n - C (p ^ m)` -/

/-- Every root `α` in `ℂ_[p]` of `X ^ n - C (p ^ m)` (`n > 0`, `m : ℤ`) has rational valuation
`m / n` and norm `p ^ (-m / n)`. -/
theorem addValuation_eq_of_mem_roots_X_pow_sub_C_zpow_p {n : ℕ} (hn : 0 < n) (m : ℤ) {α : ℂ_[p]}
    (hα : α ∈ ((X : ℂ_[p][X]) ^ n - C ((p : ℂ_[p]) ^ m)).roots) :
    PadicComplex.addValuation p α = ((m / n : ℚ) : WithTop ℚ) := by
  have hroot := isRoot_of_mem_roots hα
  rw [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hroot
  exact PadicComplex.addValuation_eq_of_pow_eq_zpow hn hroot

/-- For `n > 0` and `m : ℤ`, the polynomial `X ^ n - C (p ^ m)` over `ℂ_[p]` has `n` finite slopes
with respect to `PadicComplex.realValuation p`, all equal to `-(m : ℝ) / n`. For `n = 3` and
`m = 1`, `X ^ 3 - C p` has three finite slopes equal to `-1 / 3`. -/
theorem newtonSlopes_X_pow_sub_C_zpow_p {n : ℕ} (hn : 0 < n) (m : ℤ) :
    ((X : ℂ_[p][X]) ^ n - C ((p : ℂ_[p]) ^ m)).newtonSlopes (PadicComplex.realValuation p) =
      Multiset.replicate n (-(m : ℝ) / n) := by
  have hp0 : (p : ℂ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpm0 : (p : ℂ_[p]) ^ m ≠ 0 := zpow_ne_zero m hp0
  have hc0 : ((X : ℂ_[p][X]) ^ n - C ((p : ℂ_[p]) ^ m)).coeff 0 ≠ 0 := by
    simp [hn.ne, hpm0]
  have htr : ((X : ℂ_[p][X]) ^ n - C ((p : ℂ_[p]) ^ m)).natTrailingDegree = 0 :=
    natTrailingDegree_eq_zero_of_constantCoeff_ne_zero hc0
  have hdeg : ((X : ℂ_[p][X]) ^ n - C ((p : ℂ_[p]) ^ m)).natDegree = n :=
    natDegree_X_pow_sub_C (a := (p : ℂ_[p]) ^ m) (n := n)
  rw [newtonSlopes_eq_replicate (fun _ ↦ (PadicComplex.realValuation p).top_iff.mp)
      (IsAlgClosed.splits _) (m := -(m : ℝ) / n),
    hdeg, htr, Nat.sub_zero]
  intro α hα _
  have hroot := isRoot_of_mem_roots hα
  rw [IsRoot.def, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] at hroot
  rw [PadicComplex.realValuation_eq_of_pow_eq_zpow hn hroot, neg_div, neg_neg]

end Polynomial
