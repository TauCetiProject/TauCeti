/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Parametrix
public import TauCeti.Analysis.Pseudodifferential.Composition.ProperSupport

/-!
# Properly supported parametrices

Let `a` be a symbol of order `m` on `ℝⁿ` with values in `V →L[ℂ] W`. A parametrix symbol `b` of
`a` (`TauCeti.Symbol.IsEllipticAbove.exists_isAsymptoticSum_sharpTerm`) inverts `a` on the level
of formal compositions, `1 ∼ ∑ₖ sharpTerm b a k`. Turning it into an operator identity needs the
composition symbol of `Op(b) ∘ Op(a)`, and `b # a` is only defined when `a` has compact spatial
support; this is why the local parametrix `TauCeti.Symbol.isSmoothing_sharp_sub_ofSpatial` first
cuts `a` off in the position. This file removes that restriction with properly supported
operators. Replacing `b` by a symbol `q` of finite propagation that differs from it by a smoothing
symbol (`TauCeti.Symbol.exists_isSmoothing_sub_and_hasPropagationLE`), the composition symbol
`q.properSharp hq a` of `Op(q) ∘ Op(a)` exists for every `a`, and it is `1` up to a smoothing
symbol. So `Op(q)` is a **properly supported left parametrix** of `Op(a)` on all of `ℝⁿ`:

`Op(q) (Op(a) u) = u + Op(r) u`, with `r` smoothing,

for every Schwartz function `u` such that `Op(a) u` has compact support, with no condition on the
spatial support of `a` and no uniformity of the symbol estimates in the position. When `a` has
finite propagation as well, the same `q` is a right parametrix, and both remainders have finite
propagation: `Op(q)` is a **two-sided properly supported parametrix**, with properly supported
smoothing remainders, on the compactly supported Schwartz functions.

## Main results

* `TauCeti.Symbol.isSmoothing_properSharp_sub_iff_left`,
  `TauCeti.Symbol.isSmoothing_properSharp_sub_iff_right`: a symbol of finite propagation is a left
  (right) parametrix symbol exactly when its composition symbol with `a` is `1` up to a smoothing
  symbol.
* `TauCeti.Symbol.IsEllipticAbove.exists_hasPropagationLE_isSmoothing_properSharp_sub`: a symbol
  elliptic above some radius has, for every `ε > 0`, a parametrix symbol of propagation at most
  `ε` whose composition symbols with `a` on both sides are `1` up to smoothing symbols.
* `TauCeti.Symbol.quantizeSchwartzValue_quantizeSchwartzValue_eq_add`: the operator identity
  `Op(q) (Op(a) u) = u + Op(q.properSharp hq a - 1) u` behind the parametrix statements.
* `TauCeti.Symbol.exists_hasPropagationLE_quantizeSchwartzValue_eq_add_of_isAsymptoticSum`:
  a left parametrix symbol yields a properly supported left parametrix.
* `TauCeti.Symbol.IsEllipticAbove.exists_hasPropagationLE_quantizeSchwartzValue_eq_add`: **the
  properly supported left parametrix** of an elliptic symbol.
* `TauCeti.Symbol.IsEllipticAbove.exists_hasPropagationLE_quantizeSchwartzValue_eq_add_and_eq_add`:
  **the two-sided properly supported parametrix** of a properly supported elliptic symbol.
* `TauCeti.ClassicalSymbol.IsElliptic.exists_hasPropagationLE_quantizeSchwartzValue_eq_add`: the
  properly supported left parametrix of an elliptic classical symbol, with no radius of
  invertibility uniform in the position.
* `TauCeti.Symbol.isSmoothing_sub_of_isSmoothing_properSharp_sub`: properly supported left and
  right parametrices agree modulo smoothing symbols.

## References

* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.21)–(1.28) and (4.1)–(4.6).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {m ε ε' : ℝ}

/-! ### Parametrix symbols of finite propagation -/

/-- **Left parametrix symbols of finite propagation.** A symbol `b` of order `-m` and finite
propagation is a left parametrix symbol of `a`, `1 ∼ ∑ₖ sharpTerm b a k`, exactly when the
composition symbol `b.properSharp hb a` of `Op(b) ∘ Op(a)` is `1` up to a smoothing symbol. No
condition on the spatial support of `a` is needed. -/
theorem isSmoothing_properSharp_sub_iff_left {a : Symbol n V W m} {b : Symbol n W V (-m)}
    (hb : b.HasPropagationLE ε) :
    (b.properSharp hb a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing ↔
      IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
        (b.sharpTerm a) :=
  ((isAsymptoticSum_properSharp hb a).isAsymptoticSum_inclusion_iff_isSmoothing_sub
    (tendsto_atBot_add_const_left atTop (-m + m)
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)) _ _ _).symm

/-- **Right parametrix symbols of finite propagation.** For a symbol `a` of order `m` and finite
propagation, a symbol `b` of order `-m` is a right parametrix symbol of `a`,
`1 ∼ ∑ₖ sharpTerm a b k`, exactly when the composition symbol `a.properSharp ha b` of
`Op(a) ∘ Op(b)` is `1` up to a smoothing symbol. No condition on the spatial support of `b` is
needed. -/
theorem isSmoothing_properSharp_sub_iff_right {a : Symbol n V W m} (ha : a.HasPropagationLE ε)
    {b : Symbol n W V (-m)} :
    (a.properSharp ha b - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).IsSmoothing ↔
      IsAsymptoticSum (m := fun k : ℕ ↦ m + -m - k) (inclusion (by simp) (const (.id ℂ W)))
        (a.sharpTerm b) :=
  ((isAsymptoticSum_properSharp ha b).isAsymptoticSum_inclusion_iff_isSmoothing_sub
    (tendsto_atBot_add_const_left atTop (m + -m)
      (tendsto_neg_atTop_atBot.comp tendsto_natCast_atTop_atTop)) _ _ _).symm

/-- **Uniqueness of properly supported parametrices.** A left parametrix `q` of finite propagation
and a right parametrix `q'` of a symbol `a` of finite propagation, in the sense that
`q.properSharp hq a - 1` and `a.properSharp ha q' - 1` are smoothing, differ by a smoothing
symbol. -/
theorem isSmoothing_sub_of_isSmoothing_properSharp_sub {a : Symbol n V W m}
    (ha : a.HasPropagationLE ε) {q q' : Symbol n W V (-m)} {δ : ℝ} (hq : q.HasPropagationLE δ)
    (hL : (q.properSharp hq a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing)
    (hR : (a.properSharp ha q' - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).IsSmoothing) :
    (q - q').IsSmoothing :=
  isSmoothing_sub_of_isAsymptoticSum_sharpTerm ((isSmoothing_properSharp_sub_iff_left hq).1 hL)
    ((isSmoothing_properSharp_sub_iff_right ha).1 hR)

/-- **Elliptic symbols have parametrix symbols of finite propagation.** If `a` is elliptic above
some radius, then for every `ε > 0` there is a symbol `q` of order `-m` and propagation at most
`ε` such that the composition symbol `q.properSharp hq a` of `Op(q) ∘ Op(a)` is `1` up to a
smoothing symbol, and so is the composition symbol `a.properSharp ha q` of `Op(a) ∘ Op(q)`
whenever `a` has finite propagation. -/
theorem IsEllipticAbove.exists_hasPropagationLE_isSmoothing_properSharp_sub {a : Symbol n V W m}
    {R : ℝ} (ha : a.IsEllipticAbove R) (hε : 0 < ε) :
    ∃ q : Symbol n W V (-m), ∃ hq : q.HasPropagationLE ε,
      (q.properSharp hq a - inclusion (neg_add_cancel m).ge (const (.id ℂ V))).IsSmoothing ∧
      ∀ ε' (ha' : a.HasPropagationLE ε'),
        (a.properSharp ha' q - inclusion (add_neg_cancel m).ge (const (.id ℂ W))).IsSmoothing := by
  obtain ⟨b, hbL, hbR⟩ := ha.exists_isAsymptoticSum_sharpTerm
  obtain ⟨q, hqb, hq⟩ := exists_isSmoothing_sub_and_hasPropagationLE b hε
  exact ⟨q, hq, (isSmoothing_properSharp_sub_iff_left hq).2
    (isAsymptoticSum_sharpTerm_of_isSmoothing_sub_left hbL hqb), fun _ ha' ↦
    (isSmoothing_properSharp_sub_iff_right ha').2
      (isAsymptoticSum_sharpTerm_of_isSmoothing_sub_right hbR hqb)⟩

/-! ### The operator identities -/

/-- **The parametrix identity.** If `q` has finite propagation and `Op(a) u` has compact support,
then `Op(q) (Op(a) u) = u + Op(r) u` for the symbol `r = q.properSharp hq a - 1`, which is
smoothing when `q` is a left parametrix symbol of `a`
(`TauCeti.Symbol.isSmoothing_properSharp_sub_iff_left`). -/
theorem quantizeSchwartzValue_quantizeSchwartzValue_eq_add {μ μ' : ℝ} {a : Symbol n V W μ}
    {q : Symbol n W V μ'} (hq : q.HasPropagationLE ε) (h : 0 ≤ μ' + μ)
    {u : SchwartzMap (CoordinateSpace n) V}
    (hu : HasCompactSupport (quantizeSchwartzValue a.coefficient u)) (x : CoordinateSpace n) :
    quantizeSchwartzValue q.coefficient (hu.toSchwartzMap (a.contDiff_quantizeSchwartzValue u)) x =
      u x + quantizeSchwartzValue
        (q.properSharp hq a - inclusion h (const (.id ℂ V))).coefficient u x := by
  rw [← quantizeSchwartzValue_properSharp_of_hasCompactSupport hq a hu x,
    ← sub_add_cancel (q.properSharp hq a).coefficient (inclusion h (const (.id ℂ V))).coefficient,
    ← coefficient_sub, quantizeSchwartzValue_coefficient_add, add_comm, coefficient_inclusion,
    funext (coefficient_const (n := n) (.id ℂ V)), quantizeSchwartzValue_id]

/-- **The properly supported left parametrix of a left parametrix symbol.** Let `b` be a left
parametrix symbol of a symbol `a` of order `m`, `1 ∼ ∑ₖ sharpTerm b a k`, with no condition on the
spatial support of `a`. For every `ε > 0` there are a symbol `q` of order `-m` and propagation at
most `ε` and a smoothing symbol `r` with

`Op(q) (Op(a) u) = u + Op(r) u`

for every Schwartz function `u` such that `Op(a) u` has compact support. -/
theorem exists_hasPropagationLE_quantizeSchwartzValue_eq_add_of_isAsymptoticSum
    {a : Symbol n V W m} {b : Symbol n W V (-m)}
    (hb : IsAsymptoticSum (m := fun k : ℕ ↦ -m + m - k) (inclusion (by simp) (const (.id ℂ V)))
      (b.sharpTerm a)) (hε : 0 < ε) :
    ∃ q : Symbol n W V (-m), q.HasPropagationLE ε ∧ ∃ r : Symbol n V V (-m + m), r.IsSmoothing ∧
      ∀ (u : SchwartzMap (CoordinateSpace n) V)
        (hu : HasCompactSupport (quantizeSchwartzValue a.coefficient u)) (x : CoordinateSpace n),
        quantizeSchwartzValue q.coefficient
          (hu.toSchwartzMap (a.contDiff_quantizeSchwartzValue u)) x =
          u x + quantizeSchwartzValue r.coefficient u x := by
  obtain ⟨q, hqb, hq⟩ := exists_isSmoothing_sub_and_hasPropagationLE b hε
  exact ⟨q, hq, _, (isSmoothing_properSharp_sub_iff_left hq).2
    (isAsymptoticSum_sharpTerm_of_isSmoothing_sub_left hb hqb),
    fun u hu x ↦ quantizeSchwartzValue_quantizeSchwartzValue_eq_add hq _ hu x⟩

/-- **The properly supported left parametrix.** Let `a` be a symbol of order `m` elliptic above
some radius, with no condition on its spatial support. For every `ε > 0` there are a symbol `q` of
order `-m` and propagation at most `ε` and a smoothing symbol `r` with

`Op(q) (Op(a) u) = u + Op(r) u`

for every Schwartz function `u` such that `Op(a) u` has compact support. -/
theorem IsEllipticAbove.exists_hasPropagationLE_quantizeSchwartzValue_eq_add
    {a : Symbol n V W m} {R : ℝ} (ha : a.IsEllipticAbove R) (hε : 0 < ε) :
    ∃ q : Symbol n W V (-m), q.HasPropagationLE ε ∧ ∃ r : Symbol n V V (-m + m), r.IsSmoothing ∧
      ∀ (u : SchwartzMap (CoordinateSpace n) V)
        (hu : HasCompactSupport (quantizeSchwartzValue a.coefficient u)) (x : CoordinateSpace n),
        quantizeSchwartzValue q.coefficient
          (hu.toSchwartzMap (a.contDiff_quantizeSchwartzValue u)) x =
          u x + quantizeSchwartzValue r.coefficient u x := by
  obtain ⟨b, hb, -⟩ := ha.exists_isAsymptoticSum_sharpTerm
  exact exists_hasPropagationLE_quantizeSchwartzValue_eq_add_of_isAsymptoticSum hb hε

/-- **The two-sided properly supported parametrix.** Let `a` be a symbol of order `m` elliptic
above some radius and of propagation at most `ε' ≥ 0`, so that `Op(a)` is properly supported. For
every `ε > 0` there are a symbol `q` of order `-m` and propagation at most `ε` and smoothing
symbols `r` and `r'` of propagation at most `ε + ε'` with

`Op(q) (Op(a) u) = u + Op(r) u` and `Op(a) (Op(q) v) = v + Op(r') v`

for all compactly supported Schwartz functions `u` and `v`. -/
theorem IsEllipticAbove.exists_hasPropagationLE_quantizeSchwartzValue_eq_add_and_eq_add
    {a : Symbol n V W m} {R : ℝ} (ha : a.IsEllipticAbove R) (ha' : a.HasPropagationLE ε')
    (hε' : 0 ≤ ε') (hε : 0 < ε) :
    ∃ q : Symbol n W V (-m), ∃ hq : q.HasPropagationLE ε,
      ∃ r : Symbol n V V (-m + m), r.IsSmoothing ∧ r.HasPropagationLE (ε + ε') ∧
      ∃ r' : Symbol n W W (m + -m), r'.IsSmoothing ∧ r'.HasPropagationLE (ε + ε') ∧
      (∀ (u : SchwartzMap (CoordinateSpace n) V) (hu : HasCompactSupport u)
        (x : CoordinateSpace n),
        quantizeSchwartzValue q.coefficient
            ((ha'.hasCompactSupport_quantizeSchwartzValue hu).toSchwartzMap
              (a.contDiff_quantizeSchwartzValue u)) x =
          u x + quantizeSchwartzValue r.coefficient u x) ∧
      ∀ (v : SchwartzMap (CoordinateSpace n) W) (hv : HasCompactSupport v)
        (x : CoordinateSpace n),
        quantizeSchwartzValue a.coefficient
            ((hq.hasCompactSupport_quantizeSchwartzValue hv).toSchwartzMap
              (q.contDiff_quantizeSchwartzValue v)) x =
          v x + quantizeSchwartzValue r'.coefficient v x := by
  obtain ⟨q, hq, hL, hR⟩ := ha.exists_hasPropagationLE_isSmoothing_properSharp_sub hε
  have hpos : 0 < ε + ε' := by linarith
  exact ⟨q, hq, _, hL, (hq.properSharp ha').sub ((hasPropagationLE_const _ hpos).inclusion _), _,
    hR ε' ha', ((ha'.properSharp hq).mono (add_comm ε' ε).le).sub
      ((hasPropagationLE_const _ hpos).inclusion _),
    fun u hu x ↦ quantizeSchwartzValue_quantizeSchwartzValue_eq_add hq _ _ x,
    fun v hv x ↦ quantizeSchwartzValue_quantizeSchwartzValue_eq_add ha' _ _ x⟩

end Symbol

namespace ClassicalSymbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W] {m ε : ℝ}

/-- **The properly supported left parametrix of an elliptic classical symbol.** If the principal
symbol of a classical symbol `a` of order `m` is invertible at every nonzero frequency, then for
every `ε > 0` there are a symbol `q` of order `-m` and propagation at most `ε` and a smoothing
symbol `r` with `Op(q) (Op(a) u) = u + Op(r) u` for every Schwartz function `u` such that
`Op(a) u` has compact support. Unlike
`TauCeti.Symbol.IsEllipticAbove.exists_hasPropagationLE_quantizeSchwartzValue_eq_add`, no radius
beyond which `a(x, ξ)` is invertible at all positions is needed. -/
theorem IsElliptic.exists_hasPropagationLE_quantizeSchwartzValue_eq_add
    {a : ClassicalSymbol n V W m} (ha : a.IsElliptic) (hε : 0 < ε) :
    ∃ q : Symbol n W V (-m), q.HasPropagationLE ε ∧ ∃ r : Symbol n V V (-m + m), r.IsSmoothing ∧
      ∀ (u : SchwartzMap (CoordinateSpace n) V)
        (hu : HasCompactSupport (quantizeSchwartzValue a.toSymbol.coefficient u))
        (x : CoordinateSpace n),
        quantizeSchwartzValue q.coefficient
          (hu.toSchwartzMap (a.toSymbol.contDiff_quantizeSchwartzValue u)) x =
          u x + quantizeSchwartzValue r.coefficient u x := by
  obtain ⟨b, hb⟩ := ha.exists_isAsymptoticSum_sharpTerm_left
  exact Symbol.exists_hasPropagationLE_quantizeSchwartzValue_eq_add_of_isAsymptoticSum hb hε

end ClassicalSymbol

end TauCeti
