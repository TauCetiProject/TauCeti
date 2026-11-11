/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.Parametrix
import TauCeti.Algebra.BigOperators.Intervals

/-!
# The composition of classical symbols

Let `a ∼ ∑ᵢ a_{m'-i}` and `b ∼ ∑ⱼ b_{m-j}` be classical symbols of orders `m'` and `m`, with `b`
vanishing for positions outside a compact set. This file proves the **composition theorem of the
classical symbol calculus**: the composition symbol `a # b` (`TauCeti.Symbol.sharp`), whose
quantization is `Op(a) ∘ Op(b)`, is a classical symbol of order `m' + m`, and its homogeneous
terms are the formal composition `TauCeti.ClassicalSymbol.sharpTerms a.term b.term` of the two
expansions,

`(a # b)_{m'+m-k} = ∑_{i + j + r = k} ((-i)ʳ / r!) ∑_{|w| = r} ∂_ξ^w a_{m'-i} ∘ ∂_x^w b_{m-j}`.

Through it, the formal left inverse of an elliptic classical symbol
(`TauCeti.ClassicalSymbol.exists_sharpTerms_eq_left`) becomes a left parametrix of its
quantization.

## Main declarations

* `TauCeti.ClassicalSymbol.sharpTerm a b k`: the term `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b`
  of the composition expansion (`TauCeti.Symbol.sharpTerm`) of two classical symbols, as a
  classical symbol of order `m' + m - k` (`ClassicalSymbol.toSymbol_sharpTerm`), whose homogeneous
  terms are the sums `∑_{i + j = l} HomogeneousSymbol.sharpTerm k a_{m'-i} b_{m-j}`
  (`ClassicalSymbol.coefficient_term_sharpTerm`).
* `TauCeti.ClassicalSymbol.sharp`: **the composition of classical symbols.** For classical `a` and
  `b` with `b` of compact spatial support, `a # b` is classical with the homogeneous terms
  `sharpTerms a.term b.term`; its principal symbol is `σ(a) ∘ σ(b)`
  (`ClassicalSymbol.principal_sharp`).
* `TauCeti.ClassicalSymbol.exists_isSmoothing_sharp_sub_const` and
  `TauCeti.ClassicalSymbol.exists_leftParametrix`: **the left parametrix.** An elliptic
  classical symbol `a` of order `m` with compact spatial support has a classical symbol `q` of
  order `-m`, with principal symbol `σ(a)⁻¹`, such that `q # a - 1` is smoothing, so that
  `Op(q) (Op(a) u) = u + Op(r) u` for a smoothing symbol `r` and every Schwartz function `u`.

## Proof outline

By the asymptotic expansion of the composition symbol
(`TauCeti.Symbol.sharp_eq_sum_sharpTerm_add_sharpRemainder`), `a # b` is the sum of the terms
`Symbol.sharpTerm a b k`, `k < N`, up to a symbol of order `m' + m - N`. Each of these terms is
built from frequency derivatives of `a`, spatial derivatives of `b` and pointwise compositions,
which are all classical (`ClassicalSymbol.frequencyDeriv`, `ClassicalSymbol.spatialDeriv`,
`ClassicalSymbol.comp`), so it is a classical symbol of order `m' + m - k`, whose remainder after
`N - k` terms has order `m' + m - N`. Collecting the homogeneous terms of total degree drop `l < N`
of all of them gives the terms `sharpTerms a.term b.term l`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Theorem 18.1.8 and
  §18.1.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (2.5)–(2.7) and §4.
-/

public section

noncomputable section

open Finset
open scoped SchwartzMap

namespace TauCeti

namespace ClassicalSymbol

open HomogeneousSymbol

variable {n : ℕ} {m m' : ℝ} {V W U : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U] [NormedSpace ℂ U]

/-! ### The terms of the composition expansion -/

section Term

/-- The term `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w a ∘ ∂_x^w b` of the composition expansion of two
classical symbols, as a classical symbol of order `m' + m - k`. Its full symbol is
`Symbol.sharpTerm a b k` (`toSymbol_sharpTerm`), and its homogeneous terms are the sums
`∑_{i + j = l} HomogeneousSymbol.sharpTerm k a_{m'-i} b_{m-j}` (`coefficient_term_sharpTerm`). It
is defined by the recursion of `Symbol.sharpTerm`. -/
def sharpTerm : {m m' : ℝ} → ClassicalSymbol n W U m' → ClassicalSymbol n V W m → (k : ℕ) →
    ClassicalSymbol n V U (m' + m - k)
  | _, _, a, b, 0 => inclusion 0 (by simp) (a.comp b)
  | _, _, a, b, k + 1 => inclusion 0 (by push_cast; ring)
      ((-Complex.I / (k + 1)) • ∑ j, sharpTerm (frequencyDeriv j a) (spatialDeriv j b) k)

/-- The full symbol of `ClassicalSymbol.sharpTerm a b k` is the term `Symbol.sharpTerm` of the
composition expansion of the full symbols. -/
@[simp]
theorem toSymbol_sharpTerm (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m) (k : ℕ) :
    (a.sharpTerm b k).toSymbol = a.toSymbol.sharpTerm b.toSymbol k := by
  induction k generalizing m' a b with
  | zero =>
    rw [sharpTerm, Symbol.sharpTerm_zero, toSymbol_inclusion, toSymbol_comp]
  | succ k ih =>
    rw [sharpTerm, Symbol.sharpTerm_succ, toSymbol_inclusion, toSymbol_smul, toSymbol_sum]
    simp only [ih, toSymbol_frequencyDeriv, toSymbol_spatialDeriv]

/-- The homogeneous term of degree `m' + m - k - l` of `ClassicalSymbol.sharpTerm a b k` is
`∑_{i + j = l} HomogeneousSymbol.sharpTerm k a_{m'-i} b_{m-j}`. -/
theorem coefficient_term_sharpTerm (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m)
    (k l : ℕ) :
    ((a.sharpTerm b k).term l).coefficient =
      ∑ i ∈ range (l + 1),
        (HomogeneousSymbol.sharpTerm k (a.term i) (b.term (l - i))).coefficient := by
  induction k generalizing m' a b with
  | zero =>
    rw [sharpTerm, term_inclusion_zero, coefficient_castDegree, term_comp]
    funext z
    simp [coefficient_compTerms]
  | succ k ih =>
    rw [sharpTerm, term_inclusion_zero, coefficient_castDegree, term_smul, term_sum]
    funext z
    simp only [HomogeneousSymbol.coefficient_smul, HomogeneousSymbol.coefficient_sum,
      Pi.smul_apply, Finset.sum_apply, ih, HomogeneousSymbol.sharpTerm_succ, term_frequencyDeriv,
      term_spatialDeriv, sharpTerm_castDegree_left, coefficient_castDegree, smul_sum]
    exact Finset.sum_comm

end Term

variable [CompleteSpace W] [CompleteSpace U]

/-- The remainders of the composition of classical symbols after `N` terms of the formal
composition have order `m' + m - N`. -/
private theorem exists_remainder_sharp (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m)
    (hb : b.toSymbol.HasCompactSpatialSupport) (χ : FrequencyCutoff (CoordinateSpace n)) (N : ℕ) :
    ∃ r : Symbol n V U (m' + m - N), ∀ p, r.coefficient p =
      (a.toSymbol.sharp b.toSymbol hb).coefficient p -
        ∑ l ∈ range N, χ p.2 • (sharpTerms a.term b.term l).coefficient p := by
  -- The order `m' + m - k - (N - k)` of the remainder of the `k`-th term is at most `m' + m - N`.
  have hle : ∀ k : ℕ, m' + m - k - ((N - k : ℕ) : ℝ) ≤ m' + m - N := fun k ↦ by
    have : (N : ℝ) ≤ ((N - k : ℕ) : ℝ) + k := by exact_mod_cast (le_tsub_add : N ≤ N - k + k)
    linarith
  -- `a # b = ∑_{k < N} sharpTerm a b k + R_N`, and each `sharpTerm a b k` is classical.
  refine ⟨a.toSymbol.sharpRemainder b.toSymbol hb N +
    ∑ k ∈ range N, Symbol.inclusion (hle k) ((a.sharpTerm b k).remainder χ (N - k)), fun p ↦ ?_⟩
  simp only [Symbol.coefficient_add, Symbol.coefficient_sum, Symbol.coefficient_inclusion,
    Pi.add_apply, Finset.sum_apply, Symbol.coefficient_sharpRemainder, Pi.sub_apply,
    coefficient_remainder, toSymbol_sharpTerm, Finset.sum_sub_distrib, coefficient_sharpTerms,
    coefficient_term_sharpTerm, ← smul_sum]
  rw [sum_range_diag_flip_triple
    (fun k i j ↦ (HomogeneousSymbol.sharpTerm k (a.term i) (b.term j)).coefficient p)]
  abel

/-! ### The composition of classical symbols -/

/-- **The composition of classical symbols.** For classical symbols `a` of order `m'` and `b` of
order `m`, with `b` of compact spatial support, the composition symbol `a # b` of
`Op(a) ∘ Op(b)` is a classical symbol of order `m' + m`, whose homogeneous terms are the formal
composition `sharpTerms a.term b.term` of the expansions of `a` and `b`. -/
def sharp (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m)
    (hb : b.toSymbol.HasCompactSpatialSupport) : ClassicalSymbol n V U (m' + m) where
  toSymbol := a.toSymbol.sharp b.toSymbol hb
  term := sharpTerms a.term b.term
  exists_remainder' := ⟨default, exists_remainder_sharp a b hb default⟩

variable (a : ClassicalSymbol n W U m') (b : ClassicalSymbol n V W m)
  (hb : b.toSymbol.HasCompactSpatialSupport)

@[simp]
theorem toSymbol_sharp : (a.sharp b hb).toSymbol = a.toSymbol.sharp b.toSymbol hb :=
  (rfl)

@[simp]
theorem term_sharp (k : ℕ) : (a.sharp b hb).term k = sharpTerms a.term b.term k :=
  (rfl)

/-- **The principal symbol is multiplicative** for the composition of classical symbols:
`σ(a # b) = σ(a) ∘ σ(b)`. -/
@[simp]
theorem principal_sharp : (a.sharp b hb).principal = a.principal.comp b.principal := by
  ext1
  funext z
  simp [coefficient_principal]

theorem add_sharp (a₁ a₂ : ClassicalSymbol n W U m') :
    (a₁ + a₂).sharp b hb = a₁.sharp b hb + a₂.sharp b hb :=
  ext (Symbol.add_sharp _ _ hb)

theorem sharp_add {b₁ b₂ : ClassicalSymbol n V W m} (hb₁ : b₁.toSymbol.HasCompactSpatialSupport)
    (hb₂ : b₂.toSymbol.HasCompactSpatialSupport) :
    a.sharp (b₁ + b₂) (hb₁.add hb₂) = a.sharp b₁ hb₁ + a.sharp b₂ hb₂ :=
  ext (Symbol.sharp_add _ hb₁ hb₂)

@[simp]
theorem smul_sharp (c : ℂ) : (c • a).sharp b hb = c • a.sharp b hb :=
  ext (Symbol.smul_sharp c _ hb)

@[simp]
theorem sharp_smul (c : ℂ) : a.sharp (c • b) (hb.smul c) = c • a.sharp b hb :=
  ext (Symbol.sharp_smul _ hb c)

/-! ### The left parametrix of an elliptic classical symbol -/

section Parametrix

variable [CompleteSpace V] {a : ClassicalSymbol n V W m}

/-- **The left parametrix, on symbols.** An elliptic classical symbol `a` of order `m` with
compact spatial support has a classical left inverse modulo smoothing symbols: a classical
symbol `q` of order `-m`, with principal symbol `σ(a)⁻¹`, such that `q # a - 1` is smoothing. -/
theorem exists_isSmoothing_sharp_sub_const (ha : a.principal.IsElliptic)
    (hs : a.toSymbol.HasCompactSpatialSupport) :
    ∃ q : ClassicalSymbol n W V (-m), q.principal = a.principal.inverse ha ∧
      (q.toSymbol.sharp a.toSymbol hs - Symbol.inclusion (neg_add_cancel m).symm.le
        (Symbol.const (ContinuousLinearMap.id ℂ V))).IsSmoothing := by
  obtain ⟨q, hq, h0, hsucc⟩ := a.exists_sharpTerms_eq_left ha
  refine ⟨q, hq, ?_⟩
  -- The terms of `q # a` are those of the cut-off identity `χ(ξ) id`.
  set e := ofHomogeneous default
    ((HomogeneousSymbol.id (CoordinateSpace n) (CoordinateSpace n) V).castDegree
      (neg_add_cancel m).symm)
  have hterm : (q.sharp a hs).term = e.term := funext fun k ↦ by
    cases k with
    | zero =>
      ext1
      rw [term_sharp, h0, ← coefficient_principal, principal_ofHomogeneous]
      simp
    | succ k => rw [term_sharp, hsucc, term_ofHomogeneous_succ]
  -- `χ(ξ) id` and `id` differ only at frequencies of norm less than `2`.
  set d := e.toSymbol - Symbol.inclusion (neg_add_cancel m).symm.le
    (Symbol.const (ContinuousLinearMap.id ℂ V))
  have hd : ∀ x ξ, 2 ≤ ‖ξ‖ → d.coefficient (x, ξ) = 0 := fun x ξ hξ ↦ by
    have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (by linarith)
    simp [d, e, toSymbol_ofHomogeneous, coefficient_cutoffSymbol_of_two_le_norm _ _ hξ,
      coefficient_id hξ0]
  have h :=
    (isSmoothing_toSymbol_sub_iff.2 hterm).add (Symbol.isSmoothing_of_coefficient_eq_zero 2 hd)
  rwa [toSymbol_sharp, sub_add_sub_cancel] at h

/-- **The left parametrix.** An elliptic classical symbol `a` of order `m` with compact spatial
support has a classical symbol `q` of order `-m`, with principal symbol `σ(a)⁻¹`, and a smoothing
symbol `r` such that `Op(q) (Op(a) u) = u + Op(r) u` for every Schwartz function `u`. -/
theorem exists_leftParametrix (ha : a.principal.IsElliptic)
    (hs : a.toSymbol.HasCompactSpatialSupport) :
    ∃ q : ClassicalSymbol n W V (-m), q.principal = a.principal.inverse ha ∧
      ∃ r : Symbol n V V (-m + m), r.IsSmoothing ∧ ∀ (u : 𝓢(CoordinateSpace n, V)) x,
        quantizeSchwartzValue q.toSymbol.coefficient
          ((hs.hasCompactSupport_quantizeSchwartzValue u).toSchwartzMap
            (a.toSymbol.contDiff_quantizeSchwartzValue u)) x =
          u x + quantizeSchwartzValue r.coefficient u x := by
  obtain ⟨q, hq, hr⟩ := exists_isSmoothing_sharp_sub_const ha hs
  refine ⟨q, hq, _, hr, fun u x ↦ ?_⟩
  set c := Symbol.inclusion (neg_add_cancel m).symm.le
    (Symbol.const (ContinuousLinearMap.id ℂ V) : Symbol n V V 0)
  have hc : (q.toSymbol.sharp a.toSymbol hs).coefficient =
      c.coefficient + (q.toSymbol.sharp a.toSymbol hs - c).coefficient := by
    simp
  rw [← Symbol.quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue hs, hc]
  obtain ⟨C, -, hC⟩ := c.exists_bound_coefficient_slice x
  obtain ⟨C', -, hC'⟩ := (q.toSymbol.sharp a.toSymbol hs - c).exists_bound_coefficient_slice x
  rw [quantizeSchwartzValue_add_left (c.continuous_coefficient_slice x).aestronglyMeasurable hC
    ((q.toSymbol.sharp a.toSymbol hs - c).continuous_coefficient_slice x).aestronglyMeasurable hC']
  rw [show c.coefficient = fun _ ↦ ContinuousLinearMap.id ℂ V from funext fun _ ↦ by simp [c],
    quantizeSchwartzValue_id]

end Parametrix

end ClassicalSymbol

end TauCeti
