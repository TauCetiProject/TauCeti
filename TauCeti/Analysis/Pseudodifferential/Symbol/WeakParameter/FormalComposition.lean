/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion
public import TauCeti.Analysis.Pseudodifferential.Symbol.WeakParameter.Deriv

/-!
# The terms of the composition expansion of weakly parameter-dependent symbols

The symbol of the composition of two pseudodifferential operators with symbols `b` and `a` has the
expansion `b # a ∼ ∑_α ((1/i)^|α| / α!) ∂_ξ^α b ∂_x^α a`. For weakly parameter-dependent symbols
(`TauCeti.WeakParameterSymbol`) the reciprocal spectral parameter `r` is a passive variable of each
term: the term with `k` derivatives on each factor is again weakly parameter-dependent, of
frequency order `m' + m - k` and the same anisotropy `d`. Its values are the terms of the
composition expansion of the values of `b` and `a`, and its parameter derivatives are given by
Leibniz's rule in `r`.

These terms are the building blocks of the formal composition of weakly parameter-dependent
symbols and of the parameter-elliptic parametrix of Grubb and Seeley, whose leading term is the
normalized resolvent `(1 - r p)⁻¹` (`TauCeti.WeakParameterSymbol.normalizedResolvent`).

## Main definitions and results

* `TauCeti.WeakParameterSymbol.sharpTerm b a k`: the weakly parameter-dependent symbol
  `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a` of frequency order `m' + m - k`, summed over the
  words `w` of length `k` in the coordinate directions
  (`TauCeti.WeakParameterSymbol.coefficient_sharpTerm`).
* `TauCeti.WeakParameterSymbol.toSymbol_sharpTerm`: at a parameter `r ∈ R` it is the term
  `TauCeti.Symbol.sharpTerm` of the composition expansion of the values `b(r)` and `a(r)`.
* `TauCeti.WeakParameterSymbol.iteratedDerivSymbol_sharpTerm`: **Leibniz's rule.** Its `j`-th
  parameter derivative is the sum of the terms `(j choose i) sharpTerm (∂_r^i b) (∂_r^(j - i) a) k`
  of the composition expansions of the parameter derivatives, each of order
  `m' + m - k + d j`.
* `TauCeti.WeakParameterSymbol.sharpTerm_succ_eq_zero_of_spatialDeriv_eq_zero`: if the right
  factor does not depend on the position, only the pointwise composition survives.

The definition by recursion on `k` follows `TauCeti.Symbol.sharpTerm` and
`TauCeti.ParameterSymbol.sharpTerm`.

## References

* G. Grubb and R. T. Seeley, *Weakly parametric pseudodifferential operators and Atiyah–Patodi–
  Singer boundary problems*, Invent. Math. 121 (1995), 481–529, §1.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (2.5)–(2.7).
-/

public section

noncomputable section

open Finset

namespace TauCeti

namespace WeakParameterSymbol

variable {n : ℕ} {R : TopologicalSpace.Opens ℂ} {V W U : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [CompleteSpace W]
  [NormedAddCommGroup U] [NormedSpace ℂ U] [CompleteSpace U] {d m : ℝ}

/-- The weakly parameter-dependent symbol `((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a` of
frequency order `m' + m - k`, the part of the composition expansion of `b # a` with `k` derivatives
on each factor. It is defined by the recursion `sharpTerm b a 0 = b ∘ a` and
`sharpTerm b a (k + 1) = (-i / (k + 1)) ∑ⱼ sharpTerm (∂_{ξⱼ} b) (∂_{xⱼ} a) k`; the closed form is
`TauCeti.WeakParameterSymbol.coefficient_sharpTerm`. -/
def sharpTerm : {m' : ℝ} → WeakParameterSymbol n R W U d m' → WeakParameterSymbol n R V W d m →
    (k : ℕ) → WeakParameterSymbol n R V U d (m' + m - k)
  | _, b, a, 0 => inclusion (by simp) le_rfl (b.comp a)
  | _, b, a, k + 1 => (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      inclusion (by push_cast; linarith) le_rfl
        ((frequencyDeriv j b).sharpTerm (spatialDeriv j a) k)

variable {m' : ℝ}

theorem sharpTerm_zero (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) :
    b.sharpTerm a 0 = inclusion (by simp) le_rfl (b.comp a) := by
  rw [sharpTerm]

theorem sharpTerm_succ (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) (k : ℕ) :
    b.sharpTerm a (k + 1) = (-Complex.I / (k + 1 : ℂ)) • ∑ j : Fin n,
      inclusion (by push_cast; linarith) le_rfl
        ((frequencyDeriv j b).sharpTerm (spatialDeriv j a) k) := by
  rw [sharpTerm]

/-- The term without derivatives is the pointwise composition. -/
@[simp]
theorem coefficient_sharpTerm_zero (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) (p : CoordinateSpace n × CoordinateSpace n) (r : ℂ) :
    (b.sharpTerm a 0).coefficient p r = (b.coefficient p r).comp (a.coefficient p r) := by
  simp [sharpTerm_zero]

/-- The composition terms vanish when the right factor is zero. -/
@[simp]
theorem sharpTerm_zero_right (b : WeakParameterSymbol n R W U d m') (k : ℕ) :
    b.sharpTerm (0 : WeakParameterSymbol n R V W d m) k = 0 := by
  induction k generalizing m' b with
  | zero => simp [sharpTerm_zero]
  | succ k ih => simp [sharpTerm_succ, ih]

/-- If the right factor does not depend on the position, the terms with derivatives vanish: only
the pointwise composition `sharpTerm b a 0 = b ∘ a` remains of the composition expansion. -/
theorem sharpTerm_succ_eq_zero_of_spatialDeriv_eq_zero (b : WeakParameterSymbol n R W U d m')
    {a : WeakParameterSymbol n R V W d m} (ha : ∀ l, spatialDeriv l a = 0) (k : ℕ) :
    b.sharpTerm a (k + 1) = 0 := by
  simp [sharpTerm_succ, ha]

/-- **The values of the composition terms.** At a parameter `r ∈ R`, the term `sharpTerm b a k`
is the term of the composition expansion of the values `b(r)` and `a(r)`. -/
@[simp]
theorem toSymbol_sharpTerm (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) (k : ℕ) {r : ℂ} (hr : r ∈ R) :
    (b.sharpTerm a k).toSymbol hr = (b.toSymbol hr).sharpTerm (a.toSymbol hr) k := by
  induction k generalizing m' b a with
  | zero => exact Symbol.ext (funext fun p ↦ by simp)
  | succ k ih =>
    refine Symbol.ext (funext fun p ↦ ?_)
    have h (j : Fin n) : ((frequencyDeriv j b).sharpTerm (spatialDeriv j a) k).coefficient p r =
        ((Symbol.frequencyDeriv j (b.toSymbol hr)).sharpTerm
          (Symbol.spatialDeriv j (a.toSymbol hr)) k).coefficient p := by
      rw [← coefficient_toSymbol _ hr, ih, toSymbol_frequencyDeriv, toSymbol_spatialDeriv]
    simp [sharpTerm_succ, Symbol.coefficient_sharpTerm_succ, h]

/-- **Closed form of the composition terms.** At a parameter `r ∈ R`, `sharpTerm b a k` is
`((-i)ᵏ / k!) ∑_{|w| = k} ∂_ξ^w b ∘ ∂_x^w a`, the sum over the words `w` of length `k` in the
coordinate directions. -/
theorem coefficient_sharpTerm (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) (k : ℕ) (x ξ : CoordinateSpace n) {r : ℂ}
    (hr : r ∈ R) :
    (b.sharpTerm a k).coefficient (x, ξ) r = ((-Complex.I) ^ k / k.factorial : ℂ) •
      ∑ w : Fin k → Fin n,
        (mixedDeriv [] (List.ofFn w) (fun p ↦ b.coefficient p r) x ξ).comp
          (mixedDeriv (List.ofFn w) [] (fun p ↦ a.coefficient p r) x ξ) := by
  rw [← coefficient_toSymbol _ hr, toSymbol_sharpTerm, Symbol.coefficient_sharpTerm,
    funext (coefficient_toSymbol b hr), funext (coefficient_toSymbol a hr)]

/-- **Leibniz's rule for the parameter derivatives of the composition terms.** The `j`-th
parameter derivative of `sharpTerm b a k` is the sum of the terms
`(j choose i) sharpTerm (∂_r^i b) (∂_r^(j - i) a) k` of the composition expansions of the parameter
derivatives, each of order `m' + d i + m + d (j - i) - k = m' + m - k + d j`. -/
@[simp]
theorem iteratedDerivSymbol_sharpTerm (b : WeakParameterSymbol n R W U d m')
    (a : WeakParameterSymbol n R V W d m) (k j : ℕ) {r : ℂ} (hr : r ∈ R) :
    (b.sharpTerm a k).iteratedDerivSymbol j hr = ∑ i : Fin (j + 1), (j.choose i : ℂ) •
      Symbol.inclusion (le_of_eq (by rw [sub_add_eq_add_sub, ← add_mul_add_add_mul_sub_eq i]))
        ((b.iteratedDerivSymbol i hr).sharpTerm (a.iteratedDerivSymbol (j - i) hr) k) := by
  induction k generalizing m' b a with
  | zero => exact Symbol.ext (funext fun p ↦ by simp [sharpTerm_zero])
  | succ k ih =>
    refine Symbol.ext (funext fun p ↦ ?_)
    -- the parameter derivatives of `∂_{ξ_l} b` and `∂_{x_l} a` are those of `b` and `a`
    -- differentiated in the frequency and in the position
    have h (l : Fin n) (i : Fin (j + 1)) :
        (((frequencyDeriv l b).iteratedDerivSymbol i hr).sharpTerm
          ((spatialDeriv l a).iteratedDerivSymbol (j - i) hr) k).coefficient p =
        ((Symbol.frequencyDeriv l (b.iteratedDerivSymbol i hr)).sharpTerm
          (Symbol.spatialDeriv l (a.iteratedDerivSymbol (j - i) hr)) k).coefficient p := by
      rw [iteratedDerivSymbol_frequencyDeriv, iteratedDerivSymbol_spatialDeriv,
        Symbol.coefficient_sharpTerm_congr (Symbol.coefficient_inclusion _ _) rfl]
    simp only [sharpTerm_succ, iteratedDerivSymbol_smul, iteratedDerivSymbol_sum,
      iteratedDerivSymbol_inclusion, ih, Symbol.coefficient_smul, Symbol.coefficient_sum,
      Symbol.coefficient_inclusion, Pi.smul_apply, Finset.sum_apply, h,
      Symbol.coefficient_sharpTerm_succ, Finset.smul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun l _ ↦ smul_comm _ _ _

end WeakParameterSymbol

end TauCeti
