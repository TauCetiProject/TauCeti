/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol
public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.Homogeneous
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Classical symbols

A *classical* (one-step polyhomogeneous) symbol of order `m` on `ℝⁿ` is a symbol `a ∈ S^m_{1,0}`
with an asymptotic expansion `a ∼ ∑ⱼ χ(ξ) a_{m-j}(x, ξ)` into homogeneous terms: each `a_{m-j}`
is smooth away from `ξ = 0` and positively homogeneous of degree `m - j` in `ξ`, `χ` is a frequency
cutoff, and for every `N` the remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` is a symbol of order `m - N`.
The leading term `a_m` is the principal symbol. Differential operators with smooth coefficients
and their parametrices have classical symbols, and the principal symbol of a classical symbol is
what ellipticity, the symbol calculus and index theory are phrased in.

This file first turns a homogeneous term into a symbol. For a homogeneous symbol `a` of degree `m`
and a frequency cutoff `χ`, `TauCeti.HomogeneousSymbol.cutoffSymbol χ a` is the symbol
`χ(ξ) a(x, ξ)` of order `m`. Changing the cutoff changes it by a smoothing symbol
(`TauCeti.HomogeneousSymbol.isSmoothing_cutoffSymbol_sub_cutoffSymbol`), and it has no order
below `m` unless `a = 0` (`TauCeti.HomogeneousSymbol.eq_zero_of_coefficient_eq_cutoffSymbol`):
homogeneity transports any extra decay at large frequencies to every frequency.

It then defines the carrier `TauCeti.ClassicalSymbol n V W m` of classical symbols, with an
actual remainder symbol `TauCeti.ClassicalSymbol.remainder χ N` of order `m - N` after `N` terms,
and proves:

* `TauCeti.ClassicalSymbol.exists_remainder`: the expansion holds for every frequency cutoff, not
  only for the one used to define the symbol;
* `TauCeti.ClassicalSymbol.term_eq_of_toSymbol_eq` and `TauCeti.ClassicalSymbol.ext`: the
  homogeneous terms are determined by the symbol, so a classical symbol is determined by its full
  symbol;
* the classical symbols of order `m` form a complex vector space, termwise;
* `TauCeti.ClassicalSymbol.principal`, the principal symbol, with
  `TauCeti.ClassicalSymbol.exists_sub_cutoffSymbol_principal`: the full symbol and its cut-off
  principal symbol differ by a symbol of order `m - 1`;
* `TauCeti.ClassicalSymbol.isSmoothing_toSymbol_iff`: a classical symbol is smoothing exactly when
  all of its homogeneous terms vanish; `TauCeti.ClassicalSymbol.ofIsSmoothing` makes every
  smoothing symbol classical;
* `TauCeti.ClassicalSymbol.ofHomogeneous`: the classical symbol `χ(ξ) a(x, ξ)` of a single
  homogeneous term, whose principal symbol is `a`.

The derivative estimates for `χ(ξ) a(x, ξ)` come from those of the homogeneous term
(`TauCeti.exists_norm_iteratedFDeriv_le_of_smul_snd_eq`), read on the coordinate directions
through `TauCeti.mixedDeriv_eq_iteratedFDeriv`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, Definition 18.1.5
  and Proposition 18.1.3.
* M. E. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, September 2008,
  Lecture I, (1.17).
* R. B. Melrose, *Introduction to Microlocal Analysis*, Chapter 2.
-/

public section

noncomputable section

open Filter Topology
open scoped ContDiff

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

namespace HomogeneousSymbol

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol of degree `m` satisfies the symbol
estimates of order `m`. -/
private theorem exists_bound_mixedDeriv_smul_coefficient
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (χ : FrequencyCutoff (CoordinateSpace n)) {K : Set (CoordinateSpace n)} (hK : IsCompact K)
    (α β : List (Fin n)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, ∀ ξ,
      ‖mixedDeriv α β (fun p => χ p.2 • a.coefficient p) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by
  set L := mixedDirections α β
  have hg := a.contDiff_smul_coefficient χ
  -- Near the zero frequency the cut-off term is smooth, so compactness bounds its derivatives.
  obtain ⟨C₁, hC₁, h₁⟩ := (hg.of_le (mod_cast le_top) : ContDiff ℝ (α.length + β.length) _)
    |>.exists_norm_iteratedFDeriv_le_one_add_norm_sq_rpow_of_norm_le hK 2 (m - β.length)
  -- At large frequencies it is `a`, whose derivatives homogeneity controls.
  obtain ⟨C₂, hC₂, h₂⟩ := exists_norm_iteratedFDeriv_le_of_smul_snd_eq hK
    a.contDiffOn_coefficient (fun x ξ _ t ht => a.homogeneous x ξ t ht) (k := L.length)
    (mod_cast le_top)
  refine ⟨max C₁ (C₂ * 2 ^ (|m - β.length| / 2)), le_max_of_le_left hC₁, fun x hx ξ => ?_⟩
  rcases le_or_gt ‖ξ‖ 2 with hξ | hξ
  · exact (norm_mixedDeriv_le hg α β x ξ).trans <| (h₁ x hx ξ hξ).trans <|
      mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · have hξ0 : 0 < ‖ξ‖ := two_pos.trans hξ
    have heq : (fun p : CoordinateSpace n × CoordinateSpace n => χ p.2 • a.coefficient p)
        =ᶠ[𝓝 (x, ξ)] a.coefficient := by
      filter_upwards [continuous_snd.continuousAt.eventually
        (χ.eventuallyEq_one_of_two_lt_norm hξ)] with q hq
      simp [hq]
    rw [mixedDeriv_eq_iteratedFDeriv hg, heq.iteratedFDeriv ℝ L.length |>.eq_of_nhds]
    refine (h₂ x hx ξ (norm_pos_iff.1 hξ0) _).trans ?_
    rw [prod_norm_mixedDirections, abs_of_pos (inv_pos.2 hξ0), mul_assoc, ← Real.rpow_natCast,
      Real.inv_rpow hξ0.le, ← Real.rpow_neg hξ0.le, ← Real.rpow_add hξ0, ← sub_eq_add_neg]
    calc C₂ * ‖ξ‖ ^ (m - β.length)
        ≤ C₂ * (2 ^ (|m - β.length| / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2)) :=
          mul_le_mul_of_nonneg_left (norm_rpow_le_one_add_norm_sq_rpow (by linarith) _) hC₂
      _ = C₂ * 2 ^ (|m - β.length| / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - β.length) / 2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)

variable (χ χ' : FrequencyCutoff (CoordinateSpace n))

/-- The cut-off term `χ(ξ) a(x, ξ)` of a homogeneous symbol `a` of degree `m`, as a symbol of order
`m`. The cutoff removes the singularity of `a` at `ξ = 0` and leaves `a` unchanged at frequencies
of norm at least `2`. -/
def cutoffSymbol :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →ₗ[ℂ] Symbol n V W m where
  toFun a :=
    { coefficient p := χ p.2 • a.coefficient p
      contDiff_coefficient := a.contDiff_smul_coefficient χ
      exists_bound _ hK α β := exists_bound_mixedDeriv_smul_coefficient a χ hK α β }
  map_add' a b := Symbol.ext <| funext fun p => by simp [smul_add]
  map_smul' c a := Symbol.ext <| funext fun p => by simp [smul_comm (χ p.2) c]

@[simp]
theorem coefficient_cutoffSymbol
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoffSymbol χ a).coefficient p = χ p.2 • a.coefficient p :=
  (rfl)

/-- At frequencies of norm at least `2` the cut-off term is the homogeneous symbol itself. -/
theorem coefficient_cutoffSymbol_of_two_le_norm
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) {x ξ : CoordinateSpace n}
    (hξ : 2 ≤ ‖ξ‖) : (cutoffSymbol χ a).coefficient (x, ξ) = a.coefficient (x, ξ) := by
  simp [χ.apply_eq_one_of_two_le_norm hξ]

/-- **Independence of the cutoff.** Changing the frequency cutoff changes the cut-off term by a
smoothing symbol: the two cut-off terms agree at all frequencies of norm at least `2`. -/
theorem isSmoothing_cutoffSymbol_sub_cutoffSymbol
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    (cutoffSymbol χ a - cutoffSymbol χ' a).IsSmoothing := Symbol.isSmoothing_iff.2 fun _ =>
  ⟨Symbol.ofBoundedFrequencySupport _ (cutoffSymbol χ a - cutoffSymbol χ' a).contDiff_coefficient
    2 fun x ξ hξ => by
      simp [χ.apply_eq_one_of_two_le_norm hξ, χ'.apply_eq_one_of_two_le_norm hξ],
    Symbol.coefficient_ofBoundedFrequencySupport _ _ _ _⟩

/-- A homogeneous symbol of degree `m` whose cut-off term is a symbol of some order `m' < m`
vanishes. -/
theorem eq_zero_of_coefficient_eq_cutoffSymbol {m' : ℝ} (hm : m' < m)
    {a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m} (b : Symbol n V W m')
    (hb : b.coefficient = (cutoffSymbol χ a).coefficient) : a = 0 := by
  refine ext_of_ne_zero fun x ξ hξ => ?_
  rw [coefficient_zero, Pi.zero_apply, ← norm_le_zero_iff]
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  obtain ⟨C, hC, hbC⟩ := b.exists_bound {x} isCompact_singleton [] []
  set D := C * 2 ^ (|m'| / 2) * ‖ξ‖ ^ m'
  -- For `t ≥ 2 / ‖ξ‖`, homogeneity at `t • ξ` and the bound of order `m'` there give
  -- `t ^ m ‖a (x, ξ)‖ ≤ D t ^ m'`.
  have key : ∀ᶠ t in atTop, ‖a.coefficient (x, ξ)‖ ≤ D * t ^ (m' - m) := by
    filter_upwards [eventually_ge_atTop (2 / ‖ξ‖), eventually_gt_atTop 0] with t ht ht0
    have htξ : 2 ≤ ‖t • ξ‖ := by
      rwa [norm_smul, Real.norm_of_nonneg ht0.le, ← div_le_iff₀ hξ0]
    have h := hbC x rfl (t • ξ)
    rw [mixedDeriv_nil_nil, hb, coefficient_cutoffSymbol_of_two_le_norm χ a htξ,
      a.homogeneous x ξ t ht0, norm_smul, Real.norm_of_nonneg (by positivity),
      List.length_nil, Nat.cast_zero, sub_zero] at h
    have hw := one_add_norm_sq_rpow_le_norm_rpow (by linarith : 1 ≤ ‖t • ξ‖) m'
    rw [norm_smul, Real.norm_of_nonneg ht0.le, Real.mul_rpow ht0.le hξ0.le] at hw
    refine le_of_mul_le_mul_left ?_ (Real.rpow_pos_of_pos ht0 m)
    calc t ^ m * ‖a.coefficient (x, ξ)‖
        ≤ C * (2 ^ (|m'| / 2) * (t ^ m' * ‖ξ‖ ^ m')) :=
          h.trans (mul_le_mul_of_nonneg_left
            (by rw [norm_smul, Real.norm_of_nonneg ht0.le]; exact hw) hC)
      _ = t ^ m * (D * t ^ (m' - m)) := by
          rw [Real.rpow_sub ht0]
          field_simp
          ring
  have hlim : Tendsto (fun t : ℝ => D * t ^ (m' - m)) atTop (𝓝 0) := by
    simpa [neg_sub] using (tendsto_rpow_neg_atTop (by linarith : 0 < m - m')).const_mul D
  exact ge_of_tendsto hlim key

end HomogeneousSymbol

open HomogeneousSymbol

variable (n V W m) in
/-- A classical symbol of order `m` on `ℝⁿ`: a symbol `a` of order `m` together with homogeneous
terms `a_{m-j}` of degree `m - j` for `j = 0, 1, 2, …`, such that for some frequency cutoff `χ` and
every `N`, the remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` is a symbol of order `m - N`. The expansion
then holds for every cutoff (`TauCeti.ClassicalSymbol.exists_remainder`), and the terms are
determined by the symbol (`TauCeti.ClassicalSymbol.ext`). -/
structure ClassicalSymbol where
  /-- The full symbol. -/
  toSymbol : Symbol n V W m
  /-- The homogeneous term `a_{m-j}` of degree `m - j`. -/
  term : (j : ℕ) → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W (m - j)
  /-- For some frequency cutoff `χ`, every remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` has order `m - N`;
  use `TauCeti.ClassicalSymbol.exists_remainder` for an arbitrary cutoff. -/
  exists_remainder' : ∃ χ : FrequencyCutoff (CoordinateSpace n), ∀ N : ℕ,
    ∃ r : Symbol n V W (m - N), ∀ p,
      r.coefficient p =
        toSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (term j).coefficient p

namespace ClassicalSymbol

section Remainder

variable (a : ClassicalSymbol n V W m) (χ : FrequencyCutoff (CoordinateSpace n))

/-- **Independence of the cutoff.** For every frequency cutoff `χ` and every `N`, the remainder
`a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol is a symbol of order `m - N`. -/
theorem exists_remainder (N : ℕ) :
    ∃ r : Symbol n V W (m - N), ∀ p, r.coefficient p =
      a.toSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p := by
  obtain ⟨χ₀, h₀⟩ := a.exists_remainder'
  obtain ⟨r₀, hr₀⟩ := h₀ N
  -- The truncated expansions for `χ₀` and `χ` differ by `∑_{j<N} (χ₀ - χ)(ξ) a_{m-j}`, which
  -- vanishes at frequencies of norm at least `2` and is therefore a symbol of every order.
  let f : CoordinateSpace n × CoordinateSpace n → V →L[ℂ] W := fun p =>
    ∑ j ∈ Finset.range N,
      ((cutoffSymbol χ₀ (a.term j)).coefficient p - (cutoffSymbol χ (a.term j)).coefficient p)
  have hf : ContDiff ℝ ∞ f := ContDiff.sum fun j _ =>
    (Symbol.contDiff_coefficient _).sub (Symbol.contDiff_coefficient _)
  have hf2 : ∀ x ξ, 2 ≤ ‖ξ‖ → f (x, ξ) = 0 := fun x ξ hξ => by
    simp [f, χ₀.apply_eq_one_of_two_le_norm hξ, χ.apply_eq_one_of_two_le_norm hξ]
  refine ⟨r₀ + Symbol.ofBoundedFrequencySupport f hf 2 hf2, fun p => ?_⟩
  simp only [Symbol.coefficient_add, Pi.add_apply, hr₀, f, coefficient_cutoffSymbol,
    Symbol.coefficient_ofBoundedFrequencySupport, Finset.sum_sub_distrib]
  abel

/-- The remainder `a - ∑_{j<N} χ(ξ) a_{m-j}` of a classical symbol after `N` terms, a symbol of
order `m - N`. -/
def remainder (N : ℕ) : Symbol n V W (m - N) :=
  (a.exists_remainder χ N).choose

@[simp]
theorem coefficient_remainder (N : ℕ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.remainder χ N).coefficient p =
      a.toSymbol.coefficient p - ∑ j ∈ Finset.range N, χ p.2 • (a.term j).coefficient p :=
  (a.exists_remainder χ N).choose_spec p

end Remainder

section Uniqueness

/-- **Uniqueness of the homogeneous terms.** Two classical symbols with the same full symbol have
the same homogeneous terms. -/
theorem term_eq_of_toSymbol_eq {a b : ClassicalSymbol n V W m} (h : a.toSymbol = b.toSymbol)
    (j : ℕ) : a.term j = b.term j := by
  obtain ⟨χ, -⟩ := a.exists_remainder'
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    -- Given the equality of the earlier terms, the difference of the remainders after `j + 1`
    -- terms is the cut-off term of `b_{m-j} - a_{m-j}`, of order `m - (j + 1) < m - j`.
    refine (sub_eq_zero.1 <| eq_zero_of_coefficient_eq_cutoffSymbol χ (m' := m - (j + 1 : ℕ))
      (by push_cast; linarith) (a.remainder χ (j + 1) - b.remainder χ (j + 1)) ?_).symm
    funext p
    have hsum : ∑ i ∈ Finset.range j, χ p.2 • (a.term i).coefficient p =
        ∑ i ∈ Finset.range j, χ p.2 • (b.term i).coefficient p :=
      Finset.sum_congr rfl fun i hi => by rw [ih i (Finset.mem_range.1 hi)]
    simp only [Symbol.coefficient_sub, Pi.sub_apply, coefficient_remainder,
      Finset.sum_range_succ, hsum, h, coefficient_cutoffSymbol, HomogeneousSymbol.coefficient_sub,
      smul_sub]
    abel

/-- A classical symbol is determined by its full symbol. -/
@[ext]
theorem ext {a b : ClassicalSymbol n V W m} (h : a.toSymbol = b.toSymbol) : a = b := by
  have ht : a.term = b.term := funext (term_eq_of_toSymbol_eq h)
  cases a
  cases b
  cases h
  cases ht
  rfl

theorem toSymbol_injective :
    Function.Injective (toSymbol : ClassicalSymbol n V W m → Symbol n V W m) :=
  fun _ _ => ext

end Uniqueness

/-! ### The vector space of classical symbols of order `m` -/

section Module

instance : Zero (ClassicalSymbol n V W m) where
  zero :=
    { toSymbol := 0
      term _ := 0
      exists_remainder' := ⟨default, fun _ => ⟨0, fun p => by simp⟩⟩ }

instance : Add (ClassicalSymbol n V W m) where
  add a b :=
    { toSymbol := a.toSymbol + b.toSymbol
      term j := a.term j + b.term j
      exists_remainder' := ⟨default, fun N => ⟨a.remainder default N + b.remainder default N,
        fun p => by
          simp only [Symbol.coefficient_add, Pi.add_apply, coefficient_remainder,
            HomogeneousSymbol.coefficient_add, smul_add, Finset.sum_add_distrib]
          abel⟩⟩ }

instance : SMul ℂ (ClassicalSymbol n V W m) where
  smul c a :=
    { toSymbol := c • a.toSymbol
      term j := c • a.term j
      exists_remainder' := ⟨default, fun N => ⟨c • a.remainder default N, fun p => by
        simp only [Symbol.coefficient_smul, Pi.smul_apply, coefficient_remainder,
          HomogeneousSymbol.coefficient_smul, smul_sub, Finset.smul_sum, smul_comm c]⟩⟩ }

instance : Neg (ClassicalSymbol n V W m) where
  neg a :=
    { toSymbol := -a.toSymbol
      term j := -a.term j
      exists_remainder' := ⟨default, fun N => ⟨-a.remainder default N, fun p => by
        simp only [Symbol.coefficient_neg, Pi.neg_apply, coefficient_remainder,
          HomogeneousSymbol.coefficient_neg, smul_neg, Finset.sum_neg_distrib]
        abel⟩⟩ }

instance : Sub (ClassicalSymbol n V W m) where
  sub a b := a + -b

instance : SMul ℕ (ClassicalSymbol n V W m) where
  smul k a := (k : ℂ) • a

instance : SMul ℤ (ClassicalSymbol n V W m) where
  smul k a := (k : ℂ) • a

variable (a b : ClassicalSymbol n V W m) (c : ℂ) (j : ℕ)

@[simp]
theorem toSymbol_zero : (0 : ClassicalSymbol n V W m).toSymbol = 0 := (rfl)

@[simp]
theorem toSymbol_add : (a + b).toSymbol = a.toSymbol + b.toSymbol := (rfl)

@[simp]
theorem toSymbol_smul : (c • a).toSymbol = c • a.toSymbol := (rfl)

@[simp]
theorem toSymbol_neg : (-a).toSymbol = -a.toSymbol := (rfl)

@[simp]
theorem toSymbol_sub : (a - b).toSymbol = a.toSymbol - b.toSymbol :=
  (sub_eq_add_neg _ _).symm

@[simp]
theorem toSymbol_nsmul (k : ℕ) : (k • a).toSymbol = k • a.toSymbol :=
  Nat.cast_smul_eq_nsmul ℂ k a.toSymbol

@[simp]
theorem toSymbol_zsmul (k : ℤ) : (k • a).toSymbol = k • a.toSymbol :=
  Int.cast_smul_eq_zsmul ℂ k a.toSymbol

@[simp]
theorem term_zero : (0 : ClassicalSymbol n V W m).term j = 0 := (rfl)

@[simp]
theorem term_add : (a + b).term j = a.term j + b.term j := (rfl)

@[simp]
theorem term_smul : (c • a).term j = c • a.term j := (rfl)

@[simp]
theorem term_neg : (-a).term j = -a.term j := (rfl)

@[simp]
theorem term_sub : (a - b).term j = a.term j - b.term j :=
  (sub_eq_add_neg _ _).symm

instance : AddCommGroup (ClassicalSymbol n V W m) :=
  toSymbol_injective.addCommGroup _ toSymbol_zero toSymbol_add toSymbol_neg toSymbol_sub
    (fun a k => toSymbol_nsmul a k) (fun a k => toSymbol_zsmul a k)

instance : Module ℂ (ClassicalSymbol n V W m) :=
  toSymbol_injective.module ℂ ⟨⟨toSymbol, toSymbol_zero⟩, toSymbol_add⟩
    fun c a => toSymbol_smul a c

end Module

/-! ### The principal symbol -/

section Principal

variable (a b : ClassicalSymbol n V W m)

/-- The principal symbol of a classical symbol of order `m`: its leading homogeneous term `a_m`,
of degree `m`. -/
def principal : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m :=
  (a.term 0).castDegree (by simp)

@[simp]
theorem coefficient_principal : a.principal.coefficient = (a.term 0).coefficient :=
  coefficient_castDegree _ _

/-- A classical symbol and its cut-off principal symbol differ by a symbol of order `m - 1`. -/
theorem exists_sub_cutoffSymbol_principal (χ : FrequencyCutoff (CoordinateSpace n)) :
    ∃ r : Symbol n V W (m - 1),
      r.coefficient = (a.toSymbol - cutoffSymbol χ a.principal).coefficient :=
  ⟨Symbol.inclusion (by simp) (a.remainder χ 1), funext fun p => by simp⟩

@[simp]
theorem principal_zero : (0 : ClassicalSymbol n V W m).principal = 0 :=
  castDegree_zero _

@[simp]
theorem principal_add : (a + b).principal = a.principal + b.principal :=
  castDegree_add _ _ _

@[simp]
theorem principal_smul (c : ℂ) : (c • a).principal = c • a.principal :=
  castDegree_smul _ _ _

@[simp]
theorem principal_neg : (-a).principal = -a.principal :=
  castDegree_neg _ _

@[simp]
theorem principal_sub : (a - b).principal = a.principal - b.principal := by
  simp [principal, castDegree_sub]

end Principal

/-! ### Smoothing symbols and single homogeneous terms -/

section Examples

/-- A smoothing symbol is a classical symbol, all of whose homogeneous terms vanish. -/
def ofIsSmoothing (a : Symbol n V W m) (ha : a.IsSmoothing) : ClassicalSymbol n V W m where
  toSymbol := a
  term _ := 0
  exists_remainder' := ⟨default, fun N => ⟨(Symbol.isSmoothing_iff.1 ha (m - N)).choose, fun p => by
    simp [(Symbol.isSmoothing_iff.1 ha (m - N)).choose_spec]⟩⟩

@[simp]
theorem toSymbol_ofIsSmoothing (a : Symbol n V W m) (ha : a.IsSmoothing) :
    (ofIsSmoothing a ha).toSymbol = a :=
  (rfl)

@[simp]
theorem term_ofIsSmoothing (a : Symbol n V W m) (ha : a.IsSmoothing) (j : ℕ) :
    (ofIsSmoothing a ha).term j = 0 :=
  (rfl)

/-- A classical symbol is smoothing exactly when all of its homogeneous terms vanish. -/
theorem isSmoothing_toSymbol_iff (a : ClassicalSymbol n V W m) :
    a.toSymbol.IsSmoothing ↔ ∀ j, a.term j = 0 := by
  refine ⟨fun ha j => ?_, fun ha => Symbol.isSmoothing_iff.2 fun m' => ?_⟩
  · exact (term_eq_of_toSymbol_eq (a := a) (b := ofIsSmoothing a.toSymbol ha) rfl j).trans
      (term_ofIsSmoothing _ _ j)
  · -- With vanishing terms the remainder after `N` terms is the symbol itself, of order `m - N`.
    obtain ⟨N, hN⟩ := exists_nat_ge (m - m')
    exact ⟨Symbol.inclusion (by linarith) (a.remainder default N), funext fun p => by simp [ha]⟩

/-- The classical symbol `χ(ξ) a(x, ξ)` of a single homogeneous term `a` of degree `m`: its
principal symbol is `a` and its other homogeneous terms vanish. -/
def ofHomogeneous (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    ClassicalSymbol n V W m where
  toSymbol := cutoffSymbol χ a
  term
    | 0 => a.castDegree (by simp)
    | _ + 1 => 0
  exists_remainder' := ⟨χ, fun
    | 0 => ⟨Symbol.inclusion (by simp) (cutoffSymbol χ a), fun p => by simp⟩
    | N + 1 => ⟨0, fun p => by simp [Finset.sum_range_succ']⟩⟩

variable (χ : FrequencyCutoff (CoordinateSpace n))
  (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)

@[simp]
theorem toSymbol_ofHomogeneous : (ofHomogeneous χ a).toSymbol = cutoffSymbol χ a :=
  (rfl)

@[simp]
theorem principal_ofHomogeneous : (ofHomogeneous χ a).principal = a :=
  castDegree_castDegree _ _ _ |>.trans (castDegree_rfl a)

@[simp]
theorem term_ofHomogeneous_succ (j : ℕ) : (ofHomogeneous χ a).term (j + 1) = 0 :=
  (rfl)

end Examples

end ClassicalSymbol

end TauCeti
