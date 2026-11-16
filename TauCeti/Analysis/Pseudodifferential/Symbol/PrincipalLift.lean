/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol.Topology
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompLinear
import TauCeti.Analysis.Normed.Module.Multilinear.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds

/-!
# Continuous lifts of principal symbols

Every homogeneous symbol `a` of degree `m` on `ℝⁿ` is the principal symbol of a classical symbol of
order `m`: with a fixed frequency cutoff `χ`, the cut-off term `χ(ξ) a(x, ξ)`
(`TauCeti.HomogeneousSymbol.cutoffSymbol χ a`, the full symbol of
`TauCeti.ClassicalSymbol.ofHomogeneous χ a`) has principal symbol `a`. This file shows that this
lift is continuous: for the `C^∞` topology of homogeneous symbols on compact subsets of the
cosphere bundle (`TauCeti/Analysis/Pseudodifferential/HomogeneousSymbol/Topology.lean`) and the
seminorm topology of the symbol class `S^m_{1,0}`
(`TauCeti/Analysis/Pseudodifferential/Symbol/Topology.lean`), the map `a ↦ χ(ξ) a(x, ξ)` is a
continuous linear map (`TauCeti.HomogeneousSymbol.cutoffSymbolCLM`). Quantitatively, every symbol
seminorm `p_{K,α,β}` of `χ a` is bounded by a constant times the homogeneous seminorms `p_{K,i}(a)`
with `i ≤ |α| + |β|` (`TauCeti.HomogeneousSymbol.exists_seminorm_cutoffSymbol_le`).

Consequently a continuous family `t ↦ a_t` of principal symbols, for instance a homotopy of
elliptic principal symbols, lifts to a continuous family of classical symbols. To start the lift at
a prescribed classical symbol `P₀`, put

`P₀.liftPrincipal χ b = P₀ + χ(ξ) (b - σ(P₀))`,

a classical symbol with principal symbol `b` (`TauCeti.ClassicalSymbol.principal_liftPrincipal`)
which is `P₀` itself when `b = σ(P₀)` (`TauCeti.ClassicalSymbol.liftPrincipal_principal`). Its
lower homogeneous terms, and its remainders after at least one term for the cutoff `χ`, are those
of `P₀` (`TauCeti.ClassicalSymbol.term_liftPrincipal_succ`,
`TauCeti.ClassicalSymbol.remainder_liftPrincipal_succ`), and its full symbol depends continuously
on `b` (`TauCeti.ClassicalSymbol.continuous_toSymbol_liftPrincipal`). So for a continuous path
`t ↦ a_t` with `a_0 = σ(P₀)`, the lift `t ↦ P₀.liftPrincipal χ a_t` is a continuous path of
classical symbols in every coefficient and remainder seminorm, starting at `P₀`, with principal
symbols `a_t`. In the form `Q(a_t) + P₀ - Q(a_0)` with `Q = ofHomogeneous χ`, this is
`TauCeti.ClassicalSymbol.liftPrincipal_eq_add_sub`.

## Proof of the estimate

At frequencies `‖ξ‖ > 2` the cut-off term is `a` itself, and homogeneity bounds its derivative in
`|α|` position and `|β|` frequency directions by `‖ξ‖ ^ (m - |β|) p_{K,|α|+|β|}(a)`
(`TauCeti.HomogeneousSymbol.norm_iteratedFDeriv_append_le_seminorm`), which is at most a constant
times `⟨ξ⟩ ^ (m - |β|)`. At frequencies `‖ξ‖ ≤ 2` the Leibniz rule bounds the derivatives of
`χ(ξ) a(x, ξ)` by those of `χ`, which vanish for `‖ξ‖ ≤ 1`, and those of `a` for `1 ≤ ‖ξ‖ ≤ 2`,
which are at most `2 ^ |m|` times the seminorms
(`TauCeti.HomogeneousSymbol.norm_iteratedFDeriv_coefficient_le_seminorm`).

## References

* R. B. Melrose, *Introduction to Microlocal Analysis*, §5.3, proof of Proposition 5.2,
  (5.35)–(5.36): the quantization of principal symbols by a frequency cutoff is linear and
  continuous, which gives continuous lifts of symbol homotopies.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

noncomputable section

open Filter Topology
open TopologicalSpace (Compacts)
open scoped ContDiff

namespace TauCeti

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m : ℝ}

namespace HomogeneousSymbol

/-- The cut-off term vanishes near the zero frequency, so all its derivatives vanish there. -/
private theorem iteratedFDeriv_cutoffSymbol_zero_frequency (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) (k : ℕ)
    (x : CoordinateSpace n) : iteratedFDeriv ℝ k (cutoffSymbol χ a).coefficient (x, 0) = 0 := by
  have h0 : (cutoffSymbol χ a).coefficient =ᶠ[𝓝 (x, 0)] 0 := by
    rw [show (cutoffSymbol χ a).coefficient = fun p ↦ χ p.2 • a.coefficient p from
      funext (coefficient_cutoffSymbol χ a)]
    simpa using χ.comp_inv_smul_snd_smul_eventuallyEq_zero 1 a.coefficient
      (p := (x, (0 : CoordinateSpace n))) (by simp)
  rw [h0.iteratedFDeriv ℝ k |>.eq_of_nhds, iteratedFDeriv_zero, Pi.zero_apply]

/-- At frequencies `‖ξ‖ ≤ 2`, the derivatives of the cut-off term `χ(ξ) a(x, ξ)` are
bounded by a constant, depending only on `χ`, `m` and the order `k`, times the homogeneous
seminorms `p_{K,i}(a)`, `i ≤ k`. -/
private theorem exists_norm_iteratedFDeriv_cutoffSymbol_le
    (χ : FrequencyCutoff (CoordinateSpace n)) (K : Compacts (CoordinateSpace n)) (k : ℕ) :
    ∃ C, 0 ≤ C ∧ ∀ a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m,
      ∀ x ∈ K, ∀ ξ : CoordinateSpace n, ‖ξ‖ ≤ 2 →
        ‖iteratedFDeriv ℝ k (cutoffSymbol χ a).coefficient (x, ξ)‖ ≤
          C * ((Finset.range (k + 1)).sup fun i ↦ HomogeneousSymbol.seminorm K i) a := by
  choose B hB using fun i ↦ χ.exists_bound_iteratedFDeriv i
  set L := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * max (B i) 0
  refine ⟨L * 2 ^ |m|, by positivity, fun a x hx ξ hξ2 ↦ ?_⟩
  set P := ((Finset.range (k + 1)).sup fun i ↦ HomogeneousSymbol.seminorm K i) a
  have hcoe : (cutoffSymbol χ a).coefficient = fun p ↦ χ p.2 • a.coefficient p :=
    funext (coefficient_cutoffSymbol χ a)
  rcases eq_or_ne ξ 0 with rfl | hξ
  · rw [iteratedFDeriv_cutoffSymbol_zero_frequency, norm_zero]
    positivity
  -- Away from the zero frequency, apply the Leibniz rule on the open set `ξ ≠ 0`.
  set S : Set (CoordinateSpace n × CoordinateSpace n) := {p | p.2 ≠ 0}
  have hS : IsOpen S := isOpen_ne_fun continuous_snd continuous_const
  have hxξ : (x, ξ) ∈ S := hξ
  have hχ : ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n ↦ χ p.2 :=
    χ.contDiff.comp contDiff_snd
  have hleib := norm_iteratedFDerivWithin_smul_le hχ.contDiffOn a.contDiffOn_coefficient
    hS.uniqueDiffOn hxξ (n := k) (mod_cast le_top)
  rw [iteratedFDerivWithin_of_isOpen k hS hxξ, ← hcoe] at hleib
  refine hleib.trans ?_
  rw [mul_assoc, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [iteratedFDerivWithin_of_isOpen i hS hxξ, iteratedFDerivWithin_of_isOpen (k - i) hS hxξ,
    mul_assoc (k.choose i : ℝ), mul_assoc (k.choose i : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
  -- The derivatives of `ξ ↦ χ ξ` on the product are bounded by those of `χ`.
  have hχi : ‖iteratedFDeriv ℝ i (fun p : CoordinateSpace n × CoordinateSpace n ↦ χ p.2)
      (x, ξ)‖ ≤ ‖iteratedFDeriv ℝ i χ ξ‖ :=
    norm_iteratedFDeriv_comp_snd_le (f := χ) (x, ξ)
  rcases le_or_gt ‖ξ‖ 1 with hξ1 | hξ1
  · -- Inside the closed unit ball every derivative of `χ` vanishes.
    rw [χ.iteratedFDeriv_eq_zero_of_norm_le_one i hξ1, norm_zero] at hχi
    rw [norm_le_zero_iff.1 hχi, norm_zero, zero_mul]
    positivity
  · -- On `1 < ‖ξ‖ ≤ 2` both factors are bounded.
    have hik : k - i ∈ Finset.range (k + 1) := Finset.mem_range.2 (by omega)
    have ha : ‖iteratedFDeriv ℝ (k - i) a.coefficient (x, ξ)‖ ≤ 2 ^ |m| * P := by
      refine (a.norm_iteratedFDeriv_coefficient_le_seminorm K (k - i) hx hξ1.le).trans ?_
      refine mul_le_mul ?_ (Seminorm.le_finset_sup_apply hik) (apply_nonneg _ _) (by positivity)
      calc ‖ξ‖ ^ m ≤ ‖ξ‖ ^ |m| := Real.rpow_le_rpow_of_exponent_le hξ1.le (le_abs_self m)
        _ ≤ 2 ^ |m| := Real.rpow_le_rpow (norm_nonneg _) hξ2 (abs_nonneg m)
    calc ‖iteratedFDeriv ℝ i (fun p : CoordinateSpace n × CoordinateSpace n ↦ χ p.2) (x, ξ)‖ *
          ‖iteratedFDeriv ℝ (k - i) a.coefficient (x, ξ)‖
        ≤ max (B i) 0 * (2 ^ |m| * P) :=
          mul_le_mul (hχi.trans ((hB i ξ).trans (le_max_left _ _))) ha (norm_nonneg _)
            (le_max_right _ _)

/-- **The cut-off term depends continuously on the homogeneous symbol.** Every seminorm
`p_{K,α,β}` of the cut-off term `χ(ξ) a(x, ξ)` in `S^m_{1,0}` is bounded by a constant, depending
only on `χ`, `m`, `K`, `α` and `β`, times the largest of the homogeneous seminorms `p_{K,i}(a)`,
`i ≤ |α| + |β|`. -/
theorem exists_seminorm_cutoffSymbol_le (χ : FrequencyCutoff (CoordinateSpace n))
    (K : Compacts (CoordinateSpace n)) (α β : List (Fin n)) :
    ∃ C, 0 ≤ C ∧ ∀ a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m,
      Symbol.seminorm K α β (cutoffSymbol χ a) ≤
        C * ((Finset.range (α.length + β.length + 1)).sup fun i ↦
          HomogeneousSymbol.seminorm K i) a := by
  set k := α.length + β.length
  set l := β.length
  obtain ⟨C₁, hC₁, h₁⟩ := exists_norm_iteratedFDeriv_cutoffSymbol_le (V := V) (W := W) (m := m)
    χ K k
  refine ⟨C₁ * 5 ^ (|m - l| / 2) + 2 ^ (|m - l| / 2), by positivity, fun a ↦ ?_⟩
  set P := ((Finset.range (k + 1)).sup fun i ↦ HomogeneousSymbol.seminorm K i) a
  have hP : 0 ≤ P := apply_nonneg _ _
  refine Symbol.seminorm_le_bound K α β _ (by positivity) fun x hx ξ ↦ ?_
  have hw := rpow_weight_pos ξ (m - l)
  rw [mixedDeriv_eq_iteratedFDeriv_append α β
    ((cutoffSymbol χ a).contDiff_coefficient.of_le (mod_cast le_top))]
  -- The coordinate directions are unit vectors.
  have hunit : ((∏ i : Fin α.length, ‖EuclideanSpace.single (α.get i) (1 : ℝ)‖) *
      ∏ i : Fin β.length, ‖EuclideanSpace.single (β.get i) (1 : ℝ)‖) = 1 := by
    simp
  rcases le_or_gt ‖ξ‖ 2 with hξ2 | hξ2
  · -- Near the zero frequency use the bound of the Leibniz rule.
    refine ((iteratedFDeriv ℝ k (cutoffSymbol χ a).coefficient (x, ξ)).norm_apply_append_prod_le
      _ _).trans ?_
    rw [hunit, mul_one]
    refine (h₁ a x hx ξ hξ2).trans ?_
    have h5 := Real.one_le_five_rpow_mul_one_add_sq_rpow (t := ‖ξ‖) (by rwa [abs_norm]) (m - l)
    calc C₁ * P ≤ C₁ * P * (5 ^ (|m - l| / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2)) :=
          le_mul_of_one_le_right (by positivity) h5
      _ ≤ (C₁ * 5 ^ (|m - l| / 2) + 2 ^ (|m - l| / 2)) * P * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) := by
          nlinarith [mul_nonneg (mul_nonneg hP hw.le)
            (Real.rpow_nonneg zero_le_two (|m - l| / 2))]
  · -- At large frequencies the cut-off term is the homogeneous symbol itself.
    have hξ0 : ξ ≠ 0 := norm_pos_iff.1 (two_pos.trans hξ2)
    have heq : (cutoffSymbol χ a).coefficient =ᶠ[𝓝 (x, ξ)] a.coefficient := by
      filter_upwards [continuous_snd.continuousAt.eventually
        (χ.eventuallyEq_one_of_two_lt_norm hξ2)] with q hq
      simp [hq]
    rw [heq.iteratedFDeriv ℝ k |>.eq_of_nhds]
    refine (a.norm_iteratedFDeriv_append_le_seminorm K hx hξ0 _ _).trans ?_
    rw [hunit, mul_one]
    have hk : k ∈ Finset.range (k + 1) := Finset.self_mem_range_succ k
    have hpk : HomogeneousSymbol.seminorm K k a ≤ P := Seminorm.le_finset_sup_apply hk
    have hξw := norm_rpow_le_one_add_norm_sq_rpow (one_le_two.trans hξ2.le) (m - l)
    calc ‖ξ‖ ^ (m - l) * HomogeneousSymbol.seminorm K k a
        ≤ 2 ^ (|m - l| / 2) * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) * P :=
          mul_le_mul hξw hpk (apply_nonneg _ _) (by positivity)
      _ ≤ (C₁ * 5 ^ (|m - l| / 2) + 2 ^ (|m - l| / 2)) * P * (1 + ‖ξ‖ ^ 2) ^ ((m - l) / 2) := by
          nlinarith [mul_nonneg (mul_nonneg hP hw.le)
            (mul_nonneg hC₁ (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 5) (|m - l| / 2)))]

/-- The cut-off term `a ↦ χ(ξ) a(x, ξ)` is continuous from homogeneous symbols of degree `m` to the
symbols of order `m`. -/
theorem continuous_cutoffSymbol (χ : FrequencyCutoff (CoordinateSpace n)) :
    Continuous (cutoffSymbol (V := V) (W := W) (m := m) χ) := by
  refine WithSeminorms.continuous_of_isBounded HomogeneousSymbol.withSeminorms
    Symbol.withSeminorms _ (Seminorm.IsBounded.of_real fun ⟨K, α, β⟩ ↦ ?_)
  classical
  obtain ⟨C, -, hC⟩ := exists_seminorm_cutoffSymbol_le (V := V) (W := W) (m := m) χ K α β
  refine ⟨(Finset.range (α.length + β.length + 1)).image fun i ↦ (K, i), C, fun a ↦ ?_⟩
  simpa [Finset.sup_image, Function.comp_def] using hC a

/-- The cut-off term `a ↦ χ(ξ) a(x, ξ)` as a continuous linear map from homogeneous symbols of
degree `m` to symbols of order `m`. -/
def cutoffSymbolCLM (χ : FrequencyCutoff (CoordinateSpace n)) :
    HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m →L[ℂ] Symbol n V W m where
  toLinearMap := cutoffSymbol χ
  cont := continuous_cutoffSymbol χ

@[simp]
theorem cutoffSymbolCLM_apply (χ : FrequencyCutoff (CoordinateSpace n))
    (a : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m) :
    cutoffSymbolCLM χ a = cutoffSymbol χ a := (rfl)

end HomogeneousSymbol

namespace ClassicalSymbol

open HomogeneousSymbol

variable (χ : FrequencyCutoff (CoordinateSpace n)) (P₀ : ClassicalSymbol n V W m)
  (b : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m)

/-- The lift of a homogeneous symbol `b` of degree `m` to a classical symbol with principal symbol
`b`, relative to the classical symbol `P₀`: the symbol `P₀ + χ(ξ) (b - σ(P₀))`. It keeps the lower
order terms of `P₀`, and it is `P₀` itself for `b = σ(P₀)`. -/
def liftPrincipal : ClassicalSymbol n V W m :=
  P₀ + ofHomogeneous χ (b - P₀.principal)

theorem liftPrincipal_def : P₀.liftPrincipal χ b = P₀ + ofHomogeneous χ (b - P₀.principal) :=
  (rfl)

@[simp]
theorem toSymbol_liftPrincipal :
    (P₀.liftPrincipal χ b).toSymbol = P₀.toSymbol + cutoffSymbol χ (b - P₀.principal) := by
  rw [liftPrincipal_def, toSymbol_add, toSymbol_ofHomogeneous]

/-- The lift has the prescribed principal symbol. -/
@[simp]
theorem principal_liftPrincipal : (P₀.liftPrincipal χ b).principal = b := by
  rw [liftPrincipal_def, principal_add, principal_ofHomogeneous, add_sub_cancel]

/-- The lift keeps the homogeneous terms of order below `m` of `P₀`. -/
@[simp]
theorem term_liftPrincipal_succ (j : ℕ) :
    (P₀.liftPrincipal χ b).term (j + 1) = P₀.term (j + 1) := by
  rw [liftPrincipal_def, term_add, term_ofHomogeneous_succ, add_zero]

/-- Lifting the principal symbol of `P₀` gives back `P₀`. -/
@[simp]
theorem liftPrincipal_principal : P₀.liftPrincipal χ P₀.principal = P₀ := by
  rw [liftPrincipal_def, sub_self, ofHomogeneous_zero, add_zero]

/-- The lift is `Q(b) + P₀ - Q(σ(P₀))` for the quantization `Q = ofHomogeneous χ` of principal
symbols. -/
theorem liftPrincipal_eq_add_sub :
    P₀.liftPrincipal χ b = ofHomogeneous χ b + P₀ - ofHomogeneous χ P₀.principal := by
  refine ext ?_
  simp only [toSymbol_liftPrincipal, toSymbol_add, toSymbol_sub, toSymbol_ofHomogeneous,
    map_sub]
  abel

/-- For the cutoff `χ` of the lift, its remainders after at least one term are those of `P₀`. -/
@[simp]
theorem remainder_liftPrincipal_succ (N : ℕ) :
    (P₀.liftPrincipal χ b).remainder χ (N + 1) = P₀.remainder χ (N + 1) := by
  refine Symbol.ext <| funext fun p ↦ ?_
  rw [coefficient_remainder, coefficient_remainder, Finset.sum_range_succ',
    Finset.sum_range_succ', ← coefficient_principal, ← coefficient_principal,
    principal_liftPrincipal, toSymbol_liftPrincipal]
  simp only [term_liftPrincipal_succ, Symbol.coefficient_add, Pi.add_apply,
    coefficient_cutoffSymbol, HomogeneousSymbol.coefficient_sub, Pi.sub_apply, smul_sub]
  abel

/-- The full symbol of the lift depends continuously on the prescribed principal symbol. -/
theorem continuous_toSymbol_liftPrincipal :
    Continuous fun b : HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m ↦
      (P₀.liftPrincipal χ b).toSymbol := by
  simp only [toSymbol_liftPrincipal]
  exact continuous_const.add ((continuous_cutoffSymbol χ).comp
    (continuous_id.sub continuous_const))

/-- **Continuous lifts of symbol homotopies.** A continuous family `t ↦ a_t` of homogeneous symbols
of degree `m` lifts to the family `t ↦ P₀.liftPrincipal χ a_t` of classical symbols with principal
symbols `a_t`, whose full symbols depend continuously on `t`; it starts at `P₀` where
`a_t = σ(P₀)`. -/
theorem _root_.Continuous.toSymbol_liftPrincipal {T : Type*} [TopologicalSpace T]
    {a : T → HomogeneousSymbol (CoordinateSpace n) (CoordinateSpace n) V W m}
    (ha : Continuous a) : Continuous fun t ↦ (P₀.liftPrincipal χ (a t)).toSymbol :=
  (P₀.continuous_toSymbol_liftPrincipal χ).comp ha

end ClassicalSymbol

end TauCeti
