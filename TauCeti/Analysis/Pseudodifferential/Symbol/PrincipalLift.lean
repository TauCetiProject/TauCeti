/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.HomogeneousSymbol.Topology
public import TauCeti.Analysis.Pseudodifferential.Symbol.Classical
public import TauCeti.Analysis.Pseudodifferential.Symbol.Topology

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
elliptic principal symbols, lifts to a family of classical symbols with principal symbols `a_t`
whose full symbols depend continuously on `t` in `S^m_{1,0}`. To start the lift at
a prescribed classical symbol `P₀`, put

`P₀.liftPrincipal χ b = P₀ + χ(ξ) (b - σ(P₀))`,

a classical symbol with principal symbol `b` (`TauCeti.ClassicalSymbol.principal_liftPrincipal`)
which is `P₀` itself when `b = σ(P₀)` (`TauCeti.ClassicalSymbol.liftPrincipal_principal`). Its
lower homogeneous terms, and its remainders after at least one term for the cutoff `χ`, are those
of `P₀` (`TauCeti.ClassicalSymbol.term_liftPrincipal_succ`,
`TauCeti.ClassicalSymbol.remainder_liftPrincipal_succ`), and its full symbol depends continuously
on `b` (`TauCeti.ClassicalSymbol.continuous_toSymbol_liftPrincipal`). So for a continuous path
`t ↦ a_t` with `a_0 = σ(P₀)`, the lift `t ↦ P₀.liftPrincipal χ a_t` is a family of classical
symbols starting at `P₀`, with principal symbols `a_t`, the lower terms and `χ`-remainders of `P₀`,
and full symbols depending continuously on `t` in `S^m_{1,0}`
(`Continuous.toSymbol_liftPrincipal`). In the form `Q(a_t) + P₀ - Q(a_0)` with
`Q = ofHomogeneous χ`, this is `TauCeti.ClassicalSymbol.liftPrincipal_eq_add_sub`.

## Proof of the estimate

The estimate is the specialization to the coordinate directions of the uniform symbol estimate of
the cut-off term on any `X × E`
(`TauCeti.HomogeneousSymbol.exists_norm_iteratedFDeriv_smul_coefficient_le_seminorm`). At
frequencies `‖ξ‖ > 2` the cut-off term is `a` itself, and homogeneity bounds its derivative in
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
  obtain ⟨C, hC, h⟩ := exists_norm_iteratedFDeriv_smul_coefficient_le_seminorm
    (V := V) (W := W) (m := m) χ K α.length β.length
  refine ⟨C, hC, fun a ↦ Symbol.seminorm_le_bound K α β _
    (mul_nonneg hC (apply_nonneg _ _)) fun x hx ξ ↦ ?_⟩
  rw [mixedDeriv_eq_iteratedFDeriv_append α β
    ((cutoffSymbol χ a).contDiff_coefficient.of_le (mod_cast le_top)),
    coefficient_cutoffSymbol_eq_fun]
  -- Evaluate the uniform estimate on the coordinate directions, which are unit vectors.
  simpa using h a x hx ξ (fun i ↦ EuclideanSpace.single (α.get i) 1)
    fun i ↦ EuclideanSpace.single (β.get i) 1

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
  simp only [coefficient_remainder, Finset.sum_range_succ', ← coefficient_principal,
    principal_liftPrincipal, toSymbol_liftPrincipal, term_liftPrincipal_succ,
    Symbol.coefficient_add, Pi.add_apply, coefficient_cutoffSymbol,
    HomogeneousSymbol.coefficient_sub, Pi.sub_apply, smul_sub]
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
