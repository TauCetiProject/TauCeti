/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Basic
public import TauCeti.Analysis.Pseudodifferential.Composition.Expansion

/-!
# Compressions of a quantization by spatial cutoffs

For smooth real functions `φ` and `ψ` on `ℝⁿ`, with `ψ` compactly supported, the operator
`u ↦ φ · Op(a) (ψ u)` is again a quantization: it is `Op(φ (a # ψ))`, where `a # ψ` is the
composition symbol of `Op(a) ∘ Op(ψ)` (`TauCeti.Symbol.sharp`). This file calls `φ (a # ψ)` the
*compression* `TauCeti.Symbol.compress` of `a` by the cutoffs `φ` and `ψ`. Compressions are the
building blocks for patching local quantizations: with charts and cutoffs, a global operator is
assembled as a locally finite sum of compressions. There are two standard ways to do this.

* **Ordinary partitions.** For a partition of unity `∑ᵢ φᵢ = 1` and cutoffs `ψᵢ` equal to `1` near
  the support of `φᵢ`, the sum `∑ᵢ φᵢ Op(a) ψᵢ` differs from `Op(a)` by a smoothing operator
  (`TauCeti.Symbol.isSmoothing_sum_compress_sub`). The sum is not symmetric: its formal adjoint is
  `∑ᵢ ψᵢ Op(a*) φᵢ`.
* **Square partitions.** For a square partition of unity `∑ᵢ χᵢ² = 1`, the symmetric sum
  `∑ᵢ χᵢ Op(a) χᵢ` is formally self-adjoint whenever `Op(a)` is
  (`TauCeti.Symbol.integral_inner_quantizeSchwartzValue_compress`). Its symbol is `a` up to a
  symbol of order `m - 2` (`TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub`): the
  composition expansion gives `χᵢ (a # χᵢ) = χᵢ² a - i ∑ₖ χᵢ ∂ₖχᵢ ∂_{ξₖ} a` modulo order `m - 2`
  (`TauCeti.Symbol.exists_coefficient_compress_eq`), and the terms of order `m - 1` cancel in the
  sum because `∑ᵢ χᵢ ∂ₖχᵢ = ½ ∂ₖ (∑ᵢ χᵢ²) = 0`. In general the error of order `m - 2` is not
  smoothing: on `ℝ`, where `∑ᵢ χᵢ² = 1` the identities `∑ᵢ χᵢ χᵢ' = 0` and
  `∑ᵢ χᵢ χᵢ'' = -∑ᵢ (χᵢ')²` give `∑ᵢ χᵢ D² χᵢ = D² + ∑ᵢ (χᵢ')²` for `D = -i ∂`.

So the symmetric and the ordinary constructions differ by an operator of order `m - 2`
(`TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub_sum_compress`). Smooth square partitions of
unity on manifolds are `SmoothPartitionOfUnity.sqrtNormalized`.

## Main declarations

* `TauCeti.Symbol.compress a φ ψ`: the symbol `φ (a # ψ)` of `u ↦ φ · Op(a) (ψ u)`, with
  `TauCeti.Symbol.quantizeSchwartzValue_compress`.
* `TauCeti.Symbol.exists_coefficient_compress_eq`: its expansion to second order.
* `TauCeti.Symbol.isSmoothing_compress_sub_compress`: if `ψ = 1` near the support of `φ`, the
  compression does not depend on `ψ` modulo smoothing symbols.
* `TauCeti.Symbol.isSmoothing_sum_compress_sub`: ordinary partitions reproduce `a` modulo smoothing
  symbols, and `TauCeti.Symbol.exists_isSmoothing_sum_smul_quantizeSchwartzValue_eq` for the
  operators.
* `TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub`: square partitions reproduce `a` modulo
  symbols of order `m - 2`, and `TauCeti.Symbol.exists_sum_smul_quantizeSchwartzValue_eq` for the
  operators.
* `TauCeti.Symbol.integral_inner_quantizeSchwartzValue_compress`: the formal adjoint of the
  compression of `a` by `φ` and `ψ` is the compression of the adjoint symbol by `ψ` and `φ`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (2.5)–(2.7).
-/

public section

noncomputable section

open Filter Finset MeasureTheory
open scoped ContDiff SchwartzMap Topology

namespace TauCeti

namespace Symbol

variable {n : ℕ} {m : ℝ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [NormedAddCommGroup W] [NormedSpace ℂ W]

/-! ### Cutoff symbols -/

section Cutoff

variable {ψ : CoordinateSpace n → ℝ}

variable (V) in
/-- The symbol `ψ(x) id_V` of multiplication by a smooth real function `ψ`. -/
private def cutoff (hψ : ContDiff ℝ ∞ ψ) : Symbol n V V 0 :=
  ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V) (hψ.smul contDiff_const)

private theorem coefficient_cutoff (hψ : ContDiff ℝ ∞ ψ)
    (p : CoordinateSpace n × CoordinateSpace n) :
    (cutoff V hψ).coefficient p = ψ p.1 • ContinuousLinearMap.id ℂ V := by
  rw [cutoff, coefficient_ofSpatial]

private theorem hasCompactSpatialSupport_cutoff (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    (cutoff V hψ).HasCompactSpatialSupport :=
  (hasCompactSpatialSupport_ofSpatial_iff _).2 (hψc.smul_right)

/-- The position derivatives of the cutoff symbol are those of `ψ`. -/
private theorem mixedDeriv_cutoff (hψ : ContDiff ℝ ∞ ψ) (α : List (Fin n))
    (x ξ : CoordinateSpace n) :
    mixedDeriv α [] (cutoff V hψ).coefficient x ξ =
      coordinateDeriv α ψ x • ContinuousLinearMap.id ℂ V := by
  have h : (cutoff V hψ).coefficient = fun p ↦ ψ p.1 • ContinuousLinearMap.id ℂ V :=
    funext (coefficient_cutoff hψ)
  rw [h, mixedDeriv_nil_comp_fst (fun y ↦ ψ y • ContinuousLinearMap.id ℂ V)]
  exact (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
    (ContinuousLinearMap.id ℂ V)).coordinateDeriv_comp_left α (hψ.of_le (by simp)) x

/-- If `ψ` is constant near `x`, all nonempty position derivatives of the cutoff symbol vanish
at `x`. -/
private theorem mixedDeriv_cutoff_eq_zero (hψ : ContDiff ℝ ∞ ψ) {x : CoordinateSpace n} {c : ℝ}
    (hx : ψ =ᶠ[𝓝 x] fun _ ↦ c) {α : List (Fin n)} (hα : α ≠ []) (ξ : CoordinateSpace n) :
    mixedDeriv α [] (cutoff V hψ).coefficient x ξ = 0 := by
  rw [mixedDeriv_cutoff, (hx.coordinateDeriv α).eq_of_nhds, coordinateDeriv_const c hα,
    Pi.zero_apply, zero_smul]

end Cutoff

/-! ### The compression of a symbol by two cutoffs -/

section Compress

variable {φ ψ : CoordinateSpace n → ℝ}

/-- The **compression** of a symbol `a` of order `m` by smooth real cutoffs `φ` and `ψ`, with `ψ`
compactly supported: the symbol `φ(x) (a # ψ)(x, ξ)` of order `m`, whose quantization is
`u ↦ φ · Op(a) (ψ u)` (`TauCeti.Symbol.quantizeSchwartzValue_compress`). -/
def compress (a : Symbol n V W m) (φ ψ : CoordinateSpace n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) : Symbol n V W m :=
  inclusion (by simp)
    ((cutoff W hφ).comp (a.sharp (cutoff V hψ) (hasCompactSpatialSupport_cutoff hψ hψc)))

variable {a : Symbol n V W m}

/-- The compression in terms of the cutoff symbol. -/
private theorem coefficient_compress_eq_cutoff (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.compress φ ψ hφ hψ hψc).coefficient p = φ p.1 •
      (a.sharp (cutoff V hψ) (hasCompactSpatialSupport_cutoff hψ hψc)).coefficient p := by
  simp [compress, coefficient_cutoff]

/-- The coefficient of the compression `φ (a # ψ)`. -/
@[simp]
theorem coefficient_compress (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.compress φ ψ hφ hψ hψc).coefficient p = φ p.1 • (a.sharp
      (ofSpatial (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V) (hψ.smul contDiff_const))
      ((hasCompactSpatialSupport_ofSpatial_iff _).2 hψc.smul_right)).coefficient p :=
  coefficient_compress_eq_cutoff hφ hψ hψc p

/-- The remainder `φ r` of a compression, for a remainder symbol `r` of order `m - N`. -/
private def remainder (hφ : ContDiff ℝ ∞ φ) (N : ℕ) (r : Symbol n V W (m + 0 - N)) :
    Symbol n V W (m - N) :=
  inclusion (by simp) ((cutoff W hφ).comp r)

private theorem coefficient_remainder (hφ : ContDiff ℝ ∞ φ) (N : ℕ)
    (r : Symbol n V W (m + 0 - N)) (x ξ : CoordinateSpace n) :
    (remainder hφ N r).coefficient (x, ξ) = φ x • r.coefficient (x, ξ) := by
  simp [remainder, coefficient_cutoff]

/-- The zeroth term of the expansion of `a # ψ` is `ψ a`. -/
private theorem coefficient_sharpTerm_cutoff_zero (hψ : ContDiff ℝ ∞ ψ)
    (x ξ : CoordinateSpace n) :
    (a.sharpTerm (cutoff V hψ) 0).coefficient (x, ξ) = ψ x • a.coefficient (x, ξ) := by
  simp [coefficient_cutoff]

/-- The first term of the expansion of `a # ψ` is `-i ∑ₖ ∂ₖψ ∂_{ξₖ} a`. -/
private theorem coefficient_sharpTerm_cutoff_one (hψ : ContDiff ℝ ∞ ψ)
    (x ξ : CoordinateSpace n) :
    (a.sharpTerm (cutoff V hψ) 1).coefficient (x, ξ) =
      -Complex.I • ∑ k, coordinateDeriv [k] ψ x • (frequencyDeriv k a).coefficient (x, ξ) := by
  rw [coefficient_sharpTerm, ← (Equiv.funUnique (Fin 1) (Fin n)).symm.sum_comp]
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, div_one, mixedDeriv_cutoff]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hk : List.ofFn ((Equiv.funUnique (Fin 1) (Fin n)).symm k) = [k] := by
    simp [List.ofFn_succ]
  rw [hk, mixedDeriv_def, coordinateDeriv_nil, coefficient_frequencyDeriv]
  ext v
  simp

/-- If `ψ` is constant near `x`, every term of index `k ≥ 1` of the expansion of `a # ψ` vanishes
at `x`. -/
private theorem coefficient_sharpTerm_cutoff_eq_zero (hψ : ContDiff ℝ ∞ ψ)
    {x : CoordinateSpace n} {c : ℝ} (hx : ψ =ᶠ[𝓝 x] fun _ ↦ c) {k : ℕ} (hk : k ≠ 0)
    (ξ : CoordinateSpace n) :
    (a.sharpTerm (cutoff V hψ) k).coefficient (x, ξ) = 0 := by
  rw [coefficient_sharpTerm, Finset.sum_eq_zero, smul_zero]
  intro w _
  rw [mixedDeriv_cutoff_eq_zero hψ hx (by simpa using hk), ContinuousLinearMap.comp_zero]

variable [CompleteSpace V] [CompleteSpace W]

/-- The compression is the expansion of `φ (a # ψ)` with `N` terms, the terms with index `k ≥ 1`
involving the derivatives of `ψ` of order `k`, plus `φ` times the remainder of order `m - N`. -/
private theorem coefficient_compress_eq_sum (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (N : ℕ) (x ξ : CoordinateSpace n) :
    (a.compress φ ψ hφ hψ hψc).coefficient (x, ξ) = φ x •
      (∑ k ∈ range N, (a.sharpTerm (cutoff V hψ) k).coefficient (x, ξ) +
        (a.sharpRemainder (cutoff V hψ) (hasCompactSpatialSupport_cutoff hψ hψc) N).coefficient
          (x, ξ)) := by
  rw [coefficient_compress_eq_cutoff, coefficient_sharpRemainder]
  simp

/-- **The compression to second order.** The compression of a symbol `a` of order `m` by the
cutoffs `φ` and `ψ` is

`φ (a # ψ) = φ ψ a - i ∑ₖ φ ∂ₖψ ∂_{ξₖ} a`

up to a symbol of order `m - 2`. -/
theorem exists_coefficient_compress_eq (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) :
    ∃ r : Symbol n V W (m - 2), ∀ x ξ, (a.compress φ ψ hφ hψ hψc).coefficient (x, ξ) =
      (φ x * ψ x) • a.coefficient (x, ξ) -
        Complex.I • ∑ k, (φ x * coordinateDeriv [k] ψ x) • (frequencyDeriv k a).coefficient (x, ξ) +
        r.coefficient (x, ξ) := by
  refine ⟨inclusion (by norm_num) (remainder hφ 2
    (a.sharpRemainder (cutoff V hψ) (hasCompactSpatialSupport_cutoff hψ hψc) 2)), fun x ξ ↦ ?_⟩
  rw [coefficient_compress_eq_sum hφ hψ hψc 2, coefficient_inclusion, coefficient_remainder,
    sum_range_succ, sum_range_one, coefficient_sharpTerm_cutoff_zero,
    coefficient_sharpTerm_cutoff_one, smul_add, smul_add, smul_smul, smul_comm (φ x) (-Complex.I),
    Finset.smul_sum]
  simp only [smul_smul, sub_eq_add_neg, neg_smul]

/-- **Compressions by cutoffs that are constant near the support of the left one.** If `ψ = 1` on a
neighbourhood of the support of `φ`, the compression `φ (a # ψ)` is the product `φ a` up to a
symbol of order `m - (N + 1)`, for every `N`. -/
private theorem coefficient_compress_eq_of_eventuallyEq (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hψφ : ∀ x ∈ tsupport φ, ψ =ᶠ[𝓝 x] fun _ ↦ 1) (N : ℕ) (x ξ : CoordinateSpace n) :
    (a.compress φ ψ hφ hψ hψc).coefficient (x, ξ) = φ x • a.coefficient (x, ξ) +
      (remainder hφ (N + 1) (a.sharpRemainder (cutoff V hψ) (hasCompactSpatialSupport_cutoff hψ hψc)
        (N + 1))).coefficient (x, ξ) := by
  rw [coefficient_compress_eq_sum hφ hψ hψc (N + 1), coefficient_remainder, smul_add]
  congr 1
  by_cases hx : φ x = 0
  · simp [hx]
  have hψx := hψφ x (subset_tsupport φ hx)
  rw [sum_range_succ', Finset.sum_eq_zero fun k _ ↦
      coefficient_sharpTerm_cutoff_eq_zero hψ hψx (Nat.succ_ne_zero k) ξ, zero_add,
    coefficient_sharpTerm_cutoff_zero, hψx.eq_of_nhds, one_smul]

/-- **The quantization of a compression** is the compressed quantization:
`Op(φ (a # ψ)) u = φ · Op(a) (ψ u)`. -/
theorem quantizeSchwartzValue_compress (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.compress φ ψ hφ hψ hψc).coefficient u x =
      φ x • quantizeSchwartzValue a.coefficient
        (SchwartzMap.smulLeftCLM V (fun y ↦ (ψ y : ℂ)) u) x := by
  have hc := hasCompactSpatialSupport_cutoff (V := V) hψ hψc
  have h : quantizeSchwartzValue (a.compress φ ψ hφ hψ hψc).coefficient u x =
      φ x • quantizeSchwartzValue (a.sharp (cutoff V hψ) hc).coefficient u x := by
    rw [quantizeSchwartzValue_def, quantizeSchwartzValue_def, ← integral_smul]
    refine integral_congr_ae (.of_forall fun ζ ↦ ?_)
    simp only [coefficient_compress_eq_cutoff, smul_apply, smul_comm (φ x)]
  rw [h, quantizeSchwartzValue_sharp_eq_quantizeSchwartzValue]
  congr 2
  ext y
  have hψt : (fun y ↦ (ψ y : ℂ)).HasTemperateGrowth :=
    (hψc.comp_left Complex.ofReal_zero).hasTemperateGrowth (Complex.ofRealCLM.contDiff.comp hψ)
  rw [HasCompactSupport.toSchwartzMap_toFun, SchwartzMap.smulLeftCLM_apply_apply hψt,
    show (cutoff V hψ).coefficient = fun p ↦ ψ p.1 • ContinuousLinearMap.id ℂ V from
      funext (coefficient_cutoff hψ),
    quantizeSchwartzValue_comp_fst (fun y ↦ ψ y • ContinuousLinearMap.id ℂ V)]
  simp [Complex.coe_smul]

/-- **Independence of the input cutoff.** If `ψ` and `ψ'` both equal `1` on a neighbourhood of the
support of `φ`, the compressions of `a` by `φ, ψ` and by `φ, ψ'` differ by a smoothing symbol: both
are `φ a` modulo smoothing symbols. -/
theorem isSmoothing_compress_sub_compress {ψ' : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ' : ContDiff ℝ ∞ ψ')
    (hψ'c : HasCompactSupport ψ') (hψφ : ∀ x ∈ tsupport φ, ψ =ᶠ[𝓝 x] fun _ ↦ 1)
    (hψ'φ : ∀ x ∈ tsupport φ, ψ' =ᶠ[𝓝 x] fun _ ↦ 1) :
    (a.compress φ ψ hφ hψ hψc - a.compress φ ψ' hφ hψ' hψ'c).IsSmoothing := by
  refine isSmoothing_iff_forall_nat.2 fun N ↦ ⟨inclusion (by push_cast; linarith)
    (remainder hφ (N + 1) (a.sharpRemainder (cutoff V hψ) (hasCompactSpatialSupport_cutoff hψ hψc)
      (N + 1)) - remainder hφ (N + 1) (a.sharpRemainder (cutoff V hψ')
        (hasCompactSpatialSupport_cutoff hψ' hψ'c) (N + 1))), funext fun ⟨x, ξ⟩ ↦ ?_⟩
  rw [coefficient_inclusion, coefficient_sub, coefficient_sub, Pi.sub_apply, Pi.sub_apply,
    coefficient_compress_eq_of_eventuallyEq hφ hψ hψc hψφ N,
    coefficient_compress_eq_of_eventuallyEq hφ hψ' hψ'c hψ'φ N]
  abel

/-- **Ordinary partitions of unity reproduce a symbol modulo smoothing symbols.** Let `φᵢ` be
smooth functions with `∑ᵢ φᵢ = 1` on a set `U` outside which `a` vanishes, and `ψᵢ` compactly
supported smooth functions with `ψᵢ = 1` on a neighbourhood of the support of `φᵢ`. Then the
symbol `∑ᵢ φᵢ (a # ψᵢ)` of `∑ᵢ φᵢ Op(a) ψᵢ` is `a` up to a smoothing symbol. -/
theorem isSmoothing_sum_compress_sub {ι : Type*} {s : Finset ι} {φ ψ : ι → CoordinateSpace n → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hψc : ∀ i, HasCompactSupport (ψ i))
    (hψφ : ∀ i ∈ s, ∀ x ∈ tsupport (φ i), ψ i =ᶠ[𝓝 x] fun _ ↦ 1)
    {U : Set (CoordinateSpace n)} (hU : ∀ x ∈ U, ∑ i ∈ s, φ i x = 1)
    (ha : ∀ x ∉ U, ∀ ξ, a.coefficient (x, ξ) = 0) :
    (∑ i ∈ s, a.compress (φ i) (ψ i) (hφ i) (hψ i) (hψc i) - a).IsSmoothing := by
  refine isSmoothing_iff_forall_nat.2 fun N ↦ ⟨inclusion (by push_cast; linarith)
    (∑ i ∈ s, remainder (hφ i) (N + 1) (a.sharpRemainder (cutoff V (hψ i))
      (hasCompactSpatialSupport_cutoff (hψ i) (hψc i)) (N + 1))), funext fun ⟨x, ξ⟩ ↦ ?_⟩
  have hsum : ∑ i ∈ s, φ i x • a.coefficient (x, ξ) = a.coefficient (x, ξ) := by
    rw [← Finset.sum_smul]
    by_cases hx : x ∈ U
    · rw [hU x hx, one_smul]
    · rw [ha x hx, smul_zero]
  rw [coefficient_inclusion, coefficient_sub, coefficient_sum, coefficient_sum, Pi.sub_apply,
    Finset.sum_apply, Finset.sum_apply, Finset.sum_congr rfl fun i hi ↦
      coefficient_compress_eq_of_eventuallyEq (hφ i) (hψ i) (hψc i) (hψφ i hi) N x ξ,
    Finset.sum_add_distrib, hsum, add_sub_cancel_left]

/-- **Ordinary partitions of unity, for the operators.** Under the hypotheses of
`TauCeti.Symbol.isSmoothing_sum_compress_sub`, `∑ᵢ φᵢ Op(a) (ψᵢ u) = Op(a) u + Op(r) u` for a
smoothing symbol `r`. -/
theorem exists_isSmoothing_sum_smul_quantizeSchwartzValue_eq {ι : Type*} {s : Finset ι}
    {φ ψ : ι → CoordinateSpace n → ℝ} (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
    (hψ : ∀ i, ContDiff ℝ ∞ (ψ i)) (hψc : ∀ i, HasCompactSupport (ψ i))
    (hψφ : ∀ i ∈ s, ∀ x ∈ tsupport (φ i), ψ i =ᶠ[𝓝 x] fun _ ↦ 1)
    {U : Set (CoordinateSpace n)} (hU : ∀ x ∈ U, ∑ i ∈ s, φ i x = 1)
    (ha : ∀ x ∉ U, ∀ ξ, a.coefficient (x, ξ) = 0) :
    ∃ r : Symbol n V W m, r.IsSmoothing ∧ ∀ u x, ∑ i ∈ s, φ i x •
      quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ (ψ i y : ℂ)) u) x =
        quantizeSchwartzValue a.coefficient u x + quantizeSchwartzValue r.coefficient u x := by
  refine ⟨_, isSmoothing_sum_compress_sub hφ hψ hψc hψφ hU ha, fun u x ↦ ?_⟩
  rw [Finset.sum_congr rfl fun i _ ↦
      (quantizeSchwartzValue_compress (hφ i) (hψ i) (hψc i) u x).symm,
    ← quantizeSchwartzValue_sum_left, ← quantizeSchwartzValue_coefficient_add, coefficient_sub,
    add_sub_cancel]

/-- If the squares `χᵢ²` sum to `1` on an open set containing `x`, then `∑ᵢ χᵢ ∂ₖχᵢ = 0` at `x`. -/
private theorem sum_mul_coordinateDeriv_eq_zero {ι : Type*} {s : Finset ι}
    {χ : ι → CoordinateSpace n → ℝ} (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) {U : Set (CoordinateSpace n)}
    (hUo : IsOpen U) (hU : ∀ x ∈ U, ∑ i ∈ s, χ i x ^ 2 = 1) {x : CoordinateSpace n} (hx : x ∈ U)
    (k : Fin n) : ∑ i ∈ s, χ i x * coordinateDeriv [k] (χ i) x = 0 := by
  set g : CoordinateSpace n → ℝ := fun y ↦ ∑ i ∈ s, χ i y ^ 2
  have hd : HasFDerivAt g (∑ i ∈ s, (2 • χ i x ^ (2 - 1)) • fderiv ℝ (χ i) x) x :=
    HasFDerivAt.fun_sum fun i _ ↦ (((hχ i).differentiable (by simp) x).hasFDerivAt).pow 2
  have hg : g =ᶠ[𝓝 x] fun _ ↦ 1 := Filter.eventually_of_mem (hUo.mem_nhds hx) hU
  have h0 : coordinateDeriv [k] g x = 0 := by
    rw [(hg.coordinateDeriv [k]).eq_of_nhds, coordinateDeriv_const _ (List.cons_ne_nil k []),
      Pi.zero_apply]
  rw [coordinateDeriv_cons, coordinateDeriv_nil, hd.fderiv] at h0
  norm_num at h0
  simp only [coordinateDeriv_cons, coordinateDeriv_nil]
  have : ∑ i ∈ s, χ i x * fderiv ℝ (χ i) x (EuclideanSpace.single k 1) =
      (∑ i ∈ s, 2 * χ i x * fderiv ℝ (χ i) x (EuclideanSpace.single k 1)) / 2 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  rw [this, h0, zero_div]

/-- **Square partitions of unity reproduce a symbol modulo order `m - 2`.** Let `χᵢ` be compactly
supported smooth real functions with `∑ᵢ χᵢ² = 1` on an open set `U` outside which the symbol `a`
of order `m` vanishes. Then the symbol `∑ᵢ χᵢ (a # χᵢ)` of the symmetric sum `∑ᵢ χᵢ Op(a) χᵢ` is
`a` up to a symbol of order `m - 2`. The terms of order `m - 1` cancel, since
`∑ᵢ χᵢ ∂ₖχᵢ = ½ ∂ₖ (∑ᵢ χᵢ²) = 0` on `U`. -/
theorem exists_coefficient_eq_sum_compress_sub {ι : Type*} {s : Finset ι}
    {χ : ι → CoordinateSpace n → ℝ} (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχc : ∀ i, HasCompactSupport (χ i)) {U : Set (CoordinateSpace n)} (hUo : IsOpen U)
    (hU : ∀ x ∈ U, ∑ i ∈ s, χ i x ^ 2 = 1) (ha : ∀ x ∉ U, ∀ ξ, a.coefficient (x, ξ) = 0) :
    ∃ r : Symbol n V W (m - 2), r.coefficient =
      (∑ i ∈ s, a.compress (χ i) (χ i) (hχ i) (hχ i) (hχc i)).coefficient - a.coefficient := by
  choose r hr using fun i ↦ exists_coefficient_compress_eq (a := a) (hχ i) (hχ i) (hχc i)
  refine ⟨∑ i ∈ s, r i, funext fun ⟨x, ξ⟩ ↦ ?_⟩
  -- The terms of orders `m` and `m - 1` sum to `a` and to `0`.
  have h₀ : ∑ i ∈ s, (χ i x * χ i x) • a.coefficient (x, ξ) = a.coefficient (x, ξ) := by
    rw [← Finset.sum_smul]
    by_cases hx : x ∈ U
    · simp_rw [← sq, hU x hx, one_smul]
    · rw [ha x hx, smul_zero]
  have h₁ : ∑ i ∈ s, Complex.I • ∑ k, (χ i x * coordinateDeriv [k] (χ i) x) •
      (frequencyDeriv k a).coefficient (x, ξ) = 0 := by
    rw [← Finset.smul_sum, Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    by_cases hx : x ∈ U
    · simp [sum_mul_coordinateDeriv_eq_zero hχ hUo hU hx]
    · have h : (fun η ↦ a.coefficient (x, η)) = 0 := funext (ha x hx)
      simp [coefficient_frequencyDeriv, h]
  simp only [coefficient_sum, Pi.sub_apply, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ hr i x ξ, Finset.sum_add_distrib, Finset.sum_sub_distrib, h₀,
    h₁, sub_zero, add_sub_cancel_left]

/-- **Square partitions of unity, for the operators.** Under the hypotheses of
`TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub`, there is a symbol `r` of order `m - 2`
with `∑ᵢ χᵢ Op(a) (χᵢ u) = Op(a) u + Op(r) u` for every Schwartz function `u`. -/
theorem exists_sum_smul_quantizeSchwartzValue_eq {ι : Type*} {s : Finset ι}
    {χ : ι → CoordinateSpace n → ℝ} (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχc : ∀ i, HasCompactSupport (χ i)) {U : Set (CoordinateSpace n)} (hUo : IsOpen U)
    (hU : ∀ x ∈ U, ∑ i ∈ s, χ i x ^ 2 = 1) (ha : ∀ x ∉ U, ∀ ξ, a.coefficient (x, ξ) = 0) :
    ∃ r : Symbol n V W (m - 2), ∀ u x, ∑ i ∈ s, χ i x •
      quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (fun y ↦ (χ i y : ℂ)) u) x =
        quantizeSchwartzValue a.coefficient u x + quantizeSchwartzValue r.coefficient u x := by
  obtain ⟨r, hr⟩ := exists_coefficient_eq_sum_compress_sub hχ hχc hUo hU ha
  refine ⟨r, fun u x ↦ ?_⟩
  rw [Finset.sum_congr rfl fun i _ ↦
      (quantizeSchwartzValue_compress (hχ i) (hχ i) (hχc i) u x).symm,
    ← quantizeSchwartzValue_sum_left, ← quantizeSchwartzValue_coefficient_add, hr,
    add_sub_cancel]

/-- **Symmetric and ordinary partitions.** The symmetric sum `∑ᵢ χᵢ Op(a) χᵢ` over a square
partition of unity and the sum `∑ⱼ φⱼ Op(a) ψⱼ` over an ordinary partition of unity, as in
`TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub` and
`TauCeti.Symbol.isSmoothing_sum_compress_sub`, differ by an operator of order `m - 2`. -/
theorem exists_coefficient_eq_sum_compress_sub_sum_compress {ι κ : Type*} {s : Finset ι}
    {t : Finset κ} {χ : ι → CoordinateSpace n → ℝ} (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχc : ∀ i, HasCompactSupport (χ i)) {φ ψ : κ → CoordinateSpace n → ℝ}
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j)) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j))
    (hψφ : ∀ j ∈ t, ∀ x ∈ tsupport (φ j), ψ j =ᶠ[𝓝 x] fun _ ↦ 1) {U : Set (CoordinateSpace n)}
    (hUo : IsOpen U) (hχU : ∀ x ∈ U, ∑ i ∈ s, χ i x ^ 2 = 1) (hφU : ∀ x ∈ U, ∑ j ∈ t, φ j x = 1)
    (ha : ∀ x ∉ U, ∀ ξ, a.coefficient (x, ξ) = 0) :
    ∃ r : Symbol n V W (m - 2), r.coefficient =
      (∑ i ∈ s, a.compress (χ i) (χ i) (hχ i) (hχ i) (hχc i)).coefficient -
        (∑ j ∈ t, a.compress (φ j) (ψ j) (hφ j) (hψ j) (hψc j)).coefficient := by
  obtain ⟨r, hr⟩ := exists_coefficient_eq_sum_compress_sub hχ hχc hUo hχU ha
  obtain ⟨b, hb⟩ := isSmoothing_iff.1 (isSmoothing_sum_compress_sub hφ hψ hψc hψφ hφU ha) (m - 2)
  refine ⟨r - b, ?_⟩
  rw [coefficient_sub, hr, hb, coefficient_sub]
  abel

end Compress

/-! ### Formal adjoints of compressions -/

section Adjoint

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W] [CompleteSpace W] {a : Symbol n V W m}
  {φ ψ : CoordinateSpace n → ℝ}

/-- **The formal adjoint of a compression.** For a symbol `a` with compact spatial support between
complex Hilbert spaces, and compactly supported smooth real cutoffs `φ` and `ψ`, the formal adjoint
of `u ↦ φ · Op(a) (ψ u)` is `v ↦ ψ · Op(a*) (φ v)`, where `a*` is the adjoint symbol
(`TauCeti.Symbol.adjoint`). In particular the symmetric compression `χ Op(a) χ` of a formally
self-adjoint quantization is formally self-adjoint. -/
theorem integral_inner_quantizeSchwartzValue_compress (ha : a.HasCompactSpatialSupport)
    (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (u : 𝓢(CoordinateSpace n, V)) (v : 𝓢(CoordinateSpace n, W)) :
    ∫ x, inner ℂ (quantizeSchwartzValue (a.compress φ ψ hφ hψ hψc).coefficient u x) (v x) =
      ∫ x, inner ℂ (u x)
        (quantizeSchwartzValue ((a.adjoint ha).compress ψ φ hψ hφ hφc).coefficient v x) := by
  have hφt : (fun y ↦ (φ y : ℂ)).HasTemperateGrowth :=
    (hφc.comp_left Complex.ofReal_zero).hasTemperateGrowth (Complex.ofRealCLM.contDiff.comp hφ)
  have hψt : (fun y ↦ (ψ y : ℂ)).HasTemperateGrowth :=
    (hψc.comp_left Complex.ofReal_zero).hasTemperateGrowth (Complex.ofRealCLM.contDiff.comp hψ)
  simp_rw [quantizeSchwartzValue_compress, ← Complex.coe_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  have key := integral_inner_quantizeSchwartzValue_adjoint a ha
    (SchwartzMap.smulLeftCLM V (fun y ↦ (ψ y : ℂ)) u)
    (SchwartzMap.smulLeftCLM W (fun y ↦ (φ y : ℂ)) v)
  simp_rw [SchwartzMap.smulLeftCLM_apply_apply hφt, SchwartzMap.smulLeftCLM_apply_apply hψt,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal] at key
  exact key

end Adjoint

end Symbol

end TauCeti
