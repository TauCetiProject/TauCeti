/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Adjoint.Basic
public import TauCeti.Analysis.Pseudodifferential.Composition.FrameChange
import TauCeti.Analysis.Calculus.FDeriv.SumSq

/-!
# Compressions of a quantization by spatial cutoffs

For smooth real functions `φ` and `ψ` on `ℝⁿ`, with `ψ` compactly supported, the operator
`u ↦ φ · Op(a) (ψ u)` is again a quantization: it is `Op(φ (a # ψ))`, where `a # ψ` is the
composition symbol of `Op(a) ∘ Op(ψ)` (`TauCeti.Symbol.sharp`). This file calls `φ (a # ψ)` the
*compression* `TauCeti.Symbol.compress` of `a` by the cutoffs `φ` and `ψ`; it is the frame change
`TauCeti.Symbol.frameChange` by the scalar operators `φ id` and `ψ id`, from which it inherits its
linearity, its quantization, its expansion and its locality modulo smoothing symbols.
Compressions are the building blocks for patching local quantizations: with charts and cutoffs, a
global operator is assembled as a locally finite sum of compressions. There are two standard ways
to do this. This file treats both in a single chart, for finite sums of cutoffs `ψᵢ` (or `χᵢ`) with
compact support whose partition identity holds on a set `U` outside which `a` vanishes.

* **Ordinary partitions.** For `∑ᵢ φᵢ = 1` on `U` and cutoffs `ψᵢ` equal to `1` near the points
  where `φᵢ ≠ 0`, the symbol `∑ᵢ φᵢ (a # ψᵢ)` is `a` up to a smoothing symbol
  (`TauCeti.Symbol.isSmoothing_sum_compress_sub`), so the operator `∑ᵢ φᵢ Op(a) ψᵢ` differs from
  `Op(a)` by the quantization of a smoothing symbol
  (`TauCeti.Symbol.exists_isSmoothing_sum_smul_quantizeSchwartzValue_eq`). The sum is not
  symmetric: its formal adjoint is `∑ᵢ ψᵢ Op(a*) φᵢ`.
* **Square partitions.** For `∑ᵢ χᵢ² = 1` on `U`, the symmetric sum `∑ᵢ χᵢ Op(a) χᵢ` is formally
  self-adjoint whenever `Op(a)` is: for `a` with compact spatial support between Hilbert spaces and
  compactly supported cutoffs, the formal adjoint of a single compression `φ Op(a) ψ` is
  `ψ Op(a*) φ` (`TauCeti.Symbol.integral_inner_quantizeSchwartzValue_compress`). Its symbol is `a`
  up to a symbol of order `m - 2` (`TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub`): the
  composition expansion gives `χᵢ (a # χᵢ) = χᵢ² a - i ∑ₖ χᵢ ∂ₖχᵢ ∂_{ξₖ} a` modulo order `m - 2`
  (`TauCeti.Symbol.exists_coefficient_compress_eq`), and the terms of order `m - 1` cancel in the
  sum because `∑ᵢ χᵢ ∂ₖχᵢ = ½ ∂ₖ (∑ᵢ χᵢ²) = 0`. In general the error of order `m - 2` is not
  smoothing: on `ℝ`, where `∑ᵢ χᵢ² = 1` the identities `∑ᵢ χᵢ χᵢ' = 0` and
  `∑ᵢ χᵢ χᵢ'' = -∑ᵢ (χᵢ')²` give `∑ᵢ χᵢ D² χᵢ = D² + ∑ᵢ (χᵢ')²` for `D = -i ∂`.

So the symbols `∑ᵢ χᵢ (a # χᵢ)` and `∑ⱼ φⱼ (a # ψⱼ)` of the symmetric and the ordinary
constructions differ by a symbol of order `m - 2`
(`TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub_sum_compress`). Smooth square partitions of
unity on manifolds are `SmoothPartitionOfUnity.sqrtNormalized`.

## Main declarations

* `TauCeti.Symbol.compress a φ ψ`: the symbol `φ (a # ψ)` of `u ↦ φ · Op(a) (ψ u)`, with
  `TauCeti.Symbol.quantizeSchwartzValue_compress`.
* `TauCeti.Symbol.exists_coefficient_compress_eq`: its expansion to second order.
* `TauCeti.Symbol.exists_isSmoothing_coefficient_compress_eq`,
  `TauCeti.Symbol.isSmoothing_compress_of_eventuallyEq_zero`: if `ψ = 1` (resp. `ψ = 0`) near the
  points where `φ ≠ 0`, the compression is `φ a` (resp. `0`) modulo smoothing symbols.
* `TauCeti.Symbol.isSmoothing_compress_sub_compress`: the compression only depends on the germs of
  `ψ` at the points where `φ ≠ 0`, modulo smoothing symbols.
* `TauCeti.Symbol.isSmoothing_sum_compress_sub`: ordinary partitions reproduce `a` modulo smoothing
  symbols, and `TauCeti.Symbol.exists_isSmoothing_sum_smul_quantizeSchwartzValue_eq` for the
  operators.
* `TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub`: square partitions reproduce `a` modulo
  symbols of order `m - 2`, and `TauCeti.Symbol.exists_sum_smul_quantizeSchwartzValue_eq` for the
  operators.
* `TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub_sum_compress`: the symbols of the symmetric
  and the ordinary constructions differ by a symbol of order `m - 2`.
* `TauCeti.Symbol.integral_inner_quantizeSchwartzValue_compress`: for `a` with compact spatial
  support and compactly supported cutoffs, the formal adjoint of the compression of `a` by `φ` and
  `ψ` is the compression of the adjoint symbol by `ψ` and `φ`.

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

/-! ### The compression of a symbol by two cutoffs -/

section Compress

variable {φ ψ : CoordinateSpace n → ℝ}

/-- The **compression** of a symbol `a` of order `m` by smooth real cutoffs `φ` and `ψ`, with `ψ`
compactly supported: the symbol `φ(x) (a # ψ)(x, ξ)` of order `m`, whose quantization is
`u ↦ φ · Op(a) (ψ u)` (`TauCeti.Symbol.quantizeSchwartzValue_compress`). It is the frame change
(`TauCeti.Symbol.frameChange`) by the scalar multiples `φ id` and `ψ id` of the identity. -/
def compress (a : Symbol n V W m) (φ ψ : CoordinateSpace n → ℝ) (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) : Symbol n V W m :=
  a.frameChange (fun x ↦ φ x • ContinuousLinearMap.id ℂ W)
    (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V)
    (hφ.smul contDiff_const) (hψ.smul contDiff_const) hψc.smul_right

variable {a : Symbol n V W m}

/-- The coefficient of the compression `φ (a # ψ)`. -/
@[simp]
theorem coefficient_compress (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (p : CoordinateSpace n × CoordinateSpace n) :
    (a.compress φ ψ hφ hψ hψc).coefficient p = φ p.1 •
      (a.sharp (cutoff V hψ) (hasCompactSpatialSupport_cutoff hψ hψc)).coefficient p := by
  rw [compress, coefficient_frameChange, ContinuousLinearMap.smul_comp,
    ContinuousLinearMap.id_comp, sharp_congr _ (hasCompactSpatialSupport_cutoff hψ hψc)
      (Symbol.ext <| funext fun _ ↦ by simp)]

section Linear

variable (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
include hφ hψ hψc

theorem add_compress (a b : Symbol n V W m) :
    (a + b).compress φ ψ hφ hψ hψc = a.compress φ ψ hφ hψ hψc + b.compress φ ψ hφ hψ hψc :=
  add_frameChange _ _ _ a b

@[simp]
theorem smul_compress (c : ℂ) (a : Symbol n V W m) :
    (c • a).compress φ ψ hφ hψ hψc = c • a.compress φ ψ hφ hψ hψc :=
  smul_frameChange _ _ _ c a

@[simp]
theorem zero_compress : (0 : Symbol n V W m).compress φ ψ hφ hψ hψc = 0 :=
  zero_frameChange _ _ _

@[simp]
theorem neg_compress (a : Symbol n V W m) :
    (-a).compress φ ψ hφ hψ hψc = -a.compress φ ψ hφ hψ hψc :=
  neg_frameChange _ _ _ a

theorem sub_compress (a b : Symbol n V W m) :
    (a - b).compress φ ψ hφ hψ hψc = a.compress φ ψ hφ hψ hψc - b.compress φ ψ hφ hψ hψc :=
  sub_frameChange _ _ _ a b

theorem inclusion_compress {m' : ℝ} (h : m ≤ m') (a : Symbol n V W m) :
    (inclusion h a).compress φ ψ hφ hψ hψc = inclusion h (a.compress φ ψ hφ hψ hψc) :=
  inclusion_frameChange _ _ _ h a

theorem compress_add_left {φ' : CoordinateSpace n → ℝ} (hφ' : ContDiff ℝ ∞ φ') :
    a.compress (φ + φ') ψ (hφ.add hφ') hψ hψc =
      a.compress φ ψ hφ hψ hψc + a.compress φ' ψ hφ' hψ hψc := by
  rw [compress, compress, compress, ← frameChange_add_left]
  congr 1
  funext x
  simp [add_smul]

theorem compress_add_right {ψ' : CoordinateSpace n → ℝ} (hψ' : ContDiff ℝ ∞ ψ')
    (hψ'c : HasCompactSupport ψ') :
    a.compress φ (ψ + ψ') hφ (hψ.add hψ') (hψc.add hψ'c) =
      a.compress φ ψ hφ hψ hψc + a.compress φ ψ' hφ hψ' hψ'c := by
  rw [compress, compress, compress, ← frameChange_add_right]
  congr 1
  funext x
  simp [add_smul]

theorem compress_sub_right {ψ' : CoordinateSpace n → ℝ} (hψ' : ContDiff ℝ ∞ ψ')
    (hψ'c : HasCompactSupport ψ') :
    a.compress φ (ψ - ψ') hφ (hψ.sub hψ') (hψc.sub hψ'c) =
      a.compress φ ψ hφ hψ hψc - a.compress φ ψ' hφ hψ' hψ'c := by
  rw [compress, compress, compress, ← frameChange_sub_right]
  congr 1
  funext x
  simp [sub_smul]

omit hφ in
@[simp]
theorem compress_zero_left (hφ : ContDiff ℝ ∞ (0 : CoordinateSpace n → ℝ)) :
    a.compress 0 ψ hφ hψ hψc = 0 := by
  ext1
  funext p
  simp

omit hψ hψc in
@[simp]
theorem compress_zero_right (hψ : ContDiff ℝ ∞ (0 : CoordinateSpace n → ℝ))
    (hψc : HasCompactSupport (0 : CoordinateSpace n → ℝ)) : a.compress φ 0 hφ hψ hψc = 0 := by
  rw [compress, ← frameChange_zero_right (a := a) (hφ.smul contDiff_const) contDiff_const
    HasCompactSupport.zero]
  congr 1
  funext x
  simp

end Linear

/-- A compression by a compactly supported left cutoff has compact spatial support. -/
theorem hasCompactSpatialSupport_compress (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    (a.compress φ ψ hφ hψ hψc).HasCompactSpatialSupport :=
  hasCompactSpatialSupport_frameChange _ _ _ hφc.smul_right

/-- A compression of a symbol with compact spatial support has compact spatial support. -/
theorem HasCompactSpatialSupport.compress (ha : a.HasCompactSpatialSupport)
    (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    (a.compress φ ψ hφ hψ hψc).HasCompactSpatialSupport :=
  ha.frameChange _ _ _

/-- A compression of a smoothing symbol is smoothing. -/
theorem IsSmoothing.compress (ha : a.IsSmoothing) (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) : (a.compress φ ψ hφ hψ hψc).IsSmoothing :=
  ha.frameChange _ _ _

/-- A germ condition on the cutoff `ψ` near the support of `φ` is the same condition on the
transition map `ψ id` near the support of `φ id`. -/
private theorem eventuallyEq_smul_id {g : CoordinateSpace n → ℝ}
    (h : ∀ x ∈ Function.support φ, ψ =ᶠ[𝓝 x] g) :
    ∀ x ∈ Function.support fun x ↦ φ x • ContinuousLinearMap.id ℂ W,
      (fun x ↦ ψ x • ContinuousLinearMap.id ℂ V) =ᶠ[𝓝 x]
        fun x ↦ g x • ContinuousLinearMap.id ℂ V :=
  fun x hx ↦ (h x fun h ↦ hx (by simp [h])).fun_comp (· • ContinuousLinearMap.id ℂ V)

variable [CompleteSpace V] [CompleteSpace W]

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
  obtain ⟨r, hr⟩ := exists_coefficient_frameChange_eq (a := a)
    (Φ := fun x ↦ φ x • ContinuousLinearMap.id ℂ W) (Ψ := fun x ↦ ψ x • ContinuousLinearMap.id ℂ V)
    (hφ.smul contDiff_const) (hψ.smul contDiff_const) hψc.smul_right
  refine ⟨r, fun x ξ ↦ ?_⟩
  -- The position derivatives of `ψ id` are those of `ψ`.
  have hj (j : Fin n) : coordinateDeriv [j] (fun y ↦ ψ y • ContinuousLinearMap.id ℂ V) x =
      coordinateDeriv [j] ψ x • ContinuousLinearMap.id ℂ V :=
    (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
      (ContinuousLinearMap.id ℂ V)).coordinateDeriv_comp_left [j] (hψ.of_le (by simp)) x
  rw [compress, hr x ξ]
  simp only [hj, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul,
    ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id, smul_smul, Finset.smul_sum,
    mul_comm _ (φ x)]

/-- **Compressions by a cutoff equal to `1` near the support of the left one.** If `ψ = 1` near
every point where `φ ≠ 0`, the compression `φ (a # ψ)` is the product `φ a` up to a smoothing
symbol. -/
theorem exists_isSmoothing_coefficient_compress_eq (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψφ : ∀ x ∈ Function.support φ, ψ =ᶠ[𝓝 x] fun _ ↦ 1) :
    ∃ r : Symbol n V W m, r.IsSmoothing ∧ ∀ x ξ,
      (a.compress φ ψ hφ hψ hψc).coefficient (x, ξ) = φ x • a.coefficient (x, ξ) +
        r.coefficient (x, ξ) := by
  obtain ⟨r, hr, h⟩ := exists_isSmoothing_coefficient_frameChange_eq (a := a)
    (Φ := fun x ↦ φ x • ContinuousLinearMap.id ℂ W) (Ψ := fun x ↦ ψ x • ContinuousLinearMap.id ℂ V)
    (hφ.smul contDiff_const) (hψ.smul contDiff_const) hψc.smul_right
    (T := ContinuousLinearMap.id ℂ V) fun x hx ↦ by
      simpa using eventuallyEq_smul_id (V := V) (W := W) hψφ x hx
  exact ⟨r, hr, fun x ξ ↦ by simpa [compress] using h x ξ⟩

/-- **Compressions by a cutoff vanishing near the support of the left one.** If `ψ = 0` near every
point where `φ ≠ 0`, the compression `φ (a # ψ)` is smoothing. -/
theorem isSmoothing_compress_of_eventuallyEq_zero (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hψφ : ∀ x ∈ Function.support φ, ψ =ᶠ[𝓝 x] 0) :
    (a.compress φ ψ hφ hψ hψc).IsSmoothing :=
  isSmoothing_frameChange_of_eventuallyEq_zero _ _ _ fun x hx ↦ by
    simpa [Pi.zero_def] using eventuallyEq_smul_id (V := V) (W := W) hψφ x hx

/-- **The quantization of a compression** is the compressed quantization:
`Op(φ (a # ψ)) u = φ · Op(a) (ψ u)`. -/
theorem quantizeSchwartzValue_compress (hφ : ContDiff ℝ ∞ φ) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (u : 𝓢(CoordinateSpace n, V)) (x : CoordinateSpace n) :
    quantizeSchwartzValue (a.compress φ ψ hφ hψ hψc).coefficient u x =
      φ x • quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V ψ u) x := by
  rw [compress, quantizeSchwartzValue_frameChange _ _ _ u (SchwartzMap.smulLeftCLM V ψ u)
    fun y ↦ by simp [SchwartzMap.smulLeftCLM_apply_apply (hψc.hasTemperateGrowth hψ)]]
  simp

/-- **Independence of the input cutoff.** If `ψ` and `ψ'` agree near every point where `φ ≠ 0`,
the compressions of `a` by `φ, ψ` and by `φ, ψ'` differ by a smoothing symbol. -/
theorem isSmoothing_compress_sub_compress {ψ' : CoordinateSpace n → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψ' : ContDiff ℝ ∞ ψ')
    (hψ'c : HasCompactSupport ψ') (hψψ' : ∀ x ∈ Function.support φ, ψ =ᶠ[𝓝 x] ψ') :
    (a.compress φ ψ hφ hψ hψc - a.compress φ ψ' hφ hψ' hψ'c).IsSmoothing :=
  isSmoothing_frameChange_sub_frameChange _ _ _ _ _ (eventuallyEq_smul_id hψψ')

/-- **Ordinary partitions of unity reproduce a symbol modulo smoothing symbols.** Let `φᵢ` be
finitely many smooth functions with `∑ᵢ φᵢ = 1` on a set `U` outside which `a` vanishes, and `ψᵢ`
compactly supported smooth functions with `ψᵢ = 1` near every point where `φᵢ ≠ 0`. Then the
symbol `∑ᵢ φᵢ (a # ψᵢ)` of `∑ᵢ φᵢ Op(a) ψᵢ` is `a` up to a smoothing symbol. -/
theorem isSmoothing_sum_compress_sub {ι : Type*} {s : Finset ι} {φ ψ : ι → CoordinateSpace n → ℝ}
    (hφ : ∀ i, ContDiff ℝ ∞ (φ i)) (hψ : ∀ i, ContDiff ℝ ∞ (ψ i))
    (hψc : ∀ i, HasCompactSupport (ψ i))
    (hψφ : ∀ i ∈ s, ∀ x ∈ Function.support (φ i), ψ i =ᶠ[𝓝 x] fun _ ↦ 1)
    {U : Set (CoordinateSpace n)} (hU : ∀ x ∈ U, ∑ i ∈ s, φ i x = 1)
    (ha : ∀ x ∉ U, ∀ ξ, a.coefficient (x, ξ) = 0) :
    (∑ i ∈ s, a.compress (φ i) (ψ i) (hφ i) (hψ i) (hψc i) - a).IsSmoothing := by
  choose r hr using fun i (hi : i ∈ s) ↦ exists_isSmoothing_coefficient_compress_eq (a := a)
    (hφ i) (hψ i) (hψc i) (hψφ i hi)
  have hsum (x ξ : CoordinateSpace n) :
      ∑ i ∈ s, φ i x • a.coefficient (x, ξ) = a.coefficient (x, ξ) := by
    rw [← Finset.sum_smul]
    by_cases hx : x ∈ U
    · rw [hU x hx, one_smul]
    · rw [ha x hx, smul_zero]
  have h : ∑ i ∈ s, a.compress (φ i) (ψ i) (hφ i) (hψ i) (hψc i) - a =
      ∑ i ∈ s.attach, r i i.property := by
    ext1
    funext ⟨x, ξ⟩
    rw [coefficient_sub, coefficient_sum, coefficient_sum, Pi.sub_apply, Finset.sum_apply,
      Finset.sum_apply, ← Finset.sum_attach s,
      Finset.sum_congr rfl fun (i : s) _ ↦ (hr i i.property).2 x ξ, Finset.sum_add_distrib,
      Finset.sum_attach s fun i ↦ φ i x • a.coefficient (x, ξ), hsum, add_sub_cancel_left]
  rw [h]
  exact Finset.sum_induction _ IsSmoothing (fun _ _ ↦ IsSmoothing.add) isSmoothing_zero
    fun i _ ↦ (hr i i.property).1

/-- **Ordinary partitions of unity, for the operators.** Under the hypotheses of
`TauCeti.Symbol.isSmoothing_sum_compress_sub`, `∑ᵢ φᵢ Op(a) (ψᵢ u) = Op(a) u + Op(r) u` for a
smoothing symbol `r`. -/
theorem exists_isSmoothing_sum_smul_quantizeSchwartzValue_eq {ι : Type*} {s : Finset ι}
    {φ ψ : ι → CoordinateSpace n → ℝ} (hφ : ∀ i ∈ s, ContDiff ℝ ∞ (φ i))
    (hψ : ∀ i ∈ s, ContDiff ℝ ∞ (ψ i)) (hψc : ∀ i ∈ s, HasCompactSupport (ψ i))
    (hψφ : ∀ i ∈ s, ∀ x ∈ Function.support (φ i), ψ i =ᶠ[𝓝 x] fun _ ↦ 1)
    {U : Set (CoordinateSpace n)} (hU : ∀ x ∈ U, ∑ i ∈ s, φ i x = 1)
    (ha : ∀ x ∉ U, ∀ ξ, a.coefficient (x, ξ) = 0) :
    ∃ r : Symbol n V W m, r.IsSmoothing ∧ ∀ u x, ∑ i ∈ s, φ i x •
      quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (ψ i) u) x =
        quantizeSchwartzValue a.coefficient u x + quantizeSchwartzValue r.coefficient u x := by
  refine ⟨_, isSmoothing_sum_compress_sub (s := s.attach) (φ := fun i ↦ φ i) (ψ := fun i ↦ ψ i)
    (fun i ↦ hφ i i.property) (fun i ↦ hψ i i.property) (fun i ↦ hψc i i.property)
        (fun i _ ↦ hψφ i i.property)
    (fun x hx ↦ (Finset.sum_attach s fun i ↦ φ i x).trans (hU x hx)) ha, fun u x ↦ ?_⟩
  rw [← Finset.sum_attach s, Finset.sum_congr rfl fun (i : s) _ ↦
      (quantizeSchwartzValue_compress (hφ i i.property) (hψ i i.property)
          (hψc i i.property) u x).symm,
    ← quantizeSchwartzValue_sum_left, ← quantizeSchwartzValue_coefficient_add, coefficient_sub,
    add_sub_cancel]

/-- **Square partitions of unity reproduce a symbol modulo order `m - 2`.** Let `χᵢ` be finitely
many compactly supported smooth real functions with `∑ᵢ χᵢ² = 1` on a set `U` outside which the
symbol `a` of order `m` vanishes. Then the symbol `∑ᵢ χᵢ (a # χᵢ)` of the symmetric sum
`∑ᵢ χᵢ Op(a) χᵢ` is `a` up to a symbol of order `m - 2`. The terms of order `m - 1` cancel: on the
interior of `U`, `∑ᵢ χᵢ ∂ₖχᵢ = ½ ∂ₖ (∑ᵢ χᵢ²) = 0`, and off it `a` vanishes by continuity. -/
theorem exists_coefficient_eq_sum_compress_sub {ι : Type*} {s : Finset ι}
    {χ : ι → CoordinateSpace n → ℝ} (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχc : ∀ i, HasCompactSupport (χ i)) {U : Set (CoordinateSpace n)}
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
    by_cases hx : x ∈ interior U
    · have h := sum_smul_fderiv_eq_zero_of_eventuallyEq (s := s) (χ := χ) (c := 1)
        (fun i _ ↦ (hχ i).differentiable (by simp) x)
        (Filter.eventually_of_mem (isOpen_interior.mem_nhds hx) fun y hy ↦
          hU y (interior_subset hy))
      have hk : ∀ k, ∑ i ∈ s, χ i x * coordinateDeriv [k] (χ i) x = 0 := fun k ↦ by
        simpa [coordinateDeriv_cons, coordinateDeriv_nil] using
          congr($h (EuclideanSpace.single k 1))
      simp [hk]
    · -- Off the interior of `U`, `a` vanishes at `x` by continuity.
      have h : (fun η ↦ a.coefficient (x, η)) = 0 := funext fun η ↦
        closure_minimal (fun y hy ↦ ha y hy η) (isClosed_eq (a.contDiff_coefficient.continuous.comp
          (.prodMk continuous_id continuous_const)) continuous_const)
          (by rwa [closure_compl] : x ∈ closure Uᶜ)
      simp [coefficient_frequencyDeriv, h]
  simp only [coefficient_sum, Pi.sub_apply, Finset.sum_apply]
  rw [Finset.sum_congr rfl fun i _ ↦ hr i x ξ, Finset.sum_add_distrib, Finset.sum_sub_distrib, h₀,
    h₁, sub_zero, add_sub_cancel_left]

/-- **Square partitions of unity, for the operators.** Under the hypotheses of
`TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub`, there is a symbol `r` of order `m - 2`
with `∑ᵢ χᵢ Op(a) (χᵢ u) = Op(a) u + Op(r) u` for every Schwartz function `u`. -/
theorem exists_sum_smul_quantizeSchwartzValue_eq {ι : Type*} {s : Finset ι}
    {χ : ι → CoordinateSpace n → ℝ} (hχ : ∀ i ∈ s, ContDiff ℝ ∞ (χ i))
    (hχc : ∀ i ∈ s, HasCompactSupport (χ i)) {U : Set (CoordinateSpace n)}
    (hU : ∀ x ∈ U, ∑ i ∈ s, χ i x ^ 2 = 1) (ha : ∀ x ∉ U, ∀ ξ, a.coefficient (x, ξ) = 0) :
    ∃ r : Symbol n V W (m - 2), ∀ u x, ∑ i ∈ s, χ i x •
      quantizeSchwartzValue a.coefficient (SchwartzMap.smulLeftCLM V (χ i) u) x =
        quantizeSchwartzValue a.coefficient u x + quantizeSchwartzValue r.coefficient u x := by
  obtain ⟨r, hr⟩ := exists_coefficient_eq_sum_compress_sub (s := s.attach) (χ := fun i ↦ χ i)
    (fun i ↦ hχ i i.property) (fun i ↦ hχc i i.property)
    (fun x hx ↦ (Finset.sum_attach s fun i ↦ χ i x ^ 2).trans (hU x hx)) ha
  refine ⟨r, fun u x ↦ ?_⟩
  rw [← Finset.sum_attach s, Finset.sum_congr rfl fun (i : s) _ ↦
      (quantizeSchwartzValue_compress (hχ i i.property) (hχ i i.property)
          (hχc i i.property) u x).symm,
    ← quantizeSchwartzValue_sum_left, ← quantizeSchwartzValue_coefficient_add, hr,
    add_sub_cancel]

/-- **Symmetric and ordinary partitions.** For a square partition of unity `χᵢ` and an ordinary
partition of unity `φⱼ` with cutoffs `ψⱼ`, as in
`TauCeti.Symbol.exists_coefficient_eq_sum_compress_sub` and
`TauCeti.Symbol.isSmoothing_sum_compress_sub`, the symbols `∑ᵢ χᵢ (a # χᵢ)` and `∑ⱼ φⱼ (a # ψⱼ)`
of `∑ᵢ χᵢ Op(a) χᵢ` and `∑ⱼ φⱼ Op(a) ψⱼ` differ by a symbol of order `m - 2`. -/
theorem exists_coefficient_eq_sum_compress_sub_sum_compress {ι κ : Type*} {s : Finset ι}
    {t : Finset κ} {χ : ι → CoordinateSpace n → ℝ} (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hχc : ∀ i, HasCompactSupport (χ i)) {φ ψ : κ → CoordinateSpace n → ℝ}
    (hφ : ∀ j, ContDiff ℝ ∞ (φ j)) (hψ : ∀ j, ContDiff ℝ ∞ (ψ j))
    (hψc : ∀ j, HasCompactSupport (ψ j))
    (hψφ : ∀ j ∈ t, ∀ x ∈ Function.support (φ j), ψ j =ᶠ[𝓝 x] fun _ ↦ 1)
    {U : Set (CoordinateSpace n)} (hχU : ∀ x ∈ U, ∑ i ∈ s, χ i x ^ 2 = 1)
    (hφU : ∀ x ∈ U, ∑ j ∈ t, φ j x = 1) (ha : ∀ x ∉ U, ∀ ξ, a.coefficient (x, ξ) = 0) :
    ∃ r : Symbol n V W (m - 2), r.coefficient =
      (∑ i ∈ s, a.compress (χ i) (χ i) (hχ i) (hχ i) (hχc i)).coefficient -
        (∑ j ∈ t, a.compress (φ j) (ψ j) (hφ j) (hψ j) (hψc j)).coefficient := by
  obtain ⟨r, hr⟩ := exists_coefficient_eq_sum_compress_sub hχ hχc hχU ha
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
  simp_rw [quantizeSchwartzValue_compress, ← Complex.coe_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal]
  have key := integral_inner_quantizeSchwartzValue_adjoint a ha (SchwartzMap.smulLeftCLM V ψ u)
    (SchwartzMap.smulLeftCLM W φ v)
  simp_rw [SchwartzMap.smulLeftCLM_apply_apply (hφc.hasTemperateGrowth hφ),
    SchwartzMap.smulLeftCLM_apply_apply (hψc.hasTemperateGrowth hψ), ← Complex.coe_smul,
    inner_smul_left, inner_smul_right, Complex.conj_ofReal] at key
  exact key

end Adjoint

end Symbol

end TauCeti
