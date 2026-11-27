/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Data.Set.Card
public import TauCeti.Analysis.Complex.ThetaLine.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Int.Interval
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Algebra.Module.Cardinality
import TauCeti.Analysis.Calculus.MeanValue

/-!
# Bohr–Sommerfeld quantization of the theta line

Identify the torus `ℝ² / ℤ²` with `ℂ / (ℤ + τℤ)` through `z = q + τ p`, for `Im τ ≠ 0`, and equip
it with the level-`k` theta line with characteristics `(α, β)` and its Chern connection
(`TauCeti.thetaFactor`, `TauCeti.thetaConnectionForm`). The circles `{p = const}` are the leaves of
the real polarization spanned by `∂/∂q`. This file computes the real (Bohr–Sommerfeld)
quantization of the torus for this polarization and compares it with the space of smooth global
polarized sections.

On the leaf through `p`, lifted to the line `q ↦ q + pτ` of `ℂ`, the theta line restricts to the
line over the circle `ℝ / ℤ` with transition `e_(1,0) = exp (2πiα)`: its sections are the functions
`f : ℝ → ℂ` with `f (q + 1) = exp (2πiα) f q`. The Chern connection is `d + A dz` in the
trivialization of the pull-back to `ℂ`, and `dz (∂/∂q) = 1`, so a section is parallel along the leaf
exactly when `f' q + A (q + pτ) f q = 0`. On the leaf `A (q + pτ) = 2πikp`
(`TauCeti.thetaConnectionForm_ofReal_add_ofReal_mul`), so the parallel sections are the multiples of
`q ↦ exp (-2πikpq)`
(`TauCeti.apply_eq_apply_zero_mul_cexp_of_hasDerivAt_thetaConnectionForm`), and parallel transport
once around the leaf multiplies by the line holonomy `exp (-2πi(kp + α))`
(`TauCeti.thetaLeafHolonomy`, `TauCeti.thetaLeafHolonomy_mul_apply_zero`).

A leaf carries a nonzero parallel section exactly when its holonomy is trivial
(`TauCeti.thetaLeafSections_eq_bot_iff`), that is when `kp + α` is an integer
(`TauCeti.thetaLeafHolonomy_eq_one_iff`); the parallel sections then form a line
(`TauCeti.finrank_thetaLeafSections`). These are the **Bohr–Sommerfeld leaves**. For `k ≠ 0` there
are exactly `|k|` of them in `0 ≤ p < 1` (`TauCeti.ncard_thetaBohrSommerfeldLeaves`); for `k > 0`
they are the leaves `p = (m - α) / k` with `⌈α⌉ ≤ m < ⌈α⌉ + k`
(`TauCeti.thetaBohrSommerfeldLeaves_eq_image`), so changing the characteristic `α`, a flat twist of
the line, shifts them. The Bohr–Sommerfeld quantization, the direct sum of the parallel lines over
the Bohr–Sommerfeld leaves, therefore has dimension `|k|`
(`TauCeti.finrank_thetaBohrSommerfeldQuantization`); for `k > 0` and `Im τ > 0` this is the
dimension `k` of the Kähler quantization `TauCeti.thetaSections` (`TauCeti.finrank_thetaSections`).

In contrast, a continuous section of the theta line that is parallel along every leaf vanishes
(`TauCeti.eq_zero_of_forall_mem_thetaLeafSections`): it vanishes on every leaf with nontrivial
holonomy, and for `k ≠ 0` those leaves are dense. In particular the space of smooth global
polarized sections is zero (`TauCeti.thetaPolarizedSections_eq_bot`); the Bohr–Sommerfeld
quantization is not a space of global sections.

## Main definitions

* `TauCeti.thetaLeafSections k τ α p`: the parallel sections of the theta line along the leaf
  through `p`.
* `TauCeti.thetaLeafHolonomy k α p`: the holonomy `exp (-2πi(kp + α))` of the theta line around
  that leaf.
* `TauCeti.thetaBohrSommerfeldLeaves k α`: the Bohr–Sommerfeld leaves `0 ≤ p < 1`.
* `TauCeti.ThetaBohrSommerfeldQuantization k τ α`: the direct sum of the parallel lines over the
  Bohr–Sommerfeld leaves.
* `TauCeti.thetaPolarizedSections k τ α β`: the smooth global sections of the theta line that are
  parallel along every leaf.

## Main results

* `TauCeti.thetaLeafHolonomy_mul_apply_zero`: the holonomy is the parallel transport once around
  the leaf.
* `TauCeti.thetaLeafSections_eq_bot_iff`, `TauCeti.finrank_thetaLeafSections`: a leaf carries a
  line of parallel sections if its holonomy is trivial, and none otherwise.
* `TauCeti.thetaLeafHolonomy_eq_one_iff`: the Bohr–Sommerfeld condition `kp + α ∈ ℤ`.
* `TauCeti.ncard_thetaBohrSommerfeldLeaves`: there are `|k|` Bohr–Sommerfeld leaves.
* `TauCeti.finrank_thetaBohrSommerfeldQuantization`: the Bohr–Sommerfeld quantization has
  dimension `|k|`.
* `TauCeti.thetaPolarizedSections_eq_bot`: every smooth global polarized section vanishes.

## References

* Martin Schottenloher, *Lecture Notes on Geometric Quantization*, version 15.6, 2025,
  Definition 11.4 and Proposition 11.5 (Bohr–Sommerfeld leaves and the vanishing of polarized
  sections on leaves with nontrivial holonomy).
* Jędrzej Śniatycki, *Geometric Quantization and Quantum Mechanics*, Applied Mathematical
  Sciences 30, Springer, 1980 (Bohr–Sommerfeld conditions for real polarizations).
-/

public section

open Complex Set
open scoped Real ContDiff DirectSum

namespace TauCeti

variable {k : ℤ} {τ : ℂ} {α β p : ℝ}

/-! ### The connection along a leaf -/

/-- The connection form is invariant under real translations, along the leaves `{p = const}`. -/
@[simp]
theorem thetaConnectionForm_ofReal_add (q : ℝ) (z : ℂ) :
    thetaConnectionForm k τ (q + z) = thetaConnectionForm k τ z := by
  simp [thetaConnectionForm_def]

/-- At the point `pτ` of the leaf through `p`, the connection form is `2πikp`. -/
theorem thetaConnectionForm_ofReal_mul (hτ : τ.im ≠ 0) (p : ℝ) :
    thetaConnectionForm k τ (p * τ) = 2 * π * I * k * p := by
  have : (τ.im : ℂ) ≠ 0 := ofReal_ne_zero.mpr hτ
  rw [thetaConnectionForm_def]
  simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, ofReal_mul]
  field_simp

/-- On the leaf through `p`, the connection form is the constant `2πikp`. -/
theorem thetaConnectionForm_ofReal_add_ofReal_mul (hτ : τ.im ≠ 0) (q p : ℝ) :
    thetaConnectionForm k τ (q + p * τ) = 2 * π * I * k * p := by
  rw [thetaConnectionForm_ofReal_add, thetaConnectionForm_ofReal_mul hτ]

/-- **Parallel sections along a leaf.** A function `f` on the leaf through `p` that is parallel for
the Chern connection, `f' q = -A (q + pτ) f q`, is the multiple `f q = f 0 exp (-A (pτ) q)` of a
single exponential. -/
theorem apply_eq_apply_zero_mul_cexp_of_hasDerivAt_thetaConnectionForm {f : ℝ → ℂ}
    (hf : ∀ q : ℝ, HasDerivAt f (-thetaConnectionForm k τ (q + p * τ) * f q) q) (q : ℝ) :
    f q = f 0 * cexp (-(thetaConnectionForm k τ (p * τ) * q)) := by
  set c := thetaConnectionForm k τ (p * τ)
  have hg (t : ℝ) : HasDerivAt (fun t : ℝ ↦ f t * cexp (c * t)) 0 t := by
    have he : HasDerivAt (fun t : ℝ ↦ cexp (c * t)) (cexp (c * t) * c) t := by
      simpa using HasDerivAt.cexp (((hasDerivAt_id t).ofReal_comp).const_mul c)
    convert (hf t).mul he using 1
    rw [thetaConnectionForm_ofReal_add]
    ring
  have h := TauCeti.is_const_of_hasDerivAt_zero hg q 0
  simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at h
  rw [← h, mul_assoc, ← Complex.exp_add]
  simp

/-! ### Parallel sections and holonomy along a leaf -/

variable (k τ α p) in
/-- The **parallel sections of the theta line along the leaf** `{p = const}`: the functions
`f : ℝ → ℂ` on the line `q ↦ q + pτ` with the automorphy law `f (q + 1) = exp (2πiα) f q` of the
theta line restricted to the leaf, and parallel for its Chern connection:
`f' q + A (q + pτ) f q = 0`, where `A = TauCeti.thetaConnectionForm k τ`. -/
def thetaLeafSections : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | (∀ q : ℝ, f (q + 1) = cexp (2 * π * I * α) * f q) ∧
    ∀ q : ℝ, HasDerivAt f (-thetaConnectionForm k τ (q + p * τ) * f q) q}
  add_mem' := by
    rintro f g ⟨hf1, hf⟩ ⟨hg1, hg⟩
    exact ⟨fun q ↦ by simp [hf1, hg1, mul_add], fun q ↦ by simpa [mul_add] using (hf q).add (hg q)⟩
  zero_mem' := ⟨fun q ↦ by simp, fun q ↦ by simp⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf⟩
    exact ⟨fun q ↦ by simp [hf1, mul_left_comm],
      fun q ↦ by simpa [mul_left_comm] using (hf q).const_smul c⟩

theorem mem_thetaLeafSections_iff {f : ℝ → ℂ} :
    f ∈ thetaLeafSections k τ α p ↔ (∀ q : ℝ, f (q + 1) = cexp (2 * π * I * α) * f q) ∧
      ∀ q : ℝ, HasDerivAt f (-thetaConnectionForm k τ (q + p * τ) * f q) q :=
  Iff.rfl

/-- The parallel sections along a leaf are multiples of a single exponential. -/
theorem thetaLeafSections_le_span :
    thetaLeafSections k τ α p ≤
      ℂ ∙ fun q : ℝ ↦ cexp (-(thetaConnectionForm k τ (p * τ) * q)) := by
  intro f hf
  rw [Submodule.mem_span_singleton]
  exact ⟨f 0, funext fun q ↦
    (apply_eq_apply_zero_mul_cexp_of_hasDerivAt_thetaConnectionForm hf.2 q).symm⟩

instance : FiniteDimensional ℂ (thetaLeafSections k τ α p) :=
  Submodule.finiteDimensional_of_le thetaLeafSections_le_span

variable (k α p) in
/-- The **holonomy of the theta line around the leaf** `{p = const}`, the circle `q ↦ q + pτ`,
`0 ≤ q ≤ 1`: the scalar `exp (-2πi(kp + α))` by which parallel transport once around the leaf
multiplies the fibre (`TauCeti.thetaLeafHolonomy_mul_apply_zero`). -/
noncomputable def thetaLeafHolonomy : ℂ :=
  cexp (-(2 * π * I * (k * p + α)))

theorem thetaLeafHolonomy_def : thetaLeafHolonomy k α p = cexp (-(2 * π * I * (k * p + α))) :=
  (rfl)

/-- **Parallel transport around a leaf is its holonomy.** Transport a vector `f 0` along the leaf
to `f 1`, and identify the fibre at `q = 1` with the fibre at `q = 0` through the automorphy law
`f (q + 1) = exp (2πiα) f q`: the result is `thetaLeafHolonomy k α p * f 0`. -/
theorem thetaLeafHolonomy_mul_apply_zero (hτ : τ.im ≠ 0) {f : ℝ → ℂ}
    (hf : ∀ q : ℝ, HasDerivAt f (-thetaConnectionForm k τ (q + p * τ) * f q) q) :
    thetaLeafHolonomy k α p * f 0 = cexp (-(2 * π * I * α)) * f 1 := by
  have h := apply_eq_apply_zero_mul_cexp_of_hasDerivAt_thetaConnectionForm hf 1
  rw [thetaConnectionForm_ofReal_mul hτ] at h
  rw [h, thetaLeafHolonomy_def, mul_left_comm, ← Complex.exp_add, mul_comm]
  congr 2
  push_cast
  ring

/-- **The Bohr–Sommerfeld condition.** The holonomy around the leaf `{p = const}` is trivial exactly
when `kp + α` is an integer. -/
theorem thetaLeafHolonomy_eq_one_iff : thetaLeafHolonomy k α p = 1 ↔ ∃ m : ℤ, k * p + α = m := by
  rw [thetaLeafHolonomy_def, Complex.exp_eq_one_iff]
  refine ⟨fun ⟨n, hn⟩ ↦ ⟨-n, ?_⟩, fun ⟨m, hm⟩ ↦ ⟨-m, ?_⟩⟩
  · have h2 : (2 * π * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    apply ofReal_injective
    apply mul_left_cancel₀ h2
    push_cast
    linear_combination -hn
  · have hcast : (k : ℂ) * p + α = ((k * p + α : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, hm]
    push_cast
    ring

/-- For `k ≠ 0` the leaves with trivial holonomy are the leaves `p = (m - α) / k`, `m ∈ ℤ`. -/
theorem setOf_thetaLeafHolonomy_eq_one (hk : k ≠ 0) :
    {p | thetaLeafHolonomy k α p = 1} = range fun m : ℤ ↦ (m - α) / k := by
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  ext p
  simp only [mem_ofPred_eq, thetaLeafHolonomy_eq_one_iff, mem_range, div_eq_iff hk']
  exact exists_congr fun m ↦ ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩

/-- The leaf holonomy is unchanged by `p ↦ p + 1`: the leaves `p` and `p + 1` are the same leaf of
the torus. -/
@[simp]
theorem thetaLeafHolonomy_add_one : thetaLeafHolonomy k α (p + 1) = thetaLeafHolonomy k α p := by
  rw [thetaLeafHolonomy_def, thetaLeafHolonomy_def, Complex.exp_eq_exp_iff_exists_int]
  exact ⟨-k, by push_cast; ring⟩

/-- On a Bohr–Sommerfeld leaf the parallel sections are the multiples of `q ↦ exp (-2πikpq)`. -/
theorem thetaLeafSections_eq_span (hτ : τ.im ≠ 0) (h : thetaLeafHolonomy k α p = 1) :
    thetaLeafSections k τ α p = ℂ ∙ fun q : ℝ ↦ cexp (-(2 * π * I * k * p * q)) := by
  have hA := thetaConnectionForm_ofReal_mul (k := k) hτ p
  refine le_antisymm
    (by simpa [hA] using thetaLeafSections_le_span (k := k) (τ := τ) (α := α) (p := p)) ?_
  rw [Submodule.span_singleton_le_iff_mem]
  refine ⟨fun q ↦ ?_, fun q ↦ ?_⟩
  · have h' : cexp (-(2 * π * I * (k * p))) = cexp (2 * π * I * α) := by
      rw [thetaLeafHolonomy_def] at h
      rw [← mul_one (cexp (2 * π * I * α)), ← h, ← Complex.exp_add]
      congr 1
      ring
    beta_reduce
    rw [← h', ← Complex.exp_add]
    congr 1
    push_cast
    ring
  · rw [thetaConnectionForm_ofReal_add, hA]
    have := HasDerivAt.cexp (((hasDerivAt_id q).ofReal_comp).const_mul (-(2 * π * I * k * p)))
    convert this using 1
    · funext y
      simp
    · simp only [id_eq, ofReal_one, neg_mul]
      ring

/-- **A leaf carries a nonzero parallel section exactly when its holonomy is trivial.** -/
theorem thetaLeafSections_eq_bot_iff (hτ : τ.im ≠ 0) :
    thetaLeafSections k τ α p = ⊥ ↔ thetaLeafHolonomy k α p ≠ 1 := by
  refine ⟨fun h hhol ↦ ?_, fun hhol ↦ ?_⟩
  · rw [thetaLeafSections_eq_span hτ hhol, Submodule.span_singleton_eq_bot] at h
    simpa using congrFun h 0
  · rw [Submodule.eq_bot_iff]
    intro f hf
    have h := thetaLeafHolonomy_mul_apply_zero (α := α) hτ hf.2
    have h1 := hf.1 0
    rw [zero_add] at h1
    rw [h1, ← mul_assoc, ← Complex.exp_add] at h
    have h0 : f 0 = 0 := by
      by_contra hne
      exact hhol (by simpa [hne] using h)
    exact funext fun q ↦ by
      simpa [h0] using apply_eq_apply_zero_mul_cexp_of_hasDerivAt_thetaConnectionForm hf.2 q

/-- On a Bohr–Sommerfeld leaf the parallel sections form a line. -/
theorem finrank_thetaLeafSections (hτ : τ.im ≠ 0) (h : thetaLeafHolonomy k α p = 1) :
    Module.finrank ℂ (thetaLeafSections k τ α p) = 1 := by
  rw [thetaLeafSections_eq_span hτ h]
  exact finrank_span_singleton fun h0 ↦ by simpa using congrFun h0 0

/-! ### The Bohr–Sommerfeld leaves and the real quantization -/

variable (k α) in
/-- The **Bohr–Sommerfeld leaves** of the theta line: the leaves `{p = const}`, `0 ≤ p < 1`, along
which the holonomy of the theta line is trivial. -/
def thetaBohrSommerfeldLeaves : Set ℝ :=
  {p | p ∈ Ico 0 1 ∧ thetaLeafHolonomy k α p = 1}

theorem mem_thetaBohrSommerfeldLeaves_iff :
    p ∈ thetaBohrSommerfeldLeaves k α ↔ p ∈ Ico 0 1 ∧ ∃ m : ℤ, k * p + α = m := by
  rw [← thetaLeafHolonomy_eq_one_iff]
  rfl

/-- Reversing the level and the characteristic does not change the Bohr–Sommerfeld leaves. -/
theorem thetaBohrSommerfeldLeaves_neg :
    thetaBohrSommerfeldLeaves (-k) (-α) = thetaBohrSommerfeldLeaves k α := by
  ext p
  simp only [mem_thetaBohrSommerfeldLeaves_iff]
  refine and_congr_right fun _ ↦ ⟨fun ⟨m, hm⟩ ↦ ⟨-m, ?_⟩, fun ⟨m, hm⟩ ↦ ⟨-m, ?_⟩⟩ <;>
    push_cast at hm ⊢ <;> linarith

/-- **The Bohr–Sommerfeld leaves** for `k > 0`: the leaves `p = (m - α) / k` for the `k` integers
`⌈α⌉ ≤ m < ⌈α⌉ + k`. -/
theorem thetaBohrSommerfeldLeaves_eq_image (hk : 0 < k) :
    thetaBohrSommerfeldLeaves k α =
      (fun m : ℤ ↦ (m - α) / k) '' (Finset.Ico ⌈α⌉ (⌈α⌉ + k) : Set ℤ) := by
  have hk' : (0 : ℝ) < k := Int.cast_pos.mpr hk
  ext p
  simp only [mem_thetaBohrSommerfeldLeaves_iff, Finset.coe_Ico, mem_image, mem_Ico]
  constructor
  · rintro ⟨⟨hp0, hp1⟩, m, hm⟩
    refine ⟨m, ⟨Int.ceil_le.mpr ?_, ?_⟩, ?_⟩
    · nlinarith
    · have : ((m - k : ℤ) : ℝ) < α := by push_cast; nlinarith
      have := Int.lt_ceil.mpr this
      omega
    · field_simp
      linarith
  · rintro ⟨m, ⟨hm0, hm1⟩, rfl⟩
    have h0 : α ≤ m := Int.ceil_le.mp hm0
    have h1 : (m : ℝ) - k < α := by
      have := Int.lt_ceil.mp (by omega : m - k < ⌈α⌉)
      push_cast at this
      exact this
    refine ⟨⟨div_nonneg (by linarith) hk'.le, (div_lt_one hk').mpr (by linarith)⟩, m, ?_⟩
    field_simp
    ring

/-- **There are `|k|` Bohr–Sommerfeld leaves.** -/
theorem ncard_thetaBohrSommerfeldLeaves (hk : k ≠ 0) :
    (thetaBohrSommerfeldLeaves k α).ncard = k.natAbs := by
  wlog hk' : 0 < k generalizing k α
  · rw [← thetaBohrSommerfeldLeaves_neg, this (neg_ne_zero.mpr hk) (by omega), Int.natAbs_neg]
  have hinj : Function.Injective fun m : ℤ ↦ (m - α) / k := by
    intro m n h
    have hk'' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    simpa using (div_left_inj₀ hk'').mp h
  rw [thetaBohrSommerfeldLeaves_eq_image hk', ncard_image_of_injective _ hinj, ncard_coe_finset,
    Int.card_Ico]
  omega

/-- For `k ≠ 0` there are finitely many Bohr–Sommerfeld leaves. -/
theorem finite_thetaBohrSommerfeldLeaves (hk : k ≠ 0) :
    (thetaBohrSommerfeldLeaves k α).Finite :=
  finite_of_ncard_pos (by rw [ncard_thetaBohrSommerfeldLeaves hk]; omega)

variable (k τ α) in
/-- The **Bohr–Sommerfeld quantization** of the torus for the real polarization by the leaves
`{p = const}`: the direct sum of the lines of parallel sections over the Bohr–Sommerfeld leaves. -/
abbrev ThetaBohrSommerfeldQuantization : Type :=
  ⨁ p : thetaBohrSommerfeldLeaves k α, thetaLeafSections k τ α p

/-- **The Bohr–Sommerfeld quantization of the torus has dimension `|k|`.** For `k > 0` and
`Im τ > 0` this is the dimension `k` of the Kähler quantization `TauCeti.thetaSections`
(`TauCeti.finrank_thetaSections`). -/
theorem finrank_thetaBohrSommerfeldQuantization (hk : k ≠ 0) (hτ : τ.im ≠ 0) :
    Module.finrank ℂ (ThetaBohrSommerfeldQuantization k τ α) = k.natAbs := by
  have := (finite_thetaBohrSommerfeldLeaves (α := α) hk).fintype
  rw [Module.finrank_directSum,
    Finset.sum_congr rfl fun p _ ↦ finrank_thetaLeafSections hτ p.property.2]
  simp [← Nat.card_eq_fintype_card, ncard_thetaBohrSommerfeldLeaves hk]

/-! ### Global polarized sections -/

/-- **A continuous section parallel along every leaf vanishes.** Let `s` be a continuous function
on `ℂ` whose restriction to each leaf `q ↦ q + pτ` is a parallel section of the theta line along
that leaf. For `k ≠ 0` the leaves with nontrivial holonomy are dense, and `s` vanishes on each of
them, so `s = 0`. -/
theorem eq_zero_of_forall_mem_thetaLeafSections (hk : k ≠ 0) (hτ : τ.im ≠ 0) {s : ℂ → ℂ}
    (hs : Continuous s) (h : ∀ p : ℝ, (fun q : ℝ ↦ s (q + p * τ)) ∈ thetaLeafSections k τ α p) :
    s = 0 := by
  have hBS : {p : ℝ | thetaLeafHolonomy k α p = 1}.Countable := by
    rw [setOf_thetaLeafHolonomy_eq_one hk]
    exact countable_range _
  have hzero (q : ℝ) : (fun p : ℝ ↦ s (q + p * τ)) = 0 := by
    refine Continuous.ext_on (hBS.dense_compl ℝ) (by fun_prop) continuous_const fun p hp ↦ ?_
    have h0 := (thetaLeafSections_eq_bot_iff hτ).mpr hp ▸ h p
    exact congrFun ((Submodule.mem_bot ℂ).mp h0) q
  funext z
  have hz : z = ↑(z.re - z.im / τ.im * τ.re) + ↑(z.im / τ.im) * τ := by
    apply Complex.ext <;> simp [field]
  rw [hz]
  exact congrFun (hzero _) _

variable (k τ α β) in
/-- The **smooth global polarized sections** of the theta line for the real polarization by the
leaves `{p = const}`: the smooth functions `s` on `ℂ` with the automorphy law of the theta line
whose restriction to every leaf `q ↦ q + pτ` is parallel. -/
def thetaPolarizedSections : Submodule ℂ (ℂ → ℂ) where
  carrier := {s | ContDiff ℝ ∞ s ∧
    (∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z) ∧
    ∀ p : ℝ, (fun q : ℝ ↦ s (q + p * τ)) ∈ thetaLeafSections k τ α p}
  add_mem' := by
    rintro f g ⟨hf, hfτ, hfp⟩ ⟨hg, hgτ, hgp⟩
    exact ⟨hf.add hg, fun z ↦ by simp [hfτ, hgτ, mul_add], fun p ↦ add_mem (hfp p) (hgp p)⟩
  zero_mem' := ⟨contDiff_const, fun z ↦ by simp, fun p ↦ zero_mem _⟩
  smul_mem' := by
    rintro c f ⟨hf, hfτ, hfp⟩
    exact ⟨hf.const_smul c, fun z ↦ by simp [hfτ, mul_left_comm],
      fun p ↦ Submodule.smul_mem _ c (hfp p)⟩

theorem mem_thetaPolarizedSections_iff {s : ℂ → ℂ} :
    s ∈ thetaPolarizedSections k τ α β ↔ ContDiff ℝ ∞ s ∧
      (∀ z, s (z + τ) = cexp (2 * π * I * β - π * I * k * τ - 2 * π * I * k * z) * s z) ∧
      ∀ p : ℝ, (fun q : ℝ ↦ s (q + p * τ)) ∈ thetaLeafSections k τ α p :=
  Iff.rfl

/-- **Every smooth global polarized section of the theta line vanishes**, for `k ≠ 0`. -/
theorem thetaPolarizedSections_eq_bot (hk : k ≠ 0) (hτ : τ.im ≠ 0) :
    thetaPolarizedSections k τ α β = ⊥ :=
  (Submodule.eq_bot_iff _).mpr fun _ hs ↦
    eq_zero_of_forall_mem_thetaLeafSections hk hτ hs.1.continuous hs.2.2

end TauCeti
