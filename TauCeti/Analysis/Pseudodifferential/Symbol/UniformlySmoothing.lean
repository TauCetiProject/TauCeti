/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Basic

/-!
# Uniformly smoothing symbols

A symbol is *uniformly smoothing* (`TauCeti.Symbol.IsUniformlySmoothing`) if it is a symbol of
every real order with estimates uniform in the position (`TauCeti.Symbol.IsUniform`). This is the
uniform counterpart of a smoothing symbol (`TauCeti.Symbol.IsSmoothing`): a uniformly smoothing
symbol is smoothing and uniform. Uniformly smoothing symbols are closed under the linear operations,
inclusions and derivatives, and they form a two-sided ideal under composition with uniform symbols
(`TauCeti.Symbol.IsUniformlySmoothing.comp_right`, `TauCeti.Symbol.IsUniformlySmoothing.comp_left`).
A uniform symbol vanishing at all large frequencies is uniformly smoothing
(`TauCeti.Symbol.IsUniform.isUniformlySmoothing_of_coefficient_eq_zero`), as is a smoothing symbol
with compact spatial support
(`TauCeti.Symbol.IsSmoothing.isUniformlySmoothing_of_hasCompactSpatialSupport`).
-/

public section

noncomputable section

namespace TauCeti

namespace Symbol

variable {n : ℕ} {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
  [NormedSpace ℂ W] {m m' : ℝ}

/-- A symbol is *uniformly smoothing* if its coefficient is a symbol of every real order with
estimates uniform in the position. -/
def IsUniformlySmoothing (a : Symbol n V W m) : Prop :=
  ∀ m' : ℝ, ∃ b : Symbol n V W m', b.IsUniform ∧ b.coefficient = a.coefficient

theorem isUniformlySmoothing_iff {a : Symbol n V W m} : a.IsUniformlySmoothing ↔
    ∀ m' : ℝ, ∃ b : Symbol n V W m', b.IsUniform ∧ b.coefficient = a.coefficient :=
  Iff.rfl

/-- The estimates characterizing uniformly smoothing symbols: a symbol is uniformly smoothing
exactly when, for every real order `m'` and all words `α` and `β`, the mixed derivative
`∂_x^α ∂_ξ^β a(x, ξ)` is bounded by `C ⟨ξ⟩^(m' - |β|)` at all positions `x` and frequencies `ξ`,
with a constant `C` depending on `m'`, `α` and `β`. -/
theorem isUniformlySmoothing_iff_forall_exists_bound {a : Symbol n V W m} :
    a.IsUniformlySmoothing ↔ ∀ m' : ℝ, ∀ α β : List (Fin n), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖mixedDeriv α β a.coefficient x ξ‖ ≤ C * (1 + ‖ξ‖ ^ 2) ^ ((m' - β.length) / 2) := by
  refine ⟨fun h m' α β => ?_, fun h m' => ⟨⟨a.coefficient, a.contDiff_coefficient,
    fun _ _ α β => (h m' α β).imp fun _ hC => ⟨hC.1, fun x _ ξ => hC.2 x ξ⟩⟩,
    isUniform_iff.2 (h m'), rfl⟩⟩
  obtain ⟨b, hb, hba⟩ := h m'
  exact hba ▸ isUniform_iff.1 hb α β

/-- A symbol is uniformly smoothing iff for every `N` its coefficient is that of a uniform symbol
of order `m - N`. -/
theorem isUniformlySmoothing_iff_forall_nat {a : Symbol n V W m} :
    a.IsUniformlySmoothing ↔
      ∀ N : ℕ, ∃ b : Symbol n V W (m - N), b.IsUniform ∧ b.coefficient = a.coefficient := by
  refine ⟨fun h N => h _, fun h m' => (h ⌈m - m'⌉₊).elim fun b hb => ?_⟩
  exact ⟨inclusion (by linarith [Nat.le_ceil (m - m')]) b, hb.1.inclusion _,
    by rw [coefficient_inclusion, hb.2]⟩

theorem IsUniformlySmoothing.isSmoothing {a : Symbol n V W m} (ha : a.IsUniformlySmoothing) :
    a.IsSmoothing := isSmoothing_iff.2 fun m' => (ha m').imp fun _ hb => hb.2

theorem IsUniformlySmoothing.isUniform {a : Symbol n V W m} (ha : a.IsUniformlySmoothing) :
    a.IsUniform := by
  obtain ⟨b, hb, hba⟩ := ha m
  rw [isUniform_iff, ← hba]
  exact isUniform_iff.1 hb

/-- A smoothing symbol with compact spatial support is uniformly smoothing. -/
theorem IsSmoothing.isUniformlySmoothing_of_hasCompactSpatialSupport {a : Symbol n V W m}
    (ha : a.IsSmoothing) (hsupp : a.HasCompactSpatialSupport) : a.IsUniformlySmoothing := fun m' =>
  (isSmoothing_iff.1 ha m').imp fun _ hba => ⟨(hsupp.of_coefficient_eq hba).isUniform, hba⟩

@[simp]
theorem isUniformlySmoothing_zero : (0 : Symbol n V W m).IsUniformlySmoothing :=
  fun _ => ⟨0, isUniform_zero, rfl⟩

theorem IsUniformlySmoothing.add {a b : Symbol n V W m} (ha : a.IsUniformlySmoothing)
    (hb : b.IsUniformlySmoothing) : (a + b).IsUniformlySmoothing := fun m' => by
  obtain ⟨a', ha', haa⟩ := ha m'
  obtain ⟨b', hb', hbb⟩ := hb m'
  exact ⟨a' + b', ha'.add hb', by simp [haa, hbb]⟩

theorem IsUniformlySmoothing.smul {a : Symbol n V W m} (ha : a.IsUniformlySmoothing) (c : ℂ) :
    (c • a).IsUniformlySmoothing := fun m' => by
  obtain ⟨a', ha', haa⟩ := ha m'
  exact ⟨c • a', ha'.smul c, by simp [haa]⟩

theorem IsUniformlySmoothing.neg {a : Symbol n V W m} (ha : a.IsUniformlySmoothing) :
    (-a).IsUniformlySmoothing := fun m' => by
  obtain ⟨a', ha', haa⟩ := ha m'
  exact ⟨-a', ha'.neg, by simp [haa]⟩

theorem IsUniformlySmoothing.sub {a b : Symbol n V W m} (ha : a.IsUniformlySmoothing)
    (hb : b.IsUniformlySmoothing) : (a - b).IsUniformlySmoothing :=
  sub_eq_add_neg a b ▸ ha.add hb.neg

theorem IsUniformlySmoothing.inclusion {a : Symbol n V W m} (ha : a.IsUniformlySmoothing)
    (h : m ≤ m') : (inclusion h a).IsUniformlySmoothing :=
  fun m'' => (ha m'').imp fun _ hb => ⟨hb.1, by rw [hb.2, coefficient_inclusion]⟩

theorem IsUniformlySmoothing.frequencyDeriv {a : Symbol n V W m} (ha : a.IsUniformlySmoothing)
    (j : Fin n) : (frequencyDeriv j a).IsUniformlySmoothing := fun m' => by
  obtain ⟨a', ha', haa⟩ := ha (m' + 1)
  refine ⟨Symbol.inclusion (by linarith) (Symbol.frequencyDeriv j a'),
    (ha'.frequencyDeriv j).inclusion _, ?_⟩
  funext ⟨x, ξ⟩
  simp [haa]

theorem IsUniformlySmoothing.spatialDeriv {a : Symbol n V W m} (ha : a.IsUniformlySmoothing)
    (j : Fin n) : (spatialDeriv j a).IsUniformlySmoothing := fun m' => by
  obtain ⟨a', ha', haa⟩ := ha m'
  refine ⟨Symbol.spatialDeriv j a', ha'.spatialDeriv j, ?_⟩
  funext ⟨x, ξ⟩
  simp [haa]

section Comp

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]

/-- A uniformly smoothing symbol composed on the right with a uniform symbol is uniformly
smoothing. -/
theorem IsUniformlySmoothing.comp_right {b : Symbol n W U m'} (hb : b.IsUniformlySmoothing)
    {a : Symbol n V W m} (ha : a.IsUniform) : (b.comp a).IsUniformlySmoothing := fun m'' => by
  obtain ⟨b', hb', hbb⟩ := hb (m'' - m)
  exact ⟨Symbol.inclusion (by linarith) (b'.comp a), (hb'.comp ha).inclusion _,
    funext fun p => by simp [hbb]⟩

/-- A uniform symbol composed on the right with a uniformly smoothing symbol is uniformly
smoothing. -/
theorem IsUniformlySmoothing.comp_left {a : Symbol n V W m} (ha : a.IsUniformlySmoothing)
    {b : Symbol n W U m'} (hb : b.IsUniform) : (b.comp a).IsUniformlySmoothing := fun m'' => by
  obtain ⟨a', ha', haa⟩ := ha (m'' - m')
  exact ⟨Symbol.inclusion (by linarith) (b.comp a'), (hb.comp ha').inclusion _,
    funext fun p => by simp [haa]⟩

end Comp

/-- A symbol with estimates uniform in the position that vanishes at every frequency of norm at
least `R` is uniformly smoothing. -/
theorem IsUniform.isUniformlySmoothing_of_coefficient_eq_zero {a : Symbol n V W m}
    (ha : a.IsUniform) (R : ℝ) (h : ∀ x ξ, R ≤ ‖ξ‖ → a.coefficient (x, ξ) = 0) :
    a.IsUniformlySmoothing := fun m' => by
  refine ⟨ofBoundedFrequencySupport a.coefficient a.contDiff_coefficient R h,
    isUniform_iff.2 fun α β => ?_,
    coefficient_ofBoundedFrequencySupport _ _ _ _⟩
  obtain ⟨C, hC0, hC⟩ := isUniform_iff.1 ha α β
  refine ⟨C * (1 + R ^ 2) ^ (|m - m'| / 2), by positivity, fun x ξ => ?_⟩
  rw [coefficient_ofBoundedFrequencySupport]
  rcases le_or_gt ‖ξ‖ R with hξ | hξ
  · -- For `‖ξ‖ ≤ R`, `⟨ξ⟩^(m - |β|) = ⟨ξ⟩^(m - m') ⟨ξ⟩^(m' - |β|)` and
    -- `⟨ξ⟩^(m - m') ≤ ⟨R⟩^|m - m'|`.
    have hw : 0 < 1 + ‖ξ‖ ^ 2 := by positivity
    have hR : (1 + ‖ξ‖ ^ 2) ^ ((m - m') / 2) ≤ (1 + R ^ 2) ^ (|m - m'| / 2) :=
      (Real.rpow_le_rpow_of_exponent_le (by nlinarith [sq_nonneg ‖ξ‖])
        (by linarith [le_abs_self (m - m')])).trans
        (Real.rpow_le_rpow hw.le (by nlinarith [norm_nonneg ξ]) (by positivity))
    refine (hC x ξ).trans ?_
    rw [show (m - β.length) / 2 = (m - m') / 2 + (m' - β.length) / 2 by ring, Real.rpow_add hw,
      mul_assoc C]
    gcongr
  · -- Beyond radius `R` the coefficient vanishes on a neighbourhood, with all its derivatives.
    have hzero : a.coefficient =ᶠ[nhds (x, ξ)] 0 :=
      Filter.eventually_of_mem ((isOpen_lt continuous_const continuous_snd.norm).mem_nhds hξ)
        fun p hp => h p.1 p.2 hp.le
    rw [hzero.mixedDeriv_eq, mixedDeriv_zero, norm_zero]
    positivity

end Symbol

end TauCeti
