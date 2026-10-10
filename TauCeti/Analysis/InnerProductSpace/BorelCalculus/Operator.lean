/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.BorelCalculus.Polarization
public import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# The bounded Borel functional calculus of a normal operator

For a bounded measurable symbol `f` on `spectrum ℂ a` the polarised diagonal
integral `pair ha f` is sesquilinear and bounded, hence is the matrix-element
form of a unique bounded operator `borelCalculus ha hf : H →L[ℂ] H`:

`⟪ψ, borelCalculus ha hf ξ⟫ = pair ha f ψ ξ`.

Every step is transported from the continuous functional calculus by
`exists_continuous_pair_close`: an identity involving finitely many vectors is
checked for a continuous symbol (where it is an identity about `cfcHom`, so
free) and then the symbol is moved by `ε` in the `L¹` of the finite sum of the
diagonal measures occurring in it.

## Provenance

*New*; see `ForTauCeti/Analysis/InnerProductSpace/BorelCalculus/DiagonalMeasure.lean`.
-/

public section

open scoped InnerProductSpace ENNReal CompactlySupported
open MeasureTheory

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

namespace TauCeti
namespace BorelCalculus

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {a : H →L[ℂ] H}

/-- A symbol admissible for the bounded Borel calculus: measurable and bounded. -/
structure IsBddMeasurable (f : spectrum ℂ a → ℂ) : Prop where
  measurable : Measurable f
  exists_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ x, ‖f x‖ ≤ M

namespace IsBddMeasurable

/-- A nonnegative uniform chooseBound for an admissible symbol. -/
noncomputable def chooseBound {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) : ℝ :=
  hf.exists_bound.choose

omit [CompleteSpace H] in
/-- The chosen bound is nonnegative. -/
theorem chooseBound_nonneg {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) : 0 ≤ hf.chooseBound :=
  hf.exists_bound.choose_spec.1

omit [CompleteSpace H] in
/-- The chosen bound does bound the symbol.  It is *a* bound, not the supremum -- see
`chooseBound`. -/
theorem norm_le_chooseBound {f : spectrum ℂ a → ℂ} (hf : IsBddMeasurable f) (x : spectrum ℂ a) :
    ‖f x‖ ≤ hf.chooseBound :=
  hf.exists_bound.choose_spec.2 x

end IsBddMeasurable

section Elementary

variable (ha : IsStarNormal a)

omit [CompleteSpace H] in
/-- A bounded measurable symbol is integrable against any finite measure on the
spectrum. -/
theorem integrable_of_bounded {f : spectrum ℂ a → ℂ} (hfm : Measurable f) {M : ℝ}
    (hfb : ∀ x, ‖f x‖ ≤ M) (ν : Measure (spectrum ℂ a)) [IsFiniteMeasure ν] :
    Integrable f ν :=
  (integrable_const M).mono' hfm.aestronglyMeasurable
    (Filter.Eventually.of_forall hfb)

/-- **The transport lemma.**  A bounded measurable symbol can be replaced, to
within `ε`, by a continuous one *simultaneously* at any finite family of vector
pairs.  This is the only bridge between the continuous and the Borel calculus,
and every subsequent identity goes through it. -/
theorem exists_continuous_pair_close {ι : Type*} [Finite ι] (P : ι → H × H)
    {f : spectrum ℂ a → ℂ} (hfm : Measurable f) {M : ℝ} (hfb : ∀ x, ‖f x‖ ≤ M)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ g : C(spectrum ℂ a, ℂ), ∀ i,
      ‖pair ha f (P i).1 (P i).2 - ⟪(P i).1, cfcHom ha g (P i).2⟫_ℂ‖ ≤ ε := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  set v : ι × Fin 4 → H := fun p => pairVectors (P p.1).1 (P p.1).2 p.2 with hv
  set ν : Measure (spectrum ℂ a) := ∑ j, diagMeasure ha (v j) with hν
  have : IsFiniteMeasure ν := isFiniteMeasure_sum_diagMeasure ha v
  have hfi : Integrable f ν := integrable_of_bounded hfm hfb ν
  obtain ⟨g, hgi, hgle⟩ := exists_continuous_integral_norm_sub_le ν hfi hε
  refine ⟨g, fun i => ?_⟩
  rw [← pair_of_continuous ha g]
  exact le_trans (norm_pair_sub_pair_le ha ν _ _ (fun k => diagMeasure_le_sum ha v (i, k))
    hfi hgi) hgle

end Elementary

section Squeeze

/-- If `‖x - y‖ ≤ C * ε` for every positive `ε`, then `x = y`. -/
theorem eq_of_forall_norm_sub_le {x y : ℂ} {C : ℝ} (hC : 0 < C)
    (h : ∀ ε : ℝ, 0 < ε → ‖x - y‖ ≤ C * ε) : x = y := by
  have hle : ‖x - y‖ ≤ 0 := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    have hd : C * (δ / C) = δ := by field_simp
    have := h (δ / C) (by positivity)
    rw [hd] at this
    linarith
  have := le_antisymm hle (norm_nonneg _)
  rwa [norm_eq_zero, sub_eq_zero] at this

end Squeeze

section Sesquilinear

variable (ha : IsStarNormal a) {f : spectrum ℂ a → ℂ}

/-- Additivity of the polarised integral in the second slot. -/
theorem pair_add_right (hfm : Measurable f) {M : ℝ} (hfb : ∀ x, ‖f x‖ ≤ M)
    (ψ ξ₁ ξ₂ : H) :
    pair ha f ψ (ξ₁ + ξ₂) = pair ha f ψ ξ₁ + pair ha f ψ ξ₂ := by
  refine eq_of_forall_norm_sub_le (C := 3) (by norm_num) fun ε hε => ?_
  obtain ⟨g, hg⟩ := exists_continuous_pair_close ha
    (P := fun i : Fin 3 => (ψ, ![ξ₁ + ξ₂, ξ₁, ξ₂] i)) hfm hfb hε
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
  have hmid : ⟪ψ, cfcHom ha g (ξ₁ + ξ₂)⟫_ℂ
      = ⟪ψ, cfcHom ha g ξ₁⟫_ℂ + ⟪ψ, cfcHom ha g ξ₂⟫_ℂ := by
    rw [map_add, inner_add_right]
  have key : pair ha f ψ (ξ₁ + ξ₂) - (pair ha f ψ ξ₁ + pair ha f ψ ξ₂)
      = (pair ha f ψ (ξ₁ + ξ₂) - ⟪ψ, cfcHom ha g (ξ₁ + ξ₂)⟫_ℂ)
        - (pair ha f ψ ξ₁ - ⟪ψ, cfcHom ha g ξ₁⟫_ℂ)
        - (pair ha f ψ ξ₂ - ⟪ψ, cfcHom ha g ξ₂⟫_ℂ) := by
    rw [hmid]; ring
  rw [key]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_sub_le _ _) le_rfl) ?_
  linarith

/-- Homogeneity of the polarised integral in the second slot. -/
theorem pair_smul_right (hfm : Measurable f) {M : ℝ} (hfb : ∀ x, ‖f x‖ ≤ M)
    (c : ℂ) (ψ ξ : H) :
    pair ha f ψ (c • ξ) = c * pair ha f ψ ξ := by
  refine eq_of_forall_norm_sub_le (C := 1 + ‖c‖) (by positivity) fun ε hε => ?_
  obtain ⟨g, hg⟩ := exists_continuous_pair_close ha
    (P := fun i : Fin 2 => (ψ, ![c • ξ, ξ] i)) hfm hfb hε
  have h0 := hg 0
  have h1 := hg 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hmid : ⟪ψ, cfcHom ha g (c • ξ)⟫_ℂ = c * ⟪ψ, cfcHom ha g ξ⟫_ℂ := by
    rw [map_smul, inner_smul_right]
  have key : pair ha f ψ (c • ξ) - c * pair ha f ψ ξ
      = (pair ha f ψ (c • ξ) - ⟪ψ, cfcHom ha g (c • ξ)⟫_ℂ)
        - c * (pair ha f ψ ξ - ⟪ψ, cfcHom ha g ξ⟫_ℂ) := by
    rw [hmid]; ring
  rw [key]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul]
  have : ‖c‖ * ‖pair ha f ψ ξ - ⟪ψ, cfcHom ha g ξ⟫_ℂ‖ ≤ ‖c‖ * ε := by
    exact mul_le_mul_of_nonneg_left h1 (norm_nonneg c)
  nlinarith [norm_nonneg c]

/-- Additivity of the polarised integral in the first slot. -/
theorem pair_add_left (hfm : Measurable f) {M : ℝ} (hfb : ∀ x, ‖f x‖ ≤ M)
    (ψ₁ ψ₂ ξ : H) :
    pair ha f (ψ₁ + ψ₂) ξ = pair ha f ψ₁ ξ + pair ha f ψ₂ ξ := by
  refine eq_of_forall_norm_sub_le (C := 3) (by norm_num) fun ε hε => ?_
  obtain ⟨g, hg⟩ := exists_continuous_pair_close ha
    (P := fun i : Fin 3 => (![ψ₁ + ψ₂, ψ₁, ψ₂] i, ξ)) hfm hfb hε
  have h0 := hg 0
  have h1 := hg 1
  have h2 := hg 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons] at h0 h1 h2
  have hmid : ⟪ψ₁ + ψ₂, cfcHom ha g ξ⟫_ℂ
      = ⟪ψ₁, cfcHom ha g ξ⟫_ℂ + ⟪ψ₂, cfcHom ha g ξ⟫_ℂ := inner_add_left _ _ _
  have key : pair ha f (ψ₁ + ψ₂) ξ - (pair ha f ψ₁ ξ + pair ha f ψ₂ ξ)
      = (pair ha f (ψ₁ + ψ₂) ξ - ⟪ψ₁ + ψ₂, cfcHom ha g ξ⟫_ℂ)
        - (pair ha f ψ₁ ξ - ⟪ψ₁, cfcHom ha g ξ⟫_ℂ)
        - (pair ha f ψ₂ ξ - ⟪ψ₂, cfcHom ha g ξ⟫_ℂ) := by
    rw [hmid]; ring
  rw [key]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (norm_sub_le _ _) le_rfl) ?_
  linarith

/-- Conjugate-homogeneity of the polarised integral in the first slot. -/
theorem pair_smul_left (hfm : Measurable f) {M : ℝ} (hfb : ∀ x, ‖f x‖ ≤ M)
    (c : ℂ) (ψ ξ : H) :
    pair ha f (c • ψ) ξ = (starRingEnd ℂ) c * pair ha f ψ ξ := by
  refine eq_of_forall_norm_sub_le (C := 1 + ‖c‖) (by positivity) fun ε hε => ?_
  obtain ⟨g, hg⟩ := exists_continuous_pair_close ha
    (P := fun i : Fin 2 => (![c • ψ, ψ] i, ξ)) hfm hfb hε
  have h0 := hg 0
  have h1 := hg 1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  have hmid : ⟪c • ψ, cfcHom ha g ξ⟫_ℂ = (starRingEnd ℂ) c * ⟪ψ, cfcHom ha g ξ⟫_ℂ :=
    inner_smul_left _ _ _
  have key : pair ha f (c • ψ) ξ - (starRingEnd ℂ) c * pair ha f ψ ξ
      = (pair ha f (c • ψ) ξ - ⟪c • ψ, cfcHom ha g ξ⟫_ℂ)
        - (starRingEnd ℂ) c * (pair ha f ψ ξ - ⟪ψ, cfcHom ha g ξ⟫_ℂ) := by
    rw [hmid]; ring
  rw [key]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul, RCLike.norm_conj]
  have : ‖c‖ * ‖pair ha f ψ ξ - ⟪ψ, cfcHom ha g ξ⟫_ℂ‖ ≤ ‖c‖ * ε :=
    mul_le_mul_of_nonneg_left h1 (norm_nonneg c)
  nlinarith [norm_nonneg c]

end Sesquilinear

section Bound

variable (ha : IsStarNormal a) {f : spectrum ℂ a → ℂ}

/-- The crude quadratic chooseBound coming straight from the definition: the total
mass of `diagMeasure ha v` is `‖v‖ ^ 2`. -/
theorem norm_pair_le_crude (hfm : Measurable f) {M : ℝ} (hM : 0 ≤ M)
    (hfb : ∀ x, ‖f x‖ ≤ M) (ψ ξ : H) :
    ‖pair ha f ψ ξ‖ ≤ M * (‖ψ‖ ^ 2 + ‖ξ‖ ^ 2) := by
  have key : ∀ v : H, ‖∫ x, f x ∂(diagMeasure ha v)‖ ≤ M * ‖v‖ ^ 2 := by
    intro v
    calc ‖∫ x, f x ∂(diagMeasure ha v)‖ ≤ ∫ x, ‖f x‖ ∂(diagMeasure ha v) :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ _x, M ∂(diagMeasure ha v) :=
          integral_mono ((integrable_of_bounded hfm hfb _).norm) (integrable_const M) hfb
      _ = ‖v‖ ^ 2 * M := by
          rw [integral_const, smul_eq_mul, MeasureTheory.measureReal_def,
            diagMeasure_univ_toReal]
      _ = M * ‖v‖ ^ 2 := by ring
  have hpar1 : ‖ξ + ψ‖ ^ 2 + ‖ξ - ψ‖ ^ 2 = 2 * (‖ξ‖ ^ 2 + ‖ψ‖ ^ 2) := by
    have := parallelogram_law_with_norm ℂ ξ ψ
    simp only [pow_two]
    linarith
  have hI : ‖Complex.I • ψ‖ = ‖ψ‖ := by
    rw [norm_smul, Complex.norm_I, one_mul]
  have hpar2 : ‖ξ + Complex.I • ψ‖ ^ 2 + ‖ξ - Complex.I • ψ‖ ^ 2
      = 2 * (‖ξ‖ ^ 2 + ‖ψ‖ ^ 2) := by
    have := parallelogram_law_with_norm ℂ ξ (Complex.I • ψ)
    simp only [pow_two] at this ⊢
    rw [hI] at this
    linarith
  rw [pair_def, norm_mul]
  have hq : ‖(1 / 4 : ℂ)‖ = 1 / 4 := by norm_num
  rw [hq]
  have hsum : ‖(∫ x, f x ∂(diagMeasure ha (ξ + ψ)))
        + Complex.I * (∫ x, f x ∂(diagMeasure ha (ξ + Complex.I • ψ)))
        - (∫ x, f x ∂(diagMeasure ha (ξ - ψ)))
        - Complex.I * (∫ x, f x ∂(diagMeasure ha (ξ - Complex.I • ψ)))‖
      ≤ M * ‖ξ + ψ‖ ^ 2 + M * ‖ξ + Complex.I • ψ‖ ^ 2
        + M * ‖ξ - ψ‖ ^ 2 + M * ‖ξ - Complex.I • ψ‖ ^ 2 := by
    have e1 : ‖Complex.I * (∫ x, f x ∂(diagMeasure ha (ξ + Complex.I • ψ)))‖
        ≤ M * ‖ξ + Complex.I • ψ‖ ^ 2 := by
      rw [norm_mul, Complex.norm_I, one_mul]; exact key _
    have e3 : ‖Complex.I * (∫ x, f x ∂(diagMeasure ha (ξ - Complex.I • ψ)))‖
        ≤ M * ‖ξ - Complex.I • ψ‖ ^ 2 := by
      rw [norm_mul, Complex.norm_I, one_mul]; exact key _
    refine le_trans (norm_sub_le _ _) ?_
    refine le_trans (add_le_add (norm_sub_le _ _) e3) ?_
    refine le_trans (add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl) ?_
    have := key (ξ + ψ)
    have := key (ξ - ψ)
    linarith
  have hgoal : M * ‖ξ + ψ‖ ^ 2 + M * ‖ξ + Complex.I • ψ‖ ^ 2
      + M * ‖ξ - ψ‖ ^ 2 + M * ‖ξ - Complex.I • ψ‖ ^ 2
      = 4 * (M * (‖ψ‖ ^ 2 + ‖ξ‖ ^ 2)) := by nlinarith [hpar1, hpar2]
  calc 1 / 4 * _ ≤ 1 / 4 * (4 * (M * (‖ψ‖ ^ 2 + ‖ξ‖ ^ 2))) := by
        rw [← hgoal]; gcongr
    _ = M * (‖ψ‖ ^ 2 + ‖ξ‖ ^ 2) := by ring

/-- The product chooseBound, obtained from the crude chooseBound by rescaling `ψ ↦ t • ψ`,
`ξ ↦ t⁻¹ • ξ`, which leaves `pair` invariant. -/
theorem norm_pair_le (hfm : Measurable f) {M : ℝ} (hM : 0 ≤ M)
    (hfb : ∀ x, ‖f x‖ ≤ M) (ψ ξ : H) :
    ‖pair ha f ψ ξ‖ ≤ 2 * M * ‖ψ‖ * ‖ξ‖ := by
  rcases eq_or_ne ψ 0 with rfl | hψ
  · have h := pair_smul_left ha hfm hfb 0 0 ξ
    simp only [zero_smul, map_zero, zero_mul] at h
    simp [h]
  rcases eq_or_ne ξ 0 with rfl | hξ
  · have h := pair_smul_right ha hfm hfb 0 ψ 0
    simp only [zero_smul, zero_mul] at h
    simp [h]
  have hψn : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  have hξn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
  set t : ℝ := Real.sqrt (‖ξ‖ / ‖ψ‖) with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have htsq : t ^ 2 = ‖ξ‖ / ‖ψ‖ := Real.sq_sqrt (by positivity)
  have hinv : pair ha f ((t : ℂ) • ψ) (((t : ℂ)⁻¹) • ξ) = pair ha f ψ ξ := by
    have htne : (t : ℂ) ≠ 0 := by exact_mod_cast htpos.ne'
    rw [pair_smul_right ha hfm hfb, pair_smul_left ha hfm hfb]
    have hcj : (starRingEnd ℂ) (t : ℂ) = (t : ℂ) := Complex.conj_ofReal t
    rw [hcj, ← mul_assoc, inv_mul_cancel₀ htne, one_mul]
  have hcrude := norm_pair_le_crude ha hfm hM hfb ((t : ℂ) • ψ) (((t : ℂ)⁻¹) • ξ)
  rw [hinv] at hcrude
  have hn1 : ‖(t : ℂ) • ψ‖ = t * ‖ψ‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  have hn2 : ‖((t : ℂ)⁻¹) • ξ‖ = t⁻¹ * ‖ξ‖ := by
    rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos htpos]
  rw [hn1, hn2] at hcrude
  have hexp : (t * ‖ψ‖) ^ 2 + (t⁻¹ * ‖ξ‖) ^ 2 = 2 * (‖ψ‖ * ‖ξ‖) := by
    have h1 : (t * ‖ψ‖) ^ 2 = ‖ξ‖ * ‖ψ‖ := by
      rw [mul_pow, htsq]; field_simp
    have h2 : (t⁻¹ * ‖ξ‖) ^ 2 = ‖ψ‖ * ‖ξ‖ := by
      rw [mul_pow, inv_pow, htsq]
      field_simp
    rw [h1, h2]; ring
  rw [hexp] at hcrude
  calc ‖pair ha f ψ ξ‖ ≤ M * (2 * (‖ψ‖ * ‖ξ‖)) := hcrude
    _ = 2 * M * ‖ψ‖ * ‖ξ‖ := by ring

end Bound

section Construction

variable (ha : IsStarNormal a) {f : spectrum ℂ a → ℂ}

/-- The continuous linear functional `ψ ↦ conj (pair f ψ ξ)`. -/
noncomputable def pairFunctional (hf : IsBddMeasurable f) (ξ : H) : H →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun ψ => (starRingEnd ℂ) (pair ha f ψ ξ)
      map_add' := fun ψ₁ ψ₂ => by
        rw [pair_add_left ha hf.measurable hf.norm_le_chooseBound, map_add]
      map_smul' := fun c ψ => by
        rw [pair_smul_left ha hf.measurable hf.norm_le_chooseBound, map_mul, Complex.conj_conj,
          RingHom.id_apply, smul_eq_mul] }
    (2 * hf.chooseBound * ‖ξ‖)
    (fun ψ => by
      simp only [LinearMap.coe_mk, AddHom.coe_mk, RCLike.norm_conj]
      calc ‖pair ha f ψ ξ‖ ≤ 2 * hf.chooseBound * ‖ψ‖ * ‖ξ‖ :=
            norm_pair_le ha hf.measurable hf.chooseBound_nonneg hf.norm_le_chooseBound ψ ξ
        _ = 2 * hf.chooseBound * ‖ξ‖ * ‖ψ‖ := by ring)

/-- The polarised functional, unfolded. -/
@[simp] theorem pairFunctional_apply (hf : IsBddMeasurable f) (ξ ψ : H) :
    pairFunctional ha hf ξ ψ = (starRingEnd ℂ) (pair ha f ψ ξ) := (rfl)
/-- The polarised functional is bounded by `‖f‖ ‖x‖ ‖y‖`, which is what makes it the matrix-element
form of a bounded operator. -/
theorem norm_pairFunctional_le (hf : IsBddMeasurable f) (ξ : H) :
    ‖pairFunctional ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖ :=
  LinearMap.mkContinuous_norm_le _
    (by have := hf.chooseBound_nonneg; positivity) _

/-- The vector representing the functional `ψ ↦ conj (pair f ψ ξ)`. -/
noncomputable def borelVector (hf : IsBddMeasurable f) (ξ : H) : H :=
  (InnerProductSpace.toDual ℂ H).symm (pairFunctional ha hf ξ)

/-- The defining property of the Riesz vector: its inner products reproduce the functional. -/
theorem inner_borelVector (hf : IsBddMeasurable f) (ψ ξ : H) :
    ⟪ψ, borelVector ha hf ξ⟫_ℂ = pair ha f ψ ξ := by
  have h : ⟪borelVector ha hf ξ, ψ⟫_ℂ = (starRingEnd ℂ) (pair ha f ψ ξ) := by
    rw [borelVector, InnerProductSpace.toDual_symm_apply, pairFunctional_apply]
  rw [← inner_conj_symm, h, Complex.conj_conj]

/-- Norm bound on the Riesz vector, inherited from the functional's bound. -/
theorem norm_borelVector_le (hf : IsBddMeasurable f) (ξ : H) :
    ‖borelVector ha hf ξ‖ ≤ 2 * hf.chooseBound * ‖ξ‖ := by
  rw [borelVector, LinearIsometryEquiv.norm_map]
  exact norm_pairFunctional_le ha hf ξ

/-- **The bounded Borel functional calculus.**  The unique bounded operator
whose matrix elements are the polarised diagonal integrals of `f`. -/
noncomputable def borelCalculus (hf : IsBddMeasurable f) : H →L[ℂ] H :=
  LinearMap.mkContinuous
    { toFun := borelVector ha hf
      map_add' := fun ξ₁ ξ₂ => by
        refine ext_inner_left ℂ fun ψ => ?_
        rw [inner_add_right, inner_borelVector, inner_borelVector, inner_borelVector,
          pair_add_right ha hf.measurable hf.norm_le_chooseBound]
      map_smul' := fun c ξ => by
        refine ext_inner_left ℂ fun ψ => ?_
        rw [RingHom.id_apply, inner_smul_right, inner_borelVector, inner_borelVector,
          pair_smul_right ha hf.measurable hf.norm_le_chooseBound] }
    (2 * hf.chooseBound)
    (fun ξ => norm_borelVector_le ha hf ξ)

/-- The Borel calculus acts through the Riesz vector of the polarised functional. -/
@[simp] theorem borelCalculus_apply (hf : IsBddMeasurable f) (ξ : H) :
    borelCalculus ha hf ξ = borelVector ha hf ξ := (rfl)
/-- **The defining property of the Borel calculus.** -/
@[simp] theorem inner_borelCalculus (hf : IsBddMeasurable f) (ψ ξ : H) :
    ⟪ψ, borelCalculus ha hf ξ⟫_ℂ = pair ha f ψ ξ :=
  inner_borelVector ha hf ψ ξ

/-- The norm chooseBound for the Borel calculus. -/
theorem norm_borelCalculus_le (hf : IsBddMeasurable f) :
    ‖borelCalculus ha hf‖ ≤ 2 * hf.chooseBound :=
  LinearMap.mkContinuous_norm_le _ (by have := hf.chooseBound_nonneg; positivity) _

end Construction

end BorelCalculus
end TauCeti
