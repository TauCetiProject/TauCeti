/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Analysis.Normed.Operator.Compact.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Analysis.Normed.Operator.Compact.Pi

/-!
# Compact form pairs

A **compact form pair** consists of a form domain `E`, an ambient space `H` over `𝕜` (`ℝ` or `ℂ`),
a continuous linear map `j : E →L[𝕜] H` that is injective, dense-ranged, and compact, and a bounded
Hermitian sesquilinear form `a : E →L⋆[𝕜] E →L[𝕜] 𝕜` satisfying a Gårding-type shifted lower bound

`c ‖u‖² ≤ Re a(u, u) + ω ‖j u‖²`

for some `c > 0` and `ω : ℝ`. The coercivity constant `c` and shift `ω` enter only through
existence (`exists_shifted_lower_bound`), so a pair is uniquely determined by `(j, a)` and
admits extensionality.

The quadratic energy of a pair is `P.energy u = Re a(u, u)`. This file develops the basic
identities of `P.energy` and the standard functorial constructions on compact form pairs:

* `CompactFormPair.shift`: adding a real multiple of the ambient inner product `α ⟪j u, j v⟫_𝕜`.
* `CompactFormPair.mapLinearIsometryEquiv`: transporting the ambient space along a linear
  isometric equivalence.
* `CompactFormPair.comapEquiv`: changing the form domain to an equivalent norm.
* `CompactFormPair.restrict`: restricting to a submodule `V₁ ≤ E` with ambient space
  `(V₁.map j).topologicalClosure`.
* `CompactFormPair.pi`: finite `ℓ²`-direct sum of compact form pairs.
* `CompactFormPair.restrictScalars`: real restriction of a pair over `𝕜` to the underlying real
  spaces via `IsScalarTower ℝ 𝕜`.
* `CompactFormPair.ofFiniteDimensional`: the finite-dimensional pair with `j = id`.

## References

* J. K. Hunter, *Notes on Partial Differential Equations*, Section 4.8.
* V. Ivrii, *Partial Differential Equations*, Section 13.1.
-/

public section

noncomputable section

open scoped InnerProductSpace

namespace TauCeti

/-- A **compact form pair**: a form domain `E`, an ambient space `H` over `𝕜` (`ℝ` or `ℂ`), an
injective, dense-ranged, compact linear map `inclusion : E →L[𝕜] H`, and a bounded Hermitian
sesquilinear form `form : E →L⋆[𝕜] E →L[𝕜] 𝕜` admitting a shifted lower bound
`c ‖u‖² ≤ Re (form u u) + ω ‖inclusion u‖²` with `c > 0`.

The coercivity constant `c` and shift `ω` are existentially quantified rather than stored as data,
so equality of pairs reduces to equality of `(inclusion, form)`. -/
@[ext]
structure CompactFormPair (𝕜 E H : Type*) [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SeminormedAddCommGroup H] [NormedSpace 𝕜 H] where
  /-- The compact, dense, injective inclusion `j : E → H`. -/
  inclusion : E →L[𝕜] H
  injective : Function.Injective inclusion
  dense : DenseRange inclusion
  compact : IsCompactOperator inclusion
  /-- The bounded Hermitian sesquilinear form `a`, conjugate-linear in the first variable and
  linear in the second. -/
  form : E →L⋆[𝕜] E →L[𝕜] 𝕜
  hermitian : ∀ u v : E, form u v = star (form v u)
  /-- Existence of a coercivity constant `c > 0` and shift `ω : ℝ` satisfying the Gårding-type
  lower bound `c ‖u‖² ≤ Re (form u u) + ω ‖inclusion u‖²`. -/
  exists_shifted_lower_bound :
    ∃ c ω : ℝ, 0 < c ∧ ∀ u : E, c * ‖u‖ ^ 2 ≤ RCLike.re (form u u) + ω * ‖inclusion u‖ ^ 2

namespace CompactFormPair

section Energy

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- The real quadratic energy `q(u) = Re (form u u)` associated with a compact form pair. -/
def energy (P : CompactFormPair 𝕜 E H) (u : E) : ℝ :=
  RCLike.re (P.form u u)

/-- Unfolding lemma for `CompactFormPair.energy`. -/
theorem energy_def (P : CompactFormPair 𝕜 E H) (u : E) :
    P.energy u = RCLike.re (P.form u u) :=
  (rfl)

/-- The diagonal value `P.form u u` is real and equals `P.energy u`. -/
theorem form_self_eq_ofReal_energy (P : CompactFormPair 𝕜 E H) (u : E) :
    P.form u u = (P.energy u : 𝕜) := by
  rw [energy_def]
  exact (RCLike.conj_eq_iff_re.mp (by rw [← RCLike.star_def, ← P.hermitian u u])).symm

/-- The real part of the form is symmetric. -/
theorem re_form_symm (P : CompactFormPair 𝕜 E H) (u v : E) :
    RCLike.re (P.form u v) = RCLike.re (P.form v u) := by
  rw [P.hermitian u v, RCLike.star_def, RCLike.conj_re]

/-- Increasing the shift preserves a shifted lower bound with the same coercivity constant. -/
theorem shifted_lower_bound_mono (P : CompactFormPair 𝕜 E H) {c ω ω' : ℝ} (hω : ω ≤ ω')
    (hbound : ∀ u : E, c * ‖u‖ ^ 2 ≤ P.energy u + ω * ‖P.inclusion u‖ ^ 2) (u : E) :
    c * ‖u‖ ^ 2 ≤ P.energy u + ω' * ‖P.inclusion u‖ ^ 2 := by
  have h1 : ω * ‖P.inclusion u‖ ^ 2 ≤ ω' * ‖P.inclusion u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hω (sq_nonneg _)
  linarith [hbound u]

@[simp]
theorem energy_zero (P : CompactFormPair 𝕜 E H) : P.energy 0 = 0 := by
  simp [energy_def]

@[simp]
theorem energy_neg (P : CompactFormPair 𝕜 E H) (u : E) : P.energy (-u) = P.energy u := by
  simp [energy_def]

@[simp]
theorem energy_smul (P : CompactFormPair 𝕜 E H) (c : 𝕜) (u : E) :
    P.energy (c • u) = ‖c‖ ^ 2 * P.energy u := by
  have h : P.form (c • u) (c • u) = (starRingEnd 𝕜 c * c) * P.form u u := by
    rw [map_smul, map_smulₛₗ, smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  rw [energy_def, h, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.re_ofReal_mul, ← energy_def]

/-- Expansion of the quadratic energy on a sum `u + v`. -/
theorem energy_add (P : CompactFormPair 𝕜 E H) (u v : E) :
    P.energy (u + v) = P.energy u + 2 * RCLike.re (P.form u v) + P.energy v := by
  simp only [energy_def, map_add, add_apply, P.re_form_symm v u]
  ring

/-- Expansion of the quadratic energy on a difference `u - v`. -/
theorem energy_sub (P : CompactFormPair 𝕜 E H) (u v : E) :
    P.energy (u - v) = P.energy u - 2 * RCLike.re (P.form u v) + P.energy v := by
  simpa [sub_eq_add_neg, map_neg, energy_neg] using P.energy_add u (-v)

/-- Increment formula `q(u) - q(v) = q(u - v) + 2 Re a(v, u - v)`. -/
theorem energy_sub_energy (P : CompactFormPair 𝕜 E H) (u v : E) :
    P.energy u - P.energy v = P.energy (u - v) + 2 * RCLike.re (P.form v (u - v)) := by
  have h := P.energy_add v (u - v)
  rw [add_sub_cancel] at h
  linarith

/-- Quadratic expansion along a real line `u + t • v`. -/
theorem energy_add_real_smul (P : CompactFormPair 𝕜 E H) (u v : E) (t : ℝ) :
    P.energy (u + (t : 𝕜) • v) =
      P.energy u + 2 * t * RCLike.re (P.form u v) + t ^ 2 * P.energy v := by
  rw [P.energy_add, P.energy_smul, map_smul, smul_eq_mul, RCLike.re_ofReal_mul, RCLike.norm_ofReal,
    sq_abs]
  ring

private theorem abs_re_form_self_le {𝕜 E : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
    (a : E →L⋆[𝕜] E →L[𝕜] 𝕜) (u : E) :
    |RCLike.re (a u u)| ≤ ‖a‖ * ‖u‖ ^ 2 := by
  calc |RCLike.re (a u u)| ≤ ‖a u u‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖a‖ * ‖u‖ * ‖u‖ := a.le_opNorm₂ u u
    _ = ‖a‖ * ‖u‖ ^ 2 := by rw [mul_assoc, ← sq]

/-- The quadratic energy is bounded by `‖P.form‖ ‖u‖²`. -/
theorem abs_energy_le (P : CompactFormPair 𝕜 E H) (u : E) :
    |P.energy u| ≤ ‖P.form‖ * ‖u‖ ^ 2 :=
  abs_re_form_self_le P.form u

/-- The quadratic energy is norm-continuous on `E`. -/
theorem continuous_energy (P : CompactFormPair 𝕜 E H) : Continuous P.energy :=
  RCLike.continuous_re.comp (P.form.continuous.clm_apply continuous_id)

end Energy

section Shift

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup H] [InnerProductSpace 𝕜 H]

private def shiftForm (P : CompactFormPair 𝕜 E H) (α : ℝ) : E →L⋆[𝕜] E →L[𝕜] 𝕜 :=
  P.form + (α : 𝕜) • (innerSL 𝕜).bilinearComp P.inclusion P.inclusion

/-- Shift a compact form pair by a real multiple `α` of the ambient inner product:
`a_α(u, v) = a(u, v) + α ⟪j u, j v⟫_𝕜`. -/
def shift (P : CompactFormPair 𝕜 E H) (α : ℝ) : CompactFormPair 𝕜 E H where
  inclusion := P.inclusion
  injective := P.injective
  dense := P.dense
  compact := P.compact
  form := shiftForm P α
  hermitian u v := by
    change P.form u v + (α : 𝕜) * ⟪P.inclusion u, P.inclusion v⟫_𝕜 =
      star (P.form v u + (α : 𝕜) * ⟪P.inclusion v, P.inclusion u⟫_𝕜)
    simp only [star_add, star_mul', RCLike.star_def, RCLike.conj_ofReal,
      inner_conj_symm, P.hermitian u v]
  exists_shifted_lower_bound := by
    obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
    refine ⟨c, ω - α, hc, fun u => ?_⟩
    have hu := hbound u
    rw [← energy_def] at hu
    change c * ‖u‖ ^ 2 ≤ RCLike.re (P.form u u + (α : 𝕜) * ⟪P.inclusion u, P.inclusion u⟫_𝕜) +
      (ω - α) * ‖P.inclusion u‖ ^ 2
    rw [map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq, ← energy_def]
    linarith

@[simp]
theorem shift_inclusion (P : CompactFormPair 𝕜 E H) (α : ℝ) :
    (P.shift α).inclusion = P.inclusion :=
  (rfl)

@[simp]
theorem shift_form_apply (P : CompactFormPair 𝕜 E H) (α : ℝ) (u v : E) :
    (P.shift α).form u v = P.form u v + (α : 𝕜) * ⟪P.inclusion u, P.inclusion v⟫_𝕜 :=
  (rfl)

@[simp]
theorem shift_energy (P : CompactFormPair 𝕜 E H) (α : ℝ) (u : E) :
    (P.shift α).energy u = P.energy u + α * ‖P.inclusion u‖ ^ 2 := by
  rw [energy_def, shift_form_apply, map_add, RCLike.re_ofReal_mul, inner_self_eq_norm_sq,
    ← energy_def]

@[simp]
theorem shift_zero (P : CompactFormPair 𝕜 E H) : P.shift 0 = P := by
  ext u v <;> simp

@[simp]
theorem shift_shift (P : CompactFormPair 𝕜 E H) (α β : ℝ) :
    (P.shift α).shift β = P.shift (α + β) := by
  ext u v
  · simp
  · simp only [shift_form_apply, shift_inclusion, RCLike.ofReal_add]
    ring

/-- Every compact form pair becomes strictly coercive after a sufficiently large real shift. -/
theorem exists_shift_coercive (P : CompactFormPair 𝕜 E H) :
    ∃ ω₀ : ℝ, ∀ α : ℝ, ω₀ ≤ α → ∃ c : ℝ, 0 < c ∧ ∀ u : E, c * ‖u‖ ^ 2 ≤ (P.shift α).energy u := by
  obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
  refine ⟨ω, fun α hα => ⟨c, hc, fun u => ?_⟩⟩
  rw [shift_energy]
  exact P.shifted_lower_bound_mono hα hbound u

/-- Over `ℝ`, shifting a compact form pair by any `α` above its lower-bound shift yields a
Mathlib-coercive bilinear form. -/
theorem exists_shift_isCoercive {E H : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    [SeminormedAddCommGroup H] [InnerProductSpace ℝ H] (P : CompactFormPair ℝ E H) :
    ∃ ω₀ : ℝ, ∀ α : ℝ, ω₀ ≤ α → IsCoercive (P.shift α).form := by
  obtain ⟨ω₀, hω₀⟩ := P.exists_shift_coercive
  refine ⟨ω₀, fun α hα => ?_⟩
  obtain ⟨c, hc, hbound⟩ := hω₀ α hα
  refine ⟨c, hc, fun u => ?_⟩
  have hu := hbound u
  rw [energy_def] at hu
  simpa only [RCLike.re_to_real, sq, mul_assoc] using hu

end Shift

section Transport

variable {𝕜 E E' E'' H H' H'' : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup E'] [NormedSpace 𝕜 E']
  [SeminormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]
  [SeminormedAddCommGroup H'] [NormedSpace 𝕜 H']
  [SeminormedAddCommGroup H''] [NormedSpace 𝕜 H'']

/-- Transport the ambient space of a compact form pair along a linear isometric equivalence
`U : H ≃ₗᵢ[𝕜] H'`. -/
def mapLinearIsometryEquiv (P : CompactFormPair 𝕜 E H) (U : H ≃ₗᵢ[𝕜] H') :
    CompactFormPair 𝕜 E H' where
  inclusion := U.toContinuousLinearEquiv.toContinuousLinearMap.comp P.inclusion
  injective := U.injective.comp P.injective
  dense := U.surjective.denseRange.comp P.dense U.continuous
  compact := P.compact.clm_comp U.toContinuousLinearEquiv.toContinuousLinearMap
  form := P.form
  hermitian := P.hermitian
  exists_shifted_lower_bound := by
    obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
    exact ⟨c, ω, hc, fun u => by simpa [U.norm_map] using hbound u⟩

@[simp]
theorem mapLinearIsometryEquiv_inclusion_apply (P : CompactFormPair 𝕜 E H) (U : H ≃ₗᵢ[𝕜] H')
    (u : E) : (P.mapLinearIsometryEquiv U).inclusion u = U (P.inclusion u) :=
  (rfl)

@[simp]
theorem mapLinearIsometryEquiv_form (P : CompactFormPair 𝕜 E H) (U : H ≃ₗᵢ[𝕜] H') :
    (P.mapLinearIsometryEquiv U).form = P.form :=
  (rfl)

@[simp]
theorem mapLinearIsometryEquiv_energy (P : CompactFormPair 𝕜 E H) (U : H ≃ₗᵢ[𝕜] H') (u : E) :
    (P.mapLinearIsometryEquiv U).energy u = P.energy u :=
  (rfl)

@[simp]
theorem mapLinearIsometryEquiv_refl (P : CompactFormPair 𝕜 E H) :
    P.mapLinearIsometryEquiv (LinearIsometryEquiv.refl 𝕜 H) = P := by
  ext u <;> simp

theorem mapLinearIsometryEquiv_trans (P : CompactFormPair 𝕜 E H)
    (U : H ≃ₗᵢ[𝕜] H') (V : H' ≃ₗᵢ[𝕜] H'') :
    (P.mapLinearIsometryEquiv U).mapLinearIsometryEquiv V =
      P.mapLinearIsometryEquiv (U.trans V) := by
  ext u <;> simp

/-- Pull back a compact form pair along a continuous linear equivalence `e : E' ≃L[𝕜] E`
(change to an equivalent norm on the form domain). -/
def comapEquiv (P : CompactFormPair 𝕜 E H) (e : E' ≃L[𝕜] E) :
    CompactFormPair 𝕜 E' H where
  inclusion := P.inclusion.comp e.toContinuousLinearMap
  injective := P.injective.comp e.injective
  dense := P.dense.comp e.surjective.denseRange P.inclusion.continuous
  compact := P.compact.comp_clm e.toContinuousLinearMap
  form := P.form.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap
  hermitian u v := by
    simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
      P.hermitian (e u) (e v)]
  exists_shifted_lower_bound := by
    obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
    set M : ℝ := ‖(e.symm : E →L[𝕜] E')‖ + 1
    have hMpos : 0 < M := by positivity
    refine ⟨c / M ^ 2, ω, by positivity, fun u => ?_⟩
    have hu : ‖u‖ ≤ M * ‖e u‖ := by
      calc ‖u‖ = ‖(e.symm : E →L[𝕜] E') (e u)‖ := by simp
        _ ≤ ‖(e.symm : E →L[𝕜] E')‖ * ‖e u‖ := (e.symm : E →L[𝕜] E').le_opNorm (e u)
        _ ≤ M * ‖e u‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    have hsq : ‖u‖ ^ 2 ≤ M ^ 2 * ‖e u‖ ^ 2 := by
      have hsq' := pow_le_pow_left₀ (norm_nonneg u) hu 2
      simpa [mul_pow] using hsq'
    have hle : c / M ^ 2 * ‖u‖ ^ 2 ≤ c * ‖e u‖ ^ 2 := by
      calc c / M ^ 2 * ‖u‖ ^ 2 ≤ c / M ^ 2 * (M ^ 2 * ‖e u‖ ^ 2) :=
            mul_le_mul_of_nonneg_left hsq (by positivity)
        _ = c * ‖e u‖ ^ 2 := by field_simp
    simpa only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearEquiv.coe_coe] using hle.trans (hbound (e u))

@[simp]
theorem comapEquiv_inclusion_apply (P : CompactFormPair 𝕜 E H) (e : E' ≃L[𝕜] E) (u : E') :
    (P.comapEquiv e).inclusion u = P.inclusion (e u) :=
  (rfl)

@[simp]
theorem comapEquiv_form_apply (P : CompactFormPair 𝕜 E H) (e : E' ≃L[𝕜] E) (u v : E') :
    (P.comapEquiv e).form u v = P.form (e u) (e v) :=
  (rfl)

@[simp]
theorem comapEquiv_energy (P : CompactFormPair 𝕜 E H) (e : E' ≃L[𝕜] E) (u : E') :
    (P.comapEquiv e).energy u = P.energy (e u) :=
  (rfl)

@[simp]
theorem comapEquiv_refl (P : CompactFormPair 𝕜 E H) :
    P.comapEquiv (ContinuousLinearEquiv.refl 𝕜 E) = P := by
  ext u v <;> simp

theorem comapEquiv_trans (P : CompactFormPair 𝕜 E H)
    (e₁ : E'' ≃L[𝕜] E') (e₂ : E' ≃L[𝕜] E) :
    (P.comapEquiv e₂).comapEquiv e₁ = P.comapEquiv (e₁.trans e₂) := by
  ext u v <;> simp

end Transport

section Restrict

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H]

/-- Restrict a compact form pair to a submodule `V₁ ≤ E`, replacing the ambient space with the
norm closure `(V₁.map P.inclusion.toLinearMap).topologicalClosure` so that density is preserved. -/
def restrict (P : CompactFormPair 𝕜 E H) (V₁ : Submodule 𝕜 E) :
    CompactFormPair 𝕜 V₁ (V₁.map P.inclusion.toLinearMap).topologicalClosure :=
  let hmem : ∀ x ∈ V₁, P.inclusion x ∈ (V₁.map P.inclusion.toLinearMap).topologicalClosure :=
    fun x hx => Submodule.le_topologicalClosure _ ⟨x, hx, rfl⟩
  { inclusion := P.inclusion.restrict hmem
    injective := fun u v huv => by
      have huv' := congrArg Subtype.val huv
      rw [ContinuousLinearMap.coe_restrict_apply, ContinuousLinearMap.coe_restrict_apply] at huv'
      exact Subtype.ext (P.injective huv')
    dense := by
      rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
      refine subset_trans (le_of_eq (Submodule.topologicalClosure_coe _)) (closure_mono ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, ContinuousLinearMap.coe_restrict_apply hmem ⟨x, hx⟩⟩
    compact :=
      (P.compact.comp_clm V₁.subtypeL).codRestrict
        (V := (V₁.map P.inclusion.toLinearMap).topologicalClosure)
        (fun u => hmem u.1 u.2)
        (V₁.map P.inclusion.toLinearMap).isClosed_topologicalClosure
    form := P.form.bilinearComp V₁.subtypeL V₁.subtypeL
    hermitian := fun u v => by
      simp only [ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply,
        P.hermitian u.1 v.1]
    exists_shifted_lower_bound := by
      obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
      refine ⟨c, ω, hc, fun u => ?_⟩
      rw [ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply,
        ← Submodule.norm_coe u, ← Submodule.norm_coe ((P.inclusion.restrict hmem) u),
        ContinuousLinearMap.coe_restrict_apply]
      exact hbound u.1 }

@[simp]
theorem restrict_inclusion_coe (P : CompactFormPair 𝕜 E H) (V₁ : Submodule 𝕜 E) (u : V₁) :
    ((P.restrict V₁).inclusion u : H) = P.inclusion u := by
  dsimp only [restrict]
  exact ContinuousLinearMap.coe_restrict_apply _ u

@[simp]
theorem restrict_form_apply (P : CompactFormPair 𝕜 E H) (V₁ : Submodule 𝕜 E) (u v : V₁) :
    (P.restrict V₁).form u v = P.form u v :=
  (rfl)

@[simp]
theorem restrict_energy (P : CompactFormPair 𝕜 E H) (V₁ : Submodule 𝕜 E) (u : V₁) :
    (P.restrict V₁).energy u = P.energy u :=
  (rfl)

end Restrict

section Pi

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
  {E H : ι → Type*}
  [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)]
  [∀ i, SeminormedAddCommGroup (H i)] [∀ i, NormedSpace 𝕜 (H i)]

-- Note: `PiLp.proj` requires `NormedAddCommGroup (E i)`, whereas here `E i` is only
-- `SeminormedAddCommGroup`.
private def piProj (𝕜 : Type*) [RCLike 𝕜] {ι : Type*} (E : ι → Type*)
    [∀ i, SeminormedAddCommGroup (E i)] [∀ i, NormedSpace 𝕜 (E i)] (i : ι) :
    PiLp 2 E →L[𝕜] E i :=
  (ContinuousLinearMap.proj (R := 𝕜) i).comp
    (PiLp.continuousLinearEquiv 2 𝕜 E).toContinuousLinearMap

private def piInclusion (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) :
    PiLp 2 E →L[𝕜] PiLp 2 H :=
  (PiLp.continuousLinearEquiv 2 𝕜 H).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piMap fun i => (P i).inclusion).comp
      (PiLp.continuousLinearEquiv 2 𝕜 E).toContinuousLinearMap)

omit [Fintype ι] in
private theorem coe_piInclusion (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) :
    (piInclusion P : PiLp 2 E → PiLp 2 H) =
      (PiLp.continuousLinearEquiv 2 𝕜 H).symm ∘
        (Pi.map fun i => (P i).inclusion) ∘
        (PiLp.continuousLinearEquiv 2 𝕜 E) := by
  rw [piInclusion, ContinuousLinearMap.coe_comp, ContinuousLinearMap.coe_comp,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.coe_piMap']

private def piForm (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) :
    PiLp 2 E →L⋆[𝕜] PiLp 2 E →L[𝕜] 𝕜 :=
  ∑ i : ι, (P i).form.bilinearComp (piProj 𝕜 E i) (piProj 𝕜 E i)

/-- Finite `ℓ²`-direct sum of compact form pairs. -/
def pi (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) :
    CompactFormPair 𝕜 (PiLp 2 E) (PiLp 2 H) where
  inclusion := piInclusion P
  injective := by
    rw [coe_piInclusion]
    exact (PiLp.continuousLinearEquiv 2 𝕜 H).symm.injective.comp
      ((Function.Injective.piMap fun i => (P i).injective).comp
        (PiLp.continuousLinearEquiv 2 𝕜 E).injective)
  dense := by
    rw [coe_piInclusion]
    exact (PiLp.continuousLinearEquiv 2 𝕜 H).symm.surjective.denseRange.comp
      ((DenseRange.piMap fun i => (P i).dense).comp
        (PiLp.continuousLinearEquiv 2 𝕜 E).surjective.denseRange
        (Continuous.piMap fun i => (P i).inclusion.continuous))
      (PiLp.continuousLinearEquiv 2 𝕜 H).symm.continuous
  compact := by
    have hprod : IsCompactOperator (ContinuousLinearMap.piMap fun i => (P i).inclusion) := by
      have hpi : IsCompactOperator (fun (x : ∀ i, E i) i => (P i).inclusion (x i)) :=
        IsCompactOperator.pi (f := fun i (x : ∀ j, E j) => (P i).inclusion (x i)) fun i =>
          (P i).compact.comp_clm (ContinuousLinearMap.proj (R := 𝕜) i)
      rw [ContinuousLinearMap.coe_piMap']
      exact hpi
    exact (hprod.comp_clm (PiLp.continuousLinearEquiv 2 𝕜 E).toContinuousLinearMap).clm_comp
      (PiLp.continuousLinearEquiv 2 𝕜 H).symm.toContinuousLinearMap
  form := piForm P
  hermitian u v := by
    have hform (x y : PiLp 2 E) : piForm P x y = ∑ i : ι, (P i).form (x i) (y i) := by
      simp only [piForm, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.bilinearComp_apply]
      rfl
    simp only [hform, star_sum, fun i => (P i).hermitian (u i) (v i)]
  exists_shifted_lower_bound := by
    have hinc (u : PiLp 2 E) (i : ι) : piInclusion P u i = (P i).inclusion (u i) := rfl
    have hform (u v : PiLp 2 E) : piForm P u v = ∑ i : ι, (P i).form (u i) (v i) := by
      simp only [piForm, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.bilinearComp_apply]
      rfl
    choose c ω hc hbound using fun i => (P i).exists_shifted_lower_bound
    by_cases hne : (Finset.univ : Finset ι).Nonempty
    · refine ⟨Finset.univ.inf' hne c, Finset.univ.sup' hne ω,
        (Finset.lt_inf'_iff hne).mpr fun i _ => hc i, fun u => ?_⟩
      simp only [PiLp.norm_sq_eq_of_L2, hform, hinc, map_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hc_le : Finset.univ.inf' hne c * ‖u i‖ ^ 2 ≤ c i * ‖u i‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (Finset.inf'_le c (Finset.mem_univ i)) (sq_nonneg _)
      have hω_le : ω i * ‖(P i).inclusion (u i)‖ ^ 2 ≤
          Finset.univ.sup' hne ω * ‖(P i).inclusion (u i)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (Finset.le_sup' ω (Finset.mem_univ i)) (sq_nonneg _)
      linarith [hbound i (u i)]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨1, 0, zero_lt_one, fun u => ?_⟩
      simp [PiLp.norm_sq_eq_of_L2, hform, hne]

@[simp]
theorem pi_inclusion_apply (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) (u : PiLp 2 E) (i : ι) :
    (CompactFormPair.pi P).inclusion u i = (P i).inclusion (u i) :=
  (rfl)

@[simp]
theorem pi_form_apply (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) (u v : PiLp 2 E) :
    (CompactFormPair.pi P).form u v = ∑ i : ι, (P i).form (u i) (v i) := by
  change piForm P u v = _
  simp only [piForm, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.bilinearComp_apply]
  rfl

@[simp]
theorem pi_energy (P : ∀ i, CompactFormPair 𝕜 (E i) (H i)) (u : PiLp 2 E) :
    (CompactFormPair.pi P).energy u = ∑ i : ι, (P i).energy (u i) := by
  simp [energy_def, pi_form_apply, map_sum]

end Pi

section RestrictScalars

variable {𝕜 E H : Type*} [RCLike 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [SeminormedAddCommGroup H] [NormedSpace 𝕜 H] [NormedSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

private def formAsRealLinear (P : CompactFormPair 𝕜 E H) : E →L[ℝ] StrongDual 𝕜 E where
  toFun := P.form
  map_add' := P.form.map_add'
  map_smul' r u := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), map_smulₛₗ, RCLike.conj_ofReal,
      RingHom.id_apply, ← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  cont := P.form.continuous

private def restrictScalarsForm (P : CompactFormPair 𝕜 E H) : E →L⋆[ℝ] E →L[ℝ] ℝ :=
  (StrongDual.extendRCLikeL (𝕜 := 𝕜) (F := E)).symm.toContinuousLinearMap.comp
    (formAsRealLinear P)

/-- View a compact form pair over `𝕜` as a real compact form pair on the same underlying spaces
with real symmetric bilinear form `(u, v) ↦ Re (P.form u v)`. -/
def restrictScalars (P : CompactFormPair 𝕜 E H) : CompactFormPair ℝ E H where
  inclusion := P.inclusion.restrictScalars ℝ
  injective := P.injective
  dense := P.dense
  compact := P.compact
  form := restrictScalarsForm P
  hermitian u v := by
    change RCLike.re (P.form u v) = star (RCLike.re (P.form v u))
    simp only [star_trivial, P.re_form_symm u v]
  exists_shifted_lower_bound := by
    have hform (u : E) : restrictScalarsForm P u u = RCLike.re (P.form u u) := rfl
    obtain ⟨c, ω, hc, hbound⟩ := P.exists_shifted_lower_bound
    exact ⟨c, ω, hc, fun u => by
      simpa only [hform, RCLike.re_to_real,
        ContinuousLinearMap.coe_restrictScalars'] using hbound u⟩

@[simp]
theorem restrictScalars_inclusion (P : CompactFormPair 𝕜 E H) :
    P.restrictScalars.inclusion = P.inclusion.restrictScalars ℝ :=
  (rfl)

@[simp]
theorem restrictScalars_form_apply (P : CompactFormPair 𝕜 E H) (u v : E) :
    P.restrictScalars.form u v = RCLike.re (P.form u v) :=
  (rfl)

@[simp]
theorem restrictScalars_energy (P : CompactFormPair 𝕜 E H) (u : E) :
    P.restrictScalars.energy u = P.energy u :=
  (rfl)

end RestrictScalars

section FiniteDimensional

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] [FiniteDimensional 𝕜 H]

/-- Any bounded Hermitian form on a finite-dimensional normed space `H` forms a compact form pair
with `inclusion = ContinuousLinearMap.id 𝕜 H`. -/
def ofFiniteDimensional (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (ha : ∀ u v : H, a u v = star (a v u)) :
    CompactFormPair 𝕜 H H where
  inclusion := ContinuousLinearMap.id 𝕜 H
  injective := Function.injective_id
  dense := denseRange_id
  compact := by
    have : ProperSpace H := FiniteDimensional.proper_rclike 𝕜 H
    exact isCompactOperator_id
  form := a
  hermitian := ha
  exists_shifted_lower_bound := by
    refine ⟨1, ‖a‖ + 1, zero_lt_one, fun u => ?_⟩
    have hre : -RCLike.re (a u u) ≤ ‖a‖ * ‖u‖ ^ 2 :=
      (neg_le_abs _).trans (abs_re_form_self_le a u)
    simp only [ContinuousLinearMap.id_apply]
    linarith

@[simp]
theorem ofFiniteDimensional_inclusion (a : H →L⋆[𝕜] H →L[𝕜] 𝕜)
    (ha : ∀ u v : H, a u v = star (a v u)) :
    (ofFiniteDimensional a ha).inclusion = ContinuousLinearMap.id 𝕜 H :=
  (rfl)

@[simp]
theorem ofFiniteDimensional_form (a : H →L⋆[𝕜] H →L[𝕜] 𝕜)
    (ha : ∀ u v : H, a u v = star (a v u)) :
    (ofFiniteDimensional a ha).form = a :=
  (rfl)

theorem ofFiniteDimensional_energy (a : H →L⋆[𝕜] H →L[𝕜] 𝕜)
    (ha : ∀ u v : H, a u v = star (a v u)) (u : H) :
    (ofFiniteDimensional a ha).energy u = RCLike.re (a u u) :=
  (rfl)

end FiniteDimensional

end CompactFormPair

end TauCeti
