/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.Normed.Lp.PiLp
public import TauCeti.Analysis.InnerProductSpace.LinearPMap.ClosedForm.Basic
public import TauCeti.Analysis.InnerProductSpace.Variational.CompactFormPair
import Mathlib.Analysis.Normed.Module.RCLike.Extend
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.RCLike.Lemmas
import TauCeti.Analysis.Normed.Operator.Compact.Pi

/-!
# Functorial constructions and quadratic energy identities for compact form pairs

This file complements `TauCeti.Analysis.InnerProductSpace.Variational.CompactFormPair` with
additional algebraic identities for `CompactFormPair.energy` and the standard functorial
constructions on `CompactFormPair`:

* `CompactFormPair.shift`: adding a real multiple of the ambient inner product `α ⟪j u, j v⟫_𝕜`.
* `CompactFormPair.mapLinearIsometryEquiv`: transporting the ambient space along a linear
  isometric equivalence.
* `CompactFormPair.comapEquiv`: changing the form domain to an equivalent norm.
* `CompactFormPair.restrict`: restricting to a submodule `V₁ ≤ V` with ambient space
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

namespace CompactFormPair

section Energy

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- The diagonal value `P.form u u` is real and equals `P.energy u`. -/
theorem form_self_eq_ofReal_energy (P : CompactFormPair 𝕜 V H) (u : V) :
    P.form u u = (P.energy u : 𝕜) := by
  rw [energy_def]
  exact (RCLike.conj_eq_iff_re.mp (by rw [← RCLike.star_def, ← P.hermitian u u])).symm

/-- The real part of the form is symmetric. -/
theorem re_form_symm (P : CompactFormPair 𝕜 V H) (u v : V) :
    RCLike.re (P.form u v) = RCLike.re (P.form v u) := by
  rw [P.hermitian u v, RCLike.star_def, RCLike.conj_re]

/-- Increasing the shift preserves a shifted lower bound with the same coercivity constant. -/
theorem shifted_lower_bound_mono (P : CompactFormPair 𝕜 V H) {c ω ω' : ℝ} (hω : ω ≤ ω')
    (hbound : ∀ u : V, c * ‖u‖ ^ 2 ≤ P.energy u + ω * ‖P.inclusion u‖ ^ 2) (u : V) :
    c * ‖u‖ ^ 2 ≤ P.energy u + ω' * ‖P.inclusion u‖ ^ 2 := by
  have h1 : ω * ‖P.inclusion u‖ ^ 2 ≤ ω' * ‖P.inclusion u‖ ^ 2 :=
    mul_le_mul_of_nonneg_right hω (sq_nonneg _)
  linarith [hbound u]

/-- Expansion of the quadratic energy on a sum `u + v`. -/
theorem energy_add (P : CompactFormPair 𝕜 V H) (u v : V) :
    P.energy (u + v) = P.energy u + 2 * RCLike.re (P.form u v) + P.energy v := by
  simp only [energy_def, map_add, add_apply, P.re_form_symm v u]
  ring

/-- Expansion of the quadratic energy on a difference `u - v`. -/
theorem energy_sub (P : CompactFormPair 𝕜 V H) (u v : V) :
    P.energy (u - v) = P.energy u - 2 * RCLike.re (P.form u v) + P.energy v := by
  simpa [sub_eq_add_neg, map_neg, energy_neg] using P.energy_add u (-v)

/-- Increment formula `q(u) - q(v) = q(u - v) + 2 Re a(v, u - v)`. -/
theorem energy_sub_energy (P : CompactFormPair 𝕜 V H) (u v : V) :
    P.energy u - P.energy v = P.energy (u - v) + 2 * RCLike.re (P.form v (u - v)) := by
  have h := P.energy_add v (u - v)
  rw [add_sub_cancel] at h
  linarith

/-- Quadratic expansion along a real line `u + t • v`. -/
theorem energy_add_real_smul (P : CompactFormPair 𝕜 V H) (u v : V) (t : ℝ) :
    P.energy (u + (t : 𝕜) • v) =
      P.energy u + 2 * t * RCLike.re (P.form u v) + t ^ 2 * P.energy v := by
  rw [P.energy_add, P.energy_smul, map_smul, smul_eq_mul, RCLike.re_ofReal_mul, RCLike.norm_ofReal,
    sq_abs]
  ring

private theorem abs_re_form_self_le {𝕜 V : Type*} [RCLike 𝕜]
    [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]
    (a : V →L⋆[𝕜] V →L[𝕜] 𝕜) (u : V) :
    |RCLike.re (a u u)| ≤ ‖a‖ * ‖u‖ ^ 2 := by
  calc |RCLike.re (a u u)| ≤ ‖a u u‖ := RCLike.abs_re_le_norm _
    _ ≤ ‖a‖ * ‖u‖ * ‖u‖ := a.le_opNorm₂ u u
    _ = ‖a‖ * ‖u‖ ^ 2 := by rw [mul_assoc, ← sq]

/-- The quadratic energy is bounded by `‖P.form‖ ‖u‖²`. -/
theorem abs_energy_le (P : CompactFormPair 𝕜 V H) (u : V) :
    |P.energy u| ≤ ‖P.form‖ * ‖u‖ ^ 2 := by
  rw [energy_def]
  exact abs_re_form_self_le P.form u

end Energy

section Shift

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Shift a compact form pair by a real multiple `α` of the ambient inner product:
`a_α(u, v) = a(u, v) + α ⟪j u, j v⟫_𝕜`. -/
def shift (P : CompactFormPair 𝕜 V H) (α : ℝ) : CompactFormPair 𝕜 V H where
  inclusion := P.inclusion
  injective := P.injective
  denseRange := P.denseRange
  isCompactOperator := P.isCompactOperator
  form := ContinuousLinearMap.shiftedForm P.inclusion P.form α
  hermitian := ContinuousLinearMap.shiftedForm_eq_star P.inclusion P.hermitian α
  exists_shifted_coercive := by
    obtain ⟨c, hc, ω, hbound⟩ := P.exists_shifted_coercive
    refine ⟨c, hc, ω - α, fun u => ?_⟩
    rw [ContinuousLinearMap.re_shiftedForm_self]
    linarith [hbound u]

@[simp]
theorem shift_inclusion (P : CompactFormPair 𝕜 V H) (α : ℝ) :
    (P.shift α).inclusion = P.inclusion :=
  (rfl)

@[simp]
theorem shift_form (P : CompactFormPair 𝕜 V H) (α : ℝ) :
    (P.shift α).form = ContinuousLinearMap.shiftedForm P.inclusion P.form α :=
  (rfl)

theorem shift_form_apply (P : CompactFormPair 𝕜 V H) (α : ℝ) (u v : V) :
    (P.shift α).form u v = P.form u v + (α : 𝕜) * ⟪P.inclusion u, P.inclusion v⟫_𝕜 :=
  ContinuousLinearMap.shiftedForm_apply P.inclusion P.form α u v

@[simp]
theorem shift_energy (P : CompactFormPair 𝕜 V H) (α : ℝ) (u : V) :
    (P.shift α).energy u = P.energy u + α * ‖P.inclusion u‖ ^ 2 := by
  rw [energy_def, energy_def, shift_form]
  exact ContinuousLinearMap.re_shiftedForm_self P.inclusion P.form α u

@[simp]
theorem shift_zero (P : CompactFormPair 𝕜 V H) : P.shift 0 = P := by
  ext <;> simp

@[simp]
theorem shift_shift (P : CompactFormPair 𝕜 V H) (α β : ℝ) :
    (P.shift α).shift β = P.shift (α + β) := by
  ext <;> simp

/-- Every compact form pair becomes strictly coercive after a sufficiently large real shift. -/
theorem exists_shift_coercive (P : CompactFormPair 𝕜 V H) :
    ∃ ω₀ : ℝ, ∀ α : ℝ, ω₀ ≤ α → ∃ c : ℝ, 0 < c ∧ ∀ u : V, c * ‖u‖ ^ 2 ≤ (P.shift α).energy u := by
  obtain ⟨c, hc, ω, hbound⟩ := P.exists_mul_norm_sq_le_energy_add
  refine ⟨ω, fun α hα => ⟨c, hc, fun u => ?_⟩⟩
  rw [shift_energy]
  exact P.shifted_lower_bound_mono hα hbound u

/-- Over `ℝ`, shifting a compact form pair by any `α` above its lower-bound shift yields a
Mathlib-coercive bilinear form. -/
theorem exists_shift_isCoercive {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (P : CompactFormPair ℝ V H) :
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

variable {𝕜 V V' V'' H H' H'' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup V'] [InnerProductSpace 𝕜 V']
  [NormedAddCommGroup V''] [InnerProductSpace 𝕜 V'']
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
  [NormedAddCommGroup H'] [InnerProductSpace 𝕜 H']
  [NormedAddCommGroup H''] [InnerProductSpace 𝕜 H'']

/-- Transport the ambient space of a compact form pair along a linear isometric equivalence
`U : H ≃ₗᵢ[𝕜] H'`. -/
def mapLinearIsometryEquiv (P : CompactFormPair 𝕜 V H) (U : H ≃ₗᵢ[𝕜] H') :
    CompactFormPair 𝕜 V H' where
  inclusion := U.toContinuousLinearEquiv.toContinuousLinearMap.comp P.inclusion
  injective := U.injective.comp P.injective
  denseRange := U.surjective.denseRange.comp P.denseRange U.continuous
  isCompactOperator := P.isCompactOperator.clm_comp U.toContinuousLinearEquiv.toContinuousLinearMap
  form := P.form
  hermitian := P.hermitian
  exists_shifted_coercive := by
    obtain ⟨c, hc, ω, hbound⟩ := P.exists_shifted_coercive
    exact ⟨c, hc, ω, fun u => by simpa using hbound u⟩

@[simp]
theorem mapLinearIsometryEquiv_inclusion_apply (P : CompactFormPair 𝕜 V H) (U : H ≃ₗᵢ[𝕜] H')
    (u : V) : (P.mapLinearIsometryEquiv U).inclusion u = U (P.inclusion u) :=
  (rfl)

@[simp]
theorem mapLinearIsometryEquiv_form (P : CompactFormPair 𝕜 V H) (U : H ≃ₗᵢ[𝕜] H') :
    (P.mapLinearIsometryEquiv U).form = P.form :=
  (rfl)

@[simp]
theorem mapLinearIsometryEquiv_energy (P : CompactFormPair 𝕜 V H) (U : H ≃ₗᵢ[𝕜] H') (u : V) :
    (P.mapLinearIsometryEquiv U).energy u = P.energy u := by
  rw [energy_def, energy_def, mapLinearIsometryEquiv_form]

@[simp]
theorem mapLinearIsometryEquiv_refl (P : CompactFormPair 𝕜 V H) :
    P.mapLinearIsometryEquiv (LinearIsometryEquiv.refl 𝕜 H) = P := by
  ext u <;> simp

theorem mapLinearIsometryEquiv_trans (P : CompactFormPair 𝕜 V H)
    (U : H ≃ₗᵢ[𝕜] H') (W : H' ≃ₗᵢ[𝕜] H'') :
    (P.mapLinearIsometryEquiv U).mapLinearIsometryEquiv W =
      P.mapLinearIsometryEquiv (U.trans W) := by
  ext u <;> simp

/-- Pull back a compact form pair along a continuous linear equivalence `e : V' ≃L[𝕜] V`
(change to an equivalent norm on the form domain). -/
def comapEquiv (P : CompactFormPair 𝕜 V H) (e : V' ≃L[𝕜] V) :
    CompactFormPair 𝕜 V' H where
  inclusion := P.inclusion.comp e.toContinuousLinearMap
  injective := P.injective.comp e.injective
  denseRange := P.denseRange.comp e.surjective.denseRange P.inclusion.continuous
  isCompactOperator := P.isCompactOperator.comp_clm e.toContinuousLinearMap
  form := P.form.bilinearComp e.toContinuousLinearMap e.toContinuousLinearMap
  hermitian u v := by
    simp only [ContinuousLinearMap.bilinearComp_apply, ContinuousLinearEquiv.coe_coe,
      P.hermitian (e u) (e v)]
  exists_shifted_coercive := by
    obtain ⟨c, hc, ω, hbound⟩ := P.exists_shifted_coercive
    set M : ℝ := ‖(e.symm : V →L[𝕜] V')‖ + 1
    have hMpos : 0 < M := by positivity
    refine ⟨c / M ^ 2, by positivity, ω, fun u => ?_⟩
    have hu : ‖u‖ ≤ M * ‖e u‖ := by
      calc ‖u‖ = ‖(e.symm : V →L[𝕜] V') (e u)‖ := by simp
        _ ≤ ‖(e.symm : V →L[𝕜] V')‖ * ‖e u‖ := (e.symm : V →L[𝕜] V').le_opNorm (e u)
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
theorem comapEquiv_inclusion_apply (P : CompactFormPair 𝕜 V H) (e : V' ≃L[𝕜] V) (u : V') :
    (P.comapEquiv e).inclusion u = P.inclusion (e u) :=
  (rfl)

@[simp]
theorem comapEquiv_form_apply (P : CompactFormPair 𝕜 V H) (e : V' ≃L[𝕜] V) (u v : V') :
    (P.comapEquiv e).form u v = P.form (e u) (e v) :=
  (rfl)

@[simp]
theorem comapEquiv_energy (P : CompactFormPair 𝕜 V H) (e : V' ≃L[𝕜] V) (u : V') :
    (P.comapEquiv e).energy u = P.energy (e u) := by
  rw [energy_def, energy_def, comapEquiv_form_apply]

@[simp]
theorem comapEquiv_refl (P : CompactFormPair 𝕜 V H) :
    P.comapEquiv (ContinuousLinearEquiv.refl 𝕜 V) = P := by
  ext u v <;> simp

theorem comapEquiv_trans (P : CompactFormPair 𝕜 V H)
    (e₁ : V'' ≃L[𝕜] V') (e₂ : V' ≃L[𝕜] V) :
    (P.comapEquiv e₂).comapEquiv e₁ = P.comapEquiv (e₁.trans e₂) := by
  ext u v <;> simp

end Transport

section Restrict

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

/-- Restrict a compact form pair to a submodule `V₁ ≤ V`, replacing the ambient space with the
norm closure `(V₁.map P.inclusion.toLinearMap).topologicalClosure` so that density is preserved. -/
def restrict (P : CompactFormPair 𝕜 V H) (V₁ : Submodule 𝕜 V) :
    CompactFormPair 𝕜 V₁ (V₁.map P.inclusion.toLinearMap).topologicalClosure :=
  let hmem : ∀ x ∈ V₁, P.inclusion x ∈ (V₁.map P.inclusion.toLinearMap).topologicalClosure :=
    fun x hx => Submodule.le_topologicalClosure _ ⟨x, hx, rfl⟩
  { inclusion := P.inclusion.restrict hmem
    injective := fun u v huv => by
      have huv' := congrArg Subtype.val huv
      rw [ContinuousLinearMap.coe_restrict_apply, ContinuousLinearMap.coe_restrict_apply] at huv'
      exact Subtype.ext (P.injective huv')
    denseRange := by
      rw [DenseRange, Subtype.dense_iff, ← Set.range_comp]
      refine subset_trans (le_of_eq (Submodule.topologicalClosure_coe _)) (closure_mono ?_)
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, ContinuousLinearMap.coe_restrict_apply hmem ⟨x, hx⟩⟩
    isCompactOperator :=
      (P.isCompactOperator.comp_clm V₁.subtypeL).codRestrict
        (V := (V₁.map P.inclusion.toLinearMap).topologicalClosure)
        (fun u => hmem u.val u.property)
        (V₁.map P.inclusion.toLinearMap).isClosed_topologicalClosure
    form := P.form.bilinearComp V₁.subtypeL V₁.subtypeL
    hermitian := fun u v => by
      simp only [ContinuousLinearMap.bilinearComp_apply, Submodule.subtypeL_apply,
        P.hermitian u.val v.val]
    exists_shifted_coercive := by
      obtain ⟨c, hc, ω, hbound⟩ := P.exists_shifted_coercive
      exact ⟨c, hc, ω, fun u => by
        simpa [ContinuousLinearMap.coe_restrict_apply] using hbound u.val⟩ }

@[simp]
theorem restrict_inclusion_coe (P : CompactFormPair 𝕜 V H) (V₁ : Submodule 𝕜 V) (u : V₁) :
    ((P.restrict V₁).inclusion u : H) = P.inclusion u := by
  dsimp only [restrict]
  exact ContinuousLinearMap.coe_restrict_apply _ u

@[simp]
theorem restrict_form_apply (P : CompactFormPair 𝕜 V H) (V₁ : Submodule 𝕜 V) (u v : V₁) :
    (P.restrict V₁).form u v = P.form u v :=
  (rfl)

@[simp]
theorem restrict_energy (P : CompactFormPair 𝕜 V H) (V₁ : Submodule 𝕜 V) (u : V₁) :
    (P.restrict V₁).energy u = P.energy u := by
  rw [energy_def, energy_def, restrict_form_apply]

end Restrict

section Pi

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι]
  {V H : ι → Type*}
  [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)]
  [∀ i, NormedAddCommGroup (H i)] [∀ i, InnerProductSpace 𝕜 (H i)]

private def piProj (𝕜 : Type*) [RCLike 𝕜] {ι : Type*} (V : ι → Type*)
    [∀ i, NormedAddCommGroup (V i)] [∀ i, InnerProductSpace 𝕜 (V i)] (i : ι) :
    PiLp 2 V →L[𝕜] V i :=
  (ContinuousLinearMap.proj (R := 𝕜) i).comp
    (PiLp.continuousLinearEquiv 2 𝕜 V).toContinuousLinearMap

omit [Fintype ι] in
private theorem piProj_apply (u : PiLp 2 V) (i : ι) :
    piProj 𝕜 V i u = u i := by
  simp [piProj]

private def piInclusion (P : ∀ i, CompactFormPair 𝕜 (V i) (H i)) :
    PiLp 2 V →L[𝕜] PiLp 2 H :=
  (PiLp.continuousLinearEquiv 2 𝕜 H).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.piMap fun i => (P i).inclusion).comp
      (PiLp.continuousLinearEquiv 2 𝕜 V).toContinuousLinearMap)

omit [Fintype ι] in
private theorem coe_piInclusion (P : ∀ i, CompactFormPair 𝕜 (V i) (H i)) :
    (piInclusion P : PiLp 2 V → PiLp 2 H) =
      (PiLp.continuousLinearEquiv 2 𝕜 H).symm ∘
        (Pi.map fun i => (P i).inclusion) ∘
        (PiLp.continuousLinearEquiv 2 𝕜 V) := by
  funext u
  simp [piInclusion]

omit [Fintype ι] in
private theorem piInclusion_apply (P : ∀ i, CompactFormPair 𝕜 (V i) (H i))
    (u : PiLp 2 V) (i : ι) :
    piInclusion P u i = (P i).inclusion (u i) := by
  simp [piInclusion]

private def piForm (P : ∀ i, CompactFormPair 𝕜 (V i) (H i)) :
    PiLp 2 V →L⋆[𝕜] PiLp 2 V →L[𝕜] 𝕜 :=
  ∑ i : ι, (P i).form.bilinearComp (piProj 𝕜 V i) (piProj 𝕜 V i)

private theorem piForm_apply (P : ∀ i, CompactFormPair 𝕜 (V i) (H i))
    (u v : PiLp 2 V) :
    piForm P u v = ∑ i : ι, (P i).form (u i) (v i) := by
  simp only [piForm, FunLike.coe_sum, Finset.sum_apply, ContinuousLinearMap.bilinearComp_apply,
    piProj_apply]

/-- Finite `ℓ²`-direct sum of compact form pairs. -/
def pi (P : ∀ i, CompactFormPair 𝕜 (V i) (H i)) :
    CompactFormPair 𝕜 (PiLp 2 V) (PiLp 2 H) where
  inclusion := piInclusion P
  injective := by
    rw [coe_piInclusion]
    exact (PiLp.continuousLinearEquiv 2 𝕜 H).symm.injective.comp
      ((Function.Injective.piMap fun i => (P i).injective).comp
        (PiLp.continuousLinearEquiv 2 𝕜 V).injective)
  denseRange := by
    rw [coe_piInclusion]
    exact (PiLp.continuousLinearEquiv 2 𝕜 H).symm.surjective.denseRange.comp
      ((DenseRange.piMap fun i => (P i).denseRange).comp
        (PiLp.continuousLinearEquiv 2 𝕜 V).surjective.denseRange
        (Continuous.piMap fun i => (P i).inclusion.continuous))
      (PiLp.continuousLinearEquiv 2 𝕜 H).symm.continuous
  isCompactOperator := by
    have hprod : IsCompactOperator (ContinuousLinearMap.piMap fun i => (P i).inclusion) := by
      have hpi : IsCompactOperator (fun (x : ∀ i, V i) i => (P i).inclusion (x i)) :=
        IsCompactOperator.pi (f := fun i (x : ∀ j, V j) => (P i).inclusion (x i)) fun i =>
          (P i).isCompactOperator.comp_clm (ContinuousLinearMap.proj (R := 𝕜) i)
      rw [ContinuousLinearMap.coe_piMap']
      exact hpi
    exact (hprod.comp_clm (PiLp.continuousLinearEquiv 2 𝕜 V).toContinuousLinearMap).clm_comp
      (PiLp.continuousLinearEquiv 2 𝕜 H).symm.toContinuousLinearMap
  form := piForm P
  hermitian u v := by
    simp only [piForm_apply, star_sum, fun i => (P i).hermitian (u i) (v i)]
  exists_shifted_coercive := by
    choose c hc ω hbound using fun i => (P i).exists_shifted_coercive
    by_cases hne : (Finset.univ : Finset ι).Nonempty
    · refine ⟨Finset.univ.inf' hne c, (Finset.lt_inf'_iff hne).mpr fun i _ => hc i,
        Finset.univ.sup' hne ω, fun u => ?_⟩
      simp only [PiLp.norm_sq_eq_of_L2, piForm_apply, piInclusion_apply, map_sum,
        Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      have hc_le : Finset.univ.inf' hne c * ‖u i‖ ^ 2 ≤ c i * ‖u i‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (Finset.inf'_le c (Finset.mem_univ i)) (sq_nonneg _)
      have hω_le : ω i * ‖(P i).inclusion (u i)‖ ^ 2 ≤
          Finset.univ.sup' hne ω * ‖(P i).inclusion (u i)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (Finset.le_sup' ω (Finset.mem_univ i)) (sq_nonneg _)
      linarith [hbound i (u i)]
    · rw [Finset.not_nonempty_iff_eq_empty] at hne
      refine ⟨1, zero_lt_one, 0, fun u => ?_⟩
      simp [PiLp.norm_sq_eq_of_L2, piForm_apply, hne]

@[simp]
theorem pi_inclusion_apply (P : ∀ i, CompactFormPair 𝕜 (V i) (H i)) (u : PiLp 2 V) (i : ι) :
    (CompactFormPair.pi P).inclusion u i = (P i).inclusion (u i) :=
  piInclusion_apply P u i

@[simp]
theorem pi_form_apply (P : ∀ i, CompactFormPair 𝕜 (V i) (H i)) (u v : PiLp 2 V) :
    (CompactFormPair.pi P).form u v = ∑ i : ι, (P i).form (u i) (v i) :=
  piForm_apply P u v

@[simp]
theorem pi_energy (P : ∀ i, CompactFormPair 𝕜 (V i) (H i)) (u : PiLp 2 V) :
    (CompactFormPair.pi P).energy u = ∑ i : ι, (P i).energy (u i) := by
  simp [energy_def, pi_form_apply, map_sum]

end Pi

section RestrictScalars

variable {𝕜 V H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [InnerProductSpace ℝ V] [IsScalarTower ℝ 𝕜 V]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [InnerProductSpace ℝ H] [IsScalarTower ℝ 𝕜 H]

private def formAsRealLinear (P : CompactFormPair 𝕜 V H) : V →L[ℝ] StrongDual 𝕜 V where
  toFun := P.form
  map_add' := P.form.map_add'
  map_smul' r u := by
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), map_smulₛₗ, RCLike.conj_ofReal,
      RingHom.id_apply, ← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  cont := P.form.continuous

omit [InnerProductSpace ℝ H] [IsScalarTower ℝ 𝕜 H] in
private theorem formAsRealLinear_apply (P : CompactFormPair 𝕜 V H) (u : V) :
    formAsRealLinear P u = P.form u :=
  (rfl)

private def restrictScalarsForm (P : CompactFormPair 𝕜 V H) : V →L⋆[ℝ] V →L[ℝ] ℝ :=
  (StrongDual.extendRCLikeL (𝕜 := 𝕜) (F := V)).symm.toContinuousLinearMap.comp
    (formAsRealLinear P)

omit [InnerProductSpace ℝ H] [IsScalarTower ℝ 𝕜 H] in
private theorem restrictScalarsForm_apply (P : CompactFormPair 𝕜 V H) (u v : V) :
    restrictScalarsForm P u v = RCLike.re (P.form u v) := by
  simp [restrictScalarsForm, formAsRealLinear, StrongDual.extendRCLikeL_symm_apply]

/-- View a compact form pair over `𝕜` as a real compact form pair on the same underlying spaces
with real symmetric bilinear form `(u, v) ↦ Re (P.form u v)`. -/
def restrictScalars (P : CompactFormPair 𝕜 V H) : CompactFormPair ℝ V H where
  inclusion := P.inclusion.restrictScalars ℝ
  injective := P.injective
  denseRange := P.denseRange
  isCompactOperator := P.isCompactOperator
  form := restrictScalarsForm P
  hermitian u v := by
    rw [restrictScalarsForm_apply, restrictScalarsForm_apply, star_trivial, P.re_form_symm u v]
  exists_shifted_coercive := by
    obtain ⟨c, hc, ω, hbound⟩ := P.exists_shifted_coercive
    exact ⟨c, hc, ω, fun u => by
      simpa only [restrictScalarsForm_apply, RCLike.re_to_real,
        ContinuousLinearMap.coe_restrictScalars'] using hbound u⟩

@[simp]
theorem restrictScalars_inclusion (P : CompactFormPair 𝕜 V H) :
    P.restrictScalars.inclusion = P.inclusion.restrictScalars ℝ :=
  (rfl)

@[simp]
theorem restrictScalars_form_apply (P : CompactFormPair 𝕜 V H) (u v : V) :
    P.restrictScalars.form u v = RCLike.re (P.form u v) :=
  restrictScalarsForm_apply P u v

@[simp]
theorem restrictScalars_energy (P : CompactFormPair 𝕜 V H) (u : V) :
    P.restrictScalars.energy u = P.energy u := by
  rw [energy_def, restrictScalars_form_apply, RCLike.re_to_real, energy_def]

end RestrictScalars

section FiniteDimensional

variable {𝕜 H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]

/-- Any bounded Hermitian form on a finite-dimensional inner-product space `H` forms a compact form
pair with `inclusion = ContinuousLinearMap.id 𝕜 H`. -/
def ofFiniteDimensional (a : H →L⋆[𝕜] H →L[𝕜] 𝕜) (ha : ∀ u v : H, a u v = star (a v u)) :
    CompactFormPair 𝕜 H H where
  inclusion := ContinuousLinearMap.id 𝕜 H
  injective := Function.injective_id
  denseRange := denseRange_id
  isCompactOperator := by
    have : ProperSpace H := FiniteDimensional.proper_rclike 𝕜 H
    exact isCompactOperator_id
  form := a
  hermitian := ha
  exists_shifted_coercive := by
    refine ⟨1, zero_lt_one, ‖a‖ + 1, fun u => ?_⟩
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
    (ofFiniteDimensional a ha).energy u = RCLike.re (a u u) := by
  rw [energy_def, ofFiniteDimensional_form]

end FiniteDimensional

end CompactFormPair

end TauCeti
