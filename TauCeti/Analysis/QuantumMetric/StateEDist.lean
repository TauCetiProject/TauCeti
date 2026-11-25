/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import TauCeti.Analysis.Normed.Module.Basic
public import TauCeti.Analysis.QuantumMetric.ExtendedLipschitzSeminorm

/-!
# The state distance of an extended Lipschitz seminorm

For an extended Lipschitz seminorm `L` for `e` on a real topological vector space `E`, the
**state distance** of two continuous functionals `φ ψ : WeakDual ℝ E` is

`L.stateEDist φ ψ = ⨆ (a) (_ : L a ≤ 1), edist (φ a) (ψ a)`,

the supremum of `|φ a - ψ a|` over the unit ball of `L`, taken in `ℝ≥0∞`. On the states of an
order-unit space this is Rieffel's metric on the state space; here it is developed for all
continuous functionals, so that it applies to any set of states.

## Main statements

* `stateEDist_self`, `stateEDist_comm` and `stateEDist_triangle`: `stateEDist` is an extended
  pseudometric on `WeakDual ℝ E`.
* `stateEDist_eq_top_of_apply_ne`: functionals taking different values at `e` are at
  distance `∞`, because `L` vanishes on the multiples of `e`.
* `stateEDist_eq_zero_iff`: two continuous functionals are at distance zero exactly when they
  are equal, by density of the finite domain of `L`.
* `edist_apply_le_mul_stateEDist`: the evaluation estimate
  `|φ a - ψ a| ≤ L a * L.stateEDist φ ψ` for functionals agreeing at `e`.
* `stateEDist_antitone`, `stateEDist_smul`: a larger seminorm gives a smaller distance, and
  rescaling `L` by `t` divides the distance by `t`.
* `stateEDist_comap_le` and `stateEDist_comap`: pulling `L` back along a linear map does not
  increase the distance of the pulled-back functionals, and preserves it for surjective maps;
  `stateEDist_comapEquiv` is the case of a continuous linear equivalence.

## References

* M. A. Rieffel, *Metrics on states from actions of compact groups*, Doc. Math. 3 (1998), §1.
* M. A. Rieffel, *Metrics on state spaces*, Doc. Math. 4 (1999), §2.
-/

public section

open scoped ENNReal NNReal

namespace TauCeti

namespace ExtendedLipschitzSeminorm

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] {e : E}
  (L M : ExtendedLipschitzSeminorm e) {φ ψ χ : WeakDual ℝ E} {a : E}

/-- The **state distance** `⨆ (a) (_ : L a ≤ 1), edist (φ a) (ψ a)` of two continuous
functionals with respect to an extended Lipschitz seminorm `L`. -/
noncomputable def stateEDist (φ ψ : WeakDual ℝ E) : ℝ≥0∞ :=
  ⨆ (a : E) (_ : L a ≤ 1), edist (φ a) (ψ a)

theorem stateEDist_def (φ ψ : WeakDual ℝ E) :
    L.stateEDist φ ψ = ⨆ (a : E) (_ : L a ≤ 1), edist (φ a) (ψ a) :=
  (rfl)

variable {L M}

theorem edist_apply_le_stateEDist (ha : L a ≤ 1) : edist (φ a) (ψ a) ≤ L.stateEDist φ ψ :=
  le_iSup₂ (f := fun a (_ : L a ≤ 1) => edist (φ a) (ψ a)) a ha

theorem stateEDist_le_iff {c : ℝ≥0∞} :
    L.stateEDist φ ψ ≤ c ↔ ∀ a, L a ≤ 1 → edist (φ a) (ψ a) ≤ c :=
  iSup₂_le_iff

variable (L)

@[simp]
theorem stateEDist_self (φ : WeakDual ℝ E) : L.stateEDist φ φ = 0 :=
  nonpos_iff_eq_zero.1 <| stateEDist_le_iff.2 fun _ _ => by simp

theorem stateEDist_comm (φ ψ : WeakDual ℝ E) : L.stateEDist φ ψ = L.stateEDist ψ φ := by
  simp only [stateEDist, edist_comm]

theorem stateEDist_triangle (φ ψ χ : WeakDual ℝ E) :
    L.stateEDist φ χ ≤ L.stateEDist φ ψ + L.stateEDist ψ χ :=
  stateEDist_le_iff.2 fun _ ha => (edist_triangle _ _ _).trans <|
    add_le_add (edist_apply_le_stateEDist ha) (edist_apply_le_stateEDist ha)

/-- Functionals with different values at `e` are at infinite state distance: `L` vanishes on
every multiple of `e`, while `|φ (r • e) - ψ (r • e)|` is unbounded in `r`. -/
theorem stateEDist_eq_top_of_apply_ne (h : φ e ≠ ψ e) : L.stateEDist φ ψ = ∞ := by
  have hd : φ e - ψ e ≠ 0 := sub_ne_zero.2 h
  refine ENNReal.eq_top_of_forall_nnreal_le fun x => ?_
  set r := (x : ℝ) / (φ e - ψ e)
  have hx : φ (r • e) - ψ (r • e) = x := by
    simp only [r, map_smul, smul_eq_mul, ← mul_sub, div_mul_cancel₀ _ hd]
  calc (x : ℝ≥0∞) = edist (φ (r • e)) (ψ (r • e)) := by
        rw [edist_dist, Real.dist_eq, hx, NNReal.abs_eq, ENNReal.ofReal_coe_nnreal]
    _ ≤ L.stateEDist φ ψ := edist_apply_le_stateEDist ((L.map_smul_self r).trans_le zero_le_one)

/-- The evaluation estimate for elements of finite seminorm. -/
private theorem edist_apply_le_mul_stateEDist_of_ne_top (h : φ e = ψ e) (ha : L a ≠ ∞) :
    edist (φ a) (ψ a) ≤ L a * L.stateEDist φ ψ := by
  rcases eq_or_ne (L a) 0 with ha₀ | ha₀
  · obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 (L.eq_zero_iff.1 ha₀)
    simp [h]
  set t := (L a).toReal
  have ht : 0 < t := ENNReal.toReal_pos ha₀ ha
  have hLt : ‖t⁻¹‖ₑ * L a = 1 := by
    rw [Real.eNorm_eq_ofReal (inv_nonneg.2 ht.le), ENNReal.ofReal_inv_of_pos ht,
      ENNReal.ofReal_toReal ha, ENNReal.inv_mul_cancel ha₀ ha]
  have hb : edist (φ (t⁻¹ • a)) (ψ (t⁻¹ • a)) ≤ L.stateEDist φ ψ :=
    edist_apply_le_stateEDist (by rw [L.map_smul_eq_mul, hLt])
  rw [edist_map_smul] at hb
  calc edist (φ a) (ψ a) = L a * (‖t⁻¹‖ₑ * edist (φ a) (ψ a)) := by
        rw [← mul_assoc, mul_comm (L a), hLt, one_mul]
    _ ≤ L a * L.stateEDist φ ψ := by gcongr

/-- Two continuous functionals are at state distance zero exactly when they are equal. -/
@[simp]
theorem stateEDist_eq_zero_iff : L.stateEDist φ ψ = 0 ↔ φ = ψ := by
  refine ⟨fun h0 => ?_, fun h => h ▸ L.stateEDist_self φ⟩
  have he : φ e = ψ e := by
    by_contra h
    simp [L.stateEDist_eq_top_of_apply_ne h] at h0
  refine DFunLike.coe_injective <|
    Continuous.ext_on L.dense_domain (map_continuous φ) (map_continuous ψ) fun a ha => ?_
  simpa [h0] using L.edist_apply_le_mul_stateEDist_of_ne_top he (L.mem_domain.1 ha)

/-- **The evaluation estimate**: `|φ a - ψ a| ≤ L a * L.stateEDist φ ψ` for functionals agreeing
at `e`, with the `ℝ≥0∞` conventions `0 * ∞ = 0` and `∞ * x = ∞` for `x ≠ 0`. -/
theorem edist_apply_le_mul_stateEDist (h : φ e = ψ e) (a : E) :
    edist (φ a) (ψ a) ≤ L a * L.stateEDist φ ψ := by
  rcases ne_or_eq (L a) ∞ with ha | ha
  · exact L.edist_apply_le_mul_stateEDist_of_ne_top h ha
  rcases eq_or_ne (L.stateEDist φ ψ) 0 with h0 | h0
  · simp [(L.stateEDist_eq_zero_iff).1 h0]
  · simp [ha, ENNReal.top_mul h0]

/-- A larger extended Lipschitz seminorm has a smaller unit ball, hence a smaller state
distance. -/
theorem stateEDist_antitone (φ ψ : WeakDual ℝ E) :
    Antitone fun L : ExtendedLipschitzSeminorm e => L.stateEDist φ ψ :=
  fun _ _ hLM => stateEDist_le_iff.2 fun _ ha => edist_apply_le_stateEDist ((hLM _).trans ha)

/-- Rescaling an extended Lipschitz seminorm by `t` divides its state distance by `t`. -/
theorem stateEDist_smul (t : ℝ≥0) (ht : t ≠ 0) (φ ψ : WeakDual ℝ E) :
    (L.smul t ht).stateEDist φ ψ = L.stateEDist φ ψ / t := by
  have hφψ (s : ℝ≥0) (a : E) : edist (φ ((s : ℝ) • a)) (ψ ((s : ℝ) • a)) =
      s * edist (φ a) (ψ a) := by
    rw [edist_map_smul, NNReal.eNorm_eq]
  refine le_antisymm (stateEDist_le_iff.2 fun a ha => ?_) ?_
  · rw [smul_apply] at ha
    rw [ENNReal.le_div_iff_mul_le (by simpa using Or.inl ht) (by simp), mul_comm, ← hφψ]
    refine edist_apply_le_stateEDist ?_
    rwa [L.map_smul_eq_mul, NNReal.eNorm_eq]
  · rw [ENNReal.div_le_iff_le_mul (by simpa using Or.inl ht) (by simp)]
    refine stateEDist_le_iff.2 fun a ha => ?_
    have hta : (t : ℝ) • ((t⁻¹ : ℝ≥0) : ℝ) • a = a := by
      rw [smul_smul, NNReal.coe_inv, mul_inv_cancel₀ (by simpa using ht), one_smul]
    rw [← hta, hφψ, mul_comm]
    gcongr
    refine edist_apply_le_stateEDist ?_
    simpa [L.map_smul_eq_mul, ← mul_assoc, ENNReal.mul_inv_cancel, ht] using ha

variable [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {f : F}

variable {L} in
private theorem stateEDist_le_of_apply_eq {L' : ExtendedLipschitzSeminorm f} {T : F → E}
    (hL : ∀ a, L' a = L (T a)) {φ' ψ' : WeakDual ℝ F} (hφ : ∀ a, φ' a = φ (T a))
    (hψ : ∀ a, ψ' a = ψ (T a)) : L'.stateEDist φ' ψ' ≤ L.stateEDist φ ψ :=
  stateEDist_le_iff.2 fun a ha => by
    rw [hφ, hψ]
    exact edist_apply_le_stateEDist ((hL a).symm.trans_le ha)

variable {L} in
private theorem stateEDist_eq_of_apply_eq {L' : ExtendedLipschitzSeminorm f} {T : F → E}
    (hL : ∀ a, L' a = L (T a)) (hsurj : Function.Surjective T) {φ' ψ' : WeakDual ℝ F}
    (hφ : ∀ a, φ' a = φ (T a)) (hψ : ∀ a, ψ' a = ψ (T a)) :
    L'.stateEDist φ' ψ' = L.stateEDist φ ψ := by
  refine le_antisymm (stateEDist_le_of_apply_eq hL hφ hψ) (stateEDist_le_iff.2 fun b hb => ?_)
  obtain ⟨a, rfl⟩ := hsurj b
  rw [← hφ, ← hψ]
  exact edist_apply_le_stateEDist ((hL a).trans_le hb)

/-- Pulling `L` back along a linear map `T` does not increase the state distance of functionals
pulled back along `T`. -/
theorem stateEDist_comap_le (T : F →ₗ[ℝ] E) (hT : T f = e) (hker : LinearMap.ker T ≤ ℝ ∙ f)
    (hdense : Dense (T ⁻¹' L.domain)) {φ' ψ' : WeakDual ℝ F} (hφ : ∀ a, φ' a = φ (T a))
    (hψ : ∀ a, ψ' a = ψ (T a)) :
    (L.comap T hT hker hdense).stateEDist φ' ψ' ≤ L.stateEDist φ ψ :=
  stateEDist_le_of_apply_eq (L.comap_apply T hT hker hdense) hφ hψ

/-- Pulling `L` back along a surjective linear map `T` preserves the state distance of
functionals pulled back along `T`. -/
theorem stateEDist_comap (T : F →ₗ[ℝ] E) (hT : T f = e) (hker : LinearMap.ker T ≤ ℝ ∙ f)
    (hdense : Dense (T ⁻¹' L.domain)) (hsurj : Function.Surjective T) {φ' ψ' : WeakDual ℝ F}
    (hφ : ∀ a, φ' a = φ (T a)) (hψ : ∀ a, ψ' a = ψ (T a)) :
    (L.comap T hT hker hdense).stateEDist φ' ψ' = L.stateEDist φ ψ :=
  stateEDist_eq_of_apply_eq (L.comap_apply T hT hker hdense) hsurj hφ hψ

/-- Transport of `L` along a continuous linear equivalence preserves the state distance of
functionals transported along it. -/
theorem stateEDist_comapEquiv (T : F ≃L[ℝ] E) (hT : T f = e) {φ' ψ' : WeakDual ℝ F}
    (hφ : ∀ a, φ' a = φ (T a)) (hψ : ∀ a, ψ' a = ψ (T a)) :
    (L.comapEquiv T hT).stateEDist φ' ψ' = L.stateEDist φ ψ :=
  stateEDist_eq_of_apply_eq (L.comapEquiv_apply T hT) T.surjective hφ hψ

end ExtendedLipschitzSeminorm

end TauCeti
