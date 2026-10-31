/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import TauCeti.Analysis.Normed.Ring.MulUnit

/-!
# Rescaling multivariate power series

This file records general facts about Mathlib's coefficientwise rescaling of multivariate
power series. Rescaling by multiplicative units transports weighted coefficient norms, and hence
restrictedness, when the weights are changed by the corresponding scalar norms; in particular,
rescaling by the inverses of multiplicative units `uᵢ` turns the weighted coefficient norms at the
radii `‖uᵢ‖⁻¹` into plain coefficient norms. Rescaling by a
family of units and then by their inverses is the identity. Substituting a family into a rescaled
power series is substituting the rescaled family: `f(a X)` at `X = v` is `f(a v)`; in particular,
`s • g = f(s X)` gives `s • g(v) = f(s v)`.
-/

public section

namespace MvPowerSeries

open Filter TauCeti

variable {σ R : Type*} [NormedCommRing R] {r s : σ → ℝ}

/-- Rescaling by multiplicative units preserves weighted coefficient norms when the weights are
changed by the corresponding scalar norms. -/
theorem norm_coeff_rescale_mul_prod (u : σ → R) (hu : ∀ i, IsNormMulUnit (u i))
    (hrs : ∀ i, ‖u i‖ * s i = r i) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    ‖coeff n (rescale u f)‖ * n.prod (s · ^ ·) =
      ‖coeff n f‖ * n.prod (r · ^ ·) := by
  classical
  rcases subsingleton_or_nontrivial R with hR | hR
  · let _ : Subsingleton R := hR
    simp [Subsingleton.elim (coeff n (rescale u f)) 0, Subsingleton.elim (coeff n f) 0]
  · let _ : Nontrivial R := hR
    by_cases hn : n.support.Nonempty
    · obtain ⟨i, hi⟩ := hn
      let _ : NormOneClass R := ⟨(hu i).norm_one⟩
      have hpow (j : σ) (_ : j ∈ n.support) : IsNormMulUnit (u j ^ n j) := (hu j).pow _
      rw [coeff_rescale, Finsupp.prod, (IsNormMulUnit.prod hpow).norm_mul,
        IsNormMulUnit.norm_prod hpow, mul_right_comm, mul_comm]
      congr 1
      simp only [Finsupp.prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun j _ ↦ by rw [(hu j).norm_pow, ← mul_pow, hrs j]
    · have hn0 : n = 0 := Finsupp.support_eq_empty.mp (Finset.not_nonempty_iff_eq_empty.mp hn)
      subst n
      simp

/-- Rescaling by multiplicative units converts restrictedness at `r` into restrictedness at `s`
when `‖u i‖ * s i = r i`. -/
theorem isRestricted_rescale_iff (u : σ → R) (hu : ∀ i, IsNormMulUnit (u i))
    (hrs : ∀ i, ‖u i‖ * s i = r i) (f : MvPowerSeries σ R) :
    IsRestricted s (rescale u f) ↔ IsRestricted r f := by
  unfold IsRestricted
  apply tendsto_congr'
  exact .of_forall (norm_coeff_rescale_mul_prod u hu hrs f)

/-- **Weight bounds from multiplicative units.** If each `u i` is a multiplicative unit and
`‖u i‖ * r i = 1`, then rescaling by the inverse units turns the weighted coefficient norms at the
radii `r` into plain coefficient norms: the coefficient of `f(u⁻¹ X)` at `n` has norm
`‖coeff n f‖ * rⁿ`. -/
theorem norm_coeff_rescale_units_inv (u : σ → Rˣ) (hu : ∀ i, IsNormMulUnit (u i : R))
    (hr : ∀ i, ‖(u i : R)‖ * r i = 1) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    ‖coeff n (rescale (fun i ↦ (((u i)⁻¹ : Rˣ) : R)) f)‖ = ‖coeff n f‖ * n.prod (r · ^ ·) := by
  have hinv (i : σ) : ‖(((u i)⁻¹ : Rˣ) : R)‖ * 1 = r i := by
    have hu0 : ‖(u i : R)‖ ≠ 0 := left_ne_zero_of_mul_eq_one (hr i)
    rw [mul_one, NormedRing.norm_units_inv_of_norm_mul hu0 (hu i).norm_mul,
      inv_eq_of_mul_eq_one_right (hr i)]
  simpa [Finsupp.prod] using norm_coeff_rescale_mul_prod _ (fun i ↦ (hu i).units_inv) hinv f n

/-- Rescaling by a family of units and then by their inverses is the identity. -/
theorem rescale_inv_rescale {A : Type*} [CommSemiring A] (u : σ → Aˣ) (f : MvPowerSeries σ A) :
    rescale (fun i ↦ (((u i)⁻¹ : Aˣ) : A)) (rescale (fun i ↦ (u i : A)) f) = f := by
  have h : ((fun i ↦ (u i : A)) * fun i ↦ (((u i)⁻¹ : Aˣ) : A)) = 1 := by
    funext i
    simp
  rw [rescale_rescale, h, rescale_one, RingHom.id_apply]

/-- Substituting a family `v` into the rescaling `f(a X)` of `f` substitutes the rescaled family:
`f(a X)` at `X = v` is `f(a v)`. -/
theorem subst_rescale {τ A : Type*} [CommRing A] (a : σ → A) (f : MvPowerSeries σ A)
    {v : σ → MvPowerSeries τ A} (hv : HasSubst v) : (rescale a f).subst v = f.subst (a • v) := by
  rw [rescale_eq_subst, subst_comp_subst_apply (HasSubst.smul_X a) hv]
  congr 1
  funext i
  simp only [Pi.smul_apply', subst_smul hv, subst_X hv]

/-- If `s • g = f(s X)`, then `s • g(v) = f(s v)` at every substitutable family `v`. -/
theorem smul_subst_of_smul_eq_rescale {τ A : Type*} [CommRing A] {f g : MvPowerSeries σ A}
    {s : A} (h : s • g = rescale (fun _ ↦ s) f) {v : σ → MvPowerSeries τ A} (hv : HasSubst v) :
    s • g.subst v = f.subst (s • v) := by
  rw [← subst_smul hv, h, subst_rescale _ _ hv]
  -- The pointwise action of the constant family `fun _ ↦ s` is the action of `s`.
  rfl

end MvPowerSeries
