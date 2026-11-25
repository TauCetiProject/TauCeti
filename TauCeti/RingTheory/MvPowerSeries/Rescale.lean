/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.MvPowerSeries.Restricted
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import TauCeti.Analysis.Normed.Ring.MulUnit
import TauCeti.Analysis.Normed.MulAction

/-!
# Rescaling multivariate power series

This file records general facts about Mathlib's coefficientwise rescaling of multivariate
power series. If scalars `uᵢ` scale norms by `rᵢ / sᵢ`, then the monomial `uᵗ` turns weighted
norms at `s` into weighted norms at `r` (`TauCeti.norm_finsuppProd_pow_smul_mul_finsuppProd`).
Hence rescaling by elements `uᵢ` by which left multiplication scales every norm by `‖uᵢ‖`
(`uᵢ` need not be invertible; multiplicative units are the main instance) transports weighted
coefficient norms, and restrictedness, when the weights are changed by the corresponding scalar
norms. In particular, rescaling by the inverses of multiplicative units `uᵢ` turns the weighted
coefficient norms at the radii `‖uᵢ‖⁻¹` into plain coefficient norms. Rescaling by a family of
units and then by their inverses is the identity. Rescaling multiplies each variable by its scalar
(`MvPowerSeries.rescale_X`). Rescaling by the indicator of the complement of a set of variables
sets these variables to zero (`MvPowerSeries.coeff_rescale_indicator_compl`). Substituting a
family into a rescaled power series is substituting the rescaled family: `f(a X)` at `X = v` is
`f(a v)`; in particular, `s • g = f(s X)` gives `s • g(v) = f(s v)`.
-/

public section

namespace MvPowerSeries

open Filter TauCeti

variable {σ R : Type*} {r s : σ → ℝ}

/-- Rescaling by elements `u i` by which left multiplication scales every norm by `‖u i‖` (for
instance multiplicative units, `TauCeti.IsNormMulUnit`) preserves weighted coefficient norms when
the weights are changed by the corresponding scalar norms: if `‖u i‖ * s i = r i`, then
`‖coeff n (rescale u f)‖ * sⁿ = ‖coeff n f‖ * rⁿ`. -/
theorem norm_coeff_rescale_mul_prod [CommSemiring R] [Norm R] (u : σ → R)
    (hu : ∀ i (x : R), ‖u i * x‖ = ‖u i‖ * ‖x‖) (hrs : ∀ i, ‖u i‖ * s i = r i)
    (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    ‖coeff n (rescale u f)‖ * n.prod (s · ^ ·) =
      ‖coeff n f‖ * n.prod (r · ^ ·) := by
  rw [coeff_rescale]
  exact norm_finsuppProd_pow_smul_mul_finsuppProd u
    (fun i ↦ norm_smul_mul_of_norm_mul (hu i) (hrs i)) n _

/-- Rescaling by elements `u i` by which left multiplication scales every norm by `‖u i‖`
converts restrictedness at `r` into restrictedness at `s` when `‖u i‖ * s i = r i`. -/
theorem isRestricted_rescale_iff [NormedCommRing R] (u : σ → R)
    (hu : ∀ i (x : R), ‖u i * x‖ = ‖u i‖ * ‖x‖) (hrs : ∀ i, ‖u i‖ * s i = r i)
    (f : MvPowerSeries σ R) :
    IsRestricted s (rescale u f) ↔ IsRestricted r f := by
  unfold IsRestricted
  apply tendsto_congr'
  exact .of_forall (norm_coeff_rescale_mul_prod u hu hrs f)

/-- **Weight bounds from multiplicative units.** If each `u i` is a multiplicative unit and
`‖u i‖ * r i = 1`, then rescaling by the inverse units turns the weighted coefficient norms at the
radii `r` into plain coefficient norms: the coefficient of `f(u⁻¹ X)` at `n` has norm
`‖coeff n f‖ * rⁿ`. -/
theorem norm_coeff_rescale_units_inv [CommSemiring R] [Norm R] (u : σ → Rˣ)
    (hu : ∀ i, IsNormMulUnit (u i : R))
    (hr : ∀ i, ‖(u i : R)‖ * r i = 1) (f : MvPowerSeries σ R) (n : σ →₀ ℕ) :
    ‖coeff n (rescale (fun i ↦ (((u i)⁻¹ : Rˣ) : R)) f)‖ = ‖coeff n f‖ * n.prod (r · ^ ·) := by
  have hinv (i : σ) : ‖(((u i)⁻¹ : Rˣ) : R)‖ * 1 = r i := by
    rw [mul_one, NormedRing.norm_units_inv_of_norm_mul (hu i).norm_mul,
      inv_eq_of_mul_eq_one_right (hr i)]
  simpa [Finsupp.prod] using
    norm_coeff_rescale_mul_prod _ (fun i ↦ (hu i).units_inv.norm_mul) hinv f n

/-- Rescaling multiplies each variable by its scalar: `rescale a (X i) = a i * X i`. -/
@[simp]
theorem rescale_X {A : Type*} [CommSemiring A] (a : σ → A) (i : σ) :
    rescale a (X i) = C (a i) * X i := by
  classical
  ext n
  rw [coeff_rescale, coeff_X, coeff_C_mul, coeff_X]
  split_ifs with h
  · simp [h]
  · simp

/-- The algebra-map form of `MvPowerSeries.rescale_X`. -/
@[simp]
theorem rescaleAlgHom_X {A : Type*} [CommRing A] (a : σ → A) (i : σ) :
    rescaleAlgHom a (X i) = C (a i) * X i := by
  rw [rescaleAlgHom_apply, rescale_X]

/-- Rescaling by a family of units and then by their inverses is the identity. -/
theorem rescale_inv_rescale {A : Type*} [CommSemiring A] (u : σ → Aˣ) (f : MvPowerSeries σ A) :
    rescale (fun i ↦ (((u i)⁻¹ : Aˣ) : A)) (rescale (fun i ↦ (u i : A)) f) = f := by
  have h : ((fun i ↦ (u i : A)) * fun i ↦ (((u i)⁻¹ : Aˣ) : A)) = 1 := by
    funext i
    simp
  rw [rescale_rescale, h, rescale_one, RingHom.id_apply]

open Classical in
/-- Rescaling by the indicator of the complement of `s` sets the variables of `s` to zero. -/
theorem coeff_rescale_indicator_compl {A : Type*} [CommSemiring A] (s : Set σ)
    (f : MvPowerSeries σ A) (t : σ →₀ ℕ) :
    coeff t (rescale (sᶜ.indicator 1) f) = if ∀ j ∈ s, t j = 0 then coeff t f else 0 := by
  rw [coeff_rescale, Finsupp.prod,
    Finset.prod_congr rfl fun j hj ↦ (?_ : _ = if j ∈ sᶜ then (1 : A) else 0),
    Finset.prod_boole]
  · have : (∀ j ∈ t.support, j ∈ sᶜ) ↔ ∀ j ∈ s, t j = 0 := by
      simp only [Finsupp.mem_support_iff, Set.mem_compl_iff]
      exact ⟨fun h j hj ↦ by_contra fun h' ↦ h j h' hj, fun h j hj hjs ↦ hj (h j hjs)⟩
    by_cases h : ∀ j ∈ s, t j = 0
    · simp only [this, eq_true h, ↓reduceIte, one_mul]
    · simp only [this, eq_false h, ↓reduceIte, zero_mul]
  · rw [Set.indicator_apply]
    split_ifs
    · exact one_pow _
    · exact zero_pow (Finsupp.mem_support_iff.mp hj)

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
