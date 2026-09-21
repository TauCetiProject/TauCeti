/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.EnergyForm.Sobolev
public import TauCeti.Analysis.Sobolev.W1p.CompactSupport
public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff

/-!
# The Caccioppoli inequality for weak solutions

Let `u ∈ H¹(Ω)` be a weak solution of the divergence-form equation

`-∂ⱼ(aⁱʲ ∂ᵢu) = f` in `Ω`, with `f ∈ L²(Ω)`,

meaning `∫_Ω ⟨a ∇u, ∇v⟩ = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`; no boundary condition is imposed on
`u`. If the coefficient `a` is measurable and uniformly elliptic with constants `0 < λ ≤ Λ`,
then for every smooth cutoff `ζ` compactly supported in `Ω`,

`∫_Ω ζ² ‖∇u‖² ≤ (2Λ/λ)² ∫_Ω ‖∇ζ‖² u² + (2/λ) ∫_Ω ζ² f u`.

This is the **Caccioppoli inequality** (the reverse Poincaré, or interior energy, inequality):
the gradient of a solution on the region where `ζ = 1` is controlled by the solution itself on
the support of `ζ`. The constants depend only on the ellipticity constants `λ` and `Λ`, and not
on `Ω`, on the dimension, or on any regularity of the coefficients beyond measurability. It is
the basic interior estimate of elliptic regularity theory: it is an ingredient in
difference-quotient proofs of interior `H²` regularity under additional coefficient regularity,
and its variant for the truncations `(u - k)⁺` of subsolutions, not proved here, is the starting
point of De Giorgi's iteration.

The proof tests the equation against `ζ² u`, which lies in `H¹₀(Ω)` because `ζ` is compactly
supported in `Ω`, and whose gradient is `ζ² ∇u + 2ζu ∇ζ`. Ellipticity bounds the first term of
`⟨a ∇u, ∇(ζ² u)⟩` below by `λζ²‖∇u‖²`, and Young's inequality absorbs half of it into the cross
term `2ζu ⟨a ∇u, ∇ζ⟩`.

## Main declarations

* `TauCeti.PDE.W1p.setIntegral_sq_mul_norm_gradient_sq_le_of_pointwise`: the common
  integration and absorption step for Caccioppoli inequalities.
* `TauCeti.PDE.UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le`: the Caccioppoli
  inequality.

## References

* L. C. Evans, *Partial Differential Equations*, §6.3.1 (the energy estimate in the proof of
  Theorem 1, interior `H²` regularity).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §8.2 and §8.6.
* M. Giaquinta, L. Martinazzi, *An Introduction to the Regularity Theory for Elliptic Systems,
  Harmonic Maps and Minimal Graphs*, Theorem 4.4.
-/

public section

noncomputable section

open MeasureTheory Matrix Set TopologicalSpace
open scoped ContDiff Gradient InnerProductSpace

namespace TauCeti

namespace PDE

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {mu : Measure (EuclideanSpace ℝ ι)}
  [mu.IsAddHaarMeasure] {Omega : Opens (EuclideanSpace ℝ ι)}
  {a : EuclideanSpace ℝ ι → Matrix ι ι ℝ} {lam Lam : ℝ}

omit [DecidableEq ι] in
/-- Integrate a pointwise Caccioppoli estimate and absorb half of its energy term. This is
the common measure-theoretic step for the solution and subsolution forms of the inequality;
the caller supplies the energy density and its comparison with the forcing term. -/
theorem W1p.setIntegral_sq_mul_norm_gradient_sq_le_of_pointwise (hlam : 0 < lam)
    (w : W1p mu Omega 2) {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) {M : ℝ}
    (hψM : ∀ x, |ψ x| ≤ M) (hgradM : ∀ x, ‖∇ ψ x‖ ≤ M)
    {e force : EuclideanSpace ℝ ι → ℝ} (he : Integrable e (mu.restrict Omega))
    (hpointwise : ∀ᵐ x ∂mu.restrict Omega,
      lam * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) ≤
        e x + lam / 2 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
          + 2 * Lam ^ 2 / lam * (‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2))
    (hforce : ∫ x in Omega, e x ∂mu ≤ ∫ x in Omega, force x ∂mu) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu ≤
      (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
        + 2 / lam * ∫ x in Omega, force x ∂mu := by
  have hψ2 : AEStronglyMeasurable (fun x => ψ x ^ 2) (mu.restrict Omega) :=
    (hψ.continuous.pow 2).aestronglyMeasurable
  have hgrad2 : AEStronglyMeasurable (fun x => ‖∇ ψ x‖ ^ 2) (mu.restrict Omega) :=
    ((ContDiff.continuous_gradient hψ).norm.pow 2).aestronglyMeasurable
  have hI1 : Integrable (fun x => ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) (mu.restrict Omega) :=
    (W1p.integrable_norm_gradient_sq w).bdd_mul hψ2 (c := M ^ 2) (Filter.Eventually.of_forall
      fun x => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hψM x) 2)
  have hI2 : Integrable (fun x => ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2) (mu.restrict Omega) :=
    (W1p.integrable_value_sq w).bdd_mul hgrad2 (c := M ^ 2) (Filter.Eventually.of_forall
      fun x => by
        rw [Real.norm_eq_abs, abs_pow, abs_norm]
        exact pow_le_pow_left₀ (norm_nonneg _) (hgradM x) 2)
  have hint : ∫ x in Omega, lam * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2) ∂mu ≤
      ∫ x in Omega, (e x + lam / 2 * (ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2)
        + 2 * Lam ^ 2 / lam * (‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2)) ∂mu :=
    integral_mono_ae (hI1.const_mul lam) ((he.add (hI1.const_mul _)).add (hI2.const_mul _))
      hpointwise
  rw [integral_const_mul, integral_add, integral_add, integral_const_mul,
    integral_const_mul] at hint
  rotate_left
  · exact he
  · exact hI1.const_mul _
  · exact he.add (hI1.const_mul _)
  · exact hI2.const_mul _
  set X := ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient w x‖ ^ 2 ∂mu
  set Y := ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value w x ^ 2 ∂mu
  set F := ∫ x in Omega, force x ∂mu
  have hmain : lam * X ≤ F + lam / 2 * X + 2 * Lam ^ 2 / lam * Y := by
    calc
      lam * X ≤ (∫ x in Omega, e x ∂mu) + lam / 2 * X + 2 * Lam ^ 2 / lam * Y := by
        simpa [X, Y] using hint
      _ ≤ F + lam / 2 * X + 2 * Lam ^ 2 / lam * Y := by
        gcongr
  have hX : X = 2 / lam * (lam / 2 * X) := by field_simp
  rw [hX]
  calc
    2 / lam * (lam / 2 * X) ≤ 2 / lam * (F + 2 * Lam ^ 2 / lam * Y) := by
      gcongr
      linarith
    _ = (2 * Lam / lam) ^ 2 * Y + 2 / lam * F := by
      field_simp
      ring

/-- **The Caccioppoli inequality.** Let `a` be measurable and uniformly elliptic on `Ω` with
constants `0 < λ ≤ Λ`, and let `u ∈ H¹(Ω)` be a weak solution of `-∂ⱼ(aⁱʲ ∂ᵢu) = f` in `Ω`, in
the sense that `a(u, v) = ∫_Ω f v` for every `v ∈ H¹₀(Ω)`, with no boundary condition on `u`.
Then for every smooth `ψ` compactly supported in `Ω`,

`∫_Ω ψ² ‖∇u‖² ≤ (2Λ/λ)² ∫_Ω ‖∇ψ‖² u² + (2/λ) ∫_Ω ψ² f u`.

For `f = 0` the last term vanishes, and the gradient of `u` where `ψ = 1` is bounded by `u`
itself on the support of `ψ`. -/
theorem UniformlyEllipticOn.setIntegral_sq_mul_norm_gradient_sq_le
    (h : UniformlyEllipticOn (Omega : Set (EuclideanSpace ℝ ι)) a lam Lam)
    (ha : AEStronglyMeasurable a (mu.restrict Omega)) {f : Lp ℝ 2 (mu.restrict Omega)}
    {u : W1p mu Omega 2}
    (hu : ∀ v : W1p0 mu Omega 2, energyFormH1 a 0 0 u (v : W1p mu Omega 2) =
      ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu)
    {ψ : EuclideanSpace ℝ ι → ℝ} (hψ : ContDiff ℝ ∞ ψ) (hcpt : HasCompactSupport ψ)
    (hts : tsupport ψ ⊆ (Omega : Set (EuclideanSpace ℝ ι))) :
    ∫ x in Omega, ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2 ∂mu ≤
      (2 * Lam / lam) ^ 2 * ∫ x in Omega, ‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2 ∂mu
        + 2 / lam * ∫ x in Omega, ψ x ^ 2 * f x * W1p.value u x ∂mu := by
  have hlam := h.pos
  obtain ⟨M, hM, hψM, hgradM⟩ := (hψ.of_le (by simp)).exists_abs_le_and_norm_gradient_le hcpt
  have hψM' : ∀ x ∈ Omega, |ψ x| ≤ M := fun x _ => hψM x
  have hgradM' : ∀ x ∈ Omega, ‖∇ ψ x‖ ≤ M := fun x _ => hgradM x
  -- The test function `ψ² u = ψ (ψ u)`, which lies in `H¹₀(Ω)`.
  set w := W1p.contDiffSMul ψ hψ hM hψM' hgradM' u
  set v := W1p.contDiffSMul ψ hψ hM hψM' hgradM' w
  have hv : v ∈ w1p0Submodule mu Omega 2 :=
    W1p.contDiffSMul_mem_w1p0Submodule_of_hasCompactSupport (by simp) hψ hM hψM' hgradM' hcpt
      hts w
  have heq := hu ⟨v, hv⟩
  simp only at heq
  have hmem : ∀ᵐ x ∂mu.restrict Omega, x ∈ (Omega : Set (EuclideanSpace ℝ ι)) :=
    ae_restrict_mem Omega.isOpen.measurableSet
  have hE := h.integrable_energyIntegrand_jetField (b := 0) (c := 0) (beta := 0) (gamma := 0)
    ha aestronglyMeasurable_const aestronglyMeasurable_const (fun _ _ => by simp)
    (fun _ _ => by simp) u v
  -- The pointwise estimate, almost everywhere on `Ω`.
  have hpt : ∀ᵐ x ∂mu.restrict Omega,
      lam * (ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2) ≤
        energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
            ((0 : EuclideanSpace ℝ ι → ℝ) x) (jetField u x) (jetField v x)
          + lam / 2 * (ψ x ^ 2 * ‖W1p.gradient u x‖ ^ 2)
          + 2 * Lam ^ 2 / lam * (‖∇ ψ x‖ ^ 2 * W1p.value u x ^ 2) := by
    filter_upwards [hmem, W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.gradient_contDiffSMul_ae hψ hM hψM' hgradM' u,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' u] with x hx hgv hgw hvw
    have key := mul_sq_mul_norm_sq_le_matrixBilinearForm_add hlam (ψ x)
      (W1p.value u x) (W1p.gradient u x) (∇ ψ x)
      (h.lower_bound hx (W1p.gradient u x))
      (h.upper_bound hx (∇ ψ x) (W1p.gradient u x))
    rw [energyIntegrand_apply, jetField_apply, jetField_apply, hgv, hgw, hvw]
    simpa [driftForm_apply, massForm_apply, smul_eq_mul] using key
  -- The energy integral is `∫_Ω ψ² f u`, by the weak equation.
  have hF : ∫ x in Omega, energyIntegrand (a x) ((0 : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) x)
        ((0 : EuclideanSpace ℝ ι → ℝ) x) (jetField u x) (jetField v x) ∂mu =
      ∫ x in Omega, ψ x ^ 2 * f x * W1p.value u x ∂mu := by
    rw [← energyFormH1_def, heq]
    refine integral_congr_ae ?_
    filter_upwards [W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' w,
      W1p.value_contDiffSMul_ae hψ hM hψM' hgradM' u] with x hvv hvw
    rw [hvv, hvw, smul_eq_mul, smul_eq_mul]
    ring
  exact W1p.setIntegral_sq_mul_norm_gradient_sq_le_of_pointwise hlam u hψ hψM hgradM hE hpt hF.le

end PDE

end TauCeti
