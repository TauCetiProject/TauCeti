/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Torus
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Angle
public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
public import TauCeti.Geometry.Symplectic.Manifold.Moser.Path
import TauCeti.Geometry.Manifold.DifferentialForm.Wedge.Leibniz
import TauCeti.Geometry.Symplectic.Liouville.Volume
import TauCeti.Geometry.Symplectic.Manifold.Surface

/-!
# Moser's theorem on the two-torus

On the two-torus `T² = (ℝ / 2πℤ)²`, with angles `θ = x₀` and `φ = x₁` and area form
`dθ ∧ dφ = torusVolumeForm (fun _ ↦ 2π)`, this file compares two paths of symplectic forms
starting at `dθ ∧ dφ`. Moser's theorem pulls a path of symplectic forms back to its initial form by
an isotopy when the velocity of the path is exact. The two paths separate this exactness
hypothesis from symplecticity and from equality of total areas.

* **An exact path.** On the torus `d (sin θ dφ) = cos θ dθ ∧ dφ`
  (`TauCeti.mextDeriv_funSMulₗ_torusAngleSin_torusTimeForm`), so the path
  `ω_s = dθ ∧ dφ + (s / 2) d (sin θ dφ) = (1 + (s / 2) cos θ) dθ ∧ dφ`
  (`TauCeti.twoTorusMoserForm`) has exact velocity
  (`TauCeti.coe_twoTorusMoserForm_sub_twoTorusMoserForm_zero`). It is symplectic for `|s| < 2`
  (`TauCeti.isSymplectic_twoTorusMoserForm`), since on a surface a two-form is symplectic exactly
  when it vanishes nowhere. By Moser's theorem along an exact path there is a smooth isotopy
  pulling it back to `dθ ∧ dφ` (`TauCeti.exists_isotopy_mpullback_twoTorusMoserForm`), and every
  `ω_s` with `s ∈ [0, 1]` is diffeomorphic to `dθ ∧ dφ`
  (`TauCeti.exists_diffeomorph_mpullback_twoTorusMoserForm`).
* **A rescaled path.** The forms `(1 + t) dθ ∧ dφ` are symplectic for `t > -1`, but their
  velocity `dθ ∧ dφ` is not exact (`TauCeti.mextDeriv_ne_torusVolumeForm_fin_two`). Their total
  areas differ: a differentiable homeomorphism pulling `(1 + t) dθ ∧ dφ` back to `dθ ∧ dφ` would
  carry Liouville measure to Liouville measure, so `|1 + t| = 1`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.abs_pow_eq_one_of_mpullback_smul_eq`). Hence for
  `t ≠ 0, -2` there is no such map (`TauCeti.not_exists_mpullback_smul_torusVolumeForm_eq`), and in
  particular no isotopy pulls this path back to `dθ ∧ dφ`.

## Main definitions

* `TauCeti.twoTorusMoserForm s`: the form `(1 + (s / 2) cos θ) dθ ∧ dφ`.

## Main results

* `TauCeti.mextDeriv_funSMulₗ_torusAngleSin_torusTimeForm`: `d (sin θ dφ) = cos θ dθ ∧ dφ`.
* `TauCeti.isSymplectic_twoTorusMoserForm`: `ω_s` is symplectic for `|s| < 2`.
* `TauCeti.exists_isotopy_mpullback_twoTorusMoserForm`,
  `TauCeti.exists_diffeomorph_mpullback_twoTorusMoserForm`: the Moser isotopy of the exact path.
* `TauCeti.mextDeriv_ne_torusVolumeForm_fin_two`: the area form of a two-torus is not exact.
* `TauCeti.not_exists_mpullback_smul_torusVolumeForm_eq`: `(1 + t) dθ ∧ dφ` is not diffeomorphic
  to `dθ ∧ dφ` for `t ≠ 0, -2`.

## References

* J. Moser, *On the volume elements on a manifold*, Transactions of the American Mathematical
  Society 120 (1965), 286–294.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.2 (Moser isotopy).
-/

public section

open Set
open scoped ContDiff Manifold Real

namespace TauCeti

/-- The period `2π` is positive. -/
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

section TwoTorus

/-- **The exact cosine form.** On the two-torus with angles `θ = x₀` and `φ = x₁`,
`d (sin θ dφ) = cos θ dθ ∧ dφ`. -/
theorem mextDeriv_funSMulₗ_torusAngleSin_torusTimeForm :
    mextDeriv (SmoothForm.funSMulₗ (torusAngleSin (Fin 2) 0)
        (torusTimeForm (fun _ : Fin 2 ↦ 2 * π) 1)).val =
      (SmoothForm.funSMulₗ (torusAngleCos (Fin 2) 0)
        (torusVolumeForm fun _ : Fin 2 ↦ 2 * π)).val := by
  funext x
  ext v
  have hv : v = ![v 0, v 1] := funext fun i ↦ by fin_cases i <;> rfl
  have hd : mextDeriv (torusTimeForm (fun _ : Fin 2 ↦ 2 * π) 1).val = 0 :=
    (SmoothForm.isClosed_def _).1 (isClosed_torusTimeForm _ 1)
  rw [hv, SmoothForm.coe_funSMulₗ, mextDeriv_fun_smul_apply
    ((torusAngleSin (Fin 2) 0).contMDiff.mdifferentiableAt (by simp))
    ((torusTimeForm (fun _ : Fin 2 ↦ 2 * π) 1).mdifferentiableAt x),
    hd]
  simp only [mvfderiv_torusAngleSin, torusTimeForm_apply, SmoothForm.coe_funSMulₗ,
    ContinuousAlternatingMap.smul_apply, torusVolumeForm_fin_two_apply, Matrix.cons_val_zero,
    Pi.zero_apply, ContinuousAlternatingMap.coe_zero, mul_zero, add_zero, smul_eq_mul]
  ring

/-- The area form `dt₀ ∧ dt₁` of a two-torus is nondegenerate: it vanishes nowhere on a
surface. -/
theorem isNondegenerate_torusVolumeForm_fin_two (p : Fin 2 → ℝ) [∀ i, Fact (0 < p i)] :
    SmoothTwoForm.IsNondegenerate (torusVolumeForm p) :=
  (SmoothTwoForm.isNondegenerate_iff_forall_ne_zero_of_finrank_eq_two
    (Module.finrank_fin_fun ℝ)).2 (torusVolumeForm_apply_ne_zero p)

/-- **The area form of a two-torus is not exact.** No one-form `α` has `dα = dt₀ ∧ dt₁`, since
the torus is a closed surface and `dt₀ ∧ dt₁` vanishes nowhere
(`TauCeti.SmoothTwoForm.IsNondegenerate.mextDeriv_ne`). So the path `(1 + t) dθ ∧ dφ`, whose
velocity is `dθ ∧ dφ`, fails the exactness hypothesis of Moser's theorem. -/
theorem mextDeriv_ne_torusVolumeForm_fin_two (p : Fin 2 → ℝ) [∀ i, Fact (0 < p i)]
    (α : SmoothForm (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (∀ i, AddCircle (p i)) ℝ 1) :
    mextDeriv α.val ≠ (torusVolumeForm p).val :=
  (isNondegenerate_torusVolumeForm_fin_two p).mextDeriv_ne α

/-- The path `ω_s = dθ ∧ dφ + (s / 2) d (sin θ dφ) = (1 + (s / 2) cos θ) dθ ∧ dφ` of two-forms
on the two-torus. Every `ω_s` has the class of `ω_0 = dθ ∧ dφ`, and `ω_s` is symplectic for
`|s| < 2`. -/
noncomputable def twoTorusMoserForm (s : ℝ) :
    SmoothTwoForm (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) (∀ _ : Fin 2, AddCircle (2 * π)) :=
  torusVolumeForm (fun _ : Fin 2 ↦ 2 * π) +
    (s / 2) • SmoothForm.funSMulₗ (torusAngleCos (Fin 2) 0) (torusVolumeForm fun _ ↦ 2 * π)

/-- The form `ω_s` is `(1 + (s / 2) cos θ) dθ ∧ dφ`. -/
theorem twoTorusMoserForm_apply (s : ℝ) (x : ∀ _ : Fin 2, AddCircle (2 * π)) :
    (twoTorusMoserForm s).val x =
      (1 + s / 2 * torusAngleCos (Fin 2) 0 x) • (torusVolumeForm fun _ : Fin 2 ↦ 2 * π).val x := by
  simp only [twoTorusMoserForm, Submodule.coe_add, Submodule.coe_smul, SmoothForm.coe_funSMulₗ,
    Pi.add_apply, Pi.smul_apply, add_smul, one_smul, smul_smul]

/-- The path starts at the area form `ω_0 = dθ ∧ dφ`. -/
@[simp]
theorem twoTorusMoserForm_zero :
    twoTorusMoserForm 0 = torusVolumeForm (fun _ : Fin 2 ↦ 2 * π) := by
  simp [twoTorusMoserForm]

/-- The velocity of the path is exact: `ω_s - ω_0 = d ((s / 2) sin θ dφ)`. -/
theorem coe_twoTorusMoserForm_sub_twoTorusMoserForm_zero (s : ℝ) :
    (twoTorusMoserForm s - twoTorusMoserForm 0).val =
      mextDeriv ((s / 2) • SmoothForm.funSMulₗ (torusAngleSin (Fin 2) 0)
        (torusTimeForm (fun _ : Fin 2 ↦ 2 * π) 1)).val := by
  rw [twoTorusMoserForm_zero, twoTorusMoserForm, add_sub_cancel_left, Submodule.coe_smul,
    Submodule.coe_smul, mextDeriv_smul, mextDeriv_funSMulₗ_torusAngleSin_torusTimeForm]

/-- **The path is symplectic** for `|s| < 2`: on a surface a two-form is symplectic exactly when it
vanishes nowhere, and `1 + (s / 2) cos θ ≥ 1 - |s| / 2 > 0`. -/
theorem isSymplectic_twoTorusMoserForm {s : ℝ} (hs : |s| < 2) :
    (twoTorusMoserForm s).IsSymplectic := by
  rw [SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two (Module.finrank_fin_fun ℝ)]
  intro x
  rw [twoTorusMoserForm_apply]
  refine smul_ne_zero ?_ (torusVolumeForm_apply_ne_zero _ x)
  have hc := abs_torusAngleCos_le_one (0 : Fin 2) x
  have : |s / 2 * torusAngleCos (Fin 2) 0 x| < 1 := by
    rw [abs_mul, abs_div, abs_two]
    nlinarith [abs_nonneg s, abs_nonneg (torusAngleCos (Fin 2) 0 x)]
  have := neg_abs_le (s / 2 * torusAngleCos (Fin 2) 0 x)
  linarith

/-- The path is the segment from `ω_0` to `ω_1`: `ω_s = ω_0 + s • (ω_1 - ω_0)`. -/
theorem twoTorusMoserForm_zero_add_smul_sub (s : ℝ) :
    twoTorusMoserForm 0 + s • (twoTorusMoserForm 1 - twoTorusMoserForm 0) =
      twoTorusMoserForm s := by
  simp only [twoTorusMoserForm, zero_div, zero_smul, add_zero, add_sub_cancel_left, smul_smul]
  ring_nf

/-- The segment from `ω_0` to `ω_1` is symplectic, the hypothesis of Moser's theorem along it. -/
private theorem isSymplectic_twoTorusMoserForm_zero_add_smul_sub {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    (twoTorusMoserForm 0 + s • (twoTorusMoserForm 1 - twoTorusMoserForm 0)).IsSymplectic := by
  rw [twoTorusMoserForm_zero_add_smul_sub]
  exact isSymplectic_twoTorusMoserForm (by rw [abs_of_nonneg hs.1]; linarith [hs.2])

/-- **Moser's isotopy on the two-torus.** There is a smooth isotopy `ψ_t` of the two-torus, starting
at the identity, with `ψ_t^* ω_{c(t)} = dθ ∧ dφ` for the smooth step `c = Real.smoothTransition`,
which runs from `c = 0` on `t ≤ 0` to `c = 1` on `t ≥ 1` through every value in between. -/
theorem exists_isotopy_mpullback_twoTorusMoserForm :
    ∃ ψ : ℝ → (∀ _ : Fin 2, AddCircle (2 * π)) ≃ₘ⟮ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ),
        ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)⟯ (∀ _ : Fin 2, AddCircle (2 * π)),
      ContMDiff (𝓘(ℝ, ℝ).prod (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)))
          (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) ∞
          (fun p : ℝ × (∀ _ : Fin 2, AddCircle (2 * π)) ↦ ψ p.1 p.2) ∧
        (∀ x, ψ 0 x = x) ∧
        ∀ t, SmoothForm.mpullback (ψ t) (ψ t).contMDiff
            (twoTorusMoserForm (Real.smoothTransition t)) = torusVolumeForm fun _ ↦ 2 * π := by
  have h := SmoothTwoForm.exists_isotopy_mpullback_add_smoothTransition_smul_eq
    (twoTorusMoserForm 0) (twoTorusMoserForm 1) _
    (coe_twoTorusMoserForm_sub_twoTorusMoserForm_zero 1)
    fun _ ↦ isSymplectic_twoTorusMoserForm_zero_add_smul_sub
  -- First recognize the segment as the path, then its initial form as the area form.
  simp only [twoTorusMoserForm_zero_add_smul_sub] at h
  simpa only [twoTorusMoserForm_zero] using h

/-- **Moser's theorem along the path, pointwise.** For every `s ∈ [0, 1]` a diffeomorphism of the
two-torus pulls `ω_s = (1 + (s / 2) cos θ) dθ ∧ dφ` back to `dθ ∧ dφ`. -/
theorem exists_diffeomorph_mpullback_twoTorusMoserForm {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ∃ φ : (∀ _ : Fin 2, AddCircle (2 * π)) ≃ₘ⟮ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ),
        ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)⟯ (∀ _ : Fin 2, AddCircle (2 * π)),
      SmoothForm.mpullback φ φ.contMDiff (twoTorusMoserForm s) =
        torusVolumeForm fun _ ↦ 2 * π := by
  have h := SmoothTwoForm.exists_diffeomorph_mpullback_add_smul_eq (twoTorusMoserForm 0)
    (twoTorusMoserForm 1) _ (coe_twoTorusMoserForm_sub_twoTorusMoserForm_zero 1)
    (fun _ ↦ isSymplectic_twoTorusMoserForm_zero_add_smul_sub) hs
  -- First recognize the segment as the path, then its initial form as the area form.
  simp only [twoTorusMoserForm_zero_add_smul_sub] at h
  simpa only [twoTorusMoserForm_zero] using h

/-- **The rescaled path is not a Moser path.** The forms `(1 + t) dt₀ ∧ dt₁` on a two-torus have
total area `|1 + t|` times that of `dt₀ ∧ dt₁`, so for `t ≠ 0, -2` no differentiable
homeomorphism of the torus pulls `(1 + t) dt₀ ∧ dt₁` back to `dt₀ ∧ dt₁`. In particular no isotopy
`φ_t` satisfies `φ_t^* ((1 + t) dt₀ ∧ dt₁) = dt₀ ∧ dt₁` for `t ∈ [0, 1]`. -/
theorem not_exists_mpullback_smul_torusVolumeForm_eq (p : Fin 2 → ℝ) [∀ i, Fact (0 < p i)]
    {t : ℝ} (ht : t ≠ 0) (ht' : t ≠ -2) :
    ¬∃ Φ : (∀ i, AddCircle (p i)) ≃ₜ (∀ i, AddCircle (p i)),
      MDifferentiable (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ))
          (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) Φ ∧
        mpullback (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ))
            (ModelWithCorners.pi fun _ : Fin 2 ↦ 𝓘(ℝ)) Φ ((1 + t) • torusVolumeForm p).val =
          (torusVolumeForm p).val := by
  rintro ⟨Φ, hΦ, h⟩
  let _ : MeasurableSpace (∀ i, AddCircle (p i)) := borel _
  have : BorelSpace (∀ i, AddCircle (p i)) := ⟨rfl⟩
  have : Fact (Module.finrank ℝ (Fin 2 → ℝ) = 2 * 1) := ⟨by simp⟩
  have h1 := (isNondegenerate_torusVolumeForm_fin_two p).abs_pow_eq_one_of_mpullback_smul_eq
    (n := 1) Φ hΦ h
  rw [pow_one] at h1
  rcases abs_eq zero_le_one |>.1 h1 with h2 | h2
  · exact ht (by linarith)
  · exact ht' (by linarith)

end TwoTorus

end TauCeti
