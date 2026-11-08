/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Liouville.Action

/-!
# The symplectic form in action-angle coordinates

Let `σ` be a symplectic form on a boundaryless manifold `M`, and let `F : M → (ι → ℝ)` be a smooth
family of pairwise Poisson-commuting functions with complete Hamiltonian vector fields, with the
conventions `ι_{X_f} σ = df` and `{f, g} = σ(X_f, X_g) = df(X_g)`. Their flows generate an action
`v • y` of `ι → ℝ` on `M` (`TauCeti.SmoothTwoForm.IsSymplectic.hamiltonianFlowAction`).

Let `s` be a local section of `F`, `F (s c) = c`. Sweeping it by the action gives the map
`P (v, c) = v • s c`, and this file computes the pullback of `σ` along it:

`P^* σ = ∑ᵢ dvᵢ ∧ dcᵢ + pr^* (s^* σ)`.

Indeed the `v`-directions are the Hamiltonian vectors `X_{Fᵢ}`, which pair with each other to the
vanishing brackets `{Fᵢ, Fⱼ}` and with a vector `Y` to `dFᵢ(Y)`, while the action of `v` is
symplectic and preserves `F`. So the sweep of an isotropic section, `s^* σ = 0`, pulls `σ` back to
the standard form `∑ᵢ dvᵢ ∧ dcᵢ`.

Now let `λ⁽ⁱ⁾` be a differentiable family of periods along `s`, `λ⁽ⁱ⁾(c) • s c = s c`, and let
`Aᵢ` be corresponding action functions, `dAᵢ = (2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ`. Near a compact regular
component of a level, both are provided by
`TauCeti.SmoothTwoForm.IsSymplectic.exists_isLocalDiffeomorphAt_action_of_isCompact`. The
*angle map*

`Q (θ, c) = ((2π)⁻¹ ∑ᵢ θᵢ λ⁽ⁱ⁾(c)) • s c`

is `2π`-periodic in each angle `θᵢ`, and it pulls `σ` back to

`Q^* σ = ∑ᵢ dθᵢ ∧ dAᵢ + pr^* (s^* σ)`.

The terms in which `θ` multiplies the derivative of `λ⁽ⁱ⁾` cancel because the period one-forms
`∑ⱼ λ⁽ⁱ⁾ⱼ dcⱼ` are closed
(`TauCeti.SmoothTwoForm.IsSymplectic.fderiv_dotProduct_comm_of_mem_hamiltonianFlowStabilizer`).
Finally, writing the values as `c = g(I)` for a local right inverse `g` of the action map `A`, the
map `R (θ, I) = Q (θ, g I)` pulls `σ` back to

`R^* σ = ∑ᵢ dθᵢ ∧ dIᵢ + pr^* ((s ∘ g)^* σ)`,

which is `∑ᵢ dθᵢ ∧ dIᵢ` when `s` is isotropic: the coordinates `(θ, I)` are canonical. All
statements are pointwise and need differentiability only at the point considered. The existence of
an isotropic section and the descent of `θ` to the torus `(ℝ / 2πℤ)^ι` are not treated here.

## Main results

All in the namespace `TauCeti.SmoothTwoForm.IsSymplectic`:

* `mfderiv_hamiltonianFlowAction_section_apply`: the derivative of the sweep `(v, c) ↦ v • s c`.
* `eval₂_mfderiv_hamiltonianFlowAction_section`: the sweep pulls `σ` back to
  `∑ᵢ dvᵢ ∧ dcᵢ + pr^* (s^* σ)`; `eval₂_mfderiv_hamiltonianFlowAction_section_of_isotropic`: for an
  isotropic section, to `∑ᵢ dvᵢ ∧ dcᵢ`.
* `eval₂_mfderiv_hamiltonianFlowAction_angle`: the angle map pulls `σ` back to
  `∑ᵢ dθᵢ ∧ dAᵢ + pr^* (s^* σ)`.
* `hamiltonianFlowAction_angle_add_two_pi_mul`: the angle map is `2π`-periodic in each angle.
* `eval₂_mfderiv_hamiltonianFlowAction_actionAngle`: in the coordinates `(θ, I)`, `σ` is
  `∑ᵢ dθᵢ ∧ dIᵢ + pr^* ((s ∘ g)^* σ)`;
  `eval₂_mfderiv_hamiltonianFlowAction_actionAngle_of_isotropic`: for an isotropic section, it is
  `∑ᵢ dθᵢ ∧ dIᵢ`.

## References

* V. I. Arnold, *Mathematical Methods of Classical Mechanics*, 2nd ed., Graduate Texts in
  Mathematics 60, Springer, 1989, Section 50 (action-angle variables).
* J. J. Duistermaat, *On global action-angle coordinates*, Comm. Pure Appl. Math. 33 (1980),
  687–706, Section 1.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 18.4.
-/

public section

open Set Filter Module Topology Function Real
open ContinuousLinearMap (proj)
open scoped Manifold ContDiff Matrix

namespace TauCeti

namespace SmoothTwoForm

namespace IsSymplectic

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless] [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M] [BoundarylessManifold I M]
  {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  {ι : Type*} [Fintype ι] {F : M → ι → ℝ} (hF : ContMDiff I 𝓘(ℝ, ι → ℝ) ∞ F)
  (hcomm : ∀ i j x, σ.poissonBracket (F · i) (F · j) x = 0)
  (hc : ∀ i, IsCompleteVectorField (σ.hamiltonianVectorField (F · i)))
  {s : (ι → ℝ) → M} {p : ι → (ι → ℝ) → ι → ℝ} {A : (ι → ℝ) → ι → ℝ} {c : ι → ℝ}

include hσ hF hcomm hc

/-! ### Sweeping a section by the Hamiltonian flow action -/

/-- **The derivative of the sweep of a section.** The map `(v, c) ↦ v • s c` has derivative
`(a, b) ↦ ∑ᵢ aᵢ X_{Fᵢ}(v • s c) + d(v •)(ds b)` at `(v, c)`. -/
theorem mfderiv_hamiltonianFlowAction_section_apply (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c)
    (v a b : ι → ℝ) :
    mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
        (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul (s q.2))
        (v, c) (a, b) =
      ∑ i, a i • σ.hamiltonianVectorField (F · i)
          ((hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c)) +
        mfderiv I I (hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c)
          (mfderiv 𝓘(ℝ, ι → ℝ) I s c b) := by
  have hGd : MDifferentiableAt (𝓘(ℝ, ι → ℝ).prod I) I
      (fun q : (ι → ℝ) × M ↦ (hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul q.2) (v, s c) :=
    (hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).mdifferentiableAt (by simp)
  have hPd : MDifferentiableAt (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
      (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul (s q.2))
      (v, c) :=
    hGd.comp (v, c) (mdifferentiableAt_fst.prodMk (hs.comp (v, c) mdifferentiableAt_snd))
  have hΦ : MDifferentiableAt I I (hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c) :=
    (hσ.hamiltonianFlowAction hF hcomm hc v).toMul.contMDiff.mdifferentiableAt (by simp)
  rw [mfderiv_prod_eq_add_apply (v := ((a, b) : (ι → ℝ) × (ι → ℝ))) hPd]
  congr 1
  · exact hσ.mfderiv_hamiltonianFlowAction_apply hF hcomm hc (s c) v a
  · exact mfderiv_comp_apply c hΦ hs b

/-- **The sweep of a section pulls `σ` back to `∑ᵢ dvᵢ ∧ dcᵢ + pr^* (s^* σ)`.** Let `s` be a local
section of `F` near `c`, differentiable at `c`. The derivative of the sweep `(v, c) ↦ v • s c`
carries `(a, b)` and `(a', b')` to vectors whose `σ`-pairing is
`a ⬝ᵥ b' - a' ⬝ᵥ b + σ(ds b, ds b')`. -/
theorem eval₂_mfderiv_hamiltonianFlowAction_section (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c)
    (hFs : ∀ᶠ c' in 𝓝 c, F (s c') = c') (v a b a' b' : ι → ℝ) :
    SmoothBundleForm.eval₂ σ ((hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c))
        (mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
          (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul (s q.2))
          (v, c) (a, b))
        (mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
          (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul (s q.2))
          (v, c) (a', b')) =
      a ⬝ᵥ b' - a' ⬝ᵥ b +
        SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
          (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') := by
  rw [hσ.mfderiv_hamiltonianFlowAction_section_apply hF hcomm hc hs,
    hσ.mfderiv_hamiltonianFlowAction_section_apply hF hcomm hc hs]
  have hΦ : MDifferentiableAt I I (hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c) :=
    (hσ.hamiltonianFlowAction hF hcomm hc v).toMul.contMDiff.mdifferentiableAt (by simp)
  -- The action of `v` is symplectic: it preserves the pairing of `ds b` and `ds b'`.
  have hΦσ (u w : TangentSpace I (s c)) :
      SmoothBundleForm.eval₂ σ ((hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c))
          (mfderiv I I (hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c) u)
          (mfderiv I I (hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c) w) =
        SmoothBundleForm.eval₂ σ (s c) u w := by
    have h := SmoothForm.eval₂_mpullback _
      (hσ.hamiltonianFlowAction hF hcomm hc v).toMul.contMDiff σ (s c) u w
    rw [hσ.mpullback_hamiltonianFlowAction] at h
    exact h.symm
  set z := (hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c) with hz
  set B : LinearMap.BilinForm ℝ (TangentSpace I z) := SmoothForm.bilinFormAt σ z with hB
  have hFd : MDifferentiableAt I 𝓘(ℝ, ι → ℝ) F z := hF.mdifferentiableAt (by simp)
  -- `σ(X_{Fᵢ}, w) = dFᵢ(w)`, and `σ(X_{Fᵢ}, X_{Fₖ}) = {Fᵢ, Fₖ} = 0`.
  have hXv (i : ι) (w : TangentSpace I z) :
      B (σ.hamiltonianVectorField (F · i) z) w = mfderiv I 𝓘(ℝ, ι → ℝ) F z w i := by
    rw [hB, SmoothForm.bilinFormAt_apply,
      hσ.isNondegenerate.eval₂_hamiltonianVectorField_eq_mfderiv_apply hFd]
  have hvX (i : ι) (w : TangentSpace I z) :
      B w (σ.hamiltonianVectorField (F · i) z) = -mfderiv I 𝓘(ℝ, ι → ℝ) F z w i := by
    rw [← hXv, hB, SmoothForm.bilinFormAt_apply, SmoothForm.bilinFormAt_apply,
      SmoothBundleForm.eval₂_swap]
  have hFX (i k : ι) :
      mfderiv I 𝓘(ℝ, ι → ℝ) F z (σ.hamiltonianVectorField (F · k) z) i = 0 := by
    rw [← hXv, hB, SmoothForm.bilinFormAt_apply, ← poissonBracket_def]
    exact hcomm i k z
  -- `dF ∘ d(v •) ∘ ds = id`, since `F (v • s c') = F (s c') = c'` near `c`.
  have hFΦs (u : ι → ℝ) :
      mfderiv I 𝓘(ℝ, ι → ℝ) F z
        (mfderiv I I (hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c)
          (mfderiv 𝓘(ℝ, ι → ℝ) I s c u)) = u := by
    have hid : (F ∘ (hσ.hamiltonianFlowAction hF hcomm hc v).toMul ∘ s) =ᶠ[𝓝 c] id :=
      hFs.mono fun c' h ↦ by
        simp only [comp_apply, id, hσ.apply_hamiltonianFlowAction hF hcomm hc, h]
    have h := hid.mfderiv_eq (I := 𝓘(ℝ, ι → ℝ)) (I' := 𝓘(ℝ, ι → ℝ))
    rw [mfderiv_comp c hFd (hΦ.comp c hs), mfderiv_comp c hΦ hs, mfderiv_id] at h
    exact congrArg (fun L : (ι → ℝ) →L[ℝ] (ι → ℝ) ↦ L u) h
  rw [← SmoothForm.bilinFormAt_apply, ← hB, ← hΦσ]
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, hXv, hvX, hFX, hFΦs, smul_eq_mul, mul_zero, Finset.sum_const_zero,
    zero_add, mul_neg, Finset.sum_neg_distrib, dotProduct]
  rw [hB, SmoothForm.bilinFormAt_apply]
  ring

/-- **The sweep of an isotropic section pulls `σ` back to `∑ᵢ dvᵢ ∧ dcᵢ`.** If moreover the
section `s` is isotropic at `c`, the `σ`-pairing of the images of `(a, b)` and `(a', b')` under the
derivative of the sweep is `a ⬝ᵥ b' - a' ⬝ᵥ b`. -/
theorem eval₂_mfderiv_hamiltonianFlowAction_section_of_isotropic
    (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c) (hFs : ∀ᶠ c' in 𝓝 c, F (s c') = c')
    (hiso : ∀ b b', SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c b)
      (mfderiv 𝓘(ℝ, ι → ℝ) I s c b') = 0)
    (v a b a' b' : ι → ℝ) :
    SmoothBundleForm.eval₂ σ ((hσ.hamiltonianFlowAction hF hcomm hc v).toMul (s c))
        (mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
          (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul (s q.2))
          (v, c) (a, b))
        (mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
          (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul (s q.2))
          (v, c) (a', b')) =
      a ⬝ᵥ b' - a' ⬝ᵥ b := by
  rw [hσ.eval₂_mfderiv_hamiltonianFlowAction_section hF hcomm hc hs hFs, add_eq_left]
  exact hiso b b'

/-! ### Angle coordinates -/

/-- The derivative of the angle map `(θ, c) ↦ ((2π)⁻¹ ∑ᵢ θᵢ λ⁽ⁱ⁾(c)) • s c` is the derivative of
the sweep, applied to the derivative `(a, b) ↦ ((2π)⁻¹ ∑ᵢ (aᵢ λ⁽ⁱ⁾(c) + θᵢ Dλ⁽ⁱ⁾(b)), b)` of the
change of variables `(θ, c) ↦ ((2π)⁻¹ ∑ᵢ θᵢ λ⁽ⁱ⁾(c), c)`. -/
private theorem mdifferentiableAt_and_mfderiv_hamiltonianFlowAction_angle
    (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c) (hp : ∀ i, DifferentiableAt ℝ (p i) c)
    (θ : ι → ℝ) :
    MDifferentiableAt (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
        (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc
          ((2 * π)⁻¹ • ∑ i, q.1 i • p i q.2)).toMul (s q.2)) (θ, c) ∧
      ∀ a b : ι → ℝ, mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
        (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc
          ((2 * π)⁻¹ • ∑ i, q.1 i • p i q.2)).toMul (s q.2)) (θ, c) (a, b) =
      mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
        (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul (s q.2))
        ((2 * π)⁻¹ • ∑ i, θ i • p i c, c)
        ((2 * π)⁻¹ • ∑ i, (a i • p i c + θ i • fderiv ℝ (p i) c b), b) := by
  -- The change of variables `(θ, c) ↦ ((2π)⁻¹ ∑ᵢ θᵢ λ⁽ⁱ⁾(c), c)` and its derivative.
  set W : (ι → ℝ) × (ι → ℝ) →L[ℝ] ι → ℝ := (2 * π)⁻¹ • ∑ i,
    (θ i • (fderiv ℝ (p i) c).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)) +
      ((proj i : (ι → ℝ) →L[ℝ] ℝ).comp (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))).smulRight
        (p i c)) with hW
  have hw : HasFDerivAt (fun q : (ι → ℝ) × (ι → ℝ) ↦ (2 * π)⁻¹ • ∑ i, q.1 i • p i q.2) W
      (θ, c) := by
    have hterm (i : ι) : HasFDerivAt (fun q : (ι → ℝ) × (ι → ℝ) ↦ q.1 i • p i q.2)
        (θ i • (fderiv ℝ (p i) c).comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)) +
          ((proj i : (ι → ℝ) →L[ℝ] ℝ).comp
            (ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ))).smulRight (p i c)) (θ, c) :=
      ((proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.comp (θ, c) hasFDerivAt_fst).smul
        ((hp i).hasFDerivAt.comp (θ, c) hasFDerivAt_snd)
    exact (HasFDerivAt.fun_sum (u := Finset.univ) fun i _ ↦ hterm i).const_smul ((2 * π)⁻¹ : ℝ)
  have hg : HasMFDerivAt (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ))
      (fun q : (ι → ℝ) × (ι → ℝ) ↦ ((2 * π)⁻¹ • ∑ i, q.1 i • p i q.2, q.2)) (θ, c)
      (W.prod (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ))) := by
    have h := hasMFDerivAt_iff_hasFDerivAt.2 (hw.prodMk hasFDerivAt_snd)
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  -- The sweep is differentiable, so the angle map is differentiable by the chain rule.
  have hGd : MDifferentiableAt (𝓘(ℝ, ι → ℝ).prod I) I
      (fun q : (ι → ℝ) × M ↦ (hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul q.2)
      ((2 * π)⁻¹ • ∑ i, θ i • p i c, s c) :=
    (hσ.contMDiff_hamiltonianFlowAction_uncurry hF hcomm hc).mdifferentiableAt (by simp)
  have hPd : MDifferentiableAt (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
      (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc q.1).toMul (s q.2))
      ((2 * π)⁻¹ • ∑ i, θ i • p i c, c) :=
    hGd.comp ((2 * π)⁻¹ • ∑ i, θ i • p i c, c)
      (mdifferentiableAt_fst.prodMk (hs.comp _ mdifferentiableAt_snd))
  have hQ := hPd.hasMFDerivAt.comp (θ, c) hg
  refine ⟨hQ.mdifferentiableAt, fun a b ↦ (congrArg (fun L ↦ L (a, b)) hQ.mfderiv).trans ?_⟩
  have hWab : W (a, b) = (2 * π)⁻¹ • ∑ i, (a i • p i c + θ i • fderiv ℝ (p i) c b) := by
    simp [hW, add_comm]
  -- The tangent spaces of the product model are `(ι → ℝ) × (ι → ℝ)` only after unfolding
  -- `TangentSpace`, so the composite is evaluated with `erw`.
  erw [ContinuousLinearMap.comp_apply]
  exact congrArg _ (Prod.ext hWab rfl)

/-- **The angle map pulls `σ` back to `∑ᵢ dθᵢ ∧ dAᵢ + pr^* (s^* σ)`.** Let `s` be a local section of
`F` near `c`, differentiable at `c`, let `λ⁽ⁱ⁾` be families of periods along `s`, differentiable at
`c`, and let `Aᵢ` have differential `(2π)⁻¹ ∑ⱼ λ⁽ⁱ⁾ⱼ(c) dcⱼ` at `c`. The derivative of the angle map
`(θ, c) ↦ ((2π)⁻¹ ∑ᵢ θᵢ λ⁽ⁱ⁾(c)) • s c` carries `(α, β)` and `(α', β')` to vectors whose
`σ`-pairing is `∑ᵢ (αᵢ dAᵢ(β') - α'ᵢ dAᵢ(β)) + σ(ds β, ds β')`. -/
theorem eval₂_mfderiv_hamiltonianFlowAction_angle (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s c)
    (hFs : ∀ᶠ c' in 𝓝 c, F (s c') = c') (hp : ∀ i, DifferentiableAt ℝ (p i) c)
    (hps : ∀ i, ∀ᶠ c' in 𝓝 c, p i c' ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c'))
    (hA : ∀ i, HasFDerivAt (fun c ↦ A c i)
      ((2 * π)⁻¹ • ∑ j, p i c j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) c)
    (θ α β α' β' : ι → ℝ) :
    SmoothBundleForm.eval₂ σ
        ((hσ.hamiltonianFlowAction hF hcomm hc ((2 * π)⁻¹ • ∑ i, θ i • p i c)).toMul (s c))
        (mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
          (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc
            ((2 * π)⁻¹ • ∑ i, q.1 i • p i q.2)).toMul (s q.2)) (θ, c) (α, β))
        (mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
          (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc
            ((2 * π)⁻¹ • ∑ i, q.1 i • p i q.2)).toMul (s q.2)) (θ, c) (α', β')) =
      ∑ i, (α i * fderiv ℝ (fun c ↦ A c i) c β' - α' i * fderiv ℝ (fun c ↦ A c i) c β) +
        SmoothBundleForm.eval₂ σ (s c) (mfderiv 𝓘(ℝ, ι → ℝ) I s c β)
          (mfderiv 𝓘(ℝ, ι → ℝ) I s c β') := by
  obtain ⟨-, hQ⟩ :=
    hσ.mdifferentiableAt_and_mfderiv_hamiltonianFlowAction_angle hF hcomm hc hs hp θ
  rw [hQ, hQ, hσ.eval₂_mfderiv_hamiltonianFlowAction_section hF hcomm hc hs hFs, add_left_inj]
  -- The terms in which `θ` multiplies `Dλ⁽ⁱ⁾` cancel, since the period one-forms are closed.
  have hsym (i : ι) : fderiv ℝ (p i) c β' ⬝ᵥ β = fderiv ℝ (p i) c β ⬝ᵥ β' :=
    hσ.fderiv_dotProduct_comm_of_mem_hamiltonianFlowStabilizer hF hcomm hc hs hFs (hp i) (hps i)
      β' β
  have hdA (i : ι) (u : ι → ℝ) :
      fderiv ℝ (fun c ↦ A c i) c u = (2 * π)⁻¹ * (p i c ⬝ᵥ u) := by
    rw [(hA i).fderiv]
    simp [dotProduct, Finset.mul_sum]
  simp only [hdA, smul_dotProduct, sum_dotProduct, add_dotProduct, smul_eq_mul, hsym]
  rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

/-- **The angle map is `2π`-periodic in each angle.** If the `λ⁽ⁱ⁾(c)` are periods of `s c`,
translating the angles `θ` by `2π n`, for an integer vector `n`, does not change the point
`((2π)⁻¹ ∑ᵢ θᵢ λ⁽ⁱ⁾(c)) • s c`. -/
theorem hamiltonianFlowAction_angle_add_two_pi_mul
    (hpc : ∀ i, p i c ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c)) (θ : ι → ℝ)
    (n : ι → ℤ) :
    (hσ.hamiltonianFlowAction hF hcomm hc
        ((2 * π)⁻¹ • ∑ i, (θ i + 2 * π * n i) • p i c)).toMul (s c) =
      (hσ.hamiltonianFlowAction hF hcomm hc ((2 * π)⁻¹ • ∑ i, θ i • p i c)).toMul (s c) := by
  have hsplit : (2 * π)⁻¹ • ∑ i, (θ i + 2 * π * n i) • p i c =
      (2 * π)⁻¹ • ∑ i, θ i • p i c + ∑ i, n i • p i c := by
    simp only [add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum, smul_smul,
      ← Int.cast_smul_eq_zsmul ℝ]
    congr 1
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
  have hn : ∑ i, n i • p i c ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c) :=
    AddSubgroup.sum_mem _ fun i _ ↦ AddSubgroup.zsmul_mem _ (hpc i) _
  rw [hsplit, hσ.hamiltonianFlowAction_add_apply hF hcomm hc,
    (hσ.mem_hamiltonianFlowStabilizer hF hcomm hc).1 hn]

/-! ### Action-angle coordinates -/

/-- **`σ = ∑ᵢ dθᵢ ∧ dIᵢ + pr^* ((s ∘ g)^* σ)` in the coordinates `(θ, I)`.** In the setting of
`eval₂_mfderiv_hamiltonianFlowAction_angle`, let `g` be a local right inverse of the action map
`A` near `y`, with derivative `G` at `y`, and put `c = g y`. The derivative of
`(θ, I) ↦ ((2π)⁻¹ ∑ᵢ θᵢ λ⁽ⁱ⁾(g I)) • s (g I)` carries `(α, β)` and `(α', β')` to vectors whose
`σ`-pairing is `α ⬝ᵥ β' - α' ⬝ᵥ β + σ(ds (G β), ds (G β'))`. -/
theorem eval₂_mfderiv_hamiltonianFlowAction_actionAngle {g : (ι → ℝ) → ι → ℝ}
    {G : (ι → ℝ) →L[ℝ] ι → ℝ} {y : ι → ℝ} (hg : HasFDerivAt g G y)
    (hAg : ∀ᶠ y' in 𝓝 y, A (g y') = y') (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s (g y))
    (hFs : ∀ᶠ c' in 𝓝 (g y), F (s c') = c') (hp : ∀ i, DifferentiableAt ℝ (p i) (g y))
    (hps : ∀ i, ∀ᶠ c' in 𝓝 (g y), p i c' ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c'))
    (hA : ∀ i, HasFDerivAt (fun c ↦ A c i)
      ((2 * π)⁻¹ • ∑ j, p i (g y) j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) (g y))
    (θ α β α' β' : ι → ℝ) :
    SmoothBundleForm.eval₂ σ
        ((hσ.hamiltonianFlowAction hF hcomm hc ((2 * π)⁻¹ • ∑ i, θ i • p i (g y))).toMul (s (g y)))
        (mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
          (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc
            ((2 * π)⁻¹ • ∑ i, q.1 i • p i (g q.2))).toMul (s (g q.2))) (θ, y) (α, β))
        (mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
          (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc
            ((2 * π)⁻¹ • ∑ i, q.1 i • p i (g q.2))).toMul (s (g q.2))) (θ, y) (α', β')) =
      α ⬝ᵥ β' - α' ⬝ᵥ β +
        SmoothBundleForm.eval₂ σ (s (g y)) (mfderiv 𝓘(ℝ, ι → ℝ) I s (g y) (G β))
          (mfderiv 𝓘(ℝ, ι → ℝ) I s (g y) (G β')) := by
  -- The coordinates factor as the angle map after `(θ, I) ↦ (θ, g I)`.
  have hk₀ : HasFDerivAt (fun q : (ι → ℝ) × (ι → ℝ) ↦ (q.1, g q.2))
      ((ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).prod
        (G.comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) (θ, y) :=
    hasFDerivAt_fst.prodMk (hg.comp (θ, y) hasFDerivAt_snd)
  have hk : HasMFDerivAt (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ))
      (fun q : (ι → ℝ) × (ι → ℝ) ↦ (q.1, g q.2)) (θ, y)
      ((ContinuousLinearMap.fst ℝ (ι → ℝ) (ι → ℝ)).prod
        (G.comp (ContinuousLinearMap.snd ℝ (ι → ℝ) (ι → ℝ)))) := by
    have h := hasMFDerivAt_iff_hasFDerivAt.2 hk₀
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  obtain ⟨hQd, -⟩ :=
    hσ.mdifferentiableAt_and_mfderiv_hamiltonianFlowAction_angle hF hcomm hc hs hp θ
  have hR (a b : ι → ℝ) :
      mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
        (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc
          ((2 * π)⁻¹ • ∑ i, q.1 i • p i (g q.2))).toMul (s (g q.2))) (θ, y) (a, b) =
      mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
        (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc
          ((2 * π)⁻¹ • ∑ i, q.1 i • p i q.2)).toMul (s q.2)) (θ, g y) (a, G b) :=
    congrArg (fun L ↦ L (a, b)) (hQd.hasMFDerivAt.comp (θ, y) hk).mfderiv
  rw [hR, hR]
  rw [hσ.eval₂_mfderiv_hamiltonianFlowAction_angle hF hcomm hc hs hFs hp hps hA, add_left_inj]
  -- `dAᵢ ∘ G = dIᵢ`, since `A ∘ g` is the identity near `y`.
  have hAG (i : ι) (u : ι → ℝ) : fderiv ℝ (fun c ↦ A c i) (g y) (G u) = u i := by
    have h₁ : HasFDerivAt (fun y' ↦ A (g y') i) ((proj i : (ι → ℝ) →L[ℝ] ℝ)) y :=
      (proj i : (ι → ℝ) →L[ℝ] ℝ).hasFDerivAt.congr_of_eventuallyEq
        (hAg.mono fun y' h ↦ by simp [h])
    rw [(hA i).fderiv]
    exact congrArg (fun L : (ι → ℝ) →L[ℝ] ℝ ↦ L u) (((hA i).comp y hg).unique h₁)
  simp only [hAG, dotProduct, Finset.sum_sub_distrib]

/-- **`σ = ∑ᵢ dθᵢ ∧ dIᵢ` in action-angle coordinates.** If moreover the section `s` is isotropic
at `g y`, the coordinates `(θ, I)` of `eval₂_mfderiv_hamiltonianFlowAction_actionAngle` are
canonical at `(θ, y)`: the `σ`-pairing of the images of `(α, β)` and `(α', β')` under their
derivative is `α ⬝ᵥ β' - α' ⬝ᵥ β`. -/
theorem eval₂_mfderiv_hamiltonianFlowAction_actionAngle_of_isotropic {g : (ι → ℝ) → ι → ℝ}
    {G : (ι → ℝ) →L[ℝ] ι → ℝ} {y : ι → ℝ} (hg : HasFDerivAt g G y)
    (hAg : ∀ᶠ y' in 𝓝 y, A (g y') = y') (hs : MDifferentiableAt 𝓘(ℝ, ι → ℝ) I s (g y))
    (hFs : ∀ᶠ c' in 𝓝 (g y), F (s c') = c') (hp : ∀ i, DifferentiableAt ℝ (p i) (g y))
    (hps : ∀ i, ∀ᶠ c' in 𝓝 (g y), p i c' ∈ hσ.hamiltonianFlowStabilizer hF hcomm hc (s c'))
    (hA : ∀ i, HasFDerivAt (fun c ↦ A c i)
      ((2 * π)⁻¹ • ∑ j, p i (g y) j • (proj j : (ι → ℝ) →L[ℝ] ℝ)) (g y))
    (hiso : ∀ b b', SmoothBundleForm.eval₂ σ (s (g y)) (mfderiv 𝓘(ℝ, ι → ℝ) I s (g y) b)
      (mfderiv 𝓘(ℝ, ι → ℝ) I s (g y) b') = 0)
    (θ α β α' β' : ι → ℝ) :
    SmoothBundleForm.eval₂ σ
        ((hσ.hamiltonianFlowAction hF hcomm hc ((2 * π)⁻¹ • ∑ i, θ i • p i (g y))).toMul (s (g y)))
        (mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
          (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc
            ((2 * π)⁻¹ • ∑ i, q.1 i • p i (g q.2))).toMul (s (g q.2))) (θ, y) (α, β))
        (mfderiv (𝓘(ℝ, ι → ℝ).prod 𝓘(ℝ, ι → ℝ)) I
          (fun q : (ι → ℝ) × (ι → ℝ) ↦ (hσ.hamiltonianFlowAction hF hcomm hc
            ((2 * π)⁻¹ • ∑ i, q.1 i • p i (g q.2))).toMul (s (g q.2))) (θ, y) (α', β')) =
      α ⬝ᵥ β' - α' ⬝ᵥ β := by
  rw [hσ.eval₂_mfderiv_hamiltonianFlowAction_actionAngle hF hcomm hc hg hAg hs hFs hp hps hA,
    add_eq_left]
  exact hiso (G β) (G β')

end IsSymplectic

end SmoothTwoForm

end TauCeti
