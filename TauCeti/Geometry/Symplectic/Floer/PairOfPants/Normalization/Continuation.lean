/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Continuation
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.Geometry.Symplectic.Floer.PairOfPants.Energy.Continuation

/-!
# Normalizing the Hamiltonians of the pair of pants with continuation necks

A Hamiltonian is determined by its Hamiltonian vector field only up to a function of time, and
changing it by such a function changes its action by the time average. This file shows how the
energy identity of the pair of pants with continuation necks
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsContinuationPerturbation`)

`E(u) = ∫_S u^*ω + ∑ q, ±∫₀¹ H_q(t, x_q(t)) dt - ∫_S R_K(u)`

absorbs a change of normalization of its inner Hamiltonians `G_q` and of its outer Hamiltonians
`H_q`, for a manifold target `M` with a two-form `ω`, such as a closed symplectic manifold, and
for a symplectic vector space target. Only the outer Hamiltonians appear in the boundary term of
the identity, and correspondingly only the outer normalization survives in the curvature.

The perturbation `K = TauCeti.Floer.pairOfPantsContinuationPerturbation G H L` is additive in the
pair of inner and outer Hamiltonians, so replacing `G_q`, `H_q` by `G_q + c_q`, `H_q + d_q` adds
the perturbation `k` with continuation necks from the target-independent Hamiltonians `c_q` to
`d_q` (`TauCeti.Floer.pairOfPantsContinuationPerturbation_add_const`). This datum has no
Hamiltonian vector field. Consequently:

* the perturbed derivative `du - X_K`, hence the Floer equation, and the Floer energy density are
  unchanged
  (`TauCeti.SmoothTwoForm.perturbedMFDeriv_pairOfPantsContinuationPerturbation_add_const`,
  `TauCeti.SmoothTwoForm.floerEnergyDensity_pairOfPantsContinuationPerturbation_add_const`);
* the curvature changes by the curvature of `k`, which does not depend on the target point
  (`TauCeti.SmoothTwoForm.hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const`);
* the integral of the curvature of `k` over the pair of pants is `∑ q, ±∫₀¹ d_q`, with the sign
  `+` on the input ends `0`, `1` and `-` on the output end `∞`, whatever the inner normalizations
  `c_q` and the neck positions `L_q`
  (`SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_const`).

So along every map whose curvature for `G`, `H` is integrable on `S`, the integrated curvature
changes by `∑ q, ±∫₀¹ d_q`
(`SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const`),
which is exactly the change of the Hamiltonian terms `∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` at the
asymptotic orbits. The two changes cancel in the energy identity, as they must, since the energy
itself is unchanged. On each end the curvature of `k` is the derivative in the longitudinal
coordinate of `β(σ - 1) (c_q + β(σ - L_q) (d_q - c_q))(t)`, which is `0` near the core of the pair
of pants and `d_q(t)` far out on the end, so the inner normalization `c_q` integrates to zero.

The curvature of `k` is the exterior derivative `∂_s k_t - ∂_t k_s` of a one-form on the domain,
the same for every target. Its integral is computed once, on `ℂ` with its standard symplectic form,
by the energy identity along a constant map. The vector-space statements are the specializations
of the manifold ones to the constant form `TauCeti.SymplecticForm.constSmooth`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on the
  curvature of Hamiltonian perturbations and the energy identity.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 3, on continuation maps and their energy identity.
-/

public section

open Set Function MeasureTheory TauCeti.ThricePuncturedSphere TauCeti.ThricePuncturedSphere.Puncture
open scoped Manifold

namespace TauCeti

namespace Floer

variable {M : Type*} {c : Puncture → ℝ → ℝ} {L : Puncture → ℝ}

/-- Periodic normalizations `c_q` give period-one target-independent Hamiltonians. -/
theorem periodic_const_target (hc : ∀ q, Periodic (c q) 1) (q : Puncture) :
    Periodic (fun t (_ : M) ↦ c q t) 1 :=
  fun t ↦ funext fun _ ↦ hc q t

/-- `C¹` normalizations `c_q` give `C¹` target-independent Hamiltonians on a manifold `M`. -/
theorem contMDiff_uncurry_const_target {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace G] {I : ModelWithCorners ℝ E G} [TopologicalSpace M] [ChartedSpace G M]
    (hcs : ∀ q, ContDiff ℝ 1 (c q)) (q : Puncture) :
    ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry fun t (_ : M) ↦ c q t) :=
  (hcs q).contMDiff.comp contMDiff_fst

/-- The components of the perturbation between target-independent Hamiltonians, as functions of
the domain point alone: their values at any target point `y`. -/
private theorem pairOfPantsContinuationPerturbation_const_target_fun (c d : Puncture → ℝ → ℝ)
    (L : Puncture → ℝ) (y : M) (v : ℂ) :
    (fun z (x : M) ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
        (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x v) =
      fun z _ ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
        (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [pairOfPantsContinuationPerturbation_const_target c d L _ x y]

/-- The components of the normalized perturbation are the components of the original one plus
those of the perturbation between the normalizing functions, evaluated at any target point
`y`. -/
private theorem pairOfPantsContinuationPerturbation_add_const_fun (G H : Puncture → ℝ → M → ℝ)
    (c d : Puncture → ℝ → ℝ) (L : Puncture → ℝ) (y : M) (v : ℂ) :
    (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
        (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x v) =
      fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x v +
        pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t) (fun q t (_ : M) ↦ d q t) L
          (Complex.equivRealProdCLM.symm z) y v := by
  funext z x
  rw [pairOfPantsContinuationPerturbation_add_const, add_apply,
    pairOfPantsContinuationPerturbation_const_target c d L _ x y]

end Floer

/-! ### Manifold targets -/

namespace SmoothTwoForm

open Floer

variable {E F M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace F]
  {I : ModelWithCorners ℝ E F} [TopologicalSpace M] [ChartedSpace F M] [IsManifold I ⊤ M]
  {G H : Puncture → ℝ → M → ℝ} {c d : Puncture → ℝ → ℝ} {L : Puncture → ℝ}

/-- **Normalizing the Hamiltonians does not change the Floer equation.** The perturbed derivative
`du - X_K` of any map into `M` is the same for the inner and outer Hamiltonians `G_q`, `H_q` and
`G_q + c_q`, `H_q + d_q`. -/
@[simp]
theorem perturbedMFDeriv_pairOfPantsContinuationPerturbation_add_const (ω : SmoothTwoForm I M)
    (G H : Puncture → ℝ → M → ℝ) (c d : Puncture → ℝ → ℝ) (L : Puncture → ℝ) (u : ℝ × ℝ → M) :
    ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedMFDeriv
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u := by
  rw [pairOfPantsContinuationPerturbation_add_const_fun G H c d L (u 0),
    pairOfPantsContinuationPerturbation_add_const_fun G H c d L (u 0), perturbedMFDeriv_add_const]

/-- **Normalizing the Hamiltonians does not change the energy density.** -/
@[simp]
theorem floerEnergyDensity_pairOfPantsContinuationPerturbation_add_const (ω : SmoothTwoForm I M)
    (G H : Puncture → ℝ → M → ℝ) (c d : Puncture → ℝ → ℝ) (L : Puncture → ℝ) (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u := by
  rw [pairOfPantsContinuationPerturbation_add_const_fun G H c d L (u 0),
    pairOfPantsContinuationPerturbation_add_const_fun G H c d L (u 0), floerEnergyDensity_add_const]

/-- The curvature of the perturbation between target-independent Hamiltonians does not depend on
the target point. -/
theorem hamiltonianCurvature_pairOfPantsContinuationPerturbation_const_target
    (ω : SmoothTwoForm I M) (c d : Puncture → ℝ → ℝ) (L : Puncture → ℝ) (z : ℝ × ℝ) (x y : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
          (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
          (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
          (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
          (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) z y := by
  rw [pairOfPantsContinuationPerturbation_const_target_fun c d L x,
    pairOfPantsContinuationPerturbation_const_target_fun c d L x, hamiltonianCurvature_const,
    hamiltonianCurvature_const]

/-- **The curvature of the normalized perturbation.** At every point of the pair of pants, the
curvature of the perturbation with continuation necks from `G_q + c_q` to `H_q + d_q` is the
curvature for `G_q`, `H_q` plus the curvature of the perturbation between the target-independent
Hamiltonians `c_q` and `d_q`. -/
theorem hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const (ω : SmoothTwoForm I M)
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hd : ∀ q, Periodic (d q) 1)
    (hcs : ∀ q, ContDiff ℝ 1 (c q)) (hds : ∀ q, ContDiff ℝ 1 (d q)) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : M) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
            (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
            (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have hc' := periodic_const_target (M := M) hc
  have hd' := periodic_const_target (M := M) hd
  have hcs' := contMDiff_uncurry_const_target (I := I) (M := M) hcs
  have hds' := contMDiff_uncurry_const_target (I := I) (M := M) hds
  rw [pairOfPantsContinuationPerturbation_add_const_fun G H c d L x,
    pairOfPantsContinuationPerturbation_add_const_fun G H c d L x,
    hamiltonianCurvature_add_const ω
      (differentiableAt_pairOfPantsContinuationPerturbation_domain hG hH hGs hHs L hz x 1)
      (differentiableAt_pairOfPantsContinuationPerturbation_domain hG hH hGs hHs L hz x Complex.I)
      (differentiableAt_pairOfPantsContinuationPerturbation_domain hc' hd' hcs' hds' L hz x 1)
      (differentiableAt_pairOfPantsContinuationPerturbation_domain hc' hd' hcs' hds' L hz x
        Complex.I),
    pairOfPantsContinuationPerturbation_const_target_fun c d L x,
    pairOfPantsContinuationPerturbation_const_target_fun c d L x]

/-- The integrated curvature of the perturbation between target-independent Hamiltonians, on `ℂ`
with its standard symplectic form along the constant map `0`, is `∑ q, ±∫₀¹ d_q`. -/
private theorem setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_const_complex
    (hc : ∀ q, Periodic (c q) 1) (hd : ∀ q, Periodic (d q) 1)
    (hcs : ∀ q, ContDiff ℝ 1 (c q)) (hds : ∀ q, ContDiff ℝ 1 (d q)) (L : Puncture → ℝ) :
    ∫ z in thricePuncturedSphereReal, stdComplexSymplecticForm.constSmooth.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : ℂ) ↦ c q t)
          (fun q t (_ : ℂ) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : ℂ) ↦ c q t)
          (fun q t (_ : ℂ) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) z 0 =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, d q t := by
  -- Along the constant map `0`, the energy density and the area density vanish.
  have hE : stdComplexSymplecticForm.constSmooth.floerEnergyDensity
      (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : ℂ) ↦ c q t)
        (fun q t (_ : ℂ) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : ℂ) ↦ c q t)
        (fun q t (_ : ℂ) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I)
      (fun _ ↦ (0 : ℂ)) = 0 := by
    funext z
    rw [SymplecticForm.floerEnergyDensity_constSmooth,
      pairOfPantsContinuationPerturbation_const_target_fun c d L (0 : ℂ),
      pairOfPantsContinuationPerturbation_const_target_fun c d L (0 : ℂ),
      SymplecticForm.floerEnergyDensity_def, SymplecticForm.perturbedFDeriv_const]
    simp
  have hA : (fun z : ℝ × ℝ ↦ (SmoothBundleForm.eval₂ stdComplexSymplecticForm.constSmooth (0 : ℂ)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (fun _ ↦ (0 : ℂ)) z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℂ) (fun _ ↦ (0 : ℂ)) z stdComplexLineImag) : ℝ)) = 0 := by
    funext z
    exact (stdComplexSymplecticForm.eval₂_constSmooth_mfderiv_stdComplexLine (fun _ ↦ 0) z).trans
      (by simp)
  -- The energy identity for the constant map `0` on a truncation past every neck leaves only the
  -- curvature and the end terms.
  have hid := (SymplecticForm.isNondegenerate_constSmooth stdComplexSymplecticForm)
    |>.integral_floerEnergyDensity_pairOfPantsContinuationPerturbation_truncation
    (G := fun q t (_ : ℂ) ↦ c q t) (H := fun q t (_ : ℂ) ↦ d q t) (L := L)
    (periodic_const_target hc) (periodic_const_target hd) (contMDiff_uncurry_const_target hcs)
    (contMDiff_uncurry_const_target hds) (u := fun _ ↦ (0 : ℂ)) contMDiffOn_const
    (R := max 2 (∑ q, |L q| + 1)) (le_max_left _ _)
    fun q ↦ le_max_of_le_right (by
      linarith [le_abs_self (L q), Finset.single_le_sum (fun r _ ↦ abs_nonneg (L r))
        (Finset.mem_univ q)])
  rw [hE, hA] at hid
  simp only [integral_zero', zero_add] at hid
  linarith

/-- **The integrated curvature of a normalization.** For period-one `C¹` functions `c_q`, `d_q` of
time, the curvature of the perturbation with continuation necks from the target-independent
Hamiltonians `c_q` to `d_q` on `M` integrates over the pair of pants to `∑ q, ±∫₀¹ d_q`, with the
sign `+` on the input ends and `-` on the output end, along any map `u`. It does not depend on the
inner functions `c_q` or on the neck positions. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_const
    (ω : SmoothTwoForm I M) (hc : ∀ q, Periodic (c q) 1) (hd : ∀ q, Periodic (d q) 1)
    (hcs : ∀ q, ContDiff ℝ 1 (c q)) (hds : ∀ q, ContDiff ℝ 1 (d q)) (L : Puncture → ℝ)
    (u : ℝ × ℝ → M) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
          (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
          (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, d q t := by
  -- The curvature of a target-independent datum is the exterior derivative of a one-form on the
  -- domain, whatever the target; we compute it on `ℂ` with its standard symplectic form.
  have h (z : ℝ × ℝ) : ω.hamiltonianCurvature
      (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
        (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : M) ↦ c q t)
        (fun q t (_ : M) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) =
      stdComplexSymplecticForm.constSmooth.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : ℂ) ↦ c q t)
          (fun q t (_ : ℂ) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : ℂ) ↦ c q t)
          (fun q t (_ : ℂ) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) z 0 := by
    rw [pairOfPantsContinuationPerturbation_const_target_fun c d L (u z),
      pairOfPantsContinuationPerturbation_const_target_fun c d L (u z), hamiltonianCurvature_const,
      pairOfPantsContinuationPerturbation_const_target_fun c d L (0 : ℂ),
      pairOfPantsContinuationPerturbation_const_target_fun c d L (0 : ℂ),
      hamiltonianCurvature_const]
    -- Both sides are the same exterior derivative of a one-form on the domain.
    simp only [pairOfPantsContinuationPerturbation_def, continuationHomotopy_def]
  rw [integral_congr_ae (Filter.Eventually.of_forall h)]
  exact setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_const_complex hc hd
    hcs hds L

/-- **Normalizing the Hamiltonians shifts the integrated curvature by the outer normalization.**
Along a map whose curvature for the inner and outer Hamiltonians `G_q`, `H_q` is integrable on the
pair of pants, the integrated curvature of the perturbation with continuation necks from
`G_q + c_q` to `H_q + d_q` is the integrated curvature for `G_q`, `H_q` plus `∑ q, ±∫₀¹ d_q`, with
the sign `+` on the input ends and `-` on the output end. This is also the change of the
Hamiltonian terms `∑ q, ±∫₀¹ H_q(t, x_q(t)) dt` of the energy identity
`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_pairOfPantsContinuationPerturbation`,
so the two changes cancel and the energy identity for `G_q + c_q`, `H_q + d_q` is the one for
`G_q`, `H_q`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const
    (ω : SmoothTwoForm I M) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (G q)))
    (hHs : ∀ q, ContMDiff (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hd : ∀ q, Periodic (d q) 1)
    (hcs : ∀ q, ContDiff ℝ 1 (c q)) (hds : ∀ q, ContDiff ℝ 1 (d q)) {u : ℝ × ℝ → M}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      (∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          z (u z)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, d q t := by
  -- The curvature of the normalization does not depend on the target point, so it is integrable
  -- along `u` because it is along a constant map.
  have hk := (ω.integrableOn_hamiltonianCurvature_pairOfPantsContinuationPerturbation
    (G := fun q t (_ : M) ↦ c q t) (H := fun q t (_ : M) ↦ d q t) (L := L)
    (periodic_const_target hc) (periodic_const_target hd) (contMDiff_uncurry_const_target hcs)
    (contMDiff_uncurry_const_target hds) (u := fun _ ↦ u 0) continuousOn_const).congr_fun
    (fun z _ ↦ ω.hamiltonianCurvature_pairOfPantsContinuationPerturbation_const_target c d L z
      (u 0) (u z))
    isOpen_thricePuncturedSphereReal.measurableSet
  rw [← ω.setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_const hc hd hcs hds
    L u, ← integral_add hu hk]
  exact setIntegral_congr_fun isOpen_thricePuncturedSphereReal.measurableSet fun z hz ↦
    ω.hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const hG hH hGs hHs hc hd hcs
      hds hz (u z)

end SmoothTwoForm

/-! ### Symplectic vector spaces -/

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {G H : Puncture → ℝ → V → ℝ} {c d : Puncture → ℝ → ℝ} {L : Puncture → ℝ}

/-- **Normalizing the Hamiltonians does not change the Floer equation.** The perturbed derivative
`du - X_K` of any map into a symplectic vector space is the same for the inner and outer
Hamiltonians `G_q`, `H_q` and `G_q + c_q`, `H_q + d_q`. -/
@[simp]
theorem perturbedFDeriv_pairOfPantsContinuationPerturbation_add_const (ω : SymplecticForm V)
    (G H : Puncture → ℝ → V → ℝ) (c d : Puncture → ℝ → ℝ) (L : Puncture → ℝ) (u : ℝ × ℝ → V) :
    ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.perturbedFDeriv
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u := by
  rw [pairOfPantsContinuationPerturbation_add_const_fun G H c d L 0,
    pairOfPantsContinuationPerturbation_add_const_fun G H c d L 0, perturbedFDeriv_add_const]

/-- **Normalizing the Hamiltonians does not change the energy density**, for a symplectic vector
space target. -/
@[simp]
theorem floerEnergyDensity_pairOfPantsContinuationPerturbation_add_const (ω : SymplecticForm V)
    (G H : Puncture → ℝ → V → ℝ) (c d : Puncture → ℝ → ℝ) (L : Puncture → ℝ) (u : ℝ × ℝ → V) :
    ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) u =
      ω.floerEnergyDensity
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        u := by
  rw [pairOfPantsContinuationPerturbation_add_const_fun G H c d L 0,
    pairOfPantsContinuationPerturbation_add_const_fun G H c d L 0, floerEnergyDensity_add_const]

/-- **The curvature of the normalized perturbation**, for a symplectic vector space target. This is
the vector-space case of
`SmoothTwoForm.hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const`. -/
theorem hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const (ω : SymplecticForm V)
    (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hd : ∀ q, Periodic (d q) 1)
    (hcs : ∀ q, ContDiff ℝ 1 (c q)) (hds : ∀ q, ContDiff ℝ 1 (d q)) {z : ℝ × ℝ}
    (hz : z ∈ thricePuncturedSphereReal) (x : V) :
    ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) z x =
      ω.hamiltonianCurvature
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          z x +
        ω.hamiltonianCurvature
          (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : V) ↦ c q t)
            (fun q t (_ : V) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t (_ : V) ↦ c q t)
            (fun q t (_ : V) ↦ d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I) z x := by
  have h := ω.constSmooth.hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const
    (L := L) hG hH (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hGs q).contMDiff)
    (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hc hd hcs hds hz x
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

/-- **Normalizing the Hamiltonians shifts the integrated curvature by the outer normalization**,
for a symplectic vector space target: along a map whose curvature for `G_q`, `H_q` is integrable
on the pair of pants, the integrated curvature for `G_q + c_q`, `H_q + d_q` is the one for `G_q`,
`H_q` plus `∑ q, ±∫₀¹ d_q`. This is the vector-space case of
`SmoothTwoForm.setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const`. -/
theorem setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const
    (ω : SymplecticForm V) (hG : ∀ q, Periodic (G q) 1) (hH : ∀ q, Periodic (H q) 1)
    (hGs : ∀ q, ContDiff ℝ 1 (uncurry (G q))) (hHs : ∀ q, ContDiff ℝ 1 (uncurry (H q)))
    (hc : ∀ q, Periodic (c q) 1) (hd : ∀ q, Periodic (d q) 1)
    (hcs : ∀ q, ContDiff ℝ 1 (c q)) (hds : ∀ q, ContDiff ℝ 1 (d q)) {u : ℝ × ℝ → V}
    (hu : IntegrableOn (fun z ↦ ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦
          pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z)) thricePuncturedSphereReal) :
    ∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ pairOfPantsContinuationPerturbation (fun q t y ↦ G q t y + c q t)
          (fun q t y ↦ H q t y + d q t) L (Complex.equivRealProdCLM.symm z) x Complex.I)
        z (u z) =
      (∫ z in thricePuncturedSphereReal, ω.hamiltonianCurvature
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦
            pairOfPantsContinuationPerturbation G H L (Complex.equivRealProdCLM.symm z) x
              Complex.I)
          z (u z)) +
        ∑ q, q.endSign * ∫ t in (0 : ℝ)..1, d q t := by
  have h :=
    ω.constSmooth.setIntegral_hamiltonianCurvature_pairOfPantsContinuationPerturbation_add_const
      hG hH (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hGs q).contMDiff)
      (fun q ↦ contMDiff_prod_modelWithCornersSelf_iff.2 (hHs q).contMDiff) hc hd hcs hds
      (by simpa only [hamiltonianCurvature_constSmooth] using hu)
  simp only [hamiltonianCurvature_constSmooth] at h
  exact h

end SymplecticForm

end TauCeti
