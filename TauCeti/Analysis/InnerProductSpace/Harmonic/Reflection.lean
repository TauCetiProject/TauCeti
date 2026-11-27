/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
public import TauCeti.Analysis.Sobolev.Trace.Reflection.Basic
public import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.InnerProductSpace.Harmonic.Isometry
import TauCeti.Analysis.InnerProductSpace.Harmonic.Subharmonic
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving
import TauCeti.Analysis.PDE.PoissonIntegral.Ball

/-!
# The Schwarz reflection principle

This file proves the Schwarz reflection principle for harmonic functions in two forms: a weak form,
for functions vanishing on the hyperplane in the Sobolev sense, and the classical form, for
functions continuous up to the hyperplane.

## The weak form

Let `H = normalHalfSpace a = {x | a < x.fst}` in the Euclidean product `ℝ × E`, let
`ρ (t, y) = (2a - t, y)` be the reflection in its boundary hyperplane `{a} × E`, and let `U` be an
open set with `ρ U ⊆ U`. Suppose `w` is weakly harmonic on `U ∩ H`, vanishes off `H`, and vanishes
on the flat part `U ∩ {a} × E` of the boundary of `U ∩ H` in the Sobolev sense: `w` is weakly
differentiable on all of `U`, with a weak gradient `G` vanishing off `H`. Then the odd reflection

`x ↦ w x - w (ρ x)`

is weakly harmonic on all of `U`; for this, only the condition on `G` is needed. By Weyl's lemma
the odd reflection agrees almost everywhere with a harmonic function `h` on `U`. This `h` is odd
under `ρ`, and on `U ∩ H` it agrees almost everywhere with `w`, and `∇h` with `G`.

This is the classical Schwarz reflection principle for harmonic functions in `ℝⁿ`, in the weak
form that boundary regularity uses. A weak solution of the Dirichlet problem on a half-ball,
with zero boundary values on the flat part, becomes after reflection a harmonic function on the
whole ball. Estimates for harmonic functions on balls, such as the Campanato decay estimates of
`TauCeti.Analysis.InnerProductSpace.Harmonic.Decay`, can then be applied on balls centred on the
flat boundary.

## The classical form

Let `ρ` be the reflection in the hyperplane `⟪y, ν⟫ = c` of a finite-dimensional real inner product
space, `ν ≠ 0`, and let `Ω` be an open set with `ρ Ω ⊆ Ω`. If `v` is harmonic on the part of `Ω`
above the hyperplane, continuous up to the hyperplane from above, and zero on the part of `Ω` in the
hyperplane, then its odd reflection, equal to `v` on and above the hyperplane and to `-v ∘ ρ` below
it, is harmonic on `Ω` (`TauCeti.harmonicOnNhd_ite_neg_comp_hyperplaneReflection`). Nothing is
assumed of `v` near the hyperplane beyond continuity, which is the form in which classical
solutions of the Dirichlet problem, given by Perron's method or a Poisson integral, are known to
attain zero boundary values on a flat boundary portion.

## The argument

For the weak form, given a test function `φ` on `U`, change variables by `ρ` in the second term:
`∫ Δφ (w - w ∘ ρ) = ∫ Δψ w` with `ψ = φ - φ ∘ ρ`, since the Laplacian commutes with the isometry
`ρ`. Integrating by parts on `U` gives `-∫ ⟪∇ψ, G⟫`, and it remains to show this vanishes. Now
`ψ` vanishes on the hyperplane, because `ρ` fixes it pointwise, but `ψ` is not supported in `H`,
so weak harmonicity on `U ∩ H` does not apply to it directly. Instead it applies to `η_n ψ`, with
`η_n` the boundary cutoffs `TauCeti.normalCutoff a (n + 1)`, giving
`∫ η_n ⟪∇ψ, G⟫ + ∫ ψ ⟪∇η_n, G⟫ = 0`. As `n → ∞` the first integral tends to `∫ ⟪∇ψ, G⟫`, because
`G` vanishes off `H`. The second tends to zero, because `ψ` vanishes on the hyperplane
(`TauCeti.tendsto_integral_mul_fderiv_normalCutoff_apply`). This is the cutoff argument of
Brezis, Lemma 9.2, used in `TauCeti.Analysis.Sobolev.Trace.Reflection` for the even reflection.

For the classical form it suffices, by locality, to show that the odd reflection `w` of `v` is
harmonic on a ball `B` centred on the hyperplane, with closure in `Ω`. The function `w` is
continuous on the closed ball and odd under `ρ`. Let `h` be the harmonic function on `B` with
boundary values `w` (`TauCeti.exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere`). Then
`-h ∘ ρ` solves the same Dirichlet problem, so `h` is odd by uniqueness, and vanishes on the
hyperplane. On the upper half of `B`, `h` and `v` are harmonic, continuous up to the boundary and
agree on it, so they agree by the maximum principle
(`TauCeti.eqOn_closure_of_laplacian_eq_of_eqOn_frontier`); by oddness `h = w` on all of `B`.

## Main declarations

* `TauCeti.WeaklyHarmonicOn.sub_comp_normalReflection`: the odd reflection of a function weakly
  harmonic on `U ∩ H`, weakly differentiable on `U` with weak gradient vanishing off `H`, is weakly
  harmonic on `U`.
* `TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq_of_inf_normalHalfSpace`: if such a function
  also vanishes off `H`, it agrees almost everywhere on `U ∩ H` with a harmonic function on `U`
  that is odd under `ρ`, and its weak gradient agrees there with the classical gradient.
* `TauCeti.harmonicOnNhd_ite_neg_comp_hyperplaneReflection`: the classical form, the odd reflection
  of a harmonic function continuous up to the hyperplane and zero on it is harmonic.

## References

* S. Axler, P. Bourdon, W. Ramey, *Harmonic Function Theory*, 2nd ed., Springer GTM 137: the
  Schwarz reflection principle for harmonic functions continuous up to the hyperplane.
* H. Brezis, *Functional Analysis, Sobolev Spaces and Partial Differential Equations*, Lemma 9.2.
-/

public section

open InnerProductSpace MeasureTheory Set TopologicalSpace Filter
open scoped ContDiff Topology Distributions Gradient InnerProductSpace Laplacian

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {a : ℝ} {U : Opens (WithLp 2 (ℝ × E))}
  {w : WithLp 2 (ℝ × E) → ℝ} {G : WithLp 2 (ℝ × E) → WithLp 2 (ℝ × E)}

/-- The reflection `φ ∘ ρ` of a test function `φ` on `U`, for `U` mapped into itself by `ρ`. -/
private noncomputable def reflectTestFunction (hU : MapsTo (normalReflection E a) U U)
    (φ : 𝓓(U, ℝ)) : 𝓓(U, ℝ) :=
  ⟨fun x => φ (normalReflection E a x), φ.contDiff.comp (contDiff_normalReflection a),
    φ.hasCompactSupport.comp_homeomorph (normalReflection E a).toHomeomorph, fun x hx => by
      -- Rewrite the reflected function as a composition with a homeomorphism, so that its
      -- topological support is the preimage of that of `φ`.
      have hfun : (fun x => φ (normalReflection E a x)) =
          (φ : WithLp 2 (ℝ × E) → ℝ) ∘ (normalReflection E a).toHomeomorph := by
        funext x
        simp only [Function.comp_apply, AffineIsometryEquiv.coe_toHomeomorph]
      rw [hfun, tsupport_comp_eq_preimage] at hx
      simpa only [AffineIsometryEquiv.coe_toHomeomorph, normalReflection_normalReflection] using
        hU (φ.tsupport_subset hx)⟩

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
private theorem reflectTestFunction_apply (hU : MapsTo (normalReflection E a) U U)
    (φ : 𝓓(U, ℝ)) (x : WithLp 2 (ℝ × E)) :
    reflectTestFunction hU φ x = φ (normalReflection E a x) :=
  rfl

/-- The pairing of the weak gradient with the gradient of a test function on `U` vanishing on the
hyperplane `{a} × E` is zero, when `w` is weakly harmonic on `U ∩ H` and `G` vanishes off `H`. -/
private theorem integral_fderiv_apply_eq_zero
    (hharm : WeaklyHarmonicOn volume (U ⊓ normalHalfSpace a) w)
    (hw : HasWeakFDerivOn volume U w fun x => innerSL ℝ (G x))
    (hG0 : ∀ x ∉ normalHalfSpace (E := E) a, G x = 0) {ψ : WithLp 2 (ℝ × E) → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) (hψU : tsupport ψ ⊆ U)
    (hψa : ∀ y : E, ψ (WithLp.toLp 2 (a, y)) = 0) :
    ∫ x, fderiv ℝ ψ x (G x) = 0 := by
  -- Cutting `G` off to the support of `ψ` makes it integrable on the whole space, without
  -- changing its pairing with the derivative of any function supported there.
  set K := tsupport ψ
  have hKc : IsCompact K := hψc.isCompact
  have hGK : Integrable (K.indicator G) :=
    (hw.locallyIntegrableOn_gradient.integrableOn_compact_subset hψU hKc).integrable_indicator
      hKc.measurableSet
  set η : ℕ → WithLp 2 (ℝ × E) → ℝ := fun n => normalCutoff a ((n : ℝ) + 1) with hη
  have hηψ (n : ℕ) : ContDiff ℝ ∞ (η n * ψ) := (contDiff_normalCutoff a _).mul hψ
  have hηψU (n : ℕ) : tsupport (η n * ψ) ⊆ (U ⊓ normalHalfSpace a : Opens _) := by
    rw [Opens.coe_inf]
    exact subset_inter (tsupport_mul_subset_right.trans hψU)
      (tsupport_mul_subset_left.trans (tsupport_normalCutoff_subset a (by positivity)))
  -- Weak harmonicity on `U ∩ H`, tested against `η n * ψ`, after one integration by parts.
  have key (n : ℕ) : ∫ x, fderiv ℝ (η n * ψ) x (G x) = 0 := by
    let θ : 𝓓(U ⊓ normalHalfSpace a, ℝ) := ⟨η n * ψ, hηψ n, hψc.mul_left, hηψU n⟩
    have hθ : (θ : WithLp 2 (ℝ × E) → ℝ) = η n * ψ := rfl
    have h := hharm.integral_laplacian_smul_eq_zero θ
    rw [(hw.mono inf_le_left).integral_laplacian_smul_eq_neg_integral_inner θ, neg_eq_zero,
      hθ] at h
    simpa only [inner_gradient_left] using h
  have I1 : Integrable fun x => fderiv ℝ ψ x (G x) :=
    integrable_fderiv_apply_of_tsupport_subset (hψ.of_le (by simp)) hψc subset_rfl
      aestronglyMeasurable_id hGK
  have I2 (n : ℕ) : Integrable fun x => η n x * fderiv ℝ ψ x (G x) :=
    I1.bdd_mul (contDiff_normalCutoff a _).continuous.aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [Real.norm_of_nonneg (normalCutoff_nonneg a _ x)]; exact normalCutoff_le_one a _ x)
  -- The product rule splits `key` into the cutoff term and the boundary-layer term.
  have hsplit (n : ℕ) :
      ∫ x, ψ x * fderiv ℝ (η n) x (G x) = -∫ x, η n x * fderiv ℝ ψ x (G x) := by
    have hfun : (fun x => ψ x * fderiv ℝ (η n) x (G x)) =
        fun x => fderiv ℝ (η n * ψ) x (G x) - η n x * fderiv ℝ ψ x (G x) := by
      funext x
      rw [fderiv_mul ((contDiff_normalCutoff a _).differentiable (by simp) x)
        (hψ.differentiable (by simp) x)]
      simp only [FunLike.coe_add, Pi.add_apply, FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring
    have I3 : Integrable fun x => fderiv ℝ (η n * ψ) x (G x) :=
      integrable_fderiv_apply_of_tsupport_subset ((hηψ n).of_le (by simp)) hψc.mul_left
        tsupport_mul_subset_right aestronglyMeasurable_id hGK
    rw [hfun, integral_sub I3 (I2 n), key n, zero_sub]
  -- The boundary-layer term tends to zero.
  have hlayer := tendsto_integral_mul_fderiv_normalCutoff_apply hGK.locallyIntegrable
    hψ hψc hψa
  have hlayer' : Tendsto (fun n : ℕ => ∫ x, ψ x * fderiv ℝ (η n) x (G x)) atTop (𝓝 0) := by
    refine hlayer.congr fun n => integral_congr_ae (Eventually.of_forall fun x => ?_)
    by_cases hxK : x ∈ K
    · simp [hη, hxK]
    · simp [image_eq_zero_of_notMem_tsupport hxK]
  -- The cutoff term tends to the integral we want, since `G` vanishes off the half-space.
  have hcut := tendsto_integral_normalCutoff_mul (a := a) I1 fun x hx => by simp [hG0 x hx]
  have hcut' : Tendsto (fun n : ℕ => ∫ x, η n x * fderiv ℝ ψ x (G x)) atTop (𝓝 0) := by
    simpa [hsplit] using hlayer'.neg
  exact tendsto_nhds_unique hcut hcut'

/-- **The Schwarz reflection principle, weak form.** Let `U` be an open set mapped into itself by
the reflection `ρ` in the hyperplane `{a} × E`, and let `w` be weakly harmonic on `U ∩ H`, where
`H = {x | a < x.fst}`. Suppose that `w` is weakly differentiable on all of `U`, with weak gradient
`G` vanishing almost everywhere on `U` off `H`; for instance, `w` has zero trace on the flat
boundary `U ∩ {a} × E` and is extended by zero off `H`. Then the odd reflection
`x ↦ w x - w (ρ x)` is weakly harmonic on `U`. -/
theorem WeaklyHarmonicOn.sub_comp_normalReflection
    (hharm : WeaklyHarmonicOn volume (U ⊓ normalHalfSpace a) w)
    (hU : MapsTo (normalReflection E a) U U)
    (hw : HasWeakFDerivOn volume U w fun x => innerSL ℝ (G x))
    (hG0 : ∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → G x = 0) :
    WeaklyHarmonicOn volume U fun x => w x - w (normalReflection E a x) := by
  set ρ := normalReflection E a with hρ
  -- Modify `G` on a null set so that it vanishes everywhere off the half-space.
  set G' := (normalHalfSpace (E := E) a : Set (WithLp 2 (ℝ × E))).indicator G
  have hw' : HasWeakFDerivOn volume U w fun x => innerSL ℝ (G' x) :=
    hw.congr_ae_deriv <| hG0.mono fun x hx => by
      by_cases hxH : x ∈ normalHalfSpace (E := E) a
      · simp [G', hxH]
      · simp [G', hxH, hx hxH]
  have hG0' : ∀ x ∉ normalHalfSpace (E := E) a, G' x = 0 := fun x hx =>
    indicator_of_notMem hx _
  have hwl := hw.locallyIntegrableOn
  have hwρ : LocallyIntegrableOn (fun x => w (ρ x)) U volume :=
    (hw.comp_measurePreserving (measurePreserving_normalReflection a)
      (normalReflection E a).isometry.lipschitzWith.locallyLipschitz.locallyLipschitzOn
      hU).locallyIntegrableOn
  refine weaklyHarmonicOn_iff.2 ⟨hwl.sub hwρ, fun φ => ?_⟩
  -- The reflected test function `φ ∘ ρ` and the odd combination `ψ = φ - φ ∘ ρ`.
  set φρ := reflectTestFunction hU φ
  have hφρ : (φρ : WithLp 2 (ℝ × E) → ℝ) = fun x => φ (ρ x) :=
    funext (reflectTestFunction_apply hU φ)
  have hΔ (x : WithLp 2 (ℝ × E)) : Δ (φρ : WithLp 2 (ℝ × E) → ℝ) x = Δ (φ : _ → ℝ) (ρ x) := by
    rw [hφρ]
    exact congrFun (laplacian_comp_affineIsometryEquiv_right ρ φ) x
  have hint (v : WithLp 2 (ℝ × E) → ℝ) (hv : LocallyIntegrableOn v U volume) (θ : 𝓓(U, ℝ)) :
      Integrable fun x => Δ (θ : WithLp 2 (ℝ × E) → ℝ) x • v x := by
    simpa only [TestFunction.laplacianCLM_apply] using
      TestFunction.integrable_smul (LineDeriv.laplacianCLM ℝ (WithLp 2 (ℝ × E)) 𝓓(U, ℝ) θ) hv
  have hcv : ∫ x, Δ (φ : WithLp 2 (ℝ × E) → ℝ) x • w (ρ x) =
      ∫ x, Δ (φρ : WithLp 2 (ℝ × E) → ℝ) x • w x := by
    rw [← integral_comp_normalReflection a fun x => Δ (φρ : WithLp 2 (ℝ × E) → ℝ) x • w x]
    simp only [hΔ, hρ, normalReflection_normalReflection]
  have hψa (y : E) : (φ - φρ : 𝓓(U, ℝ)) (WithLp.toLp 2 (a, y)) = 0 := by
    have hy : ρ (WithLp.toLp 2 (a, y)) = WithLp.toLp 2 (a, y) :=
      (normalReflection_eq_self_iff a _).2 rfl
    simp [hφρ, hy]
  have hzero := integral_fderiv_apply_eq_zero hharm hw' hG0' (φ - φρ).contDiff
    (φ - φρ).hasCompactSupport (φ - φρ).tsupport_subset hψa
  calc ∫ x, Δ (φ : WithLp 2 (ℝ × E) → ℝ) x • (w x - w (ρ x))
      = (∫ x, Δ (φ : WithLp 2 (ℝ × E) → ℝ) x • w x) -
          ∫ x, Δ (φρ : WithLp 2 (ℝ × E) → ℝ) x • w x := by
        rw [← hcv, ← integral_sub (hint w hwl φ) (hint _ hwρ φ)]
        simp only [smul_sub]
    _ = ∫ x, Δ ((φ - φρ : 𝓓(U, ℝ)) : WithLp 2 (ℝ × E) → ℝ) x • w x := by
        rw [← integral_sub (hint w hwl φ) (hint w hwl φρ)]
        refine integral_congr_ae (Eventually.of_forall fun x => ?_)
        simp only [← TestFunction.laplacianCLM_apply, map_sub, sub_apply, sub_smul]
    _ = 0 := by
        rw [hw'.integral_laplacian_smul_eq_neg_integral_inner, neg_eq_zero]
        simpa only [inner_gradient_left] using hzero

/-- **The Schwarz reflection principle.** Let `U` be an open set mapped into itself by the
reflection `ρ` in the hyperplane `{a} × E`, and let `w` be weakly harmonic on `U ∩ H`, where
`H = {x | a < x.fst}`, and zero almost everywhere on `U` off `H`. Suppose that `w` is weakly
differentiable on all of `U`, with weak gradient `G` vanishing almost everywhere on `U` off `H`,
so that `w` vanishes on the flat boundary `U ∩ {a} × E` in the Sobolev sense. Then there is a
function `h` harmonic on `U` and odd under `ρ` that agrees almost everywhere on `U ∩ H` with `w`,
and whose gradient agrees almost everywhere on `U ∩ H` with `G`. -/
theorem WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq_of_inf_normalHalfSpace
    (hharm : WeaklyHarmonicOn volume (U ⊓ normalHalfSpace a) w)
    (hU : MapsTo (normalReflection E a) U U)
    (hw : HasWeakFDerivOn volume U w fun x => innerSL ℝ (G x))
    (hG0 : ∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → G x = 0)
    (hw0 : ∀ᵐ x ∂volume.restrict U, x ∉ normalHalfSpace (E := E) a → w x = 0) :
    ∃ h : WithLp 2 (ℝ × E) → ℝ, HarmonicOnNhd h U ∧
      (∀ x ∈ U, h (normalReflection E a x) = -h x) ∧
      w =ᵐ[volume.restrict (U ⊓ normalHalfSpace a : Opens _)] h ∧
      (fun x => ∇ h x) =ᵐ[volume.restrict (U ⊓ normalHalfSpace a : Opens _)] G := by
  set ρ := normalReflection E a with hρdef
  have hρ := (measurePreserving_normalReflection (E := E) a).quasiMeasurePreserving
  obtain ⟨h, hh, hae⟩ := (hharm.sub_comp_normalReflection hU hw hG0).exists_harmonicOnNhd_ae_eq
  have hae' : ∀ᵐ x, x ∈ U → w x - w (ρ x) = h x :=
    (ae_restrict_iff' U.isOpen.measurableSet).1 hae
  have hw0' : ∀ᵐ x, x ∈ U → x ∉ normalHalfSpace (E := E) a → w x = 0 :=
    (ae_restrict_iff' U.isOpen.measurableSet).1 hw0
  have hUH : ((U ⊓ normalHalfSpace a : Opens _) : Set (WithLp 2 (ℝ × E))) ⊆ U := by simp
  -- On `U ∩ H` the reflected point lies off `H`, where `w` vanishes.
  have hwh : w =ᵐ[volume.restrict (U ⊓ normalHalfSpace a : Opens _)] h := by
    rw [EventuallyEq, ae_restrict_iff' (U ⊓ normalHalfSpace a).isOpen.measurableSet]
    filter_upwards [hae', hρ.ae hw0'] with x hx hx0 hxUH
    rw [Opens.coe_inf] at hxUH
    rw [← hx hxUH.1, hx0 (hU hxUH.1) (normalReflection_notMem_normalHalfSpace hxUH.2), sub_zero]
  refine ⟨h, hh, ?_, hwh, ?_⟩
  · -- `h ∘ ρ` and `-h` are continuous on `U` and agree almost everywhere there.
    have hodd : (fun x => h (ρ x)) =ᵐ[volume.restrict U] fun x => -h x := by
      rw [EventuallyEq, ae_restrict_iff' U.isOpen.measurableSet]
      filter_upwards [hae', hρ.ae hae'] with x hx hxρ hxU
      rw [← hx hxU, ← hxρ (hU hxU), hρdef, normalReflection_normalReflection, neg_sub]
    exact fun x hx => Measure.eqOn_open_of_ae_eq hodd U.isOpen
      (hh.contDiffOn.continuousOn.comp ρ.continuous.continuousOn hU)
      hh.contDiffOn.continuousOn.neg hx
  · -- Both `G` and `∇h` are weak gradients of `w` on `U ∩ H`.
    have hG := hw.mono (inf_le_left : U ⊓ normalHalfSpace a ≤ U)
    have hh' : HasWeakFDerivOn volume (U ⊓ normalHalfSpace a) w fun x => innerSL ℝ (∇ h x) :=
      (hasWeakFDerivOn_gradient_of_contDiffOn
        ((hh.contDiffOn.of_le one_le_two).mono hUH)).congr_ae hwh.symm
    filter_upwards [hh'.ae_eq hG] with x hx
    exact innerSL_inj.1 hx

/-! ### The classical reflection principle -/

section Classical

open Metric

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {ν : F} {c : ℝ} {v : F → ℝ}

omit [FiniteDimensional ℝ F] in
/-- The odd reflection of a function continuous on the closed upper half of a ball centred on the
hyperplane and zero on the hyperplane is continuous on the closed ball and odd under `ρ`. -/
private theorem continuousOn_ite_neg_comp_hyperplaneReflection (hν : ν ≠ 0) {x : F}
    (hx : ⟪x, ν⟫_ℝ = c) {r : ℝ} (hvc : ContinuousOn v (closedBall x r ∩ {y | c ≤ ⟪y, ν⟫_ℝ}))
    (hv0 : ∀ y ∈ closedBall x r, ⟪y, ν⟫_ℝ = c → v y = 0) :
    ContinuousOn (fun y ↦ if c ≤ ⟪y, ν⟫_ℝ then v y else -v (hyperplaneReflection ν c y))
        (closedBall x r) ∧
      ∀ y ∈ closedBall x r,
        (if c ≤ ⟪hyperplaneReflection ν c y, ν⟫_ℝ then v (hyperplaneReflection ν c y)
          else -v (hyperplaneReflection ν c (hyperplaneReflection ν c y))) =
        -(if c ≤ ⟪y, ν⟫_ℝ then v y else -v (hyperplaneReflection ν c y)) := by
  set ρ := hyperplaneReflection ν c
  have hρν : ∀ y, ⟪ρ y, ν⟫_ℝ = 2 * c - ⟪y, ν⟫_ℝ := inner_hyperplaneReflection hν c
  have hinner : Continuous fun y : F ↦ ⟪y, ν⟫_ℝ := continuous_id.inner continuous_const
  refine ⟨?_, fun y hy ↦ ?_⟩
  · -- Above the hyperplane the reflection is `v`, below it `-v ∘ ρ`, and both are `0` on it.
    have hup : ContinuousOn (fun y ↦ if c ≤ ⟪y, ν⟫_ℝ then v y else -v (ρ y))
        (closedBall x r ∩ {y | c ≤ ⟪y, ν⟫_ℝ}) :=
      hvc.congr fun y hy ↦ by simp [show c ≤ ⟪y, ν⟫_ℝ from hy.2]
    have hdown : ContinuousOn (fun y ↦ if c ≤ ⟪y, ν⟫_ℝ then v y else -v (ρ y))
        (closedBall x r ∩ {y | ⟪y, ν⟫_ℝ ≤ c}) := by
      refine (hvc.comp ρ.continuous.continuousOn
        fun y (hy : y ∈ closedBall x r ∩ {y | ⟪y, ν⟫_ℝ ≤ c}) ↦
          ⟨(hyperplaneReflection_mem_closedBall_iff hx).2 hy.1, ?_⟩).neg.congr
        fun y (hy : y ∈ closedBall x r ∩ {y | ⟪y, ν⟫_ℝ ≤ c}) ↦ ?_
      · change c ≤ ⟪ρ y, ν⟫_ℝ
        rw [hρν]
        linarith [show ⟪y, ν⟫_ℝ ≤ c from hy.2]
      · rcases (show ⟪y, ν⟫_ℝ ≤ c from hy.2).lt_or_eq with h | h
        · simp [not_le.2 h]
        · simp [h.ge, hyperplaneReflection_eq_self_of_inner_eq h, hv0 y hy.1 h, ρ]
    refine (hup.union_of_isClosed hdown (isClosed_closedBall.inter
      (isClosed_le continuous_const hinner)) (isClosed_closedBall.inter
      (isClosed_le hinner continuous_const))).mono fun y hy ↦ ?_
    rcases le_total c ⟪y, ν⟫_ℝ with h | h
    · exact Or.inl ⟨hy, h⟩
    · exact Or.inr ⟨hy, h⟩
  · rcases lt_trichotomy ⟪y, ν⟫_ℝ c with h | h | h
    · simp [show c ≤ ⟪ρ y, ν⟫_ℝ by rw [hρν]; linarith, not_le.2 h, ρ]
    · simp [hyperplaneReflection_eq_self_of_inner_eq h, h.ge, hv0 y hy h, ρ]
    · simp [show ¬c ≤ ⟪ρ y, ν⟫_ℝ by rw [hρν]; linarith, h.le, ρ]

/-- **An odd harmonic function with odd boundary values.** For boundary values `w` continuous on a
closed ball centred on the hyperplane and odd under `ρ`, the Dirichlet problem on the ball has a
solution that is odd under `ρ`. -/
private theorem exists_harmonicOnNhd_ball_eqOn_sphere_of_odd (hν : ν ≠ 0) {x : F}
    (hx : ⟪x, ν⟫_ℝ = c) {r : ℝ} (hr : 0 < r) {w : F → ℝ} (hwc : ContinuousOn w (closedBall x r))
    (hodd : ∀ y ∈ closedBall x r, w (hyperplaneReflection ν c y) = -w y) :
    ∃ H : F → ℝ, HarmonicOnNhd H (ball x r) ∧ ContinuousOn H (closedBall x r) ∧
      EqOn H w (sphere x r) ∧ ∀ y ∈ closedBall x r, H y = -H (hyperplaneReflection ν c y) := by
  borelize F
  have : Nontrivial F := nontrivial_of_ne ν 0 hν
  set ρ := hyperplaneReflection ν c
  have hcl : closure (ball x r) = closedBall x r := closure_ball x hr.ne'
  obtain ⟨H, hH, hHc, hHw⟩ := exists_harmonicOnNhd_ball_continuousOn_closedBall_eqOn_sphere
    (hwc.mono sphere_subset_closedBall)
  -- `-H ∘ ρ` solves the same Dirichlet problem, so it is `H` by uniqueness.
  have hH₂ : HarmonicOnNhd (fun y ↦ -H (ρ y)) (ball x r) := by
    have h := (harmonicOnNhd_comp_affineIsometryEquiv_right_iff ρ (f := H) (s := ball x r)).2 hH
    rw [show ρ ⁻¹' ball x r = ball x r from
      Set.ext fun y ↦ hyperplaneReflection_mem_ball_iff hx] at h
    exact h.neg
  have h := eqOn_closure_of_laplacian_eq_of_eqOn_frontier isOpen_ball isBounded_ball
    hH.contDiffOn hH₂.contDiffOn (by rwa [hcl])
    (by
      rw [hcl]
      exact (hHc.comp ρ.continuous.continuousOn fun y hy ↦
        (hyperplaneReflection_mem_closedBall_iff hx).2 hy).neg)
    (fun y hy ↦ by rw [(hH y hy).2.self_of_nhds, (hH₂ y hy).2.self_of_nhds]) (fun y hy ↦ ?_)
  · rw [hcl] at h
    exact ⟨H, hH, hHc, hHw, h⟩
  rw [frontier_ball x hr.ne'] at hy
  have hρx : ρ x = x := hyperplaneReflection_eq_self_of_inner_eq hx
  have hρy : ρ y ∈ sphere x r := by
    rw [mem_sphere, ← mem_sphere.1 hy, ← hρx, ρ.dist_map, hρx]
  rw [hHw hy, hHw hρy, hodd y (sphere_subset_closedBall hy), neg_neg]

/-- **The Schwarz reflection principle on a ball centred on the hyperplane.** This is the case of
`TauCeti.harmonicOnNhd_ite_neg_comp_hyperplaneReflection` that the general case reduces to, with
continuity assumed up to the sphere. -/
private theorem harmonicOnNhd_ite_neg_comp_hyperplaneReflection_ball (hν : ν ≠ 0) {x : F}
    (hx : ⟪x, ν⟫_ℝ = c) {r : ℝ} (hv : HarmonicOnNhd v (ball x r ∩ {y | c < ⟪y, ν⟫_ℝ}))
    (hvc : ContinuousOn v (closedBall x r ∩ {y | c ≤ ⟪y, ν⟫_ℝ}))
    (hv0 : ∀ y ∈ closedBall x r, ⟪y, ν⟫_ℝ = c → v y = 0) :
    HarmonicOnNhd (fun y ↦ if c ≤ ⟪y, ν⟫_ℝ then v y else -v (hyperplaneReflection ν c y))
      (ball x r) := by
  borelize F
  have : Nontrivial F := nontrivial_of_ne ν 0 hν
  rcases le_or_gt r 0 with hr | hr
  · exact fun y hy ↦ absurd hy (by simp [ball_eq_empty.2 hr])
  set ρ := hyperplaneReflection ν c
  set w : F → ℝ := fun y ↦ if c ≤ ⟪y, ν⟫_ℝ then v y else -v (ρ y) with hw
  have hρν : ∀ y, ⟪ρ y, ν⟫_ℝ = 2 * c - ⟪y, ν⟫_ℝ := inner_hyperplaneReflection hν c
  have hinner : Continuous fun y : F ↦ ⟪y, ν⟫_ℝ := continuous_id.inner continuous_const
  -- The Dirichlet problem with the boundary values of `w` has an odd solution `H`, which
  -- therefore vanishes on the hyperplane.
  obtain ⟨hwc, hodd⟩ := continuousOn_ite_neg_comp_hyperplaneReflection hν hx hvc hv0
  obtain ⟨H, hH, hHc, hHw, hHodd⟩ :=
    exists_harmonicOnNhd_ball_eqOn_sphere_of_odd hν hx hr hwc hodd
  have hH0 : ∀ y ∈ closedBall x r, ⟪y, ν⟫_ℝ = c → H y = 0 := fun y hy h ↦ by
    have := hHodd y hy
    rw [hyperplaneReflection_eq_self_of_inner_eq h] at this
    linarith
  -- Above the hyperplane `H = v`, by uniqueness on the half-ball.
  have hUcl : closure (ball x r ∩ {y | c < ⟪y, ν⟫_ℝ}) ⊆ closedBall x r ∩ {y | c ≤ ⟪y, ν⟫_ℝ} :=
    (closure_inter_subset_inter_closure _ _).trans
      (inter_subset_inter closure_ball_subset_closedBall (closure_setOf_lt_inner_subset ν c))
  have h := eqOn_closure_of_laplacian_eq_of_eqOn_frontier
    (isOpen_ball.inter (isOpen_lt continuous_const hinner))
    (isBounded_ball.subset inter_subset_left) (hH.contDiffOn.mono inter_subset_left)
    hv.contDiffOn (hHc.mono (hUcl.trans inter_subset_left)) (hvc.mono hUcl)
    (fun y hy ↦ by rw [(hH y hy.1).2.self_of_nhds, (hv y hy).2.self_of_nhds]) (fun y hy ↦ ?_)
  swap
  · have hyc := hUcl (frontier_subset_closure hy)
    rcases frontier_inter_subset _ _ hy with ⟨hs, -⟩ | ⟨-, hf⟩
    · rw [frontier_ball x hr.ne'] at hs
      rw [hHw hs]
      simp [show c ≤ ⟪y, ν⟫_ℝ from hyc.2]
    · have h := (frontier_lt_subset_eq continuous_const hinner hf).symm
      rw [hH0 y hyc.1 h, hv0 y hyc.1 h]
  -- Hence `H = w` on the ball, and `w` is harmonic there.
  have hHw' : EqOn H w (ball x r) := by
    intro y hy
    rcases lt_trichotomy ⟪y, ν⟫_ℝ c with h' | h' | h'
    · rw [hHodd y (ball_subset_closedBall hy), h (subset_closure
        ⟨(hyperplaneReflection_mem_ball_iff hx).2 hy, by rw [mem_ofPred, hρν]; linarith⟩)]
      simp [hw, not_le.2 h', ρ]
    · rw [hH0 y (ball_subset_closedBall hy) h']
      simp [hw, h'.ge, hv0 y (ball_subset_closedBall hy) h']
    · rw [h (subset_closure ⟨hy, h'⟩)]
      simp [hw, h'.le]
  exact fun y hy ↦
    (harmonicAt_congr_nhds (eventuallyEq_of_mem (isOpen_ball.mem_nhds hy) hHw')).1 (hH y hy)

/-- **The Schwarz reflection principle.** Let `ρ` be the reflection in the hyperplane
`⟪y, ν⟫ = c`, let `Ω` be an open set with `ρ Ω ⊆ Ω`, and let `v` be harmonic on the part of `Ω`
above the hyperplane, continuous up to the hyperplane from above, and zero on the part of `Ω` in
the hyperplane. Then the odd reflection of `v`, equal to `v` on and above the hyperplane and to
`-v ∘ ρ` below it, is harmonic on `Ω`. Unlike
`TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq_of_inf_normalHalfSpace`, nothing is assumed of
`v` near the hyperplane beyond continuity. -/
theorem harmonicOnNhd_ite_neg_comp_hyperplaneReflection (hν : ν ≠ 0) {Ω : Set F}
    (hΩ : IsOpen Ω) (hρΩ : ∀ y ∈ Ω, hyperplaneReflection ν c y ∈ Ω)
    (hv : HarmonicOnNhd v (Ω ∩ {y | c < ⟪y, ν⟫_ℝ}))
    (hvc : ContinuousOn v (Ω ∩ {y | c ≤ ⟪y, ν⟫_ℝ}))
    (hv0 : ∀ y ∈ Ω, ⟪y, ν⟫_ℝ = c → v y = 0) :
    HarmonicOnNhd (fun y ↦ if c ≤ ⟪y, ν⟫_ℝ then v y else -v (hyperplaneReflection ν c y)) Ω := by
  have hinner : Continuous fun y : F ↦ ⟪y, ν⟫_ℝ := continuous_id.inner continuous_const
  intro x hx
  rcases lt_trichotomy ⟪x, ν⟫_ℝ c with h | h | h
  · -- Below the hyperplane the odd reflection is `-v ∘ ρ` near `x`.
    have hρx : c < ⟪hyperplaneReflection ν c x, ν⟫_ℝ := by
      rw [inner_hyperplaneReflection hν]
      linarith
    refine (harmonicAt_congr_nhds (eventuallyEq_of_mem
      ((isOpen_lt hinner continuous_const).mem_nhds h) fun y (hy : ⟪y, ν⟫_ℝ < c) ↦ ?_)).2
      ((harmonicAt_comp_affineIsometryEquiv_right_iff (hyperplaneReflection ν c)).2
        (hv _ ⟨hρΩ x hx, hρx⟩)).neg
    simp [not_le.2 hy]
  · -- On the hyperplane, reflect on a ball centred at `x`.
    obtain ⟨r, hr, hrΩ⟩ := nhds_basis_closedBall.mem_iff.1 (hΩ.mem_nhds hx)
    exact harmonicOnNhd_ite_neg_comp_hyperplaneReflection_ball hν h
      (hv.mono (inter_subset_inter_left _ (ball_subset_closedBall.trans hrΩ)))
      (hvc.mono (inter_subset_inter_left _ hrΩ)) (fun y hy ↦ hv0 y (hrΩ hy)) x (mem_ball_self hr)
  · -- Above the hyperplane the odd reflection is `v` near `x`.
    refine (harmonicAt_congr_nhds (eventuallyEq_of_mem
      ((isOpen_lt continuous_const hinner).mem_nhds h) fun y (hy : c < ⟪y, ν⟫_ℝ) ↦ ?_)).2
      (hv x ⟨hx, h⟩)
    simp [hy.le]

end Classical

end TauCeti
