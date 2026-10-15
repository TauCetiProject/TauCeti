/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Harmonic.Weyl
public import TauCeti.Analysis.Sobolev.Trace.Reflection
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Sobolev.WeakDeriv.Laplacian
import TauCeti.Analysis.Sobolev.WeakDeriv.MeasurePreserving

/-!
# The Schwarz reflection principle for weakly harmonic functions

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

## The argument

For a test function `φ` on `U`, change variables by `ρ` in the second term:
`∫ Δφ (w - w ∘ ρ) = ∫ Δψ w` with `ψ = φ - φ ∘ ρ`, since the Laplacian commutes with the isometry
`ρ`. Integrating by parts on `U` gives `-∫ ⟪∇ψ, G⟫`, and it remains to show this vanishes. Now
`ψ` vanishes on the hyperplane, because `ρ` fixes it pointwise, but `ψ` is not supported in `H`,
so weak harmonicity on `U ∩ H` does not apply to it directly. Instead it applies to `η_n ψ`, with
`η_n` the boundary cutoffs `TauCeti.normalCutoff a (n + 1)`, giving
`∫ η_n ⟪∇ψ, G⟫ + ∫ ψ ⟪∇η_n, G⟫ = 0`. As `n → ∞` the first integral tends to `∫ ⟪∇ψ, G⟫`, because
`G` vanishes off `H`. The second tends to zero, because `ψ` vanishes on the hyperplane
(`TauCeti.tendsto_integral_mul_fderiv_normalCutoff_apply`). This is the cutoff argument of
Brezis, Lemma 9.2, used in `TauCeti.Analysis.Sobolev.Trace.Reflection` for the even reflection.

## Main declarations

* `TauCeti.WeaklyHarmonicOn.sub_comp_normalReflection`: the odd reflection of a function weakly
  harmonic on `U ∩ H`, weakly differentiable on `U` with weak gradient vanishing off `H`, is weakly
  harmonic on `U`.
* `TauCeti.WeaklyHarmonicOn.exists_harmonicOnNhd_ae_eq_of_inf_normalHalfSpace`: if such a function
  also vanishes off `H`, it agrees almost everywhere on `U ∩ H` with a harmonic function on `U`
  that is odd under `ρ`, and its weak gradient agrees there with the classical gradient.

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
  have hint {χ : WithLp 2 (ℝ × E) → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
      (hχK : tsupport χ ⊆ K) : Integrable fun x => fderiv ℝ χ x (G x) :=
    (integrable_fderiv_apply (hχ.of_le (by simp)) hχc aestronglyMeasurable_id hGK).congr
      (Eventually.of_forall fun x => by
        by_cases hxK : x ∈ K
        · simp [hxK]
        · simp [hxK, fderiv_of_notMem_tsupport ℝ fun h => hxK (hχK h)])
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
  have I1 : Integrable fun x => fderiv ℝ ψ x (G x) := hint hψ hψc subset_rfl
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
    rw [hfun, integral_sub (hint (hηψ n) hψc.mul_left tsupport_mul_subset_right) (I2 n), key n,
      zero_sub]
  -- The boundary-layer term tends to zero.
  have hlayer := tendsto_integral_mul_fderiv_normalCutoff_apply hGK.locallyIntegrable
    (fun x hx => by by_cases hxK : x ∈ K <;> simp [hxK, hG0 x hx]) hψ hψc hψa
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
      (normalReflection E a).isometry.lipschitz.locallyLipschitzOn hU).locallyIntegrableOn
  refine weaklyHarmonicOn_iff.2 ⟨hwl.sub hwρ, fun φ => ?_⟩
  -- The reflected test function `φ ∘ ρ` and the odd combination `ψ = φ - φ ∘ ρ`.
  set φρ := reflectTestFunction hU φ
  have hφρ : (φρ : WithLp 2 (ℝ × E) → ℝ) = fun x => φ (ρ x) :=
    funext (reflectTestFunction_apply hU φ)
  have hΔ (x : WithLp 2 (ℝ × E)) : Δ (φρ : WithLp 2 (ℝ × E) → ℝ) x = Δ (φ : _ → ℝ) (ρ x) :=
    congrFun (laplacian_comp_affineIsometryEquiv_right ρ φ) x
  have hint (v : WithLp 2 (ℝ × E) → ℝ) (hv : LocallyIntegrableOn v U volume) (θ : 𝓓(U, ℝ)) :
      Integrable fun x => Δ (θ : WithLp 2 (ℝ × E) → ℝ) x • v x := by
    simpa only [TestFunction.laplacianCLM_apply] using
      integrable_smul_of_locallyIntegrableOn hv
        (LineDeriv.laplacianCLM ℝ (WithLp 2 (ℝ × E)) 𝓓(U, ℝ) θ)
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
    have hρx : ρ x ∉ normalHalfSpace (E := E) a := by
      rw [hρdef, normalReflection_mem_normalHalfSpace_iff, not_lt]
      exact (mem_normalHalfSpace a x).1 hxUH.2 |>.le
    rw [← hx hxUH.1, hx0 (hU hxUH.1) hρx, sub_zero]
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

end TauCeti
