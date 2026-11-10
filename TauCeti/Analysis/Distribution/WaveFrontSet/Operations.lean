/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.WaveFrontSet.Localization
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.PositiveDefinite.FourierAtom

/-!
# The wave front set under restriction, smooth multiplication and differentiation

This file proves that the wave front set of a complex distribution is local, and that it does not
grow under the operations making up a linear differential operator with smooth coefficients.

* **Restriction.** Over an open subset `Ω' ≤ Ω`, the wave front set of the restriction `T|Ω'` is
  that of `T`: `WF(T|Ω') = WF(T) ∩ (Ω' × E)`.
* **Smooth multiplication.** For a smooth real function `f`, `WF(f T) ⊆ WF(T)`, and the two agree
  over the open set where `f ≠ 0`. Moreover `WF(f T)` lies over the support of `f`.
* **Differentiation.** `WF(∂_v T) ⊆ WF(T)`, and hence `WF(∂^m T) ⊆ WF(T)` for iterated
  derivatives.

Combining these with the sum rule `Distribution.waveFrontSet_add_subset`, a differential operator
`P = ∑ c_α a_α ∂^α` with smooth real coefficients `a_α` and complex constants `c_α`, which covers
every operator with smooth complex coefficients, satisfies `WF(P T) ⊆ WF(T)`
(`Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`). This is the
microlocality of differential operators, the first case of that of pseudodifferential
operators.

The proofs go through the localized Fourier transform `η ↦ T (φ e_η)`, where
`e_η x = 𝐞 (-⟪x, η⟫)`. Restriction and multiplication change only the cutoff:
`(T|Ω') (φ e_η) = T (φ e_η)` and `(f T) (φ e_η) = T ((f φ) e_η)`, and rapid decay survives
multiplication of the cutoff by a smooth function (Hörmander I, Lemma 8.1.1, which is
`Distribution.exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul`).
For the derivative, the product rule gives

`(∂_v T) (φ e_η) = 2πi ⟪v, η⟫ T (φ e_η) - T ((∂_v φ) e_η)`

(`Distribution.localFourier_lineDerivOp`), and the polynomial factor `⟪v, η⟫` is absorbed by
rapid decay of every order.

## Main results

* `Distribution.localFourier_restrictCLM`, `Distribution.localFourier_smulLeftCLM`,
  `Distribution.localFourier_lineDerivOp`: localized Fourier transforms of a restriction, a
  smooth multiple and a derivative.
* `Distribution.isMicrolocallySmoothAt_restrictCLM_iff`, `Distribution.waveFrontSet_restrictCLM`:
  the wave front set of a restriction.
* `Distribution.IsMicrolocallySmoothAt.smulLeftCLM`,
  `Distribution.isMicrolocallySmoothAt_smulLeftCLM_iff`,
  `Distribution.waveFrontSet_smulLeftCLM_subset`,
  `Distribution.mem_waveFrontSet_smulLeftCLM_iff`: the wave front set of a smooth multiple.
* `Distribution.IsMicrolocallySmoothAt.lineDerivOp`, `Distribution.waveFrontSet_lineDerivOp_subset`,
  `Distribution.waveFrontSet_iteratedLineDerivOp_subset`: the wave front set of a derivative.
* `Distribution.waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset`: differential
  operators with smooth coefficients do not enlarge the wave front set.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.1.
* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI*, Lecture I, §7.
-/

public section

noncomputable section

open Complex Filter LineDeriv Metric Real Set TopologicalSpace TestFunction
open scoped Distributions Topology FourierTransform RealInnerProductSpace ContDiff

namespace Distribution

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {Ω Ω' : Opens E}
  {f : E → ℝ}

/-! ### Localized Fourier transforms -/

/-- The localized Fourier transform at `η` pairs `T` with the cut-off character `φ e_η`, written as
the product of `φ` with the smooth function `e_η x = 𝐞 (-⟪x, η⟫)`. -/
private theorem localFourier_eq_complexPairing_bilinLeftCLM (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ))
    (η : E) :
    T.localFourier φ η = T.complexPairing
      (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ) :=
  localFourier_eq T φ fun x ↦ by
    simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]

/-- The localized Fourier transform of the restriction `T|Ω'` with cutoff `φ` is that of `T` with
the extension of `φ` by zero. -/
@[simp]
theorem localFourier_restrictCLM (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω', ℂ)) (η : E) :
    (restrictCLM Ω' T).localFourier φ η = T.localFourier (monoCLM ℝ φ) η := by
  rw [localFourier_eq_complexPairing_bilinLeftCLM, complexPairing_restrictCLM]
  refine (localFourier_eq T _ fun x ↦ ?_).symm
  by_cases h : Ω' ≤ Ω <;>
    simp [h, bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]

/-- The localized Fourier transform of the smooth multiple `f T` with cutoff `φ` is that of `T`
with cutoff `f φ`. -/
@[simp]
theorem localFourier_smulLeftCLM (hf : ContDiff ℝ ∞ f) (T : 𝓓'(Ω, ℂ)) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (smulLeftCLM hf T).localFourier φ η = T.localFourier (TestFunction.smulLeftCLM hf φ) η := by
  rw [localFourier_eq_complexPairing_bilinLeftCLM, complexPairing_smulLeftCLM]
  refine (localFourier_eq T _ fun x ↦ ?_).symm
  simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply,
    mul_assoc]

/-- The directional derivative of the cut-off character `φ e_η`, where `e_η x = 𝐞 (-⟪x, η⟫)`, by
the product rule. -/
private theorem lineDerivOp_bilinLeftCLM_fourierAtom (φ : 𝓓(Ω, ℂ)) (v η : E) :
    ∂_{v} (bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ) =
      bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) (∂_{v} φ) -
        (2 * π * I * ⟪v, η⟫ : ℂ) •
          bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ) (TauCeti.contDiff_fourierAtom η) φ := by
  ext x
  have hφ : HasFDerivAt φ (fderiv ℝ φ x) x :=
    (φ.contDiff.differentiable (by simp)).differentiableAt.hasFDerivAt
  -- `innerSL ℝ`, used as a real bilinear map, still evaluates to the inner product.
  have hL (a b : E) : (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ) a b = ⟪a, b⟫ := rfl
  have he := hasFDerivAt_fourierChar_neg_bilinear_left (innerSL ℝ) x η
  simp only [hL] at he
  have hfun : (fun y ↦ φ y * TauCeti.fourierAtom η y) = fun y ↦ φ y * (𝐞 (-⟪y, η⟫) : ℂ) := by
    simp [TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply]
  simp only [TestFunction.lineDerivOp_apply, bilinLeftCLM_apply, ContinuousLinearMap.mul_apply',
    sub_apply, smul_apply, smul_eq_mul]
  rw [hfun]
  -- `hφ.mul he` is stated for the pointwise product `⇑φ * _`, which unfolds to `φ e_η`; the
  -- coercion of `𝐞` to `ℂ` in `he` agrees with the one in `TauCeti.fourierAtom` up to unfolding.
  refine ((hφ.mul he).hasLineDerivAt v).lineDeriv.trans ?_
  rw [(hφ.hasLineDerivAt v).lineDeriv]
  simp [TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply, hL, real_inner_comm v η]
  ring

/-- **The localized Fourier transform of a derivative.** By the product rule
`∂_v (φ e_η) = (∂_v φ) e_η - 2πi ⟪v, η⟫ φ e_η`,

`(∂_v T) (φ e_η) = 2πi ⟪v, η⟫ T (φ e_η) - T ((∂_v φ) e_η)`. -/
@[simp]
theorem localFourier_lineDerivOp (T : 𝓓'(Ω, ℂ)) (v : E) (φ : 𝓓(Ω, ℂ)) (η : E) :
    (∂_{v} T).localFourier φ η =
      2 * π * I * ⟪v, η⟫ * T.localFourier φ η - T.localFourier (∂_{v} φ) η := by
  rw [localFourier_eq_complexPairing_bilinLeftCLM, complexPairing_lineDerivOp,
    lineDerivOp_bilinLeftCLM_fourierAtom, map_sub, map_smul, smul_eq_mul,
    ← localFourier_eq_complexPairing_bilinLeftCLM, ← localFourier_eq_complexPairing_bilinLeftCLM]
  ring

section FiniteDimensional

variable [FiniteDimensional ℝ E] {T : 𝓓'(Ω, ℂ)} {x ξ : E}

/-! ### Restriction -/

/-- **Locality of microlocal smoothness.** At a point `x` of an open subset `Ω' ≤ Ω`, the
restriction `T|Ω'` is microlocally smooth at `(x, ξ)` exactly when `T` is. -/
theorem isMicrolocallySmoothAt_restrictCLM_iff (h : Ω' ≤ Ω) (hx : x ∈ Ω') :
    (restrictCLM Ω' T).IsMicrolocallySmoothAt x ξ ↔ T.IsMicrolocallySmoothAt x ξ := by
  refine ⟨fun hT ↦ ?_, fun hT ↦ ?_⟩
  · -- A cutoff on `Ω'` extends by zero to a cutoff on `Ω` with the same localized transform.
    obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 hT
    refine isMicrolocallySmoothAt_iff.2
      ⟨monoCLM ℝ φ, by simpa [h] using hφx, Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
    simpa only [localFourier_restrictCLM] using hdecay N
  · -- Conversely, cutoffs supported near `x` inside `Ω'` serve for `T`.
    obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hdecay⟩ := hT.exists_nhds_cone
    obtain ⟨φ, hφU, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
      (inter_mem hU (Ω'.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
    refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
    simp only [localFourier_restrictCLM]
    refine hdecay _ (subset_trans ?_ (hφU.trans inter_subset_left)) N
    simp [h]

/-- **The wave front set of a restriction.** Over an open subset `Ω' ≤ Ω`, the restriction
`T|Ω'` has the wave front set of `T`: `WF(T|Ω') = WF(T) ∩ (Ω' × E)`. -/
theorem waveFrontSet_restrictCLM (h : Ω' ≤ Ω) (T : 𝓓'(Ω, ℂ)) :
    (restrictCLM Ω' T).waveFrontSet = T.waveFrontSet ∩ (Ω' : Set E) ×ˢ univ := by
  ext ⟨x, ξ⟩
  simp only [mem_waveFrontSet_iff, mem_inter_iff, mem_prod, mem_univ, and_true]
  constructor
  · rintro ⟨hx, hξ, hT⟩
    exact ⟨⟨h hx, hξ, (isMicrolocallySmoothAt_restrictCLM_iff h hx).not.1 hT⟩, hx⟩
  · rintro ⟨⟨-, hξ, hT⟩, hx⟩
    exact ⟨hx, hξ, (isMicrolocallySmoothAt_restrictCLM_iff h hx).not.2 hT⟩

/-! ### Multiplication by a smooth function -/

/-- A smooth multiple `f T` of a distribution microlocally smooth at `(x, ξ)` is microlocally
smooth there. -/
theorem IsMicrolocallySmoothAt.smulLeftCLM (hf : ContDiff ℝ ∞ f)
    (hT : T.IsMicrolocallySmoothAt x ξ) : (smulLeftCLM hf T).IsMicrolocallySmoothAt x ξ := by
  obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 hT
  obtain ⟨Γ', hΓ'o, hξ', hcone', c, hc, hΓ'⟩ := hΓ.exists_cone_closedBall_subset hcone hξ
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, hφx, Γ', hΓ'o, hξ', hcone', fun N ↦ ?_⟩
  simp only [localFourier_smulLeftCLM]
  refine exists_one_add_norm_pow_mul_norm_localFourier_le_of_eq_mul (g := fun y ↦ (f y : ℂ))
    (ofRealCLM.contDiff.comp hf).contDiffOn (fun y ↦ ?_) hc hΓ' (hdecay N)
  simp [mul_comm]

/-- Where `f x ≠ 0`, the smooth multiple `f T` is microlocally smooth at `(x, ξ)` exactly when
`T` is. -/
theorem isMicrolocallySmoothAt_smulLeftCLM_iff (hf : ContDiff ℝ ∞ f) (hfx : f x ≠ 0) :
    (smulLeftCLM hf T).IsMicrolocallySmoothAt x ξ ↔ T.IsMicrolocallySmoothAt x ξ := by
  refine ⟨fun hT ↦ ?_, IsMicrolocallySmoothAt.smulLeftCLM hf⟩
  -- The cutoff `φ` for `f T` gives the cutoff `f φ` for `T`, which does not vanish at `x`.
  obtain ⟨φ, hφx, Γ, hΓ, hξ, hcone, hdecay⟩ := isMicrolocallySmoothAt_iff.1 hT
  refine isMicrolocallySmoothAt_iff.2
    ⟨TestFunction.smulLeftCLM hf φ, by simp [hfx, hφx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  simpa only [localFourier_smulLeftCLM] using hdecay N

/-- **The wave front set of a smooth multiple.** For a smooth real function `f`, the wave front
set of `f T` lies in that of `T`, over the support of `f`. -/
theorem waveFrontSet_smulLeftCLM_subset (hf : ContDiff ℝ ∞ f) (T : 𝓓'(Ω, ℂ)) :
    (smulLeftCLM hf T).waveFrontSet ⊆ T.waveFrontSet ∩ tsupport f ×ˢ univ := by
  rintro ⟨x, ξ⟩ hp
  refine ⟨?_, ?_⟩
  · obtain ⟨hx, hξ, hfT⟩ := mem_waveFrontSet_iff.1 hp
    exact mem_waveFrontSet_iff.2 ⟨hx, hξ, fun hT ↦ hfT (hT.smulLeftCLM hf)⟩
  · obtain ⟨hpf, -⟩ := waveFrontSet_subset_dsupport _ hp
    exact ⟨(dsupport_smulLeftCLM_subset_inter hf T hpf).1, trivial⟩

/-- Over the open set where `f ≠ 0`, the smooth multiple `f T` has the wave front set of `T`. -/
theorem mem_waveFrontSet_smulLeftCLM_iff (hf : ContDiff ℝ ∞ f) (hfx : f x ≠ 0) :
    (x, ξ) ∈ (smulLeftCLM hf T).waveFrontSet ↔ (x, ξ) ∈ T.waveFrontSet := by
  simp only [mem_waveFrontSet_iff, isMicrolocallySmoothAt_smulLeftCLM_iff hf hfx]

/-! ### Differentiation -/

/-- A derivative `∂_v T` of a distribution microlocally smooth at `(x, ξ)` is microlocally smooth
there. -/
theorem IsMicrolocallySmoothAt.lineDerivOp (hT : T.IsMicrolocallySmoothAt x ξ) (v : E) :
    (∂_{v} T).IsMicrolocallySmoothAt x ξ := by
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 hT
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξ, hcone, hdecay⟩ := hT.exists_nhds_cone
  obtain ⟨φ, hφU, hφx⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem hU (Ω.isOpen.mem_nhds hx)) inter_subset_right (1 : ℂ)
  have hφU' : tsupport φ ⊆ U := hφU.trans inter_subset_left
  refine isMicrolocallySmoothAt_iff.2 ⟨φ, by simp [hφx], Γ, hΓ, hξ, hcone, fun N ↦ ?_⟩
  -- Both terms of `localFourier_lineDerivOp` decay; the factor `⟪v, η⟫` costs one order.
  obtain ⟨C₁, hC₁⟩ := hdecay φ hφU' (N + 1)
  obtain ⟨C₂, hC₂⟩ := hdecay (∂_{v} φ) ((tsupport_fderiv_apply_subset ℝ v).trans hφU') N
  refine ⟨2 * π * ‖v‖ * C₁ + C₂, fun η hη ↦ ?_⟩
  have hinner : ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ ≤ 2 * π * ‖v‖ * (1 + ‖η‖) := by
    calc ‖(2 * π * I * ⟪v, η⟫ : ℂ)‖ = 2 * π * ‖⟪v, η⟫‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_I, Complex.norm_real, Complex.norm_real,
            Complex.norm_two, Real.norm_of_nonneg Real.pi_pos.le, mul_one]
      _ ≤ 2 * π * (‖v‖ * (1 + ‖η‖)) := by
          gcongr
          exact (norm_inner_le_norm (𝕜 := ℝ) v η).trans
            (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (norm_nonneg v))
      _ = 2 * π * ‖v‖ * (1 + ‖η‖) := by ring
  have h1 : 0 ≤ (1 + ‖η‖) ^ N := by positivity
  rw [localFourier_lineDerivOp]
  calc (1 + ‖η‖) ^ N *
        ‖2 * π * I * ⟪v, η⟫ * T.localFourier φ η - T.localFourier (∂_{v} φ) η‖
      ≤ (1 + ‖η‖) ^ N * (2 * π * ‖v‖ * (1 + ‖η‖) * ‖T.localFourier φ η‖) +
          (1 + ‖η‖) ^ N * ‖T.localFourier (∂_{v} φ) η‖ := by
        rw [← mul_add]
        refine mul_le_mul_of_nonneg_left ((norm_sub_le _ _).trans ?_) h1
        rw [norm_mul]
        gcongr
    _ = 2 * π * ‖v‖ * ((1 + ‖η‖) ^ (N + 1) * ‖T.localFourier φ η‖) +
          (1 + ‖η‖) ^ N * ‖T.localFourier (∂_{v} φ) η‖ := by ring
    _ ≤ 2 * π * ‖v‖ * C₁ + C₂ := by
        gcongr
        exacts [hC₁ η hη, hC₂ η hη]

/-- **The wave front set of a derivative** lies in the wave front set of the distribution. -/
theorem waveFrontSet_lineDerivOp_subset (T : 𝓓'(Ω, ℂ)) (v : E) :
    (∂_{v} T).waveFrontSet ⊆ T.waveFrontSet := by
  rintro ⟨x, ξ⟩ hp
  obtain ⟨hx, hξ, hvT⟩ := mem_waveFrontSet_iff.1 hp
  exact mem_waveFrontSet_iff.2 ⟨hx, hξ, fun hT ↦ hvT (hT.lineDerivOp v)⟩

/-- The wave front set of an iterated derivative `∂^m T` lies in the wave front set of `T`. -/
theorem waveFrontSet_iteratedLineDerivOp_subset (T : 𝓓'(Ω, ℂ)) {n : ℕ} (m : Fin n → E) :
    (∂^{m} T).waveFrontSet ⊆ T.waveFrontSet := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left]
    exact (waveFrontSet_lineDerivOp_subset _ _).trans (ih _)

/-- **Differential operators do not enlarge the wave front set** (Hörmander I, §8.1). For
finitely many smooth real coefficients `a i`, complex constants `c i` and iterated directions
`m i`, the operator `P T = ∑ i ∈ s, c i • a i ∂^(m i) T` satisfies `WF(P T) ⊆ WF(T)`. Writing a
smooth complex coefficient as `u + i v`, this covers every linear differential operator with
smooth complex coefficients. -/
theorem waveFrontSet_sum_smul_smulLeftCLM_iteratedLineDerivOp_subset {ι : Type*}
    (s : Finset ι) (c : ι → ℂ) {a : ι → E → ℝ} (ha : ∀ i, ContDiff ℝ ∞ (a i)) {k : ι → ℕ}
    (m : ∀ i, Fin (k i) → E) (T : 𝓓'(Ω, ℂ)) :
    (∑ i ∈ s, c i • smulLeftCLM (ha i) (∂^{m i} T)).waveFrontSet ⊆ T.waveFrontSet :=
  (waveFrontSet_sum_subset s _).trans <| iUnion₂_subset fun i _ ↦
    (waveFrontSet_smul_subset _ _).trans <| (waveFrontSet_smulLeftCLM_subset _ _).trans <|
      inter_subset_left.trans (waveFrontSet_iteratedLineDerivOp_subset T (m i))

end FiniteDimensional

end Distribution
