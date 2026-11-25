/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.Pushforward
public import TauCeti.Analysis.Distribution.WaveFrontSet.Basic
import TauCeti.Algebra.Module.ZLattice.Summable
import TauCeti.Analysis.Calculus.BumpFunction.FiniteDimension
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity
import TauCeti.Analysis.Fourier.FourierCharDeriv
import TauCeti.Analysis.Fourier.NonstationaryPhase.Basic
import TauCeti.Analysis.Normed.Module.Cone
import TauCeti.Analysis.Normed.Operator.Prod
import TauCeti.Analysis.PositiveDefinite.FourierAtom
import TauCeti.Analysis.Distribution.WaveFrontSet.Localization

/-!
# The wave front set of a pushforward along a smooth map

Let `T` be a complex distribution on an open set `Ω` of a finite-dimensional real inner product
space `E`, and let `χ` be a test function on `Ω`. For a map `Φ : E → E'` smooth on `Ω` the
pushforward `Φ_* (χ T)` is the distribution `f ↦ T (χ (f ∘ Φ))` on an open set `Ω'` of `E'`
(`Distribution.cutoffPushforwardCLM`); when `χ` is equal to one near the support of `T`, which is
then compact, it is the pushforward `Φ_* T`, and for a projection it is integration over the
fibres. This file proves Hörmander's bound for its wave front set:

`WF(Φ_* (χ T)) ⊆ {(Φ x, η) | x ∈ supp χ ∩ supp T, DΦ(x)ᵀ η = 0 or (x, DΦ(x)ᵀ η) ∈ WF(T)}`.

The same bound holds for the pushforward `Φ_* T` along a smooth map proper on the support of `T`
(`Distribution.pushforward`), with `x` ranging over the support of `T` in `Ω`
(`Distribution.waveFrontSet_pushforward_subset`).

The localized Fourier transform of `Φ_* (χ T)` with cutoff `f` at `η` is `T` paired with
`x ↦ χ x f (Φ x) 𝐞 (-⟪Φ x, η⟫)`
(`Distribution.localFourier_cutoffPushforwardCLM_eq_complexPairing`).
For linear `Φ = A` the phase `⟪A x, η⟫ = ⟪x, Aᵀ η⟫` is linear and this is a localized Fourier
transform of `T` at the transposed frequency (`Distribution.localFourier_cutoffPushforwardCLM`). In
general the phase is not linear. Expanding the phase factor times an auxiliary smooth cutoff `ρ`,
equal to one near `supp φ`, in a Fourier series on a compact set
(`Distribution.exists_forall_hasSum_localFourier_of_eq_mul`) writes `T (φ 𝐞 (-⟪Φ ·, η⟫))` as
`∑ m, κ 𝓕 (ρ 𝐞 (-⟪Φ ·, η⟫)) (m) T (φ e_(-m))`. The terms with `-m` in a
cone where `T (φ e_ξ)` decays rapidly and `‖m‖ ≳ ‖η‖` are small by that decay; for all the others
the phase `⟪x, m⟫ + ⟪Φ x, η⟫` has gradient `m + DΦ(x)ᵀ η` bounded below by a multiple of
`‖m‖ + ‖η‖`, and the Fourier coefficient is small by non-stationary phase
(`TauCeti.exists_one_add_norm_pow_mul_norm_integral_fourierChar_le`). So if `DΦ(x)ᵀ η ≠ 0` and
`T` is microlocally smooth at `(x, DΦ(x)ᵀ η)`, the pairings `T (φ 𝐞 (-⟪Φ ·, η'⟫))` decay
rapidly for cutoffs `φ` near `x` and `η'` near the ray of `η`, and a cutoff around `y` pulls back
to a sum of such cutoffs over the compact set `supp χ ∩ supp T ∩ Φ⁻¹ {y}`.

The covectors with `DΦ(x)ᵀ η = 0` cannot be omitted, even for smooth `T`: along a constant map
with value `c` the pushforward of `T` is the multiple `T χ` of the point mass at `c`, and when
`T χ ≠ 0` its wave front set is `{c} × (E' \ {0})`
(`Distribution.waveFrontSet_cutoffPushforwardCLM_const`). When the differential of `Φ` is
surjective, its transpose is injective and these covectors do not occur.

For a linear map `A` and a fixed set `Γ`, the pushforwards of all distributions with wave front
set in `Γ` therefore have wave front set in one fixed set `TauCeti.pushforwardCone (supp χ) A Γ`,
which depends on `Γ` and `supp χ` but not on the distribution.

## Main results

* `Distribution.localFourier_cutoffPushforwardCLM`: localized Fourier transforms of `A_* (χ T)`,
  for linear `A`, are localized Fourier transforms of `T` at the transposed frequency.
* `Distribution.localFourier_cutoffPushforwardCLM_eq_complexPairing`: localized Fourier transforms
  of `Φ_* (χ T)` as pairings of `T` with `χ (f ∘ Φ) 𝐞 (-⟪Φ ·, η⟫)`.
* `Distribution.exists_one_add_norm_pow_mul_norm_complexPairing_le_of_phase`: rapid decay of
  `T (φ 𝐞 (-⟪Φ ·, η⟫))` when the pulled-back covectors `DΦ(x)ᵀ η` stay in a cone of decay of
  `T (φ e_ξ)`.
* `Distribution.IsMicrolocallySmoothAt.exists_nhds_cone_forall_decay_fourierChar`,
  `Distribution.exists_isOpen_cone_forall_decay_fourierChar_of_isCompact`: if `DΦ(x)ᵀ η ≠ 0`,
  microlocal smoothness at `(x, DΦ(x)ᵀ η)` gives this decay uniformly near `x`, and near a
  compact set of such `x`.
* `Distribution.IsMicrolocallySmoothAt.cutoffPushforwardCLM`: if `DΦ(x)ᵀ η ≠ 0` and `T` is
  microlocally smooth at `(x, DΦ(x)ᵀ η)` for every `x ∈ supp χ ∩ supp T` with `Φ x = y`, then
  `Φ_* (χ T)` is microlocally smooth at `(y, η)`.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset`: the wave front bound above.
* `Distribution.waveFrontSet_pushforward_subset`: the same bound for maps proper on the support.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset_of_surjective`: when `DΦ(x)` is surjective
  on `supp χ ∩ supp T`, `WF(Φ_* (χ T)) ⊆ {(Φ x, η) | x ∈ supp χ ∩ supp T, (x, DΦ(x)ᵀ η) ∈ WF(T)}`.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_const`: the pushforward along a constant map
  with value `c` has wave front set `{c} × (E' \ {0})` whenever `T χ ≠ 0`.
* `TauCeti.pushforwardCone K A Γ`: the set of covectors `(A x, η)`, `x ∈ K`, with
  `(x, Aᵀ η) ∈ Γ`, or `η ≠ 0` and `Aᵀ η = 0`.
* `Distribution.waveFrontSet_cutoffPushforwardCLM_subset_pushforwardCone`: the pushforward of a
  distribution with wave front set in `Γ` along a linear map has wave front set in the fixed set
  `pushforwardCone (supp χ) A Γ`, independent of the distribution.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.13 (the wave front set of a pushforward) and Theorem 7.7.1
  (non-stationary phase).
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction
open scoped Distributions Topology RealInnerProductSpace InnerProduct FourierTransform ContDiff
  Pointwise

namespace Distribution

variable {E E' : Type*} [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω' : Opens E'}

section Linear

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E} {χ : 𝓓(Ω, ℝ)}

/-- **Localized Fourier transforms of a pushforward.** The localized Fourier transform of the
pushforward `A_* (χ T)` along a linear map `A`, with cutoff `f`, at the frequency `η`, is that of
`T` with the cutoff `χ (f ∘ A)` at the transposed frequency `Aᵀ η`. -/
theorem localFourier_cutoffPushforwardCLM (A : E →L[ℝ] E') (T : 𝓓'(Ω, ℂ)) (f : 𝓓(Ω', ℂ))
    (η : E') :
    (cutoffPushforwardCLM χ A A.contDiff.contDiffOn T : 𝓓'(Ω', ℂ)).localFourier f η =
      T.localFourier (cutoffCompCLM χ A A.contDiff.contDiffOn f) ((A†) η) := by
  rw [localFourier_eq _ f (ψ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
    (TauCeti.contDiff_fourierAtom η) f) fun x => by
      simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply],
    complexPairing_cutoffPushforwardCLM]
  refine (localFourier_eq _ _ fun x => ?_).symm
  simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply,
    ContinuousLinearMap.adjoint_inner_right, mul_assoc]

end Linear

section Smooth

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] {Ω : Opens E}

/-- The covector `(z, w) ↦ ⟪m, z⟫ + ⟪η, w⟫` on `E × E'`. -/
private def pairCovector (m : E) (η : E') : E × E' →L[ℝ] ℝ :=
  (innerSL ℝ m).coprod (innerSL ℝ η)

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E] in
private theorem pairCovector_apply (m : E) (η : E') (z : E) (w : E') :
    pairCovector m η (z, w) = ⟪m, z⟫ + ⟪η, w⟫ := by
  simp [pairCovector]

/-- Composed with the differential `u ↦ (u, D u)` of `x ↦ (x, Φ x)`, the covector
`pairCovector m η` is the inner product with `m + Dᵀ η`. -/
private theorem pairCovector_comp_prod (m : E) (η : E') (D : E →L[ℝ] E') :
    pairCovector m η ∘L ((ContinuousLinearMap.id ℝ E).prod D) = innerSL ℝ (m + (D†) η) := by
  ext u
  simp [pairCovector, ContinuousLinearMap.adjoint_inner_left]

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E] in
private theorem norm_add_norm_le_two_mul_norm_pairCovector (m : E) (η : E') :
    ‖m‖ + ‖η‖ ≤ 2 * ‖pairCovector m η‖ := by
  have h1 := (innerSL ℝ m).opNorm_le_opNorm_coprod_left (innerSL ℝ η)
  have h2 := (innerSL ℝ m).opNorm_le_opNorm_coprod_right (innerSL ℝ η)
  rw [innerSL_apply_norm] at h1 h2
  rw [pairCovector]
  linarith

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E] in
private theorem norm_pairCovector_le (m : E) (η : E') :
    ‖pairCovector m η‖ ≤ ‖m‖ + ‖η‖ :=
  ((innerSL ℝ m).opNorm_coprod_le (innerSL ℝ η)).trans_eq
    (by rw [innerSL_apply_norm, innerSL_apply_norm])

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E] in
/-- **The phase is non-stationary away from the decay cone.** Let `ξ` be a covector with
`c ‖η‖ ≤ ‖ξ‖ ≤ M ‖η‖` whose conic ball `closedBall ξ (c ‖ξ‖)` lies in `Γ`. Unless `-m ∈ Γ` and
`‖m‖` is comparable to `‖η‖`, the covector `m + ξ` is bounded below by a fixed multiple of
`‖m‖ + ‖η‖`, hence of the norm of `pairCovector m η`. -/
private theorem mul_norm_pairCovector_le {Γ : Set E} {c M : ℝ} (hc : 0 < c) (hM : 0 ≤ M)
    {m ξ : E} {η : E'} (hξ : c * ‖η‖ ≤ ‖ξ‖) (hξM : ‖ξ‖ ≤ M * ‖η‖)
    (hball : closedBall ξ (c * ‖ξ‖) ⊆ Γ) (h : ¬(-m ∈ Γ ∧ min (c / 2) 1 * ‖η‖ ≤ ‖m‖)) :
    (1 + (M + 1) / min (c * c) (c / 2))⁻¹ * ‖pairCovector m η‖ ≤ ‖m + ξ‖ := by
  set α := min (c * c) (c / 2)
  have hα : 0 < α := lt_min (by positivity) (by positivity)
  -- The covector `m + ξ` is at least `α ‖η‖`.
  have hmξ : α * ‖η‖ ≤ ‖m + ξ‖ := by
    by_cases hm : -m ∈ Γ
    · have hlt : ‖m‖ < min (c / 2) 1 * ‖η‖ := lt_of_not_ge fun h' ↦ h ⟨hm, h'⟩
      have h1 : min (c / 2) 1 * ‖η‖ ≤ c / 2 * ‖η‖ := by gcongr; exact min_le_left _ _
      have h2 : α * ‖η‖ ≤ c / 2 * ‖η‖ := by gcongr; exact min_le_right _ _
      have h3 := norm_sub_norm_le ξ (-m)
      rw [sub_neg_eq_add, add_comm, norm_neg] at h3
      linarith
    · have h1 : c * ‖ξ‖ < ‖m + ξ‖ := by
        by_contra h1
        refine hm (hball (mem_closedBall.2 ?_))
        rw [dist_eq_norm, ← norm_neg, neg_sub, sub_neg_eq_add, add_comm]
        exact le_of_not_gt h1
      have h2 : α * ‖η‖ ≤ c * c * ‖η‖ := by gcongr; exact min_le_left _ _
      nlinarith
  -- Hence `‖m‖ + ‖η‖ ≤ (1 + (M + 1) / α) ‖m + ξ‖`.
  have hmm : ‖m‖ ≤ ‖m + ξ‖ + M * ‖η‖ := by
    have := norm_sub_le (m + ξ) ξ
    rw [add_sub_cancel_right] at this
    linarith
  have hη : (M + 1) * ‖η‖ ≤ (M + 1) / α * ‖m + ξ‖ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hα]
    nlinarith
  have hpos : 0 < 1 + (M + 1) / α := by positivity
  rw [inv_mul_le_iff₀ hpos]
  have := norm_pairCovector_le m η
  nlinarith

omit [FiniteDimensional ℝ E'] in
/-- A smooth map `Ψ` on all of `E` agreeing with `Φ` near a compact set `K ⊆ Ω`, written as an
oscillatory phase `x ↦ (x, Ψ x)`: the Fourier coefficients of `χ (𝐞 (-⟪Φ ·, η⟫))` on the support
of `χ` are oscillatory integrals with the phase `pairCovector m η ∘ (x ↦ (x, Ψ x))`. -/
private theorem exists_contDiff_fourier_eq [MeasurableSpace E] [BorelSpace E] {χ : E → ℝ}
    (hχc : HasCompactSupport χ) (hχΩ : tsupport χ ⊆ Ω) {Φ : E → E'} (hΦ : ContDiffOn ℝ ∞ Φ Ω) :
    ∃ Ψ : E → E', ContDiff ℝ ∞ Ψ ∧ (∀ x ∈ tsupport χ, fderiv ℝ Ψ x = fderiv ℝ Φ x) ∧
      ∀ (m : E) (η : E'), 𝓕 (fun x ↦ (χ x : ℂ) * 𝐞 (-⟪Φ x, η⟫)) m =
        ∫ x, 𝐞 (-pairCovector m η (x, Ψ x)) • (χ x : ℂ) := by
  obtain ⟨Ψ, hΨ, -, -, -, hΨK⟩ :=
    hΦ.exists_contDiff_eventuallyEq_on_isCompact hχc Ω.isOpen hχΩ
  refine ⟨Ψ, hΨ, fun x hx ↦ (hΨK x hx).fderiv_eq, fun m η ↦ ?_⟩
  rw [Real.fourier_eq]
  congr 1
  ext x
  by_cases hx : χ x = 0
  · simp [hx]
  · rw [pairCovector_apply, (hΨK x (subset_tsupport _ hx)).eq_of_nhds, neg_add,
      AddChar.map_add_eq_mul, real_inner_comm m x, real_inner_comm η (Φ x)]
    simp only [Circle.smul_def, smul_eq_mul, Circle.coe_mul]
    ring

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E] in
/-- A term of the expansion in the decay cone: if `(1 + ‖m‖) ^ (N + r) G ≤ Cd`, `F ≤ I` and
`ε (1 + ‖η‖) ≤ 1 + ‖m‖`, then `(1 + ‖η‖) ^ N (κ F G) ≤ κ I ε⁻ᴺ Cd (1 + ‖m‖) ^ (-r)`. -/
private theorem one_add_pow_mul_le_of_decay {a b κ F G I ε Cd : ℝ} {N r : ℕ} (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hε : 0 < ε) (hε1 : ε ≤ 1) (hab : ε * b ≤ a) (hκ : 0 ≤ κ) (hF0 : 0 ≤ F)
    (hF : F ≤ I) (hG0 : 0 ≤ G) (hG : (1 + a) ^ (N + r) * G ≤ Cd) :
    (1 + b) ^ N * (κ * F * G) ≤ κ * I * ε⁻¹ ^ N * Cd * ((1 + a) ^ r)⁻¹ := by
  have hba : 1 + b ≤ ε⁻¹ * (1 + a) := by rw [le_inv_mul_iff₀ hε]; nlinarith
  calc (1 + b) ^ N * (κ * F * G) ≤ (ε⁻¹ * (1 + a)) ^ N * (κ * I * G) := by gcongr
    _ = κ * I * ε⁻¹ ^ N * ((1 + a) ^ (N + r) * G) * ((1 + a) ^ r)⁻¹ := by
      rw [pow_add, mul_pow]; field_simp
    _ ≤ κ * I * ε⁻¹ ^ N * Cd * ((1 + a) ^ r)⁻¹ := by
      have hI : 0 ≤ κ * I * ε⁻¹ ^ N := by have := hF0.trans hF; positivity
      gcongr

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E] in
/-- A term of the expansion where the phase is non-stationary: if `G ≤ C₀ (1 + ‖m‖) ^ k`,
`(1 + ‖Λ‖) ^ (N + k + r) F ≤ CB` and `‖m‖ + ‖η‖ ≤ 2 ‖Λ‖`, then
`(1 + ‖η‖) ^ N (κ F G) ≤ κ C₀ 2 ^ (N + k + r) CB (1 + ‖m‖) ^ (-r)`. -/
private theorem one_add_pow_mul_le_of_nonstationary {a b l κ F G C₀ CB : ℝ} {N k r : ℕ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 2 * l) (hκ : 0 ≤ κ) (hF0 : 0 ≤ F) (hC₀ : 0 ≤ C₀)
    (hG : G ≤ C₀ * (1 + a) ^ k) (hF : (1 + l) ^ (N + k + r) * F ≤ CB) :
    (1 + b) ^ N * (κ * F * G) ≤ κ * C₀ * 2 ^ (N + k + r) * CB * ((1 + a) ^ r)⁻¹ := by
  have hab' : (1 + a) ^ (k + r) * (1 + b) ^ N ≤ 2 ^ (N + k + r) * (1 + l) ^ (N + k + r) := by
    rw [← mul_pow]
    calc (1 + a) ^ (k + r) * (1 + b) ^ N ≤ (1 + a + b) ^ (k + r) * (1 + a + b) ^ N :=
          mul_le_mul (pow_le_pow_left₀ (by positivity) (by linarith) _)
            (pow_le_pow_left₀ (by positivity) (by linarith) _) (by positivity) (by positivity)
      _ = (1 + a + b) ^ (N + k + r) := by rw [← pow_add]; ring_nf
      _ ≤ (2 * (1 + l)) ^ (N + k + r) := by gcongr; linarith
  calc (1 + b) ^ N * (κ * F * G) ≤ (1 + b) ^ N * (κ * F * (C₀ * (1 + a) ^ k)) := by gcongr
    _ = κ * C₀ * F * ((1 + a) ^ (k + r) * (1 + b) ^ N) * ((1 + a) ^ r)⁻¹ := by
      rw [pow_add]; field_simp
    _ ≤ κ * C₀ * F * (2 ^ (N + k + r) * (1 + l) ^ (N + k + r)) * ((1 + a) ^ r)⁻¹ := by gcongr
    _ = κ * C₀ * 2 ^ (N + k + r) * ((1 + l) ^ (N + k + r) * F) * ((1 + a) ^ r)⁻¹ := by ring
    _ ≤ κ * C₀ * 2 ^ (N + k + r) * CB * ((1 + a) ^ r)⁻¹ := by gcongr

/-- **Rapid decay of the Fourier coefficients against a nonlinear phase.** In the setting of
`Distribution.exists_one_add_norm_pow_mul_norm_complexPairing_le_of_phase`, let `χ` be a smooth
compactly supported function with `tsupport χ ⊆ U ∩ Ω`. Each term
`κ 𝓕 (χ 𝐞 (-⟪Φ ·, η⟫)) (m) T (φ e_(-m))` of the Fourier expansion of `T (φ 𝐞 (-⟪Φ ·, η⟫))` is
bounded by `C (1 + ‖η‖) ^ (-N) (1 + ‖m‖) ^ (-r)`: either `-m` lies in the decay cone with `‖m‖`
comparable to `‖η‖`, or the phase `⟪x, m⟫ + ⟪Φ x, η⟫` is non-stationary on `tsupport χ`. -/
private theorem exists_forall_one_add_pow_mul_norm_le [MeasurableSpace E] [BorelSpace E]
    {T : 𝓓'(Ω, ℂ)} {φ : 𝓓(Ω, ℂ)} {Γ : Set E}
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ξ ∈ Γ, (1 + ‖ξ‖) ^ N * ‖T.localFourier φ ξ‖ ≤ C)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) {U : Set E}
    (hχUΩ : tsupport χ ⊆ U ∩ Ω) {Φ : E → E'} (hΦ : ContDiffOn ℝ ∞ Φ Ω) {Γ' : Set E'} {c : ℝ}
    (hc : 0 < c) (hΓ' : ∀ x ∈ U, ∀ η ∈ Γ', c * ‖η‖ ≤ ‖((fderiv ℝ Φ x)†) η‖ ∧
      closedBall (((fderiv ℝ Φ x)†) η) (c * ‖((fderiv ℝ Φ x)†) η‖) ⊆ Γ) (κ : ℂ) (r N : ℕ) :
    ∃ C, ∀ η ∈ Γ', ∀ m : E, (1 + ‖η‖) ^ N * ‖κ * 𝓕 (fun x ↦ (χ x : ℂ) * 𝐞 (-⟪Φ x, η⟫)) m *
      T.localFourier φ (0 - m)‖ ≤ C * ((1 + ‖m‖) ^ r)⁻¹ := by
  obtain ⟨Ψ, hΨ, hdΦΨ, hcoef⟩ := exists_contDiff_fourier_eq hχc (hχUΩ.trans inter_subset_right) hΦ
  have hdΨ (x : E) : fderiv ℝ (fun y ↦ (y, Ψ y)) x =
      (ContinuousLinearMap.id ℝ E).prod (fderiv ℝ Ψ x) :=
    ((hasFDerivAt_id x).prodMk (hΨ.differentiable (by simp) x).hasFDerivAt).fderiv
  -- The constants: the bound `M` of `DΦ` on `tsupport χ`, the polynomial growth
  -- `C₀ (1 + ‖ξ‖) ^ k` of `ξ ↦ T (φ e_ξ)` and its decay `Cd` of order `N + r` on `Γ`.
  obtain ⟨M₀, hM₀⟩ := hχc.exists_bound_of_continuousOn (hΨ.continuous_fderiv (by simp)).continuousOn
  obtain ⟨C₀, k, hF⟩ := exists_norm_localFourier_le T φ
  have hC₀ : 0 ≤ C₀ := (norm_nonneg _).trans (by simpa using hF 0)
  obtain ⟨Cd, hCd⟩ := hdecay (N + r)
  set ε := min (c / 2) 1
  set c₀ := (1 + (max M₀ 0 + 1) / min (c * c) (c / 2))⁻¹
  obtain ⟨CB, hCB⟩ := TauCeti.exists_one_add_norm_pow_mul_norm_integral_fourierChar_le
    MeasureTheory.volume (ofRealCLM.contDiff.comp hχ) (hχc.comp_left ofReal_zero)
    (contDiff_id.prodMk hΨ) (inv_pos.2 (by positivity) : 0 < c₀) (N + k + r)
  refine ⟨max (‖κ‖ * (∫ x, ‖(χ x : ℂ)‖) * ε⁻¹ ^ N * Cd) (‖κ‖ * C₀ * 2 ^ (N + k + r) * CB),
    fun η hη m ↦ ?_⟩
  rw [norm_mul, norm_mul, zero_sub]
  by_cases hA : -m ∈ Γ ∧ ε * ‖η‖ ≤ ‖m‖
  · -- Frequencies `-m` in the decay cone, with `‖m‖ ≳ ‖η‖`: the decay of `T (φ e_(-m))`.
    refine (one_add_pow_mul_le_of_decay (I := ∫ x, ‖(χ x : ℂ)‖) (norm_nonneg _) (norm_nonneg _)
      (lt_min (by positivity)
        one_pos) (min_le_right _ _) hA.2 (norm_nonneg _) (norm_nonneg _)
      ((Real.norm_fourier_le_integral_norm _ _).trans_eq (by simp)) (norm_nonneg _)
      (by simpa using hCd (-m) hA.1)).trans (by gcongr; exact le_max_left _ _)
  -- Otherwise the phase is non-stationary: non-stationary phase and polynomial growth.
  have hnd : ∀ x ∈ tsupport (fun x ↦ (χ x : ℂ)),
      c₀ * ‖pairCovector m η‖ ≤ ‖pairCovector m η ∘L fderiv ℝ (fun y ↦ (y, Ψ y)) x‖ := by
    intro x hx
    have hxK : x ∈ tsupport χ := by
      exact tsupport_comp_subset ofReal_zero χ hx
    rw [hdΨ, pairCovector_comp_prod, innerSL_apply_norm, hdΦΨ x hxK]
    obtain ⟨h1, h2⟩ := hΓ' x (hχUΩ hxK).1 η hη
    refine mul_norm_pairCovector_le hc (le_max_right _ _) h1 ?_ h2 hA
    calc ‖((fderiv ℝ Φ x)†) η‖ ≤ ‖(fderiv ℝ Φ x)†‖ * ‖η‖ := ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ Φ x‖ * ‖η‖ := by rw [LinearIsometryEquiv.norm_map]
      _ ≤ max M₀ 0 * ‖η‖ := by
        gcongr
        exact (hdΦΨ x hxK ▸ hM₀ x hxK).trans (le_max_left _ _)
  have hB := hCB _ hnd
  simp only [id, Function.comp_apply, ofRealCLM_apply] at hB
  rw [← hcoef] at hB
  exact (one_add_pow_mul_le_of_nonstationary (norm_nonneg _) (norm_nonneg _)
    (norm_add_norm_le_two_mul_norm_pairCovector m η) (norm_nonneg _) (norm_nonneg _) hC₀
    (by simpa using hF (-m)) hB).trans (by gcongr; exact le_max_right _ _)

/-- **Rapid decay against a nonlinear phase.** Let `φ` be a cutoff whose localized Fourier
transform decays rapidly on a set `Γ`, and `Φ : E → E'` a map smooth on `Ω`. Suppose that on a
neighbourhood `U` of the support of `φ` the pulled-back covectors `ξ = DΦ(x)ᵀ η`, for `η` in a set
`Γ'`, satisfy `c ‖η‖ ≤ ‖ξ‖` and have their conic balls `closedBall ξ (c ‖ξ‖)` in `Γ`. Then
`T (φ 𝐞 (-⟪Φ ·, η⟫))` decays rapidly for `η ∈ Γ'`. For linear `Φ = A` this is the decay of the
localized Fourier transform of `T` on the cone `Aᵀ Γ'`; in general the phase `⟪Φ x, η⟫` is not
linear and is handled by non-stationary phase. -/
theorem exists_one_add_norm_pow_mul_norm_complexPairing_le_of_phase {T : 𝓓'(Ω, ℂ)}
    {φ : 𝓓(Ω, ℂ)} {Γ : Set E}
    (hdecay : ∀ N : ℕ, ∃ C, ∀ ξ ∈ Γ, (1 + ‖ξ‖) ^ N * ‖T.localFourier φ ξ‖ ≤ C)
    {U : Set E} (hU : IsOpen U) (hφU : tsupport φ ⊆ U) {Φ : E → E'} (hΦ : ContDiffOn ℝ ∞ Φ Ω)
    {Γ' : Set E'} {c : ℝ} (hc : 0 < c)
    (hΓ' : ∀ x ∈ U, ∀ η ∈ Γ', c * ‖η‖ ≤ ‖((fderiv ℝ Φ x)†) η‖ ∧
      closedBall (((fderiv ℝ Φ x)†) η) (c * ‖((fderiv ℝ Φ x)†) η‖) ⊆ Γ) (N : ℕ) :
    ∃ C, ∀ η ∈ Γ', ∀ ψ : 𝓓(Ω, ℂ), (∀ x, ψ x = φ x * 𝐞 (-⟪Φ x, η⟫)) →
      (1 + ‖η‖) ^ N * ‖T.complexPairing ψ‖ ≤ C := by
  borelize E
  -- The Fourier expansion of smooth multiples of `φ` on a compact set around its support.
  obtain ⟨L, κ, χ, hL, hχ, hχc, hχUΩ, hsum⟩ :=
    exists_forall_hasSum_localFourier_of_eq_mul T φ hU hφU
  set r := Module.finrank ℤ L + 1
  have hr := ZLattice.summable_one_add_norm_pow_inv L (r := r) (Nat.lt_succ_self _)
  obtain ⟨C, hC⟩ :=
    exists_forall_one_add_pow_mul_norm_le hdecay hχ hχc hχUΩ hΦ hc hΓ' κ r N
  refine ⟨C * ∑' m : L, ((1 + ‖(m : E)‖) ^ r)⁻¹, fun η hη ψ hψ ↦ ?_⟩
  -- Sum the bounds of the terms over `L`.
  have hs := hsum (hΦ.inner ℝ contDiffOn_const).neg.fourierChar hψ 0
  rw [localFourier_at_zero] at hs
  have hp : 0 < (1 + ‖η‖) ^ N := by positivity
  have hbound := hs.norm_le_of_bounded ((hr.hasSum.mul_left C).div_const ((1 + ‖η‖) ^ N))
    fun m ↦ by rw [le_div_iff₀ hp, mul_comm]; exact hC η hη m
  rw [le_div_iff₀ hp, mul_comm] at hbound
  exact hbound

/-- **Uniform localization along a smooth map.** If `T` is microlocally smooth at
`(x, DΦ(x)ᵀ η)` with `DΦ(x)ᵀ η ≠ 0`, then there are an open neighbourhood `V` of `x` and an open
cone `Γ'` around `η` such that for every cutoff `φ` supported in `V` the pairings
`T (φ 𝐞 (-⟪Φ ·, η'⟫))` decay rapidly for `η' ∈ Γ'`. For linear `Φ` this is
`Distribution.IsMicrolocallySmoothAt.exists_nhds_cone` along the transposed frequency. -/
theorem IsMicrolocallySmoothAt.exists_nhds_cone_forall_decay_fourierChar {T : 𝓓'(Ω, ℂ)}
    {Φ : E → E'} (hΦ : ContDiffOn ℝ ∞ Φ Ω) {x : E} {η : E'} (hξ : ((fderiv ℝ Φ x)†) η ≠ 0)
    (h : T.IsMicrolocallySmoothAt x (((fderiv ℝ Φ x)†) η)) :
    ∃ V : Set E, IsOpen V ∧ x ∈ V ∧ ∃ Γ' : Set E', IsOpen Γ' ∧ η ∈ Γ' ∧
      (∀ t : ℝ, 0 < t → ∀ η' ∈ Γ', t • η' ∈ Γ') ∧
      ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ V → ∀ N : ℕ, ∃ C, ∀ η' ∈ Γ', ∀ ψ : 𝓓(Ω, ℂ),
        (∀ y, ψ y = φ y * 𝐞 (-⟪Φ y, η'⟫)) → (1 + ‖η'‖) ^ N * ‖T.complexPairing ψ‖ ≤ C := by
  set ξ := ((fderiv ℝ Φ x)†) η
  have hx : x ∈ Ω := by
    obtain ⟨φ, hφ, -⟩ := isMicrolocallySmoothAt_iff.1 h
    exact φ.tsupport_subset (subset_tsupport _ hφ)
  obtain ⟨U, hU, Γ, hΓ, hξΓ, hcone, hdec⟩ := h.exists_nhds_cone
  obtain ⟨Γ₁, hΓ₁, hξΓ₁, hcone₁, c₁, hc₁, hball⟩ := hΓ.exists_cone_closedBall_subset hcone hξΓ
  have hη : 0 < ‖η‖ := norm_pos_iff.2 fun h0 ↦ hξ (by simp [ξ, h0])
  have hξ0 : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  set c₂ := ‖ξ‖ / (2 * ‖η‖)
  have hc₂ : 0 < c₂ := by positivity
  -- The set `S` of `(x', η')` with `DΦ(x')ᵀ η' ∈ Γ₁` and `c₂ ‖η'‖ < ‖DΦ(x')ᵀ η'‖` is a
  -- neighbourhood of `(x, η)`, and conic in `η'`.
  set G : E × E' → E := fun p ↦ ((fderiv ℝ Φ p.1)†) p.2
  have hG : ContinuousOn (fun p : E × E' ↦ (G p, p.2)) (Ω ×ˢ univ) :=
    ((((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := E')).continuous.comp_continuousOn
      ((hΦ.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).comp continuousOn_fst
        mapsTo_fst_prod)).clm_apply continuousOn_snd).prodMk continuousOn_snd)
  set S : Set (E × E') := {q | q.1 ∈ Γ₁ ∧ c₂ * ‖q.2‖ < ‖q.1‖}
  have hS : IsOpen S :=
    (hΓ₁.preimage continuous_fst).inter
      (isOpen_lt (continuous_const.mul continuous_snd.norm) continuous_fst.norm)
  have hmem : (x, η) ∈ (Ω ×ˢ univ : Set (E × E')) ∩ (fun p ↦ (G p, p.2)) ⁻¹' S := by
    refine ⟨⟨hx, mem_univ _⟩, hξΓ₁, ?_⟩
    simp only [c₂]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1
    ((hG.isOpen_inter_preimage (Ω.isOpen.prod isOpen_univ) hS).mem_nhds hmem)
  refine ⟨interior (u ∩ U), isOpen_interior, mem_interior_iff_mem_nhds.2 (inter_mem hu hU),
    ⋃ t ∈ Ioi (0 : ℝ), t • interior v,
    isOpen_biUnion fun t ht ↦ isOpen_interior.smul₀ (ne_of_gt ht),
    mem_iUnion₂.2 ⟨1, one_pos, by simpa using mem_interior_iff_mem_nhds.2 hv⟩, ?_, ?_⟩
  · rintro s hs η' hη'
    obtain ⟨t, ht, o, ho, rfl⟩ := by simpa [mem_iUnion₂, mem_smul_set] using hη'
    exact mem_iUnion₂.2 ⟨s * t, mul_pos hs ht, o, ho, by simp [smul_smul]⟩
  -- On `V × Γ'` the pulled-back covectors stay in `Γ₁` and are bounded below.
  have hVΓ' : ∀ x' ∈ interior (u ∩ U), ∀ η' ∈ ⋃ t ∈ Ioi (0 : ℝ), t • interior v,
      G (x', η') ∈ Γ₁ ∧ c₂ * ‖η'‖ < ‖G (x', η')‖ := by
    intro x' hx' η' hη'
    obtain ⟨t, ht, o, ho, rfl⟩ := by simpa [mem_iUnion₂, mem_smul_set] using hη'
    obtain ⟨-, h1, h2⟩ := huv (mk_mem_prod (interior_subset hx').1 (interior_subset ho))
    simp only [G, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h1 h2 ⊢
    exact ⟨hcone₁ t ht _ h1, by nlinarith⟩
  intro φ hφ N
  refine exists_one_add_norm_pow_mul_norm_complexPairing_le_of_phase
    (hdec φ (hφ.trans (interior_subset.trans inter_subset_right))) isOpen_interior hφ hΦ
    (lt_min hc₁ hc₂) (fun x' hx' η' hη' ↦ ⟨?_, ?_⟩) N
  · exact (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)).trans
      (hVΓ' x' hx' η' hη').2.le
  · exact (closedBall_subset_closedBall (mul_le_mul_of_nonneg_right (min_le_left _ _)
      (norm_nonneg _))).trans (hball _ (hVΓ' x' hx' η' hη').1)

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ E'] in
/-- Let `φ = φ₀ + ∑ᵢ φᵢ` with `φ₀` supported off the support of `T`. A bound on the pairings of
`T` with the pieces `φᵢ 𝐞 (-⟪Φ ·, η⟫)` bounds the pairing with `φ 𝐞 (-⟪Φ ·, η⟫)` by their sum. -/
private theorem one_add_pow_mul_norm_complexPairing_le_sum {T : 𝓓'(Ω, ℂ)} {Φ : E → E'}
    (hΦ : ContDiffOn ℝ ∞ Φ Ω) {φ φ₀ : 𝓓(Ω, ℂ)} {ι : Type*} [Fintype ι] {φs : ι → 𝓓(Ω, ℂ)}
    (hsum : φ₀ + ∑ i, φs i = φ) (hφ₀ : Disjoint (tsupport φ₀) (dsupport T)) {η : E'} {N : ℕ}
    {C : ι → ℝ} (hC : ∀ i, ∀ ψ : 𝓓(Ω, ℂ), (∀ y, ψ y = φs i y * 𝐞 (-⟪Φ y, η⟫)) →
      (1 + ‖η‖) ^ N * ‖T.complexPairing ψ‖ ≤ C i)
    {ψ : 𝓓(Ω, ℂ)} (hψ : ∀ y, ψ y = φ y * 𝐞 (-⟪Φ y, η⟫)) :
    (1 + ‖η‖) ^ N * ‖T.complexPairing ψ‖ ≤ ∑ i, C i := by
  have hmul (φ' : 𝓓(Ω, ℂ)) : ∃ ψ' : 𝓓(Ω, ℂ), ∀ y, ψ' y = φ' y * 𝐞 (-⟪Φ y, η⟫) :=
    (exists_coe_eq_smul_of_contDiffOn (hΦ.inner ℝ contDiffOn_const).neg.fourierChar φ').imp
      fun _ h y ↦ (congrFun h y).trans (mul_comm _ _)
  obtain ⟨ψ₀, hψ₀⟩ := hmul φ₀
  choose ψs hψs using fun i ↦ hmul (φs i)
  have hψsum : ψ = ψ₀ + ∑ i, ψs i := by
    ext y
    simp only [hψ, add_apply, sum_apply, hψ₀, hψs, ← Finset.sum_mul, ← add_mul, ← hsum]
  -- The piece `ψ₀` is supported off the support of `T`.
  have hψ₀T : T.complexPairing ψ₀ = 0 := by
    rw [← localFourier_at_zero, localFourier_eq_zero_of_disjoint_dsupport
      (hφ₀.mono_left (closure_mono fun y hy ↦ left_ne_zero_of_mul (by rwa [← hψ₀])))]
  rw [hψsum, map_add, hψ₀T, zero_add, map_sum]
  calc (1 + ‖η‖) ^ N * ‖∑ i, T.complexPairing (ψs i)‖
      ≤ ∑ i, (1 + ‖η‖) ^ N * ‖T.complexPairing (ψs i)‖ := by
        rw [← Finset.mul_sum]
        gcongr
        exact norm_sum_le _ _
    _ ≤ ∑ i, C i := Finset.sum_le_sum fun i _ ↦ hC i _ (hψs i)

/-- **Uniform localization along a smooth map over a compact set.** If `DΦ(x)ᵀ η ≠ 0` and `T` is
microlocally smooth at `(x, DΦ(x)ᵀ η)` for every `x` in a compact set `K`, then there are an
open set `W ⊇ K` and an open cone `Γ'` around `η` such that for every cutoff `φ` whose support
meets the support of `T` only inside `W`, the pairings `T (φ 𝐞 (-⟪Φ ·, η'⟫))` decay rapidly for
`η' ∈ Γ'`. -/
theorem exists_isOpen_cone_forall_decay_fourierChar_of_isCompact {T : 𝓓'(Ω, ℂ)} {Φ : E → E'}
    (hΦ : ContDiffOn ℝ ∞ Φ Ω) {K : Set E} (hK : IsCompact K) {η : E'}
    (h : ∀ x ∈ K, ((fderiv ℝ Φ x)†) η ≠ 0 ∧ T.IsMicrolocallySmoothAt x (((fderiv ℝ Φ x)†) η)) :
    ∃ W : Set E, IsOpen W ∧ K ⊆ W ∧ ∃ Γ' : Set E', IsOpen Γ' ∧ η ∈ Γ' ∧
      (∀ t : ℝ, 0 < t → ∀ η' ∈ Γ', t • η' ∈ Γ') ∧
      ∀ φ : 𝓓(Ω, ℂ), tsupport φ ⊆ W ∪ (dsupport T)ᶜ → ∀ N : ℕ, ∃ C, ∀ η' ∈ Γ', ∀ ψ : 𝓓(Ω, ℂ),
        (∀ y, ψ y = φ y * 𝐞 (-⟪Φ y, η'⟫)) → (1 + ‖η'‖) ^ N * ‖T.complexPairing ψ‖ ≤ C := by
  -- Finitely many of the neighbourhoods given by the pointwise statement cover `K`.
  choose V hV hxV Γ' hΓ' hηΓ' hcone hdecay using fun x : K ↦
    IsMicrolocallySmoothAt.exists_nhds_cone_forall_decay_fourierChar hΦ (h x x.property).1
      (h x x.property).2
  obtain ⟨t, ht, hΓt, hηΓt, hconet⟩ := TauCeti.exists_finset_subset_biUnion_interior_and_isOpen_cone
    hK (fun x ↦ (hV x).mem_nhds (hxV x)) hΓ' hηΓ' hcone
  refine ⟨⋃ x ∈ t, interior (V x), isOpen_biUnion fun _ _ ↦ isOpen_interior, ht, ⋂ x ∈ t, Γ' x,
    hΓt, hηΓt, hconet, fun φ hφ N ↦ ?_⟩
  -- Split `φ` into pieces supported in these neighbourhoods and one piece off the support of `T`.
  obtain ⟨φ₀, φs, hφ₀, hφs, hsum⟩ := φ.exists_add_sum_eq_of_tsupport_subset_biUnion_union
    (fun _ ↦ isOpen_interior) isClosed_dsupport.isOpen_compl hφ
  choose C hC using fun x : t ↦ hdecay x (φs x) ((hφs x).trans interior_subset) N
  exact ⟨∑ x, C x, fun η' hη' ψ hψ ↦ one_add_pow_mul_norm_complexPairing_le_sum hΦ hsum
    (disjoint_left.2 fun _ hz ↦ hφ₀ hz) (fun x ↦ hC x η' (mem_iInter₂.1 hη' x x.property)) hψ⟩

section Pushforward

variable {χ : 𝓓(Ω, ℝ)} {Φ : E → E'} {hΦ : ContDiffOn ℝ ∞ Φ Ω}

omit [FiniteDimensional ℝ E'] [FiniteDimensional ℝ E] in
/-- **Localized Fourier transforms of a pushforward along a smooth map.** The localized Fourier
transform of the pushforward `Φ_* (χ T)` with cutoff `f` at the frequency `η` pairs `T` with the
test function `x ↦ χ x f (Φ x) 𝐞 (-⟪Φ x, η⟫)`. For linear `Φ` it is a localized Fourier transform
of `T` (`Distribution.localFourier_cutoffPushforwardCLM`). -/
theorem localFourier_cutoffPushforwardCLM_eq_complexPairing (T : 𝓓'(Ω, ℂ)) (f : 𝓓(Ω', ℂ))
    (η : E') {ψ : 𝓓(Ω, ℂ)} (hψ : ∀ x, ψ x = cutoffCompCLM χ Φ hΦ f x * 𝐞 (-⟪Φ x, η⟫)) :
    (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).localFourier f η = T.complexPairing ψ := by
  rw [localFourier_eq _ f (ψ := bilinLeftCLM (ContinuousLinearMap.mul ℝ ℂ)
    (TauCeti.contDiff_fourierAtom η) f) fun x ↦ by
      simp [bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply],
    complexPairing_cutoffPushforwardCLM]
  congr 1
  ext x
  simp [hψ, bilinLeftCLM_apply, TauCeti.fourierAtom_eq_fourierChar, -TauCeti.fourierAtom_apply,
    mul_assoc]

/-- **Microlocal smoothness of a pushforward along a smooth map.** Let `y ∈ Ω'`. If for every
`x ∈ supp χ ∩ supp T` with `Φ x = y` the covector `DΦ(x)ᵀ η` is nonzero and `T` is microlocally
smooth at `(x, DΦ(x)ᵀ η)`, then the pushforward `Φ_* (χ T)` is microlocally smooth at `(y, η)`. -/
theorem IsMicrolocallySmoothAt.cutoffPushforwardCLM {T : 𝓓'(Ω, ℂ)} {y η : E'} (hy : y ∈ Ω')
    (h : ∀ x ∈ tsupport χ ∩ dsupport T, Φ x = y →
      ((fderiv ℝ Φ x)†) η ≠ 0 ∧ T.IsMicrolocallySmoothAt x (((fderiv ℝ Φ x)†) η)) :
    (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).IsMicrolocallySmoothAt y η := by
  set D := tsupport χ ∩ dsupport T
  have hD : IsCompact D := χ.hasCompactSupport.inter_right isClosed_dsupport
  have hDΩ : D ⊆ Ω := inter_subset_left.trans χ.tsupport_subset
  -- `T` decays uniformly against the phases over a neighbourhood `W` of `D ∩ Φ⁻¹ {y}`.
  have hDy : IsCompact (D ∩ Φ ⁻¹' {y}) := hD.of_isClosed_subset
    ((hΦ.continuousOn.mono hDΩ).preimage_isClosed_of_isClosed hD.isClosed isClosed_singleton)
    inter_subset_left
  obtain ⟨W, hW, hKW, Γ', hΓ', hηΓ', hcone', hdecay⟩ :=
    exists_isOpen_cone_forall_decay_fourierChar_of_isCompact hΦ hDy fun x hx ↦ h x hx.1 hx.2
  -- The compact set `Φ (D \ W)` misses `y`, so a cutoff `f` around `y` pulls back into
  -- `W ∪ (supp T)ᶜ`.
  have hC : IsCompact (Φ '' (D \ W)) :=
    (hD.diff hW).image_of_continuousOn (hΦ.continuousOn.mono (sdiff_subset.trans hDΩ))
  have hyC : y ∉ Φ '' (D \ W) := fun ⟨x, ⟨hxD, hxW⟩, hxy⟩ ↦ hxW (hKW ⟨hxD, hxy⟩)
  obtain ⟨f, hf, hfy⟩ := exists_tsupport_subset_apply_eq (n := ⊤)
    (inter_mem (hC.isClosed.isOpen_compl.mem_nhds hyC) (Ω'.isOpen.mem_nhds hy))
    inter_subset_right (1 : ℂ)
  set ψ₀ := cutoffCompCLM χ Φ hΦ f
  have hψ₀ : tsupport ψ₀ ⊆ W ∪ (dsupport T)ᶜ := fun z hz ↦ by
    by_contra hzW
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hzW
    obtain ⟨hzχ, hzf⟩ := tsupport_cutoffCompCLM_subset f hz
    exact (hf hzf).1 ⟨z, ⟨⟨hzχ, hzW.2⟩, hzW.1⟩, rfl⟩
  refine isMicrolocallySmoothAt_iff.2 ⟨f, by simp [hfy], Γ', hΓ', hηΓ', hcone', fun N ↦ ?_⟩
  obtain ⟨C, hC⟩ := hdecay ψ₀ hψ₀ N
  refine ⟨C, fun η' hη' ↦ ?_⟩
  -- The localized Fourier transform is `T` paired with `ψ₀ 𝐞 (-⟪Φ ·, η'⟫)`.
  obtain ⟨ψ, hψ⟩ :=
    exists_coe_eq_smul_of_contDiffOn (hΦ.inner ℝ contDiffOn_const).neg.fourierChar ψ₀
  have hψ' (x : E) : ψ x = ψ₀ x * 𝐞 (-⟪Φ x, η'⟫) := (congrFun hψ x).trans (mul_comm _ _)
  rw [localFourier_cutoffPushforwardCLM_eq_complexPairing T f η' hψ']
  exact hC η' hη' _ hψ'

/-- **The wave front set of a pushforward along a smooth map** (Hörmander I, Theorem 8.2.13).
Every covector `(y, η)` in the wave front set of the pushforward `Φ_* (χ T)` lies over a point `x`
of `supp χ ∩ supp T` with `Φ x = y`, at which either `DΦ(x)ᵀ η = 0` or `(x, DΦ(x)ᵀ η)` lies in the
wave front set of `T`. When `χ` is equal to one near the support of `T`, this is the bound for the
pushforward `Φ_* T` of a compactly supported distribution. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset (T : 𝓓'(Ω, ℂ)) :
    (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, Φ x = p.1 ∧
        (((fderiv ℝ Φ x)†) p.2 = 0 ∨ (x, ((fderiv ℝ Φ x)†) p.2) ∈ T.waveFrontSet)} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨hy, -, hS⟩ := mem_waveFrontSet_iff.1 hp
  by_contra hne
  refine hS (IsMicrolocallySmoothAt.cutoffPushforwardCLM hy fun x hx hxy ↦ ?_)
  have hxΩ : x ∈ Ω := χ.tsupport_subset hx.1
  by_cases hη : ((fderiv ℝ Φ x)†) η = 0
  · exact absurd ⟨x, hx, hxy, Or.inl hη⟩ hne
  refine ⟨hη, ?_⟩
  by_contra hT
  exact hne ⟨x, hx, hxy, Or.inr (mem_waveFrontSet_iff.2 ⟨hxΩ, hη, hT⟩)⟩

/-- **Pushforward along a submersion.** If the differential of `Φ` is surjective at every point of
`supp χ ∩ supp T`, its transpose is injective there, and every covector `(y, η)` in the wave front
set of `Φ_* (χ T)` lies over a point `x` of `supp χ ∩ supp T` with `Φ x = y` and `(x, DΦ(x)ᵀ η)`
in the wave front set of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset_of_surjective {T : 𝓓'(Ω, ℂ)}
    (hΦs : ∀ x ∈ tsupport χ ∩ dsupport T, Surjective (fderiv ℝ Φ x)) :
    (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | ∃ x ∈ tsupport χ ∩ dsupport T, Φ x = p.1 ∧
        (x, ((fderiv ℝ Φ x)†) p.2) ∈ T.waveFrontSet} := by
  rintro ⟨y, η⟩ hp
  obtain ⟨x, hx, hxy, h⟩ := waveFrontSet_cutoffPushforwardCLM_subset T hp
  refine ⟨x, hx, hxy, h.resolve_left fun h0 ↦ (mem_waveFrontSet_iff.1 hp).2.1 ?_⟩
  obtain ⟨z, hz⟩ := hΦs x hx η
  have h := ContinuousLinearMap.adjoint_inner_left (fderiv ℝ Φ x) z η
  rw [h0, inner_zero_left, hz] at h
  exact inner_self_eq_zero.1 h.symm

/-- **Hörmander's wave front bound for a pushforward along a map proper on the support.**
If the smooth map `Φ` is proper on the support of `T`, the pushforward `Φ_* T` satisfies
`WF(Φ_* T) ⊆ {(Φ x, η) | x ∈ Ω ∩ supp T, DΦ(x)ᵀ η = 0 or (x, DΦ(x)ᵀ η) ∈ WF(T)}`. -/
theorem waveFrontSet_pushforward_subset (T : 𝓓'(Ω, ℂ)) (hT : IsProperOnSupport T Φ Ω') :
    (pushforward T Φ hΦ hT : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      {p | ∃ x ∈ (Ω : Set E) ∩ dsupport T, Φ x = p.1 ∧
        (((fderiv ℝ Φ x)†) p.2 = 0 ∨ (x, ((fderiv ℝ Φ x)†) p.2) ∈ T.waveFrontSet)} := by
  -- Over a neighbourhood of each point of `Ω'`, `Φ_* T` is the pushforward of `T` with a cutoff
  -- (`Distribution.restrictCLM_pushforward`), to which
  -- `Distribution.waveFrontSet_cutoffPushforwardCLM_subset` applies.
  rintro ⟨y, η⟩ hp
  obtain ⟨K, hK, hyK, hKΩ'⟩ := exists_compact_subset Ω'.isOpen (mem_waveFrontSet_iff.1 hp).1
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) (hT.isCompact hK hKΩ')
    (inter_subset_left.trans inter_subset_left)
  -- Over the interior `U` of `K`, `Φ_* T` is the pushforward of `T` with the cutoff `χ`.
  let U : Opens E' := ⟨interior K, isOpen_interior⟩
  have h := waveFrontSet_inter_eq_of_restrictCLM_eq
    (SetLike.coe_subset_coe.1 (interior_subset.trans hKΩ'))
    (restrictCLM_pushforward (hΦ := hΦ) (hT := hT) (U := U) interior_subset hχ)
  have hp' : (y, η) ∈ (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', ℂ)).waveFrontSet ∩
      (U : Set E') ×ˢ univ := by
    rw [← h]
    exact ⟨hp, hyK, mem_univ η⟩
  obtain ⟨x, hx, hxy, hη⟩ := waveFrontSet_cutoffPushforwardCLM_subset T hp'.1
  exact ⟨x, ⟨χ.tsupport_subset hx.1, hx.2⟩, hxy, hη⟩

end Pushforward

end Smooth

section Const

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E} {χ : 𝓓(Ω, ℝ)}

/-- **The zero covectors cannot be omitted.** Pushing `T` forward along the constant map with
value `c ∈ Ω'` gives the multiple `T χ` of the point mass at `c`; if `T χ ≠ 0`, its wave front set
is `{c} × (E' \ {0})`, whatever the wave front set of `T`. The differential of a constant map is
zero, so its transpose kills every covector, and all these covectors come from the term
`DΦ(x)ᵀ η = 0` of `Distribution.waveFrontSet_cutoffPushforwardCLM_subset`. -/
theorem waveFrontSet_cutoffPushforwardCLM_const (T : 𝓓'(Ω, ℂ)) (hT : T χ ≠ 0) {c : E'}
    (hc : c ∈ Ω') :
    (cutoffPushforwardCLM χ (fun _ => c) contDiffOn_const T : 𝓓'(Ω', ℂ)).waveFrontSet =
      {c} ×ˢ {0}ᶜ := by
  have h : (cutoffPushforwardCLM χ (fun _ => c) contDiffOn_const T : 𝓓'(Ω', ℂ)) =
      T χ • mapCLM ofRealCLM (delta c : 𝓓'(Ω', ℝ)) := by
    rw [cutoffPushforwardCLM_const]
    ext f
    simp [mul_comm]
  rw [h, waveFrontSet_smul hT, waveFrontSet_delta hc]

end Const

end Distribution

namespace TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']

/-! ### A fixed target set for pushforwards -/

/-- The covectors `(A x, η)` with `x ∈ K` such that `(x, Aᵀ η) ∈ Γ`, or `η ≠ 0` and `Aᵀ η = 0`.
For `K = supp χ` it contains the wave front set of the pushforward `A_* (χ T)` of every
distribution `T` with wave front set in `Γ`
(`Distribution.waveFrontSet_cutoffPushforwardCLM_subset_pushforwardCone`). When `Γ` contains no
zero covectors, it consists of the nonzero covectors `(A x, η)`, `x ∈ K`, with
`(x, Aᵀ η) ∈ Γ ∪ (K × {0})`. -/
def pushforwardCone (K : Set E) (A : E →L[ℝ] E') (Γ : Set (E × E)) : Set (E' × E') :=
  {p | ∃ x ∈ K, A x = p.1 ∧ ((x, (A†) p.2) ∈ Γ ∨ (p.2 ≠ 0 ∧ (A†) p.2 = 0))}

@[simp]
theorem mem_pushforwardCone {K : Set E} {A : E →L[ℝ] E'} {Γ : Set (E × E)} {p : E' × E'} :
    p ∈ pushforwardCone K A Γ ↔
      ∃ x ∈ K, A x = p.1 ∧ ((x, (A†) p.2) ∈ Γ ∨ (p.2 ≠ 0 ∧ (A†) p.2 = 0)) :=
  Iff.rfl

/-- `pushforwardCone K A Γ` is monotone in `K` and in `Γ`. -/
theorem pushforwardCone_mono {K K' : Set E} {A : E →L[ℝ] E'} {Γ Γ' : Set (E × E)} (hK : K ⊆ K')
    (hΓ : Γ ⊆ Γ') : pushforwardCone K A Γ ⊆ pushforwardCone K' A Γ' :=
  fun _ ⟨x, hx, hxp, h⟩ ↦ ⟨x, hK hx, hxp, h.imp_left fun h ↦ hΓ h⟩

/-- Over a point `A x` with `x ∈ K`, a frequency `η` outside `pushforwardCone K A Γ` has
`(x, Aᵀ η) ∉ Γ`. -/
theorem notMem_of_notMem_pushforwardCone {K : Set E} {A : E →L[ℝ] E'} {Γ : Set (E × E)} {x : E}
    (hx : x ∈ K) {η : E'} (h : (A x, η) ∉ pushforwardCone K A Γ) : (x, (A†) η) ∉ Γ :=
  fun hΓ ↦ h ⟨x, hx, rfl, .inl hΓ⟩

/-- Over a point `A x` with `x ∈ K`, a frequency `η` outside `pushforwardCone K A Γ` with
`Aᵀ η = 0` is zero. -/
theorem eq_zero_of_adjoint_apply_eq_zero_of_notMem_pushforwardCone {K : Set E} {A : E →L[ℝ] E'}
    {Γ : Set (E × E)} {x : E} (hx : x ∈ K) {η : E'} (h : (A x, η) ∉ pushforwardCone K A Γ)
    (h0 : (A†) η = 0) : η = 0 :=
  by_contra fun hη ↦ h ⟨x, hx, rfl, .inr ⟨hη, h0⟩⟩

end TauCeti

namespace Distribution

open TauCeti

variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℝ E'] [FiniteDimensional ℝ E']
  {Ω : Opens E} {Ω' : Opens E'}

/-- **The wave front set of a pushforward lies in a fixed set.** If the wave front set of `T` lies
in `Γ`, the wave front set of the pushforward `A_* (χ T)` lies in `pushforwardCone (supp χ) A Γ`,
a set independent of `T`. -/
theorem waveFrontSet_cutoffPushforwardCLM_subset_pushforwardCone (χ : 𝓓(Ω, ℝ))
    (A : E →L[ℝ] E') {Γ : Set (E × E)} {T : 𝓓'(Ω, ℂ)} (hT : T.waveFrontSet ⊆ Γ) :
    (cutoffPushforwardCLM χ A A.contDiff.contDiffOn T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆
      pushforwardCone (tsupport χ) A Γ := fun p hp ↦ by
  obtain ⟨x, hx, hxp, h⟩ := waveFrontSet_cutoffPushforwardCLM_subset T hp
  rw [A.fderiv] at h
  exact ⟨x, hx.1, hxp, h.symm.imp (fun h ↦ hT h) fun h ↦ ⟨(mem_waveFrontSet_iff.1 hp).2.1, h⟩⟩

end Distribution
