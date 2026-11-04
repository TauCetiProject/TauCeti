/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Cone
public import TauCeti.Analysis.Distribution.Mass.Augmentation
public import TauCeti.Analysis.Distribution.Mass.Normal
import TauCeti.Analysis.Distribution.TestFunction.PartitionOfUnity

/-!
# Mass bounds and normality for the Euclidean cone over a current

Let `Ω` be an open subset of a finite-dimensional real normed space `E` and let `x₀ : E` be a
cone apex. Pairing the Euclidean cone `Distribution.cone x₀ T` with a test `(k + 1)`-form `ω` of
supremum norm at most `1` evaluates `T` on `χ • poincareHomotopy x₀ ω`, where `χ : 𝓓(Ω, ℝ)` is a
cutoff equal to `1` near `dsupport T` with values in `[0, 1]`. By the sharp radial estimate
`‖poincareHomotopy x₀ ω x‖ ≤ ‖x - x₀‖ / (k + 1)`, localizing `χ` to a ball around `x₀` yields the
sharp Euclidean radius mass bound

`mass (cone x₀ T) ≤ ENNReal.ofReal (r / (k + 1)) * mass T`

whenever `dsupport T ⊆ Metric.ball x₀ r` (`Distribution.mass_cone_le_of_subset_ball`), with no
finiteness hypothesis on `mass T` and no sign assumption on `r`. Passing to open neighbourhoods of
a closed ball extends the bound to `dsupport T ⊆ Metric.closedBall x₀ r` whenever `0 < r` or
`mass T ≠ ⊤` (`Distribution.mass_cone_le_of_subset_closedBall`), and in particular unconditionally
for every current of locally finite mass (`Distribution.HasLocallyFiniteMass.mass_cone_le`). Note
that at `r = 0` a first-order distribution supported at `{x₀}` has infinite mass while its cone can
have nonzero finite mass, whereas `0 * ⊤ = 0` in `ℝ≥0∞`; the hypothesis `0 < r ∨ mass T ≠ ⊤`
precisely rules out this degenerate case, and for locally finite-mass currents supported in `{x₀}`
the cone vanishes (`Distribution.HasLocallyFiniteMass.cone_eq_zero_of_dsupport_subset_singleton`).

Combining the mass bound with the positive-degree and degree-zero homotopy boundary formulas shows
that `cone x₀ T` is always a normal current whenever `T` is locally normal or normal
(`Distribution.IsLocallyNormal.isNormal_cone`, `Distribution.IsNormal.cone`), without any geometric
assumption on `Ω`. When `Metric.ball x₀ r ⊆ Ω`, this yields compactly supported normal fillings in
`Metric.ball x₀ r` with radius-controlled mass both for positive-degree cycles and for
augmented-zero `0`-currents. In degree zero, an augmented-zero two-point difference `δ_q - δ_p` in
a ball is filled by a normal `1`-current supported in `segment ℝ p q` of mass at most
`dist q p * ‖ℓ‖ ≤ 2 r * ‖ℓ‖`, whereas a single current with nonzero augmentation admits no
compactly supported filling on `Ω` even though its ordinary `0`-current boundary is zero.

## Main declarations

* `Distribution.mass_cone_le_of_subset_ball`,
  `Distribution.mass_cone_le_of_subset_closedBall`,
  `Distribution.HasLocallyFiniteMass.mass_cone_le`,
  `Distribution.HasLocallyFiniteMass.mass_cone_le_nnreal`: the sharp radius mass bound
  `M(cone x₀ T) ≤ r / (k + 1) * M(T)`.
* `Distribution.HasLocallyFiniteMass.cone_eq_zero_of_dsupport_subset_singleton`: a locally
  finite-mass current supported in `{x₀}` has zero cone at `x₀`.
* `Distribution.mass_cone_ne_top`, `Distribution.HasLocallyFiniteMass.mass_cone_ne_top`: finiteness
  of the mass of `cone x₀ T`.
* `Distribution.mass_cone_finZero_comp_extDerivCLM_le`,
  `Distribution.mass_cone_comp_extDerivCLM_le_of_subset_ball`: mass bounds on `∂ (cone x₀ T)`.
* `Distribution.IsLocallyNormal.isNormal_cone`, `Distribution.IsNormal.cone`: `cone x₀` sends
  locally normal and normal currents to normal currents.
* `Distribution.exists_isNormal_comp_extDerivCLM_eq_of_subset_ball`,
  `Distribution.exists_isNormal_comp_extDerivCLM_finZero_eq_of_subset_ball`: normal fillings with
  compact support in a ball and radius-controlled mass for positive-degree cycles and
  augmented-zero `0`-currents.
* `Distribution.mass_cone_comp_evalCLM_le`,
  `Distribution.exists_isNormal_comp_extDerivCLM_eq_sub_comp_evalCLM_finZero_of_mem_ball`:
  cone mass bound on point currents and normal segment-supported filling of two-point differences
  in a ball with radius-controlled mass (contrasting with
  `Distribution.not_exists_comp_extDerivCLM_eq_comp_evalCLM` for a single nonzero point current).

## References

* H. Federer, *Geometric Measure Theory*, §4.1.11 (cones over currents) and §4.2.9–4.2.10 (cone
  mass estimates).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

noncomputable section

open ContinuousLinearMap Filter Set TopologicalSpace TauCeti
open scoped BoundedContinuousFunction Distributions ENNReal NNReal Topology

namespace Distribution

variable {E F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : Opens E} {k : ℕ}

section MassBounds

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- Helper extracting compactness and inclusion in `Ω` whenever a cutoff exists near
`dsupport T`. -/
private theorem isCompact_and_subset_of_exists_cutoff
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    IsCompact (dsupport T) ∧ dsupport T ⊆ Ω := by
  obtain ⟨χ, hχ⟩ := h
  have hsub : dsupport T ⊆ tsupport χ := fun x hx ↦
    subset_tsupport _ (by simp [hχ.self_of_nhdsSet x hx])
  exact ⟨χ.hasCompactSupport.of_isClosed_subset isClosed_dsupport hsub,
    hsub.trans χ.tsupport_subset⟩

/-- **Sharp Euclidean open-ball mass bound for the cone.** If `dsupport T ⊆ Metric.ball x₀ r`,
then `mass (cone x₀ T) ≤ ENNReal.ofReal (r / (k + 1)) * mass T`. Neither finiteness of `mass T`,
compactness of `dsupport T`, nor nonnegativity of `r` is assumed. -/
theorem mass_cone_le_of_subset_ball (x₀ : E) {r : ℝ}
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : dsupport T ⊆ Metric.ball x₀ r) :
    mass (cone x₀ T) ≤ ENNReal.ofReal (r / (k + 1)) * mass T := by
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨hc, hΩ⟩ := isCompact_and_subset_of_exists_cutoff h
    rcases le_or_gt r 0 with hr | hr
    · rw [Metric.ball_eq_empty.2 hr] at hT
      have hT0 : T = 0 :=
        DFunLike.coe_injective ((dsupport_eq_empty_iff T).1 (subset_empty_iff.1 hT))
      simp [hT0]
    · let U : Opens E := Ω ⊓ ⟨Metric.ball x₀ r, Metric.isOpen_ball⟩
      have hTU : dsupport T ⊆ (U : Set E) := subset_inter hΩ hT
      obtain ⟨ψ, hψ, hψ01⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hc hTU
      let χ : 𝓓(Ω, ℝ) := TestFunction.monoCLM ℝ ψ
      have hUΩ : U ≤ Ω := inf_le_left
      have hcoe : (χ : E → ℝ) = ψ := by simp [χ, TestFunction.monoCLM_apply, hUΩ]
      have hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1 := hψ.mono fun x hx ↦ by simp [hcoe, hx]
      have hχball : tsupport (χ : E → ℝ) ⊆ Metric.ball x₀ r := by
        rw [hcoe]
        exact ψ.tsupport_subset.trans inter_subset_right
      refine mass_le_iff.2 fun ω hω ↦ ?_
      rw [cone_apply x₀ T hχ ω, mul_comm, ← localMass_univ]
      refine enorm_apply_le_localMass_mul_of_forall_enorm_le T (subset_univ _) fun x ↦ ?_
      by_cases hx : x ∈ tsupport (χ : E → ℝ)
      · have hdist : ‖x - x₀‖ ≤ r := (mem_ball_iff_norm.1 (hχball hx)).le
        have hχx : |χ x| ≤ 1 := by
          rw [hcoe, abs_of_nonneg (hψ01 x).1]
          exact (hψ01 x).2
        rw [← ofReal_norm]
        refine ENNReal.ofReal_le_ofReal ?_
        refine (TestFunction.norm_smulPoincareHomotopyCLM_apply_le x₀ χ ω
          (fun y _ ↦ hω y)).trans ?_
        have hpos : (0 : ℝ) ≤ (k + 1 : ℝ) := by positivity
        calc |χ x| * (1 * ‖x - x₀‖ / (k + 1))
            ≤ 1 * (1 * r / (k + 1)) := by
              gcongr
          _ = r / (k + 1) := by ring
      · have hzero : TestFunction.smulPoincareHomotopyCLM x₀ χ ω x = 0 :=
          image_eq_zero_of_notMem_tsupport fun hmem ↦
            hx (TestFunction.tsupport_smulPoincareHomotopyCLM_subset_left x₀ χ ω hmem)
        rw [hzero, ← ofReal_norm, norm_zero, ENNReal.ofReal_zero]
        exact zero_le
  · simp [cone_of_not_exists x₀ h]

/-- **Sharp Euclidean closed-ball mass bound for the cone.** If
`dsupport T ⊆ Metric.closedBall x₀ r` and either `0 < r` or `mass T ≠ ⊤`, then
`mass (cone x₀ T) ≤ ENNReal.ofReal (r / (k + 1)) * mass T`. At `r = 0`, `mass T ≠ ⊤` cannot be
dropped because `0 * ⊤ = 0` in `ℝ≥0∞` while higher-order point distributions at `x₀` can have
nonzero finite-mass cones. -/
theorem mass_cone_le_of_subset_closedBall (x₀ : E) {r : ℝ}
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : dsupport T ⊆ Metric.closedBall x₀ r) (hrT : 0 < r ∨ mass T ≠ ⊤) :
    mass (cone x₀ T) ≤ ENNReal.ofReal (r / (k + 1)) * mass T := by
  rcases lt_or_ge r 0 with hr | hr
  · rw [Metric.closedBall_eq_empty.2 hr] at hT
    have hT0 : T = 0 := DFunLike.coe_injective ((dsupport_eq_empty_iff T).1 (subset_empty_iff.1 hT))
    simp [hT0]
  rcases eq_or_ne (mass T) ⊤ with htop | hM
  · rcases hrT with hrpos | hne
    · have hne0 : ENNReal.ofReal (r / (k + 1)) ≠ 0 :=
        (ENNReal.ofReal_pos.2 (by positivity)).ne'
      rw [htop, ENNReal.mul_top hne0]
      exact le_top
    · exact absurd htop hne
  rcases eq_or_ne (mass T) 0 with hM0 | hM0
  · have hT0 : T = 0 := DFunLike.coe_injective ((mass_eq_zero_iff T).1 hM0)
    simp [hT0]
  have hcone_lt : mass (cone x₀ T) < ⊤ := by
    refine (mass_cone_le_of_subset_ball x₀ (r := r + 1)
      (hT.trans (Metric.closedBall_subset_ball (lt_add_one r)))).trans_lt ?_
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM.lt_top
  have hMpos : 0 < (mass T).toReal := ENNReal.toReal_pos hM0 hM
  rw [← ENNReal.ofReal_toReal hcone_lt.ne, ← ENNReal.ofReal_toReal hM,
    ← ENNReal.ofReal_mul (div_nonneg hr (by positivity))]
  refine ENNReal.ofReal_le_ofReal (le_of_forall_pos_le_add fun ε hε ↦ ?_)
  have hkpos : (0 : ℝ) < k + 1 := by positivity
  let δ : ℝ := ε * (k + 1) / (mass T).toReal
  have hδ : 0 < δ := by positivity
  have hstep := mass_cone_le_of_subset_ball x₀ (r := r + δ)
    (hT.trans (Metric.closedBall_subset_ball (lt_add_of_pos_right r hδ)))
  rw [← ENNReal.ofReal_toReal hcone_lt.ne, ← ENNReal.ofReal_toReal hM,
    ← ENNReal.ofReal_mul (by positivity)] at hstep
  have hreal := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hstep
  refine hreal.trans_eq ?_
  have hMne : (mass T).toReal ≠ 0 := hMpos.ne'
  have hkne : (k + 1 : ℝ) ≠ 0 := hkpos.ne'
  dsimp only [δ]
  field_simp [hMne, hkne]

/-- **Closed-ball cone mass bound for currents of locally finite mass.** Whenever `T` has locally
finite mass and `dsupport T ⊆ Metric.closedBall x₀ r`,
`mass (cone x₀ T) ≤ ENNReal.ofReal (r / (k + 1)) * mass T` (including at `r = 0`). -/
theorem HasLocallyFiniteMass.mass_cone_le (x₀ : E) {r : ℝ}
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : HasLocallyFiniteMass T) (hsub : dsupport T ⊆ Metric.closedBall x₀ r) :
    mass (cone x₀ T) ≤ ENNReal.ofReal (r / (k + 1)) * mass T := by
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨hc, hΩ⟩ := isCompact_and_subset_of_exists_cutoff h
    exact mass_cone_le_of_subset_closedBall x₀ hsub (Or.inr (hT.mass_ne_top hc hΩ))
  · simp [cone_of_not_exists x₀ h]

/-- `ℝ≥0`-radius form of `Distribution.HasLocallyFiniteMass.mass_cone_le`. -/
theorem HasLocallyFiniteMass.mass_cone_le_nnreal (x₀ : E) {r : ℝ≥0}
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : HasLocallyFiniteMass T) (hsub : dsupport T ⊆ Metric.closedBall x₀ r) :
    mass (cone x₀ T) ≤ (r : ℝ≥0∞) / (k + 1) * mass T := by
  refine (hT.mass_cone_le x₀ hsub).trans_eq ?_
  rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_coe_nnreal]
  have hk : ENNReal.ofReal ((k : ℝ) + 1) = (k : ℝ≥0∞) + 1 := by
    rw [← Nat.cast_one, ← Nat.cast_add, ENNReal.ofReal_natCast, Nat.cast_add, Nat.cast_one]
  rw [hk]

/-- If `T` has locally finite mass and is supported in `{x₀}`, then `cone x₀ T = 0`. -/
theorem HasLocallyFiniteMass.cone_eq_zero_of_dsupport_subset_singleton {x₀ : E}
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : HasLocallyFiniteMass T) (hsub : dsupport T ⊆ {x₀}) :
    cone x₀ T = 0 := by
  have hball : dsupport T ⊆ Metric.closedBall x₀ 0 := by
    rwa [Metric.closedBall_zero]
  have h0 : mass (cone x₀ T) ≤ 0 := by
    simpa using hT.mass_cone_le x₀ hball
  exact DFunLike.coe_injective ((mass_eq_zero_iff (cone x₀ T)).1 (nonpos_iff_eq_zero.1 h0))

/-- If `T` has finite mass, then `cone x₀ T` has finite mass. -/
theorem mass_cone_ne_top (x₀ : E) {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : mass T ≠ ⊤) : mass (cone x₀ T) ≠ ⊤ := by
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨hc, -⟩ := isCompact_and_subset_of_exists_cutoff h
    obtain ⟨r, hr⟩ := hc.isBounded.subset_ball x₀
    exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hT)
      (mass_cone_le_of_subset_ball x₀ hr)
  · simp [cone_of_not_exists x₀ h]

/-- If `T` has locally finite mass, then `cone x₀ T` has finite total mass: either no cutoff exists
and `cone x₀ T = 0`, or `dsupport T` is compact in `Ω` so `T` itself has finite mass. -/
theorem HasLocallyFiniteMass.mass_cone_ne_top (x₀ : E)
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : HasLocallyFiniteMass T) : mass (cone x₀ T) ≠ ⊤ := by
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨hc, hΩ⟩ := isCompact_and_subset_of_exists_cutoff h
    exact Distribution.mass_cone_ne_top x₀ (hT.mass_ne_top hc hΩ)
  · simp [cone_of_not_exists x₀ h]

/-- **Degree-zero cone boundary mass bound.** For a `0`-current `T` with compact support in `Ω`,
`∂ (cone x₀ T) = T - (ev_{x₀})^* (augmentation T)` has mass at most `2 * mass T`. -/
theorem mass_cone_finZero_comp_extDerivCLM_le (x₀ : E)
    {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    mass ((cone x₀ T) ∘L TestFunction.extDerivCLM) ≤ 2 * mass T := by
  rw [two_mul]
  refine mass_le_iff.2 fun ω hω ↦ ?_
  rw [cone_comp_extDerivCLM_finZero_apply x₀ hT hTΩ ω]
  refine (enorm_sub_le).trans (add_le_add (enorm_le_mass hω) ?_)
  have haug := enorm_augmentation_le_mass_mul T hT hTΩ (ω x₀)
  have hωx₀ : ‖ω x₀‖ₑ ≤ 1 := by simpa [← ofReal_norm] using hω x₀
  exact haug.trans (mul_le_of_le_one_right zero_le hωx₀)

/-- **Positive-degree cone boundary mass bound.** For a `(k + 1)`-current `T` with compact support
in `Ω` and `dsupport T ⊆ Metric.ball x₀ r`,
`mass (∂ (cone x₀ T)) ≤ mass T + ENNReal.ofReal (r / (k + 1)) * mass (∂ T)`. -/
theorem mass_cone_comp_extDerivCLM_le_of_subset_ball (x₀ : E) {r : ℝ}
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V}
    (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω)
    (hball : dsupport T ⊆ Metric.ball x₀ r) :
    mass ((cone x₀ T) ∘L TestFunction.extDerivCLM) ≤
      mass T + ENNReal.ofReal (r / (k + 1)) * mass (T ∘L TestFunction.extDerivCLM) := by
  rw [cone_comp_extDerivCLM x₀ hT hTΩ, FunLike.coe_sub]
  refine mass_sub_le.trans (add_le_add le_rfl ?_)
  have hsub : dsupport (T ∘L TestFunction.extDerivCLM) ⊆ Metric.ball x₀ r := by
    rw [coe_comp]
    exact (dsupport_comp_extDerivCLM_subset T).trans hball
  exact mass_cone_le_of_subset_ball x₀ hsub

/-- **The Euclidean cone over a locally normal current is normal.** No geometric assumption on `Ω`
or compactness hypothesis on `dsupport T` is needed: when no cutoff exists `cone x₀ T = 0`, and
when a cutoff exists `dsupport T` is compact in `Ω`. -/
theorem IsLocallyNormal.isNormal_cone (x₀ : E) {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : IsLocallyNormal T) : IsNormal (cone x₀ T) := by
  by_cases h : ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1
  · obtain ⟨hc, hΩ⟩ := isCompact_and_subset_of_exists_cutoff h
    have hTN : IsNormal T := hT.isNormal hc hΩ
    rw [isNormal_succ_iff]
    refine ⟨Distribution.mass_cone_ne_top x₀ hTN.mass_ne_top, ?_⟩
    cases k with
    | zero =>
      exact ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hTN.mass_ne_top)
        (mass_cone_finZero_comp_extDerivCLM_le x₀ hc hΩ)
    | succ j =>
      obtain ⟨hM1, hM2⟩ := isNormal_succ_iff.1 hTN
      rw [cone_comp_extDerivCLM x₀ hc hΩ, FunLike.coe_sub]
      exact ne_top_of_le_ne_top
        (ENNReal.add_ne_top.2 ⟨hM1, Distribution.mass_cone_ne_top x₀ hM2⟩) mass_sub_le
  · rw [cone_of_not_exists x₀ h]
    exact isNormal_zero

/-- **The Euclidean cone over a normal current is normal.** -/
theorem IsNormal.cone (x₀ : E) {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : IsNormal T) : IsNormal (cone x₀ T) :=
  hT.isLocallyNormal.isNormal_cone x₀

end MassBounds

section Filling

/-- **Small-ball cycle filling in positive degree.** Every closed `(k + 1)`-current `T` (`∂ T = 0`)
of locally finite mass whose support is a compact subset of `Metric.ball x₀ r ⊆ Ω` bounds a normal
`(k + 2)`-current `Q` (namely `cone x₀ T`) with compact support in `Metric.ball x₀ r` and
`mass Q ≤ ENNReal.ofReal (r / (k + 2)) * mass T`. -/
theorem exists_isNormal_comp_extDerivCLM_eq_of_subset_ball {x₀ : E} {r : ℝ}
    (hballΩ : Metric.ball x₀ r ⊆ Ω)
    {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V}
    (hT : HasLocallyFiniteMass T) (hc : IsCompact (dsupport T))
    (hsub : dsupport T ⊆ Metric.ball x₀ r) (hcycle : T ∘L TestFunction.extDerivCLM = 0) :
    ∃ Q : 𝓓(Ω, E [⋀^Fin (k + 2)]→L[ℝ] F) →L[ℝ] V,
      IsNormal Q ∧ IsCompact (dsupport Q) ∧ dsupport Q ⊆ Metric.ball x₀ r ∧
        Q ∘L TestFunction.extDerivCLM = T ∧
        mass Q ≤ ENNReal.ofReal (r / (k + 2)) * mass T := by
  have hln : IsLocallyNormal T := by
    rw [isLocallyNormal_succ_iff, hcycle]
    exact ⟨hT, by simpa using hasLocallyFiniteMass_zero⟩
  refine ⟨cone x₀ T, hln.isNormal_cone x₀, isCompact_dsupport_cone x₀ T, ?_,
    cone_comp_extDerivCLM_of_eq_zero x₀ hc (hsub.trans hballΩ) hcycle, ?_⟩
  · rcases le_or_gt r 0 with hr | hr
    · rw [Metric.ball_eq_empty.2 hr] at hsub
      have hT0 : T = 0 :=
        DFunLike.coe_injective ((dsupport_eq_empty_iff T).1 (subset_empty_iff.1 hsub))
      rw [hT0, cone_zero, (dsupport_eq_empty_iff (0 : _ →L[ℝ] V)).2 rfl]
      exact empty_subset _
    · exact (dsupport_cone_subset x₀ T).trans <| iUnion₂_subset fun x hx ↦
        (convex_ball x₀ r).segment_subset (Metric.mem_ball_self hr) (hsub hx)
  · simpa [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      mass_cone_le_of_subset_ball x₀ hsub

/-- **Small-ball filling of augmented-zero `0`-currents.** Every `0`-current `T` of locally finite
mass whose support is a compact subset of `Metric.ball x₀ r ⊆ Ω` and whose augmentation vanishes at
every constant `0`-form bounds a normal `1`-current `Q` (namely `cone x₀ T`) with compact support
in `Metric.ball x₀ r` and `mass Q ≤ ENNReal.ofReal r * mass T`. -/
theorem exists_isNormal_comp_extDerivCLM_finZero_eq_of_subset_ball {x₀ : E} {r : ℝ}
    (hballΩ : Metric.ball x₀ r ⊆ Ω)
    {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V}
    (hT : HasLocallyFiniteMass T) (hc : IsCompact (dsupport T))
    (hsub : dsupport T ⊆ Metric.ball x₀ r) (haug : ∀ c, augmentation T c = 0) :
    ∃ Q : 𝓓(Ω, E [⋀^Fin 1]→L[ℝ] F) →L[ℝ] V,
      IsNormal Q ∧ IsCompact (dsupport Q) ∧ dsupport Q ⊆ Metric.ball x₀ r ∧
        Q ∘L TestFunction.extDerivCLM = T ∧ mass Q ≤ ENNReal.ofReal r * mass T := by
  refine ⟨cone x₀ T, (isLocallyNormal_finZero_iff.2 hT).isNormal_cone x₀,
    isCompact_dsupport_cone x₀ T, ?_,
    cone_comp_extDerivCLM_finZero_of_augmentation_eq_zero x₀ hc (hsub.trans hballΩ) haug, ?_⟩
  · rcases le_or_gt r 0 with hr | hr
    · rw [Metric.ball_eq_empty.2 hr] at hsub
      have hT0 : T = 0 :=
        DFunLike.coe_injective ((dsupport_eq_empty_iff T).1 (subset_empty_iff.1 hsub))
      rw [hT0, cone_zero, (dsupport_eq_empty_iff (0 : _ →L[ℝ] V)).2 rfl]
      exact empty_subset _
    · exact (dsupport_cone_subset x₀ T).trans <| iUnion₂_subset fun x hx ↦
        (convex_ball x₀ r).segment_subset (Metric.mem_ball_self hr) (hsub hx)
  · simpa using mass_cone_le_of_subset_ball x₀ hsub

/-- **Mass of the cone over a point current.** For any `x₀, p : E` and `ℓ` on `k`-forms,
`mass (cone x₀ δ_p) ≤ ENNReal.ofReal (dist p x₀ / (k + 1)) * ‖ℓ‖ₑ`. -/
theorem mass_cone_comp_evalCLM_le (x₀ p : E) (ℓ : (E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V) :
    mass (cone x₀ (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L
      (TestFunction.toBoundedContinuousFunctionCLM ℝ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _))) ≤
      ENNReal.ofReal (dist p x₀ / (k + 1)) * ‖ℓ‖ₑ := by
  set δp := ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L
    (TestFunction.toBoundedContinuousFunctionCLM ℝ : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)
  by_cases hp : p ∈ Ω
  · refine mass_le_iff.2 fun ω hω ↦ ?_
    rw [cone_comp_evalCLM_apply x₀ hp ℓ ω, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    calc ‖ℓ (poincareHomotopy x₀ ω p)‖
        ≤ ‖ℓ‖ * ‖poincareHomotopy x₀ ω p‖ := ℓ.le_opNorm _
      _ ≤ ‖ℓ‖ * (1 * ‖p - x₀‖ / (k + 1)) :=
          mul_le_mul_of_nonneg_left (norm_poincareHomotopy_le fun y _ ↦ hω y) (norm_nonneg ℓ)
      _ = dist p x₀ / (k + 1) * ‖ℓ‖ := by rw [dist_eq_norm]; ring
  · have hzero : δp = 0 := by
      ext φ
      simp [δp, φ.zero_on_compl hp]
    simp [hzero]

/-- **Two-point difference filling in a ball.** In contrast to a single nonzero point `0`-current
(`Distribution.not_exists_comp_extDerivCLM_eq_comp_evalCLM`), for any two points
`p, q ∈ Metric.ball x₀ r` in a ball `Metric.ball x₀ r ⊆ Ω`, the augmented-zero difference
`δ_q - δ_p` is filled by a normal `1`-current `Q` (namely `cone p (δ_q - δ_p)`) supported in
`segment ℝ p q ⊆ Metric.ball x₀ r` with `mass Q ≤ ENNReal.ofReal (dist q p) * ‖ℓ‖ₑ` and
`mass Q ≤ 2 * ENNReal.ofReal r * ‖ℓ‖ₑ`. -/
theorem exists_isNormal_comp_extDerivCLM_eq_sub_comp_evalCLM_finZero_of_mem_ball
    {x₀ p q : E} {r : ℝ} (hballΩ : Metric.ball x₀ r ⊆ Ω)
    (hp : p ∈ Metric.ball x₀ r) (hq : q ∈ Metric.ball x₀ r)
    (ℓ : (E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V) :
    ∃ Q : 𝓓(Ω, E [⋀^Fin 1]→L[ℝ] F) →L[ℝ] V,
      IsNormal Q ∧ IsCompact (dsupport Q) ∧ dsupport Q ⊆ segment ℝ p q ∧
        dsupport Q ⊆ Metric.ball x₀ r ∧
        Q ∘L TestFunction.extDerivCLM =
          (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ q ∘L
              TestFunction.toBoundedContinuousFunctionCLM ℝ) -
            (ℓ ∘L BoundedContinuousFunction.evalCLM ℝ p ∘L
              TestFunction.toBoundedContinuousFunctionCLM ℝ) ∧
        mass Q ≤ ENNReal.ofReal (dist q p) * ‖ℓ‖ₑ ∧
        mass Q ≤ 2 * ENNReal.ofReal r * ‖ℓ‖ₑ := by
  set δ : E → 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V := fun z ↦
    ℓ ∘L BoundedContinuousFunction.evalCLM ℝ z ∘L TestFunction.toBoundedContinuousFunctionCLM ℝ
  have hpΩ : p ∈ Ω := hballΩ hp
  have hqΩ : q ∈ Ω := hballΩ hq
  have hsub (z : E) : dsupport (δ z) ⊆ {z} :=
    dsupport_apply_apply_subset (Ω := Ω) (n := ⊤) (x := z) ℓ.toAddMonoidHom
  have hc (z : E) : IsCompact (dsupport (δ z)) :=
    isCompact_singleton.of_isClosed_subset isClosed_dsupport (hsub z)
  have hcone_eq : cone p (δ q - δ p) = cone p (δ q) := by
    rw [cone_sub p (hc q) ((hsub q).trans (singleton_subset_iff.2 hqΩ))
      (hc p) ((hsub p).trans (singleton_subset_iff.2 hpΩ)),
      cone_comp_evalCLM_self hpΩ ℓ, sub_zero]
  have hseg : dsupport (cone p (δ q)) ⊆ segment ℝ p q :=
    (dsupport_cone_subset p (δ q)).trans <| iUnion₂_subset fun z hz ↦ by
      rw [mem_singleton_iff.1 (hsub q hz)]
  have hseg_ball : segment ℝ p q ⊆ Metric.ball x₀ r :=
    (convex_ball x₀ r).segment_subset hp hq
  have hmass1 : mass (cone p (δ q)) ≤ ENNReal.ofReal (dist q p) * ‖ℓ‖ₑ := by
    simpa using mass_cone_comp_evalCLM_le (Ω := Ω) p q ℓ
  have hdist2r : dist q p ≤ 2 * r := by
    calc dist q p ≤ dist q x₀ + dist x₀ p := dist_triangle q x₀ p
      _ = dist q x₀ + dist p x₀ := by rw [dist_comm x₀ p]
      _ ≤ r + r := add_le_add (Metric.mem_ball.1 hq).le (Metric.mem_ball.1 hp).le
      _ = 2 * r := (two_mul r).symm
  have hmass2 : mass (cone p (δ q)) ≤ 2 * ENNReal.ofReal r * ‖ℓ‖ₑ := by
    refine hmass1.trans ?_
    have h2 : ENNReal.ofReal (2 * r) = 2 * ENNReal.ofReal r := by
      rw [ENNReal.ofReal_mul zero_le_two, ENNReal.ofReal_ofNat]
    rw [← h2]
    exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hdist2r) zero_le
  refine ⟨cone p (δ q - δ p), ?_, isCompact_dsupport_cone p _, hcone_eq ▸ hseg,
    (hcone_eq ▸ hseg).trans hseg_ball,
    cone_sub_comp_evalCLM_finZero_comp_extDerivCLM p hpΩ hqΩ ℓ,
    hcone_eq ▸ hmass1, hcone_eq ▸ hmass2⟩
  exact ((isNormal_comp_evalCLM_comp_toBoundedContinuousFunctionCLM ℓ q).sub
    (isNormal_comp_evalCLM_comp_toBoundedContinuousFunctionCLM ℓ p)).cone p

end Filling

end Distribution
