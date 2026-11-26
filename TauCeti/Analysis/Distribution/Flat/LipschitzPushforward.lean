/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.Mass.Normal
import TauCeti.Analysis.Calculus.BumpFunction.SmoothApprox
import TauCeti.Analysis.Distribution.Flat.Pushforward

/-!
# Pushforward of normal currents along Lipschitz maps

Let `Ω` be an open subset of a finite-dimensional real normed space `E`, and let `T` be a real
normal current on `Ω` (a current of finite mass with boundary of finite mass) whose support is a
compact subset of `Ω`. Along a map `f` smooth on `Ω` with values in a finite-dimensional real
normed space `E'`, the pushforward is `f_# T = T ∘ (χ f^*)` for a test function `χ` equal to one
near the support (`TauCeti.Analysis.Distribution.CutoffPushforward`). This file extends it to maps
which are only Lipschitz near the support.

The key estimate is the homotopy estimate `Distribution.norm_map_cutoffPullbackCLM_sub_le`: if `f`
and `g` are smooth on `Ω` with `‖g - f‖ ≤ ε` and `‖Df‖, ‖Dg‖ ≤ L` on the support of a normal
`(k + 1)`-current `T`, then

`|g_# T (ω) - f_# T (ω)| ≤ ε (L ^ (k + 1) M(T) sup ‖dω‖ + L ^ k M(∂T) sup ‖ω‖)`,

with the degree-zero version `Distribution.norm_map_cutoffPullbackCLM_sub_le_finZero`. It comes from
the homotopy decomposition `g_# T - f_# T = R + ∂ S` for the straight-line homotopy
`(1 - t) f + t g` (`ContinuousLinearMap.exists_comp_cutoffPullbackCLM_sub_eq_add_comp_extDerivCLM`),
whose mass bounds need the hypotheses on the support of the cutoff. As the maps are smooth, the
hypotheses on the support of `T` hold up to any `η > 0` on a neighbourhood of it; cutting off
there and letting `η → 0`, they are only needed on the support.

Consequently, if maps `gⱼ` smooth on `Ω` converge uniformly on the support to `f`, with uniformly
bounded derivatives there, then `gⱼ# T (ω)` converges for every test form `ω`, to a limit which
does not depend on the sequence. This limit is the current `Distribution.lipschitzPushforward T f`
(`Distribution.tendsto_lipschitzPushforward`). If `f` is `L`-Lipschitz on a neighbourhood of the
support, such sequences exist with derivatives bounded by `L` on the support
(`LipschitzOnWith.exists_contDiff_dist_lt_norm_fderiv_le`), and

* `Distribution.mass_lipschitzPushforward_le`: `M(f_# T) ≤ L ^ k M(T)`;
* `Distribution.lipschitzPushforward_comp_extDerivCLM`: `∂ (f_# T) = f_# (∂ T)`;
* `Distribution.dsupport_lipschitzPushforward_subset`: `spt (f_# T) ⊆ f (spt T)`;
* `Distribution.isNormal_lipschitzPushforward`: `f_# T` is normal;
* `Distribution.lipschitzPushforward_lipschitzPushforward`: `g_# (f_# T) = (g ∘ f)_# T`.

Along maps smooth on `Ω` it is the smooth pushforward
(`Distribution.lipschitzPushforward_eq_comp_cutoffPullbackCLM`), and it only depends on the values
of the map on the support of `T` (`Distribution.lipschitzPushforward_congr`). It is linear in `T`
(`Distribution.lipschitzPushforward_zero`, `Distribution.lipschitzPushforward_smul` and, for
currents with compact supports near which the map is Lipschitz,
`Distribution.lipschitzPushforward_add`).

Currents here are real valued, as the bounds go through the mass measure. Flat convergence of the
approximating pushforwards and pushforwards of currents without compact support are not treated.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.9 (the homotopy formula and its estimate) and
  §4.1.14 (pushforward along Lipschitz maps by smooth approximation).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the homotopy formula).
-/

public section

noncomputable section

open Set Filter TopologicalSpace TestFunction
open scoped Distributions Topology NNReal ENNReal BoundedContinuousFunction

namespace Distribution

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {Ω' : Opens E'} {k m : ℕ} {f g : E → E'}

section Estimate

variable [FiniteDimensional ℝ E] [CompleteSpace F]

omit [CompleteSpace F] in
/-- Given a cutoff `χ` equal to one near the compact support of `T` in `Ω`, and a function `u`
continuous on `Ω` with `u < η` on the support, there is a cutoff `ψ` equal to `χ` near the support
with `u < η` on the support of `ψ`. -/
private theorem exists_cutoff_forall_mem_tsupport_lt {T : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F) →L[ℝ] ℝ}
    {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {u : E → ℝ} (hu : ContinuousOn u Ω)
    {η : ℝ} (hη : ∀ x ∈ dsupport T, u x < η) :
    ∃ ψ : 𝓓(Ω, ℝ), (∀ᶠ x in 𝓝ˢ (dsupport T), ψ x = 1) ∧
      (χ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T)] ψ ∧ ∀ x ∈ tsupport ψ, u x < η := by
  obtain ⟨hKc, hKΩ⟩ := isCompact_dsupport_and_subset_of_eventually_eq_one hχ
  obtain ⟨ψ, -, hψ, hψu⟩ := TestFunction.exists_cutoff_tsupport_subset (n := ⊤) hKc
    (hu.isOpen_inter_preimage Ω.isOpen isOpen_Iio) (fun x hx ↦ ⟨hKΩ hx, hη x hx⟩)
    inter_subset_left
  exact ⟨ψ, hψ, (hχ.and hψ).mono fun x h ↦ h.1.trans h.2.symm, fun x hx ↦ (hψu hx).2⟩

/-- **The homotopy estimate for pushforwards**: let `T` be a normal `(k + 1)`-current whose
support is a compact subset of `Ω`, and let `f` and `g` be smooth on `Ω`. If `‖g - f‖ ≤ ε` and
`‖Df‖, ‖Dg‖ ≤ L` on the support of `T`, then the pushforwards `T ∘ (χ f^*)` and `T ∘ (χ g^*)`
satisfy

`|g_# T (ω) - f_# T (ω)| ≤ ε (L ^ (k + 1) M(T) sup ‖dω‖ + L ^ k M(∂T) sup ‖ω‖)`. -/
theorem norm_map_cutoffPullbackCLM_sub_le {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) {ε L : ℝ≥0}
    (hε : ∀ x ∈ dsupport T, ‖g x - f x‖ ≤ ε) (hfL : ∀ x ∈ dsupport T, ‖fderiv ℝ f x‖ ≤ L)
    (hgL : ∀ x ∈ dsupport T, ‖fderiv ℝ g x‖ ≤ L) (ω : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F)) :
    ‖T (cutoffPullbackCLM χ g hg ω) - T (cutoffPullbackCLM χ f hf ω)‖ ≤
      ε * (L ^ (k + 1) * (mass T).toReal *
          ‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (k + 1 + 1)]→L[ℝ] F)‖ +
        L ^ k * (mass (T ∘L extDerivCLM)).toReal *
          ‖(ω : E' →ᵇ E' [⋀^Fin (k + 1)]→L[ℝ] F)‖) := by
  -- The difference is `R ω + S (dω)` for the homotopy decomposition
  -- `ContinuousLinearMap.exists_comp_cutoffPullbackCLM_sub_eq_add_comp_extDerivCLM` of the
  -- straight-line homotopy `(1 - t) f + t g`, whose hypotheses are on the support of the cutoff.
  -- It suffices to prove the bound with `ε + η` and `L + η` for every `η > 0`.
  refine ge_of_tendsto (f := fun η : ℝ ↦ (ε + η) * ((L + η) ^ (k + 1) * (mass T).toReal *
      ‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (k + 1 + 1)]→L[ℝ] F)‖ +
    (L + η) ^ k * (mass (T ∘L extDerivCLM)).toReal * ‖(ω : E' →ᵇ E' [⋀^Fin (k + 1)]→L[ℝ] F)‖))
    (tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by fun_prop) 0 _ (by simp)))
    (eventually_nhdsWithin_of_forall (s := Ioi 0) fun η (hη : 0 < η) ↦ ?_)
  -- Near the support of `T`, the hypotheses hold up to `η`; cut off there.
  have hη' : ((η.toNNReal : ℝ≥0) : ℝ) = η := Real.coe_toNNReal _ hη.le
  have hf' := hf.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)
  have hg' := hg.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)
  obtain ⟨ψ, hψ, hχψ, hψη⟩ := exists_cutoff_forall_mem_tsupport_lt hχ
    (u := fun x ↦ max (‖g x - f x‖ - ε) (max (‖fderiv ℝ f x‖ - L) (‖fderiv ℝ g x‖ - L)))
    (ContinuousOn.sup ((hg.continuousOn.sub hf.continuousOn).norm.sub continuousOn_const)
      (ContinuousOn.sup (hf'.norm.sub continuousOn_const) (hg'.norm.sub continuousOn_const)))
    fun x hx ↦ (max_le (sub_nonpos.2 (hε x hx))
      (max_le (sub_nonpos.2 (hfL x hx)) (sub_nonpos.2 (hgL x hx)))).trans_lt hη
  obtain ⟨R, S, -, -, -, -, -, -, heq, hR, hS⟩ :=
    ContinuousLinearMap.exists_comp_cutoffPullbackCLM_sub_eq_add_comp_extDerivCLM (Ω' := Ω')
      (hf := hf) (hg := hg) T hT hψ (A := ε + η.toNNReal) (L := L + η.toNNReal)
      (fun x hx ↦ by have := max_lt_iff.1 (hψη x hx); push_cast [hη']; linarith)
      (fun x hx ↦ by
        have := max_lt_iff.1 (max_lt_iff.1 (hψη x hx)).2; push_cast [hη']; linarith)
      (fun x hx ↦ by
        have := max_lt_iff.1 (max_lt_iff.1 (hψη x hx)).2; push_cast [hη']; linarith)
  have hcut (Φ : E → E') (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω) :
      T (cutoffPullbackCLM χ Φ hΦ ω) = T (cutoffPullbackCLM ψ Φ hΦ ω) :=
    congr($(ContinuousLinearMap.comp_cutoffPullbackCLM_congr (hΦ := hΦ) T hχψ) ω)
  have hX := congr($heq ω)
  simp only [_root_.sub_apply, _root_.add_apply,
    ContinuousLinearMap.comp_apply] at hX
  rw [hcut, hcut, hX]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ ((ε + η.toNNReal) * (L + η.toNNReal) ^ k : ℝ≥0) *
          (mass (T ∘L extDerivCLM)).toReal * ‖(ω : E' →ᵇ E' [⋀^Fin (k + 1)]→L[ℝ] F)‖ +
        ((ε + η.toNNReal) * (L + η.toNNReal) ^ (k + 1) : ℝ≥0) * (mass T).toReal *
          ‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (k + 1 + 1)]→L[ℝ] F)‖ :=
        add_le_add
          (norm_apply_le_mul_toReal_mul_of_mass_le R hT.comp_extDerivCLM.mass_ne_top
            (by simpa using hR) ω)
          (norm_apply_le_mul_toReal_mul_of_mass_le S hT.mass_ne_top (by simpa using hS) _)
    _ = _ := by push_cast [hη']; ring

/-- **The homotopy estimate for pushforwards in degree zero**: let `T` be a `0`-current of finite
mass whose support is a compact subset of `Ω`, and let `f` and `g` be smooth on `Ω`. If
`‖g - f‖ ≤ ε` on the support of `T`, then the pushforwards satisfy
`|g_# T (ω) - f_# T (ω)| ≤ ε M(T) sup ‖dω‖`. No derivative bound is needed. -/
theorem norm_map_cutoffPullbackCLM_sub_le_finZero {T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : mass T ≠ ⊤) {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) {ε : ℝ≥0}
    (hε : ∀ x ∈ dsupport T, ‖g x - f x‖ ≤ ε) (ω : 𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] F)) :
    ‖T (cutoffPullbackCLM χ g hg ω) - T (cutoffPullbackCLM χ f hf ω)‖ ≤
      ε * (mass T).toReal * ‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (0 + 1)]→L[ℝ] F)‖ := by
  -- It suffices to prove the bound with `ε + η` for every `η > 0`.
  refine ge_of_tendsto (f := fun η : ℝ ↦ (ε + η) * (mass T).toReal *
      ‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (0 + 1)]→L[ℝ] F)‖)
    (tendsto_nhdsWithin_of_tendsto_nhds (Continuous.tendsto' (by fun_prop) 0 _ (by simp)))
    (eventually_nhdsWithin_of_forall (s := Ioi 0) fun η (hη : 0 < η) ↦ ?_)
  have hη' : ((η.toNNReal : ℝ≥0) : ℝ) = η := Real.coe_toNNReal _ hη.le
  obtain ⟨ψ, hψ, hχψ, hψη⟩ := exists_cutoff_forall_mem_tsupport_lt hχ
    (u := fun x ↦ ‖g x - f x‖ - ε)
    ((hg.continuousOn.sub hf.continuousOn).norm.sub continuousOn_const)
    fun x hx ↦ (sub_nonpos.2 (hε x hx)).trans_lt hη
  obtain ⟨S, -, -, -, heq, hS⟩ :=
    ContinuousLinearMap.exists_comp_cutoffPullbackCLM_sub_finZero_eq_comp_extDerivCLM
      (Ω' := Ω') (hf := hf) (hg := hg) T (isNormal_finZero_iff.2 hT) hψ (A := ε + η.toNNReal)
      (fun x hx ↦ by have := hψη x hx; push_cast [hη']; linarith)
  have hcut (Φ : E → E') (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω) :
      T (cutoffPullbackCLM χ Φ hΦ ω) = T (cutoffPullbackCLM ψ Φ hΦ ω) :=
    congr($(ContinuousLinearMap.comp_cutoffPullbackCLM_congr (hΦ := hΦ) T hχψ) ω)
  have hX := congr($heq ω)
  simp only [_root_.sub_apply, ContinuousLinearMap.comp_apply] at hX
  rw [hcut, hcut, hX]
  refine (norm_apply_le_mul_toReal_mul_of_mass_le S hT hS _).trans_eq ?_
  push_cast [hη']
  ring

end Estimate

section Pushforward

variable [FiniteDimensional ℝ E] [CompleteSpace F] {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ}

/-- The homotopy estimate in every degree: the difference of two pushforwards of a normal
current is bounded by `ε C`, where `ε` bounds the distance of the maps on the support and `C`
depends only on `T`, `ω` and a common bound for the derivatives on the support. -/
private theorem exists_norm_map_cutoffPullbackCLM_sub_le (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (L : ℝ≥0)
    (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
    ∃ C : ℝ, ∀ (f g : E → E') (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
      (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) (ε : ℝ≥0), (∀ x ∈ dsupport T, ‖g x - f x‖ ≤ ε) →
      (∀ x ∈ dsupport T, ‖fderiv ℝ f x‖ ≤ L) → (∀ x ∈ dsupport T, ‖fderiv ℝ g x‖ ≤ L) →
      ‖T (cutoffPullbackCLM χ g hg ω) - T (cutoffPullbackCLM χ f hf ω)‖ ≤ ε * C := by
  cases k with
  | zero =>
    exact ⟨(mass T).toReal * ‖(extDerivCLM ω : E' →ᵇ E' [⋀^Fin (0 + 1)]→L[ℝ] F)‖,
      fun f g hf hg ε hε _ _ ↦
        (norm_map_cutoffPullbackCLM_sub_le_finZero hT.mass_ne_top hχ hf hg hε ω).trans_eq (by ring)⟩
  | succ k =>
    exact ⟨_, fun f g hf hg ε hε hfL hgL ↦
      norm_map_cutoffPullbackCLM_sub_le hT hχ hf hg hε hfL hgL ω⟩

/-- The homotopy estimate as a modulus of continuity: for every `e > 0` there is `δ > 0` such
that pushforwards along maps `δ`-close on the support, with derivatives bounded by `L` there,
differ by less than `e` on `ω`. -/
private theorem exists_norm_map_cutoffPullbackCLM_sub_lt (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (L : ℝ≥0)
    (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) {e : ℝ} (he : 0 < e) :
    ∃ δ : ℝ≥0, 0 < (δ : ℝ) ∧ ∀ (f g : E → E') (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
      (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω), (∀ x ∈ dsupport T, ‖g x - f x‖ ≤ δ) →
      (∀ x ∈ dsupport T, ‖fderiv ℝ f x‖ ≤ L) → (∀ x ∈ dsupport T, ‖fderiv ℝ g x‖ ≤ L) →
      ‖T (cutoffPullbackCLM χ g hg ω) - T (cutoffPullbackCLM χ f hf ω)‖ < e := by
  obtain ⟨C, hC⟩ := exists_norm_map_cutoffPullbackCLM_sub_le hT hχ L ω
  obtain ⟨δ, hδ, hδC⟩ := exists_pos_mul_lt he C
  exact ⟨⟨δ, hδ.le⟩, hδ, fun f g hf hg hfg hfL hgL ↦
    (hC f g hf hg _ hfg hfL hgL).trans_lt (by rwa [mul_comm])⟩

/-- Pushforwards along two sequences of smooth maps with bounded derivatives, converging
uniformly on the support to the same map, have the same asymptotic values. -/
private theorem tendsto_map_cutoffPullbackCLM_sub (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {g g' : ℕ → E → E'}
    (hg : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) (hg' : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g' j) Ω)
    (hgf : TendstoUniformlyOn g f atTop (dsupport T))
    (hg'f : TendstoUniformlyOn g' f atTop (dsupport T)) {L : ℝ≥0}
    (hgL : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L)
    (hg'L : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g' j) x‖ ≤ L)
    (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
    Tendsto (fun j ↦ T (cutoffPullbackCLM χ (g j) (hg j) ω) -
      T (cutoffPullbackCLM χ (g' j) (hg' j) ω)) atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.2 fun e he ↦ ?_
  obtain ⟨δ, hδ, hδe⟩ := exists_norm_map_cutoffPullbackCLM_sub_lt hT hχ L ω he
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 (hgf.sub hg'f) _ hδ)
  refine ⟨N, fun j hj ↦ ?_⟩
  rw [dist_zero_right]
  have hgg' (x : E) (hx : x ∈ dsupport T) : ‖g j x - g' j x‖ ≤ δ := by
    simpa [dist_eq_norm, norm_sub_rev] using (hN j hj x hx).le
  exact hδe (g' j) (g j) (hg' j) (hg j) hgg' (hg'L j) (hgL j)

/-- Pushforwards along a sequence of smooth maps with bounded derivatives, converging uniformly on
the support, form a Cauchy sequence on each test form. -/
private theorem cauchySeq_map_cutoffPullbackCLM (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {g : ℕ → E → E'}
    (hg : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) (hgf : TendstoUniformlyOn g f atTop (dsupport T))
    {L : ℝ≥0} (hgL : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L)
    (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
    CauchySeq fun j ↦ T (cutoffPullbackCLM χ (g j) (hg j) ω) := by
  refine Metric.cauchySeq_iff'.2 fun e he ↦ ?_
  obtain ⟨δ, hδ, hδe⟩ := exists_norm_map_cutoffPullbackCLM_sub_lt hT hχ L ω he
  obtain ⟨N, hN⟩ := eventually_atTop.1
    (Metric.tendstoUniformlyOn_iff.1 hgf _ (half_pos hδ))
  refine ⟨N, fun n hn ↦ ?_⟩
  have hnN : ∀ x ∈ dsupport T, ‖g n x - g N x‖ ≤ δ := by
    intro x hx
    rw [← dist_eq_norm]
    linarith [dist_triangle_left (g n x) (g N x) (f x), hN n hn x hx, hN N le_rfl x hx]
  rw [dist_eq_norm]
  exact hδe (g N) (g n) (hg N) (hg n) hnN (hgL N) (hgL n)

omit [FiniteDimensional ℝ E] [CompleteSpace F] in
/-- `T` is normal with compact support in `Ω`, and `f` is the uniform limit on the support of maps
smooth on `Ω` whose derivatives are uniformly bounded on the support. -/
private def IsApproximable (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) (f : E → E') : Prop :=
  IsNormal T ∧ (∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) ∧
    ∃ g : ℕ → E → E', (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) ∧
      TendstoUniformlyOn g f atTop (dsupport T) ∧
      ∃ L : ℝ≥0, ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L

/-- Given one sequence of smooth approximations of `f` on the support of `T`, there is a single
current which is the weak limit of the pushforwards along every such sequence. -/
private theorem IsApproximable.exists_forall_tendsto (h : IsApproximable T f) :
    ∃ S : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ, ∀ χ : 𝓓(Ω, ℝ),
      (∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) → ∀ (g : ℕ → E → E')
      (hg : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω), TendstoUniformlyOn g f atTop (dsupport T) →
      ∀ L : ℝ≥0, (∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L) → ∀ ω,
      Tendsto (fun j ↦ T (cutoffPullbackCLM χ (g j) (hg j) ω)) atTop (𝓝 (S ω)) := by
  obtain ⟨hT, ⟨χ₀, hχ₀⟩, g₀, hg₀, hg₀f, L₀, hg₀L⟩ := h
  have hTf := hasLocallyFiniteMass_of_mass_ne_top T hT.mass_ne_top
  obtain ⟨S, -, hS⟩ := exists_tendsto_of_mass_le
    (fun j ↦ T ∘L (cutoffPullbackCLM χ₀ (g₀ j) (hg₀ j) : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _))
    (C := L₀ ^ k * mass T) (ENNReal.mul_ne_top (by simp) hT.mass_ne_top)
    (fun j ↦ mass_comp_cutoffPullbackCLM_le_of_forall_mem_dsupport hTf
      (fun x hx ↦ by simp [hχ₀.self_of_nhdsSet x hx]) (hg₀L j))
    (cauchySeq_map_cutoffPullbackCLM hT hχ₀ hg₀ hg₀f hg₀L)
  refine ⟨S, fun χ hχ g hg hgf L hgL ω ↦ ?_⟩
  -- Change the cutoff to `χ₀`, then compare with the sequence `g₀`.
  have hχχ₀ : (χ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T)] χ₀ :=
    (hχ.and hχ₀).mono fun x h ↦ h.1.trans h.2.symm
  have hcut (j : ℕ) : T (cutoffPullbackCLM χ (g j) (hg j) ω) =
      T (cutoffPullbackCLM χ₀ (g j) (hg j) ω) :=
    congr($(ContinuousLinearMap.comp_cutoffPullbackCLM_congr (hΦ := hg j) T hχχ₀) ω)
  simp_rw [hcut]
  have hdiff := tendsto_map_cutoffPullbackCLM_sub hT hχ₀ hg hg₀ hgf hg₀f (L := max L L₀)
    (fun j x hx ↦ (hgL j x hx).trans (le_max_left _ _))
    (fun j x hx ↦ (hg₀L j x hx).trans (le_max_right _ _)) ω
  simpa using hdiff.add (hS ω)

open Classical in
/-- The **pushforward `f_# T` of a normal current `T` along a Lipschitz map `f`**.

Let `T` be a normal current whose support is a compact subset of `Ω`. If `f` is the uniform limit
on the support of `T` of maps `gⱼ`, smooth on `Ω`, whose derivatives are uniformly bounded on the
support, then `f_# T` is the limit on each test form of the smooth pushforwards
`gⱼ# T = T ∘ (χ gⱼ^*)`, for any test function `χ` equal to one near the support
(`Distribution.tendsto_lipschitzPushforward`); the limit does not depend on the sequence. Such
sequences exist when `f` is Lipschitz on a neighbourhood of the support, and `f_# T` is the smooth
pushforward when `f` is smooth on `Ω`
(`Distribution.lipschitzPushforward_eq_comp_cutoffPullbackCLM`). If `T` is not normal with compact
support in `Ω`, or `f` has no such approximations, it is `0`
(`Distribution.lipschitzPushforward_of_not_isNormal`,
`Distribution.lipschitzPushforward_of_not_isCompact_and_subset` and
`Distribution.lipschitzPushforward_of_not_exists`). -/
def lipschitzPushforward (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) (f : E → E') :
    𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ :=
  if h : IsApproximable T f then Classical.choose h.exists_forall_tendsto else 0

/-- **The Lipschitz pushforward is the limit of smooth pushforwards**: if smooth maps `gⱼ` converge
to `f` uniformly on the support of a normal current `T`, with uniformly bounded derivatives there,
then `gⱼ# T (ω) → f_# T (ω)` for every test form `ω`, where `gⱼ# T = T ∘ (χ gⱼ^*)` for any test
function `χ` equal to one near the support. -/
theorem tendsto_lipschitzPushforward (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {g : ℕ → E → E'}
    (hg : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) (hgf : TendstoUniformlyOn g f atTop (dsupport T))
    {L : ℝ≥0} (hgL : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L)
    (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
    Tendsto (fun j ↦ T (cutoffPullbackCLM χ (g j) (hg j) ω)) atTop
      (𝓝 (lipschitzPushforward T f ω)) := by
  have h : IsApproximable T f := ⟨hT, ⟨χ, hχ⟩, g, hg, hgf, L, hgL⟩
  rw [lipschitzPushforward, dite_eq_left h]
  exact Classical.choose_spec h.exists_forall_tendsto χ hχ g hg hgf L hgL ω

/-- The pushforward is zero when `f` is not the uniform limit on the support of `T` of maps smooth
on `Ω` whose derivatives are uniformly bounded on the support. -/
theorem lipschitzPushforward_of_not_exists
    (h : ¬∃ g : ℕ → E → E', (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) ∧
      TendstoUniformlyOn g f atTop (dsupport T) ∧
      ∃ L : ℝ≥0, ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L) :
    (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) = 0 := by
  rw [lipschitzPushforward, dite_eq_right fun hf ↦ h hf.2.2]

/-- The pushforward of a current which is not normal is zero. -/
theorem lipschitzPushforward_of_not_isNormal (hT : ¬IsNormal T) :
    (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) = 0 := by
  rw [lipschitzPushforward, dite_eq_right fun hf ↦ hT hf.1]

/-- The pushforward is zero unless `dsupport T` is a compact subset of `Ω`. -/
theorem lipschitzPushforward_of_not_isCompact_and_subset
    (h : ¬(IsCompact (dsupport T) ∧ dsupport T ⊆ Ω)) :
    (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) = 0 := by
  rw [lipschitzPushforward, dite_eq_right fun ⟨_, ⟨_, hχ⟩, _⟩ ↦
    h (isCompact_dsupport_and_subset_of_eventually_eq_one hχ)]

/-- **Agreement with the smooth pushforward**: along a map smooth on `Ω`, the pushforward of a
normal current with compact support in `Ω` is `T ∘ (χ f^*)`, for any `χ` equal to one near the
support. -/
theorem lipschitzPushforward_eq_comp_cutoffPullbackCLM (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) :
    (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) =
      T ∘L cutoffPullbackCLM χ f hf := by
  obtain ⟨hKc, hKΩ⟩ := isCompact_dsupport_and_subset_of_eventually_eq_one hχ
  obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn
    ((hf.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).mono hKΩ)
  have hconst : TendstoUniformlyOn (fun _ : ℕ ↦ f) f atTop (dsupport T) :=
    Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ Eventually.of_forall fun _ x _ ↦ by
      simpa using hε
  ext ω
  exact tendsto_nhds_unique (tendsto_lipschitzPushforward hT hχ (fun _ ↦ hf) hconst
    (L := C.toNNReal) (fun _ x hx ↦ (hC x hx).trans (Real.le_coe_toNNReal C)) ω)
    tendsto_const_nhds

/-- **Locality**: the pushforward of `T` only depends on the values of the map on the support of
`T`. -/
theorem lipschitzPushforward_congr {f' : E → E'} (h : EqOn f f' (dsupport T)) :
    (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) =
      lipschitzPushforward T f' := by
  have key {f₁ f₂ : E → E'} (h₁₂ : EqOn f₁ f₂ (dsupport T)) (hT : IsNormal T) {χ : 𝓓(Ω, ℝ)}
      (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {g : ℕ → E → E'}
      (hg : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) (hgf : TendstoUniformlyOn g f₁ atTop (dsupport T))
      {L : ℝ≥0} (hgL : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L) :
      (lipschitzPushforward T f₁ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) =
        lipschitzPushforward T f₂ := by
    ext ω
    exact tendsto_nhds_unique (tendsto_lipschitzPushforward hT hχ hg hgf hgL ω)
      (tendsto_lipschitzPushforward hT hχ hg (hgf.congr_right h₁₂) hgL ω)
  by_cases hf : IsApproximable T f
  · obtain ⟨hT, ⟨χ, hχ⟩, g, hg, hgf, L, hgL⟩ := hf
    exact key h hT hχ hg hgf hgL
  by_cases hf' : IsApproximable T f'
  · obtain ⟨hT, ⟨χ, hχ⟩, g, hg, hgf, L, hgL⟩ := hf'
    exact (key h.symm hT hχ hg hgf hgL).symm
  rw [lipschitzPushforward, lipschitzPushforward, dite_eq_right hf, dite_eq_right hf']

/-- The pushforward of the zero current is zero. -/
@[simp]
theorem lipschitzPushforward_zero :
    (lipschitzPushforward (0 : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) f :
      𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) = 0 := by
  by_cases h : IsApproximable (0 : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) f
  · obtain ⟨hT, ⟨χ, hχ⟩, g, hg, hgf, L, hgL⟩ := h
    ext ω
    exact tendsto_nhds_unique (tendsto_lipschitzPushforward hT hχ hg hgf hgL ω)
      (by simp)
  · rw [lipschitzPushforward, dite_eq_right h]

/-- The pushforward commutes with scalar multiplication. -/
theorem lipschitzPushforward_smul (c : ℝ) :
    (lipschitzPushforward (c • T) f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) =
      c • lipschitzPushforward T f := by
  -- Approximations of `f` on the support of `T` also serve `c • T`, whose support is smaller.
  have key (c : ℝ) {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ} (h : IsApproximable T f) :
      IsApproximable (c • T) f ∧ (lipschitzPushforward (c • T) f :
        𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) = c • lipschitzPushforward T f := by
    obtain ⟨hT, ⟨χ, hχ⟩, g, hg, hgf, L, hgL⟩ := h
    have hsub : dsupport (c • T) ⊆ dsupport T := dsupport_smul_subset c ⇑T
    have hχ' := hχ.filter_mono (nhdsSet_mono hsub)
    have hgL' (j : ℕ) (x : E) (hx : x ∈ dsupport (c • T)) := hgL j x (hsub hx)
    refine ⟨⟨hT.smul c, ⟨χ, hχ'⟩, g, hg, hgf.mono hsub, L, hgL'⟩, ?_⟩
    ext ω
    exact tendsto_nhds_unique (tendsto_lipschitzPushforward (hT.smul c) hχ' hg (hgf.mono hsub)
      hgL' ω) (by simpa using (tendsto_lipschitzPushforward hT hχ hg hgf hgL ω).const_smul c)
  by_cases h : IsApproximable T f
  · exact (key c h).2
  by_cases hc : c = 0
  · subst hc
    simp
  -- Otherwise neither `T` nor `c • T` has approximations, and both sides are zero.
  have h' : ¬ IsApproximable (c • T) f := fun h' ↦ h (by
    simpa only [inv_smul_smul₀ hc] using (key c⁻¹ h').1)
  rw [lipschitzPushforward, lipschitzPushforward, dite_eq_right h, dite_eq_right h', smul_zero]

variable [FiniteDimensional ℝ E'] {U : Set E} {L : ℝ≥0}

/-- The pushforward is additive, for normal currents with compact supports in `Ω` and a map
Lipschitz on a neighbourhood of both supports. -/
theorem lipschitzPushforward_add {S : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ} (hT : IsNormal T)
    (hS : IsNormal S) (hTc : IsCompact (dsupport T)) (hSc : IsCompact (dsupport S))
    (hTΩ : dsupport T ⊆ Ω) (hSΩ : dsupport S ⊆ Ω) (hf : LipschitzOnWith L f U)
    (hTU : U ∈ 𝓝ˢ (dsupport T)) (hSU : U ∈ 𝓝ˢ (dsupport S)) :
    (lipschitzPushforward (T + S) f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) =
      lipschitzPushforward T f + lipschitzPushforward S f := by
  -- One approximating sequence and one cutoff serve `T`, `S` and `T + S`.
  obtain ⟨g, hg, hgf, hgL⟩ := hf.exists_seq_contDiff_tendstoUniformlyOn (hTc.union hSc)
    (by rw [nhdsSet_union]; exact mem_sup.2 ⟨hTU, hSU⟩)
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) (hTc.union hSc)
    (union_subset hTΩ hSΩ)
  have h {R : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ} (hR : IsNormal R)
      (hRTS : dsupport R ⊆ dsupport T ∪ dsupport S) (ω : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F)) :
      Tendsto (fun j ↦ R (cutoffPullbackCLM χ (g j) (hg j).contDiffOn ω)) atTop
        (𝓝 (lipschitzPushforward R f ω)) :=
    tendsto_lipschitzPushforward hR (hχ.filter_mono (nhdsSet_mono hRTS)) _ (hgf.mono hRTS)
      (fun j x hx ↦ hgL j x (hRTS hx)) ω
  ext ω
  exact tendsto_nhds_unique (h (hT.add hS) (dsupport_add_subset ⇑T ⇑S) ω)
    (by simpa using (h hT subset_union_left ω).add (h hS subset_union_right ω))

omit [CompleteSpace F] in
/-- Smooth approximations of a map which is Lipschitz near the support, and a cutoff. -/
private theorem exists_cutoff_seq_contDiff (hKc : IsCompact (dsupport T))
    (hKΩ : dsupport T ⊆ Ω) (hf : LipschitzOnWith L f U)
    (hU : U ∈ 𝓝ˢ (dsupport T)) :
    ∃ χ : 𝓓(Ω, ℝ), (∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) ∧ ∃ g : ℕ → E → E',
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (g j) Ω) ∧ TendstoUniformlyOn g f atTop (dsupport T) ∧
        ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (g j) x‖ ≤ L := by
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hKc hKΩ
  obtain ⟨g, hg, hgf, hgL⟩ := hf.exists_seq_contDiff_tendstoUniformlyOn hKc hU
  exact ⟨χ, hχ, g, fun j ↦ (hg j).contDiffOn, hgf, hgL⟩

/-- **The mass of a Lipschitz pushforward**: if `f` is `L`-Lipschitz on a neighbourhood of the
support of a normal current `T` with compact support in `Ω`, then `M(f_# T) ≤ L ^ k M(T)`. -/
theorem mass_lipschitzPushforward_le (hT : IsNormal T) (hKc : IsCompact (dsupport T))
    (hKΩ : dsupport T ⊆ Ω) (hf : LipschitzOnWith L f U) (hU : U ∈ 𝓝ˢ (dsupport T)) :
    mass (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) ≤ L ^ k * mass T := by
  obtain ⟨χ, hχ, g, hg, hgf, hgL⟩ := exists_cutoff_seq_contDiff hKc hKΩ hf hU
  have hTf := hasLocallyFiniteMass_of_mass_ne_top T hT.mass_ne_top
  exact (mass_le_liminf (fs := fun j ↦ ⇑(T ∘L (cutoffPullbackCLM χ (g j) (hg j) :
      𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)))
    (tendsto_lipschitzPushforward hT hχ hg hgf hgL)).trans
    (liminf_le_of_frequently_le' (Frequently.of_forall fun j ↦
      mass_comp_cutoffPullbackCLM_le_of_forall_mem_dsupport hTf
        (fun x hx ↦ by simp [hχ.self_of_nhdsSet x hx]) (hgL j)))

/-- **The pushforward commutes with the boundary**: `∂ (f_# T) = f_# (∂ T)` for a normal
`(k + 1)`-current `T` with compact support in `Ω` and a map `f` Lipschitz on a neighbourhood of
the support. -/
theorem lipschitzPushforward_comp_extDerivCLM {T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ}
    (hT : IsNormal T) (hKc : IsCompact (dsupport T)) (hKΩ : dsupport T ⊆ Ω)
    (hf : LipschitzOnWith L f U) (hU : U ∈ 𝓝ˢ (dsupport T)) :
    (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] ℝ) ∘L extDerivCLM =
      lipschitzPushforward (T ∘L extDerivCLM) f := by
  obtain ⟨χ, hχ, g, hg, hgf, hgL⟩ := exists_cutoff_seq_contDiff hKc hKΩ hf hU
  have hsub : dsupport (T ∘L extDerivCLM) ⊆ dsupport T := dsupport_comp_extDerivCLM_subset T
  ext ω
  refine tendsto_nhds_unique (tendsto_lipschitzPushforward hT hχ hg hgf hgL (extDerivCLM ω)) ?_
  have h := tendsto_lipschitzPushforward hT.comp_extDerivCLM
    (hχ.filter_mono (nhdsSet_mono hsub)) hg (hgf.mono hsub) (fun j x hx ↦ hgL j x (hsub hx)) ω
  refine h.congr fun j ↦ ?_
  exact (congr($(ContinuousLinearMap.comp_cutoffPullbackCLM_comp_extDerivCLM (hΦ := hg j) T hχ)
    ω)).symm

/-- **The support of a Lipschitz pushforward** lies in the image of the support:
`spt (f_# T) ⊆ f (spt T)`. -/
theorem dsupport_lipschitzPushforward_subset (hT : IsNormal T) (hKc : IsCompact (dsupport T))
    (hKΩ : dsupport T ⊆ Ω) (hf : LipschitzOnWith L f U) (hU : U ∈ 𝓝ˢ (dsupport T)) :
    dsupport (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) ⊆
      f '' dsupport T := by
  obtain ⟨χ, hχ, g, hg, hgf, hgL⟩ := exists_cutoff_seq_contDiff hKc hKΩ hf hU
  have hfK : IsCompact (f '' dsupport T) :=
    hKc.image_of_continuousOn (hf.continuousOn.mono (subset_of_mem_nhdsSet hU))
  -- A test form supported off the compact image is eventually supported off every `gⱼ (spt T)`.
  have hvan : IsVanishingOn (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ)
      (f '' dsupport T)ᶜ := by
    intro ω hω
    obtain ⟨δ, hδ, hδω⟩ := hfK.exists_thickening_subset_open (isClosed_tsupport ω).isOpen_compl
      fun y hy hyω ↦ hω hyω hy
    have hzero : ∀ᶠ j in atTop, T (cutoffPullbackCLM χ (g j) (hg j) ω) = 0 := by
      filter_upwards [Metric.tendstoUniformlyOn_iff.1 hgf δ hδ] with j hj
      refine map_eq_zero_of_disjoint_dsupport T (disjoint_left.2 fun x hx hxT ↦ ?_)
      have hgx : g j x ∈ Metric.thickening δ (f '' dsupport T) :=
        Metric.mem_thickening_iff.2 ⟨f x, mem_image_of_mem f hxT, by rw [dist_comm]; exact hj x hxT⟩
      exact hδω hgx (tsupport_cutoffPullbackCLM_subset ω hx).2
    exact tendsto_nhds_unique (tendsto_lipschitzPushforward hT hχ hg hgf hgL ω)
      (tendsto_const_nhds.congr' (hzero.mono fun _ h ↦ h.symm))
  have h := (hvan.disjoint_dsupport hfK.isClosed.isOpen_compl).subset_compl_left
  rwa [compl_compl] at h

/-- **Lipschitz pushforwards of normal currents are normal**, when the map is Lipschitz on a
neighbourhood of the compact support. -/
theorem isNormal_lipschitzPushforward (hT : IsNormal T) (hKc : IsCompact (dsupport T))
    (hKΩ : dsupport T ⊆ Ω) (hf : LipschitzOnWith L f U) (hU : U ∈ 𝓝ˢ (dsupport T)) :
    IsNormal (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) := by
  have hfin {j : ℕ} {S : 𝓓(Ω, E [⋀^Fin j]→L[ℝ] F) →L[ℝ] ℝ} (hS : IsNormal S)
      (hSc : IsCompact (dsupport S)) (hSΩ : dsupport S ⊆ Ω) (hSU : U ∈ 𝓝ˢ (dsupport S)) :
      mass (lipschitzPushforward S f : 𝓓(Ω', E' [⋀^Fin j]→L[ℝ] F) →L[ℝ] ℝ) ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.mul_ne_top (by simp) hS.mass_ne_top)
      (mass_lipschitzPushforward_le hS hSc hSΩ hf hSU)
  cases k with
  | zero => exact isNormal_finZero_iff.2 (hfin hT hKc hKΩ hU)
  | succ k =>
    have hsub : dsupport (T ∘L extDerivCLM) ⊆ dsupport T := dsupport_comp_extDerivCLM_subset T
    refine isNormal_succ_iff.2 ⟨hfin hT hKc hKΩ hU, ?_⟩
    rw [lipschitzPushforward_comp_extDerivCLM hT hKc hKΩ hf hU]
    exact hfin hT.comp_extDerivCLM (hKc.of_isClosed_subset isClosed_dsupport hsub)
      (hsub.trans hKΩ) (nhdsSet_mono hsub hU)

omit [CompleteSpace F] in
/-- Smooth approximations of a map which is Lipschitz near the support and sends it into the
interior of `K'`, which all send the support into `K'`, and a cutoff. -/
private theorem exists_cutoff_seq_contDiff_mapsTo (hKc : IsCompact (dsupport T))
    (hKΩ : dsupport T ⊆ Ω) (hf : LipschitzOnWith L f U) (hU : U ∈ 𝓝ˢ (dsupport T)) {K' : Set E'}
    (hfK' : f '' dsupport T ⊆ interior K') :
    ∃ χ : 𝓓(Ω, ℝ), (∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) ∧ ∃ fs : ℕ → E → E',
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fs j) Ω) ∧ TendstoUniformlyOn fs f atTop (dsupport T) ∧
        (∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (fs j) x‖ ≤ L) ∧ ∀ j, ∀ x ∈ dsupport T, fs j x ∈ K' := by
  obtain ⟨χ, hχ, fs, hfs, hfsf, hfsL⟩ := exists_cutoff_seq_contDiff hKc hKΩ hf hU
  -- Eventually the approximations send the support into `K'`; drop the first ones.
  obtain ⟨δ, hδ, hδK'⟩ := (hKc.image_of_continuousOn (hf.continuousOn.mono
    (subset_of_mem_nhdsSet hU))).exists_thickening_subset_open isOpen_interior hfK'
  obtain ⟨N, hN⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hfsf δ hδ)
  refine ⟨χ, hχ, fun j ↦ fs (j + N), fun j ↦ hfs _, Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦
    (tendsto_add_atTop_nat N).eventually (Metric.tendstoUniformlyOn_iff.1 hfsf ε hε),
    fun j ↦ hfsL _, fun j x hx ↦ interior_subset (hδK' (Metric.mem_thickening_iff.2
      ⟨f x, mem_image_of_mem f hx, by rw [dist_comm]; exact hN _ (Nat.le_add_left N j) x hx⟩))⟩

omit [FiniteDimensional ℝ E'] in
/-- If `fⱼ → f` on the support of `T` and `gᵢ → g` on a set `K'` containing every `fⱼ (spt T)`,
with bounded derivatives, and the diagonal composites `gⱼ ∘ fⱼ` converge to `g ∘ f` on the support,
then `gᵢ# (f_# T) → (g ∘ f)_# T` on each test form. The homotopy estimate makes the convergence of
`(gᵢ ∘ fⱼ)# T` to `gᵢ# (f_# T)` uniform in `i`. -/
private theorem tendsto_lipschitzPushforward_comp {E'' : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] {Ω'' : Opens E''} {g : E' → E''} {L' : ℝ≥0} (hT : IsNormal T)
    {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) {fs : ℕ → E → E'}
    (hfs : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (fs j) Ω) (hfsf : TendstoUniformlyOn fs f atTop (dsupport T))
    (hfsL : ∀ j, ∀ x ∈ dsupport T, ‖fderiv ℝ (fs j) x‖ ≤ L) {K' : Set E'}
    (hfsK' : ∀ j, ∀ x ∈ dsupport T, fs j x ∈ K') {χ' : 𝓓(Ω', ℝ)} (hχ' : ∀ᶠ y in 𝓝ˢ K', χ' y = 1)
    {gs : ℕ → E' → E''} (hgs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (gs i))
    (hgsg : TendstoUniformlyOn gs g atTop K') (hgsL : ∀ i, ∀ y ∈ K', ‖fderiv ℝ (gs i) y‖ ≤ L')
    (hcf : TendstoUniformlyOn (fun j ↦ gs j ∘ fs j) (g ∘ f) atTop (dsupport T))
    (ω : 𝓓(Ω'', E'' [⋀^Fin k]→L[ℝ] F)) :
    Tendsto (fun i ↦ lipschitzPushforward T f (cutoffPullbackCLM χ' (gs i) (hgs i).contDiffOn ω))
      atTop (𝓝 (lipschitzPushforward T (g ∘ f) ω)) := by
  -- The composites `gᵢ ∘ fⱼ` are smooth, with derivatives bounded by `L' L` on the support.
  have hc (i j : ℕ) : ContDiffOn ℝ (⊤ : ℕ∞) (gs i ∘ fs j) Ω := (hgs i).comp_contDiffOn (hfs j)
  have hcL (i j : ℕ) (x : E) (hx : x ∈ dsupport T) :
      ‖fderiv ℝ (gs i ∘ fs j) x‖ ≤ (L' * L : ℝ≥0) := by
    have hxΩ : x ∈ Ω := (isCompact_dsupport_and_subset_of_eventually_eq_one hχ).2 hx
    have hfd : DifferentiableAt ℝ (fs j) x :=
      ((hfs j).contDiffAt (Ω.isOpen.mem_nhds hxΩ)).differentiableAt (by simp)
    rw [fderiv_comp x ((hgs i).differentiable (by simp) _) hfd, NNReal.coe_mul]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul (hgsL i _ (hfsK' j x hx)) (hfsL _ x hx) (norm_nonneg _) L'.coe_nonneg)
  -- `gᵢ# (f_# T) (ω)` is the limit of `(gᵢ ∘ fⱼ)# T (ω)` in `j`.
  have hb (i : ℕ) : Tendsto (fun j ↦ T (cutoffPullbackCLM χ (gs i ∘ fs j) (hc i j) ω)) atTop
      (𝓝 (lipschitzPushforward T f (cutoffPullbackCLM χ' (gs i) (hgs i).contDiffOn ω))) := by
    refine (tendsto_lipschitzPushforward hT hχ hfs hfsf hfsL
      (cutoffPullbackCLM χ' (gs i) (hgs i).contDiffOn ω)).congr fun j ↦ ?_
    exact congr($(ContinuousLinearMap.comp_cutoffPullbackCLM_comp_cutoffPullbackCLM T
      (hΦ := hfs j) (hΨΦ := hc i j) (hχ'.filter_mono (nhdsSet_mono
        (by rintro _ ⟨x, hx, rfl⟩; exact hfsK' j x hx.2)))) ω)
  refine Metric.tendsto_atTop.2 fun e he ↦ ?_
  obtain ⟨δ, hδ, hδe⟩ := exists_norm_map_cutoffPullbackCLM_sub_lt hT hχ (L' * L) ω (half_pos he)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (Metric.tendstoUniformlyOn_iff.1 hgsg _ (half_pos hδ))
  refine ⟨M, fun i hi ↦ ?_⟩
  have hle : ‖lipschitzPushforward T f (cutoffPullbackCLM χ' (gs i) (hgs i).contDiffOn ω) -
      lipschitzPushforward T (g ∘ f) ω‖ ≤ e / 2 := by
    refine le_of_tendsto ((hb i).sub (tendsto_lipschitzPushforward hT hχ (fun j ↦ hc j j) hcf
      (fun j ↦ hcL j j) ω)).norm (eventually_atTop.2 ⟨M, fun j hj ↦ ?_⟩)
    refine (hδe _ _ (hc j j) (hc i j) (fun x hx ↦ ?_) (hcL j j) (hcL i j)).le
    have hy := hfsK' j x hx
    rw [Function.comp_apply, Function.comp_apply, ← dist_eq_norm]
    linarith [dist_triangle_left (gs i (fs j x)) (gs j (fs j x)) (g (fs j x)), hM i hi _ hy,
      hM j hj _ hy]
  rw [dist_eq_norm]
  linarith

/-- **Functoriality of the Lipschitz pushforward**: `g_# (f_# T) = (g ∘ f)_# T` for a normal
current `T` with compact support in `Ω`, a map `f` Lipschitz on a neighbourhood of the support
mapping it into `Ω'`, and a map `g` Lipschitz on a neighbourhood of the image of the support. -/
theorem lipschitzPushforward_lipschitzPushforward {E'' : Type*} [NormedAddCommGroup E'']
    [NormedSpace ℝ E''] [FiniteDimensional ℝ E''] {Ω'' : Opens E''} {g : E' → E''} {V : Set E'}
    {L' : ℝ≥0} (hT : IsNormal T) (hKc : IsCompact (dsupport T)) (hKΩ : dsupport T ⊆ Ω)
    (hf : LipschitzOnWith L f U) (hU : U ∈ 𝓝ˢ (dsupport T)) (hfΩ' : f '' dsupport T ⊆ Ω')
    (hg : LipschitzOnWith L' g V) (hV : V ∈ 𝓝ˢ (f '' dsupport T)) :
    (lipschitzPushforward (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) g :
        𝓓(Ω'', E'' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) = lipschitzPushforward T (g ∘ f) := by
  -- A compact neighbourhood `K'` of the image of the support, in `Ω'` and inside `V`.
  obtain ⟨K', hK'c, hfK', hK'⟩ := exists_compact_between
    (hKc.image_of_continuousOn (hf.continuousOn.mono (subset_of_mem_nhdsSet hU)))
    (isOpen_interior.inter Ω'.isOpen) (subset_inter (subset_interior_iff_mem_nhdsSet.2 hV) hfΩ')
  have hK'V : K' ⊆ V := fun y hy ↦ interior_subset (hK' hy).1
  have hSK' : dsupport (lipschitzPushforward T f : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ) ⊆ K' :=
    (dsupport_lipschitzPushforward_subset hT hKc hKΩ hf hU).trans (hfK'.trans interior_subset)
  obtain ⟨χ, hχ, fs, hfs, hfsf, hfsL, hfsK'⟩ := exists_cutoff_seq_contDiff_mapsTo hKc hKΩ hf hU hfK'
  obtain ⟨gs, hgs, hgsg, hgsL⟩ := hg.exists_seq_contDiff_tendstoUniformlyOn hK'c
    (mem_of_superset ((isOpen_interior.mem_nhdsSet).2 fun y hy ↦ (hK' hy).1) interior_subset)
  obtain ⟨χ', hχ', -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hK'c fun y hy ↦ (hK' hy).2
  -- The diagonal composites converge to `g ∘ f` on the support.
  have hcf : TendstoUniformlyOn (fun j ↦ gs j ∘ fs j) (g ∘ f) atTop (dsupport T) := by
    refine Metric.tendstoUniformlyOn_iff.2 fun ε hε ↦ ?_
    have hL1 : (0 : ℝ) < L' + 1 := by positivity
    filter_upwards [Metric.tendstoUniformlyOn_iff.1 hgsg (ε / 2) (half_pos hε),
      Metric.tendstoUniformlyOn_iff.1 hfsf (ε / (2 * (L' + 1))) (by positivity)] with j hj hj' x hx
    have h1 : (L' : ℝ) * dist (f x) (fs j x) ≤ ε / 2 :=
      calc (L' : ℝ) * dist (f x) (fs j x) ≤ (L' + 1) * (ε / (2 * (L' + 1))) :=
            mul_le_mul (by linarith) (hj' x hx).le dist_nonneg hL1.le
        _ = ε / 2 := by field_simp
    calc dist ((g ∘ f) x) ((gs j ∘ fs j) x)
        ≤ dist (g (f x)) (g (fs j x)) + dist (g (fs j x)) (gs j (fs j x)) := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt ((hg.dist_le_mul _
          (hK'V (interior_subset (hfK' (mem_image_of_mem f hx)))) _ (hK'V (hfsK' j x hx))).trans h1)
          (hj _ (hfsK' j x hx))
      _ = ε := add_halves ε
  ext ω
  exact tendsto_nhds_unique (tendsto_lipschitzPushforward
    (isNormal_lipschitzPushforward hT hKc hKΩ hf hU) (hχ'.filter_mono (nhdsSet_mono hSK'))
    (fun i ↦ (hgs i).contDiffOn) (hgsg.mono hSK') (fun i y hy ↦ hgsL i y (hSK' hy)) ω)
    (tendsto_lipschitzPushforward_comp hT hχ hfs hfsf hfsL hfsK' hχ' hgs hgsg hgsL hcf ω)

end Pushforward

end Distribution
