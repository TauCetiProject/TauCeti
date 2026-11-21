/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.Flat.Basic
public import TauCeti.Analysis.Distribution.TestFunction.Homotopy
import TauCeti.Topology.Instances.ENNReal

/-!
# Pushforwards of a current along nearby smooth maps

Let `Ω ⊆ E` and `Ω' ⊆ E'` be open subsets of real normed spaces, and let `T` be a `k`-current on
`Ω` together with a test function `χ` on `Ω` such that `|χ| ≤ 1` and `χ` is equal to one near the
support of `T` (so the support of `T` is a compact subset of `Ω`). For maps `Φ₀, Φ₁ : E → E'`
smooth on `Ω`, the pushforwards `Φᵢ# T = T ∘ (χ Φᵢ^*)` of
`TauCeti.Analysis.Distribution.CutoffPushforward` are joined by the straight-line homotopy
`H (x, t) = Φ₀ x + t • (Φ₁ x - Φ₀ x)`. Suppose that `‖Φ₁ - Φ₀‖ ≤ δ` and `‖DΦ₀‖, ‖DΦ₁‖ ≤ L` on the
support of `χ`. The homotopy formula for `H` with the cutoff `χ`
(`ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM`) gives the
**homotopy decomposition**

`Φ₁# T - Φ₀# T = R + ∂ S`, `M(S) ≤ δ L ^ k M(T)`, `M(R) ≤ δ L ^ (k - 1) M(∂ T)`,

where `S = H_# ([[0, 1]] × T)`, `R = H_# ([[0, 1]] × ∂ T)` and `∂ S = S ∘ d`; in degree zero
`R = 0`. Both `R` and `S` are supported in the union of the segments `[Φ₀ x, Φ₁ x]` over the
points `x` of the support of `T`. For a normal current `T` this is a decomposition into normal
currents, so the real normal flat mass (`ContinuousLinearMap.normalFlatMass`) satisfies

`F(Φ₁# T - Φ₀# T) ≤ δ (L ^ k M(T) + L ^ (k - 1) M(∂ T))`.

Consequently, if smooth maps `Φᵢ` converge uniformly to `Φ` on the support of `χ` with a uniform
bound on their derivatives there, then `Φᵢ# T → Φ# T` in flat mass, and therefore on every test
form (`ContinuousLinearMap.tendsto_apply_of_normalFlatMass_sub_tendsto_zero`). These estimates
control pushforwards along smooth approximations of a Lipschitz map.

## Main declarations

* `Distribution.exists_comp_cutoffPullbackCLM_sub_eq_add_comp_extDerivCLM`: the homotopy
  decomposition `Φ₁# T - Φ₀# T = R + ∂ S` with its mass and support bounds, for a
  `(k + 1)`-current `T`.
* `Distribution.exists_comp_cutoffPullbackCLM_sub_eq_comp_extDerivCLM_finZero`: in degree zero,
  `Φ₁# T - Φ₀# T = ∂ S` with `M(S) ≤ δ M(T)`.
* `ContinuousLinearMap.normalFlatMass_comp_cutoffPullbackCLM_sub_le` and
  `ContinuousLinearMap.normalFlatMass_comp_cutoffPullbackCLM_sub_le_finZero`: the flat mass bounds.
* `ContinuousLinearMap.tendsto_normalFlatMass_comp_cutoffPullbackCLM_sub` and
  `ContinuousLinearMap.tendsto_normalFlatMass_comp_cutoffPullbackCLM_sub_finZero`: flat
  convergence of pushforwards along uniformly convergent maps with bounded derivatives.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.9 (the affine homotopy between two maps and the
  mass of the resulting homotopy current).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2 (the homotopy formula for
  the affine homotopy).
-/

public section

noncomputable section

open Set Filter TopologicalSpace TestFunction
open scoped Distributions Topology NNReal ENNReal

namespace Distribution

variable {E E' F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {Ω : Opens E} {Ω' : Opens E'} {k : ℕ} {χ : 𝓓(Ω, ℝ)} {Φ₀ Φ₁ : E → E'}
  {hΦ₀ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₀ Ω} {hΦ₁ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₁ Ω}

section LineHomotopy

/-- The straight-line homotopy `(x, t) ↦ Φ₀ x + t • (Φ₁ x - Φ₀ x)` from `Φ₀` to `Φ₁`. -/
private def lineHomotopy (Φ₀ Φ₁ : E → E') (p : E × ℝ) : E' :=
  AffineMap.lineMap (Φ₀ p.1) (Φ₁ p.1) p.2

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem lineHomotopy_eq :
    lineHomotopy Φ₀ Φ₁ = fun p ↦ Φ₀ p.1 + p.2 • (Φ₁ p.1 - Φ₀ p.1) := by
  funext p
  rw [lineHomotopy, AffineMap.lineMap_apply_module', add_comm]

private theorem contDiffOn_lineHomotopy (hΦ₀ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₀ Ω)
    (hΦ₁ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₁ Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (lineHomotopy Φ₀ Φ₁) Ω.cylinder := by
  rw [lineHomotopy_eq]
  have hfst : MapsTo Prod.fst (Ω.cylinder : Set (E × ℝ)) Ω := fun _ hp ↦ Opens.mem_cylinder.1 hp
  have h₀ := hΦ₀.comp contDiffOn_fst hfst
  have h₁ := hΦ₁.comp contDiffOn_fst hfst
  exact h₀.add (contDiffOn_snd.smul (h₁.sub h₀))

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem lineHomotopy_zero : (fun x ↦ lineHomotopy Φ₀ Φ₁ (x, 0)) = Φ₀ := by
  funext x
  simp [lineHomotopy]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem lineHomotopy_one : (fun x ↦ lineHomotopy Φ₀ Φ₁ (x, 1)) = Φ₁ := by
  funext x
  simp [lineHomotopy]

/-- The derivative of the straight-line homotopy at `(x, t)`, for `x ∈ Ω`. -/
private theorem hasFDerivAt_lineHomotopy (hΦ₀ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₀ Ω)
    (hΦ₁ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₁ Ω) {x : E} (hx : x ∈ Ω) (t : ℝ) :
    HasFDerivAt (lineHomotopy Φ₀ Φ₁)
      ((fderiv ℝ Φ₀ x).comp (.fst ℝ E ℝ) +
        (t • ((fderiv ℝ Φ₁ x).comp (.fst ℝ E ℝ) - (fderiv ℝ Φ₀ x).comp (.fst ℝ E ℝ)) +
          (ContinuousLinearMap.snd ℝ E ℝ).smulRight (Φ₁ x - Φ₀ x))) (x, t) := by
  have hd {Φ : E → E'} (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω) :
      HasFDerivAt (fun p : E × ℝ ↦ Φ p.1) ((fderiv ℝ Φ x).comp (.fst ℝ E ℝ)) (x, t) :=
    ((hΦ.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt.comp (x, t)
      hasFDerivAt_fst
  rw [lineHomotopy_eq]
  exact (hd hΦ₀).add (hasFDerivAt_snd.smul ((hd hΦ₁).sub (hd hΦ₀)))

/-- The time derivative of the straight-line homotopy is `Φ₁ x - Φ₀ x`. -/
private theorem fderiv_lineHomotopy_apply_zero_one (hΦ₀ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₀ Ω)
    (hΦ₁ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₁ Ω) {x : E} (hx : x ∈ Ω) (t : ℝ) :
    fderiv ℝ (lineHomotopy Φ₀ Φ₁) (x, t) (0, 1) = Φ₁ x - Φ₀ x := by
  simp [(hasFDerivAt_lineHomotopy hΦ₀ hΦ₁ hx t).fderiv]

/-- At a time `t ∈ [0, 1]`, the spatial derivative of the straight-line homotopy is the convex
combination `(1 - t) DΦ₀ + t DΦ₁`, so it is bounded by any common bound of `DΦ₀` and `DΦ₁`. -/
private theorem norm_fderiv_lineHomotopy_comp_inl_le (hΦ₀ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₀ Ω)
    (hΦ₁ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₁ Ω) {x : E} (hx : x ∈ Ω) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    {L : ℝ} (hL₀ : ‖fderiv ℝ Φ₀ x‖ ≤ L) (hL₁ : ‖fderiv ℝ Φ₁ x‖ ≤ L) :
    ‖(fderiv ℝ (lineHomotopy Φ₀ Φ₁) (x, t)).comp (.inl ℝ E ℝ)‖ ≤ L := by
  have h : (fderiv ℝ (lineHomotopy Φ₀ Φ₁) (x, t)).comp (.inl ℝ E ℝ) =
      (1 - t) • fderiv ℝ Φ₀ x + t • fderiv ℝ Φ₁ x := by
    ext v
    simp [(hasFDerivAt_lineHomotopy hΦ₀ hΦ₁ hx t).fderiv, sub_smul, smul_sub]
    abel
  rw [h]
  calc ‖(1 - t) • fderiv ℝ Φ₀ x + t • fderiv ℝ Φ₁ x‖
      ≤ (1 - t) * ‖fderiv ℝ Φ₀ x‖ + t * ‖fderiv ℝ Φ₁ x‖ := by
        refine (norm_add_le _ _).trans_eq ?_
        rw [norm_smul, norm_smul, Real.norm_of_nonneg (sub_nonneg.2 ht.2),
          Real.norm_of_nonneg ht.1]
    _ ≤ (1 - t) * L + t * L :=
        add_le_add (mul_le_mul_of_nonneg_left hL₀ (sub_nonneg.2 ht.2))
          (mul_le_mul_of_nonneg_left hL₁ ht.1)
    _ = L := by ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- A point of the straight-line homotopy at a time in `[0, 1]` lies on the segment
`[Φ₀ x, Φ₁ x]`. -/
private theorem lineHomotopy_image_subset (s : Set E) :
    lineHomotopy Φ₀ Φ₁ '' (s ×ˢ Icc (0 : ℝ) 1) ⊆ ⋃ x ∈ s, segment ℝ (Φ₀ x) (Φ₁ x) := by
  rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
  exact mem_biUnion hx (by rw [segment_eq_image_lineMap]; exact ⟨t, ht, rfl⟩)

end LineHomotopy

variable (hΦ₀ hΦ₁) in
/-- The support of a homotopy current along the straight-line homotopy lies in the union of the
segments `[Φ₀ x, Φ₁ x]` over the points of the support of `T`, when `χ` is one near it. -/
private theorem dsupport_comp_cutoffHomotopyPullbackCLM_lineHomotopy_subset {m : ℕ}
    (T : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F) →L[ℝ] V) {U : Set E} (hTU : dsupport T ⊆ U) :
    dsupport (T ∘L (cutoffHomotopyPullbackCLM χ (lineHomotopy Φ₀ Φ₁)
        (contDiffOn_lineHomotopy hΦ₀ hΦ₁) : 𝓓(Ω', E' [⋀^Fin (m + 1)]→L[ℝ] F) →L[ℝ] _)) ⊆
      ⋃ x ∈ U, segment ℝ (Φ₀ x) (Φ₁ x) :=
  (dsupport_comp_cutoffHomotopyPullbackCLM_subset T).trans <|
    (image_mono (prod_mono (inter_subset_right.trans hTU) subset_rfl)).trans
      (lineHomotopy_image_subset U)

variable (hΦ₀ hΦ₁) in
/-- The hypotheses of the mass bound for homotopy currents, for the straight-line homotopy. -/
private theorem mass_comp_cutoffHomotopyPullbackCLM_lineHomotopy_le {m : ℕ}
    (T : 𝓓(Ω, E [⋀^Fin m]→L[ℝ] F) →L[ℝ] V) (hχ₁ : ∀ x, |χ x| ≤ 1) {δ L : ℝ≥0}
    (hδ : ∀ x ∈ tsupport χ, ‖Φ₁ x - Φ₀ x‖ ≤ δ) (hL₀ : ∀ x ∈ tsupport χ, ‖fderiv ℝ Φ₀ x‖ ≤ L)
    (hL₁ : ∀ x ∈ tsupport χ, ‖fderiv ℝ Φ₁ x‖ ≤ L) :
    mass (T ∘L (cutoffHomotopyPullbackCLM χ (lineHomotopy Φ₀ Φ₁)
        (contDiffOn_lineHomotopy hΦ₀ hΦ₁) : 𝓓(Ω', E' [⋀^Fin (m + 1)]→L[ℝ] F) →L[ℝ] _)) ≤
      δ * L ^ m * mass T :=
  mass_comp_cutoffHomotopyPullbackCLM_le T hχ₁
    (fun p hp ↦ by
      rw [fderiv_lineHomotopy_apply_zero_one hΦ₀ hΦ₁ (χ.tsupport_subset hp.1)]
      exact hδ _ hp.1)
    fun p hp ↦ norm_fderiv_lineHomotopy_comp_inl_le hΦ₀ hΦ₁ (χ.tsupport_subset hp.1) hp.2
      (hL₀ _ hp.1) (hL₁ _ hp.1)

/-- **The homotopy decomposition of two pushforwards**: let `T` be a `(k + 1)`-current on `Ω` and
let `χ` be a test function with `|χ| ≤ 1`, equal to one near the support of `T`. If two maps
`Φ₀, Φ₁` smooth on `Ω` satisfy `‖Φ₁ - Φ₀‖ ≤ δ`, `‖DΦ₀‖ ≤ L` and `‖DΦ₁‖ ≤ L` on the support of
`χ`, then `Φ₁# T - Φ₀# T = R + ∂ S` for currents `R`, `S` on `Ω'` with `M(S) ≤ δ L ^ (k + 1) M(T)`,
`M(R) ≤ δ L ^ k M(∂ T)`, both supported in the union of the segments `[Φ₀ x, Φ₁ x]` over the
points `x` of the support of `T`. Here `Φᵢ# T = T ∘ (χ Φᵢ^*)` and `∂ S = S ∘ d`. -/
theorem exists_comp_cutoffPullbackCLM_sub_eq_add_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1)
    (hχ₁ : ∀ x, |χ x| ≤ 1) {δ L : ℝ≥0} (hδ : ∀ x ∈ tsupport χ, ‖Φ₁ x - Φ₀ x‖ ≤ δ)
    (hL₀ : ∀ x ∈ tsupport χ, ‖fderiv ℝ Φ₀ x‖ ≤ L) (hL₁ : ∀ x ∈ tsupport χ, ‖fderiv ℝ Φ₁ x‖ ≤ L) :
    ∃ (R : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] V)
      (S : 𝓓(Ω', E' [⋀^Fin (k + 2)]→L[ℝ] F) →L[ℝ] V),
      T ∘L cutoffPullbackCLM χ Φ₁ hΦ₁ - T ∘L cutoffPullbackCLM χ Φ₀ hΦ₀ =
          R + S ∘L extDerivCLM ∧
        mass S ≤ δ * L ^ (k + 1) * mass T ∧ mass R ≤ δ * L ^ k * mass (T ∘L extDerivCLM) ∧
        dsupport S ⊆ ⋃ x ∈ dsupport T, segment ℝ (Φ₀ x) (Φ₁ x) ∧
        dsupport R ⊆ ⋃ x ∈ dsupport T, segment ℝ (Φ₀ x) (Φ₁ x) := by
  have h := ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM (Ω' := Ω')
    (hH₀ := by rw [lineHomotopy_zero]; exact hΦ₀)
    (hH₁ := by rw [lineHomotopy_one]; exact hΦ₁) (hH := contDiffOn_lineHomotopy hΦ₀ hΦ₁) T hχ
  rw [cutoffPullbackCLM_congr_fun lineHomotopy_zero (hΨ := hΦ₀),
    cutoffPullbackCLM_congr_fun lineHomotopy_one (hΨ := hΦ₁)] at h
  refine ⟨(T ∘L extDerivCLM) ∘L cutoffHomotopyPullbackCLM χ _ (contDiffOn_lineHomotopy hΦ₀ hΦ₁),
    T ∘L cutoffHomotopyPullbackCLM χ _ (contDiffOn_lineHomotopy hΦ₀ hΦ₁), by rw [h]; abel,
    mass_comp_cutoffHomotopyPullbackCLM_lineHomotopy_le hΦ₀ hΦ₁ T hχ₁ hδ hL₀ hL₁,
    mass_comp_cutoffHomotopyPullbackCLM_lineHomotopy_le hΦ₀ hΦ₁ _ hχ₁ hδ hL₀ hL₁,
    dsupport_comp_cutoffHomotopyPullbackCLM_lineHomotopy_subset hΦ₀ hΦ₁ T subset_rfl,
    dsupport_comp_cutoffHomotopyPullbackCLM_lineHomotopy_subset hΦ₀ hΦ₁ _
      (dsupport_comp_extDerivCLM_subset T)⟩

/-- **The homotopy decomposition of two pushforwards in degree zero**: let `T` be a `0`-current
on `Ω` and let `χ` be a test function with `|χ| ≤ 1`, equal to one near the support of `T`. If two
maps `Φ₀, Φ₁` smooth on `Ω` satisfy `‖Φ₁ - Φ₀‖ ≤ δ` on the support of `χ`, then
`Φ₁# T - Φ₀# T = ∂ S` for a `1`-current `S` on `Ω'` with `M(S) ≤ δ M(T)`, supported in the union
of the segments `[Φ₀ x, Φ₁ x]` over the points `x` of the support of `T`. -/
theorem exists_comp_cutoffPullbackCLM_sub_eq_comp_extDerivCLM_finZero
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] V) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1)
    (hχ₁ : ∀ x, |χ x| ≤ 1) {δ : ℝ≥0} (hδ : ∀ x ∈ tsupport χ, ‖Φ₁ x - Φ₀ x‖ ≤ δ) :
    ∃ S : 𝓓(Ω', E' [⋀^Fin 1]→L[ℝ] F) →L[ℝ] V,
      T ∘L cutoffPullbackCLM χ Φ₁ hΦ₁ - T ∘L cutoffPullbackCLM χ Φ₀ hΦ₀ = S ∘L extDerivCLM ∧
        mass S ≤ δ * mass T ∧ dsupport S ⊆ ⋃ x ∈ dsupport T, segment ℝ (Φ₀ x) (Φ₁ x) := by
  have h := ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM_finZero
    (Ω' := Ω') (hH₀ := by rw [lineHomotopy_zero]; exact hΦ₀)
    (hH₁ := by rw [lineHomotopy_one]; exact hΦ₁) (hH := contDiffOn_lineHomotopy hΦ₀ hΦ₁) T hχ
  rw [cutoffPullbackCLM_congr_fun lineHomotopy_zero (hΨ := hΦ₀),
    cutoffPullbackCLM_congr_fun lineHomotopy_one (hΨ := hΦ₁)] at h
  refine ⟨T ∘L cutoffHomotopyPullbackCLM χ _ (contDiffOn_lineHomotopy hΦ₀ hΦ₁), h.symm, ?_,
    dsupport_comp_cutoffHomotopyPullbackCLM_lineHomotopy_subset hΦ₀ hΦ₁ T subset_rfl⟩
  -- In degree zero no derivative bound is needed; the spatial derivative is bounded by
  -- compactness and enters only through its zeroth power.
  obtain ⟨C, hC⟩ := (χ.hasCompactSupport.prod isCompact_Icc).exists_bound_of_continuousOn
    (f := fun p ↦ (fderiv ℝ (lineHomotopy Φ₀ Φ₁) p).comp (.inl ℝ E ℝ))
    ((((contDiffOn_lineHomotopy hΦ₀ hΦ₁).continuousOn_fderiv_of_isOpen Ω.cylinder.isOpen
      (by simp)).clm_comp continuousOn_const).mono
        fun p (hp : p ∈ tsupport χ ×ˢ Icc (0 : ℝ) 1) ↦
          Opens.mem_cylinder.2 (χ.tsupport_subset hp.1))
  refine (mass_comp_cutoffHomotopyPullbackCLM_le (Ω' := Ω') (H := lineHomotopy Φ₀ Φ₁)
    (hH := contDiffOn_lineHomotopy hΦ₀ hΦ₁) T hχ₁ (A := δ) (L := C.toNNReal)
    (fun p hp ↦ by
      rw [fderiv_lineHomotopy_apply_zero_one hΦ₀ hΦ₁ (χ.tsupport_subset hp.1)]
      exact hδ _ hp.1)
    fun p hp ↦ (hC p hp).trans (Real.le_coe_toNNReal C)).trans_eq ?_
  rw [pow_zero, mul_one]

variable (χ) in
/-- The derivative of a map smooth on `Ω` is bounded on the compact set `tsupport χ`. -/
private theorem exists_forall_norm_fderiv_le {Φ : E → E'} (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω) :
    ∃ L : ℝ≥0, ∀ x ∈ tsupport χ, ‖fderiv ℝ Φ x‖ ≤ L := by
  obtain ⟨C, hC⟩ := χ.hasCompactSupport.exists_bound_of_continuousOn
    ((hΦ.continuousOn_fderiv_of_isOpen Ω.isOpen (by simp)).mono χ.tsupport_subset)
  exact ⟨C.toNNReal, fun x hx ↦ (hC x hx).trans (Real.le_coe_toNNReal C)⟩

end Distribution

namespace ContinuousLinearMap

open Distribution

variable {E E' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {Ω : Opens E} {Ω' : Opens E'} {k : ℕ} {χ : 𝓓(Ω, ℝ)} {Φ₀ Φ₁ : E → E'}
  {hΦ₀ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₀ Ω} {hΦ₁ : ContDiffOn ℝ (⊤ : ℕ∞) Φ₁ Ω}

/-- **Flat mass of the difference of two pushforwards**: let `T` be a normal `(k + 1)`-current on
`Ω` and let `χ` be a test function with `|χ| ≤ 1`, equal to one near the support of `T`. If two
maps `Φ₀, Φ₁` smooth on `Ω` satisfy `‖Φ₁ - Φ₀‖ ≤ δ`, `‖DΦ₀‖ ≤ L` and `‖DΦ₁‖ ≤ L` on the support of
`χ`, then `F(Φ₁# T - Φ₀# T) ≤ δ (L ^ (k + 1) M(T) + L ^ k M(∂ T))`, where `Φᵢ# T = T ∘ (χ Φᵢ^*)`
and `F` is the real normal flat mass. -/
theorem normalFlatMass_comp_cutoffPullbackCLM_sub_le
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) (hT : IsNormal T)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (hχ₁ : ∀ x, |χ x| ≤ 1) {δ L : ℝ≥0}
    (hδ : ∀ x ∈ tsupport χ, ‖Φ₁ x - Φ₀ x‖ ≤ δ) (hL₀ : ∀ x ∈ tsupport χ, ‖fderiv ℝ Φ₀ x‖ ≤ L)
    (hL₁ : ∀ x ∈ tsupport χ, ‖fderiv ℝ Φ₁ x‖ ≤ L) :
    (T ∘L cutoffPullbackCLM χ Φ₁ hΦ₁ - T ∘L cutoffPullbackCLM χ Φ₀ hΦ₀ :
        𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ).normalFlatMass ≤
      δ * (L ^ (k + 1) * mass T + L ^ k * mass (T ∘L extDerivCLM)) := by
  obtain ⟨hT₀, hT₁⟩ := isNormal_succ_iff.1 hT
  obtain ⟨R, S, heq, hS, hR, -, -⟩ :=
    exists_comp_cutoffPullbackCLM_sub_eq_add_comp_extDerivCLM (Ω' := Ω') (hΦ₀ := hΦ₀)
      (hΦ₁ := hΦ₁) T hχ hχ₁ hδ hL₀ hL₁
  -- The difference of the pushforwards is normal, and so are `R` and `S`.
  have hP : IsNormal (T ∘L cutoffPullbackCLM χ Φ₁ hΦ₁ - T ∘L cutoffPullbackCLM χ Φ₀ hΦ₀ :
      𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ) :=
    (hT.comp_cutoffPullbackCLM hχ hχ₁ hL₁).sub (hT.comp_cutoffPullbackCLM hχ hχ₁ hL₀)
  have hRd : R ∘L extDerivCLM =
      (T ∘L cutoffPullbackCLM χ Φ₁ hΦ₁ - T ∘L cutoffPullbackCLM χ Φ₀ hΦ₀) ∘L extDerivCLM := by
    rw [heq, add_comp, comp_assoc, extDerivCLM_comp_extDerivCLM, comp_zero, add_zero]
  have hSd : S ∘L extDerivCLM = T ∘L cutoffPullbackCLM χ Φ₁ hΦ₁ -
      T ∘L cutoffPullbackCLM χ Φ₀ hΦ₀ - R := by
    rw [heq]
    abel
  have hRn : IsNormal R := isNormal_succ_iff.2 ⟨ne_top_of_le_ne_top (by finiteness) hR, by
    rw [hRd]
    exact (isNormal_succ_iff.1 hP).2⟩
  have hSn : IsNormal S := isNormal_succ_iff.2 ⟨ne_top_of_le_ne_top (by finiteness) hS, by
    rw [hSd]
    exact (hP.sub hRn).mass_ne_top⟩
  calc _ ≤ mass R + mass S := normalFlatMass_le_of_eq_add_comp_extDerivCLM _ hRn hSn heq
    _ ≤ δ * L ^ k * mass (T ∘L extDerivCLM) + δ * L ^ (k + 1) * mass T := add_le_add hR hS
    _ = δ * (L ^ (k + 1) * mass T + L ^ k * mass (T ∘L extDerivCLM)) := by ring

/-- **Flat mass of the difference of two pushforwards in degree zero**: let `T` be a `0`-current
of finite mass on `Ω` and let `χ` be a test function with `|χ| ≤ 1`, equal to one near the
support of `T`. If two maps `Φ₀, Φ₁` smooth on `Ω` satisfy `‖Φ₁ - Φ₀‖ ≤ δ` on the support of `χ`,
then `F(Φ₁# T - Φ₀# T) ≤ δ M(T)`, where `Φᵢ# T = T ∘ (χ Φᵢ^*)` and `F` is the real normal flat
mass. -/
theorem normalFlatMass_comp_cutoffPullbackCLM_sub_le_finZero
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) (hT : IsNormal T)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (hχ₁ : ∀ x, |χ x| ≤ 1) {δ : ℝ≥0}
    (hδ : ∀ x ∈ tsupport χ, ‖Φ₁ x - Φ₀ x‖ ≤ δ) :
    (T ∘L cutoffPullbackCLM χ Φ₁ hΦ₁ - T ∘L cutoffPullbackCLM χ Φ₀ hΦ₀ :
        𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ).normalFlatMass ≤ δ * mass T := by
  have hT₀ : mass T ≠ ⊤ := isNormal_finZero_iff.1 hT
  obtain ⟨S, heq, hS, -⟩ :=
    exists_comp_cutoffPullbackCLM_sub_eq_comp_extDerivCLM_finZero (Ω' := Ω') (hΦ₀ := hΦ₀)
      (hΦ₁ := hΦ₁) T hχ hχ₁ hδ
  -- In degree zero the derivative enters the mass bound only through its zeroth power, so any
  -- bound, which exists by compactness of `tsupport χ`, will do.
  obtain ⟨L₀, hL₀⟩ := exists_forall_norm_fderiv_le χ hΦ₀
  obtain ⟨L₁, hL₁⟩ := exists_forall_norm_fderiv_le χ hΦ₁
  have hSn : IsNormal S := isNormal_succ_iff.2
    ⟨ne_top_of_le_ne_top (by finiteness) hS, by
      rw [← heq]
      exact ((hT.comp_cutoffPullbackCLM hχ hχ₁ hL₁).sub
        (hT.comp_cutoffPullbackCLM hχ hχ₁ hL₀)).mass_ne_top⟩
  calc _ ≤ mass (0 : 𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ) + mass S :=
        normalFlatMass_le_of_eq_add_comp_extDerivCLM _ isNormal_zero hSn (by rw [heq, zero_add])
    _ ≤ δ * mass T := by simpa using hS

/-- **Flat convergence of pushforwards**: let `T` be a normal `(k + 1)`-current on `Ω` and let `χ`
be a test function with `|χ| ≤ 1`, equal to one near the support of `T`. If maps `Φ i` smooth on
`Ω` converge uniformly to `Φ` on the support of `χ`, and eventually their derivatives are bounded
by a common `L` there, then `Φ i # T → Φ# T` in real normal flat mass, where
`Ψ# T = T ∘ (χ Ψ^*)`. -/
theorem tendsto_normalFlatMass_comp_cutoffPullbackCLM_sub {ι : Type*} {l : Filter ι}
    {Φs : ι → E → E'} {hΦs : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φs i) Ω} {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (hT : IsNormal T) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (hχ₁ : ∀ x, |χ x| ≤ 1)
    (hu : TendstoUniformlyOn Φs Φ l (tsupport χ)) {L : ℝ≥0}
    (hL : ∀ᶠ i in l, ∀ x ∈ tsupport χ, ‖fderiv ℝ (Φs i) x‖ ≤ L) :
    Tendsto (fun i ↦ (T ∘L cutoffPullbackCLM χ (Φs i) (hΦs i) - T ∘L cutoffPullbackCLM χ Φ hΦ :
      𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] ℝ) →L[ℝ] ℝ).normalFlatMass) l (𝓝 0) := by
  obtain ⟨hT₀, hT₁⟩ := isNormal_succ_iff.1 hT
  obtain ⟨C, hC⟩ := exists_forall_norm_fderiv_le χ hΦ
  refine TauCeti.tendsto_nhds_zero_of_forall_eventually_le_mul
    (C := max L C ^ (k + 1) * mass T + max L C ^ k * mass (T ∘L extDerivCLM))
    (by finiteness) fun δ hδ ↦ ?_
  filter_upwards [hL, Metric.tendstoUniformlyOn_iff.1 hu δ hδ] with i hi hdist
  exact normalFlatMass_comp_cutoffPullbackCLM_sub_le T hT hχ hχ₁
    (fun x hx ↦ by rw [← dist_eq_norm, dist_comm]; exact (hdist x hx).le)
    (fun x hx ↦ (hC x hx).trans (NNReal.coe_le_coe.2 (le_max_right _ _)))
    fun x hx ↦ (hi x hx).trans (NNReal.coe_le_coe.2 (le_max_left _ _))

/-- **Flat convergence of pushforwards in degree zero**: let `T` be a `0`-current of finite mass
on `Ω` and let `χ` be a test function with `|χ| ≤ 1`, equal to one near the support of `T`. If
maps `Φ i` smooth on `Ω` converge uniformly to `Φ` on the support of `χ`, then `Φ i # T → Φ# T`
in real normal flat mass, where `Ψ# T = T ∘ (χ Ψ^*)`. -/
theorem tendsto_normalFlatMass_comp_cutoffPullbackCLM_sub_finZero {ι : Type*} {l : Filter ι}
    {Φs : ι → E → E'} {hΦs : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φs i) Ω} {Φ : E → E'}
    {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ)
    (hT : IsNormal T) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) (hχ₁ : ∀ x, |χ x| ≤ 1)
    (hu : TendstoUniformlyOn Φs Φ l (tsupport χ)) :
    Tendsto (fun i ↦ (T ∘L cutoffPullbackCLM χ (Φs i) (hΦs i) - T ∘L cutoffPullbackCLM χ Φ hΦ :
      𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] ℝ) →L[ℝ] ℝ).normalFlatMass) l (𝓝 0) := by
  refine TauCeti.tendsto_nhds_zero_of_forall_eventually_le_mul (isNormal_finZero_iff.1 hT)
    fun δ hδ ↦ ?_
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hu δ hδ] with i hdist
  exact normalFlatMass_comp_cutoffPullbackCLM_sub_le_finZero T hT hχ hχ₁
    fun x hx ↦ by rw [← dist_eq_norm, dist_comm]; exact (hdist x hx).le

end ContinuousLinearMap
