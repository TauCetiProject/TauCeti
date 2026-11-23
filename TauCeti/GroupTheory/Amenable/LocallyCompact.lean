/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.Convolution
public import TauCeti.GroupTheory.Amenable.Linfty
public import TauCeti.MeasureTheory.Integral.PeakFunction
import TauCeti.MeasureTheory.Group.Convolution.ApproximateIdentity

/-!
# Amenable locally compact groups and invariant means on Haar `L∞`

Let `μ` be a regular left Haar measure on a locally compact group `G`. This file proves that `G`
is amenable exactly when `L∞(G, μ)` carries a left-invariant mean: a positive linear functional
`M` with `M 1 = 1` and `M (L_g φ) = M φ`. One implication restricts `M` to `UCB G`
(`TauCeti.Amenable.of_lpTop`). For the other, a left-invariant mean `m` on `UCB G` is extended to
`L∞(G, μ)` by smoothing: for a nonnegative kernel `k ∈ L¹(G, μ)` of integral one,

```text
M φ = m (k ⋆ φ),        (k ⋆ φ) x = ∫ y, k y * φ (y⁻¹ * x) ∂μ,
```

where `k ⋆ φ ∈ UCB G` is `MeasureTheory.Lp.convolutionUCB k φ`.

The functional `M` is positive and normalized for every such kernel. Left translating `φ` turns
the kernel `k` into its right translate `R_(g⁻¹) k`, again nonnegative of integral one, so `M` is
left invariant once `m (k ⋆ φ)` is known not to depend on the choice of kernel. This independence
rests on the identity `m ((h ⋆ e) ⋆ φ) = (∫ h) * m (e ⋆ φ)` for left-invariant means
(`TauCeti.Mean.IsLeftInvariant.apply_convolutionUCB_convolutionL`) together with a **right
approximate identity** in `L¹(G, μ)`: `h ⋆ e` is close to `h` in `L¹` when `e` is a nonnegative
kernel of integral one vanishing outside a small neighbourhood of `1`
(`MeasureTheory.Lp.exists_mem_nhds_one_forall_norm_convolutionL_sub_le_right`).

The right approximate identity comes from writing a convolution as an average of right
translates, `h ⋆ k = ∫ z, k z • R_(z⁻¹) h ∂μ`
(`MeasureTheory.Lp.convolutionL_eq_integral_smul_rightTranslation_inv`), where
`(R_(z⁻¹) h)(x) = c(z) * h (x * z⁻¹)` and `c` is the modular character, together with the strong
continuity of right translation on `L¹`.

## Main definitions

* `TauCeti.Mean.convolutionLpTop m hk`: the positive linear functional `φ ↦ m (k ⋆ φ)` on
  `L∞(G, μ)` for a nonnegative kernel `k ∈ L¹(G, μ)`.

## Main results

* `TauCeti.Mean.IsLeftInvariant.apply_convolutionUCB_eq_of_integral_eq`: for a left-invariant
  mean, `m (h ⋆ φ) = m (k ⋆ φ)` whenever `∫ h = ∫ k`.
* `TauCeti.Mean.IsLeftInvariant.ofLpTop_convolutionLpTop`: the functional `φ ↦ m (k ⋆ φ)`
  restricts to `m` on `UCB G`.
* `TauCeti.amenable_iff_exists_lpTop_invariant_of_regular`: a locally compact group is amenable
  exactly when `L∞` of a regular Haar measure carries a left-invariant mean.

## References

* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G, Theorem G.3.1 and
  its proof.
* G. B. Folland, *A Course in Abstract Harmonic Analysis*, 2nd ed., CRC Press (2016), §2.5, for
  approximate identities in `L¹` of a locally compact group.
-/

public section

noncomputable section

open Filter Topology MeasureTheory BoundedContinuousFunction
open scoped ENNReal BoundedContinuousFunction

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G] {μ : Measure G}
  [μ.IsHaarMeasure] [μ.Regular]

namespace TauCeti

namespace Mean

/-- **Independence of the smoothing kernel**, in symmetric form. For a left-invariant mean `m`,
the value `m (h ⋆ φ)` depends on the kernel `h ∈ L¹(G, μ)` only through `∫ h`:
`(∫ k) * m (h ⋆ φ) = (∫ h) * m (k ⋆ φ)` for all kernels `h, k`. -/
theorem IsLeftInvariant.integral_mul_apply_convolutionUCB {m : Mean G} (hm : m.IsLeftInvariant)
    (h k : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) :
    (∫ x, k x ∂μ) * m (Lp.convolutionUCB h φ) = (∫ x, h x ∂μ) * m (Lp.convolutionUCB k φ) := by
  set a := ∫ x, h x ∂μ
  set b := ∫ x, k x ∂μ
  -- Smoothing `h` and `k` on the right by one kernel `e` concentrated near `1` changes the
  -- values of `m` by at most `δ * ‖φ‖`, and turns them into `a * m (e ⋆ φ)` and `b * m (e ⋆ φ)`.
  have key (δ : ℝ) (hδ : 0 < δ) : |b * m (Lp.convolutionUCB h φ) - a * m (Lp.convolutionUCB k φ)|
      ≤ (|a| + |b|) * ‖φ‖ * δ := by
    obtain ⟨U₁, hU₁, hh⟩ :=
      Lp.exists_mem_nhds_one_forall_norm_convolutionL_sub_le_right (μ := μ) h 1 hδ
    obtain ⟨U₂, hU₂, hk⟩ :=
      Lp.exists_mem_nhds_one_forall_norm_convolutionL_sub_le_right (μ := μ) k 1 hδ
    obtain ⟨e, -, he₁, hen, heU⟩ :=
      exists_nonneg_integral_eq_one_norm_eq_one μ (x₀ := 1) (inter_mem hU₁ hU₂)
    have hU (U : Set G) (hU : U₁ ∩ U₂ ⊆ U) : ∀ᵐ z ∂μ, z ∉ U → e z = 0 := by
      filter_upwards [heU] with z hz hzU using hz fun hz' => hzU (hU hz')
    have close (u : Lp ℝ 1 μ)
        (hu : ‖Lp.convolutionL μ 1 ENNReal.one_ne_top u e - u‖ ≤ δ) :
        |m (Lp.convolutionUCB u φ) - (∫ x, u x ∂μ) * m (Lp.convolutionUCB e φ)| ≤ δ * ‖φ‖ := by
      rw [← hm.apply_convolutionUCB_convolutionL, abs_sub_comm]
      refine (m.abs_apply_sub_apply_le _ _).trans ?_
      rw [← sub_apply, ← Lp.convolutionUCB_sub]
      exact (Lp.norm_convolutionUCB_apply_le _ _).trans
        (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
    have h₁ := close h (hh e hen.le he₁ (hU _ Set.inter_subset_left))
    have h₂ := close k (hk e hen.le he₁ (hU _ Set.inter_subset_right))
    calc |b * m (Lp.convolutionUCB h φ) - a * m (Lp.convolutionUCB k φ)|
        = |b * (m (Lp.convolutionUCB h φ) - a * m (Lp.convolutionUCB e φ)) -
            a * (m (Lp.convolutionUCB k φ) - b * m (Lp.convolutionUCB e φ))| := by
          congr 1
          ring
      _ ≤ |b| * (δ * ‖φ‖) + |a| * (δ * ‖φ‖) := by
          refine (abs_sub _ _).trans (add_le_add ?_ ?_) <;> rw [abs_mul] <;> gcongr
      _ = (|a| + |b|) * ‖φ‖ * δ := by ring
  refine sub_eq_zero.1 (abs_nonpos_iff.1 (le_of_forall_pos_le_add fun ε hε => ?_))
  set C := (|a| + |b|) * ‖φ‖
  refine (key (ε / (C + 1)) (by positivity)).trans ?_
  rw [zero_add, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- **Independence of the smoothing kernel.** For a left-invariant mean `m`, kernels
`h, k ∈ L¹(G, μ)` with the same integral give the same value: `m (h ⋆ φ) = m (k ⋆ φ)`. -/
theorem IsLeftInvariant.apply_convolutionUCB_eq_of_integral_eq {m : Mean G}
    (hm : m.IsLeftInvariant) {h k : Lp ℝ 1 μ} (hhk : ∫ x, h x ∂μ = ∫ x, k x ∂μ)
    (φ : Lp ℝ ∞ μ) : m (Lp.convolutionUCB h φ) = m (Lp.convolutionUCB k φ) := by
  obtain ⟨e, -, he₁, -⟩ := exists_nonneg_integral_eq_one_norm_eq_one μ (x₀ := 1) univ_mem
  have hh := hm.integral_mul_apply_convolutionUCB h e φ
  have hk := hm.integral_mul_apply_convolutionUCB k e φ
  rw [he₁, one_mul] at hh hk
  rw [hh, hk, hhk]

/-- A left-invariant mean does not see right translation of the kernel:
`m ((R_g h) ⋆ φ) = m (h ⋆ φ)`. -/
theorem IsLeftInvariant.apply_convolutionUCB_rightTranslation {m : Mean G}
    (hm : m.IsLeftInvariant) (g : G) (h : Lp ℝ 1 μ) (φ : Lp ℝ ∞ μ) :
    m (Lp.convolutionUCB (Lp.rightTranslation μ 1 ℝ g h) φ) = m (Lp.convolutionUCB h φ) :=
  hm.apply_convolutionUCB_eq_of_integral_eq (Lp.integral_rightTranslation g h) φ

/-- The positive linear functional `φ ↦ m (k ⋆ φ)` on `L∞(G, μ)` obtained from a mean `m` on
`UCB G` by smoothing with a nonnegative kernel `k ∈ L¹(G, μ)`. When `k` has integral one it is
normalized, and when `m` is left invariant so is it. -/
def convolutionLpTop (m : Mean G) {k : Lp ℝ 1 μ} (hk : 0 ≤ k) : Lp ℝ ∞ μ →ₚ[ℝ] ℝ where
  toLinearMap := m.toPositiveLinearMap.toLinearMap ∘ₗ (Lp.convolutionUCB k).toLinearMap
  monotone' _ _ hφψ := OrderHomClass.mono m (Lp.convolutionUCB_mono hk hφψ)

@[simp]
theorem convolutionLpTop_apply (m : Mean G) {k : Lp ℝ 1 μ} (hk : 0 ≤ k) (φ : Lp ℝ ∞ μ) :
    m.convolutionLpTop hk φ = m (Lp.convolutionUCB k φ) :=
  (rfl)

/-- The functional `φ ↦ m (k ⋆ φ)` takes the value `∫ k` at the constant one. -/
theorem convolutionLpTop_one (m : Mean G) {k : Lp ℝ 1 μ} (hk : 0 ≤ k) :
    m.convolutionLpTop hk 1 = ∫ x, k x ∂μ := by
  rw [convolutionLpTop_apply, Lp.convolutionUCB_one, map_smul, map_one, smul_eq_mul,
    mul_one]

/-- For a left-invariant mean `m`, the functional `φ ↦ m (k ⋆ φ)` on `L∞(G, μ)` is invariant under
left translation. -/
theorem IsLeftInvariant.convolutionLpTop_leftTranslation {m : Mean G} (hm : m.IsLeftInvariant)
    {k : Lp ℝ 1 μ} (hk : 0 ≤ k) (g : G) (φ : Lp ℝ ∞ μ) :
    m.convolutionLpTop hk (Lp.leftTranslation μ ∞ ℝ g φ) = m.convolutionLpTop hk φ := by
  rw [convolutionLpTop_apply, convolutionLpTop_apply, Lp.convolutionUCB_apply_leftTranslation,
    hm.apply_convolutionUCB_rightTranslation]

/-- For a left-invariant mean `m` and a nonnegative kernel `k` of integral one, the functional
`φ ↦ m (k ⋆ φ)` on `L∞(G, μ)` restricts to `m` on `UCB G`. Thus every left-invariant mean on
`UCB G` is the restriction of a left-invariant mean on `L∞(G, μ)`. -/
theorem IsLeftInvariant.ofLpTop_convolutionLpTop {m : Mean G} (hm : m.IsLeftInvariant)
    {k : Lp ℝ 1 μ} (hk : 0 ≤ k) (hk₁ : ∫ x, k x ∂μ = 1) :
    ofLpTop (m.convolutionLpTop hk) ((m.convolutionLpTop_one hk).trans hk₁) = m :=
  ext fun f => by
    rw [ofLpTop_apply, convolutionLpTop_apply, hm.apply_convolutionUCB_toLpTop, hk₁, one_mul]

end Mean

variable (μ) in
/-- An amenable locally compact group carries a left-invariant mean on `L∞` of any regular left
Haar measure `μ`: a positive linear functional `M` on `L∞(G, μ)` with `M 1 = 1` and
`M (L_g φ) = M φ`. -/
theorem Amenable.exists_lpTop_invariant [Amenable G] :
    ∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M 1 = 1 ∧
      ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ := by
  obtain ⟨m, hm⟩ := (amenable_iff G).1 ‹_›
  obtain ⟨k, hk, hk₁, -⟩ := exists_nonneg_integral_eq_one_norm_eq_one μ (x₀ := 1) univ_mem
  exact ⟨m.convolutionLpTop hk, (m.convolutionLpTop_one hk).trans hk₁,
    hm.convolutionLpTop_leftTranslation hk⟩

variable (μ) in
/-- **Amenability of a locally compact group by invariant means on Haar `L∞`.** A locally compact
group `G` is amenable exactly when, for a regular left Haar measure `μ`, `L∞(G, μ)` carries a
left-invariant positive linear functional `M` with `M 1 = 1`. -/
theorem amenable_iff_exists_lpTop_invariant_of_regular :
    Amenable G ↔ ∃ M : Lp ℝ ∞ μ →ₚ[ℝ] ℝ, M 1 = 1 ∧
      ∀ g φ, M (Lp.leftTranslation μ ∞ ℝ g φ) = M φ :=
  ⟨fun _ => Amenable.exists_lpTop_invariant μ, fun ⟨M, hM, h⟩ => Amenable.of_lpTop M hM h⟩

end TauCeti
