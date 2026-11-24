/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.Spectral.Flow
import TauCeti.Algebra.Algebra.Spectrum
import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Resolvent
import TauCeti.Topology.Algebra.Indicator
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible
import TauCeti.Topology.Order.Interval

/-!
# Spectral flow under a fractional linear change of operator

Let `k` be a real number and `T` a self-adjoint operator on a real or complex Hilbert space with
`1 + k T` invertible, that is, with `1 + k x ≠ 0` on the spectrum of `T`
(`spectrum.isUnit_one_add_smul_iff`). The operator `T (1 + k T)⁻¹` is the image of `T`
under the fractional linear function `x ↦ x / (1 + k x)`
(`IsSelfAdjoint.cfc_div_one_add_mul`). This function fixes `0`, has derivative `1` there, and is
increasing on each interval avoiding its pole
`-1 / k`. So an eigenvalue of `T` crossing `0` upwards becomes an eigenvalue of `T (1 + k T)⁻¹`
crossing `0` upwards, and a continuous path `A` of self-adjoint Fredholm operators along which
`1 + k A` stays invertible has the same spectral flow as the path `A (1 + k A)⁻¹`
(`TauCeti.spectralFlow_mul_ringInverse_one_add_smul`).

Such changes of operator relate the bounded transforms `c A (c - A)⁻¹` of an unbounded
self-adjoint operator `A` at different real shifts `c`, which have the eigenvalues `c λ / (c - λ)`
for the eigenvalues `λ` of `A`: the transform at `c'` is the transform at `c` composed with
`x ↦ x / (1 + k x)` for `k = (c' - c) / (c c')`.

The proof compares local counts of eigenvalues. For `0 < c'` with `k c' < 1`, the function
`x ↦ x / (1 + k x)` maps the points of `[0, c' / (1 - k c')]` onto `[0, c']` and no other point of
the real line off its pole into `[0, c']`. So at a spectral cut `c'` of `T (1 + k T)⁻¹`, its
spectral projection for `[0, c']` is the spectral projection of `T` for `[0, c' / (1 - k c')]`. For
a smaller cut `c` of `T`, the latter differs from the count of eigenvalues of `T` in `[0, c]` by the
rank of the spectral projection for `(c, c' / (1 - k c')]`, which is locally constant along the
path. Thus
both paths have local counts which change alike, and
`TauCeti.spectralFlow_eq_of_forall_exists_isSpectralCutOn` compares their spectral flows.

## Main results

* `TauCeti.spectralFlow_mul_ringInverse_one_add_smul`: the spectral flow of `A (1 + k A)⁻¹` is that
  of `A`.

## References

* J. Phillips, *Self-adjoint Fredholm operators and spectral flow*, Canad. Math. Bull. **39**
  (1996), 460--467.
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33.
-/

public section

open Filter Metric Set Topology

variable {𝕜 H : Type*} [RCLike 𝕜] [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  [NormedAlgebra ℝ (H →L[𝕜] H)] [IsometricContinuousFunctionalCalculus ℝ (H →L[𝕜] H) IsSelfAdjoint]

namespace TauCeti

/-! ### The preimage of a small interval -/

/-- For `k c < 1`, the fractional linear function `x ↦ x / (1 + k x)` sends a point
`x` off its pole into `[0, c]` exactly when `x ∈ [0, c / (1 - k c)]`. -/
private theorem div_one_add_mul_mem_Icc_iff {k c x : ℝ} (hkc : k * c < 1)
    (hx : 1 + k * x ≠ 0) : x / (1 + k * x) ∈ Icc 0 c ↔ x ∈ Icc 0 (c / (1 - k * c)) := by
  have hd : 0 < 1 - k * c := by linarith
  rw [mem_Icc, mem_Icc, le_div_iff₀ hd]
  rcases hx.lt_or_gt with hneg | hpos
  · -- Beyond the pole, `x / (1 + k x)` is either negative or larger than `c`.
    rw [div_le_iff_of_neg hneg, le_div_iff_of_neg hneg]
    constructor
    · rintro ⟨h₁, h₂⟩
      -- Here `c (1 + k x) ≤ x ≤ 0` forces `c = 0` and then `x = 0`, off the pole.
      have hc : 0 ≤ c := by nlinarith
      have hx₀ : x * (1 - k * c) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hd.le
      have hc₁ : c ≤ x * (1 - k * c) := by nlinarith
      obtain rfl : c = 0 := by linarith
      obtain rfl : x = 0 := by linarith
      linarith
    · rintro ⟨h₁, h₂⟩
      -- Here `0 ≤ x ≤ c / (1 - k c)` and `1 + k x < 0` force `k < 0`, and then `1 + k x > 0`.
      have hk : k < 0 := by nlinarith
      nlinarith [mul_nonneg (sub_nonneg.2 h₂) (neg_nonneg.2 hk.le)]
  · rw [div_le_iff₀ hpos, le_div_iff₀ hpos]
    constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> nlinarith

/-- The fractional linear function `x ↦ x / (1 + k x)` sends `c / (1 - k c)` to `c` when
`k c ≠ 1`. -/
private theorem div_one_add_mul_div_one_sub_mul {k c : ℝ} (hkc : k * c ≠ 1) :
    c / (1 - k * c) / (1 + k * (c / (1 - k * c))) = c := by
  have hd : 1 - k * c ≠ 0 := sub_ne_zero.2 hkc.symm
  have h₁ : 1 + k * (c / (1 - k * c)) = 1 / (1 - k * c) := by
    field_simp
    ring
  rw [h₁, div_div_div_cancel_right₀ hd, div_one]

/-! ### Local counts -/

variable [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] {T : H →L[𝕜] H} {k c c' : ℝ}

/-- At a spectral cut `c'` of `T (1 + k T)⁻¹` with `k c' < 1`, the spectral projection of
`T (1 + k T)⁻¹` for `[0, c']` is the spectral projection of `T` for `[0, c' / (1 - k c')]`, and
`c' / (1 - k c')` is not in the spectrum of `T`. -/
private theorem cfc_indicator_Icc_mul_ringInverse_one_add_smul (hT : IsSelfAdjoint T)
    (hk : IsUnit (1 + k • T)) (hc' : 0 < c') (hkc : k * c' < 1)
    (h₁ : -c' ∉ spectrum ℝ (T * Ring.inverse (1 + k • T)))
    (h₂ : c' ∉ spectrum ℝ (T * Ring.inverse (1 + k • T)))
    (hfd : FiniteDimensional 𝕜
      (cfc ((Icc (-c') c').indicator (1 : ℝ → ℝ)) (T * Ring.inverse (1 + k • T))).range) :
    cfc ((Icc 0 c').indicator (1 : ℝ → ℝ)) (T * Ring.inverse (1 + k • T)) =
        cfc ((Icc 0 (c' / (1 - k * c'))).indicator (1 : ℝ → ℝ)) T ∧
      c' / (1 - k * c') ∉ spectrum ℝ T := by
  have hne := spectrum.isUnit_one_add_smul_iff.1 hk
  have hg : ContinuousOn (fun x : ℝ ↦ x / (1 + k * x)) (spectrum ℝ T) :=
    continuousOn_id.div (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) hne
  have hS := hT.cfc_div_one_add_mul hk
  have hsp : spectrum ℝ (T * Ring.inverse (1 + k • T)) =
      (fun x : ℝ ↦ x / (1 + k * x)) '' spectrum ℝ T := by
    rw [← hS, cfc_map_spectrum _ T]
  have hcut : IsSpectralCutOn (fun _ : ℝ ↦ T * Ring.inverse (1 + k • T)) c' univ :=
    isSpectralCutOn_iff.2 ⟨hc', fun _ _ ↦ ⟨h₁, h₂, hfd⟩⟩
  have hind := hcut.continuousOn_indicator_Icc_zero (mem_univ 0)
    (by rw [← hS]; exact cfc_predicate _ T)
  refine ⟨?_, fun hmem ↦ h₂ ?_⟩
  · rw [← hS, ← cfc_comp _ _ T hT (hsp ▸ hind) hg]
    refine cfc_congr fun x hx ↦ ?_
    simp only [Function.comp_apply, indicator, div_one_add_mul_mem_Icc_iff hkc (hne x hx),
      Pi.one_apply]
  · rw [hsp]
    exact ⟨_, hmem, div_one_add_mul_div_one_sub_mul hkc.ne⟩

/-- For a spectral cut `c` of `T` and `c < d` with `d` not in the spectrum, the rank of the
spectral projection for `[0, d]`, if finite, is the count of eigenvalues in `[0, c]` plus the rank
of the spectral projection for `(c, d]`. -/
private theorem finrank_range_cfc_indicator_Icc_eq_add {d : ℝ} (hT : IsSelfAdjoint T)
    (hcut : IsSpectralCutOn (fun _ : ℝ ↦ T) c univ) (hcd : c < d) (hd : d ∉ spectrum ℝ T)
    (hfd : FiniteDimensional 𝕜 (cfc ((Icc 0 d).indicator (1 : ℝ → ℝ)) T).range) :
    Module.finrank 𝕜 (cfc ((Icc 0 d).indicator (1 : ℝ → ℝ)) T).range = spectralCount c T +
      Module.finrank 𝕜 (cfc ((Ioc c d).indicator (1 : ℝ → ℝ)) T).range := by
  have hdisj : Disjoint (Icc 0 c) (Ioc c d) :=
    disjoint_left.2 fun x (hx : x ∈ Icc 0 c) (hx' : x ∈ Ioc c d) ↦ (not_lt.2 hx.2) hx'.1
  have h₀ := hcut.continuousOn_indicator_Icc_zero (mem_univ 0) hT
  have := hcut.finiteDimensional_range_cfc_indicator_Icc_zero (mem_univ 0) hT
  have hcont : ContinuousOn ((Ioc c d).indicator (1 : ℝ → ℝ)) (spectrum ℝ T) :=
    continuousOn_const.continuousOn_indicator_of_disjoint_frontier
      (disjoint_frontier_Ioc (hcut.notMem_spectrum (mem_univ 0)) hd)
  have hcontd : ContinuousOn ((Icc 0 d).indicator (1 : ℝ → ℝ)) (spectrum ℝ T) := by
    rw [← Icc_union_Ioc_eq_Icc hcut.pos.le hcd.le, indicator_union_of_disjoint hdisj]
    exact h₀.add hcont
  have : FiniteDimensional 𝕜 (cfc ((Ioc c d).indicator (1 : ℝ → ℝ)) T).range :=
    Submodule.finiteDimensional_of_le (T.range_cfc_indicator_le_of_subset (Ω := Ioc c d)
      (Ω' := Icc 0 d) (fun x hx ↦ ⟨hcut.pos.le.trans hx.1.le, hx.2⟩) hcont hcontd)
  rw [spectralCount_def, ← Icc_union_Ioc_eq_Icc hcut.pos.le hcd.le]
  exact T.finrank_range_cfc_indicator_union hdisj h₀ hcont

/-! ### Spectral flow -/

variable {A : ℝ → H →L[𝕜] H} {a b : ℝ}

omit [IsScalarTower ℝ 𝕜 (H →L[𝕜] H)] in
/-- Along a continuous path `A` of self-adjoint Fredholm operators on a set `s` with `1 + k A`
invertible, the path `A (1 + k A)⁻¹` is again a continuous path of self-adjoint Fredholm
operators. -/
private theorem mul_ringInverse_one_add_smul_regular {s : Set ℝ} (hA : ContinuousOn A s)
    (hsa : ∀ t ∈ s, IsSelfAdjoint (A t)) (hF : ∀ t ∈ s, (A t).IsFredholm)
    (hk : ∀ t ∈ s, IsUnit (1 + k • A t)) :
    ContinuousOn (fun t ↦ A t * Ring.inverse (1 + k • A t)) s ∧
      (∀ t ∈ s, IsSelfAdjoint (A t * Ring.inverse (1 + k • A t))) ∧
      ∀ t ∈ s, (A t * Ring.inverse (1 + k • A t)).IsFredholm := by
  refine ⟨fun t ht ↦ ?_, fun t ht ↦ ?_, fun t ht ↦ ?_⟩
  · obtain ⟨u, hu⟩ := hk t ht
    have h₁ : ContinuousWithinAt (fun t ↦ 1 + k • A t) s t :=
      continuousWithinAt_const.add ((hA t ht).const_smul k)
    have h₂ : ContinuousAt Ring.inverse (1 + k • A t) := hu ▸ NormedRing.inverse_continuousAt u
    exact (hA t ht).mul (ContinuousAt.comp_continuousWithinAt (f := fun t ↦ 1 + k • A t) h₂ h₁)
  · rw [← (hsa t ht).cfc_div_one_add_mul (hk t ht)]
    exact cfc_predicate _ _
  · obtain ⟨u, hu⟩ := hk t ht
    rw [← hu, Ring.inverse_unit, ContinuousLinearMap.mul_def]
    exact (hF t ht).comp (ContinuousLinearMap.isInvertible_iff_isUnit.2 u⁻¹.isUnit).isFredholm

/-- **Spectral flow under a fractional linear change of operator.** Let `A` be a continuous path of
self-adjoint Fredholm operators on `[a, b]` and `k` a real number with `1 + k A t` invertible for
every `t ∈ [a, b]`. Then the path `A (1 + k A)⁻¹`, the image of `A` under `x ↦ x / (1 + k x)`, has
the same spectral flow as `A`. -/
theorem spectralFlow_mul_ringInverse_one_add_smul (hab : a ≤ b) (hA : ContinuousOn A (Icc a b))
    (hsa : ∀ t ∈ Icc a b, IsSelfAdjoint (A t)) (hF : ∀ t ∈ Icc a b, (A t).IsFredholm)
    (hk : ∀ t ∈ Icc a b, IsUnit (1 + k • A t)) :
    spectralFlow (fun t ↦ A t * Ring.inverse (1 + k • A t)) a b = spectralFlow A a b := by
  set B := fun t ↦ A t * Ring.inverse (1 + k • A t) with hBdef
  obtain ⟨hB, hsaB, hFB⟩ := mul_ringInverse_one_add_smul_regular hA hsa hF hk
  refine spectralFlow_eq_of_forall_exists_isSpectralCutOn hab hA hsa hF hB hsaB hFB fun t ht ↦ ?_
  -- A small cut `c'` of `B`, the corresponding endpoint `d` for `A`, and a smaller cut `c` of `A`.
  obtain ⟨c', hc'η, ε₁, hε₁, hc'⟩ := exists_isSpectralCutOn_ball_inter_lt hB hsaB hFB ht
    (η := 1 / (|k| + 1)) (by positivity)
  have hkc : k * c' < 1 := by
    rw [lt_div_iff₀ (by positivity)] at hc'η
    nlinarith [le_abs_self k, hc'.pos]
  set d := c' / (1 - k * c')
  have hd : 0 < d := div_pos hc'.pos (by linarith)
  obtain ⟨c, hcd, ε₂, hε₂, hc⟩ := exists_isSpectralCutOn_ball_inter_lt hA hsa hF ht hd
  refine ⟨min ε₁ ε₂, lt_min hε₁ hε₂, c, c', hc.mono ?_, hc'.mono ?_, fun u hu ↦ ?_⟩
  · exact inter_subset_inter_left _ (ball_subset_ball (min_le_right _ _))
  · exact inter_subset_inter_left _ (ball_subset_ball (min_le_left _ _))
  -- At every time near `t`, the count of `B` in `[0, c']` is that of `A` in `[0, c]` plus the rank
  -- of the projection of `A` for `(c, d]`, which does not depend on the time.
  have hdec (v : ℝ) (hv : v ∈ ball t (min ε₁ ε₂) ∩ Icc a b) :
      spectralCount c' (B v) = spectralCount c (A v) +
          Module.finrank 𝕜 (cfc ((Ioc c d).indicator (1 : ℝ → ℝ)) (A v)).range ∧
        d ∉ spectrum ℝ (A v) := by
    have hv₁ : v ∈ ball t ε₁ ∩ Icc a b := ⟨ball_subset_ball (min_le_left _ _) hv.1, hv.2⟩
    have hv₂ : v ∈ ball t ε₂ ∩ Icc a b := ⟨ball_subset_ball (min_le_right _ _) hv.1, hv.2⟩
    obtain ⟨hP, hdv⟩ := cfc_indicator_Icc_mul_ringInverse_one_add_smul (hsa v hv.2) (hk v hv.2)
      hc'.pos hkc (hc'.neg_notMem_spectrum hv₁) (hc'.notMem_spectrum hv₁)
      (hc'.finiteDimensional_range_cfc_indicator_Icc hv₁)
    have hfd := hc'.finiteDimensional_range_cfc_indicator_Icc_zero hv₁ (hsaB v hv.2)
    simp only [hBdef] at hfd ⊢
    rw [hP] at hfd
    rw [spectralCount_def, hP]
    exact ⟨finrank_range_cfc_indicator_Icc_eq_add (hsa v hv.2)
      (isSpectralCutOn_iff.2 ⟨hc.pos, fun _ _ ↦ (isSpectralCutOn_iff.1 hc).2 v hv₂⟩) hcd hdv hfd,
      hdv⟩
  have hsub := ordConnected_Icc.uIcc_subset_ball_inter ht ⟨hu.1, hu.2⟩
  have hr := isPreconnected_uIcc.finrank_range_cfc_indicator_eq
    (hA.mono fun v hv ↦ (hsub hv).2) (fun v hv ↦ hsa v (hsub hv).2) (Ω := Ioc c d)
    (fun v hv ↦ disjoint_frontier_Ioc
      (hc.notMem_spectrum ⟨ball_subset_ball (min_le_right _ _) (hsub hv).1, (hsub hv).2⟩)
      (hdec v (hsub hv)).2) left_mem_uIcc right_mem_uIcc
  rw [(hdec u hu).1, (hdec t ⟨mem_ball_self (lt_min hε₁ hε₂), ht⟩).1, hr]
  push_cast
  ring

end TauCeti
