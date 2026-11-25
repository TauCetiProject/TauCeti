/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.Reflection
public import TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak
import TauCeti.Analysis.Sobolev.Local.Reflection.Odd
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The similarity principle up to a totally real boundary

Let `V` be a finite-dimensional complex normed space, `Ω ⊆ ℂ` an open set invariant under
conjugation, `2 < p < ∞`, and `R` a real-linear automorphism of `V` (for `V = ℂⁿ`, coordinatewise
conjugation, whose fixed space `ℝⁿ` is the boundary condition). Write `Ω⁺ = Ω ∩ {0 ≤ im}`. Let
`J ∈ W^{1,p}_loc(Ω⁺)` be continuous on `Ω⁺` with `J² = -1` there and anticommuting with `R` on
`Ω ∩ ℝ`, let `C ∈ Lᵖ_loc(Ω⁺)`, and let `ξ` be a weak solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω⁺`
in the sense of `TauCeti.IsWeakLinearCauchyRiemannOn`, with `R ξ = ξ` on `Ω ∩ ℝ`. This is the
boundary version of the similarity principle of
`TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak` for a variable `J`
(McDuff–Salamon, Theorem 2.3.5 with a totally real boundary condition).

The proof reflects across the real axis, as in the regularity theory up to the boundary of
`TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HalfPlane.Reflection`. The solution is
reflected by `R` and the leading coefficient by `M ↦ -R M R⁻¹`, keeping their values on the axis
(`TauCeti.twistedSchwarzReflection`): the boundary conditions make both reflections continuous,
and the reflected coefficient squares to `-1` at every point. Below the axis the reflected
equation is `R` applied to the original one at the conjugate point, with the zeroth-order
coefficient reflected by `TauCeti.crReflectionZeroth`
(`TauCeti.IsWeakLinearCauchyRiemannOn.twistedSchwarzReflection`). The interior theorem
`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn` then applies on `Ω`, and its
conclusions restrict to `Ω⁺`, where the reflections are `ξ` and `J`.

## Main results

* `TauCeti.IsWeakLinearCauchyRiemannOn.twistedSchwarzReflection`: the reflected solution is a weak
  solution of the reflected equation on all of `Ω`.
* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg`: near every point
  of `Ω`, boundary points included, `ξ = Φ σ` on the upper part of a disc, with `Φ` a continuous
  `W^{1,p}` family of invertible real-linear maps satisfying `J Φ = Φ i` there and `σ` holomorphic
  on the whole disc.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Theorem 2.3.5 and Appendix B.4.
-/

public section

open Complex Metric MeasureTheory Set TopologicalSpace
open scoped ComplexConjugate ENNReal

namespace TauCeti

/-! ### The reflected equation -/

section Reflection

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : Opens ℂ} {p : ℝ≥0∞}
  {R : V ≃L[ℝ] V} {J J' C : ℂ → V →L[ℝ] V} {ξ : ℂ → V}

/-- **The reflected solution.** Let `Ω` be invariant under conjugation and `1 ≤ p`, and let `ξ`
solve `∂ₛξ + J ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with `R ξ = ξ` on `Ω ∩ ℝ`. Then the
reflection of `ξ` by `R`, keeping its values on the axis, solves on `Ω` the equation whose
zeroth-order coefficient is reflected by `M ↦ R M R⁻¹`, for every leading coefficient `J'` that
agrees almost everywhere on `Ω` with the reflection `TauCeti.crReflectionCoeff R J` of `J`. No
condition on `J` along the axis is needed. -/
theorem IsWeakLinearCauchyRiemannOn.twistedSchwarzReflection (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hp : 1 ≤ p) (hξ : IsWeakLinearCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J C ξ)
    (hξR : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (ξ x) = ξ x)
    (hJ' : J' =ᵐ[volume.restrict Ω] crReflectionCoeff R J) :
    IsWeakLinearCauchyRiemannOn p Ω J' (crReflectionZeroth R C)
      (TauCeti.twistedSchwarzReflection (R : V →L[ℝ] V) ξ) := by
  obtain ⟨hc, -, D, hD, hDp, hae⟩ := isWeakLinearCauchyRiemannOn_iff.1 hξ
  have hξc := continuousOn_twistedSchwarzReflection (R := (R : V →L[ℝ] V)) hΩ hc hξR
  refine isWeakLinearCauchyRiemannOn_iff_of_isOpen.2 ⟨hξc, hξc.memLpLoc, _,
    hD.twistedSchwarzReflection (fun z hz _ => hΩ hz) _ hc hξR (hDp.mono_exponent hp),
    hDp.twistedReflection hΩ _, ?_⟩
  rw [← Opens.coe_interior, ← Measure.restrict_congr_set
    (inter_setOf_im_nonneg_ae_eq_interior Ω)] at hae
  filter_upwards [Complex.ae_restrict_of_ae_restrict_inter_setOf_im_nonneg
    Ω.isOpen.measurableSet hΩ hae, hJ', ae_restrict_of_ae Complex.ae_im_ne_zero] with z hz hJz hz0
  rw [hJz]
  rcases lt_or_gt_of_ne hz0 with h0 | h0
  · have h := congrArg R (hz.2 h0.le)
    simp only [map_add, map_zero] at h
    simp [h0, ← h]
  · simpa [h0, h0.le] using hz.1 h0.le

end Reflection

/-! ### The similarity principle -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
  {Ω : Opens ℂ} {R : V ≃L[ℝ] V} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V} {z₀ : ℂ}

/-- **The similarity principle up to a totally real boundary** (McDuff–Salamon, Theorem 2.3.5,
boundary version). Let `2 < p < ∞`, let `Ω` be invariant under conjugation, and let `R` be a
real-linear automorphism of `V`. Let `J ∈ W^{1,p}_loc(Ω ∩ {0 ≤ im})` be continuous on
`Ω ∩ {0 ≤ im}` with `J² = -1` there and `R J = -J R` on `Ω ∩ ℝ`, and let `C` be locally `Lᵖ` up
to the axis. Let `ξ` solve `∂ₛξ + J ∂ₜξ + C ξ = 0` weakly on `Ω ∩ {0 ≤ im}` with the boundary
condition `R ξ = ξ` on `Ω ∩ ℝ`. Then every point `z₀ ∈ Ω`, in particular every real one, is the
centre of a disc in `Ω` carrying a continuous `W^{1,p}_loc` family `Φ` of invertible real-linear
maps and a holomorphic `σ` such that `J Φ = Φ i` and `ξ = Φ σ` on the upper part of the disc. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg {p : ℝ≥0∞} (hp : 2 < p)
    (hp_top : p ≠ ∞) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hJ : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 J)
    (hJc : ContinuousOn J ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hJ2 : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hJR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J x v) = -J x (R v))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξ : IsWeakLinearCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J C ξ)
    (hξR : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (ξ x) = ξ x) (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → V →L[ℝ] V) (σ : ℂ → V),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      (∀ z ∈ ball z₀ r ∩ {z | 0 ≤ z.im},
        J z ∘L Φ z = Φ z ∘L (I • ContinuousLinearMap.id ℝ V)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r ∩ {z | 0 ≤ z.im}) := by
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  -- the reflection of `J` by `M ↦ -R M R⁻¹`, as in `TauCeti.crReflectionCoeff`
  set L := -(R.conjContinuousAlgEquiv.toContinuousLinearEquiv : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V)
  have hJL (x : ℝ) (hx : (x : ℂ) ∈ Ω) : L (J x) = J x := by
    ext v
    simp [L, hJR x hx]
  have hJ2' (z : ℂ) (hz : z ∈ Ω) :
      twistedSchwarzReflection L J z ∘L twistedSchwarzReflection L J z =
        -ContinuousLinearMap.id ℝ V := by
    rcases le_or_gt 0 z.im with h0 | h0
    · rw [twistedSchwarzReflection_of_im_nonneg h0]
      exact hJ2 z ⟨hz, h0⟩
    · have h := crReflectionCoeff_mul_self_of_im_neg (R := R) h0
        (by simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using
          hJ2 (conj z) ⟨hΩ hz, by simpa using h0.le⟩)
      rw [crReflectionCoeff_def, twistedReflection_of_im_neg h0,
        ← twistedSchwarzReflection_of_im_neg (ξ := J) h0] at h
      simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.one_def] using h
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦW, hΦu, hJΦ, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn hp hp_top
      (hJ.twistedSchwarzReflection hΩ hp1 L hJc hJL)
      (continuousOn_twistedSchwarzReflection hΩ hJc hJL) hJ2'
      ((memLpLoc_crReflectionZeroth_iff hΩ).2 hC)
      (hξ.twistedSchwarzReflection hΩ hp1 hξR (by
        rw [crReflectionCoeff_def]
        exact ae_restrict_of_ae (twistedSchwarzReflection_ae_eq_twistedReflection L J))) hz₀
  refine ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦW, hΦu, fun z hz ↦ ?_, hσ, fun z hz ↦ ?_⟩
  · simpa [twistedSchwarzReflection_of_im_nonneg hz.2.out] using hJΦ z hz.1
  · simpa [twistedSchwarzReflection_of_im_nonneg hz.2.out] using hξσ hz.1

end TauCeti
