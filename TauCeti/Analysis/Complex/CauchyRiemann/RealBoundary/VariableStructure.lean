/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
import TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak
import TauCeti.Analysis.Complex.Conformal.Reflection.Basic
import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Complex.Wirtinger.RealBoundary.Reflection
import TauCeti.Analysis.Sobolev.Local.Reflection.Odd
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# The similarity principle up to a totally real boundary for a variable structure

Let `Ω ⊆ ℂ` be a conjugation-invariant open set, write `z = s + i t` and `Ω⁺ = Ω ∩ {0 ≤ t}` for
its closed upper part, and let `R` be a continuous linear automorphism of a real normed space `V`
(for `V = ℂⁿ` with boundary values in `ℝⁿ`, coordinatewise conjugation). Let `ξ` be a weak
solution on `Ω⁺` of the linear Cauchy–Riemann equation

`∂ₛξ + J ∂ₜξ + C ξ = 0`

in the sense of `TauCeti.IsWeakLinearCauchyRiemannOn`: continuous up to the real axis, with a weak
derivative on `Ω ∩ {0 < t}` that is locally `Lᵖ` up to the axis, and satisfying the equation
almost everywhere. Assume the totally real boundary condition `R ξ(s) = ξ(s)` on `Ω ∩ ℝ`.

Reflecting by `ξ(conj z) = R ξ(z)`, `J(conj z) = -R J(z) R⁻¹` and `C(conj z) = R C(z) R⁻¹` gives a
weak solution of the reflected equation on all of `Ω`
(`TauCeti.IsWeakLinearCauchyRiemannOn.isWeakLinearCauchyRiemannOn_ite_conj`): the sign in the
reflection of `J` is forced by `∂ₜ (ξ ∘ conj) = -(∂ₜξ) ∘ conj`. If moreover `J` is continuous and
`W^{1,p}` up to the axis with `J² = -1`, and `J(s)` anticommutes with `R` on `Ω ∩ ℝ` (for
`R = conj`, this holds when `J(s) = i`), then the reflected structure is continuous and `W^{1,p}`
across the axis, with square `-1`. So the interior theory of
`TauCeti.Analysis.Complex.CauchyRiemann.Similarity.Weak` applies to the reflected solution, and
its conclusions restrict to `Ω⁺`, where the reflection is `ξ`. This is the boundary version of the
Carleman similarity principle and of its consequences for a variable structure, the case
McDuff–Salamon reduce to by reflection in Appendix B.4; the structure `i` was treated in
`TauCeti.Analysis.Complex.CauchyRiemann.RealBoundary.Similarity`.

## Main results

* `TauCeti.IsWeakLinearCauchyRiemannOn.isWeakLinearCauchyRiemannOn_ite_conj`: the reflection of a
  weak solution on `Ω⁺` with the boundary condition is a weak solution on `Ω`.
* `TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg`: near every point of
  `Ω`, boundary points included, `ξ = Φ σ` on the upper part of a disc, with `Φ` a continuous
  `W^{1,p}` family of invertible real-linear maps with `J Φ = Φ i` on the upper part and `σ`
  holomorphic on the whole disc.
* `TauCeti.eqOn_zero_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg_of_forall_isBigO`: unique
  continuation from a zero of infinite order, also at a point of the real axis.
* `TauCeti.setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg`:
  the zeros of a solution that is not identically zero are isolated in `Ω⁺`, also near the axis.

The reflection rests on `ContinuousOn.ite_conj`, `TauCeti.HasWeakFDerivOn.ite_conj` and
`TauCeti.MemWkpLoc.ite_conj`: continuity and weak derivatives glue across the axis for a map
continuous up to the axis whose boundary values are fixed by the twisting map.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications **52**, 2012, Theorem 2.3.5 and Appendix B.4.
-/

public section

open Complex MeasureTheory TopologicalSpace Set Filter Metric
open scoped ComplexConjugate ENNReal

namespace TauCeti

/-! ### The reflected equation -/

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p : ℝ≥0∞} {Ω : Opens ℂ}
  {R : V ≃L[ℝ] V} {J C : ℂ → V →L[ℝ] V} {ξ : ℂ → V}

/-- An almost-everywhere property on the open upper part `Ω ∩ {0 < im}` of a conjugation-invariant
open set, read at the conjugate point, holds almost everywhere on the lower part. -/
private theorem ae_restrict_im_neg_of_ae_restrict_im_pos (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    {P : ℂ → Prop} (h : ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | 0 < z.im}), P z) :
    ∀ᵐ z ∂volume.restrict ((Ω : Set ℂ) ∩ {z | z.im < 0}), P (conj z) := by
  have hconj := (conjLIE.measurePreserving.restrict_preimage_emb
    conjLIE.toHomeomorph.measurableEmbedding ((Ω : Set ℂ) ∩ {z | 0 < z.im})).quasiMeasurePreserving
  refine ae_restrict_of_ae_restrict_of_subset (fun z hz ↦ ?_) (by simpa using hconj.ae h)
  exact ⟨hΩ hz.1, by simpa using hz.2⟩

/-- **The reflected equation.** Let `Ω` be conjugation invariant and `1 ≤ p`, and let `ξ` be a
weak solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω ∩ {0 ≤ im}` with `R ξ(s) = ξ(s)` on `Ω ∩ ℝ`. Then
its reflection `ξ(conj z) = R ξ(z)` is a weak solution on `Ω` of the reflected equation, with
`J(conj z) = -R J(z) R⁻¹` and `C(conj z) = R C(z) R⁻¹`. -/
theorem IsWeakLinearCauchyRiemannOn.isWeakLinearCauchyRiemannOn_ite_conj (hp : 1 ≤ p)
    (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hξ : IsWeakLinearCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J C ξ)
    (hξR : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (ξ x) = ξ x) :
    IsWeakLinearCauchyRiemannOn p Ω
      (fun z ↦ if 0 ≤ z.im then J z else -R.conjContinuousAlgEquiv (J (conj z)))
      (fun z ↦ if 0 ≤ z.im then C z else R.conjContinuousAlgEquiv (C (conj z)))
      (fun z ↦ if 0 ≤ z.im then ξ z else R (ξ (conj z))) := by
  obtain ⟨hc, hu, D, hD, hDp, hae⟩ := isWeakLinearCauchyRiemannOn_iff.1 hξ
  set L' := (ContinuousLinearMap.compL ℝ ℂ V V (R : V →L[ℝ] V)).comp
    ((ContinuousLinearMap.compL ℝ ℂ ℂ V).flip (conjCLE : ℂ →L[ℝ] ℂ))
  have hD' := hD.ite_conj (fun _ hz _ ↦ hΩ hz) (R : V →L[ℝ] V) hc hξR (hDp.mono_exponent hp)
  refine isWeakLinearCauchyRiemannOn_iff_of_isOpen.2
    ⟨ContinuousOn.ite_conj (fun _ hz _ ↦ hΩ hz) R.continuous hc hξR,
    hu.ite_conj hΩ (R : V →L[ℝ] V), twistedReflection L' D, hD',
    (hDp.ite_conj hΩ L').congr_ae (ae_restrict_of_ae (ite_conj_ae_eq_twistedReflection L' D)),
    ?_⟩
  -- The equation above the axis, and at the conjugate point below it.
  rw [interior_inter_setOf_im_nonneg Ω.isOpen] at hae
  have hup := (ae_restrict_iff' (measurableSet_lt measurable_const Complex.measurable_im)).1
    (by rwa [Measure.restrict_restrict (measurableSet_lt measurable_const Complex.measurable_im),
      inter_comm] : ∀ᵐ z ∂(volume.restrict (Ω : Set ℂ)).restrict {z : ℂ | 0 < z.im},
        D z 1 + J z (D z I) + C z (ξ z) = 0)
  have hdown := (ae_restrict_iff' (measurableSet_lt Complex.measurable_im measurable_const)).1
    (by rw [Measure.restrict_restrict (measurableSet_lt Complex.measurable_im measurable_const),
      inter_comm]; exact ae_restrict_im_neg_of_ae_restrict_im_pos hΩ hae :
      ∀ᵐ z ∂(volume.restrict (Ω : Set ℂ)).restrict {z : ℂ | z.im < 0},
        D (conj z) 1 + J (conj z) (D (conj z) I) + C (conj z) (ξ (conj z)) = 0)
  filter_upwards [hup, hdown, ae_restrict_of_ae Complex.ae_im_ne_zero] with z hz₁ hz₂ hz
  rcases hz.lt_or_gt with hz | hz
  -- Below the axis each term is `R` of the term at `conj z`, since `conj I = -I` and `R⁻¹ R = 1`.
  · have h := congrArg R (hz₂ hz)
    simp only [map_add, map_zero] at h
    simp [hz, not_le.2 hz, L', ← h]
  · simpa [hz.le, twistedReflection_of_im_pos hz] using hz₁ hz

/-! ### The reflected structure -/

/-- The reflected structure squares to `-1` on `Ω` when `J` does on `Ω ∩ {0 ≤ im}`. -/
private theorem ite_conj_comp_self (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hJ2 : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, J z ∘L J z = -ContinuousLinearMap.id ℝ V) :
    ∀ z ∈ (Ω : Set ℂ),
      (if 0 ≤ z.im then J z else -R.conjContinuousAlgEquiv (J (conj z))) ∘L
        (if 0 ≤ z.im then J z else -R.conjContinuousAlgEquiv (J (conj z))) =
          -ContinuousLinearMap.id ℝ V := by
  intro z hz
  by_cases hz' : 0 ≤ z.im
  · simpa [hz'] using hJ2 z ⟨hz, hz'⟩
  · have h := hJ2 (conj z) ⟨hΩ hz, by simpa using (not_le.1 hz').le⟩
    refine ContinuousLinearMap.ext fun v ↦ ?_
    have hv := congr($h (R.symm v))
    simp only [ContinuousLinearMap.comp_apply, neg_apply,
      ContinuousLinearMap.id_apply] at hv
    simp [hz', hv]

/-- **The reflected data.** Let `1 ≤ p`, let `Ω` be conjugation invariant, let `J` be continuous
and `W^{1,p}` up to the axis with `J² = -1` and `J(s)` anticommuting with `R` on the axis, let `C`
be locally `Lᵖ` up to the axis, and let `ξ` be a weak solution on `Ω ∩ {0 ≤ im}` with
`R ξ(s) = ξ(s)` on the axis. Then the reflected structure is continuous and `W^{1,p}` on `Ω` with
square `-1`, the reflected coefficient is locally `Lᵖ` on `Ω`, and the reflected solution is a weak
solution on `Ω`: the hypotheses of the interior similarity principle. -/
private theorem reflection_hypotheses (hp : 1 ≤ p) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hJ : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 J)
    (hJc : ContinuousOn J ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hJ2 : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hJR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J x v) = -J x (R v))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξ : IsWeakLinearCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J C ξ)
    (hξR : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (ξ x) = ξ x) :
    MemWkpLoc p Ω 1 (fun z ↦ if 0 ≤ z.im then J z else -R.conjContinuousAlgEquiv (J (conj z))) ∧
      ContinuousOn (fun z ↦ if 0 ≤ z.im then J z else -R.conjContinuousAlgEquiv (J (conj z))) Ω ∧
      (∀ z ∈ (Ω : Set ℂ),
        (if 0 ≤ z.im then J z else -R.conjContinuousAlgEquiv (J (conj z))) ∘L
          (if 0 ≤ z.im then J z else -R.conjContinuousAlgEquiv (J (conj z))) =
            -ContinuousLinearMap.id ℝ V) ∧
      MemLpLoc p Ω (fun z ↦ if 0 ≤ z.im then C z else R.conjContinuousAlgEquiv (C (conj z))) ∧
      IsWeakLinearCauchyRiemannOn p Ω
        (fun z ↦ if 0 ≤ z.im then J z else -R.conjContinuousAlgEquiv (J (conj z)))
        (fun z ↦ if 0 ≤ z.im then C z else R.conjContinuousAlgEquiv (C (conj z)))
        (fun z ↦ if 0 ≤ z.im then ξ z else R (ξ (conj z))) := by
  -- The twisting maps `X ↦ R X R⁻¹` of the coefficient and `X ↦ -R X R⁻¹` of the structure.
  let K : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V :=
    (R.conjContinuousAlgEquiv.toContinuousLinearEquiv : (V →L[ℝ] V) →L[ℝ] V →L[ℝ] V)
  have hK (z : ℂ) : K (C (conj z)) = R.conjContinuousAlgEquiv (C (conj z)) := rfl
  have hLJ (z : ℂ) : (-K) (J (conj z)) = -R.conjContinuousAlgEquiv (J (conj z)) := rfl
  have hL : ∀ x : ℝ, (x : ℂ) ∈ Ω → (-K) (J x) = J x := fun x hx ↦
    ContinuousLinearMap.ext fun v ↦ by simp [K, hJR x hx]
  simp only [← hLJ, ← hK]
  exact ⟨hJ.ite_conj hp hΩ (-K) hJc hL,
    ContinuousOn.ite_conj (fun _ hz _ ↦ hΩ hz) (-K).continuous hJc hL,
    by simpa only [hLJ] using ite_conj_comp_self hΩ hJ2, hC.ite_conj hΩ K,
    by simpa only [hLJ, hK] using hξ.isWeakLinearCauchyRiemannOn_ite_conj hp hΩ hξR⟩

/-! ### The similarity principle and its consequences -/

/-- **The similarity principle up to a totally real boundary** (Carleman; McDuff–Salamon,
Theorem 2.3.5, with the reflection of Appendix B.4). Let `V` be a finite-dimensional complex normed
space, `2 < p < ∞`, `Ω` conjugation invariant, and `R` a real-linear automorphism of `V`. Let `J`
be continuous and `W^{1,p}` up to the real axis on `Ω ∩ {0 ≤ im}`, with `J² = -1` there and `J(s)`
anticommuting with `R` on `Ω ∩ ℝ`, let `C` be locally `Lᵖ` up to the axis, and let `ξ` be a weak
solution of `∂ₛξ + J ∂ₜξ + C ξ = 0` on `Ω ∩ {0 ≤ im}` with `R ξ(s) = ξ(s)` on `Ω ∩ ℝ`. Then every
point `z₀ ∈ Ω`, in particular every real one, is the centre of a disc in `Ω` carrying a continuous
`W^{1,p}` family `Φ` of invertible real-linear maps with `J Φ = Φ i` on the upper part of the disc,
and a holomorphic `σ` on the disc, with `ξ = Φ σ` on the upper part of the disc. -/
theorem exists_similarity_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W] (hp : 2 < p)
    (hp_top : p ≠ ∞) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω) {R : W ≃L[ℝ] W} {J C : ℂ → W →L[ℝ] W}
    {ξ : ℂ → W} (hJ : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 J)
    (hJc : ContinuousOn J ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hJ2 : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, J z ∘L J z = -ContinuousLinearMap.id ℝ W)
    (hJR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J x v) = -J x (R v))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξ : IsWeakLinearCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J C ξ)
    (hξR : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (ξ x) = ξ x) {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∃ (Φ : ℂ → W →L[ℝ] W) (σ : ℂ → W),
      ContinuousOn Φ (ball z₀ r) ∧ MemWkpLoc p (ball z₀ r) 1 Φ ∧
      (∀ z ∈ ball z₀ r, IsUnit (Φ z)) ∧
      (∀ z ∈ ball z₀ r ∩ {z | 0 ≤ z.im},
        J z ∘L Φ z = Φ z ∘L (I • ContinuousLinearMap.id ℝ W)) ∧
      DifferentiableOn ℂ σ (ball z₀ r) ∧
      EqOn ξ (fun z ↦ Φ z (σ z)) (ball z₀ r ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨hJ', hJc', hJ2', hC', hξ'⟩ := reflection_hypotheses (one_le_two.trans hp.le) hΩ hJ
    hJc hJ2 hJR hC hξ hξR
  obtain ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦW, hΦu, hJΦ, hσ, hξσ⟩ :=
    exists_similarity_of_isWeakLinearCauchyRiemannOn hp hp_top hJ' hJc' hJ2' hC' hξ' hz₀
  refine ⟨r, hr, hrΩ, Φ, σ, hΦc, hΦW, hΦu, fun z hz ↦ ?_, hσ, fun z hz ↦ ?_⟩
  · simpa [hz.2.out] using hJΦ z hz.1
  · simpa [hz.2.out] using hξσ hz.1

open Asymptotics Topology in
/-- **Unique continuation from a zero of infinite order, up to a totally real boundary.** Let `V`
be finite-dimensional, `2 < p ≤ ∞`, `Ω` conjugation invariant with `Ω ∩ {0 ≤ im}` preconnected,
and let `J`, `C`, `ξ` and `R` be as in
`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg`. If `ξ` vanishes to
infinite order within `{0 ≤ im}` at a point of `Ω ∩ {0 ≤ im}`, possibly on the real axis, it
vanishes on `Ω ∩ {0 ≤ im}`. -/
theorem eqOn_zero_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg_of_forall_isBigO
    [FiniteDimensional ℝ V] (hp : 2 < p) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hJ : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 J)
    (hJc : ContinuousOn J ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hJ2 : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hJR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J x v) = -J x (R v))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξ : IsWeakLinearCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J C ξ)
    (hξR : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (ξ x) = ξ x) {z₀ : ℂ}
    (hz₀ : z₀ ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im})
    (h₀ : ∀ n : ℕ, ξ =O[𝓝[{z | 0 ≤ z.im}] z₀] fun z ↦ (z - z₀) ^ n) :
    EqOn ξ 0 ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨hJ', hJc', hJ2', hC', hξ'⟩ := reflection_hypotheses (one_le_two.trans hp.le) hΩ hJ
    hJc hJ2 hJR hC hξ hξR
  obtain ⟨W, hWΩ, hWo, hWc, hW⟩ :=
    exists_isPreconnected_isOpen_superset_inter_im_nonneg_of_symmetric Ω.isOpen hΩ hΩc
  have h := eqOn_zero_of_isWeakLinearCauchyRiemannOn_of_forall_isBigO (Ω := ⟨W, hWo⟩) hp hWc
    (hJ'.mono hWΩ) (hJc'.mono hWΩ) (fun z hz ↦ hJ2' z (hWΩ hz)) (hC'.mono_set hWΩ)
    (hξ'.mono hWΩ) (hW hz₀) fun n ↦ isBigO_ite_conj_sub_pow (R : V →L[ℝ] V) hz₀.2.out (h₀ n)
  intro z hz
  simpa [hz.2.out] using h (hW hz)

/-- **Isolated zeros up to a totally real boundary.** Let `V` be finite-dimensional, `2 < p ≤ ∞`,
`Ω` conjugation invariant with `Ω ∩ {0 ≤ im}` preconnected, and let `J`, `C`, `ξ` and `R` be as in
`TauCeti.exists_similarity_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg`. If `ξ` is not
identically zero on `Ω ∩ {0 ≤ im}`, its zeros form a discrete subset of `Ω ∩ {0 ≤ im}`, also near
the real axis. -/
theorem setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn_inter_im_nonneg
    [FiniteDimensional ℝ V] (hp : 2 < p) (hΩ : MapsTo (starRingEnd ℂ) Ω Ω)
    (hΩc : IsPreconnected ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hJ : MemWkpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) 1 J)
    (hJc : ContinuousOn J ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}))
    (hJ2 : ∀ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (hJR : ∀ x : ℝ, (x : ℂ) ∈ Ω → ∀ v, R (J x v) = -J x (R v))
    (hC : MemLpLoc p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) C)
    (hξ : IsWeakLinearCauchyRiemannOn p ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) J C ξ)
    (hξR : ∀ x : ℝ, (x : ℂ) ∈ Ω → R (ξ x) = ξ x)
    (hne : ∃ z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}, ξ z ≠ 0) :
    {z | ξ z ≠ 0} ∈ codiscreteWithin ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := by
  obtain ⟨hJ', hJc', hJ2', hC', hξ'⟩ := reflection_hypotheses (one_le_two.trans hp.le) hΩ hJ
    hJc hJ2 hJR hC hξ hξR
  obtain ⟨W, hWΩ, hWo, hWc, hW⟩ :=
    exists_isPreconnected_isOpen_superset_inter_im_nonneg_of_symmetric Ω.isOpen hΩ hΩc
  obtain ⟨z₁, hz₁, hξz₁⟩ := hne
  have h := setOf_ne_zero_mem_codiscreteWithin_of_isWeakLinearCauchyRiemannOn
    (Ω := ⟨W, hWo⟩) hp hWc (hJ'.mono hWΩ) (hJc'.mono hWΩ) (fun z hz ↦ hJ2' z (hWΩ hz))
    (hC'.mono_set hWΩ) (hξ'.mono hWΩ) ⟨z₁, hW hz₁, by simpa [hz₁.2.out] using hξz₁⟩
  filter_upwards [codiscreteWithin_mono hW h, self_mem_codiscreteWithin _] with z hz hzΩ
  simpa [hzΩ.2.out] using hz

end TauCeti
