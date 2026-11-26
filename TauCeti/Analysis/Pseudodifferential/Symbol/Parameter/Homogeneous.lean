/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Pseudodifferential.Symbol.Parameter.Basic
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Quasi-homogeneous parameter-dependent symbols

The terms of Seeley's approximation of the resolvent `(A - z)⁻¹` of an elliptic differential
operator `A` of order `2` are quasi-homogeneous, that is, jointly homogeneous in the frequency and
the spectral parameter under the dilations `(ξ, z) ↦ (t ξ, t² z)`: the principal resolvent symbol
`(‖ξ‖² - z)⁻¹` of the Euclidean Laplacian is quasi-homogeneous of degree `-2`. This file records
this quasi-homogeneity for strongly parameter-dependent symbols (`TauCeti.ParameterSymbol`) and its
behaviour under the operations of the symbol calculus.

* `TauCeti.ParameterSymbol.IsQuasiHomogeneous a μ`: `a((x, t ξ), t² z) = t ^ μ a((x, ξ), z)` for
  `t > 0` whenever `z` and `t² z` lie in `Λ` (`TauCeti.ParameterSymbol.isQuasiHomogeneous_iff`).
* It is preserved by sums, differences, scalar multiples and the inclusions between orders, and
  pointwise compositions add the degrees (`TauCeti.ParameterSymbol.IsQuasiHomogeneous.comp`). The
  inverse of a parameter-elliptic symbol negates the degree
  (`TauCeti.ParameterSymbol.IsQuasiHomogeneous.inverse`).
* A position derivative keeps the degree (`TauCeti.ParameterSymbol.IsQuasiHomogeneous.spatialDeriv`)
  and a frequency derivative lowers it by one
  (`TauCeti.ParameterSymbol.IsQuasiHomogeneous.frequencyDeriv`).
* `TauCeti.ParameterSymbol.IsQuasiHomogeneousAbove a μ R`: the same relation for `t ≥ 1` at
  frequencies of norm at least `R` only. A smooth symbol of negative degree cannot be
  quasi-homogeneous near `(ξ, z) = (0, 0)`, so this is the form taken by the terms of Seeley's
  resolvent parametrix once they are cut off near the origin. It is implied by quasi-homogeneity
  (`TauCeti.ParameterSymbol.IsQuasiHomogeneous.isQuasiHomogeneousAbove`) and preserved by the
  linear operations, the inclusions and pointwise composition.
* Examples: the quasi-homogeneous symbols `TauCeti.ParameterSymbol.ofQuasiHomogeneous`
  (`TauCeti.ParameterSymbol.isQuasiHomogeneous_ofQuasiHomogeneous`), such as the spectral
  parameter `z`, and the symbol `‖ξ‖² - z` of `-Δ - z`, of degree `2`
  (`TauCeti.ParameterSymbol.isQuasiHomogeneous_shiftedLaplacian_zero`).

## References

* M. A. Shubin, *Pseudodifferential Operators and Spectral Theory*, Chapter II, §9.
* R. T. Seeley, *Complex powers of an elliptic operator*, Proc. Sympos. Pure Math. 10 (1967),
  288–307.
-/

public section

noncomputable section

open Filter
open scoped ContDiff Topology

namespace TauCeti

namespace ParameterSymbol

variable {n : ℕ} {Λ : TopologicalSpace.Opens ℂ} {V W U : Type*} [NormedAddCommGroup V]
  [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup U]
  [NormedSpace ℂ U] {m m' : ℝ}

/-- A parameter-dependent symbol is *quasi-homogeneous of degree `μ`* under the dilations
`(ξ, z) ↦ (t ξ, t² z)` of the frequency and the spectral parameter if
`a((x, t ξ), t² z) = t ^ μ a((x, ξ), z)` for every `t > 0` such that both `z` and `t² z` lie in
`Λ` (`TauCeti.ParameterSymbol.isQuasiHomogeneous_iff`). Since the coefficients are only defined on
`Λ`, which need not be closed under these dilations, nothing is required otherwise. The resolvent
symbol `(‖ξ‖² - z)⁻¹` is quasi-homogeneous of degree `-2`. -/
def IsQuasiHomogeneous (a : ParameterSymbol n Λ V W m) (μ : ℝ) : Prop :=
  ∀ p : (CoordinateSpace n × CoordinateSpace n) × ℂ, p.2 ∈ Λ → ∀ t : ℝ, 0 < t →
    (parameterDilation n t p).2 ∈ Λ →
      a.coefficient (parameterDilation n t p) = t ^ μ • a.coefficient p

theorem isQuasiHomogeneous_iff {a : ParameterSymbol n Λ V W m} {μ : ℝ} :
    a.IsQuasiHomogeneous μ ↔ ∀ x ξ, ∀ z ∈ Λ, ∀ t : ℝ, 0 < t → (t ^ 2 : ℝ) • z ∈ Λ →
      a.coefficient ((x, t • ξ), (t ^ 2 : ℝ) • z) = t ^ μ • a.coefficient ((x, ξ), z) := by
  simp only [IsQuasiHomogeneous, parameterDilation_apply, Prod.forall]

variable {μ μ' : ℝ}

theorem IsQuasiHomogeneous.congr_degree {a : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneous μ) (h : μ = μ') : a.IsQuasiHomogeneous μ' :=
  h ▸ ha

@[simp]
theorem isQuasiHomogeneous_zero : (0 : ParameterSymbol n Λ V W m).IsQuasiHomogeneous μ :=
  fun _ _ _ _ _ => by simp

theorem IsQuasiHomogeneous.add {a b : ParameterSymbol n Λ V W m} (ha : a.IsQuasiHomogeneous μ)
    (hb : b.IsQuasiHomogeneous μ) : (a + b).IsQuasiHomogeneous μ := fun p hp t ht htp => by
  rw [coefficient_add, Pi.add_apply, Pi.add_apply, ha p hp t ht htp, hb p hp t ht htp, smul_add]

theorem IsQuasiHomogeneous.smul {a : ParameterSymbol n Λ V W m} (ha : a.IsQuasiHomogeneous μ)
    (c : ℂ) : (c • a).IsQuasiHomogeneous μ := fun p hp t ht htp => by
  rw [coefficient_smul, Pi.smul_apply, Pi.smul_apply, ha p hp t ht htp, smul_comm]

@[simp]
theorem isQuasiHomogeneous_neg_iff {a : ParameterSymbol n Λ V W m} :
    (-a).IsQuasiHomogeneous μ ↔ a.IsQuasiHomogeneous μ := by
  simp only [IsQuasiHomogeneous, coefficient_neg, Pi.neg_apply, smul_neg, neg_inj]

theorem IsQuasiHomogeneous.neg {a : ParameterSymbol n Λ V W m} (ha : a.IsQuasiHomogeneous μ) :
    (-a).IsQuasiHomogeneous μ :=
  isQuasiHomogeneous_neg_iff.2 ha

theorem IsQuasiHomogeneous.sub {a b : ParameterSymbol n Λ V W m} (ha : a.IsQuasiHomogeneous μ)
    (hb : b.IsQuasiHomogeneous μ) : (a - b).IsQuasiHomogeneous μ := fun p hp t ht htp => by
  rw [coefficient_sub, Pi.sub_apply, Pi.sub_apply, ha p hp t ht htp, hb p hp t ht htp, smul_sub]

theorem IsQuasiHomogeneous.sum {ι : Type*} {s : Finset ι} {f : ι → ParameterSymbol n Λ V W m}
    (hf : ∀ i ∈ s, (f i).IsQuasiHomogeneous μ) : (∑ i ∈ s, f i).IsQuasiHomogeneous μ :=
  fun p hp t ht htp => by
    simp only [coefficient_sum, Finset.sum_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun i hi => hf i hi p hp t ht htp

@[simp]
theorem isQuasiHomogeneous_inclusion_iff {a : ParameterSymbol n Λ V W m} (h : m ≤ m') :
    (inclusion h a).IsQuasiHomogeneous μ ↔ a.IsQuasiHomogeneous μ := by
  simp only [IsQuasiHomogeneous, coefficient_inclusion]

theorem IsQuasiHomogeneous.inclusion {a : ParameterSymbol n Λ V W m} (ha : a.IsQuasiHomogeneous μ)
    (h : m ≤ m') : (inclusion h a).IsQuasiHomogeneous μ :=
  (isQuasiHomogeneous_inclusion_iff h).2 ha

/-- The pointwise composition of quasi-homogeneous symbols of degrees `μ'` and `μ` is
quasi-homogeneous of degree `μ' + μ`. -/
theorem IsQuasiHomogeneous.comp {b : ParameterSymbol n Λ W U m'} {a : ParameterSymbol n Λ V W m}
    (hb : b.IsQuasiHomogeneous μ') (ha : a.IsQuasiHomogeneous μ) :
    (b.comp a).IsQuasiHomogeneous (μ' + μ) :=
  fun p hp t ht htp => by
    simp only [coefficient_comp, hb p hp t ht htp, ha p hp t ht htp,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
      Real.rpow_add ht, mul_comm]

/-- The pointwise inverse of a parameter-elliptic symbol quasi-homogeneous of degree `μ` is
quasi-homogeneous of degree `-μ`. -/
theorem IsQuasiHomogeneous.inverse [CompleteSpace V] {a : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneous μ) (he : a.IsElliptic) : (a.inverse he).IsQuasiHomogeneous (-μ) :=
  fun p hp t ht htp => by
    rw [coefficient_inverse, coefficient_inverse, ha p hp t ht htp,
      ContinuousLinearMap.inverse_smul_of_isScalarTower, Real.rpow_neg ht.le]

/-- Differentiating the homogeneity relation: the derivative at the dilated point along the dilated
direction is `t ^ μ` times the derivative. -/
private theorem IsQuasiHomogeneous.fderiv_apply {a : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneous μ) {p : (CoordinateSpace n × CoordinateSpace n) × ℂ} (hp : p.2 ∈ Λ)
    {t : ℝ} (ht : 0 < t) (htp : (parameterDilation n t p).2 ∈ Λ)
    (d : (CoordinateSpace n × CoordinateSpace n) × ℂ) :
    fderiv ℝ a.coefficient (parameterDilation n t p) (parameterDilation n t d) =
      t ^ μ • fderiv ℝ a.coefficient p d := by
  set D := parameterDilation n t
  have hD : Continuous fun q : (CoordinateSpace n × CoordinateSpace n) × ℂ => (D q).2 :=
    continuous_snd.comp D.continuous
  have heq : (a.coefficient ∘ D) =ᶠ[𝓝 p] fun q => t ^ μ • a.coefficient q := by
    filter_upwards [(Λ.isOpen.preimage continuous_snd).mem_nhds hp,
      (Λ.isOpen.preimage hD).mem_nhds htp] with q hq hDq
    exact ha q hq t ht hDq
  have hchain := ((a.differentiableAt_coefficient htp).hasFDerivAt.comp p D.hasFDerivAt).fderiv
  rw [← ContinuousLinearMap.comp_apply, ← hchain, heq.fderiv_eq,
    fderiv_fun_const_smul (a.differentiableAt_coefficient hp), smul_apply]

/-- A position derivative of a quasi-homogeneous symbol is quasi-homogeneous of the same
degree. -/
theorem IsQuasiHomogeneous.spatialDeriv {a : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneous μ) (v : CoordinateSpace n) :
    (a.spatialDeriv v).IsQuasiHomogeneous μ := by
  refine isQuasiHomogeneous_iff.2 fun x ξ z hz t ht htz => ?_
  have h := ha.fderiv_apply (p := ((x, ξ), z)) hz ht (by simpa using htz) ((v, 0), 0)
  simp only [parameterDilation_apply, smul_zero] at h
  rw [coefficient_spatialDeriv_eq_fderiv a v x _ htz, coefficient_spatialDeriv_eq_fderiv a v x ξ hz,
    h]

/-- A frequency derivative of a quasi-homogeneous symbol of degree `μ` is quasi-homogeneous of
degree `μ - 1`. -/
theorem IsQuasiHomogeneous.frequencyDeriv {a : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneous μ) (w : CoordinateSpace n) :
    (a.frequencyDeriv w).IsQuasiHomogeneous (μ - 1) := by
  refine isQuasiHomogeneous_iff.2 fun x ξ z hz t ht htz => ?_
  have h := ha.fderiv_apply (p := ((x, ξ), z)) hz ht (by simpa using htz) ((0, w), 0)
  have hd : (((0, t • w), (t ^ 2 : ℝ) • (0 : ℂ)) : (CoordinateSpace n × CoordinateSpace n) × ℂ) =
      t • ((0, w), 0) := by
    simp
  simp only [parameterDilation_apply, hd, ContinuousLinearMap.map_smul] at h
  rw [coefficient_frequencyDeriv_eq_fderiv a w x _ htz,
    coefficient_frequencyDeriv_eq_fderiv a w x ξ hz]
  refine smul_right_injective _ ht.ne' ?_
  beta_reduce
  rw [h, smul_smul, Real.rpow_sub_one ht.ne', mul_div_cancel₀ _ ht.ne']

/-- A quasi-homogeneous function of degree `m` is a quasi-homogeneous symbol of degree `m`. -/
theorem isQuasiHomogeneous_ofQuasiHomogeneous
    (f : (CoordinateSpace n × CoordinateSpace n) × ℂ → V →L[ℂ] W) (hf : ContDiff ℝ ∞ f)
    (hhom : ∀ t : ℝ, 0 < t → ∀ p, f (parameterDilation n t p) = t ^ m • f p) :
    (ofQuasiHomogeneous f hf hhom : ParameterSymbol n Λ V W m).IsQuasiHomogeneous m :=
  isQuasiHomogeneous_iff.2 fun x ξ z hz t ht htz => by
    rw [coefficient_ofQuasiHomogeneous f hf hhom x _ htz,
      coefficient_ofQuasiHomogeneous f hf hhom x ξ hz, ← hhom t ht, parameterDilation_apply]

/-- The spectral parameter is quasi-homogeneous of degree `2`. -/
theorem isQuasiHomogeneous_spectralParameter :
    (spectralParameter V : ParameterSymbol n Λ V V 2).IsQuasiHomogeneous 2 :=
  isQuasiHomogeneous_iff.2 fun x ξ z hz t _ htz => by
    rw [coefficient_spectralParameter x _ htz, coefficient_spectralParameter x ξ hz, ← smul_assoc,
      Real.rpow_two]

/-- The symbol `‖ξ‖² - z` of `-Δ - z` is quasi-homogeneous of degree `2` under
`(ξ, z) ↦ (t ξ, t² z)`; hence so is its inverse, the principal resolvent symbol `(‖ξ‖² - z)⁻¹`, of
degree `-2`. -/
theorem isQuasiHomogeneous_shiftedLaplacian_zero :
    (shiftedLaplacian V 0 : ParameterSymbol n Λ V V 2).IsQuasiHomogeneous 2 := by
  refine isQuasiHomogeneous_iff.2 fun x ξ z hz t ht htz => ?_
  rw [coefficient_shiftedLaplacian 0 x _ htz, coefficient_shiftedLaplacian 0 x ξ hz,
    ← smul_assoc]
  congr 1
  simp only [zero_add, norm_smul, Real.norm_eq_abs, abs_of_pos ht, mul_pow, Real.rpow_two,
    Complex.real_smul]
  push_cast
  ring

/-! ### Quasi-homogeneity at large frequencies -/

/-- A parameter-dependent symbol is *quasi-homogeneous of degree `μ` above the radius `R`* if
`a((x, t ξ), t² z) = t ^ μ a((x, ξ), z)` for every `t ≥ 1` and every frequency `ξ` of norm at least
`R` such that both `z` and `t² z` lie in `Λ`
(`TauCeti.ParameterSymbol.isQuasiHomogeneousAbove_iff`).
A quasi-homogeneous symbol of negative degree is singular at `(ξ, z) = (0, 0)`, so a smooth symbol
whose set of spectral parameters contains `0` can only be quasi-homogeneous away from it; the terms
of Seeley's resolvent parametrix are cut off near the origin in this way. Integrated along the
spectral parameter, such symbols become homogeneous symbols at large frequencies
(`TauCeti.ParameterSymbol.IsQuasiHomogeneousAbove.isHomogeneousAbove_balakrishnanIntegral`). -/
def IsQuasiHomogeneousAbove (a : ParameterSymbol n Λ V W m) (μ R : ℝ) : Prop :=
  ∀ x ξ, R ≤ ‖ξ‖ → ∀ z ∈ Λ, ∀ t : ℝ, 1 ≤ t → (t ^ 2 : ℝ) • z ∈ Λ →
    a.coefficient ((x, t • ξ), (t ^ 2 : ℝ) • z) = t ^ μ • a.coefficient ((x, ξ), z)

variable {R R' : ℝ}

theorem isQuasiHomogeneousAbove_iff {a : ParameterSymbol n Λ V W m} :
    a.IsQuasiHomogeneousAbove μ R ↔ ∀ x ξ, R ≤ ‖ξ‖ → ∀ z ∈ Λ, ∀ t : ℝ, 1 ≤ t →
      (t ^ 2 : ℝ) • z ∈ Λ →
        a.coefficient ((x, t • ξ), (t ^ 2 : ℝ) • z) = t ^ μ • a.coefficient ((x, ξ), z) :=
  Iff.rfl

/-- A quasi-homogeneous symbol is quasi-homogeneous above every radius. -/
theorem IsQuasiHomogeneous.isQuasiHomogeneousAbove {a : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneous μ) (R : ℝ) : a.IsQuasiHomogeneousAbove μ R :=
  fun x ξ _ z hz t ht htz => isQuasiHomogeneous_iff.1 ha x ξ z hz t (zero_lt_one.trans_le ht) htz

theorem IsQuasiHomogeneousAbove.mono {a : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneousAbove μ R) (h : R ≤ R') : a.IsQuasiHomogeneousAbove μ R' :=
  fun x ξ hξ => ha x ξ (h.trans hξ)

@[simp]
theorem isQuasiHomogeneousAbove_zero :
    (0 : ParameterSymbol n Λ V W m).IsQuasiHomogeneousAbove μ R :=
  fun _ _ _ _ _ _ _ _ => by simp

theorem IsQuasiHomogeneousAbove.add {a b : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneousAbove μ R) (hb : b.IsQuasiHomogeneousAbove μ R) :
    (a + b).IsQuasiHomogeneousAbove μ R := fun x ξ hξ z hz t ht htz => by
  rw [coefficient_add, Pi.add_apply, Pi.add_apply, ha x ξ hξ z hz t ht htz,
    hb x ξ hξ z hz t ht htz, smul_add]

theorem IsQuasiHomogeneousAbove.smul {a : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneousAbove μ R) (c : ℂ) : (c • a).IsQuasiHomogeneousAbove μ R :=
  fun x ξ hξ z hz t ht htz => by
    rw [coefficient_smul, Pi.smul_apply, Pi.smul_apply, ha x ξ hξ z hz t ht htz, smul_comm]

@[simp]
theorem isQuasiHomogeneousAbove_neg_iff {a : ParameterSymbol n Λ V W m} :
    (-a).IsQuasiHomogeneousAbove μ R ↔ a.IsQuasiHomogeneousAbove μ R := by
  simp only [isQuasiHomogeneousAbove_iff, coefficient_neg, Pi.neg_apply, smul_neg, neg_inj]

theorem IsQuasiHomogeneousAbove.neg {a : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneousAbove μ R) : (-a).IsQuasiHomogeneousAbove μ R :=
  isQuasiHomogeneousAbove_neg_iff.2 ha

theorem IsQuasiHomogeneousAbove.sub {a b : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneousAbove μ R) (hb : b.IsQuasiHomogeneousAbove μ R) :
    (a - b).IsQuasiHomogeneousAbove μ R := by
  simpa only [sub_eq_add_neg] using ha.add hb.neg

@[simp]
theorem isQuasiHomogeneousAbove_inclusion_iff {a : ParameterSymbol n Λ V W m} (h : m ≤ m') :
    (inclusion h a).IsQuasiHomogeneousAbove μ R ↔ a.IsQuasiHomogeneousAbove μ R := by
  simp only [isQuasiHomogeneousAbove_iff, coefficient_inclusion]

theorem IsQuasiHomogeneousAbove.inclusion {a : ParameterSymbol n Λ V W m}
    (ha : a.IsQuasiHomogeneousAbove μ R) (h : m ≤ m') :
    (inclusion h a).IsQuasiHomogeneousAbove μ R :=
  (isQuasiHomogeneousAbove_inclusion_iff h).2 ha

/-- The pointwise composition of symbols quasi-homogeneous of degrees `μ'` and `μ` above the radius
`R` is quasi-homogeneous of degree `μ' + μ` above `R`. -/
theorem IsQuasiHomogeneousAbove.comp {b : ParameterSymbol n Λ W U m'}
    {a : ParameterSymbol n Λ V W m} (hb : b.IsQuasiHomogeneousAbove μ' R)
    (ha : a.IsQuasiHomogeneousAbove μ R) : (b.comp a).IsQuasiHomogeneousAbove (μ' + μ) R :=
  fun x ξ hξ z hz t ht htz => by
    simp only [coefficient_comp, hb x ξ hξ z hz t ht htz, ha x ξ hξ z hz t ht htz,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, smul_smul,
      Real.rpow_add (zero_lt_one.trans_le ht), mul_comm]

end ParameterSymbol

end TauCeti
