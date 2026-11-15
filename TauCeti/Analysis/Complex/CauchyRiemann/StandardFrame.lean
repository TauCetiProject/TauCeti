/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.Weak
public import TauCeti.Analysis.Complex.Wirtinger.Similarity.Transported
public import Mathlib.Analysis.Normed.Ring.Units
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Sobolev.Local.ChainRule
import TauCeti.Analysis.Sobolev.Local.Multiplication

/-!
# Reducing a variable complex structure to the standard one

Let `V` be a complex Banach space and `J : ℂ → V →L[ℝ] V` a field of real-linear maps with
`J² = -1`. The vector similarity principle (McDuff–Salamon, Theorem 2.3.5)
asks for a family `Φ` of real-linear automorphisms with `Φ⁻¹ J Φ = i` and the regularity of `J`.
This file builds such a frame near a point `z₀` and shows that it turns the weak linear
Cauchy–Riemann equation `∂ₛξ + J ∂ₜξ + C ξ = 0` into an equation for `η = Φ⁻¹ ξ` with the
constant structure `i`.

* At one point, a real-linear automorphism `Φ₁` with `J(z₀) Φ₁ = Φ₁ i` is an input; in finite
  dimension one exists by `ContinuousLinearMap.exists_continuousLinearEquiv_comp_eq_comp_I_smul`.
* The frame `Φ(z) = ½(1 - J(z) J(z₀)) Φ₁` satisfies `J(z) Φ(z) = Φ(z) i` wherever `J(z)² = -1`,
  since `J(z)(1 - J(z) J(z₀)) = J(z) + J(z₀) = (1 - J(z) J(z₀)) J(z₀)`. It equals `Φ₁` at `z₀`,
  so it is invertible near `z₀` when `J` is continuous, and it is an affine function of `J`, so it
  lies in `W^{1,p}_loc` with `J`. Its pointwise inverse is in `W^{1,p}_loc` as well, by the chain
  rule for the inverse of a normed algebra.
* For `V` finite-dimensional, where the weak Leibniz rule is available, and any continuous
  invertible frame `Φ ∈ W^{1,p}_loc` with `J Φ = Φ i`, `p > 2`, the map `ξ` solves the equation
  for `J` and `C` exactly when `η = Φ⁻¹ ξ` solves it for `i` and `C' = Φ⁻¹((∂ₛΦ + J ∂ₜΦ) + C Φ)`.
  Expanding `ξ = Φ η` by the Leibniz rule gives `∂ₛξ + J ∂ₜξ + C ξ = Φ(∂ₛη + i ∂ₜη + C' η)`. The
  coefficient `C'` is locally `Lᵖ` exactly when `C` is.

So a local similarity factorization of `η` for the structure `i` gives one of `ξ = Φ η`
(`TauCeti.HasSimilarityFactorizationAt.clm_apply`), and unique continuation and the zero orders
for a variable `J` reduce to the case `J = i`.

## Main declarations

* `TauCeti.standardFrame`: the frame `½(1 - J(z) J(z₀)) Φ₁`.
* `TauCeti.comp_standardFrame`: `J(z) Φ(z) = Φ(z) i`.
* `TauCeti.exists_ball_isUnit_standardFrame`, `TauCeti.memWkpLoc_standardFrame`,
  `TauCeti.memWkpLoc_ring_inverse_standardFrame`: invertibility near `z₀` and Sobolev regularity
  of the frame and its inverse.
* `TauCeti.frameCoeff`: the coefficient `C' = Φ⁻¹((∂ₛΦ + J ∂ₜΦ) + C Φ)`, with
  `TauCeti.frameCoeff_apply`.
* `TauCeti.isWeakLinearCauchyRiemannOn_iff_frame`: the reduction for any frame, and
  `TauCeti.isWeakLinearCauchyRiemannOn_iff_standardFrame` for the standard frame.
* `TauCeti.memLpLoc_frameCoeff_iff`: `C'` is locally `Lᵖ` exactly when `C` is.
* `TauCeti.commute_symm_comp_standardFrame_transportedComplexStructure`: for `J = Ψ i Ψ⁻¹`, the
  standard frame is `Ψ` composed with a real-linear map commuting with `i`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Section 2.3 (Theorem 2.3.5).
-/

public noncomputable section

open Complex ContinuousLinearMap MeasureTheory Metric Set Filter TopologicalSpace
open scoped NNReal ENNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

/-! ### The standard frame -/

/-- The frame `Φ(z) = ½(1 - J(z) J(z₀)) Φ₁`, for a field `J` of real-linear maps, a base point
`z₀` and a real-linear automorphism `Φ₁`, intended with `J(z₀) Φ₁ = Φ₁ i`. Where `J(z)² = -1` it
satisfies `J(z) Φ(z) = Φ(z) i` (`TauCeti.comp_standardFrame`); it equals `Φ₁` at `z₀`; and it is
an affine function of `J(z)`, so as regular as `J`. -/
def standardFrame (J : ℂ → V →L[ℝ] V) (z₀ : ℂ) (Φ₁ : V ≃L[ℝ] V) (z : ℂ) : V →L[ℝ] V :=
  ((2 : ℝ)⁻¹ • (1 - J z ∘L J z₀)) ∘L (Φ₁ : V →L[ℝ] V)

variable {J : ℂ → V →L[ℝ] V} {z₀ z : ℂ} {Φ₁ : V ≃L[ℝ] V}

omit [CompleteSpace V] in
/-- `Φ(z) v = ½(Φ₁ v - J(z) J(z₀) Φ₁ v)`. -/
theorem standardFrame_apply (v : V) :
    standardFrame J z₀ Φ₁ z v = (2 : ℝ)⁻¹ • (Φ₁ v - J z (J z₀ (Φ₁ v))) := by
  simp [standardFrame]

omit [CompleteSpace V] in
/-- **The intertwining identity** `J(z) Φ(z) = Φ(z) i`, wherever `J(z)² = -1`, given
`J(z₀)² = -1` and `J(z₀) Φ₁ = Φ₁ i`. Both sides are `½(J(z) + J(z₀)) Φ₁`. -/
theorem comp_standardFrame (hz : J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h₀ : J z₀ ∘L J z₀ = -ContinuousLinearMap.id ℝ V)
    (hΦ₁ : J z₀ ∘L (Φ₁ : V →L[ℝ] V) = (Φ₁ : V →L[ℝ] V) ∘L (I • ContinuousLinearMap.id ℝ V)) :
    J z ∘L standardFrame J z₀ Φ₁ z =
      standardFrame J z₀ Φ₁ z ∘L (I • ContinuousLinearMap.id ℝ V) := by
  have hz' (v : V) : J z (J z v) = -v := congr($hz v)
  have h₀' (v : V) : J z₀ (J z₀ v) = -v := congr($h₀ v)
  have hΦ₁' (v : V) : Φ₁ (I • v) = J z₀ (Φ₁ v) := (congr($hΦ₁ v)).symm
  ext v
  simp only [comp_apply, standardFrame_apply, smul_apply, id_apply, hΦ₁', map_smul, map_sub, hz',
    h₀', map_neg, sub_neg_eq_add, add_comm]

omit [CompleteSpace V] in
/-- The standard frame equals `Φ₁` at the base point. -/
theorem standardFrame_self (h₀ : J z₀ ∘L J z₀ = -ContinuousLinearMap.id ℝ V) :
    standardFrame J z₀ Φ₁ z₀ = Φ₁ := by
  have h₀' (v : V) : J z₀ (J z₀ v) = -v := congr($h₀ v)
  ext v
  rw [standardFrame_apply, h₀', sub_neg_eq_add, ← two_smul ℝ, smul_smul,
    inv_mul_cancel₀ two_ne_zero, one_smul, ContinuousLinearEquiv.coe_coe]

omit [CompleteSpace V] in
/-- The standard frame is invertible at the base point. -/
theorem isUnit_standardFrame_self (h₀ : J z₀ ∘L J z₀ = -ContinuousLinearMap.id ℝ V) :
    IsUnit (standardFrame J z₀ Φ₁ z₀) := by
  rw [standardFrame_self h₀]
  exact Φ₁.toUnit.isUnit

omit [CompleteSpace V] in
/-- The standard frame is continuous where `J` is. -/
theorem continuousOn_standardFrame {U : Set ℂ} (hJ : ContinuousOn J U) :
    ContinuousOn (standardFrame J z₀ Φ₁) U :=
  ((continuousOn_const.sub (hJ.clm_comp continuousOn_const)).const_smul ((2 : ℝ)⁻¹)).clm_comp
    (continuousOn_const (c := (Φ₁ : V →L[ℝ] V)))

/-- **Invertibility near the base point.** For `J` continuous on an open set `Ω ∋ z₀` with
`J(z₀)² = -1`, the standard frame is invertible on a disc about `z₀` inside `Ω`. -/
theorem exists_ball_isUnit_standardFrame {Ω : Set ℂ} (hΩ : IsOpen Ω) (hz₀ : z₀ ∈ Ω)
    (hJ : ContinuousOn J Ω) (h₀ : J z₀ ∘L J z₀ = -ContinuousLinearMap.id ℝ V) :
    ∃ r > 0, ball z₀ r ⊆ Ω ∧ ∀ z ∈ ball z₀ r, IsUnit (standardFrame J z₀ Φ₁ z) := by
  have hc : ContinuousAt (standardFrame J z₀ Φ₁) z₀ :=
    (continuousOn_standardFrame hJ).continuousAt (hΩ.mem_nhds hz₀)
  have hu := hc.preimage_mem_nhds (Units.isOpen.mem_nhds (isUnit_standardFrame_self h₀))
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.1 (inter_mem hu (hΩ.mem_nhds hz₀))
  exact ⟨r, hr, fun z hz => (hrs hz).2, fun z hz => (hrs hz).1⟩

/-- **Sobolev regularity of the frame.** The standard frame lies in `W^{1,p}_loc` with `J`, being
an affine function of `J`. -/
theorem memWkpLoc_standardFrame {p : ℝ≥0∞} {U : Set ℂ} (hJ : MemWkpLoc p U 1 J) :
    MemWkpLoc p U 1 (standardFrame J z₀ Φ₁) := by
  have h : standardFrame J z₀ Φ₁ = fun z => (2 : ℝ)⁻¹ • (Φ₁ : V →L[ℝ] V) +
      (-(2 : ℝ)⁻¹ • (compL ℝ V V V).flip (J z₀ ∘L (Φ₁ : V →L[ℝ] V))) (J z) := by
    ext z v
    simp [standardFrame_apply, sub_eq_add_neg]
  rw [h]
  exact (memWkpLoc_const (F := V →L[ℝ] V) _).add (hJ.clm_comp _)

/-- **Sobolev regularity of the inverse frame.** Where the standard frame is invertible, its
pointwise inverse lies in `W^{1,p}_loc` with `J`. -/
theorem memWkpLoc_ring_inverse_standardFrame {p : ℝ≥0∞} {U : Set ℂ} (hJ : MemWkpLoc p U 1 J)
    (hJc : ContinuousOn J U) (hu : ∀ z ∈ U, IsUnit (standardFrame J z₀ Φ₁ z)) :
    MemWkpLoc p U 1 (fun z => Ring.inverse (standardFrame J z₀ Φ₁ z)) :=
  (memWkpLoc_standardFrame hJ).ring_inverse (continuousOn_standardFrame hJc) hu

/-! ### The reduction to the standard structure -/

/-- The coefficient `C' = Φ⁻¹((∂ₛΦ + J ∂ₜΦ) + C Φ)` of the equation satisfied by `η = Φ⁻¹ ξ`,
for a frame `Φ` with derivative `DΦ`. -/
def frameCoeff (J C Φ : ℂ → V →L[ℝ] V) (DΦ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (z : ℂ) : V →L[ℝ] V :=
  Ring.inverse (Φ z) ∘L ((DΦ z 1 + J z ∘L DΦ z I) + C z ∘L Φ z)

variable {p : ℝ≥0} {Ω : Opens ℂ} {C Φ : ℂ → V →L[ℝ] V} {DΦ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ : ℂ → V}

omit [CompleteSpace V] in
/-- The defining formula `C' = Φ⁻¹((∂ₛΦ + J ∂ₜΦ) + C Φ)` of `TauCeti.frameCoeff`. -/
theorem frameCoeff_def :
    frameCoeff J C Φ DΦ z = Ring.inverse (Φ z) ∘L ((DΦ z 1 + J z ∘L DΦ z I) + C z ∘L Φ z) := by
  rw [frameCoeff]

omit [CompleteSpace V] in
/-- `C' v = Φ⁻¹(∂ₛΦ v + J ∂ₜΦ v + C Φ v)`. -/
theorem frameCoeff_apply (v : V) :
    frameCoeff J C Φ DΦ z v =
      Ring.inverse (Φ z) (DΦ z 1 v + J z (DΦ z I v) + C z (Φ z v)) := by
  simp [frameCoeff]

omit [CompleteSpace V] in
/-- The pointwise identity behind the reduction: for `ξ = Φ η` with `J Φ = Φ i`,
`∂ₛξ + J ∂ₜξ + C ξ = Φ(∂ₛη + i ∂ₜη + C' η)`, written for the values `a = ∂ₛη`, `b = ∂ₜη` and
`w = η`. -/
private theorem add_frame_eq (hu : IsUnit (Φ z))
    (hJ : J z ∘L Φ z = Φ z ∘L (I • ContinuousLinearMap.id ℝ V)) (a b w : V) :
    (DΦ z 1 w + Φ z a) + J z (DΦ z I w + Φ z b) + C z (Φ z w) =
      Φ z (a + I • b + frameCoeff J C Φ DΦ z w) := by
  have hJ' (v : V) : J z (Φ z v) = Φ z (I • v) := by simpa using congr($hJ v)
  have hinv (v : V) : Φ z (Ring.inverse (Φ z) v) = v := by
    simpa using congr($(Ring.mul_inverse_cancel _ hu) v)
  simp only [frameCoeff_apply, map_add, hinv, hJ']
  abel

/-- **Reduction to the standard structure.** Let `V` be finite-dimensional, as the weak Leibniz
rule requires, let `p > 2` and let `Φ` be a continuous family of real-linear automorphisms on an
open set `Ω`, with weak derivative `DΦ ∈ Lᵖ_loc` and `J Φ = Φ i` on `Ω`. Then `ξ` solves
`∂ₛξ + J ∂ₜξ + C ξ = 0` weakly on `Ω` exactly when `η = Φ⁻¹ ξ` solves `∂ₛη + i ∂ₜη + C' η = 0`
with `C' = Φ⁻¹((∂ₛΦ + J ∂ₜΦ) + C Φ)`. -/
theorem isWeakLinearCauchyRiemannOn_iff_frame [FiniteDimensional ℂ V] (hp : 2 < p)
    (hΦc : ContinuousOn Φ Ω) (hΦ : HasWeakFDerivOn volume Ω Φ DΦ) (hDΦ : MemLpLoc p Ω DΦ)
    (hu : ∀ z ∈ Ω, IsUnit (Φ z))
    (hJ : ∀ z ∈ Ω, J z ∘L Φ z = Φ z ∘L (I • ContinuousLinearMap.id ℝ V)) :
    IsWeakLinearCauchyRiemannOn p Ω J C ξ ↔
      IsWeakLinearCauchyRiemannOn p Ω (fun _ => I • ContinuousLinearMap.id ℝ V)
        (frameCoeff J C Φ DΦ) (fun z => Ring.inverse (Φ z) (ξ z)) := by
  have hp1 : 1 < p := one_lt_two.trans hp
  have hΩm : MeasurableSet (Ω : Set ℂ) := Ω.isOpen.measurableSet
  have hΦw : MemWkpLoc p Ω 1 Φ :=
    memWkpLoc_succ_iff_of_isOpen.2 ⟨hΦc.memLpLoc, DΦ, hΦ, memWkpLoc_zero_iff.2 hDΦ⟩
  have hΨw := hΦw.ring_inverse hΦc hu
  have hΨc : ContinuousOn (fun z => Ring.inverse (Φ z)) Ω := fun z hz => by
    have h := NormedRing.inverse_continuousAt (hu z hz).unit
    rw [IsUnit.unit_spec] at h
    exact h.comp_continuousWithinAt (hΦc z hz)
  have hinv (z : ℂ) (hz : z ∈ (Ω : Set ℂ)) (v : V) : Φ z (Ring.inverse (Φ z) v) = v := by
    simpa using congr($(Ring.mul_inverse_cancel _ (hu z hz)) v)
  have hinv' (z : ℂ) (hz : z ∈ (Ω : Set ℂ)) (v : V) : Ring.inverse (Φ z) (Φ z v) = v := by
    simpa using congr($(Ring.inverse_mul_cancel _ (hu z hz)) v)
  have hξη : (fun z => Φ z (Ring.inverse (Φ z) (ξ z))) =ᵐ[volume.restrict (Ω : Set ℂ)] ξ :=
    (ae_restrict_iff' hΩm).2 (Eventually.of_forall fun z hz => hinv z hz (ξ z))
  -- The Leibniz rule for `Φ η`, and the pointwise identity in terms of its derivative.
  let B := ContinuousLinearMap.id ℝ (V →L[ℝ] V)
  have hleib {η : ℂ → V} {Dη : ℂ → ℂ →L[ℝ] V} (hη : HasWeakFDerivOn volume Ω η Dη)
      (hηp : MemLpLoc p Ω η) (hDηp : MemLpLoc p Ω Dη) :
      HasWeakFDerivOn volume Ω (fun z => Φ z (η z))
        (fun z => B.precompL ℂ (DΦ z) (η z) + B.precompR ℂ (Φ z) (Dη z)) :=
    hΦ.bilin_of_memLpLoc B hp hp1 le_rfl hΦc.memLpLoc hDΦ hη hηp hDηp
  have halg (z : ℂ) (hz : z ∈ (Ω : Set ℂ)) (Dη : ℂ →L[ℝ] V) (w : V) :
      (B.precompL ℂ (DΦ z) w + B.precompR ℂ (Φ z) Dη) 1 +
          J z ((B.precompL ℂ (DΦ z) w + B.precompR ℂ (Φ z) Dη) I) + C z (Φ z w) =
        Φ z (Dη 1 + I • Dη I + frameCoeff J C Φ DΦ z w) := by
    simpa [B] using add_frame_eq (C := C) (DΦ := DΦ) (hu z hz) (hJ z hz) (Dη 1) (Dη I) w
  rw [isWeakLinearCauchyRiemannOn_iff_of_isOpen, isWeakLinearCauchyRiemannOn_iff_of_isOpen]
  constructor
  · rintro ⟨hξc, hξp, Dξ, hDξ, hDξp, hae⟩
    have hξw : MemWkpLoc p Ω 1 ξ :=
      memWkpLoc_succ_iff_of_isOpen.2 ⟨hξp, Dξ, hDξ, memWkpLoc_zero_iff.2 hDξp⟩
    have hηw : MemWkpLoc p Ω 1 (fun z => Ring.inverse (Φ z) (ξ z)) :=
      hΨw.bilin B hp hp1 le_rfl hξw
    obtain ⟨Dη, hDη, hDηp⟩ := hηw.exists_weakFDeriv_of_isOpen
    rw [memWkpLoc_zero_iff] at hDηp
    have hηc : ContinuousOn (fun z => Ring.inverse (Φ z) (ξ z)) Ω := hΨc.clm_apply hξc
    refine ⟨hηc, hηc.memLpLoc, Dη, hDη, hDηp, ?_⟩
    have hL := (hleib hDη hηc.memLpLoc hDηp).congr_ae hξη
    filter_upwards [ae_restrict_mem hΩm, hDξ.ae_eq hL, hae] with z hz hDz hz'
    have h := halg z hz (Dη z) (Ring.inverse (Φ z) (ξ z))
    rw [hinv z hz] at h
    rw [hDz, h] at hz'
    simpa [hinv' z hz] using congrArg (⇑(Ring.inverse (Φ z))) hz'
  · rintro ⟨hηc, hηp, Dη, hDη, hDηp, hae⟩
    have hξc : ContinuousOn ξ Ω :=
      (hΦc.clm_apply hηc).congr fun z hz => (hinv z hz (ξ z)).symm
    have hL := (hleib hDη hηp hDηp).congr_ae hξη
    have hηw : MemWkpLoc p Ω 1 (fun z => Ring.inverse (Φ z) (ξ z)) :=
      memWkpLoc_succ_iff_of_isOpen.2 ⟨hηp, Dη, hDη, memWkpLoc_zero_iff.2 hDηp⟩
    have hξw : MemWkpLoc p Ω 1 ξ := (hΦw.bilin B hp hp1 le_rfl hηw).congr_ae hξη
    refine ⟨hξc, hξc.memLpLoc, _, hL, hξw.memLpLoc_of_hasWeakFDerivOn hL, ?_⟩
    filter_upwards [ae_restrict_mem hΩm, hae] with z hz hz'
    have h := halg z hz (Dη z) (Ring.inverse (Φ z) (ξ z))
    rw [hinv z hz] at h
    simp only [smul_apply, id_apply] at hz'
    rw [h, hz', map_zero]

/-- **Integrability of the new coefficient.** For a frame `Φ` continuous and invertible on a
measurable set `U`, with `DΦ` locally `Lᵖ` and `J` continuous on `U`, the coefficient
`C' = Φ⁻¹((∂ₛΦ + J ∂ₜΦ) + C Φ)` is locally `Lᵖ` on `U` exactly when `C` is. -/
theorem memLpLoc_frameCoeff_iff {q : ℝ≥0∞} {U : Set ℂ} (hU : MeasurableSet U)
    (hΦc : ContinuousOn Φ U) (hDΦ : MemLpLoc q U DΦ) (hu : ∀ z ∈ U, IsUnit (Φ z))
    (hJc : ContinuousOn J U) :
    MemLpLoc q U (frameCoeff J C Φ DΦ) ↔ MemLpLoc q U C := by
  have hΨc : ContinuousOn (fun z => Ring.inverse (Φ z)) U := fun z hz => by
    have h := NormedRing.inverse_continuousAt (hu z hz).unit
    rw [IsUnit.unit_spec] at h
    exact h.comp_continuousWithinAt (hΦc z hz)
  have h1 : MemLpLoc q U (fun z => DΦ z 1) := by
    simpa using hDΦ.clm_comp (apply ℝ (V →L[ℝ] V) (1 : ℂ))
  have hI : MemLpLoc q U (fun z => DΦ z I) := by
    simpa using hDΦ.clm_comp (apply ℝ (V →L[ℝ] V) I)
  have hT : MemLpLoc q U (fun z => Ring.inverse (Φ z) ∘L (DΦ z 1 + J z ∘L DΦ z I)) :=
    (h1.add (hI.continuousOn_clm_comp hJc)).continuousOn_clm_comp hΨc
  have hsplit : frameCoeff J C Φ DΦ = (fun z => Ring.inverse (Φ z) ∘L
      (DΦ z 1 + J z ∘L DΦ z I)) + fun z => Ring.inverse (Φ z) ∘L C z ∘L Φ z := by
    ext z v
    simp [frameCoeff_apply]
  constructor
  · intro h
    have hdiff : frameCoeff J C Φ DΦ -
        (fun z => Ring.inverse (Φ z) ∘L (DΦ z 1 + J z ∘L DΦ z I)) =
        fun z => Ring.inverse (Φ z) ∘L C z ∘L Φ z := by
      rw [hsplit, add_sub_cancel_left]
    have h' := ((hdiff ▸ h.sub hT).clm_comp_continuousOn hΨc).continuousOn_clm_comp hΦc
    refine h'.congr_ae ((ae_restrict_iff' hU).2 (Eventually.of_forall fun z hz => ?_))
    have hinv (v : V) : Φ z (Ring.inverse (Φ z) v) = v := by
      simpa using congr($(Ring.mul_inverse_cancel _ (hu z hz)) v)
    ext v
    simp [hinv]
  · intro h
    rw [hsplit]
    exact hT.add ((h.clm_comp_continuousOn hΦc).continuousOn_clm_comp hΨc)

/-- **Reduction to the standard structure with the standard frame.** Let `V` be
finite-dimensional, let `p > 2`, let `J` be continuous on an open set `Ω` with `J² = -1` there,
and let `J(z₀)² = -1` and `J(z₀) Φ₁ = Φ₁ i`. Where the standard frame `Φ` is invertible on `Ω`,
with weak derivative `DΦ ∈ Lᵖ_loc` (which exists when `J ∈ W^{1,p}_loc`, by
`TauCeti.memWkpLoc_standardFrame`), `ξ` solves `∂ₛξ + J ∂ₜξ + C ξ = 0` weakly on `Ω` exactly when
`η = Φ⁻¹ ξ` solves `∂ₛη + i ∂ₜη + C' η = 0` with `C' = Φ⁻¹((∂ₛΦ + J ∂ₜΦ) + C Φ)`. -/
theorem isWeakLinearCauchyRiemannOn_iff_standardFrame [FiniteDimensional ℂ V]
    (hp : 2 < p) (hJc : ContinuousOn J Ω)
    (hJ : ∀ z ∈ Ω, J z ∘L J z = -ContinuousLinearMap.id ℝ V)
    (h₀ : J z₀ ∘L J z₀ = -ContinuousLinearMap.id ℝ V)
    (hΦ₁ : J z₀ ∘L (Φ₁ : V →L[ℝ] V) = (Φ₁ : V →L[ℝ] V) ∘L (I • ContinuousLinearMap.id ℝ V))
    (hu : ∀ z ∈ Ω, IsUnit (standardFrame J z₀ Φ₁ z))
    (hD : HasWeakFDerivOn volume Ω (standardFrame J z₀ Φ₁) DΦ) (hDp : MemLpLoc p Ω DΦ) :
    IsWeakLinearCauchyRiemannOn p Ω J C ξ ↔
      IsWeakLinearCauchyRiemannOn p Ω (fun _ => I • ContinuousLinearMap.id ℝ V)
        (frameCoeff J C (standardFrame J z₀ Φ₁) DΦ)
        (fun z => Ring.inverse (standardFrame J z₀ Φ₁ z) (ξ z)) :=
  isWeakLinearCauchyRiemannOn_iff_frame hp (continuousOn_standardFrame hJc) hD hDp hu
    fun z hz => comp_standardFrame (hJ z hz) h₀ hΦ₁

/-! ### Check: a transported structure -/

omit [CompleteSpace V] in
/-- **The transported structure.** For `J = Ψ i Ψ⁻¹` and any `Φ₁` with `J(z₀) Φ₁ = Φ₁ i`, for
instance `Φ₁ = Ψ(z₀)`, the standard frame is `Ψ` composed with a real-linear map commuting with
`i`, that is, a complex-linear map. Where the standard frame is invertible, so is that map, and the
frame of the reduction is then determined by `J` up to a complex-linear change of frame. -/
theorem commute_symm_comp_standardFrame_transportedComplexStructure {Ψ : ℂ → V ≃L[ℝ] V}
    (hΦ₁ : transportedComplexStructure Ψ z₀ ∘L (Φ₁ : V →L[ℝ] V) =
      (Φ₁ : V →L[ℝ] V) ∘L (I • ContinuousLinearMap.id ℝ V)) (z : ℂ) :
    Commute (I • ContinuousLinearMap.id ℝ V)
      (((Ψ z).symm : V →L[ℝ] V) ∘L standardFrame (transportedComplexStructure Ψ) z₀ Φ₁ z) := by
  have h := comp_standardFrame (transportedComplexStructure_comp_self z)
    (transportedComplexStructure_comp_self z₀) hΦ₁
  ext v
  have hv := congr($h v)
  simp only [comp_apply, transportedComplexStructure_apply, smul_apply, id_apply] at hv
  simp only [ContinuousLinearMap.mul_def, comp_apply, smul_apply, id_apply]
  rw [← hv, ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply]

end TauCeti
