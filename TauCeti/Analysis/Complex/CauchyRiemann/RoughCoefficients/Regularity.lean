/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HigherOrder.Basic
public import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Data.ENNReal.Inv

/-!
# `C^k`, `C^∞`, and normed-space interior regularity for Cauchy–Riemann equations

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and consider the real linear Cauchy–Riemann operator

`D ξ = ∂_s ξ + J ∂_t ξ + S ξ`

with Sobolev coefficients `J ∈ W^{max 1 k, p}_loc(Ω; V →L[ℝ] V)` satisfying `J² = -1` almost
everywhere on `Ω` and `S ∈ W^{k,p}_loc(Ω; V →L[ℝ] V)` for `2 < p ≤ ∞`.

Building on the higher-order interior regularity theorem `TauCeti.IsWeakCRSolution.memWkpLoc_succ`
of `TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.HigherOrder.Basic`, this file proves:

1. **`C^k` representatives for weak solutions**
   (`TauCeti.IsWeakCRSolution.exists_contDiffOn_ae_eq`). When `2 < r ≤ p`, `p⁻¹ + q⁻¹ < 1`, and
   `η ∈ W^{k,r}_loc(Ω)`, every weak solution `ξ ∈ L^q_loc(Ω)` agrees almost everywhere on `Ω` with
   a `C^k` map on `Ω`.
2. **Regularity on general finite-dimensional normed spaces**
   (`TauCeti.HasWeakFDerivOn.memWkpLoc_succ_of_ae_cauchyRiemann`,
   `TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ`,
   `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn`, and
   `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn_infty`). Transporting along a continuous linear
   equivalence to Euclidean space yields inhomogeneous `W^{k+1,r}_loc` regularity (`1 < r < ∞`,
   `r ≤ p`) directly from `HasWeakFDerivOn` (via `W^{1,1}_loc ⊆ L²_loc` and mollification of the
   continuous Morrey representative of `J`), as well as `W^{k+1,p}_loc`, `C^k`, and `C^∞`
   regularity for `TauCeti.IsWeakLinearCauchyRiemannOn` at every exponent `q : ℝ≥0∞`.

## Main declarations

* `TauCeti.IsWeakCRSolution.exists_contDiffOn_ae_eq`: `C^k` representative almost everywhere on `Ω`
  when `2 < r ≤ p` and `η ∈ W^{k,r}_loc(Ω)`.
* `TauCeti.HasWeakFDerivOn.memWkpLoc_succ_of_ae_cauchyRiemann`: inhomogeneous `W^{k+1,r}_loc`
  regularity of weakly differentiable solutions valued in any finite-dimensional real normed space.
* `TauCeti.IsWeakLinearCauchyRiemannOn.memWkpLoc_succ`,
  `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn`, and
  `TauCeti.IsWeakLinearCauchyRiemannOn.contDiffOn_infty`: `W^{k+1,p}_loc`, `C^k`, and `C^∞`
  regularity of continuous weak linear Cauchy–Riemann solutions valued in any finite-dimensional
  real normed space.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Proposition B.4.9).
-/

public noncomputable section

open Complex MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions ENNReal InnerProductSpace NNReal

namespace TauCeti

/-! ### `C^k` representatives for weak solutions -/

section HigherRegularity

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {p q r : ℝ≥0∞} {k : ℕ}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-- **Existence of a `C^k` representative.** Let `2 < r ≤ p` and `p⁻¹ + q⁻¹ < 1` (allowing `p = ∞`,
`r = ∞`, and `q = ∞`). If `J ∈ W^{max 1 k, p}_loc(Ω)` has weak derivative `DJ` with `J² = -1`
almost everywhere on `Ω`, `S ∈ W^{k,p}_loc(Ω)`, and `η ∈ W^{k,r}_loc(Ω)`, then every weak solution
`ξ ∈ L^q_loc(Ω)` agrees almost everywhere on `Ω` with a `C^k` map on `Ω`. -/
theorem IsWeakCRSolution.exists_contDiffOn_ae_eq
    (hr : 2 < r) (hrp : r ≤ p) (hpq : p⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc r Ω k η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    ∃ g : ℂ → V, ContDiffOn ℝ k g Ω ∧ ξ =ᵐ[volume.restrict Ω] g := by
  obtain ⟨r₀, hr₀, hr₀r⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hr
  have hc : IsSobolevCRCoefficients p Ω J DJ S :=
    IsSobolevCRCoefficients.of_memWkpLoc (hJ.of_le (le_max_left 1 k)) hDJ hS.memLpLoc
  exact (hsol.memWkpLoc_succ hc (hr.trans_le hrp) hJsq hpq
    ((by norm_num : (1 : ℝ≥0∞) < 2).trans hr₀) ENNReal.coe_ne_top (hr₀r.le.trans hrp)
    (hJ.of_le (le_max_right 1 k)) hS (hη.mono_exponent hr₀r.le)).exists_contDiffOn_ae_eq hr₀

end HigherRegularity

/-! ### Weak linear Cauchy–Riemann solutions in finite-dimensional normed spaces -/

section NormedSpace

section InnerProductHelper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- On a finite-dimensional real inner product space, any map `ξ` with weak derivative `Dξ` on `Ω`
satisfying `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω` for Sobolev coefficients at
exponent `2 < p ≤ ∞` lies in `L²_loc(Ω)` (via the two-dimensional embedding `W^{1,1}_loc ⊆ L²_loc`)
and satisfies `IsWeakCRSolution 2 Ω J DJ S ξ η`. -/
private theorem isWeakCRSolution_of_hasWeakFDerivOn_ae [FiniteDimensional ℝ E] {Ω : Opens ℂ}
    {p : ℝ≥0∞} (hp : 2 < p) {J S : ℂ → E →L[ℝ] E} {DJ : ℂ → ℂ →L[ℝ] E →L[ℝ] E}
    {ξ η : ℂ → E} {Dξ : ℂ → ℂ →L[ℝ] E}
    (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) (hη : LocallyIntegrableOn η Ω volume)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    IsWeakCRSolution 2 Ω J DJ S ξ η := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have hp2 : p⁻¹ + (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_add_inv_two_lt_one_iff.2 hp
  -- `HasWeakFDerivOn` places `ξ ∈ W^{1,1}_loc(Ω) ⊆ L²_loc(Ω)` via the 2D Sobolev embedding.
  have hξ1 : MemWkpLoc 1 Ω 1 ξ :=
    memWkpLoc_succ_iff_of_isOpen.2
      ⟨(memLpLoc_one_iff_locallyIntegrableOn hloc).2 hDξ.locallyIntegrableOn, Dξ, hDξ,
        memWkpLoc_zero_iff.2 ((memLpLoc_one_iff_locallyIntegrableOn hloc).2
          hDξ.locallyIntegrableOn_deriv)⟩
  have hξ2 : MemLpLoc 2 Ω ξ := hξ1.memLpLoc_two le_rfl
  -- Replace `J` by its continuous Morrey representative `J'`.
  have hJW1p : MemWkpLoc p Ω 1 J := memWkpLoc_succ_iff_of_isOpen.2
    ⟨hc.memLpLoc_coeff, DJ, hc.hasWeakFDerivOn, memWkpLoc_zero_iff.2 hc.memLpLoc_deriv⟩
  set J' := TauCeti.MeasureTheory.preciseRepresentative volume J
  have hJ'cont : ContinuousOn J' Ω := hJW1p.continuousOn_preciseRepresentative hp
  have hJJ' : J =ᵐ[volume.restrict Ω] J' := hc.memLpLoc_coeff.ae_eq_preciseRepresentative hp1
  have hc' : IsSobolevCRCoefficients p Ω J' DJ S :=
    ⟨hc.hasWeakFDerivOn.congr_ae hJJ', hc.memLpLoc_coeff.congr_ae hJJ',
      hc.memLpLoc_deriv, hc.memLpLoc_zeroth⟩
  have heq' : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J' z (Dξ z I) + S z (ξ z) = η z := by
    filter_upwards [heq, hJJ'] with z hz hJ using by rwa [← hJ]
  have hDξ1 : LocallyIntegrableOn (fun z => Dξ z 1) Ω :=
    (hDξ.hasWeakLineDerivOn 1).locallyIntegrableOn_deriv
  have hJ'DξI : LocallyIntegrableOn (fun z => J' z (Dξ z I)) Ω :=
    (hDξ.hasWeakLineDerivOn I).locallyIntegrableOn_deriv.continuousOn_clm_apply hloc hJ'cont
  have hJ'ξ : HasWeakLineDerivOn volume Ω (fun z => J' z (ξ z))
      (fun z => DJ z I (ξ z) + J' z (Dξ z I)) I := by
    simpa only [ContinuousLinearMap.id_apply] using
      (hc'.hasWeakFDerivOn.hasWeakLineDerivOn I).bilin_of_continuousOn
        (ContinuousLinearMap.id ℝ (E →L[ℝ] E)) hp2.le hJ'cont
        (hc'.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) I))
        (hDξ.hasWeakLineDerivOn I) hξ2
  exact (isWeakCRSolution_congr_ae hJJ' .rfl .rfl .rfl .rfl).2 <|
    (hc'.isWeakCRSolution_iff_ae_of_hasWeakLineDerivOn hp2.le hDξ hξ2 hJ'ξ hDξ1 hJ'DξI hη).2 heq'

end InnerProductHelper

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {p q r : ℝ≥0∞} {k : ℕ} {J S : ℂ → V →L[ℝ] V} {ξ η : ℂ → V}

/-- **Inhomogeneous interior Sobolev regularity on a finite-dimensional real normed space.** Let
`2 < p ≤ ∞`, `1 < r < ∞`, and `r ≤ p`. If `J ∈ W^{max 1 k, p}_loc(Ω)` with `J² = -1` almost
everywhere on `Ω`, `S ∈ W^{k,p}_loc(Ω)`, `η ∈ W^{k,r}_loc(Ω)`, and `ξ` has weak derivative `Dξ` on
`Ω` satisfying `Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z` almost everywhere on `Ω`, then
`ξ ∈ W^{k+1,r}_loc(Ω)`. -/
theorem HasWeakFDerivOn.memWkpLoc_succ_of_ae_cauchyRiemann {Dξ : ℂ → ℂ →L[ℝ] V}
    (hp : 2 < p) (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc r Ω k η)
    (hDξ : HasWeakFDerivOn volume Ω ξ Dξ)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    MemWkpLoc r Ω (k + 1) ξ := by
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let A : V ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq (by simp [E])
  let conjA := A.conjContinuousAlgEquiv
  have hJ' : MemWkpLoc p Ω (max 1 k) (fun z => conjA (J z)) :=
    conjA.toContinuousLinearEquiv.comp_memWkpLoc_iff.2 hJ
  have hS' : MemWkpLoc p Ω k (fun z => conjA (S z)) :=
    conjA.toContinuousLinearEquiv.comp_memWkpLoc_iff.2 hS
  have hη' : MemWkpLoc r Ω k (fun z => A (η z)) := A.comp_memWkpLoc_iff.2 hη
  obtain ⟨DJ', hDJ', -⟩ := (hJ'.of_le (le_max_left 1 k)).exists_weakFDeriv_of_isOpen
  have hc' : IsSobolevCRCoefficients p Ω (fun z => conjA (J z)) DJ' (fun z => conjA (S z)) :=
    IsSobolevCRCoefficients.of_memWkpLoc (hJ'.of_le (le_max_left 1 k)) hDJ' hS'.memLpLoc
  have heq' : ∀ᵐ z ∂volume.restrict Ω,
      ((A : V →L[ℝ] E).comp (Dξ z)) 1 + conjA (J z) (((A : V →L[ℝ] E).comp (Dξ z)) I) +
        conjA (S z) (A (ξ z)) = A (η z) := by
    filter_upwards [heq] with z hz
    simpa [conjA, map_add] using congrArg A hz
  have hsol' : IsWeakCRSolution 2 Ω (fun z => conjA (J z)) DJ' (fun z => conjA (S z))
      (fun z => A (ξ z)) (fun z => A (η z)) :=
    isWeakCRSolution_of_hasWeakFDerivOn_ae hp hc' (hDξ.clm_comp (A : V →L[ℝ] E))
      (hη'.memLpLoc.locallyIntegrableOn hr.le Ω.isOpen.isLocallyClosed) heq'
  have hp2 : p⁻¹ + (2 : ℝ≥0∞)⁻¹ < 1 := ENNReal.inv_add_inv_two_lt_one_iff.2 hp
  have hJsq' : ∀ᵐ z ∂volume.restrict Ω, conjA (J z) * conjA (J z) = -1 := by
    filter_upwards [hJsq] with z hz
    simpa [map_mul, map_neg, map_one] using congrArg conjA hz
  exact A.comp_memWkpLoc_iff.1
    (hsol'.memWkpLoc_succ hc' hp hJsq' hp2 hr hr_top hrp (hJ'.of_le (le_max_right 1 k)) hS' hη')

/-- **Interior Sobolev regularity for `TauCeti.IsWeakLinearCauchyRiemannOn` on a finite-dimensional
real normed space.** If `2 < p < ∞`, `J ∈ W^{max 1 k, p}_loc(Ω)` with `J² = -1` almost everywhere
on `Ω`, and `S ∈ W^{k,p}_loc(Ω)`, then every weak solution `ξ` of `∂_s ξ + J ∂_t ξ + S ξ = 0` on
`Ω` at any exponent `q : ℝ≥0∞` lies in `W^{k+1,p}_loc(Ω)`. -/
theorem IsWeakLinearCauchyRiemannOn.memWkpLoc_succ (hp : 2 < p) (hp_top : p ≠ ⊤)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) :
    MemWkpLoc p Ω (k + 1) ξ := by
  obtain ⟨-, -, Dξ, hDξ, -, heq⟩ := isWeakLinearCauchyRiemannOn_iff_of_isOpen.1 h
  exact hDξ.memWkpLoc_succ_of_ae_cauchyRiemann hp ((by norm_num : (1 : ℝ≥0∞) < 2).trans hp)
    hp_top le_rfl hJ hJsq hS memWkpLoc_zero_fun heq

/-- **`C^k` interior regularity for `TauCeti.IsWeakLinearCauchyRiemannOn`.** If `2 < p ≤ ∞`
(allowing `p = ∞`), `J ∈ W^{max 1 k, p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`, and
`S ∈ W^{k,p}_loc(Ω)`, then every continuous weak solution `ξ` of `∂_s ξ + J ∂_t ξ + S ξ = 0` on `Ω`
at any exponent `q : ℝ≥0∞` is of class `C^k` on `Ω`. -/
theorem IsWeakLinearCauchyRiemannOn.contDiffOn (hp : 2 < p)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) :
    ContDiffOn ℝ k ξ Ω := by
  obtain ⟨p₀, hp₀, hp₀p⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  exact (h.memWkpLoc_succ hp₀ ENNReal.coe_ne_top (hJ.mono_exponent hp₀p.le) hJsq
    (hS.mono_exponent hp₀p.le)).contDiffOn_of_continuousOn hp₀ h.continuousOn .rfl

/-- **`C^∞` interior regularity for `TauCeti.IsWeakLinearCauchyRiemannOn` with smooth
coefficients.** If `J` and `S` are `C^∞` on `Ω` and `J² = -1` almost everywhere on `Ω`, then every
weak solution `ξ` of `∂_s ξ + J ∂_t ξ + S ξ = 0` at any exponent `q : ℝ≥0∞` is `C^∞` on `Ω`. -/
theorem IsWeakLinearCauchyRiemannOn.contDiffOn_infty
    (hJ : ContDiffOn ℝ ∞ J Ω) (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : ContDiffOn ℝ ∞ S Ω) (h : IsWeakLinearCauchyRiemannOn q Ω J S ξ) :
    ContDiffOn ℝ ∞ ξ Ω :=
  _root_.contDiffOn_infty.2 fun k =>
    h.contDiffOn (p := ⊤) (by simp) ((hJ.of_le (by simp)).memWkpLoc subset_rfl) hJsq
      ((hS.of_le (by simp)).memWkpLoc subset_rfl)

end NormedSpace

end TauCeti
