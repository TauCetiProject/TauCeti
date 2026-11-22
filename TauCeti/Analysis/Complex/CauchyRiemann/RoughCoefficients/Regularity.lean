/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Interior
public import TauCeti.Analysis.Sobolev.Local.Morrey.Higher
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Topology.Algebra.Module.FiniteDimension
import TauCeti.Analysis.Calculus.BumpFunction.Convolution
import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Differentiated
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Distribution.TestFunction.LineDeriv
import TauCeti.Analysis.InnerProductSpace.Adjoint
import TauCeti.Analysis.Sobolev.Local.Coordinates
import TauCeti.Analysis.Sobolev.Local.SobolevEmbedding
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Data.ENNReal.Inv

/-!
# Higher-order interior regularity for Cauchy–Riemann operators with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. Consider the real linear Cauchy–Riemann operator

`D ξ = ∂_s ξ + J ∂_t ξ + S ξ`

with Sobolev coefficients `J ∈ W^{max 1 k, p}_loc(Ω; V →L[ℝ] V)` satisfying `J² = -1` almost
everywhere on `Ω` and `S ∈ W^{k,p}_loc(Ω; V →L[ℝ] V)` for `2 < p ≤ ∞`.

Building on the order-zero regularity theorem `TauCeti.IsWeakCRSolution.memWkpLoc_one_of_le`
of `TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Interior` and the weak differentiated
system `TauCeti.isWeakCRSolution_differentiated` of
`TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Differentiated`, this file proves
higher-order interior regularity (McDuff–Salamon, Proposition B.4.9):

1. **Higher-order interior regularity** (`TauCeti.IsWeakCRSolution.memWkpLoc_succ_of_memWkpLoc`).
   By induction on `k`, if `2 < p ≤ ∞`, `1 < r < ∞`, `r ≤ p`, `p⁻¹ + q⁻¹ < 1`,
   `J ∈ W^{max 1 k, p}_loc(Ω)` with `J² = -1` almost everywhere, `S ∈ W^{k,p}_loc(Ω)`, and
   `η ∈ W^{k,r}_loc(Ω)`, then every weak solution `ξ ∈ L^q_loc(Ω)` belongs to `W^{k+1,r}_loc(Ω)`.
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

* `TauCeti.IsWeakCRSolution.memWkpLoc_succ_of_memWkpLoc`: McDuff–Salamon Proposition B.4.9
  with exponent raising (`ξ ∈ W^{k+1,r}_loc`, allowing `p = ∞` and `q = ∞`).
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

open Complex Filter MeasureTheory Metric Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal InnerProductSpace LineDeriv NNReal Topology

namespace TauCeti

/-! ### Higher-order interior regularity -/

section HigherRegularity

section Step

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ}

private local instance : NormedAddCommGroup (V →L[ℝ] V) := inferInstance
private local instance : NormedSpace ℝ (V →L[ℝ] V) := inferInstance
private local instance : NormedAddCommGroup (V × V →L[ℝ] V × V) := inferInstance
private local instance : NormedSpace ℝ (V × V →L[ℝ] V × V) := inferInstance
private local instance :
    NormedAddCommGroup (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance
private local instance :
    NormedSpace ℝ (WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)) := inferInstance

/-- Inductive step of `IsWeakCRSolution.memWkpLoc_succ_of_memWkpLoc`: upgrades
`ξ ∈ W^{m+1,r}_loc(Ω)` to `ξ ∈ W^{m+2,r}_loc(Ω)` without assuming `p⁻¹ + r⁻¹ < 1` by entering the
weak differentiated system at exponent `2` (since `η ∈ W^{1,r}_loc ⊆ L²_loc` and `p⁻¹ + 2⁻¹ < 1`)
and applying the order-`m` exponent-raising induction hypothesis on `WithLp 2 (V × V)`. -/
private theorem memWkpLoc_succ_of_memWkpLoc_step {p r : ℝ≥0} {q : ℝ≥0∞} {m : ℕ}
    {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}
    (hp : 2 < p) (hr : 1 < r) (hrp : r ≤ p) (hpq : (p : ℝ≥0∞)⁻¹ + q⁻¹ < 1)
    (hJm1 : MemWkpLoc p Ω (m + 1) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω (m + 1) S) (hη : MemWkpLoc r Ω (m + 1) η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) (hξm : MemWkpLoc r Ω (m + 1) ξ)
    (ih_prod : ∀ {q₂ : ℝ≥0∞}
      {J₂ S₂ : ℂ → WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)}
      {DJ₂ : ℂ → ℂ →L[ℝ] WithLp 2 (V × V) →L[ℝ] WithLp 2 (V × V)}
      {Ξ H : ℂ → WithLp 2 (V × V)},
      (p : ℝ≥0∞)⁻¹ + q₂⁻¹ < 1 →
      MemWkpLoc p Ω (max 1 m) J₂ → HasWeakFDerivOn volume Ω J₂ DJ₂ →
      (∀ᵐ z ∂volume.restrict Ω, J₂ z * J₂ z = -1) →
      MemWkpLoc p Ω m S₂ → MemWkpLoc r Ω m H →
      IsWeakCRSolution q₂ Ω J₂ DJ₂ S₂ Ξ H → MemWkpLoc r Ω (m + 1) Ξ) :
    MemWkpLoc r Ω (m + 2) ξ := by
  have h1le : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  have hmax : max 1 m ≤ m + 1 := max_le h1le (Nat.le_succ m)
  have hη_2 : MemLpLoc 2 Ω η := by
    simpa only [ENNReal.coe_ofNat] using
      (((hη.of_le h1le).mono_exponent (by exact_mod_cast hr.le)).memLpLoc_of_inv_sub_inv_le
        (q := 1) (s := 2) le_rfl one_le_two (by norm_num))
  have hp2 : (p : ℝ≥0∞)⁻¹ + (2 : ℝ≥0∞)⁻¹ < 1 :=
    (ENNReal.add_lt_add_right (ENNReal.inv_ne_top.2 two_ne_zero)
      (ENNReal.inv_lt_inv.2 (by exact_mod_cast hp))).trans_eq ENNReal.inv_two_add_inv_two
  obtain ⟨Dξ, hDξ, -⟩ := hξm.exists_weakFDeriv_of_isOpen
  obtain ⟨DS, hDS, -⟩ := hS.exists_weakFDeriv_of_isOpen
  obtain ⟨Dη, hDη, -⟩ := hη.exists_weakFDeriv_of_isOpen
  have hc : IsSobolevCRCoefficients p Ω J DJ S :=
    ⟨hDJ, (hJm1.of_le h1le).memLpLoc,
      memWkpLoc_zero_iff.1 ((hJm1.of_le h1le).memWkpLoc_of_hasWeakFDerivOn hDJ), hS.memLpLoc⟩
  have hξ_2 : MemWkpLoc 2 Ω 1 ξ :=
    hsol.memWkpLoc_one_of_le hc (by exact_mod_cast hp) hJsq hpq (by norm_num) ENNReal.ofNat_ne_top
      (by exact_mod_cast hp.le) hη_2
  have heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z :=
    (hc.isWeakCRSolution_iff_ae hp2.le ENNReal.coe_ne_top ENNReal.ofNat_ne_top hDξ hξ_2.memLpLoc
      (memWkpLoc_zero_iff.1 (hξ_2.memWkpLoc_of_hasWeakFDerivOn hDξ))
      hsol.locallyIntegrableOn).1 (hsol.of_memLpLoc hξ_2.memLpLoc)
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ V V).symm
  let diagL := ContinuousLinearMap.withLpDiagL 2 ℝ V V
  have hDJ₂ : HasWeakFDerivOn volume Ω (fun z => (J z).withLpProdMap 2 (J z))
      (fun z => diagL.comp (DJ z)) := by simpa [diagL] using hDJ.clm_comp diagL
  have hJ₂ : MemWkpLoc p Ω (max 1 m) (fun z => (J z).withLpProdMap 2 (J z)) := by
    simpa [diagL] using (hJm1.of_le hmax).clm_comp diagL
  have hJ₂sq : ∀ᵐ z ∂volume.restrict Ω,
      (J z).withLpProdMap 2 (J z) * (J z).withLpProdMap 2 (J z) = -1 := by
    filter_upwards [hJsq] with z hz
    refine ContinuousLinearMap.ext fun w => ?_
    simpa [ContinuousLinearMap.mul_def, WithLp.ext_iff, Prod.ext_iff] using
      congr($(prodMap_mul_self_eq_neg_one hz) (w.fst, w.snd))
  have hH_m : MemWkpLoc r Ω m
      (fun z => WithLp.toLp 2 (Dη z 1 - DS z 1 (ξ z), Dη z I - DS z I (ξ z))) := by
    simpa only [e, ContinuousLinearEquiv.coe_coe, WithLp.prodContinuousLinearEquiv_symm_apply] using
      (memWkpLoc_differentiatedCR_rightSide hp hr hrp hS hDS (hξm.of_le hmax) hη hDη).clm_comp
        e.toContinuousLinearMap
  have hΞm := ih_prod hp2 hJ₂ hDJ₂ hJ₂sq
    ((hS.of_succ.differentiatedCRCoefficient hJm1 hDJ).clm_comp
      (e.arrowCongr e).toContinuousLinearMap) hH_m
    (isWeakCRSolution_differentiated (by exact_mod_cast one_lt_two.trans hp) (by norm_num) hp2.le
      (hJm1.of_le h1le) hDJ (hS.of_le h1le) hDS hξ_2 hDξ hDη heq)
  exact hξm.memLpLoc.memWkpLoc_succ_of_hasWeakFDerivOn (by rwa [Opens.interior_coe])
    (by simpa only [WithLp.fstL_apply, WithLp.toLp_fst] using
      hΞm.clm_comp (WithLp.fstL 2 ℝ V V))
    (by simpa only [WithLp.sndL_apply, WithLp.toLp_snd] using
      hΞm.clm_comp (WithLp.sndL 2 ℝ V V))

end Step

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  {Ω : Opens ℂ} {p q r : ℝ≥0∞} {k : ℕ}
  {J S : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ η : ℂ → V}

/-- **Higher-order interior regularity with exponent raising** (McDuff–Salamon, Proposition
B.4.9). If `2 < p ≤ ∞`, `1 < r < ∞`, `r ≤ p`, `p⁻¹ + q⁻¹ < 1` (allowing `p = ∞` and `q = ∞`),
`J ∈ W^{max 1 k, p}_loc(Ω)` with `J² = -1` almost everywhere on `Ω`, `S ∈ W^{k,p}_loc(Ω)`, and
`η ∈ W^{k,r}_loc(Ω)`, then every weak solution `ξ ∈ L^q_loc(Ω)` of `∂_s ξ + J ∂_t ξ + S ξ = η`
lies in `W^{k+1,r}_loc(Ω)`. -/
theorem IsWeakCRSolution.memWkpLoc_succ_of_memWkpLoc
    (hp : 2 < p) (hr : 1 < r) (hr_top : r ≠ ⊤) (hrp : r ≤ p) (hpq : p⁻¹ + q⁻¹ < 1)
    (hJ : MemWkpLoc p Ω (max 1 k) J) (hDJ : HasWeakFDerivOn volume Ω J DJ)
    (hJsq : ∀ᵐ z ∂volume.restrict Ω, J z * J z = -1)
    (hS : MemWkpLoc p Ω k S) (hη : MemWkpLoc r Ω k η)
    (hsol : IsWeakCRSolution q Ω J DJ S ξ η) :
    MemWkpLoc r Ω (k + 1) ξ := by
  obtain ⟨p₀, hp₀, hrp₀, hp₀p, hp₀q⟩ :=
    ENNReal.exists_nnreal_lt_and_le_and_inv_add_inv_lt_one (a := 2) (by exact_mod_cast hp)
      hr_top hrp hpq
  lift r to ℝ≥0 using hr_top
  have hr₀ : 1 < r := by exact_mod_cast hr
  have hrp₀' : r ≤ p₀ := ENNReal.coe_le_coe.1 hrp₀
  replace hJ := hJ.mono_exponent hp₀p
  replace hS := hS.mono_exponent hp₀p
  clear hp hr hrp hpq hrp₀ hp₀p
  induction k generalizing V q with
  | zero =>
    have hc : IsSobolevCRCoefficients p₀ Ω J DJ S :=
      ⟨hDJ, hJ.memLpLoc, memWkpLoc_zero_iff.1 (hJ.memWkpLoc_of_hasWeakFDerivOn hDJ),
        memWkpLoc_zero_iff.1 hS⟩
    exact hsol.memWkpLoc_one_of_le hc (by exact_mod_cast hp₀) hJsq hp₀q (by exact_mod_cast hr₀)
      ENNReal.coe_ne_top (by exact_mod_cast hrp₀') (memWkpLoc_zero_iff.1 hη)
  | succ m ih =>
    have hJm1 : MemWkpLoc p₀ Ω (m + 1) J := by simpa using hJ
    have hmax : max 1 m ≤ m + 1 := max_le (Nat.succ_le_succ (Nat.zero_le m)) (Nat.le_succ m)
    exact memWkpLoc_succ_of_memWkpLoc_step hp₀ hr₀ hrp₀' hp₀q hJm1 hDJ hJsq hS hη hsol
      (ih hDJ hJsq hsol hp₀q hη.of_succ (hJm1.of_le hmax) hS.of_succ)
      fun hpr₁ hJ₂ hDJ₂ hJ₂sq hS₂ hH₂ hsol₂ => ih hDJ₂ hJ₂sq hsol₂ hpr₁ hH₂ hJ₂ hS₂

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
  set r₀ : ℝ≥0∞ := min r 3
  have hr₀ : 2 < r₀ := lt_min hr (by norm_num)
  exact (hsol.memWkpLoc_succ_of_memWkpLoc (hr.trans_le hrp)
    ((by norm_num : (1 : ℝ≥0∞) < 2).trans hr₀)
    (ne_top_of_le_ne_top (by norm_num) (min_le_right _ _)) ((min_le_left _ _).trans hrp) hpq
    hJ hDJ hJsq hS (hη.mono_exponent (min_le_left _ _))).exists_contDiffOn_ae_eq hr₀

end HigherRegularity

/-! ### Weak linear Cauchy–Riemann solutions in finite-dimensional normed spaces -/

section NormedSpace

section InnerProductHelper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private local instance : NormedAddCommGroup (E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (E →L[ℝ] E) := inferInstance
private local instance : NormedAddCommGroup (ℂ →L[ℝ] E →L[ℝ] E) := inferInstance
private local instance : NormedSpace ℝ (ℂ →L[ℝ] E →L[ℝ] E) := inferInstance

/-- On a finite-dimensional real inner product space, any map `ξ` with weak derivative `Dξ` on `Ω`
satisfying `∂_s ξ + J ∂_t ξ + S ξ = η` almost everywhere on `Ω` for Sobolev coefficients at
exponent `2 < p ≤ ∞` lies in `L²_loc(Ω)` (via the two-dimensional embedding `W^{1,1}_loc ⊆ L²_loc`)
and satisfies `IsWeakCRSolution 2 Ω J DJ S ξ η`. -/
private theorem isWeakCRSolution_of_hasWeakFDerivOn_ae {Ω : Opens ℂ} {p : ℝ≥0∞}
    (hp : 2 < p) {J S : ℂ → E →L[ℝ] E} {DJ : ℂ → ℂ →L[ℝ] E →L[ℝ] E}
    {ξ η : ℂ → E} {Dξ : ℂ → ℂ →L[ℝ] E}
    (hc : IsSobolevCRCoefficients p Ω J DJ S)
    (hDξ : HasWeakFDerivOn volume Ω ξ Dξ) (hη : LocallyIntegrableOn η Ω volume)
    (heq : ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z) :
    IsWeakCRSolution 2 Ω J DJ S ξ η := by
  have hloc := Ω.isOpen.isLocallyClosed
  have hp1 : 1 ≤ p := one_le_two.trans hp.le
  have hp2 : p⁻¹ + (2 : ℝ≥0∞)⁻¹ < 1 :=
    (ENNReal.add_lt_add_right (ENNReal.inv_ne_top.2 two_ne_zero)
      (ENNReal.inv_lt_inv.2 hp)).trans_eq ENNReal.inv_two_add_inv_two
  -- `HasWeakFDerivOn` places `ξ ∈ W^{1,1}_loc(Ω) ⊆ L²_loc(Ω)` via the 2D Sobolev embedding.
  have hξ1 : MemWkpLoc ((1 : ℝ≥0) : ℝ≥0∞) Ω 1 ξ :=
    memWkpLoc_succ_iff_of_isOpen.2
      ⟨(memLpLoc_one_iff_locallyIntegrableOn hloc).2 hDξ.locallyIntegrableOn, Dξ, hDξ,
        memWkpLoc_zero_iff.2 ((memLpLoc_one_iff_locallyIntegrableOn hloc).2
          hDξ.locallyIntegrableOn_deriv)⟩
  have hξ2 : MemLpLoc 2 Ω ξ := by
    simpa only [ENNReal.coe_ofNat] using
      hξ1.memLpLoc_of_inv_sub_inv_le (q := 1) (s := 2) le_rfl one_le_two (by norm_num)
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
  refine (isWeakCRSolution_congr_ae hJJ' .rfl .rfl .rfl .rfl).2 <|
    isWeakCRSolution_iff.2 ⟨hξ2, hη, fun φ =>
      ⟨hc'.integrable_inner_crFormalAdjoint hp2.le hξ2 φ, ?_⟩⟩
  rw [hc'.integral_inner_crFormalAdjoint_eq_terms hp2.le hξ2 φ]
  -- Integrate `J' ξ` by parts in direction `I` by mollifying `J'` on a precompact `W ⊆ Ω`.
  have hibpI : (∫ z, ⟪fderiv ℝ (φ : ℂ → E) z I, J' z (ξ z)⟫_ℝ) +
      (∫ z, ⟪(φ : ℂ → E) z, DJ z I (ξ z)⟫_ℝ) = -∫ z, ⟪(φ : ℂ → E) z, J' z (Dξ z I)⟫_ℝ := by
    obtain ⟨W, hφW, hWΩ, hWc⟩ :=
      Opens.exists_between_and_isCompact_closure φ.hasCompactSupport φ.tsupport_subset
    obtain ⟨ρ, hρ0, hball⟩ :=
      ContDiffBump.exists_seq_tendsto_rOut_closedBall_subset W.isOpen φ.hasCompactSupport hφW
    have hWm : NullMeasurableSet (W : Set ℂ) volume := W.isOpen.measurableSet.nullMeasurableSet
    have hJW : MemLp J' p (volume.restrict W) :=
      hc'.memLpLoc_coeff.memLp_restrict_of_isCompact_closure hWc hWΩ
    have hDJW : MemLp DJ p (volume.restrict W) :=
      hc'.memLpLoc_deriv.memLp_restrict_of_isCompact_closure hWc hWΩ
    have hξW : MemLp ξ 2 (volume.restrict W) := hξ2.memLp_restrict_of_isCompact_closure hWc hWΩ
    let J_n (n : ℕ) :=
      (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator J'
    let DJ_n (n : ℕ) :=
      (ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (W : Set ℂ).indicator DJ
    have hJn_smooth (n : ℕ) : ContDiff ℝ ∞ (J_n n) :=
      (ρ n).hasCompactSupport_normed.contDiff_convolution_left _ (ρ n).contDiff_normed
        (((memLp_indicator_iff_restrict hWm).2 hJW).locallyIntegrable hp1)
    have hJn_cont {s : Set ℂ} : ∀ᶠ n in atTop, ContinuousOn (J_n n) s :=
      .of_forall fun n => (hJn_smooth n).continuous.continuousOn
    have hunif : TendstoUniformlyOn J_n J' atTop (tsupport (φ : ℂ → E)) :=
      ContDiffBump.tendstoUniformlyOn_normed_convolution_indicator (μ := volume) hρ0 W.isOpen
        φ.hasCompactSupport hφW (hJ'cont.mono (subset_closure.trans hWΩ))
    let B := (ContinuousLinearMap.adjointRealCLM (𝕜 := ℝ) (V := E) (W := E)).flip
    have hid (n : ℕ) : (∫ z, ⟪(∂_{I} φ : 𝓓(Ω, E)) z, J_n n z (ξ z)⟫_ℝ) +
        (∫ z, ⟪(φ : ℂ → E) z, DJ_n n z I (ξ z)⟫_ℝ) =
        -∫ z, ⟪(φ : ℂ → E) z, J_n n z (Dξ z I)⟫_ℝ := by
      let Ψ : 𝓓(Ω, E) := TestFunction.bilinLeftCLM B (hJn_smooth n) φ
      have hweak := (hDξ.hasWeakLineDerivOn I).integral_inner_lineDeriv_eq_neg Ψ
      have hpt (z : ℂ) : ⟪lineDeriv ℝ (Ψ : ℂ → E) z I, ξ z⟫_ℝ =
          ⟪(∂_{I} φ : 𝓓(Ω, E)) z, J_n n z (ξ z)⟫_ℝ +
            ⟪(φ : ℂ → E) z, fderiv ℝ (J_n n) z I (ξ z)⟫_ℝ := by
        rw [TestFunction.lineDeriv_eq_fderiv, TestFunction.bilinLeftCLM_apply,
          B.fderiv_of_bilinear (φ.contDiff.differentiable (by simp) z)
            ((hJn_smooth n).differentiable (by simp) z)]
        simp only [B, add_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.coe_comp,
          Function.comp_apply, ContinuousLinearMap.precompR_apply,
          ContinuousLinearMap.precompL_apply, ContinuousLinearMap.flip_apply,
          ContinuousLinearMap.adjointRealCLM_apply, TestFunction.lineDerivOp_apply_eq_fderiv,
          inner_add_left, ContinuousLinearMap.adjoint_inner_left, add_comm]
      have hi1 := (∂_{I} φ).integrable_inner (hDξ.locallyIntegrableOn.continuousOn_clm_apply hloc
        (hJn_smooth n).continuous.continuousOn)
      have hi2 := φ.integrable_inner (hDξ.locallyIntegrableOn.continuousOn_clm_apply hloc
        (((hJn_smooth n).continuous_fderiv (by simp)).clm_apply
          (continuous_const (y := I))).continuousOn)
      simp_rw [hpt] at hweak
      rw [integral_add hi1 hi2,
        hc'.hasWeakFDerivOn.integral_inner_mollified_fderiv_eq hp1
          hWΩ hJW hDJW (ρ n) φ (hball n) (fun z M => M I (ξ z))] at hweak
      simpa only [Ψ, TestFunction.bilinLeftCLM_apply, B, ContinuousLinearMap.flip_apply,
        ContinuousLinearMap.adjointRealCLM_apply, ContinuousLinearMap.adjoint_inner_left]
        using hweak
    have ht1 := (∂_{I} φ).tendsto_integral_inner_clm_of_tendstoUniformlyOn
      hDξ.locallyIntegrableOn hJn_cont (hunif.mono (φ.tsupport_lineDerivOp_subset I))
    have ht2 : Tendsto (fun n => ∫ z, ⟪(φ : ℂ → E) z, DJ_n n z I (ξ z)⟫_ℝ)
        atTop (𝓝 (∫ z, ⟪(φ : ℂ → E) z, DJ z I (ξ z)⟫_ℝ)) := by
      simpa [DJ_n] using φ.tendsto_integral_inner_bilin_normed_convolution
        (ContinuousLinearMap.apply ℝ (E →L[ℝ] E) I) hp2.le hWm hφW hDJW hξW hρ0
    have ht3 := (φ.tendsto_integral_inner_clm_of_tendstoUniformlyOn
      (hDξ.hasWeakLineDerivOn I).locallyIntegrableOn_deriv hJn_cont hunif).neg
    simpa only [TestFunction.lineDerivOp_apply_eq_fderiv] using
      tendsto_nhds_unique (ht1.add ht2) (ht3.congr fun n => (hid n).symm)
  have ibp1 := (hDξ.hasWeakLineDerivOn 1).integral_inner_lineDeriv_eq_neg φ
  simp only [TestFunction.lineDeriv_eq_fderiv] at ibp1
  have iD1 := φ.integrable_inner (hDξ.hasWeakLineDerivOn 1).locallyIntegrableOn_deriv
  have iJD := φ.integrable_inner
    ((hDξ.hasWeakLineDerivOn I).locallyIntegrableOn_deriv.continuousOn_clm_apply hloc hJ'cont)
  have iSξ := φ.integrable_inner (hc'.memLpLoc_zeroth.locallyIntegrableOn_clm_apply hξ2 hp2.le hloc)
  have hpde : (∫ z, ⟪(φ : ℂ → E) z, Dξ z 1⟫_ℝ) + (∫ z, ⟪(φ : ℂ → E) z, J' z (Dξ z I)⟫_ℝ) +
      (∫ z, ⟪(φ : ℂ → E) z, S z (ξ z)⟫_ℝ) = ∫ z, ⟪(φ : ℂ → E) z, η z⟫_ℝ := by
    rw [← integral_add iD1 iJD]
    refine (integral_add (iD1.add iJD) iSξ).symm.trans
      (integral_congr_ae ((ae_imp_of_ae_restrict heq').mono fun z hz => ?_))
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · simp only [Pi.add_apply, ← inner_add_right, hz hzΩ]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hzΩ (φ.tsupport_subset h)]
  linarith

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
  let A : V ≃L[ℝ] E := (LinearEquiv.ofFinrankEq V E (by simp [E])).toContinuousLinearEquiv
  let conjA : (V →L[ℝ] V) ≃L[ℝ] E →L[ℝ] E := A.arrowCongr A
  have hJ' : MemWkpLoc p Ω (max 1 k) (fun z => conjA (J z)) := conjA.comp_memWkpLoc_iff.2 hJ
  have hS' : MemWkpLoc p Ω k (fun z => conjA (S z)) := conjA.comp_memWkpLoc_iff.2 hS
  have hη' : MemWkpLoc r Ω k (fun z => A (η z)) := A.comp_memWkpLoc_iff.2 hη
  obtain ⟨DJ', hDJ', hDJ'0⟩ := (hJ'.of_le (le_max_left 1 k)).exists_weakFDeriv_of_isOpen
  have hc' : IsSobolevCRCoefficients p Ω (fun z => conjA (J z)) DJ' (fun z => conjA (S z)) :=
    ⟨hDJ', (hJ'.of_le (le_max_left 1 k)).memLpLoc, memWkpLoc_zero_iff.1 hDJ'0, hS'.memLpLoc⟩
  have heq' : ∀ᵐ z ∂volume.restrict Ω,
      ((A : V →L[ℝ] E).comp (Dξ z)) 1 + conjA (J z) (((A : V →L[ℝ] E).comp (Dξ z)) I) +
        conjA (S z) (A (ξ z)) = A (η z) := by
    filter_upwards [heq] with z hz
    simpa [conjA, map_add] using congrArg A hz
  have hsol' : IsWeakCRSolution 2 Ω (fun z => conjA (J z)) DJ' (fun z => conjA (S z))
      (fun z => A (ξ z)) (fun z => A (η z)) :=
    isWeakCRSolution_of_hasWeakFDerivOn_ae hp hc' (hDξ.clm_comp (A : V →L[ℝ] E))
      (hη'.memLpLoc.locallyIntegrableOn hr.le Ω.isOpen.isLocallyClosed) heq'
  have hp2 : p⁻¹ + (2 : ℝ≥0∞)⁻¹ < 1 :=
    (ENNReal.add_lt_add_right (ENNReal.inv_ne_top.2 two_ne_zero)
      (ENNReal.inv_lt_inv.2 hp)).trans_eq ENNReal.inv_two_add_inv_two
  have hJsq' : ∀ᵐ z ∂volume.restrict Ω, conjA (J z) * conjA (J z) = -1 := by
    filter_upwards [hJsq] with z hz
    refine ContinuousLinearMap.ext fun y => ?_
    have hy : J z (J z (A.symm y)) = -A.symm y := by simpa using congr($hz (A.symm y))
    simp [conjA, ContinuousLinearMap.mul_def, hy]
  exact A.comp_memWkpLoc_iff.1
    (hsol'.memWkpLoc_succ_of_memWkpLoc hp hr hr_top hrp hp2 hJ' hDJ' hJsq' hS' hη')

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
  set p₀ : ℝ≥0∞ := min p 3
  have hp₀ : 2 < p₀ := lt_min hp (by norm_num)
  obtain ⟨g, hg, hae⟩ := (h.memWkpLoc_succ hp₀
    (ne_top_of_le_ne_top (by norm_num) (min_le_right _ _))
    (hJ.mono_exponent (min_le_left _ _)) hJsq
    (hS.mono_exponent (min_le_left _ _))).exists_contDiffOn_ae_eq hp₀
  exact hg.congr (Measure.eqOn_open_of_ae_eq hae Ω.isOpen h.continuousOn hg.continuousOn)

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
