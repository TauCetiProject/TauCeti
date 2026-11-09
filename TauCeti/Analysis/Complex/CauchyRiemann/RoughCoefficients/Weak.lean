/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Sobolev.Local.Basic
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Sobolev.WeakDeriv.Bilinear.Holder

/-!
# Weak solutions of real Cauchy–Riemann equations with Sobolev coefficients

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and let `V` be a finite-dimensional real inner product
space. For coefficient fields `J, S : ℂ → (V →L[ℝ] V)` consider the real linear Cauchy–Riemann
operator

`D ξ = ∂_s ξ + J ∂_t ξ + S ξ`.

When `J` is only weakly differentiable, with weak derivative `DJ`, integration by parts against a
smooth compactly supported `φ : ℂ → V` gives the formal adjoint

`D* φ = -∂_s φ - Jᵀ ∂_t φ - (∂_t J)ᵀ φ + Sᵀ φ`,

where `ᵀ` is the Hilbert adjoint `ContinuousLinearMap.adjoint` and `∂_t J = DJ · I`. The
`∂_t J` term comes from moving `∂_t` across the rough coefficient `J`; it cannot be omitted. This
file defines `TauCeti.crFormalAdjoint` and the weak equation

`TauCeti.IsWeakCRSolution q Ω J DJ S ξ η`: `ξ` is locally `L^q`, `η` is locally integrable, and
for every test function `φ ∈ 𝓓(Ω, V)` the pairing `⟪D* φ, ξ⟫` is integrable with
`∫ ⟪D* φ, ξ⟫ = ∫ ⟪φ, η⟫`.

This is the weak formulation of the PseudoholomorphicCurveAnalysis roadmap's interior regularity
theorem with Sobolev coefficients (McDuff–Salamon, §B.4). The weak equation itself makes no
regularity assumption on the coefficients. The theorems consuming it take
`TauCeti.IsSobolevCRCoefficients p Ω J DJ S`: `DJ` is a weak derivative of `J` on `Ω`, and `J`,
`DJ` and `S` are locally `Lᵖ`. With a Hölder triple `1/p + 1/q = 1/r` and `1 ≤ r` every pairing
in the weak equation is then integrable. In the roadmap's setting `p > 2` and `p/(p-1) < q`, so
`r > 1`. Neither continuity of `J` nor `J² = -1` is needed for the statements here.

## Main results

* `TauCeti.IsSobolevCRCoefficients.integral_inner_crFormalAdjoint`: Green's formula. If `ξ` has
  a weak derivative `Dξ`, with `ξ` and `Dξ` locally `L^q`, then
  `∫ ⟪D* φ, ξ⟫ = ∫ ⟪φ, Dξ 1 + J (Dξ I) + S ξ⟫`. The proof uses the weak Leibniz rule for `J ξ`
  at the Hölder triple `(p, q, r)`.
* `TauCeti.IsSobolevCRCoefficients.isWeakCRSolution_iff_ae`: for such `ξ`, the weak equation
  holds exactly when `Dξ 1 + J (Dξ I) + S ξ = η` almost everywhere on `Ω`.
* `TauCeti.isWeakCRSolution_iff_of_contDiffOn`: for `C¹` coefficients `J`, continuous `S`, `C¹`
  `ξ` and continuous `η`, the weak equation with `DJ = fderiv ℝ J` is the classical equation
  `∂_s ξ + J ∂_t ξ + S ξ = η` at every point of `Ω`.
* Linearity in `(ξ, η)` (`TauCeti.IsWeakCRSolution.add`, `.const_smul`, `.neg`, `.sub`),
  restriction to open subsets (`TauCeti.IsWeakCRSolution.mono`) and invariance under changes of
  `J`, `DJ`, `S`, `ξ` and `η` on null subsets of `Ω` (`TauCeti.isWeakCRSolution_congr_ae`).

Two facts about vector-valued test functions are proved on the way, for an arbitrary
finite-dimensional real inner product space of values: the inner-product form of the weak
derivative identity (`TauCeti.HasWeakLineDerivOn.integral_inner_lineDeriv_eq_neg`) and the
fundamental lemma (`TauCeti.ae_eq_of_forall_integral_inner_eq`). Both reduce to scalar tests
through an orthonormal basis or a constant vector.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4 (Lemma B.4.6, Proposition B.4.9).
-/

public noncomputable section

open MeasureTheory TopologicalSpace Complex
open scoped InnerProductSpace ContDiff Distributions ENNReal

namespace TauCeti

/-! ### Vector-valued test functions -/

section TestFunction

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
  [OpensMeasurableSpace E] {μ : Measure E} {Ω : Opens E}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

/-- The weak derivative identity tested against a vector-valued test function through the inner
product: if `u'` is a weak derivative of `u` in the direction `v` on `Ω`, then
`∫ ⟪∂_v φ, u⟫ = -∫ ⟪φ, u'⟫` for every `φ ∈ 𝓓(Ω, V)`. -/
theorem HasWeakLineDerivOn.integral_inner_lineDeriv_eq_neg {u u' : E → V} {v : E}
    (h : HasWeakLineDerivOn μ Ω u u' v) (φ : 𝓓(Ω, V)) :
    ∫ x, ⟪lineDeriv ℝ (φ : E → V) x v, u x⟫_ℝ ∂μ = -∫ x, ⟪(φ : E → V) x, u' x⟫_ℝ ∂μ := by
  let b := stdOrthonormalBasis ℝ V
  let ψ : Fin (Module.finrank ℝ V) → 𝓓(Ω, ℝ) := fun i =>
    TestFunction.postcompCLM (innerSL ℝ (b i)) φ
  have hψ (i) (x : E) : (ψ i : E → ℝ) x = ⟪b i, (φ : E → V) x⟫_ℝ := rfl
  have hφd : Differentiable ℝ (φ : E → V) := φ.contDiff.differentiable (by simp)
  have hψd (i) (x : E) :
      lineDeriv ℝ (ψ i : E → ℝ) x v = ⟪b i, lineDeriv ℝ (φ : E → V) x v⟫_ℝ := by
    have h₁ : HasFDerivAt (ψ i : E → ℝ) ((innerSL ℝ (b i)).comp (fderiv ℝ (φ : E → V) x)) x :=
      (innerSL ℝ (b i)).hasFDerivAt.comp x (hφd x).hasFDerivAt
    rw [h₁.hasLineDerivAt v |>.lineDeriv, (hφd x).lineDeriv_eq_fderiv]
    rfl
  have hw (i) := h.clm_comp (innerSL ℝ (b i))
  calc ∫ x, ⟪lineDeriv ℝ (φ : E → V) x v, u x⟫_ℝ ∂μ
      = ∫ x, ∑ i, lineDeriv ℝ (ψ i : E → ℝ) x v • ⟪b i, u x⟫_ℝ ∂μ := by
        refine integral_congr_ae (.of_forall fun x => ?_)
        dsimp only
        rw [← b.sum_inner_mul_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hψd, smul_eq_mul, real_inner_comm (b i)]
    _ = ∑ i, ∫ x, lineDeriv ℝ (ψ i : E → ℝ) x v • ⟪b i, u x⟫_ℝ ∂μ :=
        integral_finsetSum _ fun i _ =>
          integrable_lineDeriv_smul_of_locallyIntegrableOn (hw i).locallyIntegrableOn (ψ i) v
    _ = ∑ i, -∫ x, (ψ i : E → ℝ) x • ⟪b i, u' x⟫_ℝ ∂μ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (hw i).integral_lineDeriv_smul_eq_neg_integral_smul (ψ i)
    _ = -∫ x, ∑ i, (ψ i : E → ℝ) x • ⟪b i, u' x⟫_ℝ ∂μ := by
        rw [Finset.sum_neg_distrib]
        congr 1
        exact (integral_finsetSum _ fun i _ =>
          (ψ i).integrable_smul (hw i).locallyIntegrableOn_deriv).symm
    _ = -∫ x, ⟪(φ : E → V) x, u' x⟫_ℝ ∂μ := by
        congr 1
        refine integral_congr_ae (.of_forall fun x => ?_)
        dsimp only
        rw [← b.sum_inner_mul_inner]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hψ, smul_eq_mul, real_inner_comm (b i)]

omit [FiniteDimensional ℝ V] in
/-- A test function paired with a locally integrable field is integrable. -/
theorem _root_.TestFunction.integrable_inner {w : E → V} (hw : LocallyIntegrableOn w Ω μ)
    (φ : 𝓓(Ω, V)) : Integrable (fun x => ⟪(φ : E → V) x, w x⟫_ℝ) μ :=
  φ.integrable_bilin (innerSL ℝ) hw

variable [FiniteDimensional ℝ E] [BorelSpace E]

/-- The **fundamental lemma** for vector-valued test functions: locally integrable `g, h` on the
open set `Ω` with `∫ ⟪φ, g⟫ = ∫ ⟪φ, h⟫` for every `φ ∈ 𝓓(Ω, V)` agree almost everywhere on
`Ω`. -/
theorem ae_eq_of_forall_integral_inner_eq {g h : E → V} (hg : LocallyIntegrableOn g Ω μ)
    (hh : LocallyIntegrableOn h Ω μ)
    (H : ∀ φ : 𝓓(Ω, V), ∫ x, ⟪(φ : E → V) x, g x⟫_ℝ ∂μ = ∫ x, ⟪(φ : E → V) x, h x⟫_ℝ ∂μ) :
    g =ᵐ[μ.restrict Ω] h := by
  have hgh : LocallyIntegrableOn (g - h) Ω μ := hg.sub hh
  have key := IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero Ω.isOpen hgh
    fun ψ hψ hψc hψΩ => by
      set w := ∫ x, ψ x • (g - h) x ∂μ
      let ψ' : 𝓓(Ω, ℝ) := ⟨ψ, hψ, hψc, hψΩ⟩
      let Φ : 𝓓(Ω, V) := ⟨fun x => ψ x • w, hψ.smul contDiff_const, hψc.smul_right,
        (tsupport_smul_subset_left _ _).trans hψΩ⟩
      have hΦ := H Φ
      have hint : Integrable (fun x => ψ x • (g - h) x) μ :=
        ψ'.integrable_smul hgh
      have : ⟪w, w⟫_ℝ = 0 := by
        calc ⟪w, w⟫_ℝ = ∫ x, ⟪w, ψ x • (g - h) x⟫_ℝ ∂μ := (integral_inner hint w).symm
          _ = ∫ x, ⟪(Φ : E → V) x, g x⟫_ℝ ∂μ - ∫ x, ⟪(Φ : E → V) x, h x⟫_ℝ ∂μ := by
            rw [← integral_sub (Φ.integrable_inner hg) (Φ.integrable_inner hh)]
            refine integral_congr_ae (.of_forall fun x => ?_)
            simp [Φ, inner_smul_left, inner_smul_right, inner_sub_right, mul_sub]
          _ = 0 := sub_eq_zero.2 hΦ
      exact inner_self_eq_zero.1 this
  rw [Filter.EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [key] with x hx hxΩ
  exact sub_eq_zero.1 (hx hxΩ)

end TestFunction

/-! ### The formal adjoint and the weak equation -/

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω Ω' : Opens ℂ} {p q : ℝ≥0∞}
  {J J' S S' : ℂ → V →L[ℝ] V} {DJ DJ' : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ ξ' η η' : ℂ → V}

/-- The **formal adjoint** of the real Cauchy–Riemann operator `∂_s + J ∂_t + S`, whose
coefficient `J` has (weak) derivative `DJ`, applied to `φ : ℂ → V`:

`D* φ = -∂_s φ - Jᵀ ∂_t φ - (∂_t J)ᵀ φ + Sᵀ φ`,

with `∂_s = fderiv ℝ · · 1`, `∂_t = fderiv ℝ · · I`, `∂_t J = DJ · I` and `ᵀ` the Hilbert
adjoint. It is meant for smooth `φ`; `J`, `DJ` and `S` may be arbitrary functions. -/
def crFormalAdjoint (J : ℂ → V →L[ℝ] V) (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V)
    (φ : ℂ → V) (z : ℂ) : V :=
  -fderiv ℝ φ z 1 - ContinuousLinearMap.adjoint (J z) (fderiv ℝ φ z I) -
    ContinuousLinearMap.adjoint (DJ z I) (φ z) + ContinuousLinearMap.adjoint (S z) (φ z)

/-- Pairing the formal adjoint with a vector moves every adjoint to the other side. -/
theorem inner_crFormalAdjoint (φ : ℂ → V) (z : ℂ) (w : V) :
    ⟪crFormalAdjoint J DJ S φ z, w⟫_ℝ =
      -⟪fderiv ℝ φ z 1, w⟫_ℝ - ⟪fderiv ℝ φ z I, J z w⟫_ℝ - ⟪φ z, DJ z I w⟫_ℝ +
        ⟪φ z, S z w⟫_ℝ := by
  simp only [crFormalAdjoint, inner_add_left, inner_sub_left, inner_neg_left,
    ContinuousLinearMap.adjoint_inner_left]

/-- The formal adjoint of a function vanishes off its topological support. -/
theorem crFormalAdjoint_of_notMem_tsupport {φ : ℂ → V} {z : ℂ} (hz : z ∉ tsupport φ) :
    crFormalAdjoint J DJ S φ z = 0 := by
  simp [crFormalAdjoint, fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]

/-- `IsWeakCRSolution q Ω J DJ S ξ η` says that `ξ` is a **weak solution** of
`∂_s ξ + J ∂_t ξ + S ξ = η` on the open set `Ω`, with `DJ` standing for the weak derivative of
`J`: `ξ` is locally `L^q` on `Ω`, `η` is locally integrable on `Ω`, and for every test function
`φ ∈ 𝓓(Ω, V)` the pairing `⟪D* φ, ξ⟫` is integrable with

`∫ ⟪D* φ, ξ⟫ = ∫ ⟪φ, η⟫`,

where `D*` is `TauCeti.crFormalAdjoint J DJ S`.

The integrability of `ξ`, `η` and `⟪D* φ, ξ⟫` is part of the definition, since the Bochner
integral of a non-integrable function is `0`. The coefficients are unconstrained here; the
theorems using the weak equation assume `TauCeti.IsSobolevCRCoefficients`, under which the
pairing is automatically integrable
(`TauCeti.IsSobolevCRCoefficients.integrable_inner_crFormalAdjoint`). -/
def IsWeakCRSolution (q : ℝ≥0∞) (Ω : Opens ℂ) (J : ℂ → V →L[ℝ] V)
    (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V) (ξ η : ℂ → V) : Prop :=
  MemLpLoc q Ω ξ ∧ LocallyIntegrableOn η Ω ∧
    ∀ φ : 𝓓(Ω, V), Integrable (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) ∧
      ∫ z, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ = ∫ z, ⟪(φ : ℂ → V) z, η z⟫_ℝ

/-- The constructor-and-eliminator form of `TauCeti.IsWeakCRSolution`. -/
theorem isWeakCRSolution_iff : IsWeakCRSolution q Ω J DJ S ξ η ↔
    MemLpLoc q Ω ξ ∧ LocallyIntegrableOn η Ω ∧
      ∀ φ : 𝓓(Ω, V), Integrable (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) ∧
        ∫ z, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ = ∫ z, ⟪(φ : ℂ → V) z, η z⟫_ℝ :=
  Iff.rfl

namespace IsWeakCRSolution

/-- A weak solution is locally `L^q`. -/
theorem memLpLoc (h : IsWeakCRSolution q Ω J DJ S ξ η) : MemLpLoc q Ω ξ := h.1

/-- The right-hand side of a weak equation is locally integrable. -/
theorem locallyIntegrableOn (h : IsWeakCRSolution q Ω J DJ S ξ η) :
    LocallyIntegrableOn η Ω := h.2.1

/-- The pairing of the formal adjoint of a test function with a weak solution is integrable. -/
theorem integrable_inner_crFormalAdjoint (h : IsWeakCRSolution q Ω J DJ S ξ η) (φ : 𝓓(Ω, V)) :
    Integrable (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) := (h.2.2 φ).1

/-- The integral identity defining a weak solution. -/
theorem integral_inner_crFormalAdjoint (h : IsWeakCRSolution q Ω J DJ S ξ η) (φ : 𝓓(Ω, V)) :
    ∫ z, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ = ∫ z, ⟪(φ : ℂ → V) z, η z⟫_ℝ := (h.2.2 φ).2

/-- A weak solution on `Ω` is a weak solution on every open subset of `Ω`. -/
theorem mono (h : IsWeakCRSolution q Ω J DJ S ξ η) (hΩ : Ω' ≤ Ω) :
    IsWeakCRSolution q Ω' J DJ S ξ η :=
  ⟨h.memLpLoc.mono_set hΩ, h.locallyIntegrableOn.mono_set hΩ, fun φ =>
    h.2.2 ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hΩ⟩⟩

/-- The weak equation is homogeneous in `(ξ, η)`. -/
theorem const_smul (h : IsWeakCRSolution q Ω J DJ S ξ η) (c : ℝ) :
    IsWeakCRSolution q Ω J DJ S (c • ξ) (c • η) := by
  refine ⟨h.memLpLoc.const_smul c, h.locallyIntegrableOn.smul c, fun φ => ⟨?_, ?_⟩⟩
  · simpa only [Pi.smul_apply, inner_smul_right] using
      (h.integrable_inner_crFormalAdjoint φ).const_mul c
  · simp only [Pi.smul_apply, inner_smul_right, integral_const_mul,
      h.integral_inner_crFormalAdjoint φ]

/-- The weak equation is compatible with negation of `(ξ, η)`. -/
theorem neg (h : IsWeakCRSolution q Ω J DJ S ξ η) : IsWeakCRSolution q Ω J DJ S (-ξ) (-η) := by
  simpa using h.const_smul (-1)

end IsWeakCRSolution

/-- `ξ = 0` is a weak solution of the homogeneous equation. -/
@[simp]
theorem isWeakCRSolution_zero : IsWeakCRSolution q Ω J DJ S 0 0 :=
  ⟨memLpLoc_zero, locallyIntegrableOn_zero, fun φ => by simp⟩

/-- Replacing the coefficients, the solution or the right-hand side by functions agreeing with
them almost everywhere on `Ω` does not change the weak equation: test functions vanish off `Ω`,
so only values on `Ω` enter. -/
theorem isWeakCRSolution_congr_ae (hJ : J =ᵐ[volume.restrict Ω] J')
    (hDJ : DJ =ᵐ[volume.restrict Ω] DJ') (hS : S =ᵐ[volume.restrict Ω] S')
    (hξ : ξ =ᵐ[volume.restrict Ω] ξ') (hη : η =ᵐ[volume.restrict Ω] η') :
    IsWeakCRSolution q Ω J DJ S ξ η ↔ IsWeakCRSolution q Ω J' DJ' S' ξ' η' := by
  have hrhs (φ : 𝓓(Ω, V)) : ∫ z, ⟪(φ : ℂ → V) z, η z⟫_ℝ = ∫ z, ⟪(φ : ℂ → V) z, η' z⟫_ℝ := by
    refine integral_congr_ae ?_
    filter_upwards [ae_imp_of_ae_restrict hη] with z hz
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · rw [hz hzΩ]
    · simp [image_eq_zero_of_notMem_tsupport fun h' => hzΩ (φ.tsupport_subset h')]
  have hlhs (φ : 𝓓(Ω, V)) : (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) =ᵐ[volume]
      fun z => ⟪crFormalAdjoint J' DJ' S' φ z, ξ' z⟫_ℝ := by
    filter_upwards [ae_imp_of_ae_restrict hJ, ae_imp_of_ae_restrict hDJ,
      ae_imp_of_ae_restrict hS, ae_imp_of_ae_restrict hξ] with z hJz hDJz hSz hξz
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · simp only [crFormalAdjoint, hJz hzΩ, hDJz hzΩ, hSz hzΩ, hξz hzΩ]
    · have hz : z ∉ tsupport (φ : ℂ → V) := fun h' => hzΩ (φ.tsupport_subset h')
      simp [crFormalAdjoint_of_notMem_tsupport hz]
  simp only [isWeakCRSolution_iff, hrhs, integral_congr_ae (hlhs _), integrable_congr (hlhs _)]
  exact and_congr ⟨fun h => h.congr_ae hξ, fun h => h.congr_ae hξ.symm⟩
    (and_congr ⟨fun h => h.congr hη, fun h => h.congr hη.symm⟩ Iff.rfl)

/-! ### Sobolev coefficients and Green's formula -/

/-- `IsSobolevCRCoefficients p Ω J DJ S` says that the coefficients of the real Cauchy–Riemann
operator `∂_s + J ∂_t + S` are of class `W^{1,p}` and `Lᵖ` locally on `Ω`: `DJ` is a weak
derivative of `J` on `Ω`, and `J`, `DJ` and `S` are locally `Lᵖ` on `Ω`. -/
structure IsSobolevCRCoefficients (p : ℝ≥0∞) (Ω : Opens ℂ) (J : ℂ → V →L[ℝ] V)
    (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V) : Prop where
  /-- `DJ` is a weak derivative of `J` on `Ω`. -/
  hasWeakFDerivOn : HasWeakFDerivOn volume Ω J DJ
  /-- `J` is locally `Lᵖ` on `Ω`. -/
  memLpLoc_coeff : MemLpLoc p Ω J
  /-- The weak derivative of `J` is locally `Lᵖ` on `Ω`. -/
  memLpLoc_deriv : MemLpLoc p Ω DJ
  /-- The zeroth-order coefficient is locally `Lᵖ` on `Ω`. -/
  memLpLoc_zeroth : MemLpLoc p Ω S

section Holder

/-- An exponent pair with `1/p + 1/q ≤ 1` has `1 ≤ q`. -/
private theorem one_le_right_of_inv_add_inv_le_one (hpq : p⁻¹ + q⁻¹ ≤ 1) : 1 ≤ q :=
  ENNReal.inv_le_one.1 (le_add_self.trans hpq)

/-- An exponent pair with `1/p + 1/q ≤ 1` has `1 ≤ p`. -/
private theorem one_le_left_of_inv_add_inv_le_one (hpq : p⁻¹ + q⁻¹ ≤ 1) : 1 ≤ p :=
  ENNReal.inv_le_one.1 (le_self_add.trans hpq)

omit [CompleteSpace V] in
/-- Hölder's inequality on compact subsets: an `Lᵖ_loc` operator field applied to an `L^q_loc`
vector field is locally integrable when `1/p + 1/q ≤ 1`. -/
private theorem locallyIntegrableOn_apply (hpq : p⁻¹ + q⁻¹ ≤ 1) {A : ℂ → V →L[ℝ] V}
    {w : ℂ → V} (hA : MemLpLoc p Ω A) (hw : MemLpLoc q Ω w) :
    LocallyIntegrableOn (fun z => A z (w z)) Ω := by
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  exact MemLpLoc.locallyIntegrableOn
    (memLpLoc_iff.2 fun K hK hc => (ContinuousLinearMap.id ℝ (V →L[ℝ] V)).memLp_of_bilin _
      (memLpLoc_iff.1 hA K hK hc) (memLpLoc_iff.1 hw K hK hc))
    (ENNReal.one_le_inv.2 hpq) Ω.isOpen.isLocallyClosed

omit [CompleteSpace V] in
/-- The `∂_t J` coefficient `DJ · I` inherits local `Lᵖ` membership from `DJ`. -/
private theorem IsSobolevCRCoefficients.memLpLoc_derivI
    (hc : IsSobolevCRCoefficients p Ω J DJ S) : MemLpLoc p Ω (fun z => DJ z I) :=
  hc.memLpLoc_deriv.clm_comp (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)

omit [CompleteSpace V] in
/-- The coordinate derivatives of a test function are coordinate derivatives in the sense of
`fderiv`. -/
private theorem lineDeriv_testFunction (φ : 𝓓(Ω, V)) (v z : ℂ) :
    lineDeriv ℝ (φ : ℂ → V) z v = fderiv ℝ (φ : ℂ → V) z v :=
  ((φ.contDiff.differentiable (by simp)) z).lineDeriv_eq_fderiv

omit [CompleteSpace V] in
/-- A coordinate derivative of a test function, paired with a locally integrable field, is
integrable. -/
private theorem integrable_inner_fderiv {w : ℂ → V} (hw : LocallyIntegrableOn w Ω)
    (φ : 𝓓(Ω, V)) (v : ℂ) :
    Integrable (fun z => ⟪fderiv ℝ (φ : ℂ → V) z v, w z⟫_ℝ) := by
  have h := (TestFunction.lineDerivCLM ℝ v φ : 𝓓(Ω, V)).integrable_inner hw
  simp only [TestFunction.lineDerivCLM_apply, le_top, ite_true, lineDeriv_testFunction] at h
  exact h

omit [CompleteSpace V] in
/-- A test function paired with a locally integrable field is integrable. -/
private theorem integrable_inner_testFunction {w : ℂ → V} (hw : LocallyIntegrableOn w Ω)
    (φ : 𝓓(Ω, V)) : Integrable (fun z => ⟪(φ : ℂ → V) z, w z⟫_ℝ) :=
  φ.integrable_inner hw

/-- Under Sobolev coefficients and the Hölder condition `1/p + 1/q ≤ 1`, the pairing
`⟪D* φ, ξ⟫` of the weak equation is integrable for every locally `L^q` field `ξ`. -/
theorem IsSobolevCRCoefficients.integrable_inner_crFormalAdjoint
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    (hξ : MemLpLoc q Ω ξ) (φ : 𝓓(Ω, V)) :
    Integrable (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) := by
  have h₁ := integrable_inner_fderiv (hξ.locallyIntegrableOn
    (one_le_right_of_inv_add_inv_le_one hpq) Ω.isOpen.isLocallyClosed) φ 1
  have h₂ := integrable_inner_fderiv (locallyIntegrableOn_apply hpq hc.memLpLoc_coeff hξ) φ I
  have h₃ := integrable_inner_testFunction
    (locallyIntegrableOn_apply hpq hc.memLpLoc_derivI hξ) φ
  have h₄ := integrable_inner_testFunction
    (locallyIntegrableOn_apply hpq hc.memLpLoc_zeroth hξ) φ
  simp only [inner_crFormalAdjoint]
  exact ((h₁.neg.sub h₂).sub h₃).add h₄

/-- **Green's formula** for the real Cauchy–Riemann operator with Sobolev coefficients. If `ξ`
has weak derivative `Dξ` on `Ω`, with `ξ` and `Dξ` locally `L^q`, and `1/p + 1/q ≤ 1` with
finite `p, q`, then for every test function `φ`,

`∫ ⟪D* φ, ξ⟫ = ∫ ⟪φ, Dξ 1 + J (Dξ I) + S ξ⟫`.

The `∂_t J` term of `D*` cancels the derivative of `J` in the weak Leibniz rule for `J ξ`. -/
theorem IsSobolevCRCoefficients.integral_inner_crFormalAdjoint [FiniteDimensional ℝ V]
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    {Dξ : ℂ → ℂ →L[ℝ] V} (hξ : HasWeakFDerivOn volume Ω ξ Dξ) (hξq : MemLpLoc q Ω ξ)
    (hDξq : MemLpLoc q Ω Dξ) (φ : 𝓓(Ω, V)) :
    ∫ z, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ =
      ∫ z, ⟪(φ : ℂ → V) z, Dξ z 1 + J z (Dξ z I) + S z (ξ z)⟫_ℝ := by
  have hq1 := one_le_right_of_inv_add_inv_le_one hpq
  have : Fact (1 ≤ p) := ⟨one_le_left_of_inv_add_inv_le_one hpq⟩
  have : Fact (1 ≤ q) := ⟨hq1⟩
  have : Fact (1 ≤ (p⁻¹ + q⁻¹)⁻¹) := ⟨ENNReal.one_le_inv.2 hpq⟩
  have : ENNReal.HolderTriple p q (p⁻¹ + q⁻¹)⁻¹ := ⟨(inv_inv _).symm⟩
  have hloc := Ω.isOpen.isLocallyClosed
  have hDξI : MemLpLoc q Ω (fun z => Dξ z I) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)
  have hDξ1 : MemLpLoc q Ω (fun z => Dξ z 1) :=
    hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)
  -- the weak Leibniz rule for `J ξ` in the direction `I`
  have hJξ : HasWeakLineDerivOn volume Ω (fun z => J z (ξ z))
      (fun z => DJ z I (ξ z) + J z (Dξ z I)) I := by
    simpa using (hc.hasWeakFDerivOn.hasWeakLineDerivOn I).bilin_of_memLp
      (r := (p⁻¹ + q⁻¹)⁻¹) (ContinuousLinearMap.id ℝ (V →L[ℝ] V)) hp hq (hξ.hasWeakLineDerivOn I)
      (fun K hK hKΩ => memLpLoc_iff.1 hc.memLpLoc_coeff K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hc.memLpLoc_derivI K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hξq K hKΩ hK)
      (fun K hK hKΩ => memLpLoc_iff.1 hDξI K hKΩ hK)
  have hA := integrable_inner_testFunction
    (locallyIntegrableOn_apply hpq hc.memLpLoc_derivI hξq) φ
  have hB := integrable_inner_testFunction (locallyIntegrableOn_apply hpq hc.memLpLoc_coeff hDξI) φ
  have hC := integrable_inner_testFunction (locallyIntegrableOn_apply hpq hc.memLpLoc_zeroth hξq) φ
  have hD := integrable_inner_testFunction (hDξ1.locallyIntegrableOn hq1 hloc) φ
  have h₁ := integrable_inner_fderiv (hξq.locallyIntegrableOn hq1 hloc) φ 1
  have h₂ := integrable_inner_fderiv (locallyIntegrableOn_apply hpq hc.memLpLoc_coeff hξq) φ I
  have hξ1 : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, ξ z⟫_ℝ = -∫ z, ⟪(φ : ℂ → V) z, Dξ z 1⟫_ℝ := by
    have h := (hξ.hasWeakLineDerivOn 1).integral_inner_lineDeriv_eq_neg φ
    simp only [lineDeriv_testFunction] at h
    exact h
  have hJξI : ∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (ξ z)⟫_ℝ =
      -((∫ z, ⟪(φ : ℂ → V) z, DJ z I (ξ z)⟫_ℝ) + ∫ z, ⟪(φ : ℂ → V) z, J z (Dξ z I)⟫_ℝ) := by
    have h := hJξ.integral_inner_lineDeriv_eq_neg φ
    simp only [lineDeriv_testFunction, inner_add_right] at h
    refine h.trans ?_
    congr 1
    exact integral_add hA hB
  have hDB : Integrable (fun z => ⟪(φ : ℂ → V) z, Dξ z 1⟫_ℝ +
      ⟪(φ : ℂ → V) z, J z (Dξ z I)⟫_ℝ) := hD.add hB
  have hrhs : ∫ z, ⟪(φ : ℂ → V) z, Dξ z 1 + J z (Dξ z I) + S z (ξ z)⟫_ℝ =
      (∫ z, ⟪(φ : ℂ → V) z, Dξ z 1⟫_ℝ) + (∫ z, ⟪(φ : ℂ → V) z, J z (Dξ z I)⟫_ℝ) +
        ∫ z, ⟪(φ : ℂ → V) z, S z (ξ z)⟫_ℝ := by
    simp only [inner_add_right]
    rw [integral_add hDB hC, integral_add hD hB]
  have e₁ : Integrable (fun z => -⟪fderiv ℝ (φ : ℂ → V) z 1, ξ z⟫_ℝ) := h₁.neg
  have e₂ : Integrable (fun z => -⟪fderiv ℝ (φ : ℂ → V) z 1, ξ z⟫_ℝ -
      ⟪fderiv ℝ (φ : ℂ → V) z I, J z (ξ z)⟫_ℝ) := e₁.sub h₂
  have e₃ : Integrable (fun z => -⟪fderiv ℝ (φ : ℂ → V) z 1, ξ z⟫_ℝ -
      ⟪fderiv ℝ (φ : ℂ → V) z I, J z (ξ z)⟫_ℝ - ⟪(φ : ℂ → V) z, DJ z I (ξ z)⟫_ℝ) := e₂.sub hA
  have hlhs : ∫ z, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ =
      -(∫ z, ⟪fderiv ℝ (φ : ℂ → V) z 1, ξ z⟫_ℝ) - (∫ z, ⟪fderiv ℝ (φ : ℂ → V) z I, J z (ξ z)⟫_ℝ) -
        (∫ z, ⟪(φ : ℂ → V) z, DJ z I (ξ z)⟫_ℝ) + ∫ z, ⟪(φ : ℂ → V) z, S z (ξ z)⟫_ℝ := by
    simp only [inner_crFormalAdjoint]
    rw [integral_add e₃ hC, integral_sub e₂ hA, integral_sub e₁ h₂, integral_neg]
  rw [hlhs, hrhs, hξ1, hJξI]
  ring

/-- **Weak solutions with a weak derivative.** If `ξ` has weak derivative `Dξ` on `Ω`, with `ξ`
and `Dξ` locally `L^q`, `1/p + 1/q ≤ 1` and `p, q` finite, then `ξ` is a weak solution of
`∂_s ξ + J ∂_t ξ + S ξ = η` exactly when `Dξ 1 + J (Dξ I) + S ξ = η` almost everywhere on
`Ω`. -/
theorem IsSobolevCRCoefficients.isWeakCRSolution_iff_ae [FiniteDimensional ℝ V]
    (hc : IsSobolevCRCoefficients p Ω J DJ S) (hpq : p⁻¹ + q⁻¹ ≤ 1) (hp : p ≠ ⊤) (hq : q ≠ ⊤)
    {Dξ : ℂ → ℂ →L[ℝ] V} (hξ : HasWeakFDerivOn volume Ω ξ Dξ) (hξq : MemLpLoc q Ω ξ)
    (hDξq : MemLpLoc q Ω Dξ) (hη : LocallyIntegrableOn η Ω) :
    IsWeakCRSolution q Ω J DJ S ξ η ↔
      ∀ᵐ z ∂volume.restrict Ω, Dξ z 1 + J z (Dξ z I) + S z (ξ z) = η z := by
  have hq1 := one_le_right_of_inv_add_inv_le_one hpq
  have hloc := Ω.isOpen.isLocallyClosed
  have hL : LocallyIntegrableOn (fun z => Dξ z 1 + J z (Dξ z I) + S z (ξ z)) Ω :=
    (((hDξq.clm_comp (ContinuousLinearMap.apply ℝ V 1)).locallyIntegrableOn hq1 hloc).add
      (locallyIntegrableOn_apply hpq hc.memLpLoc_coeff
        (hDξq.clm_comp (ContinuousLinearMap.apply ℝ V I)))).add
      (locallyIntegrableOn_apply hpq hc.memLpLoc_zeroth hξq)
  simp only [isWeakCRSolution_iff, hc.integral_inner_crFormalAdjoint hpq hp hq hξ hξq hDξq,
    hc.integrable_inner_crFormalAdjoint hpq hξq, hξq, hη, true_and]
  refine ⟨ae_eq_of_forall_integral_inner_eq hL hη, fun h φ => integral_congr_ae ?_⟩
  filter_upwards [ae_imp_of_ae_restrict h] with z hz
  by_cases hzΩ : z ∈ (Ω : Set ℂ)
  · rw [hz hzΩ]
  · simp [image_eq_zero_of_notMem_tsupport fun h' => hzΩ (φ.tsupport_subset h')]

end Holder

namespace IsWeakCRSolution

/-- The weak equation is additive in `(ξ, η)`. -/
theorem add (h : IsWeakCRSolution q Ω J DJ S ξ η) (h' : IsWeakCRSolution q Ω J DJ S ξ' η') :
    IsWeakCRSolution q Ω J DJ S (ξ + ξ') (η + η') := by
  refine ⟨h.memLpLoc.add h'.memLpLoc, h.locallyIntegrableOn.add h'.locallyIntegrableOn,
    fun φ => ⟨?_, ?_⟩⟩
  · simp only [Pi.add_apply, inner_add_right]
    exact (h.integrable_inner_crFormalAdjoint φ).add (h'.integrable_inner_crFormalAdjoint φ)
  · simp only [Pi.add_apply, inner_add_right]
    rw [integral_add (h.integrable_inner_crFormalAdjoint φ)
        (h'.integrable_inner_crFormalAdjoint φ),
      integral_add (integrable_inner_testFunction h.locallyIntegrableOn φ)
        (integrable_inner_testFunction h'.locallyIntegrableOn φ),
      h.integral_inner_crFormalAdjoint φ, h'.integral_inner_crFormalAdjoint φ]

/-- The weak equation is compatible with subtraction of `(ξ, η)`. -/
theorem sub (h : IsWeakCRSolution q Ω J DJ S ξ η) (h' : IsWeakCRSolution q Ω J DJ S ξ' η') :
    IsWeakCRSolution q Ω J DJ S (ξ - ξ') (η - η') := by
  simpa [sub_eq_add_neg] using h.add h'.neg

end IsWeakCRSolution

/-! ### Comparison with the classical equation -/

/-- **Classical solutions.** For `C¹` coefficients `J` on `Ω`, with `DJ = fderiv ℝ J`, continuous
`S`, a `C¹` field `ξ` and a continuous right-hand side `η`, the weak equation is the classical
equation `∂_s ξ + J ∂_t ξ + S ξ = η` at every point of `Ω`, for every exponent `q`. -/
theorem isWeakCRSolution_iff_of_contDiffOn [FiniteDimensional ℝ V] (hJ : ContDiffOn ℝ 1 J Ω)
    (hS : ContinuousOn S Ω) (hξ : ContDiffOn ℝ 1 ξ Ω) (hη : ContinuousOn η Ω) :
    IsWeakCRSolution q Ω J (fderiv ℝ J) S ξ η ↔
      ∀ z ∈ (Ω : Set ℂ), fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z) = η z := by
  have hJ' : ContinuousOn (fderiv ℝ J) Ω := hJ.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
  have hξ' : ContinuousOn (fderiv ℝ ξ) Ω := hξ.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
  have hdiff {f : ℂ → V →L[ℝ] V} (hf : ContDiffOn ℝ 1 f Ω) (z : ℂ) (hz : z ∈ (Ω : Set ℂ)) :
      DifferentiableAt ℝ f z :=
    (hf.differentiableOn one_ne_zero z hz).differentiableAt (Ω.isOpen.mem_nhds hz)
  have hc : IsSobolevCRCoefficients 2 Ω J (fderiv ℝ J) S :=
    ⟨hasWeakFDerivOn_of_differentiableOn (hJ'.locallyIntegrableOn Ω.isOpen.measurableSet)
      (hdiff hJ), hJ.continuousOn.memLpLoc, hJ'.memLpLoc, hS.memLpLoc⟩
  have hξw : HasWeakFDerivOn volume Ω ξ (fderiv ℝ ξ) :=
    hasWeakFDerivOn_of_differentiableOn (hξ'.locallyIntegrableOn Ω.isOpen.measurableSet)
      fun z hz => (hξ.differentiableOn one_ne_zero z hz).differentiableAt (Ω.isOpen.mem_nhds hz)
  have hη' : LocallyIntegrableOn η Ω := hη.locallyIntegrableOn Ω.isOpen.measurableSet
  have hL : ContinuousOn (fun z => fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)) Ω :=
    ((hξ'.clm_apply continuousOn_const).add
      (hJ.continuousOn.clm_apply (hξ'.clm_apply continuousOn_const))).add
      (hS.clm_apply hξ.continuousOn)
  have key : IsWeakCRSolution q Ω J (fderiv ℝ J) S ξ η ↔
      IsWeakCRSolution 2 Ω J (fderiv ℝ J) S ξ η := by
    simp only [isWeakCRSolution_iff, hξ.continuousOn.memLpLoc, true_and]
  rw [key, hc.isWeakCRSolution_iff_ae (by simp [ENNReal.inv_two_add_inv_two]) (by simp) (by simp)
    hξw hξ.continuousOn.memLpLoc hξ'.memLpLoc hη']
  exact ⟨fun h => Measure.eqOn_open_of_ae_eq h Ω.isOpen hL hη, fun h =>
    (ae_restrict_iff' Ω.isOpen.measurableSet).2 (.of_forall h)⟩

end TauCeti
