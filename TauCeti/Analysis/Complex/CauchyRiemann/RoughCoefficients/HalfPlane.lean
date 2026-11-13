/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Complex.Wirtinger.HalfPlaneAdjoint.Variable
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Weak solutions of real Cauchy–Riemann equations on half-discs with a boundary condition

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and consider the part `Ω ∩ {0 ≤ t}` of `Ω` in the
closed upper half-plane. Let `V` be a real inner product space, `Λ ⊆ V` a real subspace (the
boundary condition, `ℝⁿ ⊆ ℂⁿ` in the local model of a totally real boundary condition) and
`J, S : ℂ → (V →L[ℝ] V)` coefficient fields, with `DJ` standing for the (weak) derivative of `J`.
This file defines the weak form of the boundary value problem

`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω ∩ {0 < t}`, `ξ(s) ∈ Λ` for real `s ∈ Ω`,

`TauCeti.IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η`: `ξ` is locally `L^q` and `η` locally
integrable on `Ω ∩ {0 ≤ t}`, and for every test function `φ ∈ 𝓓(Ω, V)` with `φ(s) ∈ Λ` for real
`s` the pairing `⟪D* φ, ξ⟫` is integrable on `{0 < t}` with

`∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, η⟫`,

where `D* φ = -∂_s φ - Jᵀ ∂_t φ - (∂_t J)ᵀ φ + Sᵀ φ` is `TauCeti.crFormalAdjoint J DJ S`. The test
functions are compactly supported in `Ω` but are not required to vanish on `ℝ`; only their values
there are restricted. This is McDuff–Salamon's weak equation (B.4.3), with the zeroth-order term
added, in the normalization of the interior weak equation `TauCeti.IsWeakCRSolution`. The
boundary condition on `ξ` is not part of the definition: it is encoded by the boundary values of
the test functions, as the Checks below show.

## Main results

* Linearity in `(ξ, η)` (`TauCeti.IsWeakCRSolutionHalfOn.add`, `.const_smul`, `.neg`, `.sub`,
  `TauCeti.isWeakCRSolutionHalfOn_zero`), restriction to smaller open sets
  (`TauCeti.IsWeakCRSolutionHalfOn.mono`), lowering the exponent
  (`TauCeti.IsWeakCRSolutionHalfOn.mono_exponent`) and invariance under changes of the data on
  null subsets of `Ω ∩ {0 ≤ t}` (`TauCeti.isWeakCRSolutionHalfOn_congr_ae`).
* `TauCeti.IsWeakCRSolutionHalfOn.isWeakCRSolution`: a weak solution up to the boundary is a weak
  solution of the interior equation on the open upper part `Ω ∩ {0 < t}`.
* `TauCeti.isWeakCRSolutionHalfOn_of_contDiffOn`: for `C¹` coefficients `J` with `DJ = fderiv ℝ J`
  and continuous `S`, a `C¹` field `ξ` solving the equation classically on `Ω ∩ {0 < t}`, with
  `ξ(s) ∈ Λ` and `⟪Λ, J(s) Λ⟫ = 0` for real `s ∈ Ω`, is a weak solution.
* Checks for `V = ℂ`, `J = i`, `S = 0`, `Λ = ℝ`: `ξ = z` is a weak solution of the homogeneous
  equation (`TauCeti.isWeakCRSolutionHalfOn_id`); the constant `ξ = i`, which solves the equation
  in the interior but violates the boundary condition, is not
  (`TauCeti.not_isWeakCRSolutionHalfOn_const_I`); and without the restriction on the boundary
  values of the test functions even the constant `ξ = 1` would fail
  (`TauCeti.exists_setIntegral_inner_crFormalAdjoint_one_ne_zero`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, equation (B.4.3) and Lemma B.4.6.
-/

public noncomputable section

open MeasureTheory TopologicalSpace Complex Set
open scoped InnerProductSpace ContDiff Distributions ENNReal

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω Ω' : Opens ℂ} {Λ : Submodule ℝ V} {q r : ℝ≥0∞}
  {J J' S S' : ℂ → V →L[ℝ] V} {DJ DJ' : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ ξ' η η' : ℂ → V}

/-- `IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η` says that `ξ` is a **weak solution up to the real
axis** of `∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω ∩ {0 ≤ t}` with boundary condition `Λ`, with `DJ`
standing for the weak derivative of `J`: `ξ` is locally `L^q` and `η` is locally integrable on
`Ω ∩ {0 ≤ t}`, and for every test function `φ ∈ 𝓓(Ω, V)` taking values in `Λ` on `ℝ` the pairing
`⟪D* φ, ξ⟫` is integrable on the upper half-plane with

`∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, η⟫`,

where `D*` is `TauCeti.crFormalAdjoint J DJ S`. The test functions need not vanish on `ℝ`. As
for `TauCeti.IsWeakCRSolution`, the integrability is part of the definition and the coefficients
are unconstrained. -/
def IsWeakCRSolutionHalfOn (q : ℝ≥0∞) (Ω : Opens ℂ) (Λ : Submodule ℝ V) (J : ℂ → V →L[ℝ] V)
    (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V) (ξ η : ℂ → V) : Prop :=
  MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ ∧
    LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
    ∀ φ : 𝓓(Ω, V), (∀ s : ℝ, (φ : ℂ → V) s ∈ Λ) →
      IntegrableOn (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) {z : ℂ | 0 < z.im} ∧
        ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ =
          ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, η z⟫_ℝ

/-- The constructor-and-eliminator form of `TauCeti.IsWeakCRSolutionHalfOn`. -/
theorem isWeakCRSolutionHalfOn_iff : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η ↔
    MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ ∧
      LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
      ∀ φ : 𝓓(Ω, V), (∀ s : ℝ, (φ : ℂ → V) s ∈ Λ) →
        IntegrableOn (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) {z : ℂ | 0 < z.im} ∧
          ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ =
            ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, η z⟫_ℝ :=
  Iff.rfl

omit [CompleteSpace V] in
/-- A test function on `Ω`, paired with a field that is locally integrable on `Ω ∩ {0 ≤ t}`, is
integrable on the upper half-plane. -/
private theorem integrableOn_im_pos_inner
    (hη : LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})) (φ : 𝓓(Ω, V)) :
    IntegrableOn (fun z => ⟪(φ : ℂ → V) z, η z⟫_ℝ) {z : ℂ | 0 < z.im} := by
  set K := tsupport (φ : ℂ → V) ∩ {z : ℂ | 0 ≤ z.im}
  have hK : IsCompact K :=
    φ.hasCompactSupport.isCompact.inter_right (isClosed_le continuous_const continuous_im)
  have hηK : IntegrableOn η K :=
    hη.integrableOn_compact_subset (inter_subset_inter_left _ φ.tsupport_subset) hK
  have hon : IntegrableOn (fun z => ⟪(φ : ℂ → V) z, η z⟫_ℝ) K := by
    rw [IntegrableOn, ← memLp_one_iff_integrable]
    exact (innerSL ℝ).memLp_of_bilin 1 φ.memLp_top (memLp_one_iff_integrable.2 hηK)
  refine hon.of_forall_sdiff_eq_zero (measurableSet_lt measurable_const measurable_im)
    fun z hz => ?_
  have h0 : 0 < z.im := hz.1
  have hz' : z ∉ tsupport (φ : ℂ → V) := fun h => hz.2 ⟨h, h0.le⟩
  simp [image_eq_zero_of_notMem_tsupport hz']

namespace IsWeakCRSolutionHalfOn

/-- A weak solution up to the boundary is locally `L^q` up to the boundary. -/
theorem memLpLoc (h : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η) :
    MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ := h.1

/-- The right-hand side of a weak equation up to the boundary is locally integrable up to the
boundary. -/
theorem locallyIntegrableOn (h : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η) :
    LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := h.2.1

/-- The pairing of the formal adjoint of an admissible test function with a weak solution is
integrable on the upper half-plane. -/
theorem integrableOn_inner_crFormalAdjoint (h : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η)
    (φ : 𝓓(Ω, V)) (hφ : ∀ s : ℝ, (φ : ℂ → V) s ∈ Λ) :
    IntegrableOn (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) {z : ℂ | 0 < z.im} :=
  (h.2.2 φ hφ).1

/-- The integral identity defining a weak solution up to the boundary. -/
theorem setIntegral_inner_crFormalAdjoint (h : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η)
    (φ : 𝓓(Ω, V)) (hφ : ∀ s : ℝ, (φ : ℂ → V) s ∈ Λ) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ =
      ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, η z⟫_ℝ :=
  (h.2.2 φ hφ).2

/-- A weak solution on `Ω` is a weak solution on every open subset of `Ω`, with the same
boundary condition. -/
theorem mono (h : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η) (hΩ : Ω' ≤ Ω) :
    IsWeakCRSolutionHalfOn q Ω' Λ J DJ S ξ η :=
  ⟨h.memLpLoc.mono_set (inter_subset_inter_left _ hΩ),
    h.locallyIntegrableOn.mono_set (inter_subset_inter_left _ hΩ), fun φ hφ =>
    h.2.2 ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hΩ⟩ hφ⟩

/-- A weak solution for the exponent `q` is a weak solution for every smaller exponent. -/
theorem mono_exponent (h : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η) (hrq : r ≤ q) :
    IsWeakCRSolutionHalfOn r Ω Λ J DJ S ξ η :=
  ⟨h.memLpLoc.mono_exponent hrq, h.locallyIntegrableOn, h.2.2⟩

/-- The weak equation up to the boundary is homogeneous in `(ξ, η)`. -/
theorem const_smul (h : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η) (c : ℝ) :
    IsWeakCRSolutionHalfOn q Ω Λ J DJ S (c • ξ) (c • η) := by
  refine ⟨h.memLpLoc.const_smul c, h.locallyIntegrableOn.smul c, fun φ hφ => ⟨?_, ?_⟩⟩
  · simpa only [IntegrableOn, Pi.smul_apply, inner_smul_right] using
      (h.integrableOn_inner_crFormalAdjoint φ hφ).const_mul c
  · simp only [Pi.smul_apply, inner_smul_right, integral_const_mul,
      h.setIntegral_inner_crFormalAdjoint φ hφ]

/-- The weak equation up to the boundary is compatible with negation of `(ξ, η)`. -/
theorem neg (h : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η) :
    IsWeakCRSolutionHalfOn q Ω Λ J DJ S (-ξ) (-η) := by
  simpa using h.const_smul (-1)

/-- The weak equation up to the boundary is additive in `(ξ, η)`. -/
theorem add (h : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η)
    (h' : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ' η') :
    IsWeakCRSolutionHalfOn q Ω Λ J DJ S (ξ + ξ') (η + η') := by
  refine ⟨h.memLpLoc.add h'.memLpLoc, h.locallyIntegrableOn.add h'.locallyIntegrableOn,
    fun φ hφ => ⟨?_, ?_⟩⟩
  · simp only [Pi.add_apply, inner_add_right]
    exact (h.integrableOn_inner_crFormalAdjoint φ hφ).add
      (h'.integrableOn_inner_crFormalAdjoint φ hφ)
  · simp only [Pi.add_apply, inner_add_right]
    rw [integral_add (h.integrableOn_inner_crFormalAdjoint φ hφ)
        (h'.integrableOn_inner_crFormalAdjoint φ hφ),
      integral_add (integrableOn_im_pos_inner h.locallyIntegrableOn φ)
        (integrableOn_im_pos_inner h'.locallyIntegrableOn φ),
      h.setIntegral_inner_crFormalAdjoint φ hφ, h'.setIntegral_inner_crFormalAdjoint φ hφ]

/-- The weak equation up to the boundary is compatible with subtraction of `(ξ, η)`. -/
theorem sub (h : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η)
    (h' : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ' η') :
    IsWeakCRSolutionHalfOn q Ω Λ J DJ S (ξ - ξ') (η - η') := by
  simpa [sub_eq_add_neg] using h.add h'.neg

/-- **Restriction to the interior.** A weak solution up to the boundary is a weak solution of the
interior equation `TauCeti.IsWeakCRSolution` on the open upper part `Ω ∩ {0 < t}`: a test
function supported there vanishes on `ℝ`, so it is admissible for every boundary condition. -/
theorem isWeakCRSolution (h : IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η) :
    IsWeakCRSolution q Ω.upperHalf J DJ S ξ η := by
  have hsub : (Ω.upperHalf : Set ℂ) ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} :=
    fun z hz => ⟨(Opens.mem_upperHalf.1 hz).1, (Opens.mem_upperHalf.1 hz).2.le⟩
  refine isWeakCRSolution_iff.2
    ⟨h.memLpLoc.mono_set hsub, h.locallyIntegrableOn.mono_set hsub, fun φ => ?_⟩
  have hout {z : ℂ} (hz : z ∉ {z : ℂ | 0 < z.im}) : z ∉ tsupport (φ : ℂ → V) :=
    fun h' => hz (Opens.mem_upperHalf.1 (φ.tsupport_subset h')).2
  have hφΛ (s : ℝ) : (φ : ℂ → V) s ∈ Λ := by
    rw [image_eq_zero_of_notMem_tsupport (hout (by simp))]
    exact Λ.zero_mem
  let ψ : 𝓓(Ω, V) := ⟨φ, φ.contDiff, φ.hasCompactSupport,
    φ.tsupport_subset.trans (hsub.trans inter_subset_left)⟩
  have hψ : (ψ : ℂ → V) = φ := rfl
  obtain ⟨hint, heq⟩ := h.2.2 ψ hφΛ
  rw [hψ] at hint heq
  have hzero {f : ℂ → ℝ} (hf : ∀ z, z ∉ tsupport (φ : ℂ → V) → f z = 0) :
      ∀ z, z ∉ {z : ℂ | 0 < z.im} → f z = 0 := fun z hz => hf z (hout hz)
  have hl := hzero (f := fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ)
    fun z hz => by simp [crFormalAdjoint_of_notMem_tsupport hz]
  have hr := hzero (f := fun z => ⟪(φ : ℂ → V) z, η z⟫_ℝ)
    fun z hz => by simp [image_eq_zero_of_notMem_tsupport hz]
  refine ⟨(integrableOn_iff_integrable_of_support_subset fun z hz => ?_).1 hint, ?_⟩
  · by_contra hz'
    exact hz (hl z hz')
  · rwa [setIntegral_eq_integral_of_forall_compl_eq_zero hl,
      setIntegral_eq_integral_of_forall_compl_eq_zero hr] at heq

end IsWeakCRSolutionHalfOn

/-- `ξ = 0` is a weak solution of the homogeneous equation for every boundary condition. -/
@[simp]
theorem isWeakCRSolutionHalfOn_zero : IsWeakCRSolutionHalfOn q Ω Λ J DJ S 0 0 :=
  ⟨memLpLoc_zero, locallyIntegrableOn_zero, fun φ _ => by simp⟩

/-- Replacing the coefficients, the solution or the right-hand side by functions agreeing with
them almost everywhere on `Ω ∩ {0 ≤ t}` does not change the weak equation up to the boundary. -/
theorem isWeakCRSolutionHalfOn_congr_ae
    (hJ : J =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] J')
    (hDJ : DJ =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] DJ')
    (hS : S =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] S')
    (hξ : ξ =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] ξ')
    (hη : η =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] η') :
    IsWeakCRSolutionHalfOn q Ω Λ J DJ S ξ η ↔ IsWeakCRSolutionHalfOn q Ω Λ J' DJ' S' ξ' η' := by
  have hH : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
  have hrhs (φ : 𝓓(Ω, V)) : ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, η z⟫_ℝ =
      ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, η' z⟫_ℝ := by
    refine setIntegral_congr_ae hH ?_
    filter_upwards [ae_imp_of_ae_restrict hη] with z hz hz0
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · rw [hz ⟨hzΩ, le_of_lt hz0⟩]
    · simp [image_eq_zero_of_notMem_tsupport fun h' => hzΩ (φ.tsupport_subset h')]
  have hlhs (φ : 𝓓(Ω, V)) : (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) =ᵐ[volume.restrict
      {z : ℂ | 0 < z.im}] fun z => ⟪crFormalAdjoint J' DJ' S' φ z, ξ' z⟫_ℝ := by
    refine (ae_restrict_iff' hH).2 ?_
    filter_upwards [ae_imp_of_ae_restrict hJ, ae_imp_of_ae_restrict hDJ,
      ae_imp_of_ae_restrict hS, ae_imp_of_ae_restrict hξ] with z hJz hDJz hSz hξz hz0
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · have hz : z ∈ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im} := ⟨hzΩ, le_of_lt hz0⟩
      simp only [crFormalAdjoint_def, hJz hz, hDJz hz, hSz hz, hξz hz]
    · have hz : z ∉ tsupport (φ : ℂ → V) := fun h' => hzΩ (φ.tsupport_subset h')
      simp [crFormalAdjoint_of_notMem_tsupport hz]
  simp only [isWeakCRSolutionHalfOn_iff, hrhs, integral_congr_ae (hlhs _),
    IntegrableOn, integrable_congr (hlhs _)]
  exact and_congr ⟨fun h => h.congr_ae hξ, fun h => h.congr_ae hξ.symm⟩
    (and_congr ⟨fun h => h.congr hη, fun h => h.congr hη.symm⟩ Iff.rfl)

/-! ### Classical solutions -/

/-- Green's formula for `TauCeti.crFormalAdjoint` on the half-plane with `C¹` data: the
`∂_t J` terms of `D*` and of the integration by parts cancel, leaving
`∫_{0<t} ⟪D* φ, ξ⟫ = ∫_{0<t} ⟪φ, ∂_s ξ + J ∂_t ξ + S ξ⟫ + ∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds`. -/
private theorem setIntegral_im_pos_inner_crFormalAdjoint_of_contDiffOn {φ ξ : ℂ → V} {U : Set ℂ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hU : IsOpen U) (hξ : ContDiffOn ℝ 1 ξ U)
    (hJ : ContDiffOn ℝ 1 J U) (hS : ContinuousOn S U) (hφU : tsupport φ ⊆ U) :
    IntegrableOn (fun z => ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ) {z : ℂ | 0 < z.im} ∧
      ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ =
        (∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ) +
          ∫ s : ℝ, ⟪φ s, J s (ξ s)⟫_ℝ := by
  have hint {f : ℂ → ℝ} (hf : ContinuousOn f U) (h0 : ∀ z, z ∉ tsupport φ → f z = 0) :
      Integrable f :=
    ((hf.mono hφU).integrableOn_compact hφc).integrable_of_forall_notMem_eq_zero h0
  have hdφ := hφ.continuous_fderiv one_ne_zero
  have hdξ := hξ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hdJ := hJ.continuousOn_fderiv_of_isOpen hU le_rfl
  have hadj {A : ℂ → V →L[ℝ] V} (hA : ContinuousOn A U) :
      ContinuousOn (fun z => ContinuousLinearMap.adjoint (A z)) U :=
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V) (F := V)).continuous.comp_continuousOn hA
  set G : ℂ → ℝ := fun z => ⟪fderiv ℝ φ z 1 + ContinuousLinearMap.adjoint (J z)
    (fderiv ℝ φ z I) - ContinuousLinearMap.adjoint (S z) (φ z), ξ z⟫_ℝ
  set P : ℂ → ℝ := fun z => ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ
  set T : ℂ → ℝ := fun z => ⟪φ z, fderiv ℝ J z I (ξ z)⟫_ℝ
  have hpt (z : ℂ) : ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ = -G z - T z := by
    simp only [G, T, inner_crFormalAdjoint, inner_add_left, inner_sub_left,
      ContinuousLinearMap.adjoint_inner_left]
    ring
  have hG : Integrable G := hint
    ((((hdφ.clm_apply continuous_const).continuousOn.add ((hadj hJ.continuousOn).clm_apply
      (hdφ.clm_apply continuous_const).continuousOn)).sub
      ((hadj hS).clm_apply hφ.continuous.continuousOn)).inner hξ.continuousOn)
    fun z hz => by simp [G, fderiv_of_notMem_tsupport ℝ hz, image_eq_zero_of_notMem_tsupport hz]
  have hP : Integrable P := hint
    (hφ.continuous.continuousOn.inner (((hdξ.clm_apply continuousOn_const).add
      (hJ.continuousOn.clm_apply (hdξ.clm_apply continuousOn_const))).add
      (hS.clm_apply hξ.continuousOn)))
    fun z hz => by simp [P, image_eq_zero_of_notMem_tsupport hz]
  have hT : Integrable T := hint
    (hφ.continuous.continuousOn.inner
      ((hdJ.clm_apply continuousOn_const).clm_apply hξ.continuousOn))
    fun z hz => by simp [T, image_eq_zero_of_notMem_tsupport hz]
  have hgreen := setIntegral_im_pos_inner_cauchyRiemann_adjoint hφ hφc hU hξ hJ hS hφU
  have hsplit : ∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) +
      S z (ξ z) + fderiv ℝ J z I (ξ z)⟫_ℝ =
      (∫ z in {z : ℂ | 0 < z.im}, P z) + ∫ z in {z : ℂ | 0 < z.im}, T z := by
    simp only [inner_add_right (x := φ _) (y := _ + _ + _)]
    exact integral_add hP.integrableOn hT.integrableOn
  refine ⟨(hG.neg.sub hT).integrableOn.congr_fun (fun z _ => (hpt z).symm)
    (measurableSet_lt measurable_const measurable_im), ?_⟩
  simp_rw [hpt]
  rw [integral_sub (f := fun z => -G z) hG.neg.integrableOn hT.integrableOn, integral_neg, hgreen, hsplit]
  ring

/-- **Classical solutions are weak solutions up to the boundary.** Let `J` be `C¹` on `Ω`, with
`DJ = fderiv ℝ J`, and `S` continuous on `Ω`. If `ξ` is `C¹` on `Ω`, solves
`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω ∩ {0 < t}`, and on `ℝ ∩ Ω` takes values in a subspace `Λ` with
`⟪Λ, J(s) Λ⟫ = 0`, then `ξ` is a weak solution up to the boundary for every exponent `q`. The
boundary term `∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds` of Green's formula vanishes because the admissible test
functions take values in `Λ` on `ℝ`. -/
theorem isWeakCRSolutionHalfOn_of_contDiffOn (hJ : ContDiffOn ℝ 1 J Ω) (hS : ContinuousOn S Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hη : ∀ z ∈ Ω.upperHalf, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z) = η z)
    (hξΛ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ξ s ∈ Λ)
    (hJΛ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ v ∈ Λ, ∀ w ∈ Λ, ⟪v, J s w⟫_ℝ = 0) :
    IsWeakCRSolutionHalfOn q Ω Λ J (fderiv ℝ J) S ξ η := by
  have hH : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
  set L : ℂ → V := fun z => fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)
  have hL : ContinuousOn L Ω := by
    have hdξ := hξ.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl
    exact ((hdξ.clm_apply continuousOn_const).add
      (hJ.continuousOn.clm_apply (hdξ.clm_apply continuousOn_const))).add
      (hS.clm_apply hξ.continuousOn)
  -- `η = L` on the upper part, and the real axis is null.
  have hLη : L =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] η := by
    rw [Measure.restrict_congr_set (ae_eq_set_inter (by rfl) (Complex.setOf_le_im_ae_eq 0))]
    exact (ae_restrict_iff' (Ω.isOpen.measurableSet.inter hH)).2
      (.of_forall fun z hz => hη z (Opens.mem_upperHalf.2 hz))
  refine ⟨(hξ.continuousOn.mono inter_subset_left).memLpLoc,
    ((hL.mono inter_subset_left).locallyIntegrableOn
      (Ω.isOpen.measurableSet.inter (measurableSet_le measurable_const measurable_im))).congr hLη,
    fun φ hφΛ => ?_⟩
  obtain ⟨hint, heq⟩ := setIntegral_im_pos_inner_crFormalAdjoint_of_contDiffOn
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport Ω.isOpen hξ hJ hS φ.tsupport_subset
  have hbdry (s : ℝ) : ⟪(φ : ℂ → V) s, J s (ξ s)⟫_ℝ = 0 := by
    by_cases hs : (s : ℂ) ∈ Ω
    · exact hJΛ s hs _ (hφΛ s) _ (hξΛ s hs)
    · simp [image_eq_zero_of_notMem_tsupport fun h => hs (φ.tsupport_subset h)]
  refine ⟨hint, heq.trans ?_⟩
  simp only [hbdry, integral_zero, add_zero]
  refine setIntegral_congr_fun hH fun z hz => ?_
  by_cases hzΩ : z ∈ (Ω : Set ℂ)
  · simp only [← hη z (Opens.mem_upperHalf.2 ⟨hzΩ, hz⟩)]
  · simp [image_eq_zero_of_notMem_tsupport fun h => hzΩ (φ.tsupport_subset h)]

/-! ### Checks: `J = i`, `S = 0` and the real boundary condition on `ℂ` -/

/-- A smooth real bump on `ℂ`, equal to `1` near `0`, as a test function. -/
private def realBump (c : ℂ) : 𝓓((⊤ : Opens ℂ), ℂ) :=
  let ψ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  ⟨fun z => c * (ψ z : ℂ), contDiff_const.mul (ofRealCLM.contDiff.comp ψ.contDiff),
    (ψ.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero).mul_left,
    subset_univ _⟩

/-- The boundary integral of the bump is positive. -/
private theorem integral_realBump_pos :
    0 < ∫ s : ℝ, ((realBump 1 : ℂ → ℂ) s).re := by
  let ψ : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩
  have hψ (s : ℝ) : ((realBump 1 : ℂ → ℂ) s).re = ψ s := by simp [realBump, ψ]
  simp_rw [hψ]
  refine (ψ.continuous.comp continuous_ofReal).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (ψ.hasCompactSupport.comp_isClosedEmbedding isometry_ofReal.isClosedEmbedding)
    (fun s => ψ.nonneg) (x := 0) ?_
  simp [ψ.one_of_mem_closedBall (Metric.mem_closedBall_self (by norm_num : (0 : ℝ) ≤ 1))]

/-- Green's formula of `TauCeti.isWeakCRSolutionHalfOn_of_contDiffOn` for `J = i`, `S = 0` and a
constant field `c`: only the boundary term survives. -/
private theorem setIntegral_inner_crFormalAdjoint_I_const (φ : 𝓓((⊤ : Opens ℂ), ℂ)) (c : ℂ) :
    ∫ z in {z : ℂ | 0 < z.im},
        ⟪crFormalAdjoint (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 φ z, c⟫_ℝ =
      ∫ s : ℝ, ⟪(φ : ℂ → ℂ) s, I * c⟫_ℝ := by
  have h := (setIntegral_im_pos_inner_crFormalAdjoint_of_contDiffOn (J := fun _ =>
    I • ContinuousLinearMap.id ℝ ℂ) (S := 0) (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
    isOpen_univ (contDiffOn_const (c := c)) contDiffOn_const continuousOn_const
    (subset_univ _)).2
  simpa [fderiv_const] using h

/-- **Check: `ξ = z` is a weak solution.** For `J = i`, `S = 0` and the real boundary condition,
the identity `ξ(z) = z` is holomorphic and real on `ℝ`, so it solves the homogeneous weak equation
up to the boundary. -/
theorem isWeakCRSolutionHalfOn_id :
    IsWeakCRSolutionHalfOn q ⊤ (Submodule.span ℝ {(1 : ℂ)})
      (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 id 0 := by
  have h := isWeakCRSolutionHalfOn_of_contDiffOn (q := q) (Ω := ⊤)
    (Λ := Submodule.span ℝ {(1 : ℂ)}) (J := fun _ => I • ContinuousLinearMap.id ℝ ℂ) (S := 0)
    (η := 0) contDiffOn_const continuousOn_const contDiff_id.contDiffOn
    (fun z _ => by simp) (fun s _ => Submodule.mem_span_singleton.2 ⟨s, by simp⟩) ?_
  · simpa [fderiv_const] using h
  rintro s - v hv w hw
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hw
  simp

/-- **Check: the boundary condition is encoded by the test functions.** For `J = i`, `S = 0` and
the real boundary condition, the constant `ξ = i` solves `∂_s ξ + i ∂_t ξ = 0` in the interior but
is not real on `ℝ`, and it is not a weak solution up to the boundary: for a real bump `φ = χ` the
boundary term is `⟪χ, i · i⟫ = -χ`, with nonzero integral. -/
theorem not_isWeakCRSolutionHalfOn_const_I :
    ¬ IsWeakCRSolutionHalfOn q ⊤ (Submodule.span ℝ {(1 : ℂ)})
      (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 (fun _ => I) 0 := by
  intro h
  have hφ (s : ℝ) : (realBump 1 : ℂ → ℂ) s ∈ Submodule.span ℝ {(1 : ℂ)} :=
    Submodule.mem_span_singleton.2 ⟨((realBump 1 : ℂ → ℂ) s).re, by simp [realBump]⟩
  have h1 := h.setIntegral_inner_crFormalAdjoint _ hφ
  rw [setIntegral_inner_crFormalAdjoint_I_const] at h1
  have h2 (s : ℝ) : ⟪(realBump 1 : ℂ → ℂ) s, I * I⟫_ℝ = -((realBump 1 : ℂ → ℂ) s).re := by
    simp [Complex.inner]
  simp only [h2, integral_neg, Pi.zero_apply, inner_zero_right, integral_zero, neg_eq_zero] at h1
  exact integral_realBump_pos.ne' h1

/-- **Check: the test functions must be restricted on `ℝ`.** For `J = i` and `S = 0`, the
constant `ξ = 1` is holomorphic and real on `ℝ`, but the weak identity `∫ ⟪D* φ, 1⟫ = 0` fails
for the test function `φ = i χ`, which is not real on `ℝ`: the boundary term is
`∫_ℝ ⟪i χ, i⟫ = ∫_ℝ χ ≠ 0`. -/
theorem exists_setIntegral_inner_crFormalAdjoint_one_ne_zero :
    ∃ φ : 𝓓((⊤ : Opens ℂ), ℂ), ∫ z in {z : ℂ | 0 < z.im},
      ⟪crFormalAdjoint (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 φ z, 1⟫_ℝ ≠ 0 := by
  refine ⟨realBump I, ?_⟩
  rw [setIntegral_inner_crFormalAdjoint_I_const]
  have h (s : ℝ) : ⟪(realBump I : ℂ → ℂ) s, I * 1⟫_ℝ = ((realBump 1 : ℂ → ℂ) s).re := by
    simp [Complex.inner, realBump]
  simp only [h]
  exact integral_realBump_pos.ne'

end TauCeti
