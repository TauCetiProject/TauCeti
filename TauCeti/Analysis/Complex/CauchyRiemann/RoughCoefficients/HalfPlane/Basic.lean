/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Complex.ReImTopology
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Complex.Wirtinger.HalfPlaneAdjoint.Basic
import TauCeti.Analysis.Complex.Wirtinger.HalfPlaneAdjoint.Dual
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Weak solutions of real Cauchy–Riemann equations on half-discs with a boundary condition

Let `Ω ⊆ ℂ` be open, write `z = s + i t`, and consider the part `Ω ∩ {0 ≤ t}` of `Ω` in the
closed upper half-plane. Let `V` be a real inner product space, `Λ ⊆ V` a real subspace (the
space of boundary values of the test functions, `ℝⁿ ⊆ ℂⁿ` in the local model of a totally real
boundary condition) and `J, S : ℂ → (V →L[ℝ] V)` coefficient fields, with `DJ` standing for the
(weak) derivative of `J`. This file defines the weak form of `∂_s ξ + J ∂_t ξ + S ξ = η` on
`Ω ∩ {0 < t}` with the boundary condition carried by `Λ`,
`TauCeti.IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η`: `ξ` is locally `L^q` and `η` locally
integrable on `Ω ∩ {0 ≤ t}`, and for every test function `φ ∈ 𝓓(Ω, V)` with `φ(s) ∈ Λ` for real
`s` the pairing `⟪D* φ, ξ⟫` is integrable on `{0 < t}` with

`∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, η⟫`,

where `D* φ = -∂_s φ - Jᵀ ∂_t φ - (∂_t J)ᵀ φ + Sᵀ φ` is `TauCeti.crFormalAdjoint J DJ S`. The test
functions are compactly supported in `Ω` but are not required to vanish on `ℝ`; only their values
there are restricted. This is McDuff–Salamon's weak equation (B.4.3), with the zeroth-order term
added, in the normalization of the interior weak equation `TauCeti.IsWeakCRSolution`.

No condition on `ξ` along `ℝ` is part of the definition. By Green's formula the boundary term of
a classical solution is `∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds`, so restricting the test functions to
`φ(s) ∈ Λ` weakly imposes `⟪Λ, J(s) ξ(s)⟫ = 0`, that is `J(s) ξ(s) ∈ Λᗮ`. This is the boundary
condition `ξ(s) ∈ Λ` exactly when `J(s)⁻¹ Λᗮ = Λ`, for instance when `J(s)` is invertible and
`V = Λ ⊕ J(s) Λ` is an orthogonal decomposition, as for `J(s) = i` and `Λ = ℝⁿ ⊆ ℂⁿ` (the case of
McDuff–Salamon and of the Checks below). For general `(J, Λ)` the two conditions differ: `Λ = ⊥`
imposes nothing.

## Main results

* Linearity in `(ξ, η)` (`TauCeti.IsWeakCRSolutionHalf.add`, `.const_smul`, `.neg`, `.sub`,
  `TauCeti.isWeakCRSolutionHalf_zero`), restriction to open sets with smaller part in
  `{0 ≤ t}` (`TauCeti.IsWeakCRSolutionHalf.mono`), lowering the exponent
  (`TauCeti.IsWeakCRSolutionHalf.mono_exponent`) and invariance under changes of the data on
  null subsets of `Ω ∩ {0 ≤ t}` (`TauCeti.isWeakCRSolutionHalf_congr_ae`).
* `TauCeti.IsWeakCRSolutionHalf.isWeakCRSolution`: a weak solution up to the boundary is a weak
  solution of the interior equation on the open upper part `Ω ∩ {0 < t}`.
* `TauCeti.isWeakCRSolutionHalf_of_contDiffOn`: for `C¹` coefficients `J` with `DJ = fderiv ℝ J`
  and continuous `S`, a `C¹` field `ξ` solving the equation classically on `Ω ∩ {0 < t}`, with
  `⟪Λ, J(s) ξ(s)⟫ = 0` for real `s ∈ Ω`, is a weak solution;
  `TauCeti.isWeakCRSolutionHalf_of_contDiffOn_of_mem` is the case `ξ(s) ∈ Λ`, `⟪Λ, J(s) Λ⟫ = 0`.
  Conversely (`TauCeti.isWeakCRSolutionHalf_iff_of_contDiffOn`), for finite-dimensional `V` and
  `η` continuous on `Ω ∩ {0 < t}`, a `C¹` weak solution solves the equation classically on
  `Ω ∩ {0 < t}` and satisfies `J(s) ξ(s) ∈ Λᗮ` on `ℝ ∩ Ω`.
* Checks for `V = ℂ`, `J = i`, `S = 0`, `Λ = ℝ` on any open `Ω` (meeting `ℝ` for the negative
  checks): `ξ = z` is a weak solution of the homogeneous
  equation (`TauCeti.isWeakCRSolutionHalf_id`); the constant `ξ = i`, which solves the equation
  in the interior but violates the boundary condition, is not
  (`TauCeti.not_isWeakCRSolutionHalf_const_I`); and without the restriction on the boundary
  values of the test functions even the constant `ξ = 1` would fail
  (`TauCeti.exists_setIntegral_inner_crFormalAdjoint_one_ne_zero`).

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  Appendix B.4, equation (B.4.3) and Lemma B.4.6.
-/

public noncomputable section

open MeasureTheory TopologicalSpace Complex Set Filter
open scoped InnerProductSpace ContDiff Distributions ENNReal Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω Ω' : Opens ℂ} {Λ : Submodule ℝ V} {q r : ℝ≥0∞}
  {J J' S S' : ℂ → V →L[ℝ] V} {DJ DJ' : ℂ → ℂ →L[ℝ] V →L[ℝ] V} {ξ ξ' η η' : ℂ → V}

/-- `IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η` says that `ξ` is a **weak solution up to the real
axis** of `∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω ∩ {0 ≤ t}`, with `DJ` standing for the weak
derivative of `J` and `Λ` the subspace of admissible boundary values of the test functions: `ξ` is
locally `L^q` and `η` is locally integrable on `Ω ∩ {0 ≤ t}`, and for every test function
`φ ∈ 𝓓(Ω, V)` taking values in `Λ` on `ℝ` the pairing `⟪D* φ, ξ⟫` is integrable on the upper
half-plane with

`∫_{0 < t} ⟪D* φ, ξ⟫ = ∫_{0 < t} ⟪φ, η⟫`,

where `D*` is `TauCeti.crFormalAdjoint J DJ S`. The test functions need not vanish on `ℝ`. Through
the boundary term `∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds` of Green's formula this weakly imposes
`⟪Λ, J(s) ξ(s)⟫ = 0` on `ℝ ∩ Ω`, which is the boundary condition `ξ(s) ∈ Λ` when
`J(s)⁻¹ Λᗮ = Λ` (for instance `J(s) = i` and `Λ = ℝⁿ ⊆ ℂⁿ`). As for
`TauCeti.IsWeakCRSolution`, the integrability is part of the definition and the coefficients are
unconstrained. -/
def IsWeakCRSolutionHalf (q : ℝ≥0∞) (Ω : Opens ℂ) (Λ : Submodule ℝ V) (J : ℂ → V →L[ℝ] V)
    (DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V) (S : ℂ → V →L[ℝ] V) (ξ η : ℂ → V) : Prop :=
  MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ ∧
    LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
    ∀ φ : 𝓓(Ω, V), (∀ s : ℝ, (φ : ℂ → V) s ∈ Λ) →
      IntegrableOn (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) {z : ℂ | 0 < z.im} ∧
        ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ =
          ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, η z⟫_ℝ

/-- The constructor-and-eliminator form of `TauCeti.IsWeakCRSolutionHalf`. -/
theorem isWeakCRSolutionHalf_iff : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η ↔
    MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ ∧
      LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ∧
      ∀ φ : 𝓓(Ω, V), (∀ s : ℝ, (φ : ℂ → V) s ∈ Λ) →
        IntegrableOn (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) {z : ℂ | 0 < z.im} ∧
          ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ =
            ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, η z⟫_ℝ :=
  Iff.rfl

namespace IsWeakCRSolutionHalf

/-- A weak solution up to the boundary is locally `L^q` up to the boundary. -/
theorem memLpLoc (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) :
    MemLpLoc q ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) ξ := h.1

/-- The right-hand side of a weak equation up to the boundary is locally integrable up to the
boundary. -/
theorem locallyIntegrableOn (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) :
    LocallyIntegrableOn η ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) := h.2.1

/-- The pairing of a test function with the right-hand side of a weak equation up to the
boundary is integrable on the upper half-plane. -/
theorem integrableOn_inner (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) (φ : 𝓓(Ω, V)) :
    IntegrableOn (fun z => ⟪(φ : ℂ → V) z, η z⟫_ℝ) {z : ℂ | 0 < z.im} :=
  IntegrableOn.mono_set (φ.integrable_inner (h.locallyIntegrableOn.restrict_of_inter Ω.isOpen
    (isClosed_le continuous_const continuous_im))) fun _ hz => le_of_lt hz

/-- The pairing of the formal adjoint of an admissible test function with a weak solution is
integrable on the upper half-plane. -/
theorem integrableOn_inner_crFormalAdjoint (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η)
    (φ : 𝓓(Ω, V)) (hφ : ∀ s : ℝ, (φ : ℂ → V) s ∈ Λ) :
    IntegrableOn (fun z => ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ) {z : ℂ | 0 < z.im} :=
  (h.2.2 φ hφ).1

/-- The integral identity defining a weak solution up to the boundary. -/
theorem setIntegral_inner_crFormalAdjoint (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η)
    (φ : 𝓓(Ω, V)) (hφ : ∀ s : ℝ, (φ : ℂ → V) s ∈ Λ) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ =
      ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, η z⟫_ℝ :=
  (h.2.2 φ hφ).2

/-- A weak solution on `Ω` is a weak solution on every open set `Ω'` whose part in the closed
upper half-plane lies in that of `Ω`, with the same boundary condition: a test function on `Ω'`
agrees near `{0 ≤ t}` with its product by a cutoff, which is a test function on `Ω`. -/
theorem mono (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η)
    (hΩ : (Ω' : Set ℂ) ∩ {z | 0 ≤ z.im} ⊆ (Ω : Set ℂ) ∩ {z | 0 ≤ z.im}) :
    IsWeakCRSolutionHalf q Ω' Λ J DJ S ξ η := by
  refine ⟨h.memLpLoc.mono_set hΩ, h.locallyIntegrableOn.mono_set hΩ, fun φ hφ => ?_⟩
  have hH : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
  obtain ⟨ψ, hψ, -, hψ1, hψc, hψΩ⟩ := (φ.hasCompactSupport.isCompact.inter_right
    (isClosed_le continuous_const continuous_im)).exists_contDiff_cutoff_eventuallyEq_one Ω.isOpen
    fun z hz => (hΩ ⟨φ.tsupport_subset hz.1, hz.2⟩).1
  let φ' : 𝓓(Ω, V) := ⟨fun z => ψ z • (φ : ℂ → V) z, hψ.smul φ.contDiff,
    hψc.smul_right, (tsupport_smul_subset_left _ _).trans hψΩ⟩
  have hφ' {z : ℂ} (hz : 0 < z.im) : (φ' : ℂ → V) =ᶠ[𝓝 z] φ := by
    by_cases hzφ : z ∈ tsupport (φ : ℂ → V)
    · filter_upwards [hψ1 z ⟨hzφ, hz.le⟩] with w hw
      simp [φ', hw]
    · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hzφ] with w hw
      simp [φ', hw]
  have hadj {z : ℂ} (hz : z ∈ {z : ℂ | 0 < z.im}) :
      ⟪crFormalAdjoint J DJ S φ' z, ξ z⟫_ℝ = ⟪crFormalAdjoint J DJ S φ z, ξ z⟫_ℝ := by
    simp only [crFormalAdjoint_def, (hφ' hz).fderiv_eq, (hφ' hz).eq_of_nhds]
  have hrhs {z : ℂ} (hz : z ∈ {z : ℂ | 0 < z.im}) :
      ⟪(φ' : ℂ → V) z, η z⟫_ℝ = ⟪(φ : ℂ → V) z, η z⟫_ℝ := by
    rw [(hφ' hz).eq_of_nhds]
  obtain ⟨hint, heq⟩ := h.2.2 φ' fun s => Λ.smul_mem (ψ s) (hφ s)
  exact ⟨hint.congr_fun (fun z hz => hadj hz) hH, by
    rwa [setIntegral_congr_fun hH fun z hz => hadj hz,
      setIntegral_congr_fun hH fun z hz => hrhs hz] at heq⟩

/-- A weak solution for the exponent `q` is a weak solution for every smaller exponent. -/
theorem mono_exponent (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) (hrq : r ≤ q) :
    IsWeakCRSolutionHalf r Ω Λ J DJ S ξ η :=
  ⟨h.memLpLoc.mono_exponent hrq, h.locallyIntegrableOn, h.2.2⟩

/-- The weak equation up to the boundary is homogeneous in `(ξ, η)`. -/
theorem const_smul (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) (c : ℝ) :
    IsWeakCRSolutionHalf q Ω Λ J DJ S (c • ξ) (c • η) := by
  refine ⟨h.memLpLoc.const_smul c, h.locallyIntegrableOn.smul c, fun φ hφ => ⟨?_, ?_⟩⟩
  · simpa only [IntegrableOn, Pi.smul_apply, inner_smul_right] using
      (h.integrableOn_inner_crFormalAdjoint φ hφ).const_mul c
  · simp only [Pi.smul_apply, inner_smul_right, integral_const_mul,
      h.setIntegral_inner_crFormalAdjoint φ hφ]

/-- The weak equation up to the boundary is compatible with negation of `(ξ, η)`. -/
theorem neg (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) :
    IsWeakCRSolutionHalf q Ω Λ J DJ S (-ξ) (-η) := by
  simpa using h.const_smul (-1)

/-- The weak equation up to the boundary is additive in `(ξ, η)`. -/
theorem add (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η)
    (h' : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ' η') :
    IsWeakCRSolutionHalf q Ω Λ J DJ S (ξ + ξ') (η + η') := by
  refine ⟨h.memLpLoc.add h'.memLpLoc, h.locallyIntegrableOn.add h'.locallyIntegrableOn,
    fun φ hφ => ⟨?_, ?_⟩⟩
  · simp only [Pi.add_apply, inner_add_right]
    exact (h.integrableOn_inner_crFormalAdjoint φ hφ).add
      (h'.integrableOn_inner_crFormalAdjoint φ hφ)
  · simp only [Pi.add_apply, inner_add_right]
    rw [integral_add (h.integrableOn_inner_crFormalAdjoint φ hφ)
        (h'.integrableOn_inner_crFormalAdjoint φ hφ),
      integral_add (h.integrableOn_inner φ) (h'.integrableOn_inner φ),
      h.setIntegral_inner_crFormalAdjoint φ hφ, h'.setIntegral_inner_crFormalAdjoint φ hφ]

/-- The weak equation up to the boundary is compatible with subtraction of `(ξ, η)`. -/
theorem sub (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η)
    (h' : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ' η') :
    IsWeakCRSolutionHalf q Ω Λ J DJ S (ξ - ξ') (η - η') := by
  simpa [sub_eq_add_neg] using h.add h'.neg

/-- **Restriction to the interior.** A weak solution up to the boundary is a weak solution of the
interior equation `TauCeti.IsWeakCRSolution` on the open upper part `Ω ∩ {0 < t}`: a test
function supported there vanishes on `ℝ`, so it is admissible for every boundary condition. -/
theorem isWeakCRSolution (h : IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η) :
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

end IsWeakCRSolutionHalf

/-- `ξ = 0` is a weak solution of the homogeneous equation for every boundary condition. -/
@[simp]
theorem isWeakCRSolutionHalf_zero : IsWeakCRSolutionHalf q Ω Λ J DJ S 0 0 :=
  ⟨memLpLoc_zero, locallyIntegrableOn_zero, fun φ _ => by simp⟩

/-- Replacing the coefficients, the solution or the right-hand side by functions agreeing with
them almost everywhere on `Ω ∩ {0 ≤ t}` does not change the weak equation up to the boundary. -/
theorem isWeakCRSolutionHalf_congr_ae
    (hJ : J =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] J')
    (hDJ : DJ =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] DJ')
    (hS : S =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] S')
    (hξ : ξ =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] ξ')
    (hη : η =ᵐ[volume.restrict ((Ω : Set ℂ) ∩ {z | 0 ≤ z.im})] η') :
    IsWeakCRSolutionHalf q Ω Λ J DJ S ξ η ↔ IsWeakCRSolutionHalf q Ω Λ J' DJ' S' ξ' η' := by
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
  simp only [isWeakCRSolutionHalf_iff, hrhs, integral_congr_ae (hlhs _),
    IntegrableOn, integrable_congr (hlhs _)]
  exact and_congr ⟨fun h => h.congr_ae hξ, fun h => h.congr_ae hξ.symm⟩
    (and_congr ⟨fun h => h.congr hη, fun h => h.congr hη.symm⟩ Iff.rfl)

/-! ### Classical solutions -/

/-- **Classical solutions are weak solutions up to the boundary.** Let `J` be `C¹` on `Ω`, with
`DJ = fderiv ℝ J`, and `S` continuous on `Ω`. If `ξ` is `C¹` on `Ω`, solves
`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω ∩ {0 < t}`, and `⟪Λ, J(s) ξ(s)⟫ = 0` on `ℝ ∩ Ω`, then `ξ` is a
weak solution up to the boundary for every exponent `q`: the boundary term
`∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds` of Green's formula vanishes because the admissible test functions
take values in `Λ` on `ℝ`. -/
theorem isWeakCRSolutionHalf_of_contDiffOn (hJ : ContDiffOn ℝ 1 J Ω) (hS : ContinuousOn S Ω)
    (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hη : ∀ z ∈ Ω.upperHalf, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z) = η z)
    (hJξ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ v ∈ Λ, ⟪v, J s (ξ s)⟫_ℝ = 0) :
    IsWeakCRSolutionHalf q Ω Λ J (fderiv ℝ J) S ξ η := by
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
  refine ⟨integrableOn_im_pos_inner_crFormalAdjoint_of_contDiffOn (φ.contDiff.of_le (by simp))
    φ.hasCompactSupport Ω.isOpen hξ.continuousOn hJ hS φ.tsupport_subset, ?_⟩
  rw [setIntegral_im_pos_inner_crFormalAdjoint_of_inner_eq_zero Ω.isOpen
    (φ.contDiff.of_le (by simp)).contDiffOn hξ hJ hS
    (φ.hasCompactSupport.isCompact.inter_right (isClosed_tsupport ξ))
    (inter_subset_left.trans φ.tsupport_subset) fun s hs => hJξ s hs _ (hφΛ s)]
  refine setIntegral_congr_fun hH fun z hz => ?_
  by_cases hzΩ : z ∈ (Ω : Set ℂ)
  · simp only [← hη z (Opens.mem_upperHalf.2 ⟨hzΩ, hz⟩)]
  · simp [image_eq_zero_of_notMem_tsupport fun h => hzΩ (φ.tsupport_subset h)]

/-- **Classical solutions are weak solutions up to the boundary**, for the boundary condition
`ξ(s) ∈ Λ` on `ℝ ∩ Ω` and coefficients with `⟪Λ, J(s) Λ⟫ = 0` there. -/
theorem isWeakCRSolutionHalf_of_contDiffOn_of_mem (hJ : ContDiffOn ℝ 1 J Ω)
    (hS : ContinuousOn S Ω) (hξ : ContDiffOn ℝ 1 ξ Ω)
    (hη : ∀ z ∈ Ω.upperHalf, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z) = η z)
    (hξΛ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ξ s ∈ Λ)
    (hJΛ : ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ v ∈ Λ, ∀ w ∈ Λ, ⟪v, J s w⟫_ℝ = 0) :
    IsWeakCRSolutionHalf q Ω Λ J (fderiv ℝ J) S ξ η :=
  isWeakCRSolutionHalf_of_contDiffOn hJ hS hξ hη fun s hs v hv => hJΛ s hs v hv _ (hξΛ s hs)

/-- **Classical solutions up to the boundary.** For `C¹` coefficients `J` on `Ω`, with
`DJ = fderiv ℝ J`, continuous `S`, a `C¹` field `ξ` and a right-hand side `η` continuous on
`Ω ∩ {0 < t}`, the weak equation up to the boundary is the classical equation
`∂_s ξ + J ∂_t ξ + S ξ = η` on `Ω ∩ {0 < t}` together with the boundary condition
`⟪Λ, J(s) ξ(s)⟫ = 0`, that is `J(s) ξ(s) ∈ Λᗮ`, on `ℝ ∩ Ω`, for every exponent `q`. The boundary
condition is recovered by testing against bumps `ψ • v` with `v ∈ Λ`. -/
theorem isWeakCRSolutionHalf_iff_of_contDiffOn [FiniteDimensional ℝ V] (hJ : ContDiffOn ℝ 1 J Ω)
    (hS : ContinuousOn S Ω) (hξ : ContDiffOn ℝ 1 ξ Ω) (hη : ContinuousOn η Ω.upperHalf) :
    IsWeakCRSolutionHalf q Ω Λ J (fderiv ℝ J) S ξ η ↔
      (∀ z ∈ Ω.upperHalf, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z) = η z) ∧
        ∀ s : ℝ, (s : ℂ) ∈ Ω → ∀ v ∈ Λ, ⟪v, J s (ξ s)⟫_ℝ = 0 := by
  refine ⟨fun h => ?_, fun h => isWeakCRSolutionHalf_of_contDiffOn hJ hS hξ h.1 h.2⟩
  have hH : MeasurableSet {z : ℂ | 0 < z.im} := measurableSet_lt measurable_const measurable_im
  have hU : (Ω.upperHalf : Set ℂ) ⊆ Ω := fun z hz => (Opens.mem_upperHalf.1 hz).1
  have hint := (isWeakCRSolution_iff_of_contDiffOn (hJ.mono hU) (hS.mono hU) (hξ.mono hU)
    hη).1 h.isWeakCRSolution
  have hbdry := (Λ.forall_integral_inner_clm_apply_eq_zero_iff_of_isOpen
    (J := fun _ => ContinuousLinearMap.id ℝ V) (η := fun s : ℝ => J s (ξ s)) Ω.isOpen
    continuousOn_const ((hJ.continuousOn.comp continuous_ofReal.continuousOn
      (mapsTo_preimage _ _)).clm_apply
        (hξ.continuousOn.comp continuous_ofReal.continuousOn (mapsTo_preimage _ _)))).1
  refine ⟨hint, fun s hs v hv =>
    real_inner_comm v _ ▸ hbdry (fun ψ hψ hψc hψΩ hψΛ => ?_) s hs v hv⟩
  let φ : 𝓓(Ω, V) := ⟨ψ, hψ, hψc, hψΩ⟩
  have hφΛ : ∀ s : ℝ, (φ : ℂ → V) s ∈ Λ := hψΛ
  -- The boundary term of Green's formula is all that remains of the weak identity.
  have h1 := setIntegral_im_pos_inner_crFormalAdjoint Ω.isOpen
    (φ.contDiff.of_le (by simp)).contDiffOn hξ hJ hS
    (φ.hasCompactSupport.isCompact.inter_right (isClosed_tsupport ξ))
    (inter_subset_left.trans φ.tsupport_subset)
  have h2 : ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z,
      fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ =
      ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, η z⟫_ℝ := by
    refine setIntegral_congr_fun hH fun z hz => ?_
    by_cases hzΩ : z ∈ (Ω : Set ℂ)
    · rw [hint z (Opens.mem_upperHalf.2 ⟨hzΩ, hz⟩)]
    · simp [image_eq_zero_of_notMem_tsupport fun h => hzΩ (φ.tsupport_subset h)]
  rw [h.setIntegral_inner_crFormalAdjoint φ hφΛ, h2, left_eq_add] at h1
  refine (integral_congr_ae (.of_forall fun s => ?_)).trans h1
  exact real_inner_comm _ _

/-! ### Checks: `J = i`, `S = 0` and the real boundary condition -/

/-- **Check: `ξ = z` is a weak solution.** For `J = i`, `S = 0` and the real boundary condition,
the identity `ξ(z) = z` is holomorphic and real on `ℝ`, so it solves the homogeneous weak equation
up to the boundary on every open set. -/
theorem isWeakCRSolutionHalf_id :
    IsWeakCRSolutionHalf q Ω (Submodule.span ℝ {(1 : ℂ)})
      (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 id 0 := by
  have h := isWeakCRSolutionHalf_of_contDiffOn (q := q) (Ω := Ω)
    (Λ := Submodule.span ℝ {(1 : ℂ)}) (J := fun _ => I • ContinuousLinearMap.id ℝ ℂ) (S := 0)
    (η := 0) contDiffOn_const continuousOn_const contDiff_id.contDiffOn
    (fun z _ => by simp) ?_
  · simpa [fderiv_const] using h
  rintro s - v hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
  simp

/-- **Check: the boundary condition is encoded by the test functions.** For `J = i`, `S = 0` and
the real boundary condition on an open set meeting `ℝ`, the constant `ξ = i` solves
`∂_s ξ + i ∂_t ξ = 0` in the interior but is not real on `ℝ`, and it is not a weak solution up to
the boundary: the boundary condition of `TauCeti.isWeakCRSolutionHalf_iff_of_contDiffOn` fails,
since `⟪1, i · i⟫ = -1`. -/
theorem not_isWeakCRSolutionHalf_const_I (hΩ : ∃ s : ℝ, (s : ℂ) ∈ Ω) :
    ¬ IsWeakCRSolutionHalf q Ω (Submodule.span ℝ {(1 : ℂ)})
      (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 (fun _ => I) 0 := by
  intro h
  obtain ⟨s, hs⟩ := hΩ
  have h' := ((isWeakCRSolutionHalf_iff_of_contDiffOn (Λ := Submodule.span ℝ {(1 : ℂ)})
    (J := fun _ => I • ContinuousLinearMap.id ℝ ℂ) (S := 0) (ξ := fun _ => I) (η := 0)
    contDiffOn_const continuousOn_const contDiffOn_const continuousOn_const).1
    (by simpa [fderiv_const] using h)).2 s hs 1 (Submodule.mem_span_singleton_self 1)
  simp at h'

/-- **Check: the test functions must be restricted on `ℝ`.** For `J = i` and `S = 0` on an open
set meeting `ℝ`, the constant `ξ = 1` is holomorphic and real on `ℝ`, but the weak identity
`∫ ⟪D* φ, 1⟫ = 0` fails for some test function: otherwise `ξ = 1` would be a weak solution for
the boundary subspace `⊤`, and the boundary condition of
`TauCeti.isWeakCRSolutionHalf_iff_of_contDiffOn` would give `⟪i, i · 1⟫ = 0`. -/
theorem exists_setIntegral_inner_crFormalAdjoint_one_ne_zero (hΩ : ∃ s : ℝ, (s : ℂ) ∈ Ω) :
    ∃ φ : 𝓓(Ω, ℂ), ∫ z in {z : ℂ | 0 < z.im},
      ⟪crFormalAdjoint (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 φ z, 1⟫_ℝ ≠ 0 := by
  by_contra! h0
  obtain ⟨s, hs⟩ := hΩ
  have hweak : IsWeakCRSolutionHalf 1 Ω ⊤ (fun _ => I • ContinuousLinearMap.id ℝ ℂ)
      (fderiv ℝ fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 (fun _ => 1) 0 := by
    refine ⟨memLpLoc_const 1, locallyIntegrableOn_zero, fun φ _ =>
      ⟨integrableOn_im_pos_inner_crFormalAdjoint_of_contDiffOn (φ.contDiff.of_le (by simp))
        φ.hasCompactSupport Ω.isOpen continuousOn_const contDiffOn_const continuousOn_const
        φ.tsupport_subset, ?_⟩⟩
    simpa [fderiv_const] using h0 φ
  have h' := ((isWeakCRSolutionHalf_iff_of_contDiffOn contDiffOn_const continuousOn_const
    contDiffOn_const continuousOn_const).1 hweak).2 s hs I Submodule.mem_top
  simp at h'

end TauCeti
