/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyRiemann.RoughCoefficients.Weak
public import TauCeti.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Complex.Wirtinger.HalfPlaneAdjoint.Variable
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
condition `ξ(s) ∈ Λ` exactly when `J(s)⁻¹ Λᗮ = Λ`, for instance when `V = Λ ⊕ J(s) Λ` is an
orthogonal decomposition, as for `J(s) = i` and `Λ = ℝⁿ ⊆ ℂⁿ` (the case of McDuff–Salamon and of
the Checks below). For general `(J, Λ)` the two conditions differ: `Λ = ⊥` imposes nothing.

## Main results

* Linearity in `(ξ, η)` (`TauCeti.IsWeakCRSolutionHalf.add`, `.const_smul`, `.neg`, `.sub`,
  `TauCeti.isWeakCRSolutionHalf_zero`), restriction to open sets with smaller part in
  `{0 ≤ t}` (`TauCeti.IsWeakCRSolutionHalf.mono`), lowering the exponent
  (`TauCeti.IsWeakCRSolutionHalf.mono_exponent`) and invariance under changes of the data on
  null subsets of `Ω ∩ {0 ≤ t}` (`TauCeti.isWeakCRSolutionHalf_congr_ae`).
* `TauCeti.IsWeakCRSolutionHalf.isWeakCRSolution`: a weak solution up to the boundary is a weak
  solution of the interior equation on the open upper part `Ω ∩ {0 < t}`.
* `TauCeti.setIntegral_im_pos_inner_crFormalAdjoint_of_contDiffOn`: Green's formula
  `∫_{0<t} ⟪D* φ, ξ⟫ = ∫_{0<t} ⟪φ, ∂_s ξ + J ∂_t ξ + S ξ⟫ + ∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds` for `C¹`
  data with `DJ = fderiv ℝ J`.
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
    (isClosed_le continuous_const continuous_im)).exists_contDiff_cutoff Ω.isOpen
    fun z hz => (hΩ ⟨φ.tsupport_subset hz.1, hz.2⟩).1
  let φ' : 𝓓(Ω, V) := ⟨fun z => ψ z • (φ : ℂ → V) z, hψ.smul φ.contDiff,
    hψc.smul_right, (tsupport_smul_subset_left _ _).trans hψΩ⟩
  have hφ' {z : ℂ} (hz : 0 < z.im) : (φ' : ℂ → V) =ᶠ[𝓝 z] φ := by
    by_cases hzφ : z ∈ tsupport (φ : ℂ → V)
    · filter_upwards [mem_interior_iff_mem_nhds.1 (hψ1 ⟨hzφ, hz.le⟩)] with w hw
      simp [φ', show ψ w = 1 from hw]
    · filter_upwards [notMem_tsupport_iff_eventuallyEq.1 hzφ] with w hw
      simp [φ', show (φ : ℂ → V) w = 0 from hw]
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

/-- The integrability and the identity of Green's formula for `TauCeti.crFormalAdjoint`, proved
together since they share the decomposition of the integrand. -/
private theorem integrableOn_and_setIntegral_im_pos_inner_crFormalAdjoint {φ ξ : ℂ → V} {U : Set ℂ}
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
  rw [integral_sub (f := fun z => -G z) hG.neg.integrableOn hT.integrableOn, integral_neg, hgreen,
    hsplit]
  ring

/-- For `C¹` data with `DJ = fderiv ℝ J`, the pairing of the formal adjoint of a compactly
supported `C¹` field `φ` with `ξ` is integrable on the upper half-plane. -/
theorem integrableOn_im_pos_inner_crFormalAdjoint_of_contDiffOn {φ ξ : ℂ → V} {U : Set ℂ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hU : IsOpen U) (hξ : ContDiffOn ℝ 1 ξ U)
    (hJ : ContDiffOn ℝ 1 J U) (hS : ContinuousOn S U) (hφU : tsupport φ ⊆ U) :
    IntegrableOn (fun z => ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ) {z : ℂ | 0 < z.im} :=
  (integrableOn_and_setIntegral_im_pos_inner_crFormalAdjoint hφ hφc hU hξ hJ hS hφU).1

/-- **Green's formula** for `TauCeti.crFormalAdjoint` on the half-plane with `C¹` data and
`DJ = fderiv ℝ J`: the `∂_t J` terms of `D*` and of the integration by parts cancel, leaving
`∫_{0<t} ⟪D* φ, ξ⟫ = ∫_{0<t} ⟪φ, ∂_s ξ + J ∂_t ξ + S ξ⟫ + ∫_ℝ ⟪φ(s), J(s) ξ(s)⟫ ds`. -/
theorem setIntegral_im_pos_inner_crFormalAdjoint_of_contDiffOn {φ ξ : ℂ → V} {U : Set ℂ}
    (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (hU : IsOpen U) (hξ : ContDiffOn ℝ 1 ξ U)
    (hJ : ContDiffOn ℝ 1 J U) (hS : ContinuousOn S U) (hφU : tsupport φ ⊆ U) :
    ∫ z in {z : ℂ | 0 < z.im}, ⟪crFormalAdjoint J (fderiv ℝ J) S φ z, ξ z⟫_ℝ =
      (∫ z in {z : ℂ | 0 < z.im}, ⟪φ z, fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ) +
        ∫ s : ℝ, ⟪φ s, J s (ξ s)⟫_ℝ :=
  (integrableOn_and_setIntegral_im_pos_inner_crFormalAdjoint hφ hφc hU hξ hJ hS hφU).2

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
  obtain ⟨hint, heq⟩ := integrableOn_and_setIntegral_im_pos_inner_crFormalAdjoint
    (φ.contDiff.of_le (by simp)) φ.hasCompactSupport Ω.isOpen hξ hJ hS φ.tsupport_subset
  have hbdry (s : ℝ) : ⟪(φ : ℂ → V) s, J s (ξ s)⟫_ℝ = 0 := by
    by_cases hs : (s : ℂ) ∈ Ω
    · exact hJξ s hs _ (hφΛ s)
    · simp [image_eq_zero_of_notMem_tsupport fun h => hs (φ.tsupport_subset h)]
  refine ⟨hint, heq.trans ?_⟩
  simp only [hbdry, integral_zero, add_zero]
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
  refine ⟨hint, fun s₀ hs₀ v hv => ?_⟩
  -- `g = ⟪v, J ξ⟫` along `ℝ`; if `g(s₀) ≠ 0`, test against a bump on which `g(s₀) g > 0`.
  set g : ℝ → ℝ := fun s => ⟪v, J s (ξ s)⟫_ℝ
  have hO : IsOpen (((↑) : ℝ → ℂ) ⁻¹' Ω) := Ω.isOpen.preimage continuous_ofReal
  have hg : ContinuousOn g (((↑) : ℝ → ℂ) ⁻¹' Ω) :=
    continuousOn_const.inner ((hJ.continuousOn.comp continuous_ofReal.continuousOn
      (mapsTo_preimage _ _)).clm_apply
      (hξ.continuousOn.comp continuous_ofReal.continuousOn (mapsTo_preimage _ _)))
  by_contra hc
  obtain ⟨ε, hε, hpos⟩ := Metric.eventually_nhds_iff.1
    ((continuousAt_const.mul (hg.continuousAt (hO.mem_nhds hs₀))).eventually
      (lt_mem_nhds (mul_self_pos.2 hc)))
  obtain ⟨ε', hε', hball⟩ := Metric.isOpen_iff.1 Ω.isOpen _ hs₀
  have hδ : 0 < min ε ε' := lt_min hε hε'
  let ψ : ContDiffBump (s₀ : ℂ) := ⟨min ε ε' / 4, min ε ε' / 2, by positivity, by linarith⟩
  have hψΩ : tsupport ψ ⊆ Ω := by
    rw [ψ.tsupport_eq]
    exact (Metric.closedBall_subset_ball (by simp [ψ]; linarith [min_le_right ε ε'])).trans hball
  let φ : 𝓓(Ω, V) := ⟨fun z => ψ z • g s₀ • v, ψ.contDiff.smul contDiff_const,
    ψ.hasCompactSupport.smul_right, (tsupport_smul_subset_left _ _).trans hψΩ⟩
  have hφΛ (s : ℝ) : (φ : ℂ → V) s ∈ Λ := Λ.smul_mem _ (Λ.smul_mem _ hv)
  have hB : ∫ s : ℝ, ⟪(φ : ℂ → V) s, J s (ξ s)⟫_ℝ = 0 := by
    have h1 := setIntegral_im_pos_inner_crFormalAdjoint_of_contDiffOn
      (φ.contDiff.of_le (by simp)) φ.hasCompactSupport Ω.isOpen hξ hJ hS φ.tsupport_subset
    have h2 : ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z,
        fderiv ℝ ξ z 1 + J z (fderiv ℝ ξ z I) + S z (ξ z)⟫_ℝ =
        ∫ z in {z : ℂ | 0 < z.im}, ⟪(φ : ℂ → V) z, η z⟫_ℝ := by
      refine setIntegral_congr_fun hH fun z hz => ?_
      by_cases hzΩ : z ∈ (Ω : Set ℂ)
      · rw [hint z (Opens.mem_upperHalf.2 ⟨hzΩ, hz⟩)]
      · simp [image_eq_zero_of_notMem_tsupport fun h => hzΩ (φ.tsupport_subset h)]
    rw [h.setIntegral_inner_crFormalAdjoint φ hφΛ, h2] at h1
    linarith
  have hF (s : ℝ) : ⟪(φ : ℂ → V) s, J s (ξ s)⟫_ℝ = ψ s * (g s₀ * g s) := by
    simp only [φ, TestFunction.coe_mk, real_inner_smul_left, g]
  simp_rw [hF] at hB
  refine (Continuous.integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (continuous_of_tsupport fun s hs => ?_)
    (ψ.hasCompactSupport.comp_isClosedEmbedding isometry_ofReal.isClosedEmbedding).mul_right
    (fun s => ?_) (x := s₀) ?_).ne' hB
  · have hsΩ : s ∈ ((↑) : ℝ → ℂ) ⁻¹' Ω :=
      hψΩ (tsupport_comp_subset_preimage (ψ : ℂ → ℝ) continuous_ofReal
        (tsupport_mul_subset_left hs))
    exact (ψ.continuous.comp continuous_ofReal).continuousAt.mul
      (continuousAt_const.mul (hg.continuousAt (hO.mem_nhds hsΩ)))
  · change 0 ≤ ψ s * (g s₀ * g s)
    by_cases hs : dist s s₀ < ε
    · exact mul_nonneg ψ.nonneg (hpos hs).le
    · rw [ψ.zero_of_le_dist (by
        simp only [ψ, isometry_ofReal.dist_eq]; linarith [min_le_left ε ε']), zero_mul]
  · simpa [ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le)] using hc

/-! ### Checks: `J = i`, `S = 0` and the real boundary condition -/

/-- An open set meeting `ℝ` contains the closed support of a smooth bump around a real point. -/
private theorem exists_contDiffBump (hΩ : ∃ s : ℝ, (s : ℂ) ∈ Ω) :
    ∃ (x : ℝ) (ψ : ContDiffBump (x : ℂ)), Metric.closedBall (x : ℂ) ψ.rOut ⊆ Ω := by
  obtain ⟨x, hx⟩ := hΩ
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 Ω.isOpen _ hx
  exact ⟨x, ⟨ε / 4, ε / 2, by positivity, by linarith⟩,
    (Metric.closedBall_subset_ball (by linarith)).trans hball⟩

/-- The multiple `c ψ` of a smooth real bump `ψ` supported in `Ω`, as a test function. -/
private def bumpTest {x : ℝ} (ψ : ContDiffBump (x : ℂ))
    (hψ : Metric.closedBall (x : ℂ) ψ.rOut ⊆ Ω) (c : ℂ) : 𝓓(Ω, ℂ) :=
  ⟨fun z => c * (ψ z : ℂ), contDiff_const.mul (ofRealCLM.contDiff.comp ψ.contDiff),
    (ψ.hasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) ofReal_zero).mul_left,
    (closure_minimal (fun z hz => Metric.ball_subset_closedBall (ψ.support_eq ▸
      show ψ z ≠ 0 from fun h0 => hz (by simp [h0]))) Metric.isClosed_closedBall).trans hψ⟩

private theorem bumpTest_apply {x : ℝ} (ψ : ContDiffBump (x : ℂ))
    (hψ : Metric.closedBall (x : ℂ) ψ.rOut ⊆ Ω) (c z : ℂ) :
    (bumpTest ψ hψ c : ℂ → ℂ) z = c * ψ z := rfl

/-- The boundary integral of a bump around a real point is positive. -/
private theorem integral_bumpTest_pos {x : ℝ} (ψ : ContDiffBump (x : ℂ))
    (hψ : Metric.closedBall (x : ℂ) ψ.rOut ⊆ Ω) :
    0 < ∫ s : ℝ, ((bumpTest ψ hψ 1 : ℂ → ℂ) s).re := by
  have h (s : ℝ) : ((bumpTest ψ hψ 1 : ℂ → ℂ) s).re = ψ s := by simp [bumpTest_apply]
  simp_rw [h]
  refine (ψ.continuous.comp continuous_ofReal).integral_pos_of_hasCompactSupport_nonneg_ne_zero
    (ψ.hasCompactSupport.comp_isClosedEmbedding isometry_ofReal.isClosedEmbedding)
    (fun s => ψ.nonneg) (x := x) ?_
  simp [ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le)]

/-- Green's formula of `TauCeti.setIntegral_im_pos_inner_crFormalAdjoint_of_contDiffOn` for
`J = i`, `S = 0` and a constant field `c`: only the boundary term survives. -/
private theorem setIntegral_inner_crFormalAdjoint_I_const (φ : 𝓓(Ω, ℂ)) (c : ℂ) :
    ∫ z in {z : ℂ | 0 < z.im},
        ⟪crFormalAdjoint (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 φ z, c⟫_ℝ =
      ∫ s : ℝ, ⟪(φ : ℂ → ℂ) s, I * c⟫_ℝ := by
  have h := setIntegral_im_pos_inner_crFormalAdjoint_of_contDiffOn (J := fun _ =>
    I • ContinuousLinearMap.id ℝ ℂ) (S := 0) (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
    Ω.isOpen (contDiffOn_const (c := c)) contDiffOn_const continuousOn_const φ.tsupport_subset
  simpa [fderiv_const] using h

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
the boundary: for a real bump `φ = χ` the boundary term is `⟪χ, i · i⟫ = -χ`, with nonzero
integral. -/
theorem not_isWeakCRSolutionHalf_const_I (hΩ : ∃ s : ℝ, (s : ℂ) ∈ Ω) :
    ¬ IsWeakCRSolutionHalf q Ω (Submodule.span ℝ {(1 : ℂ)})
      (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 (fun _ => I) 0 := by
  intro h
  obtain ⟨x, ψ, hψ⟩ := exists_contDiffBump hΩ
  have hφ (s : ℝ) : (bumpTest ψ hψ 1 : ℂ → ℂ) s ∈ Submodule.span ℝ {(1 : ℂ)} :=
    Submodule.mem_span_singleton.2 ⟨((bumpTest ψ hψ 1 : ℂ → ℂ) s).re, by simp [bumpTest_apply]⟩
  have h1 := h.setIntegral_inner_crFormalAdjoint _ hφ
  rw [setIntegral_inner_crFormalAdjoint_I_const] at h1
  have h2 (s : ℝ) : ⟪(bumpTest ψ hψ 1 : ℂ → ℂ) s, I * I⟫_ℝ =
      -((bumpTest ψ hψ 1 : ℂ → ℂ) s).re := by
    simp [Complex.inner]
  simp only [h2, integral_neg, Pi.zero_apply, inner_zero_right, integral_zero, neg_eq_zero] at h1
  exact (integral_bumpTest_pos ψ hψ).ne' h1

/-- **Check: the test functions must be restricted on `ℝ`.** For `J = i` and `S = 0` on an open
set meeting `ℝ`, the constant `ξ = 1` is holomorphic and real on `ℝ`, but the weak identity
`∫ ⟪D* φ, 1⟫ = 0` fails for a test function `φ = i χ`, which is not real on `ℝ`: the boundary
term is `∫_ℝ ⟪i χ, i⟫ = ∫_ℝ χ ≠ 0`. -/
theorem exists_setIntegral_inner_crFormalAdjoint_one_ne_zero (hΩ : ∃ s : ℝ, (s : ℂ) ∈ Ω) :
    ∃ φ : 𝓓(Ω, ℂ), ∫ z in {z : ℂ | 0 < z.im},
      ⟪crFormalAdjoint (fun _ => I • ContinuousLinearMap.id ℝ ℂ) 0 0 φ z, 1⟫_ℝ ≠ 0 := by
  obtain ⟨x, ψ, hψ⟩ := exists_contDiffBump hΩ
  refine ⟨bumpTest ψ hψ I, ?_⟩
  rw [setIntegral_inner_crFormalAdjoint_I_const]
  have h (s : ℝ) : ⟪(bumpTest ψ hψ I : ℂ → ℂ) s, I * 1⟫_ℝ =
      ((bumpTest ψ hψ 1 : ℂ → ℂ) s).re := by
    simp [Complex.inner, bumpTest_apply]
  simp only [h]
  exact (integral_bumpTest_pos ψ hψ).ne'

end TauCeti
