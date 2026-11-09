/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Constructions
public import TauCeti.MeasureTheory.Function.LpSection.Basic

/-!
# `Lᵖ` sections in local coordinates

This file compares the spaces `Lᵖ(E, μ)` of sections of a vector bundle (`TauCeti.LpSection`)
with Mathlib's spaces `MeasureTheory.Lp` of functions with values in a fixed normed space, in three
situations.

* For the trivial bundle `Bundle.Trivial B F` over a normed space `F`, sections are
  functions `B → F` and `Lᵖ(Bundle.Trivial B F, μ) ≃ₗᵢ[𝕜] Lp F p μ` is the identity on
  representatives (`TauCeti.LpSection.trivialEquiv`).
* Over the base set of an atlas chart `e`, the Gram–Schmidt orthonormal frame of `e` (built from a
  basis `c` of the model fibre and an orthonormal basis `b` of an inner product space `V`) gives a
  linear isometry `Lᵖ(E, μ|_U) ≃ₗᵢ[𝕜] Lp V p μ|_U`, `U = e.baseSet`, reading sections in the frame
  (`Bundle.Trivialization.orthonormalLpSectionEquiv`).
* The coordinates of an arbitrary atlas chart `e` give a continuous linear equivalence
  `Lᵖ(E, μ|_U) ≃L[𝕜] Lp F p μ|_U` on any measurable `U ⊆ e.baseSet` on which the fibre norms are
  uniformly comparable to the norm of `F`, that is `‖e.symm x v‖ ≤ C ‖v‖` and
  `‖v‖ ≤ C' ‖e.symm x v‖` for `x ∈ U` (`Bundle.Trivialization.lpSectionEquivOfBounds`). Such bounds
  are not available on the whole chart in general: for the trivial line bundle over `(0, 1)` with
  its standard metric, read in the chart whose frame at `x` is `x • 1`, the lower bound forces
  `C' ≥ 1 / x` for every `x`.
-/

public section

noncomputable section

open Bundle MeasureTheory Set Filter Module
open scoped Topology InnerProductSpace ENNReal NNReal

variable {𝕜 B : Type*} [RCLike 𝕜] [TopologicalSpace B] [MeasurableSpace B]
  [OpensMeasurableSpace B] [SecondCountableTopology B] {p : ℝ≥0∞} [Fact (1 ≤ p)]
  {μ : Measure B}

namespace TauCeti

section Trivial

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

omit [SecondCountableTopology B] in
variable (𝕜 F μ) in
/-- The identity frame of the trivial bundle over a normed space is a measurable isometric frame:
a section of `Bundle.Trivial B F` is a.e.-strongly measurable exactly when it is as a function
`B → F`. -/
theorem isMeasurableIsometricFrame_trivial :
    IsMeasurableIsometricFrame F μ (fun x ↦ LinearIsometryEquiv.refl 𝕜 (Trivial B F x)) := by
  have : MemTrivializationAtlas (Trivial.trivialization B F) := ⟨mem_singleton _⟩
  refine isMeasurableIsometricFrame_iff.2 fun s ↦ ⟨fun hs ↦ ?_, fun hs ↦ .of_coord fun e _ ↦ ?_⟩
  · have h := hs.aestronglyMeasurable_coord (Trivial.trivialization B F)
    simp only [Trivial.trivialization_baseSet, Measure.restrict_univ,
      Trivial.trivialization_apply] at h
    exact h
  · rw [Trivial.eq_trivialization B F e]
    simp only [Trivial.trivialization_baseSet, Measure.restrict_univ,
      Trivial.trivialization_apply]
    exact hs

namespace LpSection

variable (𝕜 p μ) in
/-- The space `Lᵖ` of sections of the trivial bundle `Bundle.Trivial B F` over a normed
space is `Lp F p μ`, by the identity on representatives. -/
def trivialEquiv : LpSection 𝕜 F (Trivial B F) p μ ≃ₗᵢ[𝕜] Lp F p μ :=
  (isMeasurableIsometricFrame_trivial (𝕜 := 𝕜) (F := F) (μ := μ)).lpSectionEquiv p

theorem coeFn_trivialEquiv (f : LpSection 𝕜 F (Trivial B F) p μ) :
    ∀ᵐ x ∂μ, trivialEquiv 𝕜 p μ f x = f x :=
  (isMeasurableIsometricFrame_trivial (𝕜 := 𝕜) (F := F) (μ := μ)).coeFn_lpSectionEquiv p f

theorem coeFn_trivialEquiv_symm (g : Lp F p μ) :
    ∀ᵐ x ∂μ, (trivialEquiv 𝕜 p μ).symm g x = g x :=
  (isMeasurableIsometricFrame_trivial (𝕜 := 𝕜) (F := F) (μ := μ)).coeFn_lpSectionEquiv_symm p g

end LpSection

end Trivial

end TauCeti

namespace Bundle.Trivialization

open TauCeti

section Unitary

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, InnerProductSpace 𝕜 (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E]
  [ContinuousFiberNorm F E] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  {ι : Type*} [Fintype ι] [LinearOrder ι] [LocallyFiniteOrderBot ι]
  (e : Trivialization F (π F E)) [MemTrivializationAtlas e] (c : Basis ι 𝕜 F)
  (b : OrthonormalBasis ι 𝕜 V)

variable (p μ) in
/-- **Unitary charts.** Over the base set `U` of an atlas chart `e`, reading sections in the
Gram–Schmidt orthonormal frame of `e` is a linear isometry from `Lᵖ(E, μ|_U)` onto `Lp V p μ|_U`. -/
def orthonormalLpSectionEquiv :
    LpSection 𝕜 F E p (μ.restrict e.baseSet) ≃ₗᵢ[𝕜] Lp V p (μ.restrict e.baseSet) :=
  (e.isMeasurableIsometricFrame_orthonormalFrameAt c b).lpSectionEquiv p

theorem coeFn_orthonormalLpSectionEquiv (f : LpSection 𝕜 F E p (μ.restrict e.baseSet)) :
    ∀ᵐ x ∂μ.restrict e.baseSet, ∀ hx : x ∈ e.baseSet,
      e.orthonormalLpSectionEquiv p μ c b f x = (e.orthonormalFrame c b ⟨x, hx⟩).symm (f x) := by
  filter_upwards
    [(e.isMeasurableIsometricFrame_orthonormalFrameAt c b).coeFn_lpSectionEquiv p f]
    with x h hx
  rw [orthonormalLpSectionEquiv, h]
  rw [e.orthonormalFrameAt_of_mem c b hx]

theorem coeFn_orthonormalLpSectionEquiv_symm (g : Lp V p (μ.restrict e.baseSet)) :
    ∀ᵐ x ∂μ.restrict e.baseSet, ∀ hx : x ∈ e.baseSet,
      (e.orthonormalLpSectionEquiv p μ c b).symm g x = e.orthonormalFrame c b ⟨x, hx⟩ (g x) := by
  filter_upwards
    [(e.isMeasurableIsometricFrame_orthonormalFrameAt c b).coeFn_lpSectionEquiv_symm p g]
    with x h hx
  rw [orthonormalLpSectionEquiv, h]
  rw [e.orthonormalFrameAt_of_mem c b hx]

end Unitary

section Bounds

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {E : B → Type*}
  [TopologicalSpace (TotalSpace F E)] [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace 𝕜 (E x)] [FiberBundle F E] [VectorBundle 𝕜 F E] [ContinuousFiberNorm F E]
  (e : Trivialization F (π F E)) [MemTrivializationAtlas e] {U : Set B} (hU : MeasurableSet U)
  (hUe : U ⊆ e.baseSet) (C C' : ℝ≥0) (hC : ∀ x ∈ U, ∀ v : F, ‖e.symm x v‖ ≤ C * ‖v‖)
  (hC' : ∀ x ∈ U, ∀ v : F, ‖v‖ ≤ C' * ‖e.symm x v‖)

omit [Fact (1 ≤ p)] in
include hU hUe hC' in
/-- Coordinates in `e` of an `Lᵖ` section, on a set where the fibre norms dominate the norm of the
model fibre, are `p`-integrable. -/
private theorem memLp_coord_of_bound (f : LpSection 𝕜 F E p (μ.restrict U)) :
    MemLp (fun x ↦ (e ⟨x, f x⟩).2) p (μ.restrict U) := by
  refine f.memLp_norm.of_le_mul (c := C') ?_ ?_
  · have h := f.aestronglyMeasurableSection.aestronglyMeasurable_coord e
    rwa [Measure.restrict_restrict e.open_baseSet.measurableSet, inter_eq_right.2 hUe] at h
  · filter_upwards [ae_restrict_mem hU] with x hx
    simpa only [norm_norm, e.symm_apply_apply_mk (hUe hx)] using hC' x hx (e ⟨x, f x⟩).2

omit [Fact (1 ≤ p)] in
include 𝕜 hU hUe hC in
private theorem memLp_norm_symm_of_bound (g : Lp F p (μ.restrict U)) :
    MemLp (fun x ↦ ‖e.symm x (g x)‖) p (μ.restrict U) := by
  refine (Lp.memLp g).of_le_mul (c := C)
    (aestronglyMeasurableSection_restrict_symm (𝕜 := 𝕜) hU e hUe (Lp.aestronglyMeasurable g)
      |>.aestronglyMeasurable_norm) ?_
  filter_upwards [ae_restrict_mem hU] with x hx
  simpa only [norm_norm] using hC x hx (g x)

variable (𝕜 p μ) in
/-- **Bounded charts.** On a measurable subset `U` of the base set of an atlas chart `e` on which
the fibre norms are uniformly comparable to the norm of the model fibre `F`, reading sections in
the coordinates of `e` is a continuous linear equivalence from `Lᵖ(E, μ|_U)` onto `Lp F p μ|_U`. -/
def lpSectionEquivOfBounds :
    LpSection 𝕜 F E p (μ.restrict U) ≃L[𝕜] Lp F p (μ.restrict U) :=
  LinearEquiv.toContinuousLinearEquivOfBounds
    { toFun f := (memLp_coord_of_bound e hU hUe C' hC' f).toLp _
      invFun g := LpSection.mk (fun x ↦ e.symm x (g x))
        (aestronglyMeasurableSection_restrict_symm (𝕜 := 𝕜) hU e hUe (Lp.aestronglyMeasurable g))
        (memLp_norm_symm_of_bound (𝕜 := 𝕜) e hU hUe C hC g)
      map_add' f g := by
        rw [← MemLp.toLp_add]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [LpSection.coeFn_add f g, ae_restrict_mem hU] with x hx hxU
        simp only [Pi.add_apply, hx, ← e.continuousLinearMapAt_apply_of_mem (R := 𝕜) (hUe hxU),
          map_add]
      map_smul' c f := by
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        refine MemLp.toLp_congr _ _ ?_
        filter_upwards [LpSection.coeFn_smul f c, ae_restrict_mem hU] with x hx hxU
        simp only [Pi.smul_apply, hx, ← e.continuousLinearMapAt_apply_of_mem (R := 𝕜) (hUe hxU),
          map_smul]
      left_inv f := by
        refine LpSection.ext _ _ ?_
        filter_upwards [LpSection.coeFn_mk
          (aestronglyMeasurableSection_restrict_symm (𝕜 := 𝕜) hU e hUe (Lp.aestronglyMeasurable _))
          (memLp_norm_symm_of_bound (𝕜 := 𝕜) e hU hUe C hC _),
          MemLp.coeFn_toLp (memLp_coord_of_bound e hU hUe C' hC' f), ae_restrict_mem hU]
          with x h1 h2 hx
        rw [h1, h2, e.symm_apply_apply_mk (hUe hx)]
      right_inv g := by
        refine Lp.ext ?_
        filter_upwards [MemLp.coeFn_toLp (memLp_coord_of_bound (𝕜 := 𝕜) e hU hUe C' hC' _),
          LpSection.coeFn_mk
            (aestronglyMeasurableSection_restrict_symm (𝕜 := 𝕜) hU e hUe
              (Lp.aestronglyMeasurable g))
            (memLp_norm_symm_of_bound (𝕜 := 𝕜) e hU hUe C hC g), ae_restrict_mem hU]
          with x h1 h2 hx
        rw [h1, h2, e.apply_mk_symm (hUe hx)] }
    C' C
    (fun f ↦ by
      rw [LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LpSection.norm_eq_norm_toLp]
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_coord_of_bound e hU hUe C' hC' f),
        MemLp.coeFn_toLp f.memLp_norm, ae_restrict_mem hU] with x h1 h2 hx
      rw [h1, h2, norm_norm]
      simpa only [e.symm_apply_apply_mk (hUe hx)] using hC' x hx (e ⟨x, f x⟩).2)
    (fun g ↦ by
      rw [LinearEquiv.coe_symm_mk', LpSection.norm_mk_eq_norm_toLp]
      refine Lp.norm_le_mul_norm_of_ae_le_mul ?_
      filter_upwards [MemLp.coeFn_toLp (memLp_norm_symm_of_bound (𝕜 := 𝕜) e hU hUe C hC g),
        ae_restrict_mem hU] with x h1 hx
      rw [h1, norm_norm]
      exact hC x hx (g x))

theorem coeFn_lpSectionEquivOfBounds (f : LpSection 𝕜 F E p (μ.restrict U)) :
    ∀ᵐ x ∂μ.restrict U,
      e.lpSectionEquivOfBounds 𝕜 p μ hU hUe C C' hC hC' f x = (e ⟨x, f x⟩).2 :=
  MemLp.coeFn_toLp (memLp_coord_of_bound e hU hUe C' hC' f)

theorem coeFn_lpSectionEquivOfBounds_symm (g : Lp F p (μ.restrict U)) :
    ∀ᵐ x ∂μ.restrict U,
      (e.lpSectionEquivOfBounds 𝕜 p μ hU hUe C C' hC hC').symm g x = e.symm x (g x) :=
  LpSection.coeFn_mk
    (aestronglyMeasurableSection_restrict_symm (𝕜 := 𝕜) hU e hUe (Lp.aestronglyMeasurable g))
    (memLp_norm_symm_of_bound (𝕜 := 𝕜) e hU hUe C hC g)

end Bounds

end Bundle.Trivialization
