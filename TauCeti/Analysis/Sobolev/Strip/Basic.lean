/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import TauCeti.MeasureTheory.Integral.Rectangle
import TauCeti.MeasureTheory.Measure.Haar.Prod

/-!
# Jet spaces of `W^{1,2}` maps on the strip

Let `V` be a real normed space. Maps on the strip `ℝ × [0, 1]` with values in `V` are maps
`ξ : ℝ × ℝ → V`, read on the strip with its Lebesgue measure `TauCeti.StripSobolev.stripMeasure`.
This file sets up the `W^{1,2}` completions of classes of such maps, realized as closed subspaces
of `L²(ℝ × [0, 1], V × V × V)`. They are the Sobolev spaces on which the linearized operators of
Floer theory act: on the cylinder `ℝ × S¹`, whose sections are the maps of period one in `t`
(`TauCeti.Analysis.Sobolev.Cylinder`), and on the strip with boundary conditions on its two edges
(`TauCeti.Analysis.Sobolev.Strip.BoundaryCondition`).

* **Test maps** (`TauCeti.StripSobolev.testMap`) are the `C²` maps that vanish for `|s|` large.
* The **jet** of a map is `jet ξ = (ξ, ∂s ξ, ∂t ξ)`. The jet of a test map is square integrable on
  the strip (`TauCeti.StripSobolev.memLp_jet`), which gives the linear map
  `TauCeti.StripSobolev.jetₗ` into `L²(ℝ × [0, 1], V × V × V)`. Its norm is the `W^{1,2}` norm up
  to a factor between `1` and `√3`.
* For a class `S` of maps, given as a submodule, `TauCeti.StripSobolev.H1 S` is the closure of the
  jets of the test maps in `S`: the completion of these maps in the `W^{1,2}` norm, realized
  inside `L²` as a closed subspace, hence complete. An element is an `L²` jet `(ξ, ξ_s, ξ_t)`, and
  it is determined by its value `ξ` (`TauCeti.StripSobolev.valueL_injective`): integrating by
  parts against test functions supported in the open strip `ℝ × (0, 1)` shows that `ξ_s` and `ξ_t`
  are the weak derivatives of `ξ` (`TauCeti.HasWeakLineDerivOn`), which vanish where `ξ` does
  (`TauCeti.HasWeakLineDerivOn.ae_eq_zero_of_isOpen`).
* **Pairing identities.** Pairing an `L²` jet with `L²` coefficients through a continuous bilinear
  map is a continuous linear functional of the jet, so an integral identity for this pairing that
  holds on the jets of the test maps in `S` holds on all of `H1 S`
  (`TauCeti.StripSobolev.integral_add_eq_zero_of_mem_H1`). This gives both the weak derivatives
  above and the weak boundary conditions of `TauCeti.Analysis.Sobolev.Strip.BoundaryCondition`.
* **Translation invariance.** The translation `(s, t) ↦ (s + a, t)` preserves the measure of the
  strip (`TauCeti.StripSobolev.measurePreserving_add_fst`) and commutes with taking jets
  (`TauCeti.StripSobolev.jet_comp_add`). If `S` is invariant under it, it acts on `H1 S` by a
  linear isometry (`TauCeti.StripSobolev.translateₗᵢ`), carrying the jet of a test map to the jet
  of its translate (`TauCeti.StripSobolev.translateₗᵢ_jetₗ`): the `W^{1,2}` norm on the strip is
  translation invariant.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, 2nd ed., Appendix B,
  on Sobolev spaces as completions of smooth maps.
* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. 7 (1999), Lecture 2, on the Sobolev spaces of the strip and the cylinder.
-/

public section

noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace TauCeti.StripSobolev

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Lebesgue measure on the strip `ℝ × [0, 1]`. -/
abbrev stripMeasure : Measure (ℝ × ℝ) := volume.restrict (univ ×ˢ Icc 0 1)

variable (V) in
/-- The test maps on the strip: `C²` maps `ξ : ℝ × ℝ → V` that vanish for `|s|` large. -/
def testMap : Submodule ℝ (ℝ × ℝ → V) where
  carrier := {ξ | ContDiff ℝ 2 ξ ∧ ∃ R, ∀ s t, R ≤ |s| → ξ (s, t) = 0}
  zero_mem' := ⟨contDiff_const, 0, fun _ _ _ ↦ rfl⟩
  add_mem' := by
    rintro ξ η ⟨hξ, R, hR⟩ ⟨hη, R', hR'⟩
    refine ⟨hξ.add hη, max R R', fun s t hs ↦ ?_⟩
    simp [hR s t ((le_max_left _ _).trans hs), hR' s t ((le_max_right _ _).trans hs)]
  smul_mem' := by
    rintro c ξ ⟨hξ, R, hR⟩
    exact ⟨contDiff_const.smul hξ, R, fun s t hs ↦ by simp [hR s t hs]⟩

/-- Membership in the test maps. -/
theorem mem_testMap_iff {ξ : ℝ × ℝ → V} :
    ξ ∈ testMap V ↔ ContDiff ℝ 2 ξ ∧ ∃ R, ∀ s t, R ≤ |s| → ξ (s, t) = 0 :=
  Iff.rfl

/-- The jet `(ξ, ∂s ξ, ∂t ξ)` of a map `ξ : ℝ × ℝ → V`. -/
def jet (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) : V × V × V :=
  (ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1))

/-- The components of the jet. -/
theorem jet_apply (ξ : ℝ × ℝ → V) (z : ℝ × ℝ) :
    jet ξ z = (ξ z, fderiv ℝ ξ z (1, 0), fderiv ℝ ξ z (0, 1)) :=
  (rfl)

variable {ξ η : ℝ × ℝ → V}

/-- The jet of a `C¹` map is continuous. -/
theorem continuous_jet (hξ : ContDiff ℝ 1 ξ) : Continuous (jet ξ) :=
  have h := hξ.continuous_fderiv one_ne_zero
  hξ.continuous.prodMk ((h.clm_apply continuous_const).prodMk (h.clm_apply continuous_const))

/-- The jet is additive on differentiable maps. -/
theorem jet_add (hξ : Differentiable ℝ ξ) (hη : Differentiable ℝ η) :
    jet (ξ + η) = jet ξ + jet η := by
  funext z
  simp [jet, fderiv_add (hξ z) (hη z)]

/-- The jet commutes with scalar multiplication. -/
theorem jet_smul (c : ℝ) (ξ : ℝ × ℝ → V) : jet (c • ξ) = c • jet ξ := by
  funext z
  simp [jet, fderiv_const_smul_field]

/-- The jet of a map vanishing for `|s| ≥ R` vanishes for `|s| > R`. -/
theorem jet_eq_zero_of_lt_abs {R : ℝ} (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) {z : ℝ × ℝ}
    (hz : R < |z.1|) : jet ξ z = 0 := by
  have : ∀ᶠ w : ℝ × ℝ in 𝓝 z, R < |w.1| :=
    (continuous_abs.comp continuous_fst).continuousAt.eventually (lt_mem_nhds hz)
  have h : ξ =ᶠ[𝓝 z] 0 := by
    filter_upwards [this] with w hw
    exact hR w.1 w.2 hw.le
  simp [jet, h.fderiv_eq, h.eq_of_nhds]

/-- For a map vanishing for `|s| ≥ R`, the integral over the strip of a function vanishing
wherever the jet of the map vanishes is its integral over `[-R, R] × [0, 1]`. -/
theorem integral_strip_eq_setIntegral_of_jet_eq_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {R : ℝ} (hR : ∀ s t, R ≤ |s| → ξ (s, t) = 0) {F : ℝ × ℝ → E}
    (hF : ∀ z, jet ξ z = 0 → F z = 0) :
    ∫ z, F z ∂stripMeasure = ∫ z in Icc (-R) R ×ˢ Icc (0 : ℝ) 1, F z :=
  setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (MeasurableSet.univ.prod measurableSet_Icc)
    (prod_mono (subset_univ _) subset_rfl) fun z hz ↦ hF z (jet_eq_zero_of_lt_abs hR (by
      have h : z.1 ∉ Icc (-R) R := fun h ↦ hz.2 ⟨h, hz.1.2⟩
      rwa [mem_Icc, ← abs_le, not_le] at h))

/-- The jet of a test map is square integrable on the strip. -/
theorem memLp_jet (hξ : ξ ∈ testMap V) : MemLp (jet ξ) 2 stripMeasure := by
  obtain ⟨hξ2, R, hR⟩ := mem_testMap_iff.1 hξ
  have hc := continuous_jet (hξ2.of_le (by norm_num))
  set K : Set (ℝ × ℝ) := Icc (-R) R ×ˢ Icc 0 1
  have hK : IsCompact K := isCompact_Icc.prod isCompact_Icc
  have hae : jet ξ =ᵐ[stripMeasure] K.indicator (jet ξ) := by
    filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Icc)] with z hz
    by_cases hzK : z ∈ K
    · rw [indicator_of_mem hzK]
    · rw [indicator_of_notMem hzK]
      refine jet_eq_zero_of_lt_abs hR ?_
      by_contra h
      exact hzK ⟨abs_le.1 (not_lt.1 h), hz.2⟩
  refine (memLp_congr_ae hae).2 ?_
  rw [memLp_indicator_iff_restrict hK.measurableSet.nullMeasurableSet]
  have : IsFiniteMeasure (stripMeasure.restrict K) :=
    isFiniteMeasure_restrict.2 ((Measure.restrict_apply_le _ K).trans_lt
      hK.measure_lt_top).ne
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  exact MemLp.of_bound hc.aestronglyMeasurable C ((ae_restrict_mem hK.measurableSet).mono hC)

variable (V) in
/-- The `L²` jet `(ξ, ∂s ξ, ∂t ξ)` of a test map, as a linear map into
`L²(ℝ × [0, 1], V × V × V)`. -/
def jetₗ : testMap V →ₗ[ℝ] Lp (V × V × V) 2 stripMeasure where
  toFun ξ := (memLp_jet ξ.2).toLp (jet (ξ : ℝ × ℝ → V))
  map_add' ξ η := by
    have hξ := ((mem_testMap_iff.1 ξ.2).1.differentiable (by norm_num))
    have hη := ((mem_testMap_iff.1 η.2).1.differentiable (by norm_num))
    simp only [Submodule.coe_add, ← MemLp.toLp_add]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by rw [jet_add hξ hη])
  map_smul' c ξ := by
    simp only [SetLike.val_smul, RingHom.id_apply, ← MemLp.toLp_const_smul]
    exact MemLp.toLp_congr _ _ (Eventually.of_forall fun z ↦ by rw [jet_smul])

/-- The `L²` jet of a test map is represented by its jet. -/
theorem coeFn_jetₗ (ξ : testMap V) : jetₗ V ξ =ᵐ[stripMeasure] jet (ξ : ℝ × ℝ → V) :=
  MemLp.coeFn_toLp (memLp_jet ξ.2)

/-- The `L²` jet of a test map is the class of its jet. -/
theorem jetₗ_apply (ξ : testMap V) :
    jetₗ V ξ = (memLp_jet ξ.2).toLp (jet (ξ : ℝ × ℝ → V)) :=
  (rfl)

/-- The norm of the `L²` jet of a test map is the `L²` norm of its jet on the strip. -/
theorem norm_jetₗ (ξ : testMap V) :
    ‖jetₗ V ξ‖ = (eLpNorm (jet (ξ : ℝ × ℝ → V)) 2 stripMeasure).toReal := by
  rw [jetₗ_apply, Lp.norm_toLp]

/-- The `W^{1,2}` completion of a class `S` of maps on the strip: the closure in
`L²(ℝ × [0, 1], V × V × V)` of the jets of the test maps in `S`. An element is an `L²` jet
`(ξ, ξ_s, ξ_t)`; it is determined by its value `ξ` (`TauCeti.StripSobolev.valueL_injective`). -/
def H1 (S : Submodule ℝ (ℝ × ℝ → V)) : Submodule ℝ (Lp (V × V × V) 2 stripMeasure) :=
  ((S.comap (testMap V).subtype).map (jetₗ V)).topologicalClosure

variable {S T : Submodule ℝ (ℝ × ℝ → V)}

/-- The definition of `H1`: the closure of the jets of the test maps in `S`. -/
theorem H1_def : H1 S = ((S.comap (testMap V).subtype).map (jetₗ V)).topologicalClosure :=
  (rfl)

/-- `H1 S` is the closure of the set of jets of the test maps in `S`. -/
theorem coe_H1 : (H1 S : Set (Lp (V × V × V) 2 stripMeasure)) =
    closure (jetₗ V '' {ξ | (ξ : ℝ × ℝ → V) ∈ S}) := by
  simp only [H1_def, Submodule.topologicalClosure_coe, Submodule.map_coe, Submodule.comap_coe,
    Submodule.coe_subtype, Set.preimage, SetLike.mem_coe]

/-- A closed set containing the jets of all test maps in `S` contains `H1 S`. -/
theorem H1_subset_of_isClosed {C : Set (Lp (V × V × V) 2 stripMeasure)} (hC : IsClosed C)
    (h : ∀ ξ : testMap V, (ξ : ℝ × ℝ → V) ∈ S → jetₗ V ξ ∈ C) :
    (H1 S : Set (Lp (V × V × V) 2 stripMeasure)) ⊆ C := by
  rw [coe_H1]
  exact closure_minimal (by rintro _ ⟨ξ, hξ, rfl⟩; exact h ξ hξ) hC

/-- `H1 S` is a closed subspace of `L²`. -/
theorem isClosed_H1 : IsClosed (H1 S : Set (Lp (V × V × V) 2 stripMeasure)) :=
  Submodule.isClosed_topologicalClosure _

/-- `H1 S` is complete: it is a closed subspace of the complete space `L²`. -/
instance [CompleteSpace V] : CompleteSpace (H1 S) :=
  Submodule.topologicalClosure.completeSpace _

/-- The jet of a test map in `S` lies in `H1 S`. -/
theorem jetₗ_mem_H1 {ξ : testMap V} (hξ : (ξ : ℝ × ℝ → V) ∈ S) : jetₗ V ξ ∈ H1 S :=
  Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem hξ)

/-- `H1` is monotone in the class of maps. -/
theorem H1_mono (h : S ≤ T) : H1 S ≤ H1 T :=
  Submodule.topologicalClosure_mono (Submodule.map_mono (Submodule.comap_mono h))

variable (S) in
/-- The value `(ξ, ξ_s, ξ_t) ↦ ξ` of an element of `H1 S`, in `L²(ℝ × [0, 1], V)`. It is
injective (`TauCeti.StripSobolev.valueL_injective`). -/
def valueL : H1 S →L[ℝ] Lp V 2 stripMeasure :=
  ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL 2 stripMeasure).comp (H1 S).subtypeL

/-- The value of an element of `H1 S` is represented by the first component of its jet. -/
theorem coeFn_valueL (x : H1 S) :
    valueL S x =ᵐ[stripMeasure] fun z ↦ ((x : Lp (V × V × V) 2 stripMeasure) z).1 :=
  (ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLpL _

/-! ### Pairing `L²` jets with `L²` coefficients -/

section Pairing

variable {A F : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [NormedAddCommGroup F]
  [NormedSpace ℝ F] (B : A →L[ℝ] V →L[ℝ] F) (P : V × V × V →L[ℝ] V) {g₁ g₂ : ℝ × ℝ → A}

/-- Pairing the `L²` jet of a test map `ξ` with coefficients `g₁` and `g₂` in `L²`, through a
continuous bilinear map `B`, on a component `P` of the jet and on the value, gives the integral of
the same pairing with the jet of `ξ`. -/
theorem integral_jetₗ_add_eq_integral (hg₁ : MemLp g₁ 2 stripMeasure)
    (hg₂ : MemLp g₂ 2 stripMeasure) (ξ : testMap V) :
    ∫ z, B (g₁ z) (P (jetₗ V ξ z)) ∂stripMeasure + ∫ z, B (g₂ z) (jetₗ V ξ z).1 ∂stripMeasure =
      ∫ z, (B (g₁ z) (P (jet (ξ : ℝ × ℝ → V) z)) + B (g₂ z) ((ξ : ℝ × ℝ → V) z))
        ∂stripMeasure := by
  have hj := memLp_jet ξ.2
  have hint₁ : Integrable (fun z ↦ B (g₁ z) (P (jet (ξ : ℝ × ℝ → V) z))) stripMeasure :=
    memLp_one_iff_integrable.1 (B.memLp_of_bilin 1 hg₁ (P.comp_memLp' hj))
  have hint₂ : Integrable (fun z ↦ B (g₂ z) ((ξ : ℝ × ℝ → V) z)) stripMeasure :=
    memLp_one_iff_integrable.1
      (B.memLp_of_bilin 1 hg₂ ((ContinuousLinearMap.fst ℝ V (V × V)).comp_memLp' hj))
  rw [integral_add hint₁ hint₂]
  congr 1 <;> exact integral_congr_ae ((coeFn_jetₗ ξ).mono fun z hz ↦ by simp [hz, jet_apply])

variable [CompleteSpace F]

/-- **Pairing identities pass from the test maps in `S` to `H1 S`.** Let `B` be a continuous
bilinear map, `g₁` and `g₂` coefficients in `L²` and `P` a component of the jet. If
`∫ B g₁ (P (jet ξ)) + B g₂ ξ` vanishes for every test map `ξ` in `S`, then
`∫ B g₁ (P x) + ∫ B g₂ x₁ = 0` for every `L²` jet `x = (x₁, x_s, x_t)` in `H1 S`: the left side is
a continuous linear functional of `x`, vanishing on the jets of the test maps in `S`. -/
theorem integral_add_eq_zero_of_mem_H1 (hg₁ : MemLp g₁ 2 stripMeasure)
    (hg₂ : MemLp g₂ 2 stripMeasure)
    (h : ∀ ξ : testMap V, (ξ : ℝ × ℝ → V) ∈ S →
      ∫ z, (B (g₁ z) (P (jet (ξ : ℝ × ℝ → V) z)) + B (g₂ z) ((ξ : ℝ × ℝ → V) z))
        ∂stripMeasure = 0)
    {x : Lp (V × V × V) 2 stripMeasure} (hx : x ∈ H1 S) :
    ∫ z, B (g₁ z) (P (x z)) ∂stripMeasure + ∫ z, B (g₂ z) (x z).1 ∂stripMeasure = 0 := by
  set L : Lp (V × V × V) 2 stripMeasure →L[ℝ] F :=
    (B.lpPairing stripMeasure 2 2 (hg₁.toLp g₁)).comp (P.compLpL 2 stripMeasure) +
      (B.lpPairing stripMeasure 2 2 (hg₂.toLp g₂)).comp
        ((ContinuousLinearMap.fst ℝ V (V × V)).compLpL 2 stripMeasure)
  have hL : ∀ f : Lp (V × V × V) 2 stripMeasure, L f =
      ∫ z, B (g₁ z) (P (f z)) ∂stripMeasure + ∫ z, B (g₂ z) (f z).1 ∂stripMeasure := by
    intro f
    simp only [L, add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.lpPairing_eq_integral]
    congr 1 <;> refine integral_congr_ae ?_
    · filter_upwards [hg₁.coeFn_toLp, P.coeFn_compLpL f] with z h₁ h₂
      simp [h₁, h₂]
    · filter_upwards [hg₂.coeFn_toLp,
        (ContinuousLinearMap.fst ℝ V (V × V)).coeFn_compLpL f] with z h₁ h₂
      simp [h₁, h₂]
  have hker : (H1 S : Set (Lp (V × V × V) 2 stripMeasure)) ⊆ {f | L f = 0} :=
    H1_subset_of_isClosed (isClosed_eq L.continuous continuous_const) fun ξ hξ ↦ by
      rw [mem_ofPred_eq, hL, integral_jetₗ_add_eq_integral B P hg₁ hg₂, h ξ hξ]
  rw [← hL]
  exact hker hx

end Pairing

/-! ### Elements of `H1 S` are determined by their values -/

section Value

/-- The open strip `ℝ × (0, 1)`, of full measure in the closed strip. -/
private theorem ae_mem_openStrip : ∀ᵐ z ∂stripMeasure, z ∈ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1 := by
  rw [ae_restrict_iff' (MeasurableSet.univ.prod measurableSet_Icc)]
  have h : (volume : Measure (ℝ × ℝ)) ((univ : Set ℝ) ×ˢ ({0, 1} : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp [(Set.toFinite ({0, 1} : Set ℝ)).measure_zero]
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h] with z hz hzS
  refine ⟨mem_univ _, lt_of_le_of_ne hzS.2.1 fun h0 ↦ hz ⟨mem_univ _, ?_⟩,
    lt_of_le_of_ne hzS.2.2 fun h1 ↦ hz ⟨mem_univ _, ?_⟩⟩
  · simp [← h0]
  · simp [h1]

/-- Integration by parts against a test function supported in the open strip: the integral of
`φ ∂ ξ + (∂ φ) ξ` vanishes, in each of the two coordinate directions `e`. -/
private theorem integral_smul_fderiv_add_eq_zero {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφU : tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1)
    (hξ : ξ ∈ testMap V) {e : ℝ × ℝ} (he : e = (1, 0) ∨ e = (0, 1)) :
    ∫ z, (φ z • fderiv ℝ ξ z e + fderiv ℝ φ z e • ξ z) ∂stripMeasure = 0 := by
  obtain ⟨hξ1, R, hR⟩ := mem_testMap_iff.1 hξ
  set F : ℝ × ℝ → V := fun z ↦ φ z • fderiv ℝ ξ z e + fderiv ℝ φ z e • ξ z
  have hξd := hξ1.differentiable (by norm_num)
  have hφd := hφ.differentiable one_ne_zero
  have hFc : Continuous F :=
    ((hφ.continuous.smul ((hξ1.continuous_fderiv (by norm_num)).clm_apply continuous_const)).add
      (((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).smul hξ1.continuous))
  have hΦ : ∀ z, HasFDerivAt (fun w ↦ φ w • ξ w)
      (φ z • fderiv ℝ ξ z + (fderiv ℝ φ z).smulRight (ξ z)) z := fun z ↦
    (hφd z).hasFDerivAt.smul (hξd z).hasFDerivAt
  have hF : ∀ z, jet ξ z = 0 → F z = 0 := fun z h ↦ by
    simp only [jet, Prod.mk_eq_zero] at h
    have hd : fderiv ℝ ξ z e = 0 := by
      rcases he with rfl | rfl
      exacts [h.2.1, h.2.2]
    simp [F, hd, h.1]
  rw [integral_strip_eq_setIntegral_of_jet_eq_zero hR hF]
  rcases he with rfl | rfl
  · refine setIntegral_rect_eq_zero_of_hasDerivAt_fst (Φ := fun w ↦ φ w • ξ w) hFc
      (fun s t ↦ ?_) fun t ↦ ?_
    · have := (hΦ (s, t)).comp_hasDerivAt (f := fun x : ℝ ↦ (x, t)) s
        (HasDerivAt.prodMk (hasDerivAt_id' s) (hasDerivAt_const s t))
      simpa [F, Function.comp_def] using this
    · simp [hR R t (le_abs_self R), hR (-R) t (by rw [abs_neg]; exact le_abs_self R)]
  · refine setIntegral_rect_eq_zero_of_hasDerivAt_snd (Φ := fun w ↦ φ w • ξ w) hFc
      (fun s t ↦ ?_) fun s ↦ ?_
    · have := (hΦ (s, t)).comp_hasDerivAt (f := fun x : ℝ ↦ (s, x)) t
        (HasDerivAt.prodMk (hasDerivAt_const t s) (hasDerivAt_id' t))
      simpa [F, Function.comp_def] using this
    · have h₀ : φ (s, 0) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hφU h).2.1.false
      have h₁ : φ (s, 1) = 0 := image_eq_zero_of_notMem_tsupport fun h ↦ (hφU h).2.2.false
      simp [h₀, h₁]

variable [CompleteSpace V]

/-- The weak derivative identity on `H1 S`: for an `L²` jet `x ∈ H1 S`, a test function `φ`
supported in the open strip and a coordinate direction `e`, with `P` the component of the jet
recording the derivative in the direction `e`, `∫ φ P(x) + ∫ (∂_e φ) x₁ = 0`. -/
private theorem integral_smul_add_eq_zero_of_mem_H1 {x : Lp (V × V × V) 2 stripMeasure}
    (hx : x ∈ H1 S) {φ : ℝ × ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ)
    (hφU : tsupport φ ⊆ (univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) {e : ℝ × ℝ}
    (he : e = (1, 0) ∨ e = (0, 1)) {P : V × V × V →L[ℝ] V}
    (hP : ∀ (ξ : ℝ × ℝ → V) z, P (jet ξ z) = fderiv ℝ ξ z e) :
    ∫ z, φ z • P (x z) ∂stripMeasure + ∫ z, fderiv ℝ φ z e • (x z).1 ∂stripMeasure = 0 := by
  have hφ₂ : MemLp φ 2 stripMeasure := hφ.continuous.memLp_of_hasCompactSupport hφs
  have hφe : MemLp (fun z ↦ fderiv ℝ φ z e) 2 stripMeasure :=
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφs.fderiv_apply (𝕜 := ℝ) e)
  have h := integral_add_eq_zero_of_mem_H1 (ContinuousLinearMap.lsmul ℝ ℝ) P hφ₂ hφe
    (fun ξ _ ↦ by
      simpa only [ContinuousLinearMap.lsmul_apply, hP] using
        integral_smul_fderiv_add_eq_zero hφ hφU ξ.2 he) hx
  simpa only [ContinuousLinearMap.lsmul_apply] using h

/-- On the open strip `ℝ × (0, 1)`, the derivative component `P x` of an `L²` jet `x ∈ H1 S` in
the coordinate direction `e` is the weak derivative of its value `x₁` in the direction `e`. -/
private theorem hasWeakLineDerivOn_of_mem_H1 {x : Lp (V × V × V) 2 stripMeasure} (hx : x ∈ H1 S)
    {e : ℝ × ℝ} (he : e = (1, 0) ∨ e = (0, 1)) {P : V × V × V →L[ℝ] V}
    (hP : ∀ (ξ : ℝ × ℝ → V) z, P (jet ξ z) = fderiv ℝ ξ z e) :
    HasWeakLineDerivOn stripMeasure ⟨univ ×ˢ Ioo 0 1, isOpen_univ.prod isOpen_Ioo⟩
      (fun z ↦ (x z).1) (fun z ↦ P (x z)) e := by
  have hloc : ∀ Q : V × V × V →L[ℝ] V, LocallyIntegrableOn (fun z ↦ Q (x z))
      (univ ×ˢ Ioo 0 1) stripMeasure := fun Q ↦
    (((memLp_congr_ae (Q.coeFn_compLpL x)).1 (Lp.memLp _)).locallyIntegrable
      (by norm_num)).locallyIntegrableOn _
  refine hasWeakLineDerivOn_iff_testFunction.2
    ⟨inferInstance, hloc (ContinuousLinearMap.fst ℝ V (V × V)), hloc P, fun φ ↦ ?_⟩
  have hl : ∀ z, lineDeriv ℝ (φ : ℝ × ℝ → ℝ) z e = fderiv ℝ φ z e := fun z ↦
    ((φ.contDiff.differentiable (by simp)) z).lineDeriv_eq_fderiv
  simp_rw [hl]
  refine eq_neg_of_add_eq_zero_left ?_
  rw [add_comm]
  exact integral_smul_add_eq_zero_of_mem_H1 hx (φ.contDiff.of_le (by simp)) φ.hasCompactSupport
    φ.tsupport_subset he hP

/-- **An element of `H1 S` is determined by its value.** The value map `(ξ, ξ_s, ξ_t) ↦ ξ` is
injective on `H1 S`: if the value of an `L²` jet in `H1 S` vanishes, so do its derivative
components, as they are its weak derivatives. Thus `H1 S` is a space of maps on the strip, a
subspace of the Sobolev space `W^{1,2}(ℝ × [0, 1], V)`. -/
theorem valueL_injective : Function.Injective (valueL S) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  have hx₁ : ∀ᵐ z ∂stripMeasure, ((x : Lp (V × V × V) 2 stripMeasure) z).1 = 0 := by
    have h := coeFn_valueL x
    rw [hx] at h
    filter_upwards [h, Lp.coeFn_zero V 2 stripMeasure] with z h₁ h₂
    simpa using h₁.symm.trans h₂
  have hΩ : stripMeasure.restrict ((univ : Set ℝ) ×ˢ Ioo (0 : ℝ) 1) = stripMeasure :=
    Measure.restrict_eq_self_of_ae_mem ae_mem_openStrip
  -- Each derivative component vanishes almost everywhere, as the weak derivative of `0`.
  have hcomp : ∀ {e : ℝ × ℝ} {P : V × V × V →L[ℝ] V}, (e = (1, 0) ∨ e = (0, 1)) →
      (∀ (ξ : ℝ × ℝ → V) z, P (jet ξ z) = fderiv ℝ ξ z e) →
      ∀ᵐ z ∂stripMeasure, P ((x : Lp (V × V × V) 2 stripMeasure) z) = 0 := by
    intro e P he hP
    have h := (hasWeakLineDerivOn_of_mem_H1 x.2 he hP).ae_eq_zero_of_isOpen isOpen_univ
      (ae_restrict_of_ae (hx₁.mono fun z hz _ ↦ hz))
    simp only [TopologicalSpace.Opens.coe_mk, hΩ] at h
    exact h.mono fun z hz ↦ hz (mem_univ z)
  have h₂ := hcomp (Or.inl rfl) (P := (ContinuousLinearMap.fst ℝ V V).comp
    (ContinuousLinearMap.snd ℝ V (V × V))) fun ξ z ↦ rfl
  have h₃ := hcomp (Or.inr rfl) (P := (ContinuousLinearMap.snd ℝ V V).comp
    (ContinuousLinearMap.snd ℝ V (V × V))) fun ξ z ↦ rfl
  refine Subtype.ext ((Lp.eq_zero_iff_ae_eq_zero).2 ?_)
  filter_upwards [hx₁, h₂, h₃] with z h₁ h₂ h₃
  exact Prod.ext h₁ (Prod.ext h₂ h₃)

end Value

/-! ### Translations along the strip -/

section Translation

/-- The translation `(s, t) ↦ (s + a, t)` preserves the measure of the strip. -/
theorem measurePreserving_add_fst (a : ℝ) :
    MeasurePreserving (· + ((a, 0) : ℝ × ℝ)) stripMeasure stripMeasure := by
  have h := (measurePreserving_add_right (volume : Measure (ℝ × ℝ)) (a, 0)).restrict_preimage
    (MeasurableSet.univ.prod (measurableSet_Icc (a := (0 : ℝ)) (b := 1)))
  have hpre : (· + ((a, 0) : ℝ × ℝ)) ⁻¹' (univ ×ˢ Icc (0 : ℝ) 1) = univ ×ˢ Icc 0 1 := by
    ext z
    simp
  rwa [hpre] at h

/-- Taking jets commutes with translations along the strip. -/
theorem jet_comp_add (ξ : ℝ × ℝ → V) (a : ℝ) :
    jet (fun z ↦ ξ (z + (a, 0))) = fun z ↦ jet ξ (z + (a, 0)) := by
  funext z
  simp [jet, fderiv_comp_add_right]

/-- The translate of a test map is a test map. -/
theorem comp_add_mem_testMap (hξ : ξ ∈ testMap V) (a : ℝ) :
    (fun z ↦ ξ (z + (a, 0))) ∈ testMap V := by
  obtain ⟨hξ2, R, hR⟩ := mem_testMap_iff.1 hξ
  refine ⟨hξ2.comp (contDiff_id.add contDiff_const), R + |a|, fun s t hs ↦ ?_⟩
  have h := abs_sub_abs_le_abs_sub s (-a)
  rw [abs_neg, sub_neg_eq_add] at h
  simpa using hR (s + a) t (by linarith)

/-- The translate of a test map, as a test map. -/
private def translateTestMap (a : ℝ) (ξ : testMap V) : testMap V :=
  ⟨fun z ↦ (ξ : ℝ × ℝ → V) (z + (a, 0)), comp_add_mem_testMap ξ.2 a⟩

/-- Translating an `L²` jet along the strip carries the jet of a test map to the jet of its
translate. -/
private theorem compMeasurePreserving_jetₗ (a : ℝ) (ξ : testMap V) :
    Lp.compMeasurePreserving _ (measurePreserving_add_fst a) (jetₗ V ξ) =
      jetₗ V (translateTestMap a ξ) := by
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_compMeasurePreserving (jetₗ V ξ) (measurePreserving_add_fst a),
    (measurePreserving_add_fst a).quasiMeasurePreserving.ae_eq_comp (coeFn_jetₗ ξ),
    coeFn_jetₗ (translateTestMap a ξ)] with z h₁ h₂ h₃
  rw [h₁, h₂, h₃]
  simp [translateTestMap, jet_comp_add]

/-- If `S` is invariant under the translation by `a`, so is `H1 S`. -/
theorem compMeasurePreserving_mem_H1 {a : ℝ} (hS : ∀ ξ ∈ S, (fun z ↦ ξ (z + (a, 0))) ∈ S)
    {x : Lp (V × V × V) 2 stripMeasure} (hx : x ∈ H1 S) :
    Lp.compMeasurePreserving _ (measurePreserving_add_fst a) x ∈ H1 S := by
  have hc : Continuous (Lp.compMeasurePreserving (E := V × V × V) (p := 2) _
      (measurePreserving_add_fst a)) :=
    (Lp.isometry_compMeasurePreserving (measurePreserving_add_fst a)).continuous
  refine H1_subset_of_isClosed (isClosed_H1.preimage hc) (fun ξ hξ ↦ ?_) hx
  rw [mem_preimage, compMeasurePreserving_jetₗ]
  exact jetₗ_mem_H1 (hS _ hξ)

variable (S) in
/-- The translation `(s, t) ↦ (s + a, t)` acting on `H1 S`, for a class `S` of maps invariant
under it, as a linear isometry: the `W^{1,2}` norm on the strip is translation invariant. -/
def translateₗᵢ (a : ℝ) (hS : ∀ ξ ∈ S, (fun z ↦ ξ (z + (a, 0))) ∈ S) : H1 S →ₗᵢ[ℝ] H1 S where
  toLinearMap := (Lp.compMeasurePreservingₗ ℝ _ (measurePreserving_add_fst a)).restrict
    fun _ hx ↦ compMeasurePreserving_mem_H1 hS hx
  norm_map' x := Lp.norm_compMeasurePreserving (x : Lp (V × V × V) 2 stripMeasure) _

/-- The translate of an element of `H1 S` is its composition with the translation. -/
@[simp]
theorem coe_translateₗᵢ_apply {a : ℝ} (hS : ∀ ξ ∈ S, (fun z ↦ ξ (z + (a, 0))) ∈ S) (x : H1 S) :
    (translateₗᵢ S a hS x : Lp (V × V × V) 2 stripMeasure) =
      Lp.compMeasurePreserving _ (measurePreserving_add_fst a) x :=
  (rfl)

/-- The translate of an element of `H1 S` is represented by the translate of its jet. -/
theorem coeFn_translateₗᵢ {a : ℝ} (hS : ∀ ξ ∈ S, (fun z ↦ ξ (z + (a, 0))) ∈ S) (x : H1 S) :
    (translateₗᵢ S a hS x : Lp (V × V × V) 2 stripMeasure) =ᵐ[stripMeasure]
      fun z ↦ (x : Lp (V × V × V) 2 stripMeasure) (z + (a, 0)) :=
  Lp.coeFn_compMeasurePreserving _ _

/-- The translate of the jet of a test map is the jet of the translated test map. -/
theorem translateₗᵢ_jetₗ {a : ℝ} (hS : ∀ ξ ∈ S, (fun z ↦ ξ (z + (a, 0))) ∈ S) (ξ : testMap V)
    (hξ : (ξ : ℝ × ℝ → V) ∈ S) :
    translateₗᵢ S a hS ⟨jetₗ V ξ, jetₗ_mem_H1 hξ⟩ =
      ⟨jetₗ V ⟨fun z ↦ (ξ : ℝ × ℝ → V) (z + (a, 0)), comp_add_mem_testMap ξ.2 a⟩,
        jetₗ_mem_H1 (hS _ hξ)⟩ :=
  Subtype.ext (compMeasurePreserving_jetₗ a ξ)

end Translation

end TauCeti.StripSobolev
