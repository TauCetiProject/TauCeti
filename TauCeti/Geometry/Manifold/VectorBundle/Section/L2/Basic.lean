/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.LpSection.Basic
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Support

/-!
# Compactly supported Cⁿ sections in geometric L²

On a manifold, a compactly supported `C^n` section of a bundle with continuous fibre inner
products defines a square-integrable section for every measure that is finite on compact sets.
`ContMDiffSection.toL2` sends the section to its almost-everywhere class in `TauCeti.LpSection`.
Any regularity `n`, including `n = 0`, is allowed. Two sections have the same class exactly when
they agree almost everywhere, so the map is injective for a measure charging every nonempty open
set. Pairing the class with an `L²` section integrates the fibre inner product.
-/

public noncomputable section

open Bundle MeasureTheory Set TauCeti
open scoped Manifold ContDiff InnerProductSpace

namespace ContMDiffSection

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  [MeasurableSpace M] [OpensMeasurableSpace M] [SecondCountableTopology M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContinuousFiberNorm F V]
  {μ : Measure M} [IsFiniteMeasureOnCompacts μ] {n : ℕ∞ω}

omit [MeasurableSpace M] [OpensMeasurableSpace M] [SecondCountableTopology M]
  [ContinuousFiberNorm F V] in
/-- The fibre norm of a compactly supported section has compact support. -/
private theorem hasCompactSupport_norm (s : compactlySupported I F n V) :
    HasCompactSupport fun x ↦ ‖(s : Cₛ^n⟮I; F, V⟯) x‖ := by
  refine (mem_compactlySupported.1 s.property).of_isClosed_subset
    (_root_.isClosed_tsupport _) ?_
  rw [tsupport_def]
  exact closure_mono fun x hx ↦ norm_ne_zero_iff.1 hx

/-- A compactly supported `C^n` section defines a geometric L² class, with the given fibre
inner products and measure. -/
def toL2 (μ : Measure M) [IsFiniteMeasureOnCompacts μ] :
    compactlySupported I F n V →ₗ[ℝ] LpSection ℝ F V 2 μ where
  toFun s :=
    LpSection.mk (s : Cₛ^n⟮I; F, V⟯) (.of_continuous s.val.contMDiff.continuous)
      ((Continuous.norm_bundle_of_continuousFiberNorm s.val.contMDiff.continuous)
        |>.memLp_of_hasCompactSupport (hasCompactSupport_norm s))
  map_add' s t := by
    rw [LpSection.mk_add, LpSection.mk_eq_mk_iff]
    exact .of_forall fun x ↦ congrFun (coe_add (s : Cₛ^n⟮I; F, V⟯) t) x
  map_smul' c s := by
    rw [LpSection.mk_smul, LpSection.mk_eq_mk_iff]
    exact .of_forall fun x ↦ congrFun (coe_smul c (s : Cₛ^n⟮I; F, V⟯)) x

/-- The L² class of a compactly supported `C^n` section agrees almost everywhere with that
section. -/
theorem coeFn_toL2 (s : compactlySupported I F n V) :
    ∀ᵐ x ∂μ, toL2 μ s x = (s : Cₛ^n⟮I; F, V⟯) x :=
  LpSection.coeFn_mk _ _

/-- Two compactly supported `C^n` sections have the same L² class exactly when they agree
almost everywhere. -/
theorem toL2_eq_toL2_iff {s t : compactlySupported I F n V} :
    toL2 μ s = toL2 μ t ↔ ∀ᵐ x ∂μ, (s : Cₛ^n⟮I; F, V⟯) x = (t : Cₛ^n⟮I; F, V⟯) x :=
  LpSection.mk_eq_mk_iff

/-- For a measure charging every nonempty open set, distinct compactly supported `C^n` sections
have distinct L² classes. -/
theorem toL2_injective [μ.IsOpenPosMeasure] :
    Function.Injective (toL2 μ : compactlySupported I F n V → LpSection ℝ F V 2 μ) := by
  intro s t h
  -- The continuous fibre norm of `s - t` vanishes almost everywhere, hence everywhere.
  have hcont := Continuous.norm_bundle_of_continuousFiberNorm
    ((s : Cₛ^n⟮I; F, V⟯) - t).contMDiff.continuous
  have hzero := (hcont.ae_eq_iff_eq μ (continuous_const (y := (0 : ℝ)))).1 <|
    (toL2_eq_toL2_iff.1 h).mono fun x hx ↦ by simp [hx]
  refine Subtype.ext <| ContMDiffSection.ext fun x ↦ ?_
  simpa [sub_eq_zero] using congrFun hzero x

/-- Pairing a compactly supported `C^n` section with an L² section is the integral of the fibre
inner product. -/
theorem inner_toL2_left (s : compactlySupported I F n V) (u : LpSection ℝ F V 2 μ) :
    ⟪toL2 μ s, u⟫_ℝ = ∫ x, ⟪(s : Cₛ^n⟮I; F, V⟯) x, u x⟫_ℝ ∂μ := by
  conv_lhs => rw [← LpSection.mk_coeFn u]
  exact LpSection.inner_mk _ _ _ _

/-- The pointwise pairing of a compactly supported `C^n` section with an L² section is
integrable. -/
theorem integrable_inner_l2 (s : compactlySupported I F n V) (u : LpSection ℝ F V 2 μ) :
    Integrable (fun x ↦ ⟪(s : Cₛ^n⟮I; F, V⟯) x, u x⟫_ℝ) μ :=
  (LpSection.integrable_inner (toL2 μ s) u).congr
    ((coeFn_toL2 s).mono fun x hx ↦ congrArg (fun v ↦ ⟪v, u x⟫_ℝ) hx)

end ContMDiffSection
