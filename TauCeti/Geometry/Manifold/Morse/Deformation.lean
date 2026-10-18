/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.ModelTransport.Boundaryless
public import TauCeti.Topology.Order.Sublevel
import TauCeti.Dynamics.Flow.Conjugacy
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# Deformation of sublevels across a band without critical points

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let
`a ≤ b` be such that the band `f⁻¹[a, b]` is compact and contains no critical point of `f`. Then
the sublevel `M_b = {f ≤ b}` deformation retracts onto `M_a = {f ≤ a}`, by a homotopy fixing
`M_a` pointwise (`TauCeti.exists_sublevelDeformation`); in particular the inclusion of `M_a` into
`M_b` is a homotopy equivalence (`TauCeti.exists_sublevelHomotopyEquiv`). The manifold itself need
not be compact, nor σ-compact.

Following Milnor, the deformation is the flow of a vector field `X` with `df(X) = -1` on the band,
along which `f` decreases at unit speed.

## Main declarations

* `TauCeti.exists_flow_apply_eq_sub`: a flow lowering `f` at unit speed through a compact band
  without critical points.
* `TauCeti.exists_sublevelDeformation` and `TauCeti.exists_sublevelHomotopyEquiv`: the deformation
  retraction of `M_b` onto `M_a` and the resulting homotopy equivalence.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1.
-/

public section

open Function Set Topology
open scoped ContDiff Manifold

namespace TauCeti

section Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [I.Boundaryless]
  [IsManifold I ∞ M] {f : M → ℝ} {a b : ℝ}

/-- **A unit-speed descending flow across a band without critical points.** If `f` is smooth and
the band `f⁻¹[a, b]` is compact and contains no critical point of `f`, there is a flow on `M` along
which `f` decreases at unit speed through the band: if `f x ≤ b`, `t ≥ 0` and `f x - t ≥ a`, then
`f (φ t x) = f x - t`. -/
theorem exists_flow_apply_eq_sub (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ φ : Flow ℝ M, ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t := by
  -- Work on the self-modelled copy `M'` of `M`, which has the same topology.
  set e := BoundarylessModel.homeomorph I M with he
  let M' := BoundarylessModel I M
  set f' : M' → ℝ := f ∘ e.symm with hf'_def
  have : T2Space M' := e.symm.isEmbedding.t2Space
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hf' : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f' := by
    have h := (BoundarylessModel.diffeomorph I (M := M) ∞).symm.contMDiff
    rw [BoundarylessModel.coe_diffeomorph_symm, ← he] at h
    exact hf.comp h
  have hK : IsCompact (f' ⁻¹' Icc a b) := by
    have : f' ⁻¹' Icc a b = e '' (f ⁻¹' Icc a b) := by
      rw [e.image_eq_preimage_symm, hf'_def, preimage_comp]
    rw [this]
    exact hcompact.image e.continuous
  have hreg' : ∀ y ∈ f' ⁻¹' Icc a b, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f' y ≠ 0 := by
    intro y hy h0
    rw [hf'_def, he, BoundarylessModel.mfderiv_source_eq_zero_iff] at h0
    exact hreg (e.symm y) hy.1 hy.2 h0
  obtain ⟨X, hX, ⟨U, hUo, hKU, hXU⟩, C, hC, hXC⟩ :=
    exists_vectorField_mvfderiv_eq_neg_one hf' hK hreg'
  have hX1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M')) := hX.of_le (by simp)
  have hcomplete := isCompleteVectorField_of_isCompact_of_eq_zero_off hX1 hC hXC
  -- Conjugate the flow on `M'` back to `M`.
  have hfx : ∀ x, f' (e x) = f x := fun x ↦ by simp [hf'_def]
  refine ⟨e.symm.conjFlow (globalFlow X hX1 hcomplete), fun x t ht hxt hxb ↦ ?_⟩
  rw [← hfx] at hxt hxb
  have h := apply_globalFlow_eq_sub hX1 hcomplete hf'.continuous hUo hXU
    (fun y h1 h2 ↦ hKU ⟨h1, h2⟩) ht hxt hxb
  rw [Homeomorph.conjFlow_apply, Homeomorph.symm_symm]
  rwa [hfx, hf'_def, comp_apply] at h

/-- **Deformation of sublevels across a band without critical points** (Milnor, Theorem 3.1). If
`f` is smooth, `a ≤ b`, and the band `f⁻¹[a, b]` is compact and contains no critical point of `f`,
then the sublevel `{f ≤ a}` is a strong deformation retract of `{f ≤ b}`: there is a retraction
`r` of `{f ≤ b}` onto `{f ≤ a}` and a homotopy from the inclusion of `r` to the identity fixing
`{f ≤ a}` pointwise. -/
theorem exists_sublevelDeformation (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ r : C({x | f x ≤ b}, {x | f x ≤ a}),
      (∀ x, r (sublevelInclusion f a b hab x) = x) ∧
      Nonempty (ContinuousMap.HomotopyRel
        ((sublevelInclusion f a b hab).comp r)
        (ContinuousMap.id _) {x | f x ≤ a}) := by
  obtain ⟨φ, hφ⟩ := exists_flow_apply_eq_sub hf hcompact hreg
  exact exists_sublevelDeformation_of_apply_eq_sub hf.continuous hab φ φ.cont' φ.map_zero_apply hφ

/-- **The sublevels on either side of a band without critical points are homotopy equivalent.**
Under the hypotheses of `TauCeti.exists_sublevelDeformation`, the inclusion of `{f ≤ a}` into
`{f ≤ b}` is a homotopy equivalence. -/
theorem exists_sublevelHomotopyEquiv (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ e : ContinuousMap.HomotopyEquiv {x | f x ≤ a} {x | f x ≤ b},
      ∀ x : {x | f x ≤ a}, (e x : M) = x := by
  obtain ⟨r, hr, ⟨F⟩⟩ := exists_sublevelDeformation hf hab hcompact hreg
  refine ⟨
    { toFun := sublevelInclusion f a b hab
      invFun := r
      left_inv := ?_
      right_inv := ⟨F.toHomotopy⟩ }, coe_sublevelInclusion_apply f hab⟩
  have : r.comp (sublevelInclusion f a b hab) =
      ContinuousMap.id _ := ContinuousMap.ext hr
  exact this ▸ .refl _

end Flow

end TauCeti
