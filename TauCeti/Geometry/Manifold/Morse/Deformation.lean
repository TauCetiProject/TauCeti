/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Geometry.Manifold.IntegralCurve.GlobalFlow
public import TauCeti.Geometry.Manifold.IntegralCurve.Monotone
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
along which `f` decreases at unit speed. Since `df(X) ≤ 0` everywhere, the time-`(b - a)` map of
this flow is a diffeomorphism of `M` carrying `M_b` onto `M_a` and the level `f⁻¹(b)` onto
`f⁻¹(a)` (`TauCeti.exists_diffeomorph_sublevel`); in particular `M_b` is homeomorphic to `M_a`
(`TauCeti.exists_sublevelHomeomorph`).

## Main declarations

* `TauCeti.exists_flow_apply_eq_sub`: a flow by diffeomorphisms along which `f` never increases,
  lowering `f` at unit speed through a compact band without critical points.
* `TauCeti.exists_sublevelDeformation` and `TauCeti.exists_sublevelHomotopyEquiv`: the deformation
  retraction of `M_b` onto `M_a` and the resulting homotopy equivalence.
* `TauCeti.exists_diffeomorph_sublevel` and `TauCeti.exists_sublevelHomeomorph`: a diffeomorphism
  of `M` carrying `M_b` onto `M_a` and `f⁻¹(b)` onto `f⁻¹(a)`, and the resulting homeomorphism
  `M_b ≃ₜ M_a`.

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
the band `f⁻¹[a, b]` is compact and contains no critical point of `f`, there is a flow `φ` on `M`
by smooth maps along which `f` never increases, strictly decreases from every point of the band,
and decreases at unit speed through the band: if `f x ≤ b`, `t ≥ 0` and `f x - t ≥ a`, then
`f (φ t x) = f x - t`. -/
theorem exists_flow_apply_eq_sub (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ φ : Flow ℝ M, (∀ t, ContMDiff I I ∞ (φ t)) ∧ (∀ x, Antitone fun t ↦ f (φ t x)) ∧
      (∀ x t, a ≤ f x → f x ≤ b → 0 < t → f (φ t x) < f x) ∧
      ∀ x t, 0 ≤ t → a ≤ f x - t → f x ≤ b → f (φ t x) = f x - t := by
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
  obtain ⟨X, hX, hXle, ⟨U, hUo, hKU, hXU⟩, C, hC, hXC⟩ :=
    exists_vectorField_mvfderiv_eq_neg_one hf' hK hreg'
  have hX1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M')) := hX.of_le (by simp)
  have hcomplete := isCompleteVectorField_of_isCompact_of_eq_zero_off hX1 hC hXC
  set ψ := globalFlow X hX1 hcomplete
  have hfd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f' := hf'.mdifferentiable (by simp)
  -- Conjugate the flow on `M'` back to `M`.
  have hfx : ∀ x, f' (e x) = f x := fun x ↦ by simp [hf'_def]
  have hφ : ∀ t x, f (e.symm.conjFlow ψ t x) = f' (ψ t (e x)) := fun t x ↦ by
    rw [Homeomorph.conjFlow_apply, Homeomorph.symm_symm, hf'_def, comp_apply]
  refine ⟨e.symm.conjFlow ψ, fun t ↦ ?_, fun x ↦ ?_, fun x t hxa hxb ht ↦ ?_,
    fun x t ht hxt hxb ↦ ?_⟩
  · have h := (BoundarylessModel.diffeomorph I (M := M) ∞).symm.contMDiff.comp
      ((contMDiff_globalFlow_apply hcomplete le_top hX t).comp
        (BoundarylessModel.diffeomorph I (M := M) ∞).contMDiff)
    rw [BoundarylessModel.coe_diffeomorph_symm, BoundarylessModel.coe_diffeomorph, ← he] at h
    convert h using 1
    ext x
    rw [Homeomorph.conjFlow_apply, Homeomorph.symm_symm, comp_apply, comp_apply]
  · simp only [hφ]
    exact (isMIntegralCurve_globalFlow hX1 hcomplete (e x)).antitone_comp (fun _ ↦ hfd _)
      fun _ ↦ hXle _
  · have h := (isMIntegralCurve_globalFlow hX1 hcomplete (e x)).lt_of_mvfderiv_apply_lt_zero
      (fun _ ↦ hfd _) (fun _ ↦ hXle _) (s := 0) ?_ ht
    · rwa [Flow.map_zero_apply, hfx, ← hφ] at h
    rw [Flow.map_zero_apply, hXU _ (hKU ⟨by rwa [hfx], by rwa [hfx]⟩)]
    norm_num
  · rw [← hfx] at hxt hxb
    rw [hφ, apply_globalFlow_eq_sub hX1 hcomplete hf'.continuous hUo hXU
      (fun y h1 h2 ↦ hKU ⟨h1, h2⟩) ht hxt hxb, hfx]

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
  obtain ⟨φ, -, -, -, hφ⟩ := exists_flow_apply_eq_sub hf hcompact hreg
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

/-- **Sublevels on either side of a band without critical points are diffeomorphic**
(Milnor, Theorem 3.1). If `f` is smooth, `a ≤ b`, and the band `f⁻¹[a, b]` is compact and contains
no critical point of `f`, then there is a diffeomorphism `Φ` of `M` carrying the sublevel
`{f ≤ b}` onto `{f ≤ a}` and the level `f⁻¹(b)` onto `f⁻¹(a)`. -/
theorem exists_diffeomorph_sublevel (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ Φ : M ≃ₘ⟮I, I⟯ M, ∀ x, (f (Φ x) ≤ a ↔ f x ≤ b) ∧ (f (Φ x) = a ↔ f x = b) := by
  obtain ⟨φ, hφs, hanti, hlt, hφ⟩ := exists_flow_apply_eq_sub hf hcompact hreg
  have hanti' : ∀ x, AntitoneOn (fun t ↦ f (φ t x)) (Ici 0) := fun x ↦ (hanti x).antitoneOn _
  have hφa : ∀ x t, f x = a → 0 < t → f (φ t x) < a := fun x t hx ht ↦
    (hlt x t hx.ge (hx.trans_le hab) ht).trans_eq hx
  refine ⟨⟨(φ.toHomeomorph (b - a)).toEquiv, hφs (b - a), hφs (-(b - a))⟩, fun x ↦
    ⟨apply_flow_le_iff_of_apply_eq_sub φ hf.continuous hab hanti' hφ x,
      apply_flow_eq_iff_of_apply_eq_sub φ hf.continuous hab hanti' hφ hφa x⟩⟩

/-- **Sublevels on either side of a band without critical points are homeomorphic**
(Milnor, Theorem 3.1). Under the hypotheses of `TauCeti.exists_diffeomorph_sublevel`, there is a
homeomorphism from `{f ≤ b}` to `{f ≤ a}` carrying the level `f⁻¹(b)` onto `f⁻¹(a)`. -/
theorem exists_sublevelHomeomorph (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ e : {x | f x ≤ b} ≃ₜ {x | f x ≤ a}, ∀ x, f (e x) = a ↔ f x = b := by
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_sublevel hf hab hcompact hreg
  exact ⟨Φ.toHomeomorph.sets (ext fun x ↦ (hΦ x).1.symm), fun x ↦ (hΦ x).2⟩

end Flow

end TauCeti
