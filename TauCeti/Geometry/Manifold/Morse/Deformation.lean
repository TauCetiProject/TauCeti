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
import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import TauCeti.Dynamics.Flow.Conjugacy
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# Deformation of sublevels across a band without critical points

Let `f` be a smooth real function on a boundaryless finite-dimensional manifold `M`, and let
`a ≤ b` be such that the band `f⁻¹[a, b]` is compact and contains no critical point of `f`. Then
the sublevel `M_b = {f ≤ b}` deformation retracts onto `M_a = {f ≤ a}`, by a homotopy fixing
`M_a` pointwise (`TauCeti.exists_sublevelDeformation`); in particular the inclusion of `M_a` into
`M_b` is a homotopy equivalence (`TauCeti.exists_sublevelHomotopyEquiv`). The manifold itself need
not be compact, nor σ-compact.

Following Milnor, the deformation is the flow of a vector field `X` with `df(X) = -1` on the band.
Near each regular point a constant chart field, rescaled, has this property. Finitely many of these
local fields, cut off by smooth bump functions, cover the compact band; their sum `Y` has
`df(Y) = -g` for the sum `g` of the bump functions, and `g ≥ 1` near the band. Dividing `Y` by a
smooth positive modification of `g` gives a smooth field which is `-1`-normalized on a
neighbourhood of the band and vanishes outside a compact set
(`TauCeti.exists_vectorField_mvfderiv_eq_neg_one`). The field is therefore complete, and `f`
decreases at unit speed along its flow while the flow stays in the band
(`TauCeti.apply_globalFlow_eq_sub`). Following each point of `M_b` until it reaches the level `a`
is the required retraction (`TauCeti.exists_sublevelDeformation_of_apply_eq_sub`).

The field is built on a manifold modelled on its own model vector space; arbitrary boundaryless
models are reduced to this case through `TauCeti.BoundarylessModel`, which carries the same
topology (`TauCeti.exists_flow_apply_eq_sub`).

## Main declarations

* `TauCeti.exists_vectorField_mvfderiv_eq_neg_one`: a smooth, compactly supported vector field with
  `df(X) = -1` on a neighbourhood of a compact set of regular points.
* `TauCeti.apply_globalFlow_eq_sub`: `f` decreases at unit speed along the flow of such a field.
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

section VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] {f : M → ℝ}

/-- **A unit-speed descending field near a compact set of regular points.** If a compact set `K`
contains no critical point of the smooth function `f`, there is a smooth vector field `X`, vanishing
outside a compact set, with `df(X) = -1` on an open neighbourhood of `K`. -/
theorem exists_vectorField_mvfderiv_eq_neg_one (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ f) {K : Set M}
    (hK : IsCompact K) (hreg : ∀ x ∈ K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f x ≠ 0) :
    ∃ X : (x : M) → TangentSpace 𝓘(ℝ, E) x,
      ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞ (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
      (∃ U, IsOpen U ∧ K ⊆ U ∧ ∀ x ∈ U, mvfderiv 𝓘(ℝ, E) f x (X x) = -1) ∧
      ∃ C, IsCompact C ∧ ∀ x ∉ C, X x = 0 := by
  -- Near each `x ∈ K` take a local field `s x` with `df(s x) = -1` on `V x`, and a bump function
  -- `ρ x` supported in the interior of `V x`.
  choose V hV s hs hsf using fun x : K ↦ exists_mem_nhds_contMDiffOn_mvfderiv_eq_neg_one hf
    (hreg x x.2)
  choose ρ hρ using fun x : K ↦
    (SmoothBumpFunction.nhds_basis_tsupport (I := 𝓘(ℝ, E)) (x : M)).mem_iff.1
      (interior_mem_nhds.2 (hV x))
  -- Finitely many of the open sets where some `ρ x` is `1` cover `K`.
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x hx ↦ interior {y | ρ ⟨x, hx⟩ y = 1})
    fun x hx ↦ interior_mem_nhds.2 (ρ ⟨x, hx⟩).eventuallyEq_one
  -- `Y = ∑ ρ i • s i` has `df(Y) = -g` with `g = ∑ ρ i`, and `g ≥ 1` near `K`; divide by `g`,
  -- smoothly modified where `g < 1` so that it stays positive.
  set g : M → ℝ := fun y ↦ ∑ i ∈ t, ρ i y with hg
  set d : M → ℝ := fun y ↦ g y + (1 - Real.smoothTransition (g y)) with hd
  set Y : (y : M) → TangentSpace 𝓘(ℝ, E) y := fun y ↦ ∑ i ∈ t, ((ρ i : M → ℝ) • s i) y with hY
  have hg0 : ∀ y, 0 ≤ g y := fun y ↦ Finset.sum_nonneg fun i _ ↦ (ρ i).nonneg
  have hd0 : ∀ y, d y ≠ 0 := by
    intro y
    have h1 := Real.smoothTransition.le_one (g y)
    rcases (hg0 y).eq_or_lt with h | h
    · simp [hd, ← h]
    · exact (by linarith : 0 < d y).ne'
  have hgC : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ g := ContMDiff.sum fun i _ ↦ (ρ i).contMDiff
  have hdC : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) ∞ d :=
    hgC.add (contMDiff_const.sub (Real.smoothTransition.contDiff.contMDiff.comp hgC))
  have hYC : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun y ↦ (⟨y, Y y⟩ : TangentBundle 𝓘(ℝ, E) M)) :=
    ContMDiff.sum_section fun i _ ↦ ContMDiffOn.smul_section_of_tsupport
      (ρ i).contMDiff.contMDiffOn isOpen_interior (hρ i).2 ((hs i).mono interior_subset)
  have hdfY : ∀ y, mvfderiv 𝓘(ℝ, E) f y (Y y) = -g y := by
    intro y
    simp only [hY, hg, map_sum, Pi.smul_apply', map_smul, smul_eq_mul, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    by_cases hy : ρ i y = 0
    · simp [hy]
    · rw [hsf i y (interior_subset ((hρ i).2 (subset_closure hy))), mul_neg_one]
  refine ⟨fun y ↦ (d y)⁻¹ • Y y, ContMDiff.smul_section (hdC.inv₀ hd0) hYC,
    ⟨⋃ i ∈ t, interior {y | ρ i y = 1}, isOpen_biUnion fun _ _ ↦ isOpen_interior, ht, ?_⟩,
    ⋃ i ∈ t, tsupport (ρ i), t.isCompact_biUnion fun i _ ↦ (ρ i).hasCompactSupport, ?_⟩
  · intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.1 hy
    have h1 : 1 ≤ g y := by
      have := Finset.single_le_sum (fun j _ ↦ (ρ j).nonneg) hi (f := fun j ↦ ρ j y)
      rwa [(interior_subset hyi : ρ i y = 1)] at this
    have hdg : d y = g y := by simp [hd, Real.smoothTransition.one_of_one_le h1]
    rw [map_smul, hdfY, hdg, smul_eq_mul, mul_neg, inv_mul_cancel₀ (by linarith)]
  · intro y hy
    have h0 : ∀ i ∈ t, ρ i y = 0 := fun i hi ↦
      image_eq_zero_of_notMem_tsupport fun h ↦ hy (mem_iUnion₂.2 ⟨i, hi, h⟩)
    have hY0 : Y y = 0 := Finset.sum_eq_zero fun i hi ↦ by simp [h0 i hi]
    simp [hY0]

end VectorField

section Flow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M]
  {f : M → ℝ} {a b : ℝ}

/-- **Unit-speed descent along a flow.** Let `X` be a complete `C¹` vector field with
`df(X) = -1` on an open set `U` containing the band `a ≤ f ≤ b`. If `f x ≤ b`, then `f` decreases
at unit speed along the flow line of `x` until it reaches the level `a`. -/
theorem apply_globalFlow_eq_sub [IsManifold I 1 M] [BoundarylessManifold I M]
    {X : (x : M) → TangentSpace I x}
    (hX : ContMDiff I I.tangent 1 (fun y ↦ (⟨y, X y⟩ : TangentBundle I M)))
    (hcomplete : IsCompleteVectorField X) (hf : Continuous f) {U : Set M} (hU : IsOpen U)
    (hXU : ∀ y ∈ U, mvfderiv I f y (X y) = -1) (hband : ∀ y, a ≤ f y → f y ≤ b → y ∈ U)
    {x : M} {t : ℝ} (ht : 0 ≤ t) (hxt : a ≤ f x - t) (hxb : f x ≤ b) :
    f (globalFlow X hX hcomplete t x) = f x - t := by
  set γ : ℝ → M := fun u ↦ globalFlow X hX hcomplete u x
  have hγ : Continuous γ := (globalFlow X hX hcomplete).continuous continuous_id continuous_const
  -- The set of times at which the unit-speed identity holds is closed and contains `0`; near any
  -- such time before `t` the flow line stays in `U`, where `f ∘ γ + id` has zero derivative.
  let S := {u : ℝ | f (γ u) = f x - u}
  have hS : IsClosed S := isClosed_eq (hf.comp hγ) (continuous_const.sub continuous_id)
  suffices Icc 0 t ⊆ S from this ⟨ht, le_rfl⟩
  refine (hS.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin ?_ ?_
  · simp only [S, γ, mem_ofPred_eq, Flow.map_zero_apply, sub_zero]
  rintro u ⟨hu, hu0, hut⟩
  have hu' : f (γ u) = f x - u := hu
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (hU.preimage hγ) u
    (hband _ (by rw [hu']; linarith) (by rw [hu']; linarith))
  have hderiv : ∀ v ∈ Metric.ball u ε, HasDerivAt (fun w ↦ f (γ w) + w) 0 v := by
    intro v hv
    have hvU : γ v ∈ U := hball hv
    have hmd : MDifferentiableAt I 𝓘(ℝ) f (γ v) :=
      mdifferentiableAt_of_mvfderiv_apply_ne_zero (by rw [hXU _ hvU]; norm_num)
    have h := Manifold.hasDerivAt_comp_curve hmd (isMIntegralCurve_globalFlow hX hcomplete x v)
    rw [hXU _ hvU] at h
    have h' := h.add (hasDerivAt_id' v)
    rwa [neg_add_cancel] at h'
  have hconst : ∀ v ∈ Metric.ball u ε, f (γ v) + v = f (γ u) + u := fun v hv ↦
    Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball u ε).isPreconnected
      (fun w hw ↦ (hderiv w hw).differentiableAt.differentiableWithinAt)
      (fun w hw ↦ (hderiv w hw).deriv) hv (Metric.mem_ball_self hε)
  filter_upwards [nhdsWithin_le_nhds (Metric.ball_mem_nhds u hε)] with v hv
  simp only [S, mem_ofPred_eq]
  linarith [hconst v hv]

variable [I.Boundaryless] [IsManifold I ∞ M]

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
