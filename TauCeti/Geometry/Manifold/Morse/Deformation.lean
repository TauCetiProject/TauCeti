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
import TauCeti.Geometry.Manifold.MFDeriv.Curve
import TauCeti.Geometry.Manifold.Morse.CriticalPoints
import TauCeti.Geometry.Manifold.VectorField.ModelChart

/-!
# Deformation of sublevels

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

Following each point of the band down its flow line to the level `a` shows that the band itself is
a product: `f⁻¹[a, b]` is homeomorphic to `f⁻¹(a) × [a, b]` by a homeomorphism preserving the value
of `f` and fixing the level `f⁻¹(a)` (`TauCeti.exists_bandHomeomorph`).

Running such a flow for a longer time deforms the whole manifold, through maps along which `f`
never increases, so that `M_b` ends in the open sublevel `{f < a}`
(`TauCeti.exists_ambientSublevelDeformation`). Across a critical level `c` the same flow, built
away from a compact neighbourhood of the critical points, deforms `{f ≤ c + ε}` into
`{f < c - ε} ∪ U` for any open `U` containing the critical points of a compact band around `c`
(`TauCeti.exists_criticalLevelDeformation`). These critical points may be degenerate, and need
not be finite in number. Such ambient deformations are the steps of the Lusternik–Schnirelmann
bound on the number of critical points of a smooth function.

## Main declarations

* `TauCeti.exists_flow_apply_eq_sub_of_isCompact`: a flow by diffeomorphisms along which `f` never
  increases, lowering `f` at unit speed near a compact set without critical points.
* `TauCeti.exists_flow_apply_eq_sub`: such a flow lowering `f` at unit speed through a compact band
  without critical points.
* `TauCeti.exists_sublevelDeformation` and `TauCeti.exists_sublevelHomotopyEquiv`: the deformation
  retraction of `M_b` onto `M_a` and the resulting homotopy equivalence.
* `TauCeti.exists_diffeomorph_sublevel` and `TauCeti.exists_sublevelHomeomorph`: a diffeomorphism
  of `M` carrying `M_b` onto `M_a` and `f⁻¹(b)` onto `f⁻¹(a)`, and the resulting homeomorphism
  `M_b ≃ₜ M_a`.
* `TauCeti.exists_bandHomeomorph`: the product structure `f⁻¹[a, b] ≃ₜ f⁻¹(a) × [a, b]` of the
  band.
* `TauCeti.exists_ambientSublevelDeformation`: a deformation of `M` carrying `M_b` into `{f < a}`.
* `TauCeti.exists_criticalLevelDeformation`: a deformation of `M` carrying `{f ≤ c + ε}` into
  `{f < c - ε} ∪ U`, for arbitrary, possibly degenerate, critical points in `U`.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.1.
* J. Milnor, *Lectures on the h-cobordism theorem*, Princeton University Press, 1965,
  Theorem 3.4.
* O. Cornea, G. Lupton, J. Oprea and D. Tanré, *Lusternik–Schnirelmann Category*, Mathematical
  Surveys and Monographs 103, American Mathematical Society, 2003, Chapter 1.
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

/-- **A descending flow lowering `f` at unit speed near a compact set of regular points.** If `f`
is smooth and the compact set `K` contains no critical point of `f`, there is a flow `φ` on `M` by
smooth maps along which `f` never increases, and an open neighbourhood `U` of `K` such that `f`
decreases at unit speed along every orbit segment lying in `U`: if `φ s x ∈ U` for all
`s ∈ [r, t]`, then `f (φ t x) = f (φ r x) - (t - r)`. -/
theorem exists_flow_apply_eq_sub_of_isCompact (hf : ContMDiff I 𝓘(ℝ) ∞ f) {K : Set M}
    (hK : IsCompact K) (hreg : ∀ x ∈ K, mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ φ : Flow ℝ M, (∀ t, ContMDiff I I ∞ (φ t)) ∧ (∀ x, Antitone fun t ↦ f (φ t x)) ∧
      ∃ U, IsOpen U ∧ K ⊆ U ∧
        ∀ x r t, r ≤ t → (∀ s ∈ Icc r t, φ s x ∈ U) → f (φ t x) = f (φ r x) - (t - r) := by
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
  have hreg' : ∀ y ∈ e '' K, mfderiv 𝓘(ℝ, E) 𝓘(ℝ) f' y ≠ 0 := by
    rintro _ ⟨x, hx, rfl⟩ h0
    rw [hf'_def, he, BoundarylessModel.mfderiv_source_eq_zero_iff] at h0
    exact hreg x hx (by rwa [Homeomorph.symm_apply_apply] at h0)
  obtain ⟨X, hX, hXle, ⟨U, hUo, hKU, hXU⟩, C, hC, hXC⟩ :=
    exists_vectorField_mvfderiv_eq_neg_one hf' (hK.image e.continuous) hreg'
  have hX1 : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E).tangent 1
      (fun x ↦ (⟨x, X x⟩ : TangentBundle 𝓘(ℝ, E) M')) := hX.of_le (by simp)
  have hcomplete := isCompleteVectorField_of_isCompact_of_eq_zero_off hX1 hC hXC
  set ψ := globalFlow X hX1 hcomplete
  have hfd : MDifferentiable 𝓘(ℝ, E) 𝓘(ℝ) f' := hf'.mdifferentiable (by simp)
  -- Conjugate the flow on `M'` back to `M`.
  have hφ : ∀ t x, f (e.symm.conjFlow ψ t x) = f' (ψ t (e x)) := fun t x ↦ by
    rw [Homeomorph.conjFlow_apply, Homeomorph.symm_symm, hf'_def, comp_apply]
  refine ⟨e.symm.conjFlow ψ, fun t ↦ ?_, fun x ↦ ?_, e ⁻¹' U, hUo.preimage e.continuous,
    fun x hx ↦ hKU ⟨x, hx, rfl⟩, fun x r t hrt hU ↦ ?_⟩
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
  -- Along the orbit segment in `U`, `f` has derivative `-1`.
  have hd : ∀ s ∈ Icc r t, HasDerivAt (fun s ↦ f' (ψ s (e x))) (-1) s := by
    intro s hs
    have hsU : ψ s (e x) ∈ U := by
      simpa [Homeomorph.conjFlow_apply] using hU s hs
    have h := Manifold.hasDerivAt_comp_curve (hfd _)
      (isMIntegralCurve_globalFlow hX1 hcomplete (e x) s)
    rwa [hXU _ hsU] at h
  simp only [hφ]
  exact eq_of_has_deriv_right_eq (f' := fun _ ↦ -1)
    (fun s hs ↦ (hd s (Ico_subset_Icc_self hs)).hasDerivWithinAt)
    (fun s _ ↦ ((hasDerivAt_id s).sub_const r).const_sub _ |>.hasDerivWithinAt)
    (fun s hs ↦ (hd s hs).continuousAt.continuousWithinAt) (by fun_prop) (by simp)
    t ⟨hrt, le_rfl⟩

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
  obtain ⟨φ, hφs, hanti, U, hU, hKU, hφU⟩ :=
    exists_flow_apply_eq_sub_of_isCompact hf hcompact fun x hx ↦ hreg x hx.1 hx.2
  -- An orbit passing through `U` at time `u` stays in `U` for a while after `u`.
  have hnear : ∀ x u, φ u x ∈ U → ∃ η > 0, ∀ s ∈ Icc u (u + η), φ s x ∈ U := by
    intro x u hu
    obtain ⟨η, hη, hball⟩ :=
      Metric.isOpen_iff.1 (hU.preimage (φ.continuous continuous_id continuous_const)) u hu
    refine ⟨η / 2, by positivity, fun s hs ↦ hball ?_⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hs.1, hs.2]
  refine ⟨φ, hφs, hanti, fun x t hxa hxb ht ↦ ?_, fun x t ht hxt hxb ↦ ?_⟩
  · obtain ⟨η, hη, hηU⟩ := hnear x 0 (by rw [φ.map_zero_apply]; exact hKU ⟨hxa, hxb⟩)
    have h := hφU x 0 (min η t) (by positivity) fun s hs ↦
      hηU s ⟨hs.1, by linarith [hs.2, min_le_left η t]⟩
    rw [φ.map_zero_apply] at h
    calc f (φ t x) ≤ f (φ (min η t) x) := hanti x (min_le_right _ _)
      _ < f x := by rw [h]; linarith [lt_min hη ht]
  -- The set of times at which the unit-speed identity holds is closed and contains `0`; after any
  -- such time before `t` the orbit is in the band, hence in `U`, for a while.
  let S := {u : ℝ | f (φ u x) = f x - u}
  have hS : IsClosed S := isClosed_eq (hf.continuous.comp
    (φ.continuous continuous_id continuous_const)) (continuous_const.sub continuous_id)
  suffices Icc 0 t ⊆ S from this ⟨ht, le_rfl⟩
  refine (hS.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsWithin ?_ ?_
  · simp [S]
  rintro u ⟨hu, hu0, hut⟩
  have hu' : f (φ u x) = f x - u := hu
  obtain ⟨η, hη, hηU⟩ :=
    hnear x u (hKU ⟨by rw [hu']; linarith, by rw [hu']; linarith⟩)
  filter_upwards [Ioo_mem_nhdsGT (show u < u + η by linarith)] with s hs
  have h := hφU x u s hs.1.le fun r hr ↦ hηU r ⟨hr.1, hr.2.trans hs.2.le⟩
  simp only [S, mem_ofPred_eq]
  linarith

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
    ⟨φ.apply_le_iff_of_apply_eq_sub hf.continuous hab hanti' hφ x,
      φ.apply_eq_iff_of_apply_eq_sub hf.continuous hab hanti' hφ hφa x⟩⟩

/-- **Sublevels on either side of a band without critical points are homeomorphic**
(Milnor, Theorem 3.1). Under the hypotheses of `TauCeti.exists_diffeomorph_sublevel`, there is a
homeomorphism from `{f ≤ b}` to `{f ≤ a}` carrying the level `f⁻¹(b)` onto `f⁻¹(a)`. -/
theorem exists_sublevelHomeomorph (hf : ContMDiff I 𝓘(ℝ) ∞ f) (hab : a ≤ b)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ e : {x | f x ≤ b} ≃ₜ {x | f x ≤ a}, ∀ x, f (e x) = a ↔ f x = b := by
  obtain ⟨Φ, hΦ⟩ := exists_diffeomorph_sublevel hf hab hcompact hreg
  exact ⟨Φ.toHomeomorph.sets (ext fun x ↦ (hΦ x).1.symm), fun x ↦ (hΦ x).2⟩

/-- **A band without critical points is a product** (Milnor, *Lectures on the h-cobordism
theorem*, Theorem 3.4). If `f` is smooth and the band `f⁻¹[a, b]` is compact and contains no
critical point of `f`, then there is a homeomorphism `e : f⁻¹[a, b] ≃ₜ f⁻¹(a) × [a, b]` whose
second component is the value of `f` and which is the identity on the level `f⁻¹(a)`. In particular
each level `f⁻¹(s)`, `a ≤ s ≤ b`, is carried onto `f⁻¹(a) × {s}`. -/
theorem exists_bandHomeomorph (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ e : f ⁻¹' Icc a b ≃ₜ (f ⁻¹' {a}) × Icc a b,
      (∀ x, ((e x).2 : ℝ) = f x) ∧
        ∀ x : f ⁻¹' Icc a b, f x = a → ((e x).1 : M) = x := by
  rcases lt_or_ge b a with hba | hab
  · -- For `b < a` both sides are empty.
    have : IsEmpty (Icc a b) := by simp [hba]
    have : IsEmpty (f ⁻¹' Icc a b) := by simp [Icc_eq_empty_of_lt hba]
    exact ⟨.empty, fun x ↦ isEmptyElim x, fun x ↦ isEmptyElim x⟩
  obtain ⟨φ, -, hanti, hlt, hφ⟩ := exists_flow_apply_eq_sub hf hcompact hreg
  have hanti' : ∀ x, AntitoneOn (fun t ↦ f (φ t x)) (Ici 0) := fun x ↦ (hanti x).antitoneOn _
  have hφa : ∀ x t, f x = a → 0 < t → f (φ t x) < a := fun x t hx ht ↦
    (hlt x t hx.ge (hx.trans_le hab) ht).trans_eq hx
  exact ⟨φ.bandHomeomorph hf.continuous hanti' hφ hφa,
    φ.coe_bandHomeomorph_apply_snd hf.continuous hanti' hφ hφa,
    fun _ hx ↦ φ.coe_bandHomeomorph_apply_fst_of_apply_eq hf.continuous hanti' hφ hφa hx⟩

/-- **Deformation into an open lower sublevel across a band without critical points.** If `f` is
smooth and the band `f⁻¹[a, b]` is compact and contains no critical point of `f`, there is a
deformation `Φ` of the whole manifold `M`, starting at the identity, along which `f` never
increases and whose endpoint carries the closed sublevel `{f ≤ b}` into the open sublevel
`{f < a}`. -/
theorem exists_ambientSublevelDeformation (hf : ContMDiff I 𝓘(ℝ) ∞ f)
    (hcompact : IsCompact (f ⁻¹' Icc a b))
    (hreg : ∀ x, a ≤ f x → f x ≤ b → mfderiv I 𝓘(ℝ) f x ≠ 0) :
    ∃ Φ : C(unitInterval × M, M), (∀ x, Φ (0, x) = x) ∧ (∀ t x, f (Φ (t, x)) ≤ f x) ∧
      ∀ x, f x ≤ b → f (Φ (1, x)) < a := by
  obtain ⟨φ, -, hanti, hlt, hφ⟩ := exists_flow_apply_eq_sub hf hcompact hreg
  -- Every point of `{f ≤ b}` reaches the level `a` before the time `T`.
  set T := max (b - a) 0 + 1
  have hT0 : 0 ≤ T := by positivity
  refine ⟨⟨fun p ↦ φ (T * p.1) p.2, φ.continuous
    (continuous_const.mul (continuous_subtype_val.comp continuous_fst)) continuous_snd⟩,
    fun x ↦ by simp, fun t x ↦ ?_, fun x hx ↦ ?_⟩
  · simpa using hanti x (mul_nonneg hT0 t.2.1)
  simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, mul_one]
  rcases lt_or_ge (f x) a with hxa | hxa
  · exact (hanti x hT0).trans_lt (by simpa using hxa)
  have hs : f (φ (f x - a) x) = a := by
    rw [hφ x _ (by linarith) (by linarith) hx]
    ring
  have h := hlt (φ (f x - a) x) (T - (f x - a)) hs.ge (hs.trans_le (hxa.trans hx))
    (by linarith [le_max_left (b - a) 0])
  rwa [← Flow.map_add, sub_add_cancel, hs] at h

/-- **Deformation near a critical level.** Let `f` be smooth, let the band `f⁻¹[c - δ, c + δ]`,
`δ > 0`, be compact, and let `U` be an open set containing every critical point of `f` in this
band. Then for some `0 < ε < δ` there is a deformation `Φ` of the whole manifold `M`, starting at
the identity, along which `f` never increases and whose endpoint carries the sublevel
`{f ≤ c + ε}` into `{f < c - ε} ∪ U`.

No nondegeneracy, finiteness or isolation of the critical points is assumed. When the critical
points of the band all lie on the level `c`, this is the deformation across a critical level used
to bound the Lusternik–Schnirelmann category of `M` by the number of critical points of `f`. -/
theorem exists_criticalLevelDeformation (hf : ContMDiff I 𝓘(ℝ) ∞ f) {c δ : ℝ} (hδ : 0 < δ)
    (hcompact : IsCompact (f ⁻¹' Icc (c - δ) (c + δ))) {U : Set M} (hU : IsOpen U)
    (hcrit : ∀ x, c - δ ≤ f x → f x ≤ c + δ → mfderiv I 𝓘(ℝ) f x = 0 → x ∈ U) :
    ∃ ε, 0 < ε ∧ ε < δ ∧ ∃ Φ : C(unitInterval × M, M), (∀ x, Φ (0, x) = x) ∧
      (∀ t x, f (Φ (t, x)) ≤ f x) ∧ ∀ x, f x ≤ c + ε → f (Φ (1, x)) < c - ε ∨ Φ (1, x) ∈ U := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  -- The critical points of the band form a compact subset of `U`; choose a compact set `L ⊆ U`
  -- containing them in its interior.
  have hS : IsCompact (f ⁻¹' Icc (c - δ) (c + δ) ∩ {x | mfderiv I 𝓘(ℝ) f x = 0}) := by
    refine hcompact.inter_right ?_
    rw [← criticalPoints_eq_setOf_mfderiv_eq_zero]
    exact isClosed_criticalPoints (hf.of_le (by simp))
  obtain ⟨L, hL, hSL, hLU⟩ :=
    exists_compact_between hS hU fun x hx ↦ hcrit x hx.1.1 hx.1.2 hx.2
  -- A flow lowering `f` at unit speed on the band away from the interior of `L`.
  obtain ⟨φ, -, hanti, V, -, hKV, hφV⟩ := exists_flow_apply_eq_sub_of_isCompact hf
    (hcompact.diff isOpen_interior) fun x hx h0 ↦ hx.2 (hSL ⟨hx.1, h0⟩)
  -- The orbits of the points of `L` stay in `U` for a uniform positive time `τ`.
  obtain ⟨τ, hτ, hτU⟩ : ∃ τ > 0, ∀ s ∈ Icc 0 τ, ∀ y ∈ L, φ s y ∈ U := by
    have h : ∀ᶠ s in 𝓝 (0 : ℝ), ∀ y ∈ L, φ s y ∈ U :=
      hL.eventually_forall_of_forall_eventually fun y hy ↦
        (φ.continuous continuous_fst continuous_snd).continuousAt.preimage_mem_nhds
          (hU.mem_nhds (by simpa using hLU hy))
    obtain ⟨η, hη, hηU⟩ := Metric.eventually_nhds_iff.1 h
    refine ⟨η / 2, by positivity, fun s hs ↦ hηU ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
    linarith [hs.2]
  refine ⟨min (δ / 2) (τ / 3), by positivity, by linarith [min_le_left (δ / 2) (τ / 3)],
    ⟨fun p ↦ φ (τ * p.1) p.2, φ.continuous
      (continuous_const.mul (continuous_subtype_val.comp continuous_fst)) continuous_snd⟩,
    fun x ↦ by simp, fun t x ↦ by simpa using hanti x (mul_nonneg hτ.le t.2.1), fun x hx ↦ ?_⟩
  set ε := min (δ / 2) (τ / 3)
  have hεδ : ε ≤ δ / 2 := min_le_left _ _
  have hετ : ε ≤ τ / 3 := min_le_right _ _
  simp only [ContinuousMap.coe_mk, Set.Icc.coe_one, mul_one]
  by_contra! h
  -- Otherwise the orbit of `x` up to time `τ` stays in the band and never meets the interior of
  -- `L`, from which it would reach `U` at time `τ`; so `f` drops by `τ > 2 ε` along it.
  have hseg : ∀ s ∈ Icc 0 τ, φ s x ∈ f ⁻¹' Icc (c - δ) (c + δ) \ interior L := by
    intro s hs
    have h1 : f (φ τ x) ≤ f (φ s x) := hanti x hs.2
    have h2 : f (φ s x) ≤ f x := by simpa using hanti x hs.1
    refine ⟨⟨by linarith, by linarith⟩, fun hsL ↦ h.2 ?_⟩
    have := hτU (τ - s) ⟨by linarith [hs.2], by linarith [hs.1]⟩ _ (interior_subset hsL)
    rwa [← Flow.map_add, sub_add_cancel] at this
  have := hφV x 0 τ hτ.le fun s hs ↦ hKV (hseg s hs)
  rw [φ.map_zero_apply] at this
  linarith

end Flow

end TauCeti
