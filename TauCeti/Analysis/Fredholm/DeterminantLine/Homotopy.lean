/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.OrientationCover
public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport
public import TauCeti.Topology.VectorBundle.Orientation.Cover.Character
import Mathlib.Topology.Homotopy.Lifting

/-!
# Homotopy invariance and covering monodromy of Fredholm determinant orientations

Along a path `T` of Fredholm operators between real Banach spaces, orientations of the
determinant lines `det (ker T t) ⊗ (det (F ⧸ range T t))^*` are transported by
`TauCeti.detLineOrientationTransport`. This file proves that the transport only depends on the
path up to homotopy relative to its endpoints, establishes path independence in convex sets of
Fredholm operators, and connects `detLineOrientationTransport` with covering monodromy and the
orientation sign character on the fundamental group of `{T : E →L[ℝ] F // T.IsFredholm}`.

Let `H : ℝ × ℝ → E →L[ℝ] F` be continuous and Fredholm on a rectangle
`[[s₀, s₁]] ×ˢ [[a, b]]`. Transporting an orientation of the determinant line at the corner
`H (s₀, a)` to the opposite corner `H (s₁, b)` along the left and top edges gives the same result
as transporting it along the bottom and right edges
(`TauCeti.detLineOrientationTransport_comm`). When the bottom and top edges are constant, that is,
when `H` is a homotopy of paths `t ↦ H (s₀, t)` and `t ↦ H (s₁, t)` relative to their endpoints,
the transports along the two paths agree (`TauCeti.detLineOrientationTransport_eq_of_homotopy`);
here the determinant lines of equal operators are identified by
`LinearMap.detLineCongrOfEq`, and transport along a path constant on the interval
of transport is this identification (`TauCeti.detLineOrientationTransport_eq_map_of_forall_eq`).

The proof is local. If a single kernel chart `ContinuousLinearMap.detLineChartEquiv` is valid
along a path, the transport keeps the reading of an orientation in that chart fixed
(`TauCeti.detLineOrientationTransport_detLineChartEquiv_symm`), so around a rectangle on which
one kernel chart is valid both ways of transporting read the same element of the chart. A
rectangle is cut into such small rectangles by two connectedness arguments: the set of `σ` for
which the law holds on `[[s₀, σ]] ×ˢ [[τ, τ']]` for all `τ'` near `τ` is open and closed in
`[[s₀, s₁]]`, since near each point of the edge at height `τ` there is a kernel chart; then the set
of `τ` for which the law holds on `[[s₀, s₁]] ×ˢ [[a, τ]]` is open and closed in `[[a, b]]`.
Small rectangles are combined by the concatenation and reversal laws of transport
(`TauCeti.detLineOrientationTransport_trans`, `TauCeti.detLineOrientationTransport_symm`).

## Main results

* `TauCeti.detLineOrientationTransport_detLineChartEquiv_symm`: transport within a kernel chart
  fixes the reading in the chart.
* `TauCeti.detLineOrientationTransport_eq_map_of_forall_eq`: transport along a path which is
  constant on the interval of transport is the identification of the determinant lines.
* `TauCeti.detLineOrientationTransport_map_detLineCongrOfEq`: transport along pointwise equal paths
  commutes with the identifications of the determinant lines of equal operators.
* `TauCeti.detLineOrientationTransport_comm`: transport around a rectangle commutes.
* `TauCeti.detLineOrientationTransport_eq_of_homotopy`: transport is invariant under homotopies
  relative to the endpoints.
* `TauCeti.detLineOrientationTransport_eq_of_homotopyRel`: endpoint-relative homotopy invariance
  between two separate paths `T₀, T₁ : ℝ → E →L[ℝ] F`.
* `TauCeti.detLineOrientationTransport_eq_of_convex`: path independence in a convex set of
  Fredholm operators.
* `TauCeti.IsDetLineCoherentOn.monodromy_orientationCoverMk`,
  `TauCeti.FredholmDetLine.quotientOrientationTransport`,
  `TauCeti.FredholmDetLine.pathOrientationTransport`: covering monodromy transport along paths and
  path homotopy classes, agreeing with `TauCeti.detLineOrientationTransport`.
* `TauCeti.FredholmDetLine.orientationMonodromySign`: the loop orientation sign character
  `FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀ →* ℤˣ`.

## References

* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
-/

public section

open Filter Set Topology ContinuousLinearMap TensorProduct Module

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

section Chart

variable {Λ G : Type*} [NormedAddCommGroup Λ] [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] {D₂ : Λ →L[ℝ] F}
  {q : E × Λ →L[ℝ] G}

/-- **Orientation transport within a kernel chart.** If a kernel chart is valid along the whole
path, transport carries the orientation read in the chart as `w` at `T a` to the orientation read
in the chart as `w` at `T b`. -/
theorem detLineOrientationTransport_detLineChartEquiv_symm {T : ℝ → E →L[ℝ] F} {a b : ℝ}
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t))
    (hq : ∀ t ∈ uIcc a b, (((T t).coprod D₂).prod q).IsInvertible)
    {w : TauCeti.detLine ℝ G ⊗[ℝ] Dual ℝ (TauCeti.detLine ℝ Λ)} (hw : w ≠ 0) :
    detLineOrientationTransport a b hT hF
        (rayOfNeZero ℝ ((detLineChartEquiv (T a) D₂ q (hq a left_mem_uIcc)).symm w)
          ((LinearEquiv.map_ne_zero_iff _).2 hw)) =
      rayOfNeZero ℝ ((detLineChartEquiv (T b) D₂ q (hq b right_mem_uIcc)).symm w)
        ((LinearEquiv.map_ne_zero_iff _).2 hw) := by
  classical
  -- The family read in the chart as `w` along the path.
  let v : ∀ t, (T t : E →ₗ[ℝ] F).detLine := fun t ↦
    if h : (((T t).coprod D₂).prod q).IsInvertible then (detLineChartEquiv (T t) D₂ q h).symm w
    else 0
  have hv (t : ℝ) (ht : t ∈ uIcc a b) : v t = (detLineChartEquiv (T t) D₂ q (hq t ht)).symm w :=
    dite_eq_left (hq t ht)
  have key := detLineOrientationTransport_rayOfNeZero hT hF
    (isDetLineCoherentOn_of_detLineChartEquiv_eq (v := v) hT hF hw fun t ht ↦
      ⟨hq t ht, by rw [hv t ht, LinearEquiv.apply_symm_apply]⟩)
  simp only [hv a left_mem_uIcc, hv b right_mem_uIcc] at key
  exact key

end Chart

section Constant

/-- **Transport along a constant path.** If the path `T` is constant on the interval of
transport, transport from `a` to `b` is the identification of the determinant lines of the equal
operators `T a` and `T b`. -/
theorem detLineOrientationTransport_eq_map_of_forall_eq {T : ℝ → E →L[ℝ] F} {a b : ℝ}
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t))
    (hTa : ∀ t ∈ uIcc a b, T t = T a) (o : Module.Ray ℝ (T a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT hF o =
      Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg _ (hTa b right_mem_uIcc).symm)) o := by
  classical
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  -- The family of images of `v₀` in the determinant lines of the equal operators `T t`.
  let v : ∀ t, (T t : E →ₗ[ℝ] F).detLine := fun t ↦
    if ht : T t = T a then LinearMap.detLineCongrOfEq (congrArg _ ht.symm) v₀ else 0
  have hv (t : ℝ) (ht : t ∈ uIcc a b) :
      v t = LinearMap.detLineCongrOfEq (congrArg _ (hTa t ht).symm) v₀ :=
    dite_eq_left (hTa t ht)
  -- A kernel chart at `T a` is valid along the path and reads every member of the family as the
  -- reading of `v₀`.
  obtain ⟨S, hS, G, hG, q, U, -, haU, hinv⟩ := (hF a left_mem_uIcc).exists_isOpen_kernelChart
  have hq : (((T a).coprod S.subtypeL).prod q).IsInvertible := hinv _ haU
  have key := detLineOrientationTransport_rayOfNeZero hT hF
    (isDetLineCoherentOn_of_detLineChartEquiv_eq (v := v) hT hF
      ((LinearEquiv.map_ne_zero_iff (detLineChartEquiv (T a) S.subtypeL q hq)).2 hv₀)
      fun t ht ↦ ⟨by rw [hTa t ht]; exact hq, by
        rw [hv t ht]
        exact detLineChartEquiv_detLineCongrOfEq (hTa t ht).symm S.subtypeL q hq _ v₀⟩)
  have ha : v a = v₀ := by
    rw [hv a left_mem_uIcc, LinearMap.detLineCongrOfEq_rfl, LinearEquiv.refl_apply]
  simp only [ha, hv b right_mem_uIcc] at key
  rw [Module.Ray.map_apply, key]

/-- **Transport along pointwise equal paths.** Transport along two pointwise equal paths agrees,
once the determinant lines of the equal operators at the endpoints are identified by
`LinearMap.detLineCongrOfEq`. -/
theorem detLineOrientationTransport_map_detLineCongrOfEq {T₁ T₂ : ℝ → E →L[ℝ] F}
    (h : ∀ t, T₁ t = T₂ t) {a b : ℝ} (hT₁ : ContinuousOn T₁ (uIcc a b))
    (hF₁ : ∀ t ∈ uIcc a b, IsFredholm (T₁ t)) (hT₂ : ContinuousOn T₂ (uIcc a b))
    (hF₂ : ∀ t ∈ uIcc a b, IsFredholm (T₂ t)) (o : Module.Ray ℝ (T₁ a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT₂ hF₂
        (Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg _ (h a))) o) =
      Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg _ (h b)))
        (detLineOrientationTransport a b hT₁ hF₁ o) := by
  obtain rfl : T₁ = T₂ := funext h
  simp only [LinearMap.detLineCongrOfEq_rfl, Module.Ray.map_refl, Equiv.refl_apply]

end Constant

section Square

variable {H : ℝ × ℝ → E →L[ℝ] F}

/-- The commutation of orientation transport around the rectangle `[[σ, σ']] ×ˢ [[τ, τ']]`:
transport from the corner `(σ, τ)` along the left and top edges agrees with transport along the
bottom and right edges, whenever the operators are continuous and Fredholm along the edges. -/
private def SquareLaw (H : ℝ × ℝ → E →L[ℝ] F) (σ σ' τ τ' : ℝ) : Prop :=
  ∀ (hl : ContinuousOn (fun t ↦ H (σ, t)) (uIcc τ τ'))
    (hl' : ∀ t ∈ uIcc τ τ', IsFredholm (H (σ, t)))
    (hr : ContinuousOn (fun t ↦ H (σ', t)) (uIcc τ τ'))
    (hr' : ∀ t ∈ uIcc τ τ', IsFredholm (H (σ', t)))
    (hb : ContinuousOn (fun s ↦ H (s, τ)) (uIcc σ σ'))
    (hb' : ∀ s ∈ uIcc σ σ', IsFredholm (H (s, τ)))
    (ht : ContinuousOn (fun s ↦ H (s, τ')) (uIcc σ σ'))
    (ht' : ∀ s ∈ uIcc σ σ', IsFredholm (H (s, τ')))
    (o : Module.Ray ℝ (H (σ, τ) : E →ₗ[ℝ] F).detLine),
    detLineOrientationTransport (T := fun s ↦ H (s, τ')) σ σ' ht ht'
        (detLineOrientationTransport (T := fun t ↦ H (σ, t)) τ τ' hl hl' o) =
      detLineOrientationTransport (T := fun t ↦ H (σ', t)) τ τ' hr hr'
        (detLineOrientationTransport (T := fun s ↦ H (s, τ)) σ σ' hb hb' o)

/-- The law holds around a rectangle on which one kernel chart is valid, since transport along
each edge keeps the reading in the chart fixed. -/
private theorem squareLaw_of_kernelChart {Λ G : Type*} [NormedAddCommGroup Λ]
    [NormedSpace ℝ Λ] [FiniteDimensional ℝ Λ] [NormedAddCommGroup G] [NormedSpace ℝ G]
    [FiniteDimensional ℝ G] {D₂ : Λ →L[ℝ] F} {q : E × Λ →L[ℝ] G} {σ σ' τ τ' : ℝ}
    (hq : ∀ x ∈ uIcc σ σ' ×ˢ uIcc τ τ', (((H x).coprod D₂).prod q).IsInvertible) :
    SquareLaw H σ σ' τ τ' := by
  intro hl hl' hr hr' hb hb' ht ht' o
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  have h₀ := hq (σ, τ) ⟨left_mem_uIcc, left_mem_uIcc⟩
  obtain ⟨w, rfl⟩ := (detLineChartEquiv (H (σ, τ)) D₂ q h₀).symm.surjective v₀
  have hw : w ≠ 0 := fun h ↦ hv₀ (by rw [h, map_zero])
  rw [detLineOrientationTransport_detLineChartEquiv_symm (T := fun t ↦ H (σ, t)) hl hl'
      (fun t ht ↦ hq _ ⟨left_mem_uIcc, ht⟩) hw,
    detLineOrientationTransport_detLineChartEquiv_symm (T := fun s ↦ H (s, τ')) ht ht'
      (fun s hs ↦ hq _ ⟨hs, right_mem_uIcc⟩) hw,
    detLineOrientationTransport_detLineChartEquiv_symm (T := fun s ↦ H (s, τ)) hb hb'
      (fun s hs ↦ hq _ ⟨hs, left_mem_uIcc⟩) hw,
    detLineOrientationTransport_detLineChartEquiv_symm (T := fun t ↦ H (σ', t)) hr hr'
      (fun t ht ↦ hq _ ⟨right_mem_uIcc, ht⟩) hw]

/-- The law holds around a rectangle of width zero. -/
private theorem squareLaw_self_left (σ τ τ' : ℝ) : SquareLaw H σ σ τ τ' := by
  intro hl hl' hr hr' hb hb' ht ht' o
  rw [detLineOrientationTransport_self, detLineOrientationTransport_self]
  rfl

/-- The law holds around a rectangle of height zero. -/
private theorem squareLaw_self_right (σ σ' τ : ℝ) : SquareLaw H σ σ' τ τ := by
  intro hl hl' hr hr' hb hb' ht ht' o
  rw [detLineOrientationTransport_self, detLineOrientationTransport_self]
  rfl

variable {s₀ s₁ a b : ℝ}

omit [CompleteSpace E] [CompleteSpace F] in
/-- Continuity along a vertical segment of the rectangle. -/
private theorem continuousOn_vertical (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b)) {σ τ τ' : ℝ}
    (hσ : σ ∈ uIcc s₀ s₁) (hτ : τ ∈ uIcc a b) (hτ' : τ' ∈ uIcc a b) :
    ContinuousOn (fun t ↦ H (σ, t)) (uIcc τ τ') :=
  hH.comp (Continuous.prodMk_right σ).continuousOn fun _ ht ↦ ⟨hσ, uIcc_subset_uIcc hτ hτ' ht⟩

omit [CompleteSpace E] [CompleteSpace F] in
/-- Continuity along a horizontal segment of the rectangle. -/
private theorem continuousOn_horizontal (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    {σ σ' τ : ℝ} (hσ : σ ∈ uIcc s₀ s₁) (hσ' : σ' ∈ uIcc s₀ s₁) (hτ : τ ∈ uIcc a b) :
    ContinuousOn (fun s ↦ H (s, τ)) (uIcc σ σ') :=
  hH.comp (Continuous.prodMk_left τ).continuousOn fun _ hs ↦ ⟨uIcc_subset_uIcc hσ hσ' hs, hτ⟩

/-- **Horizontal concatenation.** The law around two rectangles side by side gives the law around
their union. -/
private theorem SquareLaw.trans_left (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x)) {σ σ' σ'' τ τ' : ℝ}
    (hσ : σ ∈ uIcc s₀ s₁) (hσ' : σ' ∈ uIcc s₀ s₁) (hσ'' : σ'' ∈ uIcc s₀ s₁)
    (hτ : τ ∈ uIcc a b) (hτ' : τ' ∈ uIcc a b)
    (h₁ : SquareLaw H σ σ' τ τ') (h₂ : SquareLaw H σ' σ'' τ τ') : SquareLaw H σ σ'' τ τ' := by
  intro hl hl' hr hr' hb hb' ht ht' o
  have hm := continuousOn_vertical hH hσ' hτ hτ'
  have hm' (t : ℝ) (htt : t ∈ uIcc τ τ') : IsFredholm (H (σ', t)) :=
    hF _ ⟨hσ', uIcc_subset_uIcc hτ hτ' htt⟩
  have hF₁ (t : ℝ) (σ₁ σ₂ : ℝ) (h₁ : σ₁ ∈ uIcc s₀ s₁) (h₂ : σ₂ ∈ uIcc s₀ s₁) (htt : t ∈ uIcc a b)
      (s : ℝ) (hs : s ∈ uIcc σ₁ σ₂) : IsFredholm (H (s, t)) :=
    hF _ ⟨uIcc_subset_uIcc h₁ h₂ hs, htt⟩
  rw [← detLineOrientationTransport_trans (T := fun s ↦ H (s, τ'))
      (continuousOn_horizontal hH hσ hσ' hτ') (continuousOn_horizontal hH hσ' hσ'' hτ') ht
      (hF₁ τ' σ σ' hσ hσ' hτ') (hF₁ τ' σ' σ'' hσ' hσ'' hτ') ht',
    h₁ hl hl' hm hm' (continuousOn_horizontal hH hσ hσ' hτ) (hF₁ τ σ σ' hσ hσ' hτ),
    h₂ hm hm' hr hr' (continuousOn_horizontal hH hσ' hσ'' hτ) (hF₁ τ σ' σ'' hσ' hσ'' hτ),
    detLineOrientationTransport_trans (T := fun s ↦ H (s, τ))
      (continuousOn_horizontal hH hσ hσ' hτ) (continuousOn_horizontal hH hσ' hσ'' hτ) hb
      (hF₁ τ σ σ' hσ hσ' hτ) (hF₁ τ σ' σ'' hσ' hσ'' hτ) hb']

/-- **Vertical concatenation.** The law around two rectangles one above the other gives the law
around their union. -/
private theorem SquareLaw.trans_right (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x)) {σ σ' τ τ' τ'' : ℝ}
    (hσ : σ ∈ uIcc s₀ s₁) (hσ' : σ' ∈ uIcc s₀ s₁) (hτ : τ ∈ uIcc a b) (hτ' : τ' ∈ uIcc a b)
    (hτ'' : τ'' ∈ uIcc a b)
    (h₁ : SquareLaw H σ σ' τ τ') (h₂ : SquareLaw H σ σ' τ' τ'') : SquareLaw H σ σ' τ τ'' := by
  intro hl hl' hr hr' hb hb' ht ht' o
  have hm := continuousOn_horizontal hH hσ hσ' hτ'
  have hm' (s : ℝ) (hs : s ∈ uIcc σ σ') : IsFredholm (H (s, τ')) :=
    hF _ ⟨uIcc_subset_uIcc hσ hσ' hs, hτ'⟩
  have hF₁ (s : ℝ) (τ₁ τ₂ : ℝ) (h₁ : τ₁ ∈ uIcc a b) (h₂ : τ₂ ∈ uIcc a b) (hs : s ∈ uIcc s₀ s₁)
      (t : ℝ) (htt : t ∈ uIcc τ₁ τ₂) : IsFredholm (H (s, t)) :=
    hF _ ⟨hs, uIcc_subset_uIcc h₁ h₂ htt⟩
  rw [← detLineOrientationTransport_trans (T := fun t ↦ H (σ, t))
      (continuousOn_vertical hH hσ hτ hτ') (continuousOn_vertical hH hσ hτ' hτ'') hl
      (hF₁ σ τ τ' hτ hτ' hσ) (hF₁ σ τ' τ'' hτ' hτ'' hσ) hl',
    h₂ (continuousOn_vertical hH hσ hτ' hτ'') (hF₁ σ τ' τ'' hτ' hτ'' hσ)
      (continuousOn_vertical hH hσ' hτ' hτ'') (hF₁ σ' τ' τ'' hτ' hτ'' hσ') hm hm' ht ht',
    h₁ (continuousOn_vertical hH hσ hτ hτ') (hF₁ σ τ τ' hτ hτ' hσ)
      (continuousOn_vertical hH hσ' hτ hτ') (hF₁ σ' τ τ' hτ hτ' hσ') hb hb' hm hm',
    detLineOrientationTransport_trans (T := fun t ↦ H (σ', t))
      (continuousOn_vertical hH hσ' hτ hτ') (continuousOn_vertical hH hσ' hτ' hτ'') hr
      (hF₁ σ' τ τ' hτ hτ' hσ') (hF₁ σ' τ' τ'' hτ' hτ'' hσ') hr']

/-- **Vertical reversal.** The law around a rectangle holds whichever horizontal edge is taken as
the bottom one. -/
private theorem SquareLaw.symm_right {σ σ' τ τ' : ℝ} (h : SquareLaw H σ σ' τ τ') :
    SquareLaw H σ σ' τ' τ := by
  intro hl hl' hr hr' hb hb' ht ht' o
  have hl₁ : ContinuousOn (fun t ↦ H (σ, t)) (uIcc τ τ') := uIcc_comm τ' τ ▸ hl
  have hl₁' : ∀ t ∈ uIcc τ τ', IsFredholm (H (σ, t)) := uIcc_comm τ' τ ▸ hl'
  have hr₁ : ContinuousOn (fun t ↦ H (σ', t)) (uIcc τ τ') := uIcc_comm τ' τ ▸ hr
  have hr₁' : ∀ t ∈ uIcc τ τ', IsFredholm (H (σ', t)) := uIcc_comm τ' τ ▸ hr'
  -- Write `o` as the transport of `p` from `τ` to `τ'` along the left edge.
  obtain ⟨p, rfl⟩ : ∃ p, detLineOrientationTransport (T := fun t ↦ H (σ, t)) τ τ' hl₁ hl₁' p = o :=
    ⟨_, detLineOrientationTransport_symm (T := fun t ↦ H (σ, t)) hl hl₁ hl' hl₁' o⟩
  rw [h hl₁ hl₁' hr₁ hr₁' ht ht' hb hb' p, detLineOrientationTransport_symm,
    detLineOrientationTransport_symm]

/-- Near every point `(σ, τ)` of the rectangle, the law holds around every rectangle with corner
`(σ, τ)` and the opposite corner close enough. -/
private theorem eventually_squareLaw (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x)) {σ τ : ℝ} (hσ : σ ∈ uIcc s₀ s₁)
    (hτ : τ ∈ uIcc a b) :
    ∃ δ > 0, ∀ σ' ∈ uIcc s₀ s₁, ∀ τ' ∈ uIcc a b, dist σ' σ < δ → dist τ' τ < δ →
      SquareLaw H σ σ' τ τ' ∧ SquareLaw H σ' σ τ τ' := by
  obtain ⟨S, hS, G, hG, q, U, hU, hxU, hinv⟩ := (hF (σ, τ) ⟨hσ, hτ⟩).exists_isOpen_kernelChart
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.1
    ((hH (σ, τ) ⟨hσ, hτ⟩).preimage_mem_nhdsWithin (hU.mem_nhds hxU))
  refine ⟨δ, hδ, fun σ' hσ' τ' hτ' hσσ' hττ' ↦ ?_⟩
  -- The rectangle with corners `(σ, τ)` and `(σ', τ')` lies in the `δ`-ball, where the kernel
  -- chart of `H (σ, τ)` is valid.
  have hsub {x y : ℝ} (hy : dist y x < δ) : uIcc x y ⊆ Metric.ball x δ :=
    (Real.ball_eq_Ioo x δ ▸ ordConnected_Ioo :).uIcc_subset (Metric.mem_ball_self hδ) hy
  have hq (x : ℝ × ℝ) (hx : x ∈ uIcc σ σ' ×ˢ uIcc τ τ') :
      (((H x).coprod S.subtypeL).prod q).IsInvertible := by
    refine hinv _ (hball ⟨?_, uIcc_subset_uIcc hσ hσ' hx.1, uIcc_subset_uIcc hτ hτ' hx.2⟩)
    rw [← ball_prod_same]
    exact ⟨hsub hσσ' hx.1, hsub hττ' hx.2⟩
  exact ⟨squareLaw_of_kernelChart hq, squareLaw_of_kernelChart (by rwa [uIcc_comm σ' σ])⟩

/-- **Thin strips.** The law holds around every rectangle spanning the whole width whose
horizontal edges are close enough. -/
private theorem eventually_squareLaw_strip (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x)) {τ : ℝ} (hτ : τ ∈ uIcc a b) :
    ∀ᶠ τ' in 𝓝[uIcc a b] τ, SquareLaw H s₀ s₁ τ τ' := by
  let P : ℝ → Prop := fun σ ↦ ∀ᶠ τ' in 𝓝[uIcc a b] τ, SquareLaw H s₀ σ τ τ'
  have hstep (σ : ℝ) (hσ : σ ∈ uIcc s₀ s₁) : ∀ᶠ σ' in 𝓝[uIcc s₀ s₁] σ, (P σ ↔ P σ') ∧
      (P σ' ↔ P σ) := by
    obtain ⟨δ, hδ, hsq⟩ := eventually_squareLaw hH hF hσ hτ
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds σ hδ)]
      with σ' hσ' hσσ'
    -- Paste the small rectangles between `σ` and `σ'` to the rectangles from `s₀`.
    have hP (σ₁ σ₂ : ℝ) (h₁ : σ₁ ∈ uIcc s₀ s₁) (h₂ : σ₂ ∈ uIcc s₀ s₁)
        (h₁₂ : ∀ᶠ τ' in 𝓝[uIcc a b] τ, SquareLaw H σ₁ σ₂ τ τ') : P σ₁ → P σ₂ := fun hP ↦ by
      filter_upwards [hP, h₁₂, self_mem_nhdsWithin] with τ' h h' hτ'
      exact h.trans_left hH hF left_mem_uIcc h₁ h₂ hτ hτ' h'
    have hsmall : ∀ᶠ τ' in 𝓝[uIcc a b] τ, SquareLaw H σ σ' τ τ' ∧ SquareLaw H σ' σ τ τ' := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Metric.ball_mem_nhds τ hδ)]
        with τ' hτ' hττ' using hsq σ' hσ' τ' hτ' hσσ' hττ'
    have h₁ := hP σ σ' hσ hσ' (hsmall.mono fun _ h ↦ h.1)
    have h₂ := hP σ' σ hσ' hσ (hsmall.mono fun _ h ↦ h.2)
    exact ⟨⟨h₁, h₂⟩, ⟨h₂, h₁⟩⟩
  have hP₀ : P s₀ := Eventually.of_forall fun τ' ↦ squareLaw_self_left s₀ τ τ'
  exact (isPreconnected_uIcc.induction₂' (fun x y ↦ P x ↔ P y) hstep
    (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂) left_mem_uIcc right_mem_uIcc).1 hP₀

/-- The law holds around the whole rectangle. -/
private theorem squareLaw (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x)) : SquareLaw H s₀ s₁ a b := by
  let Q : ℝ → Prop := fun τ ↦ SquareLaw H s₀ s₁ a τ
  have hstep (τ : ℝ) (hτ : τ ∈ uIcc a b) : ∀ᶠ τ' in 𝓝[uIcc a b] τ, (Q τ ↔ Q τ') ∧
      (Q τ' ↔ Q τ) := by
    filter_upwards [eventually_squareLaw_strip hH hF hτ, self_mem_nhdsWithin] with τ' h hτ'
    have h₁ : Q τ → Q τ' := fun hQ ↦
      hQ.trans_right hH hF left_mem_uIcc right_mem_uIcc left_mem_uIcc hτ hτ' h
    have h₂ : Q τ' → Q τ := fun hQ ↦
      hQ.trans_right hH hF left_mem_uIcc right_mem_uIcc left_mem_uIcc hτ' hτ h.symm_right
    exact ⟨⟨h₁, h₂⟩, ⟨h₂, h₁⟩⟩
  exact (isPreconnected_uIcc.induction₂' (fun x y ↦ Q x ↔ Q y) hstep
    (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂) left_mem_uIcc right_mem_uIcc).1
    (squareLaw_self_right s₀ s₁ a)

/-- **Orientation transport around a rectangle commutes.** For a family of operators `H` which is
continuous and Fredholm on the rectangle `[[s₀, s₁]] ×ˢ [[a, b]]`, transporting an orientation of
the determinant line of `H (s₀, a)` along the left edge `t ↦ H (s₀, t)` and then along the top
edge `s ↦ H (s, b)` agrees with transporting it along the bottom edge `s ↦ H (s, a)` and then
along the right edge `t ↦ H (s₁, t)`. -/
theorem detLineOrientationTransport_comm (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x))
    (o : Module.Ray ℝ (H (s₀, a) : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := fun s ↦ H (s, b)) s₀ s₁
        (hH.comp (Continuous.prodMk_left b).continuousOn fun _ hs ↦ ⟨hs, right_mem_uIcc⟩)
        (fun _ hs ↦ hF _ ⟨hs, right_mem_uIcc⟩)
        (detLineOrientationTransport (T := fun t ↦ H (s₀, t)) a b
          (hH.comp (Continuous.prodMk_right s₀).continuousOn fun _ ht ↦ ⟨left_mem_uIcc, ht⟩)
          (fun _ ht ↦ hF _ ⟨left_mem_uIcc, ht⟩) o) =
      detLineOrientationTransport (T := fun t ↦ H (s₁, t)) a b
        (hH.comp (Continuous.prodMk_right s₁).continuousOn fun _ ht ↦ ⟨right_mem_uIcc, ht⟩)
        (fun _ ht ↦ hF _ ⟨right_mem_uIcc, ht⟩)
        (detLineOrientationTransport (T := fun s ↦ H (s, a)) s₀ s₁
          (hH.comp (Continuous.prodMk_left a).continuousOn fun _ hs ↦ ⟨hs, left_mem_uIcc⟩)
          (fun _ hs ↦ hF _ ⟨hs, left_mem_uIcc⟩) o) :=
  squareLaw hH hF _ _ _ _ _ _ _ _ o

/-- **Homotopy invariance of orientation transport.** Let `H` be continuous and Fredholm on the
rectangle `[[s₀, s₁]] ×ˢ [[a, b]]`, and constant along its bottom and top edges: a homotopy from
the path `t ↦ H (s₀, t)` to the path `t ↦ H (s₁, t)` relative to the endpoints. Then transport
from `a` to `b` along the two paths agree, once the determinant lines of the equal operators at
their endpoints are identified by `LinearMap.detLineCongrOfEq`. -/
theorem detLineOrientationTransport_eq_of_homotopy (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x))
    (ha : ∀ s ∈ uIcc s₀ s₁, H (s, a) = H (s₀, a)) (hb : ∀ s ∈ uIcc s₀ s₁, H (s, b) = H (s₀, b))
    (o : Module.Ray ℝ (H (s₀, a) : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := fun t ↦ H (s₁, t)) a b
        (hH.comp (Continuous.prodMk_right s₁).continuousOn fun _ ht ↦ ⟨right_mem_uIcc, ht⟩)
        (fun _ ht ↦ hF _ ⟨right_mem_uIcc, ht⟩)
        (Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg _ (ha s₁ right_mem_uIcc).symm)) o) =
      Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg _ (hb s₁ right_mem_uIcc).symm))
        (detLineOrientationTransport (T := fun t ↦ H (s₀, t)) a b
          (hH.comp (Continuous.prodMk_right s₀).continuousOn fun _ ht ↦ ⟨left_mem_uIcc, ht⟩)
          (fun _ ht ↦ hF _ ⟨left_mem_uIcc, ht⟩) o) := by
  have hbot := detLineOrientationTransport_eq_map_of_forall_eq (T := fun s ↦ H (s, a))
    (hH.comp (Continuous.prodMk_left a).continuousOn fun _ hs ↦ ⟨hs, left_mem_uIcc⟩)
    (fun _ hs ↦ hF _ ⟨hs, left_mem_uIcc⟩) ha
  have htop := detLineOrientationTransport_eq_map_of_forall_eq (T := fun s ↦ H (s, b))
    (hH.comp (Continuous.prodMk_left b).continuousOn fun _ hs ↦ ⟨hs, right_mem_uIcc⟩)
    (fun _ hs ↦ hF _ ⟨hs, right_mem_uIcc⟩) hb
  rw [← hbot, ← htop]
  exact (detLineOrientationTransport_comm hH hF o).symm

end Square

section UnbundledHomotopy

/-- **Endpoint-relative homotopy invariance between two paths** `T₀, T₁ : ℝ → E →L[ℝ] F`. -/
theorem detLineOrientationTransport_eq_of_homotopyRel
    {T₀ T₁ : ℝ → E →L[ℝ] F} {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b : ℝ}
    (hT₀ : ContinuousOn T₀ (uIcc a b)) (hF₀ : ∀ t ∈ uIcc a b, (T₀ t).IsFredholm)
    (hT₁ : ContinuousOn T₁ (uIcc a b)) (hF₁ : ∀ t ∈ uIcc a b, (T₁ t).IsFredholm)
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hFH : ∀ p ∈ uIcc s₀ s₁ ×ˢ uIcc a b, (H p).IsFredholm)
    (hs₀ : ∀ t ∈ uIcc a b, H (s₀, t) = T₀ t) (hs₁ : ∀ t ∈ uIcc a b, H (s₁, t) = T₁ t)
    (ha : ∀ s ∈ uIcc s₀ s₁, H (s, a) = T₀ a) (hb : ∀ s ∈ uIcc s₀ s₁, H (s, b) = T₀ b)
    (o : Module.Ray ℝ (T₀ a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT₁ hF₁
        (Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg ContinuousLinearMap.toLinearMap
          ((ha s₁ right_mem_uIcc).symm.trans (hs₁ a left_mem_uIcc)))) o) =
      Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg ContinuousLinearMap.toLinearMap
          ((hb s₁ right_mem_uIcc).symm.trans (hs₁ b right_mem_uIcc))))
        (detLineOrientationTransport a b hT₀ hF₀ o) := by
  have hHs₀ : ContinuousOn (fun t ↦ H (s₀, t)) (uIcc a b) :=
    hH.comp (Continuous.prodMk_right s₀).continuousOn fun _ ht ↦ ⟨left_mem_uIcc, ht⟩
  have hFs₀ : ∀ t ∈ uIcc a b, (H (s₀, t)).IsFredholm := fun t ht ↦ hFH (s₀, t) ⟨left_mem_uIcc, ht⟩
  have hHs₁ : ContinuousOn (fun t ↦ H (s₁, t)) (uIcc a b) :=
    hH.comp (Continuous.prodMk_right s₁).continuousOn fun _ ht ↦ ⟨right_mem_uIcc, ht⟩
  have hFs₁ : ∀ t ∈ uIcc a b, (H (s₁, t)).IsFredholm := fun t ht ↦ hFH (s₁, t) ⟨right_mem_uIcc, ht⟩
  have ha' (s : ℝ) (hs : s ∈ uIcc s₀ s₁) : H (s, a) = H (s₀, a) :=
    (ha s hs).trans (ha s₀ left_mem_uIcc).symm
  have hb' (s : ℝ) (hs : s ∈ uIcc s₀ s₁) : H (s, b) = H (s₀, b) :=
    (hb s hs).trans (hb s₀ left_mem_uIcc).symm
  let o' := Module.Ray.map (LinearMap.detLineCongrOfEq
    (congrArg ContinuousLinearMap.toLinearMap (hs₀ a left_mem_uIcc).symm)) o
  let o₁ := Module.Ray.map (LinearMap.detLineCongrOfEq
    (congrArg ContinuousLinearMap.toLinearMap (ha' s₁ right_mem_uIcc).symm)) o'
  have hc₀ := detLineOrientationTransport_congr hHs₀ hT₀ hFs₀ hF₀ hs₀ o'
  simp only [o', LinearMap.map_detLineCongrOfEq_map_detLineCongrOfEq,
    LinearMap.detLineCongrOfEq_rfl, Module.Ray.map_refl, Equiv.refl_apply] at hc₀
  have hin₁ : Module.Ray.map (LinearMap.detLineCongrOfEq
      (congrArg ContinuousLinearMap.toLinearMap (hs₁ a left_mem_uIcc))) o₁ =
      Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg ContinuousLinearMap.toLinearMap
        ((ha s₁ right_mem_uIcc).symm.trans (hs₁ a left_mem_uIcc)))) o := by
    simp only [o₁, o', LinearMap.map_detLineCongrOfEq_map_detLineCongrOfEq]
  have hslice : detLineOrientationTransport (T := fun t ↦ H (s₁, t)) a b hHs₁ hFs₁ o₁ =
      Module.Ray.map (LinearMap.detLineCongrOfEq
          (congrArg ContinuousLinearMap.toLinearMap (hb' s₁ right_mem_uIcc).symm))
        (detLineOrientationTransport (T := fun t ↦ H (s₀, t)) a b hHs₀ hFs₀ o') := by
    simpa only [o₁] using detLineOrientationTransport_eq_of_homotopy hH hFH ha' hb' o'
  rw [← hin₁, detLineOrientationTransport_congr hHs₁ hT₁ hFs₁ hF₁ hs₁ o₁, hslice, hc₀,
    LinearMap.map_detLineCongrOfEq_map_detLineCongrOfEq,
    LinearMap.map_detLineCongrOfEq_map_detLineCongrOfEq]

/-- **Path-independence in a convex set of Fredholm operators.** Any two continuous paths in a
convex set `U` of Fredholm operators sharing endpoints at `a` and `b` induce the same transport. -/
theorem detLineOrientationTransport_eq_of_convex {U : Set (E →L[ℝ] F)} (hU : Convex ℝ U)
    (hUF : ∀ S ∈ U, S.IsFredholm) {T₀ T₁ : ℝ → E →L[ℝ] F} {a b : ℝ}
    (hT₀ : ContinuousOn T₀ (uIcc a b)) (hT₁ : ContinuousOn T₁ (uIcc a b))
    (hT₀U : ∀ t ∈ uIcc a b, T₀ t ∈ U) (hT₁U : ∀ t ∈ uIcc a b, T₁ t ∈ U)
    (ha : T₀ a = T₁ a) (hb : T₀ b = T₁ b) (o : Module.Ray ℝ (T₀ a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT₁ (fun t ht ↦ hUF _ (hT₁U t ht))
        (Module.Ray.map
          (LinearMap.detLineCongrOfEq (congrArg ContinuousLinearMap.toLinearMap ha)) o) =
      Module.Ray.map (LinearMap.detLineCongrOfEq (congrArg ContinuousLinearMap.toLinearMap hb))
        (detLineOrientationTransport a b hT₀ (fun t ht ↦ hUF _ (hT₀U t ht)) o) := by
  let H : ℝ × ℝ → E →L[ℝ] F := fun p ↦ (1 - p.1) • T₀ p.2 + p.1 • T₁ p.2
  have hmaps : MapsTo Prod.snd (uIcc (0 : ℝ) 1 ×ˢ uIcc a b) (uIcc a b) := fun _ hp ↦ hp.2
  have hH : ContinuousOn H (uIcc (0 : ℝ) 1 ×ˢ uIcc a b) :=
    ((continuousOn_const.sub continuous_fst.continuousOn).smul
      (hT₀.comp continuous_snd.continuousOn hmaps)).add
      (continuous_fst.continuousOn.smul (hT₁.comp continuous_snd.continuousOn hmaps))
  have hHU (p : ℝ × ℝ) (hp : p ∈ uIcc (0 : ℝ) 1 ×ˢ uIcc a b) : H p ∈ U := by
    have hs : p.1 ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (zero_le_one' ℝ)] using hp.1
    exact hU (hT₀U p.2 hp.2) (hT₁U p.2 hp.2) (sub_nonneg.2 hs.2) hs.1 (sub_add_cancel 1 p.1)
  exact detLineOrientationTransport_eq_of_homotopyRel
    hT₀ (fun t ht ↦ hUF _ (hT₀U t ht)) hT₁ (fun t ht ↦ hUF _ (hT₁U t ht))
    hH (fun p hp ↦ hUF _ (hHU p hp)) (fun t _ ↦ by simp [H]) (fun t _ ↦ by simp [H])
    (fun s _ ↦ by simp [H, ← ha, sub_smul]) (fun s _ ↦ by simp [H, ← hb, sub_smul]) o

end UnbundledHomotopy

noncomputable section

/-- Along a continuous Fredholm family `T : ℝ → E →L[ℝ] F` on `[[0, 1]]`, covering monodromy of the
orientation double cover carries the initial ray of a coherent family `v` to its final ray. -/
theorem IsDetLineCoherentOn.monodromy_orientationCoverMk
    {T : ℝ → E →L[ℝ] F} {v : ∀ t, (T t : E →ₗ[ℝ] F).detLine}
    (hv : IsDetLineCoherentOn T v (uIcc 0 1))
    (hT : ContinuousOn T (uIcc 0 1)) (hF : ∀ t ∈ uIcc (0 : ℝ) 1, (T t).IsFredholm) :
    (FredholmDetLine.isCoveringMap_orientationCover_proj (E := E) (F := F) (ι := Fin 1)).monodromy
      (.mk ⟨⟨fun t : unitInterval ↦ ⟨T t.val, hF t.val (Icc_subset_uIcc t.property)⟩,
        (hT.comp_continuous continuous_subtypeVal
          fun t ↦ Icc_subset_uIcc t.property).subtype_mk _⟩, rfl, rfl⟩)
      ((FredholmDetLine.orientationCoverFiberEquiv (Fin 1) ⟨T 0, hF 0 left_mem_uIcc⟩).symm
        (rayOfNeZero ℝ (v 0) (hv.ne_zero left_mem_uIcc))) =
    ⟨FredholmDetLine.orientationCoverMk (Fin 1) ⟨T 1, hF 1 right_mem_uIcc⟩
      (rayOfNeZero ℝ (v 1) (hv.ne_zero right_mem_uIcc)),
      FredholmDetLine.proj_orientationCoverMk _ _⟩ := by
  obtain ⟨hv_ne, hg⟩ :=
    (isDetLineCoherentOn_iff_continuous_orientationCoverMk (ι := Fin 1) hT hF).1 hv
  let g_sub : uIcc (0 : ℝ) 1 → VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1) :=
    fun x ↦ FredholmDetLine.orientationCoverMk (Fin 1) ⟨T x.val, hF x.val x.property⟩
      (rayOfNeZero ℝ (v x.val) (hv_ne x.val x.property))
  let Γ : C(unitInterval, VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1)) :=
    ⟨fun t ↦ g_sub ⟨t.val, Icc_subset_uIcc t.property⟩,
      hg.comp (continuous_subtypeVal.subtype_mk _)⟩
  let γ : Path (⟨T 0, hF 0 left_mem_uIcc⟩ : {T : E →L[ℝ] F // T.IsFredholm})
      ⟨T 1, hF 1 right_mem_uIcc⟩ :=
    ⟨⟨fun t : unitInterval ↦ ⟨T t.val, hF t.val (Icc_subset_uIcc t.property)⟩,
      (hT.comp_continuous continuous_subtypeVal fun t ↦ Icc_subset_uIcc t.property).subtype_mk _⟩,
        rfl, rfl⟩
  have hpΓ : (VectorBundleOrientationCover.proj :
      VectorBundleOrientationCover ℝ (FredholmDetLine ℝ E F) (Fin 1) → _) ∘ ⇑Γ = ⇑γ :=
    funext fun _ ↦ FredholmDetLine.proj_orientationCoverMk _ _
  have hΓ0 : Γ 0 = ((FredholmDetLine.orientationCoverFiberEquiv (Fin 1)
      ⟨T 0, hF 0 left_mem_uIcc⟩).symm (rayOfNeZero ℝ (v 0) (hv.ne_zero left_mem_uIcc))).val := by
    rw [FredholmDetLine.orientationCoverFiberEquiv_symm_apply]
    exact congrArg g_sub (Subtype.ext rfl)
  refine Subtype.ext ?_
  rw [(FredholmDetLine.isCoveringMap_orientationCover_proj (E := E) (F := F)
    (ι := Fin 1)).monodromy_eq_apply_one hpΓ hΓ0]
  exact congrArg g_sub (Subtype.ext rfl)

namespace FredholmDetLine

variable {T₀ T₁ T₂ : {T : E →L[ℝ] F // T.IsFredholm}}

/-- **Orientation transport along a path homotopy class.** Obtained by conjugating
`VectorBundleOrientationCover.quotientTransport` of `FredholmDetLine ℝ E F` by
`FredholmDetLine.orientationEquivRay`. -/
def quotientOrientationTransport (γ : Path.Homotopic.Quotient T₀ T₁) :
    Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine ≃ Module.Ray ℝ (T₁.val : E →ₗ[ℝ] F).detLine :=
  ((orientationEquivRay (ι := Fin 1) T₀).symm.trans
    (VectorBundleOrientationCover.quotientTransport (F := ℝ) (E := FredholmDetLine ℝ E F)
      (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) γ)).trans
    (orientationEquivRay (ι := Fin 1) T₁)

theorem quotientOrientationTransport_def (γ : Path.Homotopic.Quotient T₀ T₁) :
    quotientOrientationTransport γ =
      ((orientationEquivRay (ι := Fin 1) T₀).symm.trans
        (VectorBundleOrientationCover.quotientTransport (F := ℝ) (E := FredholmDetLine ℝ E F)
          (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) γ)).trans
        (orientationEquivRay (ι := Fin 1) T₁) := (rfl)

-- Kept non-`simp` so `quotientOrientationTransport_neg` / `_units_smul` satisfy `simpNF`.
theorem quotientOrientationTransport_apply (γ : Path.Homotopic.Quotient T₀ T₁)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ r =
      orientationCoverFiberEquiv (Fin 1) T₁
        ((isCoveringMap_orientationCover_proj (E := E) (F := F) (ι := Fin 1)).monodromy γ
          ((orientationCoverFiberEquiv (Fin 1) T₀).symm r)) := by
  simp [quotientOrientationTransport_def, VectorBundleOrientationCover.quotientTransport_apply,
    orientationCoverFiberEquiv_def]

@[simp]
theorem quotientOrientationTransport_refl (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    quotientOrientationTransport (.refl T₀) = Equiv.refl _ := by
  ext r
  simp [quotientOrientationTransport_def]

@[simp]
theorem quotientOrientationTransport_symm (γ : Path.Homotopic.Quotient T₀ T₁) :
    quotientOrientationTransport γ.symm = (quotientOrientationTransport γ).symm := by
  ext r
  simp [quotientOrientationTransport_def]

/-- Concatenation law for orientation transport along path homotopy classes. -/
theorem quotientOrientationTransport_trans
    (γ₁ : Path.Homotopic.Quotient T₀ T₁) (γ₂ : Path.Homotopic.Quotient T₁ T₂) :
    quotientOrientationTransport (γ₁.trans γ₂) =
      (quotientOrientationTransport γ₁).trans (quotientOrientationTransport γ₂) := by
  ext r
  simp [quotientOrientationTransport_def, VectorBundleOrientationCover.quotientTransport_trans]

@[simp]
theorem quotientOrientationTransport_neg (γ : Path.Homotopic.Quotient T₀ T₁)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ (-r) = -quotientOrientationTransport γ r := by
  simp [quotientOrientationTransport_def]

@[simp]
theorem quotientOrientationTransport_units_smul (γ : Path.Homotopic.Quotient T₀ T₁) (u : ℝˣ)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ (u • r) = u • quotientOrientationTransport γ r := by
  simp [quotientOrientationTransport_def]

/-- **Orientation transport along a continuous path of Fredholm operators.** -/
def pathOrientationTransport (γ : Path T₀ T₁) :
    Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine ≃ Module.Ray ℝ (T₁.val : E →ₗ[ℝ] F).detLine :=
  quotientOrientationTransport (.mk γ)

theorem pathOrientationTransport_def (γ : Path T₀ T₁) :
    pathOrientationTransport γ = quotientOrientationTransport (.mk γ) := (rfl)

@[simp]
theorem pathOrientationTransport_refl (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    pathOrientationTransport (Path.refl T₀) = Equiv.refl _ := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_refl,
    quotientOrientationTransport_refl]

@[simp]
theorem pathOrientationTransport_symm (γ : Path T₀ T₁) :
    pathOrientationTransport γ.symm = (pathOrientationTransport γ).symm := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_symm,
    quotientOrientationTransport_symm, pathOrientationTransport_def]

/-- Concatenation law for orientation transport along continuous paths of Fredholm operators. -/
theorem pathOrientationTransport_trans (γ₁ : Path T₀ T₁) (γ₂ : Path T₁ T₂) :
    pathOrientationTransport (γ₁.trans γ₂) =
      (pathOrientationTransport γ₁).trans (pathOrientationTransport γ₂) := by
  rw [pathOrientationTransport_def, Path.Homotopic.Quotient.mk_trans,
    quotientOrientationTransport_trans, pathOrientationTransport_def, pathOrientationTransport_def]

/-- **Endpoint-relative homotopy invariance** for `Path`s in `{T : E →L[ℝ] F // T.IsFredholm}`. -/
theorem pathOrientationTransport_eq_of_homotopic {γ₀ γ₁ : Path T₀ T₁} (h : γ₀.Homotopic γ₁) :
    pathOrientationTransport γ₀ = pathOrientationTransport γ₁ := by
  rw [pathOrientationTransport_def, pathOrientationTransport_def, Path.Homotopic.Quotient.eq.2 h]

/-- Compatibility of `pathOrientationTransport` with `Path.cast` along endpoint equalities. -/
theorem pathOrientationTransport_cast {S₀ S₁ T₀ T₁ : {T : E →L[ℝ] F // T.IsFredholm}}
    (γ : Path S₀ S₁) (h₀ : T₀ = S₀) (h₁ : T₁ = S₁)
    (o : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport (γ.cast h₀ h₁) o =
      Module.Ray.map (LinearMap.detLineCongrOfEq
          (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.val : E →ₗ[ℝ] F)) h₁.symm))
        (pathOrientationTransport γ
          (Module.Ray.map (LinearMap.detLineCongrOfEq
            (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.val : E →ₗ[ℝ] F)) h₀)) o)) := by
  subst h₀
  subst h₁
  simp

@[simp]
theorem pathOrientationTransport_neg (γ : Path T₀ T₁)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport γ (-r) = -pathOrientationTransport γ r :=
  quotientOrientationTransport_neg (.mk γ) r

@[simp]
theorem pathOrientationTransport_units_smul (γ : Path T₀ T₁) (u : ℝˣ)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport γ (u • r) = u • pathOrientationTransport γ r :=
  quotientOrientationTransport_units_smul (.mk γ) u r

/-- **Agreement of covering monodromy and coherent-family transport** on `[[0, 1]]`. -/
theorem pathOrientationTransport_mk_eq_detLineOrientationTransport
    {T : ℝ → E →L[ℝ] F} (hT : ContinuousOn T (uIcc 0 1))
    (hF : ∀ t ∈ uIcc (0 : ℝ) 1, (T t).IsFredholm)
    (o : Module.Ray ℝ (T 0 : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport
        (⟨⟨fun t : unitInterval ↦ ⟨T t.val, hF t.val (Icc_subset_uIcc t.property)⟩,
          (hT.comp_continuous continuous_subtypeVal
            fun t ↦ Icc_subset_uIcc t.property).subtype_mk _⟩, rfl, rfl⟩ :
          Path ⟨T 0, hF 0 left_mem_uIcc⟩ ⟨T 1, hF 1 right_mem_uIcc⟩) o =
      detLineOrientationTransport 0 1 hT hF o := by
  induction o using Module.Ray.ind with | h v₀ hv₀ =>
  obtain ⟨v, rfl, hv⟩ := exists_isDetLineCoherentOn_Icc hT hF left_mem_uIcc hv₀
  rw [pathOrientationTransport_def, quotientOrientationTransport_apply,
    hv.monodromy_orientationCoverMk hT hF,
    orientationCoverFiberEquiv_mk' ⟨T 1, hF 1 right_mem_uIcc⟩,
    detLineOrientationTransport_rayOfNeZero hT hF hv]

/-- **Bridge between `pathOrientationTransport` and `detLineOrientationTransport`** along
`γ.extend`. -/
theorem pathOrientationTransport_apply_eq_map_detLineOrientationTransport
    (γ : Path T₀ T₁) (o : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    pathOrientationTransport γ o =
      Module.Ray.map (LinearMap.detLineCongrOfEq
          (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.val : E →ₗ[ℝ] F)) γ.extend_one))
        (detLineOrientationTransport (T := fun t ↦ (γ.extend t).val) 0 1
          (continuous_subtypeVal.comp γ.continuous_extend).continuousOn
          (fun t _ ↦ (γ.extend t).property)
          (Module.Ray.map (LinearMap.detLineCongrOfEq
            (congrArg (fun x : {T : E →L[ℝ] F // T.IsFredholm} ↦ (x.val : E →ₗ[ℝ] F))
              γ.extend_zero.symm)) o)) := by
  have hT : ContinuousOn (fun t ↦ (γ.extend t).val) (uIcc 0 1) :=
    (continuous_subtypeVal.comp γ.continuous_extend).continuousOn
  have hF : ∀ t ∈ uIcc (0 : ℝ) 1, ((γ.extend t).val).IsFredholm := fun t _ ↦ (γ.extend t).property
  let γ' : Path (γ.extend 0) (γ.extend 1) :=
    ⟨⟨fun t : unitInterval ↦ ⟨(γ.extend t.val).val, hF t.val (Icc_subset_uIcc t.property)⟩,
      (hT.comp_continuous continuous_subtypeVal fun t ↦ Icc_subset_uIcc t.property).subtype_mk _⟩,
        rfl, rfl⟩
  have hγ : pathOrientationTransport γ =
      pathOrientationTransport (γ'.cast γ.extend_zero.symm γ.extend_one.symm) :=
    congrArg pathOrientationTransport
      (Path.ext (funext fun t ↦ Subtype.ext (congrArg Subtype.val (γ.extend_extends' t).symm)))
  simp only [hγ, pathOrientationTransport_cast]
  congr 1
  exact pathOrientationTransport_mk_eq_detLineOrientationTransport hT hF _

/-- Around any loop homotopy class based at `T₀`, orientation transport either fixes every ray or
reverses every ray. -/
theorem quotientOrientationTransport_eq_self_or_eq_neg (γ : Path.Homotopic.Quotient T₀ T₀) :
    (∀ r, quotientOrientationTransport γ r = r) ∨
      (∀ r, quotientOrientationTransport γ r = -r) := by
  rcases VectorBundleOrientationCover.quotientTransport_eq_self_or_eq_neg
    (F := ℝ) (E := FredholmDetLine ℝ E F) (ι := Fin 1)
    (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) γ with h | h
  · exact .inl fun r ↦ by simp [quotientOrientationTransport_def, h]
  · exact .inr fun r ↦ by simp [quotientOrientationTransport_def, h]

/-- **Orientation monodromy sign character** `FundamentalGroup _ T₀ →* ℤˣ`, defined as
`VectorBundleOrientationCover.orientationCharacter` of `FredholmDetLine ℝ E F`. -/
def orientationMonodromySign (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀ →* ℤˣ :=
  VectorBundleOrientationCover.orientationCharacter ℝ (FredholmDetLine ℝ E F)
    (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) T₀

theorem orientationMonodromySign_def (T₀ : {T : E →L[ℝ] F // T.IsFredholm}) :
    orientationMonodromySign T₀ =
      VectorBundleOrientationCover.orientationCharacter ℝ (FredholmDetLine ℝ E F)
        (ι := Fin 1) (Fintype.card_unique.trans (Module.finrank_self ℝ).symm) T₀ := (rfl)

/-- Orientation transport along `γ : FundamentalGroup _ T₀` acts on every ray by
`orientationMonodromySign T₀ γ`. -/
theorem quotientOrientationTransport_toPath_eq_smul
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    quotientOrientationTransport γ.toPath r =
      (Units.map (Int.castRingHom ℝ).toMonoidHom (orientationMonodromySign T₀ γ)) • r := by
  simp [quotientOrientationTransport_def,
    VectorBundleOrientationCover.quotientTransport_toPath_eq_smul, orientationMonodromySign_def]

/-- `orientationMonodromySign T₀ γ = 1` iff orientation transport along `γ` fixes `r`. -/
theorem orientationMonodromySign_eq_one_iff_apply
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    orientationMonodromySign T₀ γ = 1 ↔ quotientOrientationTransport γ.toPath r = r := by
  simp [orientationMonodromySign_def,
    VectorBundleOrientationCover.orientationCharacter_eq_one_iff_quotientTransport_eq _ γ
      ((orientationEquivRay (ι := Fin 1) T₀).symm r),
    quotientOrientationTransport_def, Equiv.eq_symm_apply]

/-- `orientationMonodromySign T₀ γ = -1` iff orientation transport along `γ` reverses `r`. -/
theorem orientationMonodromySign_eq_neg_one_iff_apply
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀)
    (r : Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine) :
    orientationMonodromySign T₀ γ = -1 ↔ quotientOrientationTransport γ.toPath r = -r := by
  simp only [orientationMonodromySign_def,
    VectorBundleOrientationCover.orientationCharacter_eq_neg_one_iff_quotientTransport_eq _ γ
      ((orientationEquivRay (ι := Fin 1) T₀).symm r),
    quotientOrientationTransport_def, Equiv.trans_apply,
    ← orientationEquivRay_symm_neg, Equiv.eq_symm_apply, iff_self]

/-- `orientationMonodromySign T₀ γ = 1` iff orientation transport along `γ` is the identity. -/
theorem orientationMonodromySign_eq_one_iff
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀) :
    orientationMonodromySign T₀ γ = 1 ↔ quotientOrientationTransport γ.toPath = Equiv.refl _ := by
  obtain ⟨r₀⟩ := (inferInstance : Nonempty (Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine))
  refine ⟨fun h ↦ Equiv.ext fun r ↦ (orientationMonodromySign_eq_one_iff_apply γ r).1 h,
    fun h ↦ (orientationMonodromySign_eq_one_iff_apply γ r₀).2 ?_⟩
  simp [h]

/-- `orientationMonodromySign T₀ γ = -1` iff orientation transport along `γ` reverses every ray. -/
theorem orientationMonodromySign_eq_neg_one_iff
    (γ : FundamentalGroup {T : E →L[ℝ] F // T.IsFredholm} T₀) :
    orientationMonodromySign T₀ γ = -1 ↔
      ∀ r, quotientOrientationTransport γ.toPath r = -r := by
  obtain ⟨r₀⟩ := (inferInstance : Nonempty (Module.Ray ℝ (T₀.val : E →ₗ[ℝ] F).detLine))
  exact ⟨fun h r ↦ (orientationMonodromySign_eq_neg_one_iff_apply γ r).1 h,
    fun h ↦ (orientationMonodromySign_eq_neg_one_iff_apply γ r₀).2 (h r₀)⟩

end FredholmDetLine

end

end TauCeti
