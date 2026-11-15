/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Fredholm.DeterminantLine.Transport

/-!
# Homotopy invariance of the transport of orientations of Fredholm determinant lines

Orientations of the determinant lines `det (ker T) ⊗ (det (F ⧸ range T))^*` of real Fredholm
operators are transported along continuous paths of Fredholm operators
(`TauCeti.detLineOrientationTransport`). This file proves that the transport only depends on the
path up to homotopy.

Let `H : ℝ × ℝ → E →L[ℝ] F` be continuous and Fredholm on a rectangle
`[[s₀, s₁]] ×ˢ [[a, b]]`. Its four edges are paths of Fredholm operators, and the **square law**
(`TauCeti.detLineOrientationTransport_comm_square`) says that transporting an orientation of the
determinant line at the corner `(s₀, a)` along the edge `t ↦ H (s₀, t)` and then along
`s ↦ H (s, b)` gives the same orientation at `(s₁, b)` as transporting it first along
`s ↦ H (s, a)` and then along `t ↦ H (s₁, t)`. If the homotopy fixes the endpoint operators, so
that `H (s, a)` and `H (s, b)` do not depend on `s`, the transports along these sides are the
identifications of equal determinant lines (`TauCeti.detLineOrientationTransport_eq_cast`), and the
square law becomes the **endpoint-relative homotopy law**
(`TauCeti.detLineOrientationTransport_eq_of_homotopy`): homotopic paths of Fredholm operators with
fixed ends transport orientations in the same way.

The proof of the square law cuts the rectangle into small boxes. By the Lebesgue number lemma there
is `δ > 0` such that every box of side less than `δ` with a corner in the rectangle lies in the set
where a single kernel chart is valid, and on such a box the family read by that chart as a constant
is coherent (`TauCeti.isDetLineCoherentOn_of_detLineChartEquiv_eq`). Its restrictions to the four
edges then compute all four transports, so the square law holds on the box. Square laws on two
boxes sharing an edge combine into the square law on their union, by the concatenation law
`TauCeti.detLineOrientationTransport_trans`. Stacking boxes along the second coordinate gives the
square law on every strip of width less than `δ`, and placing strips side by side gives it on the
whole rectangle; both steps are inductions over a preconnected interval.

## Main results

* `TauCeti.detLineOrientationTransport_comm_square`: the square law for a homotopy of paths of
  Fredholm operators.
* `TauCeti.detLineOrientationTransport_eq_cast`: along a path of equal operators, orientation
  transport is the identification of their determinant lines.
* `TauCeti.detLineOrientationTransport_eq_of_homotopy`: homotopic paths with fixed endpoint
  operators transport orientations in the same way.

## References

* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties, and
  classification*, Math. Scand. 118 (2016), 203–268, arXiv:1304.6368.
* D. McDuff, D. Salamon, *J-holomorphic Curves and Symplectic Topology*, second edition,
  AMS Colloquium Publications 52, 2012, Section A.2 (determinant line bundles).
-/

public section

open Set Metric ContinuousLinearMap Module

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

section Square

variable {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b s s' t t' : ℝ}

private theorem continuousOn_snd_uIcc (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hs : s ∈ uIcc s₀ s₁) (ht : t ∈ uIcc a b) (ht' : t' ∈ uIcc a b) :
    ContinuousOn (fun τ ↦ H (s, τ)) (uIcc t t') :=
  hH.comp (by fun_prop : Continuous fun τ : ℝ ↦ (s, τ)).continuousOn
    fun _ hτ ↦ ⟨hs, uIcc_subset_uIcc ht ht' hτ⟩

private theorem continuousOn_fst_uIcc (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hs : s ∈ uIcc s₀ s₁) (hs' : s' ∈ uIcc s₀ s₁) (ht : t ∈ uIcc a b) :
    ContinuousOn (fun σ ↦ H (σ, t)) (uIcc s s') :=
  hH.comp (by fun_prop : Continuous fun σ : ℝ ↦ (σ, t)).continuousOn
    fun _ hσ ↦ ⟨uIcc_subset_uIcc hs hs' hσ, ht⟩

private theorem isFredholm_snd_uIcc (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x))
    (hs : s ∈ uIcc s₀ s₁) (ht : t ∈ uIcc a b) (ht' : t' ∈ uIcc a b) :
    ∀ τ ∈ uIcc t t', IsFredholm (H (s, τ)) :=
  fun _ hτ ↦ hF _ ⟨hs, uIcc_subset_uIcc ht ht' hτ⟩

private theorem isFredholm_fst_uIcc (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x))
    (hs : s ∈ uIcc s₀ s₁) (hs' : s' ∈ uIcc s₀ s₁) (ht : t ∈ uIcc a b) :
    ∀ σ ∈ uIcc s s', IsFredholm (H (σ, t)) :=
  fun _ hσ ↦ hF _ ⟨uIcc_subset_uIcc hs hs' hσ, ht⟩

variable [CompleteSpace E] [CompleteSpace F]

/-- The square law on the box `[[s, s']] ×ˢ [[t, t']]` inside the rectangle
`[[s₀, s₁]] ×ˢ [[a, b]]` on which `H` is continuous and Fredholm. -/
private def SquareLaw (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x)) (s s' t t' : ℝ) : Prop :=
  ∀ (hs : s ∈ uIcc s₀ s₁) (hs' : s' ∈ uIcc s₀ s₁) (ht : t ∈ uIcc a b) (ht' : t' ∈ uIcc a b)
    (o : Ray ℝ (H (s, t) : E →ₗ[ℝ] F).detLine),
    detLineOrientationTransport (T := fun σ ↦ H (σ, t')) s s'
        (continuousOn_fst_uIcc hH hs hs' ht') (isFredholm_fst_uIcc hF hs hs' ht')
        (detLineOrientationTransport (T := fun τ ↦ H (s, τ)) t t'
          (continuousOn_snd_uIcc hH hs ht ht') (isFredholm_snd_uIcc hF hs ht ht') o) =
      detLineOrientationTransport (T := fun τ ↦ H (s', τ)) t t'
        (continuousOn_snd_uIcc hH hs' ht ht') (isFredholm_snd_uIcc hF hs' ht ht')
        (detLineOrientationTransport (T := fun σ ↦ H (σ, t)) s s'
          (continuousOn_fst_uIcc hH hs hs' ht) (isFredholm_fst_uIcc hF hs hs' ht) o)

variable {hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b)}
  {hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x)}

/-- The square law holds on a box carrying a coherent family through every orientation at its
corner `(s, t)`: the restrictions of the family to the four edges compute the four transports. -/
private theorem squareLaw_of_exists_isDetLineCoherentOn
    (hex : ∀ v₀ : (H (s, t) : E →ₗ[ℝ] F).detLine, v₀ ≠ 0 →
      ∃ v : ∀ x, (H x : E →ₗ[ℝ] F).detLine, v (s, t) = v₀ ∧
        IsDetLineCoherentOn H v (uIcc s s' ×ˢ uIcc t t')) :
    SquareLaw hH hF s s' t t' := by
  intro hs hs' ht ht' o
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  obtain ⟨v, rfl, hv⟩ := hex v₀ hv₀
  -- The restrictions of `v` to the four edges of the box are coherent.
  have hvert {σ : ℝ} (hσ : σ ∈ uIcc s s') :
      IsDetLineCoherentOn (fun τ ↦ H (σ, τ)) (fun τ ↦ v (σ, τ)) (uIcc t t') :=
    hv.comp (by fun_prop : Continuous fun τ : ℝ ↦ (σ, τ)).continuousOn fun _ hτ ↦ ⟨hσ, hτ⟩
  have hhor {τ : ℝ} (hτ : τ ∈ uIcc t t') :
      IsDetLineCoherentOn (fun σ ↦ H (σ, τ)) (fun σ ↦ v (σ, τ)) (uIcc s s') :=
    hv.comp (by fun_prop : Continuous fun σ : ℝ ↦ (σ, τ)).continuousOn fun _ hσ ↦ ⟨hσ, hτ⟩
  rw [detLineOrientationTransport_rayOfNeZero _ _ (hvert left_mem_uIcc),
    detLineOrientationTransport_rayOfNeZero _ _ (hhor right_mem_uIcc),
    detLineOrientationTransport_rayOfNeZero _ _ (hhor left_mem_uIcc),
    detLineOrientationTransport_rayOfNeZero _ _ (hvert right_mem_uIcc)]

/-- The square law on a degenerate box `[[s, s']] ×ˢ [[t, t]]`. -/
private theorem squareLaw_self_right : SquareLaw hH hF s s' t t := by
  intro hs hs' ht _ o
  simp only [detLineOrientationTransport_self, id_eq]

/-- The square law on a degenerate box `[[s, s]] ×ˢ [[t, t']]`. -/
private theorem squareLaw_self_left : SquareLaw hH hF s s t t' := by
  intro hs _ ht ht' o
  simp only [detLineOrientationTransport_self, id_eq]

/-- Square laws on two boxes stacked along the second coordinate combine. -/
private theorem SquareLaw.trans_right {t'' : ℝ} (ht' : t' ∈ uIcc a b)
    (h₁ : SquareLaw hH hF s s' t t') (h₂ : SquareLaw hH hF s s' t' t'') :
    SquareLaw hH hF s s' t t'' := by
  intro hs hs' ht ht'' o
  rw [← detLineOrientationTransport_trans (T := fun τ ↦ H (s, τ)) (b := t')
      (continuousOn_snd_uIcc hH hs ht ht') (continuousOn_snd_uIcc hH hs ht' ht'')
      (continuousOn_snd_uIcc hH hs ht ht'') (isFredholm_snd_uIcc hF hs ht ht')
      (isFredholm_snd_uIcc hF hs ht' ht'') (isFredholm_snd_uIcc hF hs ht ht''),
    h₂ hs hs' ht' ht'', h₁ hs hs' ht ht',
    detLineOrientationTransport_trans (T := fun τ ↦ H (s', τ))
      (continuousOn_snd_uIcc hH hs' ht ht') (continuousOn_snd_uIcc hH hs' ht' ht'')
      (continuousOn_snd_uIcc hH hs' ht ht'') (isFredholm_snd_uIcc hF hs' ht ht')
      (isFredholm_snd_uIcc hF hs' ht' ht'') (isFredholm_snd_uIcc hF hs' ht ht'')]

/-- Square laws on two boxes placed side by side along the first coordinate combine. -/
private theorem SquareLaw.trans_left {s'' : ℝ} (hs' : s' ∈ uIcc s₀ s₁)
    (h₁ : SquareLaw hH hF s s' t t') (h₂ : SquareLaw hH hF s' s'' t t') :
    SquareLaw hH hF s s'' t t' := by
  intro hs hs'' ht ht' o
  rw [← detLineOrientationTransport_trans (T := fun σ ↦ H (σ, t')) (b := s')
      (continuousOn_fst_uIcc hH hs hs' ht') (continuousOn_fst_uIcc hH hs' hs'' ht')
      (continuousOn_fst_uIcc hH hs hs'' ht') (isFredholm_fst_uIcc hF hs hs' ht')
      (isFredholm_fst_uIcc hF hs' hs'' ht') (isFredholm_fst_uIcc hF hs hs'' ht'),
    h₁ hs hs' ht ht', h₂ hs' hs'' ht ht',
    detLineOrientationTransport_trans (T := fun σ ↦ H (σ, t))
      (continuousOn_fst_uIcc hH hs hs' ht) (continuousOn_fst_uIcc hH hs' hs'' ht)
      (continuousOn_fst_uIcc hH hs hs'' ht) (isFredholm_fst_uIcc hF hs hs' ht)
      (isFredholm_fst_uIcc hF hs' hs'' ht) (isFredholm_fst_uIcc hF hs hs'' ht)]

/-- There is `δ > 0` such that the square law holds on every box of sides less than `δ` with a
corner in the rectangle: such a box lies in the set where a single kernel chart is valid. -/
private theorem exists_forall_squareLaw :
    ∃ δ > 0, ∀ s s' t t', s ∈ uIcc s₀ s₁ → s' ∈ uIcc s₀ s₁ → t ∈ uIcc a b → t' ∈ uIcc a b →
      |s' - s| < δ → |t' - t| < δ → SquareLaw hH hF s s' t t' := by
  set R := uIcc s₀ s₁ ×ˢ uIcc a b
  -- The open sets on whose intersection with `R` a single kernel chart is valid cover `R`.
  let ι := {V : Set (ℝ × ℝ) // IsOpen V ∧ ∃ (S : Submodule ℝ F) (_ : FiniteDimensional ℝ S)
    (G : Submodule ℝ (E × S)) (_ : FiniteDimensional ℝ G) (q : E × S →L[ℝ] G),
    ∀ y ∈ V ∩ R, (((H y).coprod S.subtypeL).prod q).IsInvertible}
  have hcover : R ⊆ ⋃ V : ι, V.1 := by
    intro x hx
    obtain ⟨S, hS, G, hG, q, U, hU, hxU, hinv⟩ := (hF x hx).exists_isOpen_kernelChart
    obtain ⟨V, hV, hxV, hVU⟩ := mem_nhdsWithin.1 ((hH x hx).preimage_mem_nhdsWithin
      (hU.mem_nhds hxU))
    exact mem_iUnion.2 ⟨⟨V, hV, S, hS, G, hG, q, fun y hy ↦ hinv _ (hVU hy)⟩, hxV⟩
  obtain ⟨δ, hδ, hball⟩ := lebesgue_number_lemma_of_metric
    (isCompact_uIcc.prod isCompact_uIcc) (fun V : ι ↦ V.2.1) hcover
  refine ⟨δ, hδ, fun s s' t t' hs hs' ht ht' hss' htt' ↦ ?_⟩
  obtain ⟨V, hV⟩ := hball (s, t) ⟨hs, ht⟩
  obtain ⟨-, S, _, G, _, q, hinv⟩ := V.2
  -- The box lies in `V ∩ R`, where the chart is valid.
  have hbox : uIcc s s' ×ˢ uIcc t t' ⊆ V.1 ∩ R := fun y hy ↦
    ⟨hV (by
      rw [mem_ball, Prod.dist_eq, Real.dist_eq, Real.dist_eq, max_lt_iff]
      exact ⟨(abs_sub_left_of_mem_uIcc hy.1).trans_lt hss',
        (abs_sub_left_of_mem_uIcc hy.2).trans_lt htt'⟩),
      uIcc_subset_uIcc hs hs' hy.1, uIcc_subset_uIcc ht ht' hy.2⟩
  have hst : (s, t) ∈ uIcc s s' ×ˢ uIcc t t' := ⟨left_mem_uIcc, left_mem_uIcc⟩
  refine squareLaw_of_exists_isDetLineCoherentOn fun v₀ hv₀ ↦ ?_
  -- The family which the chart reads as the constant reading of `v₀`.
  classical
  have h₀ := hinv _ (hbox hst)
  set w₀ := detLineChartEquiv (H (s, t)) S.subtypeL q h₀ v₀
  have hw₀ : w₀ ≠ 0 := (LinearEquiv.map_ne_zero_iff _).2 hv₀
  refine ⟨fun x ↦ if h : (((H x).coprod S.subtypeL).prod q).IsInvertible then
    (detLineChartEquiv (H x) S.subtypeL q h).symm w₀ else 0, ?_,
    isDetLineCoherentOn_of_detLineChartEquiv_eq hw₀ fun x hx ↦ ⟨hinv _ (hbox hx), ?_⟩⟩
  · simp only [dite_eq_left h₀, w₀, LinearEquiv.symm_apply_apply]
  · simp only [dite_eq_left (hinv _ (hbox hx)), LinearEquiv.apply_symm_apply]

/-- The square law on every strip `[[s, s']] ×ˢ [[a, t]]` of width less than a `δ` for which the
square law holds on boxes of sides less than `δ`, by stacking boxes along the second coordinate. -/
private theorem squareLaw_strip {δ : ℝ} (hδ₀ : 0 < δ)
    (hδ : ∀ s s' t t', s ∈ uIcc s₀ s₁ → s' ∈ uIcc s₀ s₁ → t ∈ uIcc a b → t' ∈ uIcc a b →
      |s' - s| < δ → |t' - t| < δ → SquareLaw hH hF s s' t t')
    (hs : s ∈ uIcc s₀ s₁) (hs' : s' ∈ uIcc s₀ s₁) (hss' : |s' - s| < δ) (ht : t ∈ uIcc a b) :
    SquareLaw hH hF s s' a t := by
  refine (isPreconnected_uIcc.induction₂' (fun x y ↦ SquareLaw hH hF s s' a x ↔
    SquareLaw hH hF s s' a y) (fun x hx ↦ ?_) (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂)
    left_mem_uIcc ht).1 squareLaw_self_right
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds x hδ₀)] with y hy hyx
  have hxy : |y - x| < δ := by rwa [mem_ball, Real.dist_eq] at hyx
  have hiff : SquareLaw hH hF s s' a x ↔ SquareLaw hH hF s s' a y :=
    ⟨fun h ↦ h.trans_right hx (hδ s s' x y hs hs' hx hy hss' hxy),
      fun h ↦ h.trans_right hy (hδ s s' y x hs hs' hy hx hss' (by rwa [abs_sub_comm]))⟩
  exact ⟨hiff, hiff.symm⟩

/-- The square law on the whole rectangle, by placing strips side by side. -/
private theorem squareLaw_rectangle : SquareLaw hH hF s₀ s₁ a b := by
  obtain ⟨δ, hδ₀, hδ⟩ := exists_forall_squareLaw (hH := hH) (hF := hF)
  refine (isPreconnected_uIcc.induction₂' (fun x y ↦ SquareLaw hH hF s₀ x a b ↔
    SquareLaw hH hF s₀ y a b) (fun x hx ↦ ?_) (fun _ _ _ _ _ _ h₁ h₂ ↦ h₁.trans h₂)
    left_mem_uIcc right_mem_uIcc).1 squareLaw_self_left
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (ball_mem_nhds x hδ₀)] with y hy hyx
  have hxy : |y - x| < δ := by rwa [mem_ball, Real.dist_eq] at hyx
  have hiff : SquareLaw hH hF s₀ x a b ↔ SquareLaw hH hF s₀ y a b :=
    ⟨fun h ↦ h.trans_left hx (squareLaw_strip hδ₀ hδ hx hy hxy right_mem_uIcc),
      fun h ↦ h.trans_left hy
        (squareLaw_strip hδ₀ hδ hy hx (by rwa [abs_sub_comm]) right_mem_uIcc)⟩
  exact ⟨hiff, hiff.symm⟩

end Square

variable [CompleteSpace E] [CompleteSpace F] {H : ℝ × ℝ → E →L[ℝ] F} {s₀ s₁ a b : ℝ}

/-- **Square law of orientation transport.** For a family `H` of operators which is continuous and
Fredholm on the rectangle `[[s₀, s₁]] ×ˢ [[a, b]]`, transporting an orientation from the corner
`(s₀, a)` to the opposite corner `(s₁, b)` along the edges through `(s₀, b)` gives the same
orientation as along the edges through `(s₁, a)`. -/
theorem detLineOrientationTransport_comm_square (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x))
    (o : Ray ℝ (H (s₀, a) : E →ₗ[ℝ] F).detLine) :
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
  squareLaw_rectangle (hH := hH) (hF := hF) left_mem_uIcc right_mem_uIcc left_mem_uIcc
    right_mem_uIcc o

/-- Along a path of operators which are all equal to `T a`, orientation transport is the
identification of the determinant lines of the equal operators `T a` and `T b`. -/
theorem detLineOrientationTransport_eq_cast {T : ℝ → E →L[ℝ] F}
    (hT : ContinuousOn T (uIcc a b)) (hF : ∀ t ∈ uIcc a b, IsFredholm (T t))
    (h : ∀ t ∈ uIcc a b, T t = T a) (o : Ray ℝ (T a : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport a b hT hF o = (h b right_mem_uIcc).symm ▸ o := by
  induction o using Module.Ray.ind with | h v₀ hv₀ => ?_
  classical
  obtain ⟨S, _, G, _, q, U, -, hU, hinv⟩ := (hF a left_mem_uIcc).exists_isOpen_kernelChart
  have h₀ := hinv _ hU
  -- A kernel chart at `T a` reads the identifications of `v₀` as the same element.
  have hchart (B : E →L[ℝ] F) (e : T a = B) (hB : ((B.coprod S.subtypeL).prod q).IsInvertible) :
      detLineChartEquiv B S.subtypeL q hB (e ▸ v₀) =
        detLineChartEquiv (T a) S.subtypeL q h₀ v₀ := by
    subst e
    rfl
  let v : ∀ t, (T t : E →ₗ[ℝ] F).detLine := fun t ↦ if e : T a = T t then e ▸ v₀ else 0
  have hv : IsDetLineCoherentOn T v (uIcc a b) :=
    isDetLineCoherentOn_of_detLineChartEquiv_eq ((LinearEquiv.map_ne_zero_iff _).2 hv₀)
      fun t ht ↦ ⟨(h t ht).symm ▸ h₀, by
        simp only [v, dite_eq_left (h t ht).symm]
        exact hchart _ _ _⟩
  have hray (B : E →L[ℝ] F) (e : T a = B) (hne : e ▸ v₀ ≠ 0) :
      e ▸ rayOfNeZero ℝ v₀ hv₀ = rayOfNeZero ℝ (e ▸ v₀) hne := by
    subst e
    rfl
  have hva : v a = v₀ := by simp only [v, dite_eq_left rfl]
  have hvb : v b = (h b right_mem_uIcc).symm ▸ v₀ := by
    simp only [v, dite_eq_left (h b right_mem_uIcc).symm]
  calc detLineOrientationTransport a b hT hF (rayOfNeZero ℝ v₀ hv₀)
      = detLineOrientationTransport a b hT hF
          (rayOfNeZero ℝ (v a) (hv.ne_zero left_mem_uIcc)) := by simp only [hva]
    _ = rayOfNeZero ℝ (v b) (hv.ne_zero right_mem_uIcc) :=
        detLineOrientationTransport_rayOfNeZero hT hF hv
    _ = _ := by
        rw [hray _ _ (hvb ▸ hv.ne_zero right_mem_uIcc)]
        simp only [hvb]

/-- **Endpoint-relative homotopy law of orientation transport.** Let `H` be continuous and
Fredholm on the rectangle `[[s₀, s₁]] ×ˢ [[a, b]]`, and assume that it fixes the endpoint
operators: `H (s, a) = H (s₀, a)` and `H (s, b) = H (s₀, b)` for every `s ∈ [[s₀, s₁]]`. Then the
homotopic paths `t ↦ H (s₀, t)` and `t ↦ H (s₁, t)` transport orientations in the same way, up to
the identifications of the determinant lines of the equal endpoint operators. -/
theorem detLineOrientationTransport_eq_of_homotopy
    (hH : ContinuousOn H (uIcc s₀ s₁ ×ˢ uIcc a b))
    (hF : ∀ x ∈ uIcc s₀ s₁ ×ˢ uIcc a b, IsFredholm (H x))
    (ha : ∀ s ∈ uIcc s₀ s₁, H (s, a) = H (s₀, a)) (hb : ∀ s ∈ uIcc s₀ s₁, H (s, b) = H (s₀, b))
    (o : Ray ℝ (H (s₀, a) : E →ₗ[ℝ] F).detLine) :
    detLineOrientationTransport (T := fun t ↦ H (s₁, t)) a b
        (hH.comp (Continuous.prodMk_right s₁).continuousOn fun _ ht ↦ ⟨right_mem_uIcc, ht⟩)
        (fun _ ht ↦ hF _ ⟨right_mem_uIcc, ht⟩) ((ha s₁ right_mem_uIcc).symm ▸ o) =
      (hb s₁ right_mem_uIcc).symm ▸ detLineOrientationTransport (T := fun t ↦ H (s₀, t)) a b
        (hH.comp (Continuous.prodMk_right s₀).continuousOn fun _ ht ↦ ⟨left_mem_uIcc, ht⟩)
        (fun _ ht ↦ hF _ ⟨left_mem_uIcc, ht⟩) o := by
  have hsq := detLineOrientationTransport_comm_square hH hF o
  rw [detLineOrientationTransport_eq_cast (T := fun s ↦ H (s, a)) _ _ ha,
    detLineOrientationTransport_eq_cast (T := fun s ↦ H (s, b)) _ _ hb] at hsq
  exact hsq.symm

end TauCeti
