/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ConnectedSum.Smooth

import TauCeti.Geometry.Manifold.ContMDiff.Subtype
import TauCeti.Geometry.Manifold.ContMDiff.Sum
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Composition
import TauCeti.Order.Filter.Basic

/-!
# The connected sum depends on its balls only near their centres

The connected sum `TauCeti.ConnectedSum e₁ e₂` of `M` and `N` removes the centres of the balls
`e₁ : E → M` and `e₂ : E → N` and glues `e₁ v` to `e₂ (inversion 0 1 v)` for `v ≠ 0`. This file
shows that, up to homeomorphism and diffeomorphism, the result depends on each ball only through
its germ at the centre, and only up to a homeomorphism or diffeomorphism of the summand.

* **Exchanging the summands.** `TauCeti.ConnectedSum.commHomeomorph` and
  `TauCeti.ConnectedSum.commDiffeomorph` identify the connected sum of `M` and `N` with that of `N`
  and `M`, by the identity on each punctured summand: the inversion is an involution, so the same
  points are glued.
* **Moving the first ball.** Let `φ : M ≃ₜ M'` agree with `e₁' ∘ e₁⁻¹` near `e₁ 0`, that is,
  `φ ∘ e₁ = e₁'` on a ball of radius `ε` about `0`. Then
  `TauCeti.ConnectedSum.congrLeftHomeomorph` identifies the connected sum along `e₁` and `e₂` with
  the connected sum along `e₁'` and `e₂`. It is `φ` on the punctured first summand. On the second
  summand it is the identity away from the image of the closed ball of radius `ε⁻¹` under `e₂`, and
  on the punctured ball it sends `e₂ w`, glued to `e₁ (inversion 0 1 w)`, to
  `φ (e₁ (inversion 0 1 w))`. The two descriptions agree far out along the ball, where
  `‖w‖ > ε⁻¹`, for there `φ (e₁ (inversion 0 1 w)) = e₁' (inversion 0 1 w)` is glued to `e₂ w`.
  When `φ` is a diffeomorphism and the balls are local diffeomorphisms, it is a diffeomorphism
  (`TauCeti.ConnectedSum.congrLeftDiffeomorph`).

Combining the two, `TauCeti.ConnectedSum.nonempty_diffeomorph_of_eventuallyEq` shows that
diffeomorphisms `φ : M ≃ₘ M'` and `ψ : N ≃ₘ N'` with `φ ∘ e₁ = e₁'` and `ψ ∘ e₂ = e₂'` near `0`
give a diffeomorphism between the two connected sums. With the disc theorem in its ambient form,
which carries two orientation-compatible balls of a connected manifold into one another near their
centres by a diffeomorphism, this shows that the connected sum does not depend on its balls
(`TauCeti.ConnectedSum.nonempty_diffeomorph_of_isOrientationPreservingAt`).

The homeomorphism `TauCeti.ConnectedSum.congrLeftHomeomorph` needs the image of a closed ball under
`e₂` to be closed, so `E` is proper (finite-dimensional) and `N` is Hausdorff.

## Main definitions

* `TauCeti.ConnectedSum.commHomeomorph`, `TauCeti.ConnectedSum.commDiffeomorph`: the connected sum
  with its summands exchanged.
* `TauCeti.ConnectedSum.congrLeftHomeomorph`, `TauCeti.ConnectedSum.congrLeftDiffeomorph`: the
  connected sum along a first ball moved by a homeomorphism or diffeomorphism of the first summand,
  up to its germ at the centre.

## Main results

* `TauCeti.ConnectedSum.nonempty_homeomorph_of_eventuallyEq`,
  `TauCeti.ConnectedSum.nonempty_diffeomorph_of_eventuallyEq`: connected sums along balls carried
  into one another near their centres by homeomorphisms or diffeomorphisms of the summands are
  homeomorphic or diffeomorphic.

## References

* A. Kosinski, *Differential Manifolds*, Academic Press (1993), Chapter VI, Section 1.
* R. Palais, *Extending diffeomorphisms*, Proc. Amer. Math. Soc. 11 (1960), 274–277.
* M. Hirsch, *Differential Topology*, Springer GTM 33 (1976), Chapter 4, §6, Theorem 6.6.
-/

public section

noncomputable section

open Set Filter Function Topology TopologicalSpace EuclideanGeometry
open scoped Manifold ContDiff

namespace TauCeti.ConnectedSum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [T1Space M] {M' : Type*} [TopologicalSpace M'] [T1Space M']
  {N : Type*} [TopologicalSpace N] [T1Space N] {N' : Type*} [TopologicalSpace N'] [T1Space N']

/-! ### Exchanging the summands -/

section Comm

variable (e₁ : E → M) (e₂ : E → N)

/-- **Exchanging the summands of a connected sum.** The connected sum of `M` and `N` along `e₁`
and `e₂` is homeomorphic to the connected sum of `N` and `M` along `e₂` and `e₁`, by the identity
on each punctured summand: `e₁ v` is glued to `e₂ (inversion 0 1 v)` in both, as the inversion is
an involution. -/
def commHomeomorph : ConnectedSum e₁ e₂ ≃ₜ ConnectedSum e₂ e₁ where
  toFun := lift (inr e₂ e₁) (inl e₂ e₁) fun _ hv _ _ ↦ (inl_inversion_eq_inr hv _ _).symm
  invFun := lift (inr e₁ e₂) (inl e₁ e₂) fun _ hv _ _ ↦ (inl_inversion_eq_inr hv _ _).symm
  left_inv p := by obtain ⟨x | y, rfl⟩ := mk_surjective e₁ e₂ p <;> simp
  right_inv p := by obtain ⟨y | x, rfl⟩ := mk_surjective e₂ e₁ p <;> simp
  continuous_toFun := continuous_lift _ _ _ (continuous_inr e₂ e₁) (continuous_inl e₂ e₁)
  continuous_invFun := continuous_lift _ _ _ (continuous_inr e₁ e₂) (continuous_inl e₁ e₂)

@[simp]
theorem commHomeomorph_inl (x : puncture e₁) :
    commHomeomorph e₁ e₂ (inl e₁ e₂ x) = inr e₂ e₁ x :=
  lift_inl _ _ _ x

@[simp]
theorem commHomeomorph_inr (y : puncture e₂) :
    commHomeomorph e₁ e₂ (inr e₁ e₂ y) = inl e₂ e₁ y :=
  lift_inr _ _ _ y

@[simp]
theorem commHomeomorph_symm : (commHomeomorph e₁ e₂).symm = commHomeomorph e₂ e₁ :=
  (rfl)

/-- Read on the disjoint union of the punctured summands, the exchange of the summands is the swap
of the disjoint union. -/
theorem commHomeomorph_comp_mk : commHomeomorph e₁ e₂ ∘ mk e₁ e₂ = mk e₂ e₁ ∘ Sum.swap := by
  ext (x | y) <;> simp

section Smooth

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞}
  [ChartedSpace H M] [ChartedSpace H N] [IsManifold I n M] [IsManifold I n N]
  {e₁ e₂} (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
  (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂)

include h₁ h₂ d₁ d₂ in
/-- The exchange of the summands is `C^n` for the charts of the connected sums. -/
private theorem contMDiff_commHomeomorph :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₂ h₁
    ContMDiff I I n (commHomeomorph e₁ e₂) := by
  let := chartedSpace (H := H) h₁ h₂
  let := chartedSpace (H := H) h₂ h₁
  have := isManifold h₁ h₂ d₁ d₂
  have := isManifold h₂ h₁ d₂ d₁
  rw [← (isLocalDiffeomorph_mk h₁ h₂ d₁ d₂).contMDiff_comp_iff (mk_surjective e₁ e₂) le_rfl,
    commHomeomorph_comp_mk]
  exact (isLocalDiffeomorph_mk h₂ h₁ d₂ d₁).contMDiff.comp ContMDiff.swap

/-- **Exchanging the summands of a connected sum of manifolds.** For balls which are `C^n` local
diffeomorphisms, the homeomorphism `TauCeti.ConnectedSum.commHomeomorph` is a `C^n`
diffeomorphism for the charts of the connected sums. -/
def commDiffeomorph :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₂ h₁
    ConnectedSum e₁ e₂ ≃ₘ^n⟮I, I⟯ ConnectedSum e₂ e₁ :=
  letI := chartedSpace (H := H) h₁ h₂
  letI := chartedSpace (H := H) h₂ h₁
  { toEquiv := (commHomeomorph e₁ e₂).toEquiv
    contMDiff_toFun := contMDiff_commHomeomorph h₁ h₂ d₁ d₂
    contMDiff_invFun := contMDiff_commHomeomorph h₂ h₁ d₂ d₁ }

@[simp]
theorem coe_commDiffeomorph :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₂ h₁
    ⇑(commDiffeomorph h₁ h₂ d₁ d₂) = commHomeomorph e₁ e₂ :=
  (rfl)

/-- The diffeomorphism `TauCeti.ConnectedSum.commDiffeomorph` is the homeomorphism
`TauCeti.ConnectedSum.commHomeomorph`. -/
@[simp]
theorem toHomeomorph_commDiffeomorph :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₂ h₁
    (commDiffeomorph h₁ h₂ d₁ d₂).toHomeomorph = commHomeomorph e₁ e₂ :=
  (rfl)

@[simp]
theorem coe_commDiffeomorph_symm :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₂ h₁
    ⇑(commDiffeomorph h₁ h₂ d₁ d₂).symm = commHomeomorph e₂ e₁ :=
  (rfl)

end Smooth

end Comm

/-! ### Moving the first ball -/

section CongrLeft

variable {e₁ : E → M} {e₁' : E → M'} {e₂ : E → N} (φ : M ≃ₜ M') (hφ : φ ∘ e₁ =ᶠ[𝓝 0] e₁')

/-- The restriction of `φ` to the punctured first summands. -/
private def punctureMap (x : puncture e₁) : puncture e₁' :=
  ⟨φ x, apply_mem_puncture φ.injective hφ.eq_of_nhds x.2⟩

open Classical in
/-- The connected sum along `e₁'` and `e₂` receives the second punctured summand: a point `e₂ w`
of the punctured ball, glued to `e₁ (inversion 0 1 w)`, goes to `φ (e₁ (inversion 0 1 w))`, and a
point outside the ball goes to itself. -/
private def congrLeftInr (he₁ : Injective e₁) (y : puncture e₂) : ConnectedSum e₁' e₂ :=
  if h : (y : N) ∈ range e₂ then
    inl e₁' e₂ (punctureMap φ hφ ⟨e₁ (inversion 0 1 (invFun e₂ y)),
      apply_inversion_mem_puncture he₁ fun h0 ↦ mem_puncture.1 y.2 (h0 ▸ invFun_eq h).symm⟩)
  else inr e₁' e₂ y

private theorem congrLeftInr_apply (he₁ : Injective e₁) (he₂ : Injective e₂) {w : E} (hw : w ≠ 0)
    (hy : e₂ w ∈ puncture e₂) :
    congrLeftInr φ hφ he₁ ⟨e₂ w, hy⟩ =
      inl e₁' e₂
        (punctureMap φ hφ ⟨e₁ (inversion 0 1 w), apply_inversion_mem_puncture he₁ hw⟩) := by
  simp only [congrLeftInr, mem_range_self, ↓reduceDIte, leftInverse_invFun he₂ w]

private theorem congrLeftInr_of_notMem (he₁ : Injective e₁) {y : puncture e₂}
    (hy : (y : N) ∉ range e₂) : congrLeftInr φ hφ he₁ y = inr e₁' e₂ y := by
  simp only [congrLeftInr, hy, ↓reduceDIte]

/-- The map of connected sums induced by `φ`, before it is shown to be a homeomorphism. -/
private def congrLeftMap (he₁ : Injective e₁) (he₂ : Injective e₂) :
    ConnectedSum e₁ e₂ → ConnectedSum e₁' e₂ :=
  lift (inl e₁' e₂ ∘ punctureMap φ hφ) (congrLeftInr φ hφ he₁) fun v hv hx hy ↦ by
    rw [congrLeftInr_apply φ hφ he₁ he₂ (by simpa [inversion_eq_center one_ne_zero] using hv)]
    simp only [comp_apply, punctureMap, inversion_inversion (0 : E) one_ne_zero]

private theorem congrLeftMap_inl (he₁ : Injective e₁) (he₂ : Injective e₂) (x : puncture e₁) :
    congrLeftMap φ hφ he₁ he₂ (inl e₁ e₂ x) = inl e₁' e₂ (punctureMap φ hφ x) :=
  lift_inl _ _ _ x

private theorem congrLeftMap_inr (he₁ : Injective e₁) (he₂ : Injective e₂) (y : puncture e₂) :
    congrLeftMap φ hφ he₁ he₂ (inr e₁ e₂ y) = congrLeftInr φ hφ he₁ y :=
  lift_inr _ _ _ y

/-- Far out along the ball `e₂`, the map `congrLeftMap` is the identity of the second summand:
there `φ (e₁ (inversion 0 1 w)) = e₁' (inversion 0 1 w)`, which is glued to `e₂ w`. -/
private theorem exists_congrLeftInr_eq (he₁ : Injective e₁) (he₂ : Injective e₂) :
    ∃ r, ∀ y : puncture e₂, (y : N) ∉ e₂ '' Metric.closedBall 0 r →
      congrLeftInr φ hφ he₁ y = inr e₁' e₂ y := by
  obtain ⟨ε, hε, hεφ⟩ := Metric.eventually_nhds_iff.1 hφ
  refine ⟨ε⁻¹, fun ⟨y, hy⟩ hyr ↦ ?_⟩
  by_cases h : y ∈ range e₂
  · obtain ⟨w, rfl⟩ := h
    have hw : ε⁻¹ < ‖w‖ := not_le.1 fun hw ↦ hyr ⟨w, mem_closedBall_zero_iff.2 hw, rfl⟩
    have hw0 : w ≠ 0 := norm_pos_iff.1 ((inv_pos.2 hε).trans hw)
    have hdist : dist (inversion 0 1 w) 0 < ε := by
      rw [dist_inversion_center, one_pow, dist_zero_right, one_div_lt (norm_pos_iff.2 hw0) hε,
        one_div]
      exact hw
    have hx : e₁' (inversion 0 1 w) ∈ puncture e₁' := by
      rw [← hεφ hdist]
      exact apply_mem_puncture φ.injective hφ.eq_of_nhds (apply_inversion_mem_puncture he₁ hw0)
    rw [congrLeftInr_apply φ hφ he₁ he₂ hw0]
    exact (congrArg (inl e₁' e₂) (Subtype.ext (hεφ hdist))).trans
      (inl_inversion_eq_inr hw0 hx hy)
  · exact congrLeftInr_of_notMem φ hφ he₁ h

/-- Every point of the connected sum lies in the first punctured summand, or is a point of the
second punctured summand outside the image of a given ball. -/
private theorem exists_eq_inl_or_exists_eq_inr (he₁ : Injective e₁) (r : ℝ)
    (p : ConnectedSum e₁ e₂) :
    (∃ x, inl e₁ e₂ x = p) ∨ ∃ y : puncture e₂, (y : N) ∉ e₂ '' Metric.closedBall 0 r ∧
      inr e₁ e₂ y = p := by
  obtain ⟨x | ⟨y, hy⟩, rfl⟩ := mk_surjective e₁ e₂ p
  · exact .inl ⟨x, (mk_inl e₁ e₂ x).symm⟩
  by_cases hyr : y ∈ e₂ '' Metric.closedBall 0 r
  · obtain ⟨w, -, rfl⟩ := hyr
    have hw : w ≠ 0 := by rintro rfl; exact mem_puncture.1 hy rfl
    exact .inl ⟨⟨e₁ (inversion 0 1 w), apply_inversion_mem_puncture he₁ hw⟩,
      (inl_inversion_eq_inr hw _ hy).trans (mk_inr e₁ e₂ _).symm⟩
  · exact .inr ⟨⟨y, hy⟩, hyr, (mk_inr e₁ e₂ _).symm⟩

/-- The map `congrLeftMap` for `φ.symm` undoes the map for `φ`. -/
private theorem congrLeftMap_symm_congrLeftMap (hφ' : φ.symm ∘ e₁' =ᶠ[𝓝 0] e₁)
    (he₁ : Injective e₁) (he₁' : Injective e₁') (he₂ : Injective e₂) (p : ConnectedSum e₁ e₂) :
    congrLeftMap φ.symm hφ' he₁' he₂ (congrLeftMap φ hφ he₁ he₂ p) = p := by
  obtain ⟨x, rfl⟩ | ⟨⟨y, hy⟩, -, rfl⟩ := exists_eq_inl_or_exists_eq_inr he₁ 0 p
  · rw [congrLeftMap_inl, congrLeftMap_inl]
    exact congrArg (inl e₁ e₂) (Subtype.ext (φ.symm_apply_apply x))
  rw [congrLeftMap_inr]
  by_cases h : y ∈ range e₂
  · -- `e₂ w` went to `φ (e₁ (inversion 0 1 w))`, which comes back to `e₁ (inversion 0 1 w)`.
    obtain ⟨w, rfl⟩ := h
    have hw : w ≠ 0 := by rintro rfl; exact mem_puncture.1 hy rfl
    rw [congrLeftInr_apply φ hφ he₁ he₂ hw, congrLeftMap_inl]
    exact (congrArg (inl e₁ e₂) (Subtype.ext (φ.symm_apply_apply _))).trans
      (inl_inversion_eq_inr hw _ hy)
  · rw [congrLeftInr_of_notMem φ hφ he₁ h, congrLeftMap_inr]
    exact congrLeftInr_of_notMem φ.symm _ he₁' h

/-- The map `congrLeftMap` is continuous: on the first summand it is `φ`, and far out along the
ball `e₂` it is the identity of the second summand. -/
private theorem continuous_congrLeftMap [ProperSpace E] [T2Space N] (h₁ : IsOpenEmbedding e₁)
    (h₂ : IsOpenEmbedding e₂) :
    Continuous (congrLeftMap φ hφ h₁.injective h₂.injective) := by
  obtain ⟨r, hr⟩ := exists_congrLeftInr_eq φ hφ h₁.injective h₂.injective
  have hK : IsClosed (e₂ '' Metric.closedBall 0 r) :=
    ((isCompact_closedBall 0 r).image h₂.continuous).isClosed
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  obtain ⟨x, rfl⟩ | ⟨y, hy, rfl⟩ := exists_eq_inl_or_exists_eq_inr h₁.injective r p
  · refine (isOpenEmbedding_inl h₁ h₂).continuousAt_iff.1 ?_
    have : congrLeftMap φ hφ h₁.injective h₂.injective ∘ inl e₁ e₂ =
        inl e₁' e₂ ∘ punctureMap φ hφ :=
      funext (congrLeftMap_inl φ hφ h₁.injective h₂.injective)
    rw [this]
    exact ((continuous_inl e₁' e₂).comp
      ((φ.continuous.comp continuous_subtype_val).subtype_mk _)).continuousAt
  · refine (isOpenEmbedding_inr h₁ h₂).continuousAt_iff.1 ?_
    refine (continuous_inr e₁' e₂).continuousAt.congr ?_
    filter_upwards [(hK.isOpen_compl.preimage continuous_subtype_val).mem_nhds hy] with y' hy'
    rw [comp_apply, congrLeftMap_inr, hr y' hy']

/-- **Moving the first ball of a connected sum.** Let `φ : M ≃ₜ M'` carry the ball `e₁` to the
ball `e₁'` near the centre: `φ ∘ e₁ = e₁'` near `0`. Then the connected sum of `M` and `N` along
`e₁` and `e₂` is homeomorphic to the connected sum of `M'` and `N` along `e₁'` and `e₂`. The
homeomorphism is `φ` on the punctured first summand
(`TauCeti.ConnectedSum.congrLeftHomeomorph_inl`), sends a point `e₂ w` of the punctured second
ball, glued to `e₁ (inversion 0 1 w)`, to `φ (e₁ (inversion 0 1 w))`
(`TauCeti.ConnectedSum.congrLeftHomeomorph_inr_apply`), and is the identity on the rest of the
second summand (`TauCeti.ConnectedSum.congrLeftHomeomorph_inr_of_notMem`). -/
def congrLeftHomeomorph [ProperSpace E] [T2Space N] (h₁ : IsOpenEmbedding e₁)
    (h₁' : IsOpenEmbedding e₁') (h₂ : IsOpenEmbedding e₂) :
    ConnectedSum e₁ e₂ ≃ₜ ConnectedSum e₁' e₂ where
  toFun := congrLeftMap φ hφ h₁.injective h₂.injective
  invFun := congrLeftMap φ.symm (φ.toEquiv.symm_comp_eventuallyEq_iff.2 hφ.symm) h₁'.injective
    h₂.injective
  left_inv := congrLeftMap_symm_congrLeftMap φ hφ _ h₁.injective h₁'.injective h₂.injective
  right_inv p := by
    simpa using congrLeftMap_symm_congrLeftMap φ.symm
      (φ.toEquiv.symm_comp_eventuallyEq_iff.2 hφ.symm) hφ h₁'.injective h₁.injective h₂.injective p
  continuous_toFun := continuous_congrLeftMap φ hφ h₁ h₂
  continuous_invFun := continuous_congrLeftMap φ.symm _ h₁' h₂

variable [ProperSpace E] [T2Space N] (h₁ : IsOpenEmbedding e₁) (h₁' : IsOpenEmbedding e₁')
  (h₂ : IsOpenEmbedding e₂)

@[simp]
theorem congrLeftHomeomorph_inl (x : puncture e₁) :
    congrLeftHomeomorph φ hφ h₁ h₁' h₂ (inl e₁ e₂ x) =
      inl e₁' e₂ ⟨φ x, apply_mem_puncture φ.injective hφ.eq_of_nhds x.2⟩ :=
  congrLeftMap_inl φ hφ h₁.injective h₂.injective x

@[simp]
theorem congrLeftHomeomorph_inr_apply {w : E} (hw : w ≠ 0) (hy : e₂ w ∈ puncture e₂) :
    congrLeftHomeomorph φ hφ h₁ h₁' h₂ (inr e₁ e₂ ⟨e₂ w, hy⟩) =
      inl e₁' e₂ ⟨φ (e₁ (inversion 0 1 w)), apply_mem_puncture φ.injective hφ.eq_of_nhds
        (apply_inversion_mem_puncture h₁.injective hw)⟩ :=
  (congrLeftMap_inr φ hφ h₁.injective h₂.injective _).trans
    (congrLeftInr_apply φ hφ h₁.injective h₂.injective hw hy)

@[simp]
theorem congrLeftHomeomorph_inr_of_notMem {y : puncture e₂} (hy : (y : N) ∉ range e₂) :
    congrLeftHomeomorph φ hφ h₁ h₁' h₂ (inr e₁ e₂ y) = inr e₁' e₂ y :=
  (congrLeftMap_inr φ hφ h₁.injective h₂.injective y).trans
    (congrLeftInr_of_notMem φ hφ h₁.injective hy)

/-- The inverse of `TauCeti.ConnectedSum.congrLeftHomeomorph` is the homeomorphism for `φ.symm`. -/
theorem congrLeftHomeomorph_symm (hφ' : φ.symm ∘ e₁' =ᶠ[𝓝 0] e₁) :
    (congrLeftHomeomorph φ hφ h₁ h₁' h₂).symm = congrLeftHomeomorph φ.symm hφ' h₁' h₁ h₂ :=
  (rfl)

section Smooth

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞}
  [ChartedSpace H M] [ChartedSpace H M'] [ChartedSpace H N]
  [IsManifold I n M] [IsManifold I n M'] [IsManifold I n N]
  (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁) (d₁' : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁')
  (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂)

include d₁ d₁' d₂ in
/-- The map `congrLeftMap` is `C^n` when `φ` is: read on the disjoint union of the punctured
summands, it is `φ` on the first summand, and far out along the ball `e₂` it is the inclusion of
the second summand; every point of the connected sum is the image of a point of one of these two
kinds. -/
private theorem contMDiff_congrLeftMap (hφs : ContMDiff I I n φ) :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₁' h₂
    ContMDiff I I n (congrLeftMap φ hφ h₁.injective h₂.injective) := by
  let := chartedSpace (H := H) h₁ h₂
  let := chartedSpace (H := H) h₁' h₂
  have := isManifold h₁ h₂ d₁ d₂
  have := isManifold h₁' h₂ d₁' d₂
  have hmk := isLocalDiffeomorph_mk h₁ h₂ d₁ d₂
  have hmk' := isLocalDiffeomorph_mk h₁' h₂ d₁' d₂
  obtain ⟨r, hr⟩ := exists_congrLeftInr_eq φ hφ h₁.injective h₂.injective
  have hK : IsClosed (e₂ '' Metric.closedBall 0 r) :=
    ((isCompact_closedBall 0 r).image h₂.continuous).isClosed
  intro p
  obtain ⟨x, rfl⟩ | ⟨y, hy, rfl⟩ := exists_eq_inl_or_exists_eq_inr h₁.injective r p
  · rw [← mk_inl, ← ((hmk (.inl x)).contMDiffAt_comp_iff le_rfl), congrLeftMap, lift_comp_mk,
      contMDiffAt_sumElim_inl]
    have hinl : inl e₁' e₂ = mk e₁' e₂ ∘ Sum.inl := funext fun x ↦ (mk_inl e₁' e₂ x).symm
    have hφ' : ContMDiff I I n (punctureMap φ hφ) :=
      (ContMDiff.subtypeVal_comp_iff _ _).1 (hφs.comp contMDiff_subtype_val)
    rw [hinl]
    exact (hmk'.contMDiff.comp (ContMDiff.inl.comp hφ')).contMDiffAt
  · rw [← mk_inr, ← ((hmk (.inr y)).contMDiffAt_comp_iff le_rfl), congrLeftMap, lift_comp_mk,
      contMDiffAt_sumElim_inr]
    refine (hmk'.contMDiff.comp ContMDiff.inr).contMDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [(hK.isOpen_compl.preimage continuous_subtype_val).mem_nhds hy] with y' hy'
    rw [hr y' hy', comp_apply, mk_inr]

/-- **Moving the first ball of a connected sum of manifolds.** If `φ : M ≃ₘ M'` is a `C^n`
diffeomorphism with `φ ∘ e₁ = e₁'` near `0`, and the balls are `C^n` local diffeomorphisms, the
homeomorphism `TauCeti.ConnectedSum.congrLeftHomeomorph` is a `C^n` diffeomorphism for the charts
of the connected sums. -/
def congrLeftDiffeomorph (φ : M ≃ₘ^n⟮I, I⟯ M') (hφ : φ ∘ e₁ =ᶠ[𝓝 0] e₁') :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₁' h₂
    ConnectedSum e₁ e₂ ≃ₘ^n⟮I, I⟯ ConnectedSum e₁' e₂ :=
  letI := chartedSpace (H := H) h₁ h₂
  letI := chartedSpace (H := H) h₁' h₂
  { toEquiv := (congrLeftHomeomorph φ.toHomeomorph hφ h₁ h₁' h₂).toEquiv
    contMDiff_toFun :=
      contMDiff_congrLeftMap φ.toHomeomorph hφ h₁ h₁' h₂ d₁ d₁' d₂ φ.contMDiff
    contMDiff_invFun :=
      contMDiff_congrLeftMap φ.toHomeomorph.symm _ h₁' h₁ h₂ d₁' d₁ d₂ φ.symm.contMDiff }

/-- The diffeomorphism `TauCeti.ConnectedSum.congrLeftDiffeomorph` is the homeomorphism
`TauCeti.ConnectedSum.congrLeftHomeomorph`. -/
@[simp]
theorem toHomeomorph_congrLeftDiffeomorph (φ : M ≃ₘ^n⟮I, I⟯ M') (hφ : φ ∘ e₁ =ᶠ[𝓝 0] e₁') :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₁' h₂
    (congrLeftDiffeomorph h₁ h₁' h₂ d₁ d₁' d₂ φ hφ).toHomeomorph =
      congrLeftHomeomorph φ.toHomeomorph hφ h₁ h₁' h₂ :=
  (rfl)

@[simp]
theorem coe_congrLeftDiffeomorph (φ : M ≃ₘ^n⟮I, I⟯ M') (hφ : φ ∘ e₁ =ᶠ[𝓝 0] e₁') :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₁' h₂
    ⇑(congrLeftDiffeomorph h₁ h₁' h₂ d₁ d₁' d₂ φ hφ) =
      congrLeftHomeomorph φ.toHomeomorph hφ h₁ h₁' h₂ :=
  (rfl)

end Smooth

end CongrLeft

/-! ### Moving both balls -/

/-- **Connected sums along balls that agree near their centres are homeomorphic.** If
homeomorphisms `φ : M ≃ₜ M'` and `ψ : N ≃ₜ N'` satisfy `φ ∘ e₁ = e₁'` and `ψ ∘ e₂ = e₂'` near `0`,
the connected sum along `e₁` and `e₂` is homeomorphic to the connected sum along `e₁'` and
`e₂'`. -/
theorem nonempty_homeomorph_of_eventuallyEq [ProperSpace E] [T2Space N] [T2Space M']
    {e₁ : E → M} {e₂ : E → N} {e₁' : E → M'} {e₂' : E → N'} (φ : M ≃ₜ M') (ψ : N ≃ₜ N')
    (hφ : φ ∘ e₁ =ᶠ[𝓝 0] e₁') (hψ : ψ ∘ e₂ =ᶠ[𝓝 0] e₂') (h₁ : IsOpenEmbedding e₁)
    (h₂ : IsOpenEmbedding e₂) (h₁' : IsOpenEmbedding e₁') (h₂' : IsOpenEmbedding e₂') :
    Nonempty (ConnectedSum e₁ e₂ ≃ₜ ConnectedSum e₁' e₂') :=
  ⟨(congrLeftHomeomorph φ hφ h₁ h₁' h₂).trans <| (commHomeomorph e₁' e₂).trans <|
    (congrLeftHomeomorph ψ hψ h₂ h₂' h₁').trans (commHomeomorph e₂' e₁')⟩

/-- **Connected sums along balls that agree near their centres are diffeomorphic.** If
`C^n` diffeomorphisms `φ : M ≃ₘ M'` and `ψ : N ≃ₘ N'` satisfy `φ ∘ e₁ = e₁'` and `ψ ∘ e₂ = e₂'`
near `0`, and the balls are open embeddings and `C^n` local diffeomorphisms, the connected sum
along `e₁` and `e₂` is `C^n` diffeomorphic to the connected sum along `e₁'` and `e₂'`. -/
theorem nonempty_diffeomorph_of_eventuallyEq [ProperSpace E] [T2Space N] [T2Space M']
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞}
    [ChartedSpace H M] [ChartedSpace H N] [ChartedSpace H M'] [ChartedSpace H N']
    [IsManifold I n M] [IsManifold I n N] [IsManifold I n M'] [IsManifold I n N']
    {e₁ : E → M} {e₂ : E → N} {e₁' : E → M'} {e₂' : E → N'}
    (φ : M ≃ₘ^n⟮I, I⟯ M') (ψ : N ≃ₘ^n⟮I, I⟯ N') (hφ : φ ∘ e₁ =ᶠ[𝓝 0] e₁')
    (hψ : ψ ∘ e₂ =ᶠ[𝓝 0] e₂') (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
    (h₁' : IsOpenEmbedding e₁') (h₂' : IsOpenEmbedding e₂')
    (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂)
    (d₁' : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₁') (d₂' : IsLocalDiffeomorph 𝓘(ℝ, E) I n e₂') :
    letI := chartedSpace (H := H) h₁ h₂
    letI := chartedSpace (H := H) h₁' h₂'
    Nonempty (ConnectedSum e₁ e₂ ≃ₘ^n⟮I, I⟯ ConnectedSum e₁' e₂') := by
  let := chartedSpace (H := H) h₁ h₂
  let := chartedSpace (H := H) h₁' h₂
  let := chartedSpace (H := H) h₂ h₁'
  let := chartedSpace (H := H) h₂' h₁'
  let := chartedSpace (H := H) h₁' h₂'
  exact ⟨(congrLeftDiffeomorph h₁ h₁' h₂ d₁ d₁' d₂ φ hφ).trans <|
    (commDiffeomorph h₁' h₂ d₁' d₂).trans <|
    (congrLeftDiffeomorph h₂ h₂' h₁' d₂ d₂' d₁' ψ hψ).trans (commDiffeomorph h₂' h₁' d₂' d₁')⟩

end TauCeti.ConnectedSum
