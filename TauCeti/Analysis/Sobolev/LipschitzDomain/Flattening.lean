/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.GraphFlattening
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import TauCeti.Analysis.Calculus.ContDiff.Bounds

/-!
# Flattening a `Cᵏ` boundary graph by a change of variables

Near a boundary point of class `Cᵏ`, a domain is the region above the graph of a `Cᵏ` function
`γ` in rigid coordinates. The shear `(t, y) ↦ (t - γ(y), y)` (`TauCeti.graphFlattening`) carries
that region to a half-space. This file shows that the shear and its inverse, conjugated back by
the rigid coordinates, are changes of variables of order `k` in the sense of
`TauCeti.Wkp.IsChangeOfVariables`, on a neighbourhood of the boundary point, with Jacobian
determinant one. For `1 ≤ p < ∞`, precomposition with them is therefore bounded between the
Sobolev spaces `W^{k,p}` of the curved boundary portion and of the flat one
(`TauCeti.Wkp.IsChangeOfVariables.compL`).

This is how boundary regularity is transferred from a half-space to a domain with a `Cᵏ`
boundary: a statement proved near a flat boundary, such as `H²` regularity of weak solutions
vanishing on the boundary hyperplane, is pulled back along the flattening chart, applied there,
and pushed forward again. The neighbourhood on the flat side is a product cylinder, hence convex.

The domain is described by local graphs as in `TauCeti.isLipschitzDomainWith_of_contDiffAt`,
following Evans's definition of a `Cᵏ` boundary, with a height function of class `Cᵏ` on the
whole tangential space. Its derivatives of orders `1` through `k` are bounded on a closed ball by
compactness, which bounds those of the shear.

## Main declarations

* `TauCeti.Wkp.isChangeOfVariables_graphFlattening` and
  `TauCeti.Wkp.isChangeOfVariables_graphFlattening_symm`: graph flattening by a `Cᵏ` height and
  its inverse are changes of variables of order `k`, with Jacobian determinant one.
* `TauCeti.exists_isChangeOfVariables_of_contDiff`: a `Cᵏ` boundary graph gives a flattening
  change of variables of order `k` between a convex neighbourhood on the flat side and a
  neighbourhood of the boundary point, mapping the half-space part onto the domain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., Appendix C.1 (`Cᵏ` boundaries) and
  §6.3.2 (boundary regularity by flattening the boundary).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  §6.2 (boundary straightening maps).
-/

public section

noncomputable section

namespace TauCeti

open Metric Set TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Wkp

/-- Graph flattening by a `Cᵏ` height `γ`, `k ≥ 1`, is a change of variables of order `k` on any
open set `U` on which the derivatives of `γ` of orders `1` through `k` are bounded by `M`, with
constants `1 + M` and `1`: its Jacobian determinant is one. -/
theorem isChangeOfVariables_graphFlattening {k : ℕ} (hk : 1 ≤ k) {γ : E → ℝ}
    (hγ : ContDiff ℝ k γ) {U V : Opens (WithLp 2 (ℝ × E))}
    (hUV : MapsTo (graphFlattening γ hγ.continuous) U V) {M : ℝ}
    (hM : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set (WithLp 2 (ℝ × E))),
      ‖iteratedFDeriv ℝ i γ x.snd‖ ≤ M) :
    IsChangeOfVariables k U V (graphFlattening γ hγ.continuous) (1 + M) 1 := by
  have hk0 : (k : WithTop ℕ∞) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hγd : Differentiable ℝ γ := hγ.differentiable hk0
  exact
    { contDiffOn := (contDiff_graphFlattening hγ).contDiffOn
      differentiableOn := ((contDiff_graphFlattening hγ).differentiable hk0).differentiableOn
      injOn := (graphFlattening γ hγ.continuous).injective.injOn
      mapsTo := hUV
      norm_iteratedFDeriv_le := fun i hi hik x hx ↦ by
        rcases hi.eq_or_lt with rfl | hi2
        · rw [norm_iteratedFDeriv_one]
          refine (norm_fderiv_graphFlattening_le hγ.continuous (hγd _)).trans ?_
          simpa [norm_iteratedFDeriv_one] using hM 1 le_rfl hk x hx
        · refine (norm_iteratedFDeriv_graphFlattening_le hγ hi2 (by exact_mod_cast hik) x).trans
            ?_
          linarith [hM i hi hik x hx]
      pos := one_pos
      le_abs_det := fun x _ ↦ by
        rw [ContinuousLinearMap.det, det_fderiv_graphFlattening hγ.continuous (hγd _), abs_one] }

/-- Inverse graph flattening by a `Cᵏ` height `γ`, `k ≥ 1`, is a change of variables of order `k`
on any open set `U` on which the derivatives of `γ` of orders `1` through `k` are bounded by `M`,
with constants `1 + M` and `1`. -/
theorem isChangeOfVariables_graphFlattening_symm {k : ℕ} (hk : 1 ≤ k) {γ : E → ℝ}
    (hγ : ContDiff ℝ k γ) {U V : Opens (WithLp 2 (ℝ × E))}
    (hUV : MapsTo (graphFlattening γ hγ.continuous).symm U V) {M : ℝ}
    (hM : ∀ i, 1 ≤ i → i ≤ k → ∀ x ∈ (U : Set (WithLp 2 (ℝ × E))),
      ‖iteratedFDeriv ℝ i γ x.snd‖ ≤ M) :
    IsChangeOfVariables k U V (graphFlattening γ hγ.continuous).symm (1 + M) 1 := by
  rw [graphFlattening_symm] at hUV ⊢
  exact isChangeOfVariables_graphFlattening (γ := -γ) hk hγ.neg hUV fun i hi hik x hx ↦ by
    simpa [iteratedFDeriv_neg] using hM i hi hik x hx

end Wkp

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- **Flattening a `Cᵏ` boundary graph.** Let `k ≥ 1`, and suppose that inside the normal
cylinder of radius `b` and half-height `a`, in rigid coordinates `e` centred at a boundary point
`e.symm 0`, the set `Ω` is the region above the graph of a `Cᵏ` function `γ` with `γ 0 = 0`. Let
`Φ = e⁻¹ ∘ G⁻¹ ∘ e` and `Ψ = e⁻¹ ∘ G ∘ e`, where `G` is graph flattening by `γ`; they are mutually
inverse. Then there are an open convex set `U'`, an open neighbourhood `U` of `e.symm 0` and a
constant `L` such that `Φ` is a change of variables of order `k` from `U'` into `U` and `Ψ` one
from `U` into `U'`, both with Jacobian determinant one, and `Φ` maps the part of `U'` in the
half-space `0 < (e x).fst` onto `Ω ∩ U`. -/
theorem exists_isChangeOfVariables_of_contDiff {Omega : Set F}
    {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ} {k : ℕ} {a b : ℝ} (hk : 1 ≤ k) (ha : 0 < a)
    (hb : 0 < b) (hγ0 : γ 0 = 0) (hγ : ContDiff ℝ k γ)
    (hgraph : ∀ z ∈ normalCylinder a b, (e.symm z ∈ Omega ↔ γ z.snd < z.fst)) :
    ∃ (U' U : Opens F) (L : ℝ), e.symm 0 ∈ U ∧ Convex ℝ (U' : Set F) ∧
      Wkp.IsChangeOfVariables k U' U (e.symm ∘ (graphFlattening γ hγ.continuous).symm ∘ e) L 1 ∧
      Wkp.IsChangeOfVariables k U U' (e.symm ∘ graphFlattening γ hγ.continuous ∘ e) L 1 ∧
      (e.symm ∘ (graphFlattening γ hγ.continuous).symm ∘ e) ''
        ({x | 0 < (e x).fst} ∩ U') = Omega ∩ U := by
  set G := graphFlattening γ hγ.continuous
  -- A tangential radius `b' ≤ b` on which the graph stays within `a / 2` of zero.
  obtain ⟨δ, hδ, hγδ⟩ :=
    Metric.continuousAt_iff.mp (hγ.continuous.continuousAt (x := 0)) (a / 2) (half_pos ha)
  set b' := min b δ
  have hb' : 0 < b' := lt_min hb hδ
  have hγb' : ∀ y ∈ ball (0 : E) b', |γ y| < a / 2 := fun y hy ↦ by
    simpa [hγ0, Real.dist_eq] using
      hγδ (by simpa using (mem_ball_zero_iff.mp hy).trans_le (min_le_right b δ))
  -- A common bound `M` for the derivatives of `γ` of orders `1` through `k` on `closedBall 0 b'`.
  obtain ⟨M, -, hM⟩ := hγ.contDiffOn.exists_nonneg_bound_iteratedFDeriv_of_isOpen isOpen_univ
    (isCompact_closedBall (0 : E) b') (subset_univ _)
  have hMb : ∀ i, i ≤ k → ∀ y ∈ ball (0 : E) b', ‖iteratedFDeriv ℝ i γ y‖ ≤ M :=
    fun i hik y hy ↦ hM i hik y (ball_subset_closedBall hy)
  -- The flat cylinder `W` and its preimage `W₁` under flattening.
  let W : Opens (WithLp 2 (ℝ × E)) := ⟨normalCylinder (a / 2) b', isOpen_normalCylinder _ _⟩
  let W₁ : Opens (WithLp 2 (ℝ × E)) := ⟨G ⁻¹' W, W.isOpen.preimage G.continuous⟩
  have hW₁ (x : WithLp 2 (ℝ × E)) : x ∈ (W₁ : Set _) ↔ G x ∈ (W : Set _) := Iff.rfl
  have hW (w : WithLp 2 (ℝ × E)) :
      w ∈ (W : Set _) ↔ -(a / 2) < w.fst ∧ w.fst < a / 2 ∧ ‖w.snd‖ < b' :=
    mem_normalCylinder
  -- Unflattening `W` lands in the cylinder where `Ω` is described by the graph.
  have hcyl : ∀ w ∈ (W : Set (WithLp 2 (ℝ × E))), G.symm w ∈ normalCylinder a b := by
    intro w hw
    obtain ⟨h1, h2, h3⟩ := (hW w).1 hw
    have hγw := abs_lt.mp (hγb' w.snd (mem_ball_zero_iff.mpr h3))
    simp only [G, graphFlattening_symm_apply, mem_normalCylinder, WithLp.toLp_fst,
      WithLp.toLp_snd]
    exact ⟨by linarith [hγw.1], by linarith [hγw.2], h3.trans_le (min_le_left _ _)⟩
  have hWsnd : ∀ w ∈ (W : Set (WithLp 2 (ℝ × E))), w.snd ∈ ball (0 : E) b' := fun w hw ↦
    mem_ball_zero_iff.mpr ((hW w).1 hw).2.2
  have hΦG : Wkp.IsChangeOfVariables k W W₁ G.symm (1 + M) 1 :=
    Wkp.isChangeOfVariables_graphFlattening_symm hk hγ
      (fun w hw ↦ (hW₁ _).2 (by rwa [G.apply_symm_apply]))
      fun i _ hik w hw ↦ hMb i hik _ (hWsnd w hw)
  have hΨG : Wkp.IsChangeOfVariables k W₁ W G (1 + M) 1 :=
    Wkp.isChangeOfVariables_graphFlattening hk hγ (fun _ hx ↦ hx)
      fun i _ hik x hx ↦ by simpa [G] using hMb i hik _ (hWsnd _ hx)
  -- Pull everything back to `F` along the rigid coordinates.
  let U' : Opens F := ⟨e ⁻¹' W, W.isOpen.preimage e.continuous⟩
  let U : Opens F := ⟨e ⁻¹' W₁, W₁.isOpen.preimage e.continuous⟩
  have hU'mem (x : F) : x ∈ (U' : Set F) ↔ e x ∈ (W : Set _) := Iff.rfl
  have hUmem (x : F) : x ∈ (U : Set F) ↔ G (e x) ∈ (W : Set _) := Iff.rfl
  have hUe : MapsTo e.symm (W₁ : Set _) (U : Set F) := fun x hx ↦ by
    rwa [hUmem, e.apply_symm_apply]
  have hU'e : MapsTo e.symm (W : Set _) (U' : Set F) := fun x hx ↦ by
    rwa [hU'mem, e.apply_symm_apply]
  refine ⟨U', U, 1 + M, ?_, ?_, hΦG.conj e (fun _ hx ↦ hx) hUe,
    hΨG.conj e (fun _ hx ↦ hx) hU'e, ?_⟩
  · -- The boundary point is flattened to the origin, which lies in `W`.
    refine (hUmem _).2 ?_
    rw [e.apply_symm_apply, hW]
    simp [G, hγ0, ha, hb']
  · -- `U'` is the preimage of a product of an interval and a ball under an affine map.
    exact (convex_normalCylinder _ _).affine_preimage e.toAffineEquiv.toAffineMap
  · ext y
    constructor
    · rintro ⟨x, ⟨hxH, hxU'⟩, rfl⟩
      have hz := hcyl (e x) ((hU'mem x).1 hxU')
      refine ⟨?_, ?_⟩
      · simp only [Function.comp_apply]
        rw [hgraph _ hz]
        simpa [G] using hxH
      · rw [hUmem, Function.comp_apply, Function.comp_apply, e.apply_symm_apply,
          G.apply_symm_apply]
        exact (hU'mem x).1 hxU'
    · rintro ⟨hyΩ, hyU⟩
      have hz : e y ∈ normalCylinder a b := by
        simpa using hcyl (G (e y)) ((hUmem y).1 hyU)
      have hlt : γ (e y).snd < (e y).fst := (hgraph _ hz).1 (by simpa using hyΩ)
      refine ⟨e.symm (G (e y)), ⟨?_, ?_⟩, ?_⟩
      · simpa [G] using hlt
      · rw [hU'mem, e.apply_symm_apply]
        exact (hUmem y).1 hyU
      · simp

end TauCeti
