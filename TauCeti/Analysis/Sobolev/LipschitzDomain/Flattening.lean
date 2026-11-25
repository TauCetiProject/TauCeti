/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.GraphFlattening.Basic
public import TauCeti.Analysis.Sobolev.LipschitzDomain.Basic
public import TauCeti.Analysis.Sobolev.Wkp.ChangeOfVariables
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.InnerProductSpace.HalfSpace
import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection

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
* `TauCeti.exists_isChangeOfVariables_normalHalfSpace_of_contDiff`: for a domain in `ℝ × E` itself,
  the flattening chart `e⁻¹ ∘ G⁻¹` maps the normal half-space `{0 < x.fst}`, in standard position,
  onto the domain near the boundary point, which is the form the half-space estimates are stated
  in.
* `TauCeti.exists_isChangeOfVariables_halfSpace_of_contDiff_graph`: the flattening chart fixes the
  boundary point, which lies in the closure of the flat half-space, and maps the part of a
  neighbourhood in that half-space onto the domain near the boundary point.
* `TauCeti.mapsTo_closure_of_image_eq` and `TauCeti.mapsTo_setOf_le_inner_of_image_eq`: a
  flattening chart maps the closed half-space part of its domain into the closure of the domain,
  and its inverse maps the closure of the domain back into the closed half-space.

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
open scoped InnerProductSpace

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

/-- **Flattening a `Cᵏ` boundary graph, in flat coordinates.** Let `k ≥ 1`, and suppose that
inside the normal cylinder of radius `b` and half-height `a` the set `Ω` is the region above the
graph of a `Cᵏ` function `γ` with `γ 0 = 0`. Let `G` be graph flattening by `γ`. Then there are an
open convex neighbourhood `W` of `0`, an open set `W₁` and a constant `L` such that `G⁻¹` is a
change of variables of order `k` from `W` into `W₁` and `G` one from `W₁` into `W`, both with
Jacobian determinant one, and `G⁻¹` maps the part of `W` in the half-space `{0 < x.fst}` onto
`Ω ∩ W₁`. Both flattening theorems below transport this along rigid coordinates. -/
private theorem exists_isChangeOfVariables_graphFlattening_of_contDiff
    {Omega : Set (WithLp 2 (ℝ × E))} {γ : E → ℝ} {k : ℕ} {a b : ℝ} (hk : 1 ≤ k) (ha : 0 < a)
    (hb : 0 < b) (hγ0 : γ 0 = 0) (hγ : ContDiff ℝ k γ)
    (hgraph : ∀ z ∈ normalCylinder a b, (z ∈ Omega ↔ γ z.snd < z.fst)) :
    ∃ (W W₁ : Opens (WithLp 2 (ℝ × E))) (L : ℝ), 0 ∈ W ∧
      Convex ℝ (W : Set (WithLp 2 (ℝ × E))) ∧
      Wkp.IsChangeOfVariables k W W₁ (graphFlattening γ hγ.continuous).symm L 1 ∧
      Wkp.IsChangeOfVariables k W₁ W (graphFlattening γ hγ.continuous) L 1 ∧
      (graphFlattening γ hγ.continuous).symm '' ({x | 0 < x.fst} ∩ W) = Omega ∩ W₁ := by
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
  refine ⟨W, W₁, 1 + M, (hW 0).2 ?_, convex_normalCylinder _ _, hΦG, hΨG, ?_⟩
  · simp [ha, hb']
  · ext y
    constructor
    · rintro ⟨x, ⟨hxH, hxW⟩, rfl⟩
      refine ⟨(hgraph _ (hcyl x hxW)).2 (by simpa [G] using hxH), (hW₁ _).2 ?_⟩
      rwa [G.apply_symm_apply]
    · rintro ⟨hyΩ, hyW₁⟩
      have hz : y ∈ normalCylinder a b := by simpa using hcyl (G y) ((hW₁ y).1 hyW₁)
      refine ⟨G y, ⟨?_, (hW₁ y).1 hyW₁⟩, G.symm_apply_apply y⟩
      simpa [G] using (hgraph _ hz).1 hyΩ

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
  obtain ⟨W, W₁, L, hW0, hWc, hΦG, hΨG, himage⟩ :=
    exists_isChangeOfVariables_graphFlattening_of_contDiff (Omega := e.symm ⁻¹' Omega) hk ha hb
      hγ0 hγ hgraph
  -- Pull everything back to `F` along the rigid coordinates.
  let U' : Opens F := ⟨e ⁻¹' W, W.isOpen.preimage e.continuous⟩
  let U : Opens F := ⟨e ⁻¹' W₁, W₁.isOpen.preimage e.continuous⟩
  have hU'mem (x : F) : x ∈ (U' : Set F) ↔ e x ∈ (W : Set _) := Iff.rfl
  have hUmem (x : F) : x ∈ (U : Set F) ↔ e x ∈ (W₁ : Set _) := Iff.rfl
  have hUe : MapsTo e.symm (W₁ : Set _) (U : Set F) := fun x hx ↦ by
    rwa [hUmem, e.apply_symm_apply]
  have hU'e : MapsTo e.symm (W : Set _) (U' : Set F) := fun x hx ↦ by
    rwa [hU'mem, e.apply_symm_apply]
  refine ⟨U', U, L, ?_, hWc.affine_preimage e.toAffineEquiv.toAffineMap,
    hΦG.conj e (fun _ hx ↦ hx) hUe, hΨG.conj e (fun _ hx ↦ hx) hU'e, ?_⟩
  · -- The boundary point is flattened to the origin, which lies in `W`.
    have h0 : G.symm 0 = 0 := by simp [G, hγ0]
    exact hUe (h0 ▸ hΦG.mapsTo hW0)
  · -- `e` carries the half-space part of `U'` to that of `W`, which `G⁻¹` maps onto `Ω ∩ W₁`.
    have hpre : {x | 0 < (e x).fst} ∩ (U' : Set F) = e ⁻¹' ({x | 0 < x.fst} ∩ W) := rfl
    rw [hpre, image_comp, image_comp, e.surjective.image_preimage, himage, image_preimage_inter,
      image_eq_preimage_of_inverse e.apply_symm_apply e.symm_apply_apply]
    rfl

/-- **Flattening a `Cᵏ` boundary graph onto the normal half-space.** Let `k ≥ 1`, and suppose that
inside the normal cylinder of radius `b` and half-height `a`, in rigid coordinates `e` of `ℝ × E`
centred at a boundary point `e.symm 0`, the set `Ω` is the region above the graph of a `Cᵏ`
function `γ` with `γ 0 = 0`. Let `G` be graph flattening by `γ`. Then there are an open convex
neighbourhood `U'` of `0`, an open set `U` and a constant `L` such that `e⁻¹ ∘ G⁻¹` is a change of
variables of order `k` from `U'` into `U` and its inverse `G ∘ e` one from `U` into `U'`, both with
Jacobian determinant one, and `e⁻¹ ∘ G⁻¹` maps the part of `U'` in the normal half-space
`{0 < x.fst}` onto `Ω ∩ U`. Unlike `TauCeti.exists_isChangeOfVariables_of_contDiff`, the flat side
is the half-space in standard position, not its image under `e⁻¹`. -/
theorem exists_isChangeOfVariables_normalHalfSpace_of_contDiff
    {Omega : Set (WithLp 2 (ℝ × E))} {e : WithLp 2 (ℝ × E) ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ}
    {k : ℕ} {a b : ℝ} (hk : 1 ≤ k) (ha : 0 < a) (hb : 0 < b) (hγ0 : γ 0 = 0)
    (hγ : ContDiff ℝ k γ)
    (hgraph : ∀ z ∈ normalCylinder a b, (e.symm z ∈ Omega ↔ γ z.snd < z.fst)) :
    ∃ (U' U : Opens (WithLp 2 (ℝ × E))) (L : ℝ), 0 ∈ U' ∧
      Convex ℝ (U' : Set (WithLp 2 (ℝ × E))) ∧
      Wkp.IsChangeOfVariables k U' U (e.symm ∘ (graphFlattening γ hγ.continuous).symm) L 1 ∧
      Wkp.IsChangeOfVariables k U U' (graphFlattening γ hγ.continuous ∘ e) L 1 ∧
      (e.symm ∘ (graphFlattening γ hγ.continuous).symm) ''
        ((normalHalfSpace (E := E) 0 : Set (WithLp 2 (ℝ × E))) ∩ U') = Omega ∩ U := by
  set G := graphFlattening γ hγ.continuous
  obtain ⟨W, W₁, L, hW0, hWc, hΦG, hΨG, himage⟩ :=
    exists_isChangeOfVariables_graphFlattening_of_contDiff (Omega := e.symm ⁻¹' Omega) hk ha hb
      hγ0 hγ hgraph
  -- The curved side is `U = e⁻¹(W₁)`; `W` stays in standard position.
  let U : Opens (WithLp 2 (ℝ × E)) := ⟨e ⁻¹' W₁, W₁.isOpen.preimage e.continuous⟩
  let W' : Opens (WithLp 2 (ℝ × E)) := ⟨e ⁻¹' W, W.isOpen.preimage e.continuous⟩
  have hUe : MapsTo e.symm (W₁ : Set _) (U : Set _) := fun x hx ↦ by
    simpa only [U, SetLike.mem_coe, Opens.mem_mk, mem_preimage, e.apply_symm_apply] using hx
  have hW'e : MapsTo e.symm (W : Set _) (W' : Set _) := fun x hx ↦ by
    simpa only [W', SetLike.mem_coe, Opens.mem_mk, mem_preimage, e.apply_symm_apply] using hx
  -- `G ∘ e = e ∘ (e⁻¹ ∘ G ∘ e)`, the conjugate of `G` followed by `e`.
  have hΨe : e ∘ (e.symm ∘ G ∘ e) = G ∘ e := by
    funext x
    simp
  refine ⟨W, U, L, hW0, hWc, hΦG.affineIsometryEquiv_comp e.symm hUe,
    hΨe ▸ (hΨG.conj e (fun _ hx ↦ hx) hW'e).affineIsometryEquiv_comp e fun _ hx ↦ hx, ?_⟩
  -- `G⁻¹` maps the half-space part of `W` onto `e⁻¹' Ω ∩ W₁`, which `e⁻¹` carries to `Ω ∩ U`.
  rw [coe_normalHalfSpace, image_comp, himage, image_preimage_inter,
    image_eq_preimage_of_inverse e.apply_symm_apply e.symm_apply_apply]
  rfl

omit [FiniteDimensional ℝ E] in
/-- **Flattening a boundary graph.** Let `F` be finite-dimensional, and suppose that in rigid
coordinates `e : F ≃ ℝ × E` centred at `x₀ = e⁻¹ 0`, inside the normal cylinder of half-height
`h₀` and radius `r₀`, `Ω` is the region above the graph of a `Cᵏ` function `γ`, `k ≥ 1`, with
`γ 0 = 0`. Let `G` be the graph flattening of `γ`. Then `Φ = e⁻¹ ∘ G⁻¹ ∘ e` and
`Ψ = e⁻¹ ∘ G ∘ e` are mutually inverse changes of variables of order `k` between open sets
`U' ∋ x₀` and `U`, with Jacobian determinants at least one in absolute value; `Φ` fixes `x₀` and
maps the part of `U'` in a half-space `H`, whose closure contains `x₀`, onto `Ω ∩ U`. -/
theorem exists_isChangeOfVariables_halfSpace_of_contDiff_graph [FiniteDimensional ℝ F]
    {Omega : Set F} {e : F ≃ᵃⁱ[ℝ] WithLp 2 (ℝ × E)} {γ : E → ℝ}
    {h₀ r₀ : ℝ} {k : ℕ} (hk : 1 ≤ k) (hh₀ : 0 < h₀) (hr₀ : 0 < r₀) (hγ0 : γ 0 = 0)
    (hγ : ContDiff ℝ k γ)
    (hgraph : ∀ z ∈ normalCylinder h₀ r₀, (e.symm z ∈ Omega ↔ γ z.snd < z.fst)) :
    ∃ (U' U : Opens F) (L : ℝ) (ν : F) (c₀ : ℝ),
      Wkp.IsChangeOfVariables k U' U (e.symm ∘ (graphFlattening γ hγ.continuous).symm ∘ e) L 1 ∧
      Wkp.IsChangeOfVariables k U U' (e.symm ∘ graphFlattening γ hγ.continuous ∘ e) L 1 ∧
      ν ≠ 0 ∧ (e.symm ∘ (graphFlattening γ hγ.continuous).symm ∘ e) ''
        ({x | c₀ < ⟪x, ν⟫_ℝ} ∩ U') = Omega ∩ U ∧ e.symm 0 ∈ U' ∧
      e.symm 0 ∈ closure {x | c₀ < ⟪x, ν⟫_ℝ} ∧
      (e.symm ∘ (graphFlattening γ hγ.continuous).symm ∘ e) (e.symm 0) = e.symm 0 := by
  -- `E` is finite-dimensional, being a factor of `ℝ × E ≃ F`.
  have : FiniteDimensional ℝ (WithLp 2 (ℝ × E)) :=
    e.linearIsometryEquiv.toLinearEquiv.finiteDimensional
  have : FiniteDimensional ℝ E := Module.Finite.of_surjective (WithLp.sndₗ 2 ℝ ℝ E)
    fun y => ⟨WithLp.toLp 2 (0, y), rfl⟩
  obtain ⟨U', U, L, hx₀U, -, hΦ, hΨ, himage⟩ :=
    exists_isChangeOfVariables_of_contDiff hk hh₀ hr₀ hγ0 hγ hgraph
  set G := graphFlattening γ hγ.continuous
  -- `Ψ` fixes `x₀`, hence so does its inverse `Φ`.
  have hΨx₀ : (e.symm ∘ G ∘ e) (e.symm 0) = e.symm 0 := by simp [G, hγ0]
  have hΦx₀ : (e.symm ∘ G.symm ∘ e) (e.symm 0) = e.symm 0 := by
    conv_lhs => rw [← hΨx₀]
    simp
  -- In rigid coordinates the flat side is the half-space `{-(e 0).fst < ⟪x, ν⟫}`.
  set ν := e.linearIsometryEquiv.symm (WithLp.toLp 2 (1, 0))
  have hHν (x : F) : 0 < (e x).fst ↔ -(e 0).fst < ⟪x, ν⟫_ℝ := by
    rw [e.fst_apply_eq_inner_add]
    constructor <;> intro h <;> linarith
  have hH : {x | 0 < (e x).fst} = {x | -(e 0).fst < ⟪x, ν⟫_ℝ} := Set.ext hHν
  refine ⟨U', U, L, ν, -(e 0).fst, hΦ, hΨ, by simp [ν], hH ▸ himage,
    hΨx₀ ▸ hΨ.mapsTo hx₀U, ?_, hΦx₀⟩
  -- `x₀` is a limit of the points `e⁻¹ (t, 0)`, `t > 0`, of the flat side.
  refine Metric.mem_closure_iff.2 fun ε hε => ⟨e.symm (WithLp.toLp 2 (ε / 2, 0)), ?_, ?_⟩
  · exact (hHν _).1 (by simpa using half_pos hε)
  · rw [dist_comm, e.symm.dist_map, dist_zero_right]
    simpa [WithLp.prod_norm_eq_of_L2, abs_of_pos hε] using half_lt_self hε


/-- **A flattening chart on the closed half-space.** If `Φ` is continuous on an open set `U'` and
maps the part of `U'` in the open half-space `{c₀ < ⟪y, ν⟫}` onto `Ω ∩ U`, then it maps the part
of `U'` in the closed half-space `{c₀ ≤ ⟪y, ν⟫}` into the closure of `Ω`. -/
theorem mapsTo_closure_of_image_eq {Omega U U' : Set F} {Φ : F → F} {ν : F} {c₀ : ℝ}
    (hν : ν ≠ 0) (hU' : IsOpen U') (hΦc : ContinuousOn Φ U')
    (himage : Φ '' ({y | c₀ < ⟪y, ν⟫_ℝ} ∩ U') = Omega ∩ U) :
    MapsTo Φ ({y | c₀ ≤ ⟪y, ν⟫_ℝ} ∩ U') (closure Omega) := fun y hy => by
  have h := mem_closure_image (hΦc.continuousAt (hU'.mem_nhds hy.2))
    (mem_closure_setOf_lt_inner_inter hν hy.1 hU' hy.2)
  rw [himage] at h
  exact closure_mono inter_subset_left h

/-- **The inverse of a flattening chart on the closure of the domain.** If `Φ` maps the part of
`U'` in the open half-space `{c₀ < ⟪y, ν⟫}` onto `Ω ∩ U`, with `U` open, and `Ψ` is continuous on
`U` and `Ψ (Φ y) = y` for `y` in the part of `U'` in the open half-space, then `Ψ` maps
`closure Ω ∩ U` into the closed half-space `{c₀ ≤ ⟪y, ν⟫}`. -/
theorem mapsTo_setOf_le_inner_of_image_eq {Omega U U' : Set F} {Φ Ψ : F → F} {ν : F} {c₀ : ℝ}
    (hU : IsOpen U) (hΨc : ContinuousOn Ψ U) (hΨΦ : LeftInvOn Ψ Φ ({y | c₀ < ⟪y, ν⟫_ℝ} ∩ U'))
    (himage : Φ '' ({y | c₀ < ⟪y, ν⟫_ℝ} ∩ U') = Omega ∩ U) :
    MapsTo Ψ (closure Omega ∩ U) {y | c₀ ≤ ⟪y, ν⟫_ℝ} := fun x hx => by
  have hx' : x ∈ closure (Omega ∩ U) := by
    rw [inter_comm]
    exact hU.inter_closure ⟨hx.2, hx.1⟩
  rw [← himage] at hx'
  have hΨim : Ψ '' (Φ '' ({y | c₀ < ⟪y, ν⟫_ℝ} ∩ U')) ⊆ {y | c₀ ≤ ⟪y, ν⟫_ℝ} := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [hΨΦ hy, mem_ofPred_eq]
    rw [mem_inter_iff, mem_ofPred_eq] at hy
    exact hy.1.le
  exact closure_minimal hΨim (isClosed_le continuous_const (continuous_id.inner continuous_const))
    (mem_closure_image (hΨc.continuousAt (hU.mem_nhds hx.2)) hx')

end TauCeti
