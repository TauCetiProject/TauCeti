/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Analysis.InnerProductSpace.Projection.Basic

/-!
# Covectors and graphs over an orthogonal hyperplane

Let `e` be a unit vector of a real inner product space and `v` a vector of the orthogonal
hyperplane `(ℝ ∙ e)ᗮ` with `‖v‖ ≤ 1`. By Pythagoras in orthogonal line coordinates
(`TauCeti.norm_add_smul_sq`), the vectors `±√(1 - ‖v‖²) e - v` have norm one, so every covector
`L` satisfies `√(1 - ‖v‖²) |L e| - L v ≤ ‖L‖`. This pointwise bound is what lets the variation
of a function along `e`, weighted by `√(1 - ‖v‖²)`, be combined with its variation in the
transverse direction `-v` without exceeding its total variation.

Orthogonal line coordinates `TauCeti.orthogonalLineEquiv` also identify the graph
`Set.range (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v)` of a scalar function `g : (ℝ ∙ v)ᗮ → ℝ` over
the orthogonal hyperplane of a unit vector `v` with the image of `g.graph`: when `g` is continuous
(and in particular when `g` is Lipschitz), this graph is closed in `E`, and when `g` is
`K`-Lipschitz the parametrization `w ↦ (w : E) + g w • v` is `(1 + K)`-Lipschitz. We also record
the transformation of a graph `{x | ⟪x, e⟫ = w (P x)}` under a continuous linear equivalence, and
the collapse of orthogonal graphs and hyperplanes to singletons in dimension one.

## Main results

* `TauCeti.sqrt_mul_abs_apply_sub_apply_le`: `√(1 - ‖v‖²) |L e| - L v ≤ ‖L‖` for a covector `L`,
  a unit vector `e` and `v ⊥ e` with `‖v‖ ≤ 1`.
* `TauCeti.setOf_inner_eq_eq_range` and `TauCeti.vadd_setOf_inner_eq`: parametric graphs and
  translations over `(𝕜 ∙ e)ᗮ`.
* `TauCeti.lipschitzWith_coe_add_smul`: `w ↦ (w : E) + g w • v` is `(1 + K)`-Lipschitz when
  `‖v‖ = 1` and `g : (ℝ ∙ v)ᗮ → ℝ` is `K`-Lipschitz.
* `TauCeti.isClosed_range_add_smul_of_continuous` and
  `TauCeti.isClosed_range_add_smul_of_lipschitzWith`: a continuous or globally Lipschitz graph over
  `(ℝ ∙ v)ᗮ` (`‖v‖ = 1`) is closed.
* `TauCeti.image_continuousLinearEquiv_setOf_inner_eq`: image of a graph over `(ℝ ∙ e)ᗮ` under a
  continuous linear equivalence `L : E ≃L[ℝ] F`.
* `TauCeti.range_eq_singleton_of_finrank_eq_one` and
  `TauCeti.exists_unit_singleton_eq_setOf_inner_eq`: orthogonal graphs and singletons in
  dimension one.
-/

public section

open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A covector `L` and a vector `v ⊥ e` with `‖v‖ ≤ 1` satisfy
`√(1 - ‖v‖²) |L e| - L v ≤ ‖L‖`: the left side is `L` applied to `±√(1 - ‖v‖²) e - v`, a vector
of norm one by `TauCeti.norm_add_smul_sq`. -/
theorem sqrt_mul_abs_apply_sub_apply_le (e : E) (he : ‖e‖ = 1) (L : E →L[ℝ] ℝ)
    {v : (ℝ ∙ e)ᗮ} (hv : ‖v‖ ≤ 1) :
    √(1 - ‖v‖ ^ 2) * |L e| - L v ≤ ‖L‖ := by
  have key (σ : ℝ) (hσ : σ ^ 2 = 1) : σ * √(1 - ‖v‖ ^ 2) * L e - L v ≤ ‖L‖ := by
    set z : E := ((-v : (ℝ ∙ e)ᗮ) : E) + (σ * √(1 - ‖v‖ ^ 2)) • e
    have hz : ‖z‖ ^ 2 = 1 := by
      rw [norm_add_smul_sq e he, norm_neg, mul_pow, hσ,
        Real.sq_sqrt (by nlinarith [norm_nonneg v])]
      ring
    calc σ * √(1 - ‖v‖ ^ 2) * L e - L v = L z := by simp [z, sub_eq_neg_add]
      _ ≤ ‖L‖ * 1 := (le_abs_self _).trans (L.le_opNorm_of_le (by nlinarith [norm_nonneg z]))
      _ = ‖L‖ := mul_one _
  rcases le_total 0 (L e) with h | h
  · simpa [abs_of_nonneg h] using key 1 (by norm_num)
  · simpa [abs_of_nonpos h] using key (-1) (by norm_num)

/-- The graph map `w ↦ (w : E) + g w • v` over `(ℝ ∙ v)ᗮ` along a unit vector `v` is
`(1 + K)`-Lipschitz when `g` is `K`-Lipschitz. -/
theorem lipschitzWith_coe_add_smul {v : E} (hv : ‖v‖ = 1) {K : ℝ≥0} {g : (ℝ ∙ v)ᗮ → ℝ}
    (hg : LipschitzWith K g) :
    LipschitzWith (1 + K) (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) := by
  simpa using (ℝ ∙ v)ᗮ.subtypeₗᵢ.lipschitzWith.add
    ((LinearIsometry.toSpanSingleton ℝ E hv).lipschitzWith.comp hg)

/-- The graph `Set.range (fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v)` over the orthogonal complement of
a unit vector `v` is closed whenever `g` is continuous (in particular whenever `g` is Lipschitz). -/
theorem isClosed_range_add_smul_of_continuous {v : E} (hv : ‖v‖ = 1) {g : (ℝ ∙ v)ᗮ → ℝ}
    (hg : Continuous g) :
    IsClosed (Set.range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) := by
  have heq : (Set.range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) =
      orthogonalLineEquiv v hv '' g.graph := by
    ext z
    simp [Function.graph, eq_comm]
  rw [heq]
  exact (orthogonalLineEquiv v hv).toHomeomorph.isClosed_image.mpr hg.isClosed_graph

/-- A globally Lipschitz graph over `(ℝ ∙ v)ᗮ` (`‖v‖ = 1`) is closed. -/
theorem isClosed_range_add_smul_of_lipschitzWith {v : E} (hv : ‖v‖ = 1) {K : ℝ≥0}
    {g : (ℝ ∙ v)ᗮ → ℝ} (hg : LipschitzWith K g) :
    IsClosed (Set.range fun w : (ℝ ∙ v)ᗮ => (w : E) + g w • v) :=
  isClosed_range_add_smul_of_continuous hv hg.continuous

/-- A graph `{x | ⟪e, x⟫_𝕜 = φ (P x)}` over `(𝕜 ∙ e)ᗮ` for a unit vector `e` is the parametric
range `y ↦ y + φ y • e`. -/
theorem setOf_inner_eq_eq_range {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] {e : F} (he : ‖e‖ = 1) (φ : (𝕜 ∙ e)ᗮ → 𝕜) :
    {x : F | inner 𝕜 e x = φ ((𝕜 ∙ e)ᗮ.orthogonalProjectionOnto x)} =
      Set.range fun y : (𝕜 ∙ e)ᗮ => (y : F) + φ y • e := by
  ext x; simp only [Set.mem_ofPred_eq, Set.mem_range]
  refine ⟨fun hx => ⟨_, hx ▸ orthogonalProjectionOnto_add_inner_smul he x⟩, ?_⟩
  rintro ⟨y, rfl⟩
  simp [inner_add_right, inner_smul_right,
    Submodule.mem_orthogonal_singleton_iff_inner_right.mp y.property, he]

open scoped Pointwise in
/-- Translating a graph `{x | ⟪e, x⟫_𝕜 = φ (P x)}` over `(𝕜 ∙ e)ᗮ` by `v` translates the base
coordinate by `P v` and adds `⟪e, v⟫_𝕜` to the height. -/
theorem vadd_setOf_inner_eq {𝕜 F : Type*} [RCLike 𝕜] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] (e v : F) (φ : (𝕜 ∙ e)ᗮ → 𝕜) :
    v +ᵥ {x : F | inner 𝕜 e x = φ ((𝕜 ∙ e)ᗮ.orthogonalProjectionOnto x)} =
      {x : F | inner 𝕜 e x =
        φ ((𝕜 ∙ e)ᗮ.orthogonalProjectionOnto x - (𝕜 ∙ e)ᗮ.orthogonalProjectionOnto v) +
          inner 𝕜 e v} := by
  ext x
  simp only [Set.mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub, Set.mem_ofPred_eq,
    map_sub, inner_sub_right, sub_eq_iff_eq_add]

/-- The image of a graph `{x | ⟪x, e⟫ = w (P x)}` over `(ℝ ∙ e)ᗮ` under a continuous linear
equivalence `L : E ≃L[ℝ] F` is again a graph over `(ℝ ∙ e')ᗮ` for some unit vector `e'` of a
positively scaled pullback `c * w ∘ B - ℓ`, where `B` and `ℓ` are continuous linear. -/
theorem image_continuousLinearEquiv_setOf_inner_eq {F : Type*}
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (L : E ≃L[ℝ] F) {e : E} (he : ‖e‖ = 1)
    (w : ↥(ℝ ∙ e)ᗮ → ℝ) :
    ∃ (e' : F) (_ : ‖e'‖ = 1) (c : ℝ) (_ : 0 < c)
      (B : ↥(ℝ ∙ e')ᗮ →L[ℝ] ↥(ℝ ∙ e)ᗮ) (ℓ : ↥(ℝ ∙ e')ᗮ →L[ℝ] ℝ),
      L '' {x : E | inner ℝ x e = w ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto x)} =
        {z : F | inner ℝ z e' = c * w (B ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z)) -
          ℓ ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z)} := by
  let c := ‖L e‖
  let e' : F := c⁻¹ • L e
  have hc : 0 < c := norm_pos_iff.2 ((map_ne_zero_iff L L.injective).2 fun h => by simp [h] at he)
  have he' : ‖e'‖ = 1 := by simp [e', c, norm_smul, inv_mul_cancel₀ hc.ne']
  let B : ↥(ℝ ∙ e')ᗮ →L[ℝ] ↥(ℝ ∙ e)ᗮ :=
    (ℝ ∙ e)ᗮ.orthogonalProjectionOnto.comp (L.symm.toContinuousLinearMap.comp (ℝ ∙ e')ᗮ.subtypeL)
  let ℓ : ↥(ℝ ∙ e')ᗮ →L[ℝ] ℝ :=
    c • ((innerSL ℝ e).comp (L.symm.toContinuousLinearMap.comp (ℝ ∙ e')ᗮ.subtypeL))
  refine ⟨e', he', c, hc, B, ℓ, Set.ext fun z => ?_⟩
  have hd := congrArg L.symm (real_inner_comm e' z ▸ orthogonalProjectionOnto_add_inner_smul he' z)
  have hLe' : L.symm e' = c⁻¹ • e := by simp [e', map_smul]
  simp only [map_add, map_smul, hLe', smul_smul] at hd
  have hproj : (ℝ ∙ e)ᗮ.orthogonalProjectionOnto (L.symm z) =
      B ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z) := by
    simpa [B, map_add, map_smul,
      Submodule.orthogonalProjectionOnto_orthogonalComplement_singleton_eq_zero]
      using (congrArg (ℝ ∙ e)ᗮ.orthogonalProjectionOnto hd).symm
  have hi : c * inner ℝ (L.symm z) e = ℓ ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z) + inner ℝ z e' := by
    have h : inner ℝ (L.symm ((ℝ ∙ e')ᗮ.orthogonalProjectionOnto z)) e + inner ℝ z e' * c⁻¹ =
        inner ℝ (L.symm z) e := by
      simpa [inner_add_left, real_inner_smul_left, he] using congrArg (inner ℝ · e) hd
    rw [← h, mul_add]
    simp [ℓ, real_inner_comm e]
    field_simp [hc.ne']
  simp only [Set.mem_image, Set.mem_ofPred_eq]
  refine ⟨?_, fun hz => ⟨L.symm z, mul_left_cancel₀ hc.ne' (by rw [hproj]; linarith),
    L.apply_symm_apply z⟩⟩
  rintro ⟨x, hx, rfl⟩
  rw [L.symm_apply_apply] at hproj hi
  have hmul := congrArg (c * ·) hx
  rw [hproj] at hmul
  linarith

/-- In a one-dimensional real inner product space, every parametric graph over `(ℝ ∙ e)ᗮ` collapses
to the singleton `{φ 0 • e}`. -/
theorem range_eq_singleton_of_finrank_eq_one (hdim : Module.finrank ℝ E = 1) {e : E}
    (he : e ≠ 0) (φ : ↥(ℝ ∙ e)ᗮ → ℝ) :
    (Set.range fun y : ↥(ℝ ∙ e)ᗮ => (y : E) + φ y • e) = {φ 0 • e} := by
  have horth := Submodule.orthogonal_span_singleton_eq_bot_of_finrank_eq_one hdim (v := e) he
  ext z
  refine ⟨?_, by rintro rfl; exact ⟨0, by simp⟩⟩
  rintro ⟨y, rfl⟩
  have hy0 : y = 0 := Subtype.ext ((Submodule.mem_bot ℝ).1 (horth ▸ y.property))
  simp [hy0]

/-- In a one-dimensional real inner product space, every singleton `{x}` is an affine hyperplane
`{z | ⟪z, e⟫ = ⟪x, e⟫}` for a unit vector `e`. -/
theorem exists_unit_singleton_eq_setOf_inner_eq (hdim : Module.finrank ℝ E = 1) (x : E) :
    ∃ (e : E) (_ : ‖e‖ = 1), {x} = {z : E | inner ℝ z e = inner ℝ x e} := by
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hdim
  obtain ⟨e, he⟩ := exists_norm_eq E (zero_le_one (α := ℝ))
  have horth := Submodule.orthogonal_span_singleton_eq_bot_of_finrank_eq_one hdim (v := e)
    (fun h => by simp [h] at he)
  have hrep (w : E) : inner ℝ w e • e = w := by
    have h := orthogonalProjectionOnto_add_inner_smul (𝕜 := ℝ) he w
    have hmem : ((ℝ ∙ e)ᗮ.orthogonalProjectionOnto w : E) ∈ (⊥ : Submodule ℝ E) := by
      rw [← horth]
      exact Subtype.prop _
    have h0 := (Submodule.mem_bot ℝ).1 hmem
    simpa only [h0, zero_add, real_inner_comm] using h
  exact ⟨e, he, Set.ext fun z => ⟨by rintro rfl; simp, fun h =>
    Set.mem_singleton_iff.2 (by rw [← hrep z, ← hrep x, Set.mem_ofPred_eq.mp h])⟩⟩

end TauCeti
