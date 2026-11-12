/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.ProdLp
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Homeomorph.Lemmas

/-!
# The unit sphere of an `L²` product as a union of two solid pieces

Let `F` and `G` be real normed spaces. A point `x` of the unit sphere of the `L²` product
`WithLp 2 (F × G)` satisfies `‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1`, so the sphere is the union of the two
closed pieces `‖x.fst‖ ≤ ‖x.snd‖` and `‖x.snd‖ ≤ ‖x.fst‖`, which meet in the common frontier
`‖x.fst‖ = ‖x.snd‖`. The first piece is homeomorphic to the product of the closed unit ball of
`F` with the unit sphere of `G`, through `x ↦ (x.fst / ‖x.snd‖, x.snd / ‖x.snd‖)`, whose inverse
sends `(u, v)` to `(u, v) / √(1 + ‖u‖ ^ 2)`; symmetrically, the second piece is homeomorphic to the
product of the unit sphere of `F` with the closed unit ball of `G`.

This is the decomposition of the join `S(F) * S(G) = S(F ⊕ G)` into the two mapping cylinders.
For `F = G = ℂ` it writes the `3`-sphere as the union of two solid tori `D² × S¹` and `S¹ × D²`
glued along the torus `‖x.fst‖ = ‖x.snd‖`, the genus-one Heegaard splitting of the `3`-sphere.

## Main definitions

* `TauCeti.sphereProdFstLeHomeomorph F G`: the piece `‖x.fst‖ ≤ ‖x.snd‖` of the unit sphere of
  `WithLp 2 (F × G)` is homeomorphic to `closedBall (0 : F) 1 × sphere (0 : G) 1`.
* `TauCeti.sphereProdSndLeHomeomorph F G`: the piece `‖x.snd‖ ≤ ‖x.fst‖` is homeomorphic to
  `sphere (0 : F) 1 × closedBall (0 : G) 1`.

## Main results

* `TauCeti.frontier_setOf_norm_fst_le_norm_snd` and `TauCeti.frontier_setOf_norm_snd_le_norm_fst`:
  the frontier of each piece in the unit sphere is the set where `‖x.fst‖ = ‖x.snd‖`.
* `TauCeti.norm_sphereProdFstLeHomeomorph_fst_eq_one_iff` and
  `TauCeti.norm_sphereProdSndLeHomeomorph_snd_eq_one_iff`: each homeomorphism carries this common
  frontier onto the product of the two unit spheres.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Chapter 0 (joins; the
  decomposition of `S³` into two solid tori).
-/

public section

noncomputable section

open Metric Set Topology

namespace TauCeti

variable {F G : Type*} [SeminormedAddCommGroup F] [SeminormedAddCommGroup G]

/-- A point of the unit sphere of `WithLp 2 (F × G)` has `‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1`. -/
private theorem norm_fst_sq_add_norm_snd_sq_of_mem_sphere {x : WithLp 2 (F × G)}
    (hx : x ∈ sphere 0 1) :
    ‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1 := by
  rw [← WithLp.prod_norm_sq_eq_of_L2, mem_sphere_zero_iff_norm.1 hx, one_pow]

/-- On the piece `‖x.fst‖ ≤ ‖x.snd‖` of the unit sphere, the second component is nonzero. -/
private theorem norm_snd_pos {x : WithLp 2 (F × G)} (hx : x ∈ sphere 0 1)
    (hle : ‖x.fst‖ ≤ ‖x.snd‖) : 0 < ‖x.snd‖ := by
  have h := norm_fst_sq_add_norm_snd_sq_of_mem_sphere hx
  by_contra! h0
  have h0 : ‖x.snd‖ = 0 := le_antisymm h0 (norm_nonneg _)
  have h1 : ‖x.fst‖ = 0 := le_antisymm (h0 ▸ hle) (norm_nonneg _)
  simp [h0, h1] at h

/-- The positive scalar `1 / √(1 + r ^ 2)`; it normalizes `(u, v)` when `‖u‖ = r` and `v` is a
unit vector. -/
private def normalizer (r : ℝ) : ℝ := (√(1 + r ^ 2))⁻¹

private theorem normalizer_pos (r : ℝ) : 0 < normalizer r :=
  inv_pos.2 (Real.sqrt_pos.2 (by positivity))

private theorem continuous_normalizer : Continuous normalizer :=
  .inv₀ (by fun_prop) fun r ↦ (Real.sqrt_pos.2 (by positivity)).ne'

private theorem normalizer_sq (r : ℝ) : normalizer r ^ 2 * (1 + r ^ 2) = 1 := by
  rw [normalizer, inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]

/-- Exchanging the two factors of `WithLp 2 (F × G)` restricts to a homeomorphism of unit
spheres. -/
private def sphereProdComm : sphere (0 : WithLp 2 (F × G)) 1 ≃ₜ sphere (0 : WithLp 2 (G × F)) 1 :=
  (IsometryEquiv.withLpProdComm 2 F G).toHomeomorph.subtype fun x ↦ by
    simp only [mem_sphere_zero_iff_norm, IsometryEquiv.coe_toHomeomorph,
      (IsometryEquiv.withLpProdComm 2 F G).isometry.norm_map_of_map_zero (by simp)]

private theorem coe_sphereProdComm_apply (x : sphere (0 : WithLp 2 (F × G)) 1) :
    (sphereProdComm x : WithLp 2 (G × F)) =
      WithLp.toLp 2 ((x : WithLp 2 (F × G)).snd, (x : WithLp 2 (F × G)).fst) := by
  simp [sphereProdComm]

private theorem coe_sphereProdComm_symm_apply (y : sphere (0 : WithLp 2 (G × F)) 1) :
    (sphereProdComm.symm y : WithLp 2 (F × G)) =
      WithLp.toLp 2 ((y : WithLp 2 (G × F)).snd, (y : WithLp 2 (G × F)).fst) := by
  simp [sphereProdComm]

variable [NormedSpace ℝ F] [NormedSpace ℝ G]

/-- The inverse of `TauCeti.sphereProdFstLeHomeomorph`: the unit vector `(u, v) / √(1 + ‖u‖ ^ 2)`
for `u` in the closed unit ball of `F` and `v` in the unit sphere of `G`. -/
private def sphereProdFstLeInv (p : closedBall (0 : F) 1 × sphere (0 : G) 1) :
    WithLp 2 (F × G) :=
  WithLp.toLp 2 (normalizer ‖(p.1 : F)‖ • (p.1 : F), normalizer ‖(p.1 : F)‖ • (p.2 : G))

private theorem norm_snd_sphereProdFstLeInv (p : closedBall (0 : F) 1 × sphere (0 : G) 1) :
    ‖(sphereProdFstLeInv p).snd‖ = normalizer ‖(p.1 : F)‖ := by
  simp [sphereProdFstLeInv, norm_smul, (normalizer_pos _).le, norm_eq_of_mem_sphere p.2]

private theorem norm_fst_sphereProdFstLeInv (p : closedBall (0 : F) 1 × sphere (0 : G) 1) :
    ‖(sphereProdFstLeInv p).fst‖ = normalizer ‖(p.1 : F)‖ * ‖(p.1 : F)‖ := by
  simp [sphereProdFstLeInv, norm_smul, (normalizer_pos _).le]

private theorem sphereProdFstLeInv_mem_sphere (p : closedBall (0 : F) 1 × sphere (0 : G) 1) :
    sphereProdFstLeInv p ∈ sphere (0 : WithLp 2 (F × G)) 1 := by
  rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    WithLp.prod_norm_sq_eq_of_L2, norm_fst_sphereProdFstLeInv, norm_snd_sphereProdFstLeInv]
  linear_combination normalizer_sq ‖(p.1 : F)‖

private theorem norm_fst_le_norm_snd_sphereProdFstLeInv
    (p : closedBall (0 : F) 1 × sphere (0 : G) 1) :
    ‖(sphereProdFstLeInv p).fst‖ ≤ ‖(sphereProdFstLeInv p).snd‖ := by
  rw [norm_fst_sphereProdFstLeInv, norm_snd_sphereProdFstLeInv]
  exact mul_le_of_le_one_right (normalizer_pos _).le (mem_closedBall_zero_iff.1 p.1.2)

variable (F G) in
/-- The piece `‖x.fst‖ ≤ ‖x.snd‖` of the unit sphere of `WithLp 2 (F × G)` is homeomorphic to the
product of the closed unit ball of `F` with the unit sphere of `G`, through
`x ↦ (x.fst / ‖x.snd‖, x.snd / ‖x.snd‖)`, with inverse `(u, v) ↦ (u, v) / √(1 + ‖u‖ ^ 2)`. -/
def sphereProdFstLeHomeomorph :
    {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).fst‖ ≤
        ‖(x : WithLp 2 (F × G)).snd‖} ≃ₜ
      closedBall (0 : F) 1 × sphere (0 : G) 1 where
  toFun x :=
    (⟨‖(x : WithLp 2 (F × G)).snd‖⁻¹ • (x : WithLp 2 (F × G)).fst, by
        have h := norm_snd_pos x.1.2 x.2
        rw [mem_closedBall_zero_iff, norm_smul, norm_inv, norm_norm, inv_mul_le_one₀ h]
        exact x.2⟩,
      ⟨‖(x : WithLp 2 (F × G)).snd‖⁻¹ • (x : WithLp 2 (F × G)).snd, by
        have h := norm_snd_pos x.1.2 x.2
        rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ h.ne']⟩)
  invFun p := ⟨⟨sphereProdFstLeInv p, sphereProdFstLeInv_mem_sphere p⟩,
    norm_fst_le_norm_snd_sphereProdFstLeInv p⟩
  left_inv x := by
    obtain ⟨⟨x, hx⟩, hle⟩ := x
    have h := norm_snd_pos hx hle
    have hsum := norm_fst_sq_add_norm_snd_sq_of_mem_sphere hx
    -- The normalizer of `x.fst / ‖x.snd‖` is `‖x.snd‖`, since `‖x.fst‖ ^ 2 + ‖x.snd‖ ^ 2 = 1`.
    have hn : normalizer ‖‖x.snd‖⁻¹ • x.fst‖ = ‖x.snd‖ := by
      have hsq : 1 + ‖‖x.snd‖⁻¹ • x.fst‖ ^ 2 = (‖x.snd‖⁻¹) ^ 2 := by
        rw [norm_smul, norm_inv, norm_norm]
        field_simp
        linarith
      rw [normalizer, hsq, Real.sqrt_sq (by positivity), inv_inv]
    ext : 2
    simp only [sphereProdFstLeInv, hn, smul_smul, mul_inv_cancel₀ h.ne', one_smul]
    exact WithLp.ofLp_injective 2 <| Prod.ext (by simp) (by simp)
  right_inv p := by
    obtain ⟨u, v⟩ := p
    have hn := normalizer_pos ‖(u : F)‖
    ext <;> simp only [norm_snd_sphereProdFstLeInv] <;>
      simp [sphereProdFstLeInv, smul_smul, inv_mul_cancel₀ hn.ne']
  continuous_toFun := by
    have hpos (x : {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).fst‖ ≤
        ‖(x : WithLp 2 (F × G)).snd‖}) : ‖(x : WithLp 2 (F × G)).snd‖ ≠ 0 :=
      (norm_snd_pos x.1.2 x.2).ne'
    have hc : Continuous fun x : {x : sphere (0 : WithLp 2 (F × G)) 1 |
        ‖(x : WithLp 2 (F × G)).fst‖ ≤ ‖(x : WithLp 2 (F × G)).snd‖} ↦
          ‖(x : WithLp 2 (F × G)).snd‖⁻¹ :=
      .inv₀ (by fun_prop) hpos
    exact .prodMk (.subtype_mk (hc.smul (by fun_prop)) _) (.subtype_mk (hc.smul (by fun_prop)) _)
  continuous_invFun := by
    have hc : Continuous fun p : closedBall (0 : F) 1 × sphere (0 : G) 1 ↦
        normalizer ‖(p.1 : F)‖ :=
      continuous_normalizer.comp (by fun_prop)
    refine .subtype_mk (.subtype_mk ?_ _) _
    exact (WithLp.prod_continuous_toLp 2 F G).comp
      (.prodMk (hc.smul (continuous_subtype_val.comp continuous_fst))
        (hc.smul (continuous_subtype_val.comp continuous_snd)))

@[simp]
theorem coe_sphereProdFstLeHomeomorph_apply_fst
    (x : {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).fst‖ ≤
        ‖(x : WithLp 2 (F × G)).snd‖}) :
    ((sphereProdFstLeHomeomorph F G x).1 : F) =
      ‖(x : WithLp 2 (F × G)).snd‖⁻¹ • (x : WithLp 2 (F × G)).fst :=
  (rfl)

@[simp]
theorem coe_sphereProdFstLeHomeomorph_apply_snd
    (x : {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).fst‖ ≤
        ‖(x : WithLp 2 (F × G)).snd‖}) :
    ((sphereProdFstLeHomeomorph F G x).2 : G) =
      ‖(x : WithLp 2 (F × G)).snd‖⁻¹ • (x : WithLp 2 (F × G)).snd :=
  (rfl)

@[simp]
theorem coe_sphereProdFstLeHomeomorph_symm_apply (p : closedBall (0 : F) 1 × sphere (0 : G) 1) :
    (((sphereProdFstLeHomeomorph F G).symm p : sphere (0 : WithLp 2 (F × G)) 1) :
        WithLp 2 (F × G)) =
      WithLp.toLp 2 ((√(1 + ‖(p.1 : F)‖ ^ 2))⁻¹ • (p.1 : F),
        (√(1 + ‖(p.1 : F)‖ ^ 2))⁻¹ • (p.2 : G)) :=
  (rfl)

/-- `TauCeti.sphereProdFstLeHomeomorph` carries the common frontier `‖x.fst‖ = ‖x.snd‖` onto
`sphere (0 : F) 1 × sphere (0 : G) 1`, the boundary of `closedBall (0 : F) 1 × sphere (0 : G) 1`. -/
theorem norm_sphereProdFstLeHomeomorph_fst_eq_one_iff
    (x : {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).fst‖ ≤
        ‖(x : WithLp 2 (F × G)).snd‖}) :
    ‖((sphereProdFstLeHomeomorph F G x).1 : F)‖ = 1 ↔
      ‖(x : WithLp 2 (F × G)).fst‖ = ‖(x : WithLp 2 (F × G)).snd‖ := by
  rw [coe_sphereProdFstLeHomeomorph_apply_fst, norm_smul, norm_inv, norm_norm,
    inv_mul_eq_one₀ (norm_snd_pos x.1.2 x.2).ne', eq_comm]

/-- The frontier of the piece `‖x.fst‖ ≤ ‖x.snd‖` of the unit sphere of `WithLp 2 (F × G)` is the
set where `‖x.fst‖ = ‖x.snd‖`. -/
theorem frontier_setOf_norm_fst_le_norm_snd :
    frontier {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).fst‖ ≤
        ‖(x : WithLp 2 (F × G)).snd‖} =
      {x : sphere (0 : WithLp 2 (F × G)) 1 |
        ‖(x : WithLp 2 (F × G)).fst‖ = ‖(x : WithLp 2 (F × G)).snd‖} := by
  refine (frontier_le_subset_eq (by fun_prop) (by fun_prop)).antisymm fun x (hx : _ = _) ↦ ?_
  rw [frontier_eq_closure_inter_closure]
  refine ⟨subset_closure hx.le, ?_⟩
  obtain ⟨x, hxs⟩ := x
  have hsnd : 0 < ‖x.snd‖ := norm_snd_pos hxs hx.le
  -- Lengthening the first component of `x` and normalizing leaves the piece.
  let w : ℝ → WithLp 2 (F × G) := fun t ↦ WithLp.toLp 2 ((1 + t) • x.fst, x.snd)
  have hw (t : ℝ) : 0 < ‖w t‖ := hsnd.trans_le (WithLp.norm_snd_le _ (w t))
  let γ : ℝ → sphere (0 : WithLp 2 (F × G)) 1 := fun t ↦ ⟨‖w t‖⁻¹ • w t, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hw t).ne']⟩
  have hγ : Continuous γ :=
    .subtype_mk (.smul (.inv₀ (by fun_prop) fun t ↦ (hw t).ne') (by fun_prop)) _
  have hγ₀ : γ 0 = ⟨x, hxs⟩ := by
    have hw₀ : w 0 = x := WithLp.ofLp_injective 2 <| Prod.ext (by simp [w]) (by simp [w])
    ext1
    simp [γ, hw₀, mem_sphere_zero_iff_norm.1 hxs]
  rw [← hγ₀]
  refine map_mem_closure hγ (by simp) (s := Ioi 0) fun t (ht : 0 < t) ↦ ?_
  simp only [γ, w, mem_compl_iff, mem_ofPred_eq, WithLp.smul_fst, WithLp.smul_snd,
    WithLp.toLp_fst, WithLp.toLp_snd, norm_smul, norm_inv, norm_norm, not_le]
  refine mul_lt_mul_of_pos_left ?_ (inv_pos.2 (hw t))
  rw [Real.norm_of_nonneg (by linarith), ← hx]
  exact lt_mul_left (hx ▸ hsnd) (by linarith)

/-! ### The second piece -/

variable (F G) in
/-- The piece `‖x.snd‖ ≤ ‖x.fst‖` of the unit sphere of `WithLp 2 (F × G)` is homeomorphic to the
product of the unit sphere of `F` with the closed unit ball of `G`, through
`x ↦ (x.fst / ‖x.fst‖, x.snd / ‖x.fst‖)`. -/
def sphereProdSndLeHomeomorph :
    {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).snd‖ ≤
        ‖(x : WithLp 2 (F × G)).fst‖} ≃ₜ
      sphere (0 : F) 1 × closedBall (0 : G) 1 :=
  (sphereProdComm.subtype fun x ↦ by simp [coe_sphereProdComm_apply]).trans <|
    (sphereProdFstLeHomeomorph G F).trans (Homeomorph.prodComm _ _)

/-- `TauCeti.sphereProdSndLeHomeomorph` is `TauCeti.sphereProdFstLeHomeomorph` after the coordinate
swap. Unfolding the definition directly leaves the domain of `TauCeti.sphereProdFstLeHomeomorph`
in the form produced by `Homeomorph.subtype`, on which `simp` does not apply the simp lemmas of
`TauCeti.sphereProdFstLeHomeomorph`; this lemma restates the composite with the domain written as
in those simp lemmas. -/
private theorem sphereProdSndLeHomeomorph_apply
    (x : {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).snd‖ ≤
        ‖(x : WithLp 2 (F × G)).fst‖}) :
    sphereProdSndLeHomeomorph F G x =
      (sphereProdFstLeHomeomorph G F ⟨sphereProdComm x.1, by
        simp only [mem_ofPred_eq, coe_sphereProdComm_apply, WithLp.toLp_fst, WithLp.toLp_snd]
        exact x.2⟩).swap :=
  rfl

/-- The inverse of `TauCeti.sphereProdSndLeHomeomorph` through the coordinate swap, for the same
reason as `TauCeti.sphereProdSndLeHomeomorph_apply`. -/
private theorem coe_sphereProdSndLeHomeomorph_symm_apply_eq
    (p : sphere (0 : F) 1 × closedBall (0 : G) 1) :
    ((sphereProdSndLeHomeomorph F G).symm p : sphere (0 : WithLp 2 (F × G)) 1) =
      sphereProdComm.symm ((sphereProdFstLeHomeomorph G F).symm p.swap) :=
  rfl

@[simp]
theorem coe_sphereProdSndLeHomeomorph_apply_fst
    (x : {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).snd‖ ≤
        ‖(x : WithLp 2 (F × G)).fst‖}) :
    ((sphereProdSndLeHomeomorph F G x).1 : F) =
      ‖(x : WithLp 2 (F × G)).fst‖⁻¹ • (x : WithLp 2 (F × G)).fst := by
  simp [sphereProdSndLeHomeomorph_apply, coe_sphereProdComm_apply]

@[simp]
theorem coe_sphereProdSndLeHomeomorph_apply_snd
    (x : {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).snd‖ ≤
        ‖(x : WithLp 2 (F × G)).fst‖}) :
    ((sphereProdSndLeHomeomorph F G x).2 : G) =
      ‖(x : WithLp 2 (F × G)).fst‖⁻¹ • (x : WithLp 2 (F × G)).snd := by
  simp [sphereProdSndLeHomeomorph_apply, coe_sphereProdComm_apply]

@[simp]
theorem coe_sphereProdSndLeHomeomorph_symm_apply (p : sphere (0 : F) 1 × closedBall (0 : G) 1) :
    (((sphereProdSndLeHomeomorph F G).symm p : sphere (0 : WithLp 2 (F × G)) 1) :
        WithLp 2 (F × G)) =
      WithLp.toLp 2 ((√(1 + ‖(p.2 : G)‖ ^ 2))⁻¹ • (p.1 : F),
        (√(1 + ‖(p.2 : G)‖ ^ 2))⁻¹ • (p.2 : G)) := by
  simp [coe_sphereProdSndLeHomeomorph_symm_apply_eq, coe_sphereProdComm_symm_apply]

/-- `TauCeti.sphereProdSndLeHomeomorph` carries the common frontier `‖x.fst‖ = ‖x.snd‖` onto
`sphere (0 : F) 1 × sphere (0 : G) 1`, the boundary of `sphere (0 : F) 1 × closedBall (0 : G) 1`. -/
theorem norm_sphereProdSndLeHomeomorph_snd_eq_one_iff
    (x : {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).snd‖ ≤
        ‖(x : WithLp 2 (F × G)).fst‖}) :
    ‖((sphereProdSndLeHomeomorph F G x).2 : G)‖ = 1 ↔
      ‖(x : WithLp 2 (F × G)).fst‖ = ‖(x : WithLp 2 (F × G)).snd‖ := by
  rw [sphereProdSndLeHomeomorph_apply, Prod.snd_swap,
    norm_sphereProdFstLeHomeomorph_fst_eq_one_iff]
  simp [coe_sphereProdComm_apply, eq_comm]

/-- The frontier of the piece `‖x.snd‖ ≤ ‖x.fst‖` of the unit sphere of `WithLp 2 (F × G)` is the
set where `‖x.fst‖ = ‖x.snd‖`. -/
theorem frontier_setOf_norm_snd_le_norm_fst :
    frontier {x : sphere (0 : WithLp 2 (F × G)) 1 | ‖(x : WithLp 2 (F × G)).snd‖ ≤
        ‖(x : WithLp 2 (F × G)).fst‖} =
      {x : sphere (0 : WithLp 2 (F × G)) 1 |
        ‖(x : WithLp 2 (F × G)).fst‖ = ‖(x : WithLp 2 (F × G)).snd‖} := by
  have h := (sphereProdComm (F := F) (G := G)).preimage_frontier
    {x | ‖(x : WithLp 2 (G × F)).fst‖ ≤ ‖(x : WithLp 2 (G × F)).snd‖}
  rw [frontier_setOf_norm_fst_le_norm_snd] at h
  ext x
  exact Iff.symm (by simpa [coe_sphereProdComm_apply, eq_comm] using congrArg (x ∈ ·) h)

end TauCeti
