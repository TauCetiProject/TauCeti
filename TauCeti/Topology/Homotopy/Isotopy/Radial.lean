/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import Mathlib.Topology.Order.ProjIcc
public import TauCeti.Topology.Homotopy.Isotopy.Basic

/-!
# Absorbing an isotopy of the boundary into a radial collar

Let `E` be a real normed space, `S ⊆ E` its unit sphere and `D` its closed unit ball, and let `Z`
be any topological space. An ambient isotopy `Φ` of the boundary `S × Z` of `D × Z` extends to a
homeomorphism of `D × Z` which is the identity on the inner ball `‖x‖ ≤ 1 / 2` and is the final
homeomorphism `Φ₁` of the isotopy on the boundary. The radial coordinate `‖x‖ ∈ [1 / 2, 1]` serves
as the time of the isotopy: in polar coordinates `x = r • u`,

`(r • u, z) ↦ (r • Φ_t (u, z).1, Φ_t (u, z).2)` with `t = 2 r - 1` clamped to `[0, 1]`.

So the boundary homeomorphisms of `D × Z` that extend over `D × Z` are closed under composition
with homeomorphisms isotopic to the identity. This is the step of the classical proof that a
gluing along the boundary depends only on the isotopy class of the gluing map, in which the
isotopy is absorbed into a collar of the boundary (Rolfsen, *Knots and Links*, Section 9F, for
Dehn fillings, where `D × Z = D² × S¹` is the filling solid torus; with `Z = S^(q-1)` it is the
handle `D^(k+1) × S^(q-1)` of surgery on a framed sphere).

The homeomorphism is first built on all of `E × Z`, where it preserves the norm of the first
coordinate, and then restricted to `D × Z`.

## Main definitions

* `TauCeti.AmbientIsotopy.radialHomeomorph`: the homeomorphism of `E × Z` running the ambient
  isotopy `Φ` of `S × Z` along the radial coordinate.
* `TauCeti.AmbientIsotopy.closedBallProdHomeomorph`: its restriction to `D × Z`.

## Main results

* `TauCeti.AmbientIsotopy.radialHomeomorph_smul`: the formula in polar coordinates.
* `TauCeti.AmbientIsotopy.norm_fst_radialHomeomorph`: the norm of the first coordinate is
  preserved.
* `TauCeti.AmbientIsotopy.radialHomeomorph_of_norm_le`: the identity on `‖x‖ ≤ 1 / 2`.
* `TauCeti.AmbientIsotopy.radialHomeomorph_smul_of_one_le`: the final homeomorphism of `Φ`,
  rescaled, on `‖x‖ ≥ 1`.
* `TauCeti.AmbientIsotopy.closedBallProdHomeomorph_inclusion`: on the boundary `S × Z`, the
  restriction to `D × Z` is the final homeomorphism of `Φ`.

## References

* D. Rolfsen, *Knots and Links*, Publish or Perish (1976), Section 9F (the result of a Dehn
  filling depends only on the isotopy class of the gluing).
-/

public section

noncomputable section

namespace TauCeti

open Metric Set Topology Filter unitInterval

namespace AmbientIsotopy

variable {E Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace Z]

/-- The direction `‖x‖⁻¹ • x` of a nonzero vector, as a point of the unit sphere: the angular
part of the polar coordinates `homeomorphUnitSphereProd`. -/
private def direction (x : E) (hx : x ≠ 0) : sphere (0 : E) 1 :=
  (homeomorphUnitSphereProd E ⟨x, hx⟩).1

/-- The time at which the isotopy runs on the sphere of radius `r`: `0` up to `r = 1 / 2`, then
linear, reaching `1` at `r = 1`. -/
private def collarTime (r : ℝ) : I := projIcc 0 1 zero_le_one (2 * r - 1)

private theorem collarTime_of_le {r : ℝ} (hr : r ≤ 1 / 2) : collarTime r = 0 :=
  projIcc_of_le_left _ (by linarith)

private theorem collarTime_of_one_le {r : ℝ} (hr : 1 ≤ r) : collarTime r = 1 :=
  projIcc_of_right_le _ (by linarith)

private theorem direction_smul (u : sphere (0 : E) 1) {r : ℝ} (hr : 0 < r)
    (h : r • (u : E) ≠ 0) : direction (r • (u : E)) h = u := by
  ext
  simp [direction, norm_smul, abs_of_pos hr, smul_smul, inv_mul_cancel₀ hr.ne']

private theorem norm_smul_direction (x : E) (hx : x ≠ 0) : ‖x‖ • (direction x hx : E) = x := by
  simp [direction, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx)]

open scoped Classical in
/-- The map underlying `radialHomeomorph`, for an arbitrary ambient isotopy `Ψ`. -/
private def radialMap (Ψ : AmbientIsotopy (sphere (0 : E) 1 × Z)) (p : E × Z) : E × Z :=
  if hp : p.1 = 0 then p else
    (‖p.1‖ • ((Ψ.toContinuousMap (collarTime ‖p.1‖, (direction p.1 hp, p.2))).1 : E),
      (Ψ.toContinuousMap (collarTime ‖p.1‖, (direction p.1 hp, p.2))).2)

private theorem radialMap_of_ne_zero (Ψ : AmbientIsotopy (sphere (0 : E) 1 × Z)) {p : E × Z}
    (hp : p.1 ≠ 0) :
    radialMap Ψ p =
      (‖p.1‖ • ((Ψ.toContinuousMap (collarTime ‖p.1‖, (direction p.1 hp, p.2))).1 : E),
        (Ψ.toContinuousMap (collarTime ‖p.1‖, (direction p.1 hp, p.2))).2) := by
  simp only [radialMap, hp, ↓reduceDIte]

private theorem radialMap_smul (Ψ : AmbientIsotopy (sphere (0 : E) 1 × Z))
    (u : sphere (0 : E) 1) {r : ℝ} (hr : 0 < r) (z : Z) :
    radialMap Ψ (r • (u : E), z) =
      (r • ((Ψ.toContinuousMap (collarTime r, (u, z))).1 : E),
        (Ψ.toContinuousMap (collarTime r, (u, z))).2) := by
  have hu : ‖(u : E)‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have h : r • (u : E) ≠ 0 := by
    rw [← norm_ne_zero_iff, norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le]
    exact hr.ne'
  have hn : ‖r • (u : E)‖ = r := by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le]
  rw [radialMap_of_ne_zero Ψ h]
  simp only [direction_smul u hr h, hn]

private theorem norm_fst_radialMap (Ψ : AmbientIsotopy (sphere (0 : E) 1 × Z)) (p : E × Z) :
    ‖(radialMap Ψ p).1‖ = ‖p.1‖ := by
  by_cases hp : p.1 = 0
  · simp [radialMap, hp]
  · rw [radialMap_of_ne_zero Ψ hp, norm_smul, norm_norm,
      mem_sphere_zero_iff_norm.mp (Subtype.prop _), mul_one]

/-- `radialMap Ψ'` undoes `radialMap Ψ` when every time slice of `Ψ'` undoes that of `Ψ`. -/
private theorem radialMap_radialMap (Ψ Ψ' : AmbientIsotopy (sphere (0 : E) 1 × Z))
    (h : ∀ t y, Ψ'.toContinuousMap (t, Ψ.toContinuousMap (t, y)) = y) (p : E × Z) :
    radialMap Ψ' (radialMap Ψ p) = p := by
  by_cases hp : p.1 = 0
  · simp [radialMap, hp]
  · have hr : 0 < ‖p.1‖ := norm_pos_iff.mpr hp
    rw [radialMap_of_ne_zero Ψ hp, radialMap_smul Ψ' _ hr, h, norm_smul_direction]

/-- On the inner ball `‖x‖ ≤ 1 / 2` the radial map is the identity. -/
private theorem radialMap_of_norm_le (Ψ : AmbientIsotopy (sphere (0 : E) 1 × Z)) {p : E × Z}
    (hp : ‖p.1‖ ≤ 1 / 2) : radialMap Ψ p = p := by
  by_cases h0 : p.1 = 0
  · simp [radialMap, h0]
  · rw [radialMap_of_ne_zero Ψ h0, collarTime_of_le hp, map_zero_left, norm_smul_direction]

private theorem continuous_radialMap (Ψ : AmbientIsotopy (sphere (0 : E) 1 × Z)) :
    Continuous (radialMap Ψ) := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  by_cases hp : p.1 = 0
  · -- Near the core the map is the identity.
    have hU : {q : E × Z | ‖q.1‖ < 1 / 2} ∈ 𝓝 p :=
      (isOpen_lt (by fun_prop) continuous_const).mem_nhds (by simp [hp])
    exact continuousAt_id.congr
      (Filter.eventuallyEq_of_mem hU fun q hq => (radialMap_of_norm_le Ψ (le_of_lt hq)).symm)
  · -- Away from the core the map is given by a formula, read on the open set `x ≠ 0`.
    let e : {x : E // x ≠ 0} × Z → E × Z := Prod.map Subtype.val id
    have he : IsOpenEmbedding e :=
      (isOpen_ne.isOpenEmbedding_subtypeVal).prodMap IsOpenEmbedding.id
    have hdir : Continuous fun x : {x : E // x ≠ 0} => direction x.1 x.2 :=
      continuous_fst.comp (homeomorphUnitSphereProd E).continuous
    have hcomp : radialMap Ψ ∘ e = fun q =>
        (‖(q.1 : E)‖ • ((Ψ.toContinuousMap (collarTime ‖(q.1 : E)‖,
          (direction q.1.1 q.1.2, q.2))).1 : E),
        (Ψ.toContinuousMap (collarTime ‖(q.1 : E)‖, (direction q.1.1 q.1.2, q.2))).2) := by
      funext q
      exact radialMap_of_ne_zero Ψ q.1.2
    have hcont : Continuous (radialMap Ψ ∘ e) := by
      rw [hcomp]
      have ht : Continuous fun q : {x : E // x ≠ 0} × Z => collarTime ‖(q.1 : E)‖ :=
        continuous_projIcc.comp (by fun_prop)
      have hΨ : Continuous fun q : {x : E // x ≠ 0} × Z =>
          Ψ.toContinuousMap (collarTime ‖(q.1 : E)‖, (direction q.1.1 q.1.2, q.2)) :=
        Ψ.toContinuousMap.continuous.comp (ht.prodMk ((hdir.comp continuous_fst).prodMk
          continuous_snd))
      exact ((by fun_prop : Continuous fun q : {x : E // x ≠ 0} × Z => ‖(q.1 : E)‖).smul
        (continuous_subtype_val.comp (continuous_fst.comp hΨ))).prodMk (continuous_snd.comp hΨ)
    have := he.continuousAt_iff (g := radialMap Ψ) (x := (⟨p.1, hp⟩, p.2))
    exact this.mp hcont.continuousAt

/-- The **radial extension** of an ambient isotopy `Φ` of `S × Z`, `S` the unit sphere of `E`:
the homeomorphism `(r • u, z) ↦ (r • Φ_t (u, z).1, Φ_t (u, z).2)` of `E × Z`, for `u ∈ S` and
`r > 0`, where the time `t = 2 r - 1` is clamped to `[0, 1]`. It fixes `{0} × Z`, is the identity
on `‖x‖ ≤ 1 / 2` (`radialHomeomorph_of_norm_le`), preserves `‖x‖`
(`norm_fst_radialHomeomorph`) and on `‖x‖ ≥ 1` is the final homeomorphism of `Φ`, rescaled
(`radialHomeomorph_smul_of_one_le`). -/
def radialHomeomorph (Φ : AmbientIsotopy (sphere (0 : E) 1 × Z)) : E × Z ≃ₜ E × Z where
  toFun := radialMap Φ
  invFun := radialMap Φ.symm
  left_inv := radialMap_radialMap Φ Φ.symm Φ.symm_apply_apply_slice
  right_inv := radialMap_radialMap Φ.symm Φ Φ.apply_symm_apply_slice
  continuous_toFun := continuous_radialMap Φ
  continuous_invFun := continuous_radialMap Φ.symm

variable (Φ : AmbientIsotopy (sphere (0 : E) 1 × Z))

/-- The radial extension in polar coordinates `x = r • u`, `u` in the unit sphere and `r > 0`:
the isotopy is run on the sphere of radius `r` at the time `2 r - 1`, clamped to `[0, 1]`. -/
theorem radialHomeomorph_smul (u : sphere (0 : E) 1) {r : ℝ} (hr : 0 < r) (z : Z) :
    Φ.radialHomeomorph (r • (u : E), z) =
      (r • ((Φ.toContinuousMap (projIcc 0 1 zero_le_one (2 * r - 1), (u, z))).1 : E),
        (Φ.toContinuousMap (projIcc 0 1 zero_le_one (2 * r - 1), (u, z))).2) :=
  radialMap_smul Φ u hr z

/-- The inverse of the radial extension of `Φ` is the radial extension of the inverse isotopy. -/
theorem symm_radialHomeomorph : Φ.radialHomeomorph.symm = Φ.symm.radialHomeomorph :=
  Homeomorph.ext fun p => Φ.radialHomeomorph.symm_apply_eq.mpr
    (radialMap_radialMap Φ.symm Φ Φ.apply_symm_apply_slice p).symm

/-- The radial extension preserves the norm of the first coordinate. -/
@[simp]
theorem norm_fst_radialHomeomorph (p : E × Z) : ‖(Φ.radialHomeomorph p).1‖ = ‖p.1‖ :=
  norm_fst_radialMap Φ p

/-- The radial extension is the identity on the inner ball `‖x‖ ≤ 1 / 2`. -/
theorem radialHomeomorph_of_norm_le {p : E × Z} (hp : ‖p.1‖ ≤ 1 / 2) :
    Φ.radialHomeomorph p = p :=
  radialMap_of_norm_le Φ hp

/-- Outside the open unit ball the radial extension is the final homeomorphism of `Φ`, rescaled:
`(r • u, z) ↦ (r • Φ₁ (u, z).1, Φ₁ (u, z).2)` for `r ≥ 1`. -/
theorem radialHomeomorph_smul_of_one_le (u : sphere (0 : E) 1) {r : ℝ} (hr : 1 ≤ r) (z : Z) :
    Φ.radialHomeomorph (r • (u : E), z) =
      (r • ((Φ.final (u, z)).1 : E), (Φ.final (u, z)).2) := by
  rw [radialHomeomorph_smul Φ u (zero_lt_one.trans_le hr), ← collarTime,
    collarTime_of_one_le hr, final_apply]

/-- On the unit sphere the radial extension is the final homeomorphism of `Φ`. -/
theorem radialHomeomorph_coe_sphere (q : sphere (0 : E) 1 × Z) :
    Φ.radialHomeomorph ((q.1 : E), q.2) = (((Φ.final q).1 : E), (Φ.final q).2) := by
  simpa using Φ.radialHomeomorph_smul_of_one_le q.1 le_rfl q.2

/-- The **extension of an ambient isotopy of `S × Z` over `D × Z`**, `S` and `D` the unit sphere
and closed unit ball of `E`: the restriction of `radialHomeomorph` to `D × Z`. It is the identity
on `‖x‖ ≤ 1 / 2` (`closedBallProdHomeomorph_of_norm_le`) and the final homeomorphism of `Φ` on the
boundary `S × Z` (`closedBallProdHomeomorph_inclusion`). -/
def closedBallProdHomeomorph : closedBall (0 : E) 1 × Z ≃ₜ closedBall (0 : E) 1 × Z where
  toFun p := (⟨(Φ.radialHomeomorph ((p.1 : E), p.2)).1, by
      simpa only [mem_closedBall_zero_iff, norm_fst_radialHomeomorph] using p.1.2⟩,
    (Φ.radialHomeomorph ((p.1 : E), p.2)).2)
  invFun p := (⟨(Φ.radialHomeomorph.symm ((p.1 : E), p.2)).1, by
      simpa only [mem_closedBall_zero_iff, symm_radialHomeomorph, norm_fst_radialHomeomorph]
        using p.1.2⟩,
    (Φ.radialHomeomorph.symm ((p.1 : E), p.2)).2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

@[simp]
theorem coe_closedBallProdHomeomorph_fst (p : closedBall (0 : E) 1 × Z) :
    ((Φ.closedBallProdHomeomorph p).1 : E) = (Φ.radialHomeomorph ((p.1 : E), p.2)).1 :=
  (rfl)

@[simp]
theorem closedBallProdHomeomorph_snd (p : closedBall (0 : E) 1 × Z) :
    (Φ.closedBallProdHomeomorph p).2 = (Φ.radialHomeomorph ((p.1 : E), p.2)).2 :=
  (rfl)

/-- The inverse of the extension of `Φ` is the extension of the inverse isotopy. -/
theorem symm_closedBallProdHomeomorph :
    Φ.closedBallProdHomeomorph.symm = Φ.symm.closedBallProdHomeomorph :=
  Homeomorph.ext fun p => Φ.closedBallProdHomeomorph.symm_apply_eq.mpr <| by
    ext <;> simp [← symm_radialHomeomorph]

/-- The extension of `Φ` over the closed unit ball is the identity on `‖x‖ ≤ 1 / 2`. -/
theorem closedBallProdHomeomorph_of_norm_le {p : closedBall (0 : E) 1 × Z}
    (hp : ‖(p.1 : E)‖ ≤ 1 / 2) : Φ.closedBallProdHomeomorph p = p := by
  have h := Φ.radialHomeomorph_of_norm_le (p := ((p.1 : E), p.2)) hp
  ext
  · simp [h]
  · simp [h]

/-- On the boundary `S × Z` of `D × Z` the extension of `Φ` is the final homeomorphism of `Φ`. -/
@[simp]
theorem closedBallProdHomeomorph_inclusion (q : sphere (0 : E) 1 × Z) :
    Φ.closedBallProdHomeomorph (inclusion sphere_subset_closedBall q.1, q.2) =
      (inclusion sphere_subset_closedBall (Φ.final q).1, (Φ.final q).2) := by
  have h := Φ.radialHomeomorph_coe_sphere q
  ext
  · simp [h]
  · simp [h]

end AmbientIsotopy

end TauCeti
