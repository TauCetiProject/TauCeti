/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.ChartedSpace
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Edges

import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Rotations of the edges at the black and white points of a filled cover

Let `p : E → ℂ ∖ {0, 1}` be a covering map whose fibre over `1/2` is numbered by `ν`, with
monodromy triple `(σ0, σ1, σinf)`. Its filled cover carries the embedded dessin: the edge of the
sheet `k` is the component of `p ⁻¹' (0, 1)` through the point numbered `k`
(`TauCeti.FilledCover.edge`), its black end is an added point over `0` and its white end an added
point over `1`. This file shows that, read in the holomorphic chart at a black point, turning
counterclockwise by one step advances each edge there by `σ0`, and likewise at a white point by
`σ1`.

Precisely, let `P` be the added point over `0` of a component of local degree `e`. In the filling
chart of that component, under which `p` becomes `w ↦ w ^ e` in the coordinate `z ↦ 2 * z`, the
preimage of `(0, 1)` consists of the `e` radial segments of arguments `2πj/e`. Rotation
counterclockwise by `2π/e`, that is multiplication by `exp (2πi/e)`, carries the part of the edge of
the sheet `k` near `P` onto the part of the edge of the sheet `σ0 k`
(`TauCeti.FilledCover.incl_chart_overZero_mem_edge_iff`). The same holds over `1`, in the coordinate
`z ↦ 2 * (1 - z)`, with `σ1` (`TauCeti.FilledCover.incl_chart_overOne_mem_edge_iff`). These filling
charts are the holomorphic charts of the filled cover at its added points
(`TauCeti.FilledCover.chartedSpace`), so the statements also read in the complex structure of the
filled cover (`TauCeti.FilledCover.chartAt_center_overZero_symm_mul_mem_edge_iff` and
`TauCeti.FilledCover.chartAt_center_overOne_symm_mul_mem_edge_iff`).

The reason is that the counterclockwise circle `δZero` of radius `1/4` about `0`, transported to
`1/2` along the segment, is the peripheral loop at `0`, whose monodromy is `σ0`; in the filling
chart its lift from a point `v` with `v ^ e = 1/2` is the arc `t ↦ exp (2πit/e) * v`, which ends at
`exp (2πi/e) * v`. Radial motion in the chart stays over `(0, 1)`, so it does not change the edge.

## Main results

* `TauCeti.FilledCover.incl_chart_overZero_mem_edge_iff`,
  `TauCeti.FilledCover.incl_chart_overOne_mem_edge_iff`: in the filling chart of a component over
  `0`, respectively `1`, of local degree `e`, multiplication by `exp (2πi/e)` carries the edge of
  the sheet `k` to the edge of the sheet `σ0 k`, respectively `σ1 k`.
* `TauCeti.FilledCover.chartAt_center_overZero_symm_mul_mem_edge_iff`,
  `TauCeti.FilledCover.chartAt_center_overOne_symm_mul_mem_edge_iff`: the same statements in the
  holomorphic chart of the filled cover at the added point.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  Chapter 4 (the dessin of a Belyi function, and the monodromy permutations around `0` and `1` as
  the rotations of its edges around the black and white vertices).
* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, Chapter 1 (the monodromy of a cover of the sphere
  branched over three points, read off its embedded graph).
-/

public section

noncomputable section

namespace TauCeti

open Complex Equiv Equiv.Perm FilledPoint Function Metric Set ThricePuncturedSphere Topology

open scoped Real

namespace FilledCover

/-- The punctured unit disc of `ℂ`, as a subtype. -/
local notation "𝔻*" => Set.Elem (ball (0 : ℂ) 1 \ {0})

variable {E : Type*} [TopologicalSpace E] {p : E → ThricePuncturedSphere} {n : ℕ}

/-- Multiplication by a complex number of norm `1` maps the punctured unit disc to itself. -/
private theorem mul_mem_puncturedDisc_of_norm_eq_one {ζ : ℂ} (hζ : ‖ζ‖ = 1) (w : 𝔻*) :
    ζ * w ∈ ball (0 : ℂ) 1 \ {0} := by
  refine ⟨mem_ball_zero_iff.2 ?_, mul_ne_zero (norm_ne_zero_iff.1 (by simp [hζ])) w.2.2⟩
  rw [norm_mul, hζ, one_mul]
  exact mem_ball_zero_iff.1 w.2.1

/-- Rotation by `exp (2πi/e)` does not change `e`-th powers. -/
private theorem exp_mul_pow {e : ℕ} (he : e ≠ 0) (z : ℂ) :
    (exp (2 * π * I / e) * z) ^ e = z ^ e := by
  rw [mul_pow, (isPrimitiveRoot_exp e he).pow_eq_one, one_mul]

/-! ### The local argument at a puncture -/

section Local

/-! Throughout, `φ` is a chart of a component of `p ⁻¹' D_q*` in which `p` is `w ↦ w ^ e` in the
coordinate of `D_q*`, the segment `(0, 1)` is the positive real axis in that coordinate, `y` is the
point with coordinate `1/2`, joined to `1/2` by a path `α` along `(0, 1)`, `δ` is the
counterclockwise circle of radius `1/2` in the coordinate, based at `y`, and `σ` is the monodromy
of the transport `g` of `δ` along `α`. -/

variable (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n) {q : Puncture} {φ : 𝔻* → E}
  {e : ℕ} {y : q.neighborhood} {α : Path basePt (y : ThricePuncturedSphere)} {δ : Path y y}
  {σ : Perm (Fin n)} {g : FundamentalGroup ThricePuncturedSphere basePt}
  (hφ : Continuous φ) (he : e ≠ 0)
  (hφq : ∀ w, ∃ hw : p (φ w) ∈ q.neighborhood, (q.coord ⟨p (φ w), hw⟩ : ℂ) = (w : ℂ) ^ e)
  (hseg : ∀ z (hz : z ∈ q.neighborhood),
    z ∈ unitSegment ↔ (q.coord ⟨z, hz⟩ : ℂ).im = 0 ∧ 0 < (q.coord ⟨z, hz⟩ : ℂ).re)
  (hy : (q.coord y : ℂ) = 1 / 2)
  (hα : ∀ m (hm : (hp.monodromy (.mk α) (ν.symm m) : E) ∈ p ⁻¹' unitSegment),
    hp.finEquivConnectedComponentsUnitSegment ν m = ConnectedComponents.mk ⟨_, hm⟩)
  (hδ : ∀ t, (q.coord (δ t) : ℂ) = circleMap 0 (1 / 2) (2 * π * t))
  (hσ : σ = ν.permCongr (hp.monodromyPerm basePt g))
  (hg : (FundamentalGroup.fundamentalGroupMulEquivOfPath α).symm
    (FundamentalGroup.map ⟨Subtype.val, continuous_subtype_val⟩ y
      (FundamentalGroup.fromPath (.mk δ))) = g)

include hσ hg in
/-- If `σ` is the monodromy of the transport along `α` of the loop `δ` at `y`, then the lift of `δ`
from the endpoint of the lift of `α` from the sheet `m` ends at the endpoint of the lift of `α` from
the sheet `σ m`. -/
private theorem monodromy_δ_monodromy_α (m : Fin n) :
    hp.monodromy (.mk (δ.map continuous_subtype_val)) (hp.monodromy (.mk α) (ν.symm m)) =
      hp.monodromy (.mk α) (ν.symm (σ m)) := by
  subst hσ hg
  -- Lifting the transport of `δ` and then `α` is lifting `α` and then `δ`.
  have h := hp.monodromy_fundamentalGroupMulEquivOfPath_symm_apply α
    (FundamentalGroup.fromPath (.mk (δ.map continuous_subtype_val))) (ν.symm m)
  rw [eq_symm_apply, coveringFiberEquiv_apply] at h
  rw [FundamentalGroup.map_fromPath]
  simpa only [permCongr_apply, symm_apply_apply, IsCoveringMap.coe_monodromyPerm] using h.symm

include hp hφq hy in
/-- A point of the chart whose `e`-th power is `1/2` lies over `y`, so it is the endpoint of the
lift of `α` from some sheet. -/
private theorem exists_eq_monodromy_α {v : 𝔻*} (hv : (v : ℂ) ^ e = 1 / 2) :
    ∃ m, φ v = hp.monodromy (.mk α) (ν.symm m) := by
  obtain ⟨hv', h⟩ := hφq v
  have hpv : p (φ v) = y :=
    congrArg Subtype.val (q.coord.injective (Subtype.ext (h.trans (hv.trans hy.symm))))
  refine ⟨ν ((coveringFiberEquiv hp (.mk α)).symm ⟨φ v, hpv⟩), ?_⟩
  rw [symm_apply_apply, ← coveringFiberEquiv_apply, apply_symm_apply]

include hp hφ he hφq hδ in
/-- **The monodromy of the local loop is a rotation.** In a chart in which `p` is `w ↦ w ^ e` in
the coordinate of `D_q*`, and in which the loop `δ` is the counterclockwise circle of radius `1/2`,
the lift of `δ` from a point `v` with `v ^ e = 1/2` ends at `exp (2πi/e) * v`. -/
private theorem monodromy_δ_eq {v v' : 𝔻*}
    (hv : (v : ℂ) ^ e = 1 / 2) (hv' : (v' : ℂ) = exp (2 * π * I / e) * v)
    {x : p ⁻¹' {(y : ThricePuncturedSphere)}} (hx : φ v = x) :
    (hp.monodromy (.mk (δ.map continuous_subtype_val)) x : E) = φ v' := by
  have hmem (t : unitInterval) : exp (2 * π * I * t / e) * v ∈ ball (0 : ℂ) 1 \ {0} := by
    refine mul_mem_puncturedDisc_of_norm_eq_one ?_ v
    rw [show 2 * π * I * t / e = ((2 * π * t / e : ℝ) : ℂ) * I by push_cast; ring]
    exact norm_exp_ofReal_mul_I _
  -- The arc `t ↦ exp (2πit/e) * v` lifts `δ`.
  let Γ : C(unitInterval, E) := ⟨fun t ↦ φ ⟨_, hmem t⟩,
    hφ.comp (Continuous.subtype_mk (by fun_prop) _)⟩
  have hΓ : p ∘ Γ = δ.map continuous_subtype_val := by
    funext t
    obtain ⟨ht, h⟩ := hφq ⟨_, hmem t⟩
    refine congrArg Subtype.val (q.coord.injective (Subtype.ext (h.trans ?_)))
    rw [hδ t, mul_pow, ← exp_nat_mul, hv, circleMap, zero_add]
    have he' : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.2 he
    have harg : (e : ℂ) * (2 * π * I * t / e) = (2 * π * t : ℝ) * I := by
      field_simp
      push_cast
      ring
    rw [harg]
    push_cast
    ring
  rw [hp.monodromy_eq_apply_one hΓ (by simp [Γ, hx])]
  exact congrArg φ (Subtype.ext (by simp [hv']))

include hφ he hφq hseg hy hα hδ hσ hg in
/-- **Rotation carries the edge of `k` to the edge of `σ k`.** In a chart in which `p` is
`w ↦ w ^ e` in the coordinate of `D_q*`, where `(0, 1)` is the positive real axis, the loop `δ` is
the counterclockwise circle of radius `1/2` based at `1/2`, the path `α` runs along `(0, 1)`, and
`σ` is the monodromy of the transport `g` of `δ` along `α`, multiplication by `exp (2πi/e)`
carries a point of the edge of the sheet `k` to a point of the edge of the sheet `σ k`. -/
private theorem exists_mk_eq_σ
    {w w' : 𝔻*} (hw' : (w' : ℂ) = exp (2 * π * I / e) * w) (hw : p (φ w) ∈ unitSegment)
    {k : Fin n}
    (hk : ConnectedComponents.mk ⟨φ w, hw⟩ = hp.finEquivConnectedComponentsUnitSegment ν k) :
    ∃ hw'' : p (φ w') ∈ unitSegment,
      ConnectedComponents.mk ⟨φ w', hw''⟩ = hp.finEquivConnectedComponentsUnitSegment ν (σ k) := by
  -- The label of a point `x` of the lift of `α` from the sheet `m` is `m`.
  have hlabel {m : Fin n} {x : E} (hx : x = hp.monodromy (.mk α) (ν.symm m))
      (hxseg : p x ∈ unitSegment) :
      ConnectedComponents.mk (⟨x, hxseg⟩ : p ⁻¹' unitSegment) =
        hp.finEquivConnectedComponentsUnitSegment ν m := by
    subst hx
    exact (hα m hxseg).symm
  -- Write `w ^ e = a` with `a > 0`, and scale `w` by `r > 0` with `r ^ e * a = 1/2`.
  have hwe := (mem_unitSegment_iff_of_coe_coord_eq_pow hφq hseg w).1 hw
  set a := ((w : ℂ) ^ e).re with ha
  have hwa : (w : ℂ) ^ e = a := Complex.ext (by simp [ha]) (by simp [hwe.1])
  set r : ℝ := (2 * a)⁻¹ ^ (e⁻¹ : ℝ)
  have ha2 : 0 < (2 * a)⁻¹ := inv_pos.2 (mul_pos two_pos hwe.2)
  have hr : 0 < r := Real.rpow_pos_of_pos ha2 _
  have hre : r ^ e = (2 * a)⁻¹ := Real.rpow_inv_natCast_pow ha2.le he
  have hrw (u : 𝔻*) (hu : (u : ℂ) ^ e = a) : ((r : ℂ) * u) ^ e = 1 / 2 := by
    rw [mul_pow, hu, ← ofReal_pow, hre]
    push_cast
    field_simp [ofReal_ne_zero.2 hwe.2.ne']
  have hmem (u : 𝔻*) (hu : (u : ℂ) ^ e = a) : (r : ℂ) * u ∈ ball (0 : ℂ) 1 \ {0} := by
    refine ⟨mem_ball_zero_iff.2 ?_, mul_ne_zero (ofReal_ne_zero.2 hr.ne') u.2.2⟩
    have h := congrArg norm (hrw u hu)
    rw [norm_pow] at h
    exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 (by rw [h]; norm_num)
  -- The rotated point also has `e`-th power `a`.
  have hw'a : (w' : ℂ) ^ e = a := by
    rw [hw', exp_mul_pow he, hwa]
  let v : 𝔻* := ⟨_, hmem w hwa⟩
  let v' : 𝔻* := ⟨_, hmem w' hw'a⟩
  -- The point `φ v` lies on the edge of `k` and over `y`, so it is the endpoint of the lift of `α`
  -- from the sheet `k`.
  obtain ⟨hvseg, hvk⟩ := exists_mk_eq_of_coe_eq_ofReal_mul hφ hφq hseg (w' := v) hr rfl hw
  obtain ⟨m, hm⟩ := exists_eq_monodromy_α hp ν hφq hy (α := α) (v := v) (hrw w hwa)
  obtain rfl : m = k := (hp.finEquivConnectedComponentsUnitSegment ν).injective <| by
    rw [← hlabel hm hvseg, hvk, hk]
  -- Its rotation `φ v'` is the endpoint of the lift of `α` from the sheet `σ m`.
  have hv' : φ v' = hp.monodromy (.mk α) (ν.symm (σ m)) := by
    rw [← monodromy_δ_monodromy_α hp ν hσ hg m]
    exact (monodromy_δ_eq hp hφ he hφq hδ (hrw w hwa) (by simp only [v, v', hw']; ring) hm).symm
  -- Radial motion from `w'` to `v'` stays on one edge.
  have hw'seg : p (φ w') ∈ unitSegment :=
    (mem_unitSegment_iff_of_coe_coord_eq_pow hφq hseg w').2 (by rw [hw'a]; simpa using hwe.2)
  obtain ⟨hv'seg, hv'w'⟩ := exists_mk_eq_of_coe_eq_ofReal_mul hφ hφq hseg (w' := v') hr rfl hw'seg
  exact ⟨hw'seg, by rw [← hv'w', hlabel hv' hv'seg]⟩

include hφ he hφq hseg hy hα hδ hσ hg in
/-- **Rotation matches the edge of `k` with the edge of `σ k`.** Multiplication by `exp (2πi/e)` in
the chart carries the points of the edge of the sheet `k` exactly to the points of the edge of the
sheet `σ k`. -/
private theorem exists_mk_eq_σ_iff {w w' : 𝔻*} (hw' : (w' : ℂ) = exp (2 * π * I / e) * w)
    (k : Fin n) :
    (∃ hw'' : p (φ w') ∈ unitSegment,
        ConnectedComponents.mk ⟨φ w', hw''⟩ = hp.finEquivConnectedComponentsUnitSegment ν (σ k)) ↔
      ∃ hw : p (φ w) ∈ unitSegment,
        ConnectedComponents.mk ⟨φ w, hw⟩ = hp.finEquivConnectedComponentsUnitSegment ν k := by
  refine ⟨fun ⟨hw'', hk⟩ ↦ ?_, fun ⟨hw, hk⟩ ↦
    exists_mk_eq_σ hp ν hφ he hφq hseg hy hα hδ hσ hg hw' hw hk⟩
  -- `w` and `w'` have the same `e`-th power, so `φ w` lies over `(0, 1)` as well.
  have hw : p (φ w) ∈ unitSegment := by
    rw [mem_unitSegment_iff_of_coe_coord_eq_pow hφq hseg, ← exp_mul_pow he, ← hw',
      ← mem_unitSegment_iff_of_coe_coord_eq_pow hφq hseg]
    exact hw''
  -- The edge of `φ w` is that of some sheet `m`, and rotation carries it to the edge of `σ m`.
  set m := (hp.finEquivConnectedComponentsUnitSegment ν).symm (ConnectedComponents.mk ⟨φ w, hw⟩)
  have hm : ConnectedComponents.mk ⟨φ w, hw⟩ = hp.finEquivConnectedComponentsUnitSegment ν m :=
    (apply_symm_apply _ _).symm
  obtain ⟨_, hσm⟩ := exists_mk_eq_σ hp ν hφ he hφq hseg hy hα hδ hσ hg hw' hw hm
  have hmk : m = k :=
    σ.injective ((hp.finEquivConnectedComponentsUnitSegment ν).injective (hσm.symm.trans hk))
  exact ⟨hw, hmk ▸ hm⟩

end Local

/-! ### The data at `0` and `1` -/

/-- The filling chart of an added point over `q` is a power map in the coordinate of `D_q*`. -/
private theorem exists_coe_coord_chart_eq_pow_of_eq (hp : IsCoveringMap p)
    {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀})) {i : FilledPoint p} {q : Puncture}
    (hq : (sigmaEquiv p i).1 = q) (w : 𝔻*) :
    ∃ hw : p (chart p i w) ∈ q.neighborhood, (q.coord ⟨_, hw⟩ : ℂ) = (w : ℂ) ^ degree p i := by
  subst hq
  obtain ⟨hw, -, h⟩ := exists_coe_coord_chart_eq_pow hp hfin i w
  exact ⟨hw, h⟩

/-! ### Rotations at the black and white points -/

/-- If multiplication by `ζ`, of norm `1`, in the filling chart of `i` carries the points of the
edge of `k` exactly to the points of the edge of `k'`, then so does multiplication by `ζ` in the
holomorphic chart of the filled cover at the added point of `i`. -/
private theorem chartAt_center_symm_mul_mem_edge_iff_of (hp : IsCoveringMap p)
    {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀})) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (i : FilledPoint p) {k k' : Fin n} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hrot : ∀ {w w' : 𝔻*}, (w' : ℂ) = ζ * w →
      (PunctureFilling.incl (chart p) (chart p i w') ∈ edge hp ν k' ↔
        PunctureFilling.incl (chart p) (chart p i w) ∈ edge hp ν k))
    {z : FilledCover p}
    (hz : z ∈
      (@chartAt ℂ _ _ _ (chartedSpace hp hfin) (PunctureFilling.center (chart p) i)).source) :
    letI := chartedSpace hp hfin
    (chartAt ℂ (PunctureFilling.center (chart p) i)).symm
        (ζ * chartAt ℂ (PunctureFilling.center (chart p) i) z) ∈ edge hp ν k' ↔
      z ∈ edge hp ν k := by
  let := chartedSpace hp hfin
  rw [chartAt_center_source] at hz
  obtain ⟨d, rfl⟩ := hz
  -- The centre of the chart lies on no edge.
  have hcenter (m : Fin n) : PunctureFilling.center (chart p) i ∉ edge hp ν m := by
    intro h
    obtain ⟨x, -, -, hx⟩ := (mem_edge_iff hp ν m _).1 h
    exact PunctureFilling.incl_ne_center x i hx
  rw [chartAt_center_apply_disc]
  by_cases hd : d = 0
  · subst hd
    have h0 : ζ * ((0 : ball (0 : ℂ) 1) : ℂ) = ((0 : ball (0 : ℂ) 1) : ℂ) := by simp
    rw [h0, chartAt_center_symm_apply, PunctureFilling.disc_zero]
    exact iff_of_false (hcenter k') (hcenter k)
  -- Off the centre, both points lie in `E`, on the filling chart.
  obtain ⟨w, rfl⟩ : ∃ w : 𝔻*, inclusion sdiff_subset w = d :=
    ⟨⟨d, d.2, fun h ↦ hd (Subtype.ext h)⟩, rfl⟩
  let w' : 𝔻* := ⟨_, mul_mem_puncturedDisc_of_norm_eq_one hζ w⟩
  have hw' : ζ * ((inclusion sdiff_subset w : ball (0 : ℂ) 1) : ℂ) =
      ((inclusion sdiff_subset w' : ball (0 : ℂ) 1) : ℂ) := by
    simp [w']
  rw [hw', chartAt_center_symm_apply, PunctureFilling.disc_inclusion,
    PunctureFilling.disc_inclusion]
  exact hrot rfl

/-- **The edges at a black point rotate by `σ0`.** Let `P` be the added point over `0` of a
component `b` of `p ⁻¹' D₀*`, of local degree `e`. In the filling chart of `b`, multiplication by
`exp (2πi/e)` carries the points of the edge of the sheet `k` exactly to the points of the edge of
the sheet `σ0 k`: turning counterclockwise by `2π/e` around `P` advances each edge at `P` by
`σ0`. -/
theorem incl_chart_overZero_mem_edge_iff (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero)) (k : Fin n) {w w' : 𝔻*}
    (hw' : (w' : ℂ) = exp (2 * π * I / degree p (overZero p b)) * w) :
    PunctureFilling.incl (chart p) (chart p (overZero p b) w') ∈
        edge hp ν ((hp.monodromyTriple ν).σ0 k) ↔
      PunctureFilling.incl (chart p) (chart p (overZero p b) w) ∈ edge hp ν k := by
  have hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  simp only [incl_mem_edge_iff]
  exact exists_mk_eq_σ_iff hp ν (q := .zero) (isOpenEmbedding_chart hp hfin _).continuous
    (degree_ne_zero hp hfin _)
    (exists_coe_coord_chart_eq_pow_of_eq hp hfin (q := .zero)
      (congrArg Sigma.fst (sigmaEquiv_overZero (p := p) b)))
    mem_unitSegment_iff_coord_zero (y := zeroBasePt)
    ((Puncture.coe_coord_zero zeroBasePt).trans (by rw [coe_zeroBasePt]; norm_num)) (α := αZero)
    (fun m _ ↦ hp.finEquivConnectedComponentsUnitSegment_eq_mk_monodromy_αZero ν m) (δ := δZero)
    (fun t ↦ (Puncture.coe_coord_zero (δZero t)).trans (by rw [coe_δZero]; simp [circleMap]; ring))
    (hp.monodromyTriple_σ0 ν) transport_δZero_eq_periph0 hw' k

/-- **The edges at a white point rotate by `σ1`.** Let `P` be the added point over `1` of a
component `b` of `p ⁻¹' D₁*`, of local degree `e`. In the filling chart of `b`, multiplication by
`exp (2πi/e)` carries the points of the edge of the sheet `k` exactly to the points of the edge of
the sheet `σ1 k`: turning counterclockwise by `2π/e` around `P` advances each edge at `P` by
`σ1`. -/
theorem incl_chart_overOne_mem_edge_iff (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne)) (k : Fin n) {w w' : 𝔻*}
    (hw' : (w' : ℂ) = exp (2 * π * I / degree p (overOne p b)) * w) :
    PunctureFilling.incl (chart p) (chart p (overOne p b) w') ∈
        edge hp ν ((hp.monodromyTriple ν).σ1 k) ↔
      PunctureFilling.incl (chart p) (chart p (overOne p b) w) ∈ edge hp ν k := by
  have hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  simp only [incl_mem_edge_iff]
  exact exists_mk_eq_σ_iff hp ν (q := .one) (isOpenEmbedding_chart hp hfin _).continuous
    (degree_ne_zero hp hfin _)
    (exists_coe_coord_chart_eq_pow_of_eq hp hfin (q := .one)
      (congrArg Sigma.fst (sigmaEquiv_overOne (p := p) b)))
    mem_unitSegment_iff_coord_one (y := oneBasePt)
    ((Puncture.coe_coord_one oneBasePt).trans (by rw [coe_oneBasePt]; norm_num)) (α := αOne)
    (fun m _ ↦ hp.finEquivConnectedComponentsUnitSegment_eq_mk_monodromy_αOne ν m) (δ := δOne)
    (fun t ↦ (Puncture.coe_coord_one (δOne t)).trans (by rw [coe_δOne]; simp [circleMap]; ring))
    (hp.monodromyTriple_σ1 ν) transport_δOne_eq_periph1 hw' k

/-- **The edges at a black point rotate by `σ0`, in the complex structure.** Let `P` be the added
point over `0` of a component `b` of `p ⁻¹' D₀*`, of local degree `e`. In the holomorphic chart of
the filled cover at `P`, multiplication by `exp (2πi/e)` carries the points of the edge of the
sheet `k` exactly to the points of the edge of the sheet `σ0 k`. -/
theorem chartAt_center_overZero_symm_mul_mem_edge_iff (hp : IsCoveringMap p)
    {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀})) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodZero)) (k : Fin n) {z : FilledCover p}
    (hz : z ∈ (@chartAt ℂ _ _ _ (chartedSpace hp hfin)
      (PunctureFilling.center (chart p) (overZero p b))).source) :
    letI := chartedSpace hp hfin
    (chartAt ℂ (PunctureFilling.center (chart p) (overZero p b))).symm
        (exp (2 * π * I / degree p (overZero p b)) *
          chartAt ℂ (PunctureFilling.center (chart p) (overZero p b)) z) ∈
        edge hp ν ((hp.monodromyTriple ν).σ0 k) ↔
      z ∈ edge hp ν k :=
  chartAt_center_symm_mul_mem_edge_iff_of hp hfin ν _
    ((isPrimitiveRoot_exp _ (degree_ne_zero hp hfin _)).norm'_eq_one (degree_ne_zero hp hfin _))
    (incl_chart_overZero_mem_edge_iff hp ν b k) hz

/-- **The edges at a white point rotate by `σ1`, in the complex structure.** Let `P` be the added
point over `1` of a component `b` of `p ⁻¹' D₁*`, of local degree `e`. In the holomorphic chart of
the filled cover at `P`, multiplication by `exp (2πi/e)` carries the points of the edge of the
sheet `k` exactly to the points of the edge of the sheet `σ1 k`. -/
theorem chartAt_center_overOne_symm_mul_mem_edge_iff (hp : IsCoveringMap p)
    {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀})) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodOne)) (k : Fin n) {z : FilledCover p}
    (hz : z ∈ (@chartAt ℂ _ _ _ (chartedSpace hp hfin)
      (PunctureFilling.center (chart p) (overOne p b))).source) :
    letI := chartedSpace hp hfin
    (chartAt ℂ (PunctureFilling.center (chart p) (overOne p b))).symm
        (exp (2 * π * I / degree p (overOne p b)) *
          chartAt ℂ (PunctureFilling.center (chart p) (overOne p b)) z) ∈
        edge hp ν ((hp.monodromyTriple ν).σ1 k) ↔
      z ∈ edge hp ν k :=
  chartAt_center_symm_mul_mem_edge_iff_of hp hfin ν _
    ((isPrimitiveRoot_exp _ (degree_ne_zero hp hfin _)).norm'_eq_one (degree_ne_zero hp hfin _))
    (incl_chart_overOne_mem_edge_iff hp ν b k) hz

end FilledCover

end TauCeti
