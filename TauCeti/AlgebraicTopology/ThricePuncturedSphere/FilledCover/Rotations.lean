/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.ChartedSpace
public import TauCeti.AlgebraicTopology.ThricePuncturedSphere.FilledCover.Edges

import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.SlitPlane

/-!
# Rotations of the edges and positive triangles around the added points of a filled cover

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

No edge reaches an added point `P` over `∞`. What turns around `P` are the positive triangles, the
components of the preimage of the upper half-plane, numbered by the sheets through the lifts of the
vertical segment `αPlus` from `1/2` to `p₊ = 1/2 + (√35/2)·i`
(`IsCoveringMap.finEquivConnectedComponentsUpperHalfPlane`). In the filling chart of `P`, under
which `p` becomes `w ↦ w ^ e` in the coordinate `z ↦ 2 / z`, the upper half-plane is the lower
half-plane of the coordinate, and its preimage consists of `e` sectors. Rotation counterclockwise
by `2π/e` carries the positive triangle of the sheet `k` near `P` onto that of the sheet `σinf k`
(`TauCeti.FilledCover.incl_chart_overInf_mem_upperTriangle_iff`, and
`TauCeti.FilledCover.chartAt_center_overInf_symm_mul_mem_upperTriangle_iff` in the complex
structure). The orientation is that of the coordinate at `∞`, in which the loop `δInf` turns
counterclockwise; in `z` it turns clockwise, and its transport to `1/2` along `αPlus` is
`periphInf`, whose monodromy is `σinf` rather than its inverse.

## Main results

* `TauCeti.FilledCover.incl_chart_overZero_mem_edge_iff`,
  `TauCeti.FilledCover.incl_chart_overOne_mem_edge_iff`: in the filling chart of a component over
  `0`, respectively `1`, of local degree `e`, multiplication by `exp (2πi/e)` carries the edge of
  the sheet `k` to the edge of the sheet `σ0 k`, respectively `σ1 k`.
* `TauCeti.FilledCover.chartAt_center_overZero_symm_mul_mem_edge_iff`,
  `TauCeti.FilledCover.chartAt_center_overOne_symm_mul_mem_edge_iff`: the same statements in the
  holomorphic chart of the filled cover at the added point.
* `TauCeti.FilledCover.incl_chart_overInf_mem_upperTriangle_iff`,
  `TauCeti.FilledCover.chartAt_center_overInf_symm_mul_mem_upperTriangle_iff`: in the filling
  chart, respectively the holomorphic chart, at an added point over `∞` of local degree `e`,
  multiplication by `exp (2πi/e)` carries the positive triangle of the sheet `k` to that of the
  sheet `σinf k`.

## References

* E. Girondo and G. González-Diez, *Introduction to Compact Riemann Surfaces and Dessins
  d'Enfants*, London Mathematical Society Student Texts 79, Cambridge University Press, 2012,
  Chapter 4 (the dessin of a Belyi function, the monodromy permutations around `0` and `1` as
  the rotations of its edges around the black and white vertices, and the triangulation by the
  preimages of the two half-planes, whose positive triangles turn by `σinf` around the faces).
* G. A. Jones and J. Wolfart, *Dessins d'Enfants on Riemann Surfaces*, Springer Monographs in
  Mathematics, Springer, 2016, §2.2 (the positive and negative triangles of a dessin, and the
  permutation `σinf` as their rotation around the face centres).
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
coordinate of `D_q*`, `y` is a point of `D_q*` joined to `1/2` by a path `α`, `δ` is the loop
`t ↦ c · exp (2πit)` in the coordinate, based at `y` of coordinate `c`, and `σ` is the monodromy of
the transport `g` of `δ` along `α`. At `0` and `1`, the segment `(0, 1)` is the positive real axis
in the coordinate, `c = 1/2` and `α` runs along `(0, 1)`; at `∞`, `α` is `αPlus`. -/

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
  (hδ : ∀ t : unitInterval, (q.coord (δ t) : ℂ) = q.coord y * exp (2 * π * I * t))
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

include hp hφq in
/-- A point of the chart whose `e`-th power is the coordinate of `y` lies over `y`, so it is the
endpoint of the lift of `α` from some sheet. -/
private theorem exists_eq_monodromy_α {v : 𝔻*} (hv : (v : ℂ) ^ e = q.coord y) :
    ∃ m, φ v = hp.monodromy (.mk α) (ν.symm m) := by
  obtain ⟨hv', h⟩ := hφq v
  have hpv : p (φ v) = y :=
    congrArg Subtype.val (q.coord.injective (Subtype.ext (h.trans hv)))
  refine ⟨ν ((coveringFiberEquiv hp (.mk α)).symm ⟨φ v, hpv⟩), ?_⟩
  rw [symm_apply_apply, ← coveringFiberEquiv_apply, apply_symm_apply]

include hp hφ he hφq hδ in
/-- **The monodromy of the local loop is a rotation.** In a chart in which `p` is `w ↦ w ^ e` in
the coordinate of `D_q*`, and in which the loop `δ` turns once counterclockwise around `0` from the
coordinate `c` of `y`, the lift of `δ` from a point `v` with `v ^ e = c` ends at
`exp (2πi/e) * v`. -/
private theorem monodromy_δ_eq {v v' : 𝔻*}
    (hv : (v : ℂ) ^ e = q.coord y) (hv' : (v' : ℂ) = exp (2 * π * I / e) * v)
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
    have he' : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.2 he
    rw [hδ t, mul_pow, ← exp_nat_mul, hv, mul_comm, mul_div_cancel₀ _ he']
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
  obtain ⟨m, hm⟩ := exists_eq_monodromy_α hp ν hφq (α := α) (v := v) ((hrw w hwa).trans hy.symm)
  obtain rfl : m = k := (hp.finEquivConnectedComponentsUnitSegment ν).injective <| by
    rw [← hlabel hm hvseg, hvk, hk]
  -- Its rotation `φ v'` is the endpoint of the lift of `α` from the sheet `σ m`.
  have hv' : φ v' = hp.monodromy (.mk α) (ν.symm (σ m)) := by
    rw [← monodromy_δ_monodromy_α hp ν hσ hg m]
    exact (monodromy_δ_eq hp hφ he hφq hδ ((hrw w hwa).trans hy.symm)
      (by simp only [v, v', hw']; ring) hm).symm
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

/-- If multiplication by `ζ`, of norm `1`, in the filling chart of `i` carries the points of `E` in
`s` exactly to the points of `E` in `s'`, and neither set contains the added point of `i`, then
multiplication by `ζ` in the holomorphic chart of the filled cover at that point also carries the
points of `s` exactly to the points of `s'`. -/
private theorem chartAt_center_symm_mul_mem_iff_of (hp : IsCoveringMap p)
    {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀})) (i : FilledPoint p)
    {s s' : Set (FilledCover p)} (hs : PunctureFilling.center (chart p) i ∉ s)
    (hs' : PunctureFilling.center (chart p) i ∉ s') {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hrot : ∀ {w w' : 𝔻*}, (w' : ℂ) = ζ * w →
      (PunctureFilling.incl (chart p) (chart p i w') ∈ s' ↔
        PunctureFilling.incl (chart p) (chart p i w) ∈ s))
    {z : FilledCover p}
    (hz : z ∈
      (@chartAt ℂ _ _ _ (chartedSpace hp hfin) (PunctureFilling.center (chart p) i)).source) :
    letI := chartedSpace hp hfin
    (chartAt ℂ (PunctureFilling.center (chart p) i)).symm
        (ζ * chartAt ℂ (PunctureFilling.center (chart p) i) z) ∈ s' ↔ z ∈ s := by
  let := chartedSpace hp hfin
  rw [chartAt_center_source] at hz
  obtain ⟨d, rfl⟩ := hz
  rw [chartAt_center_apply_disc]
  by_cases hd : d = 0
  · subst hd
    have h0 : ζ * ((0 : ball (0 : ℂ) 1) : ℂ) = ((0 : ball (0 : ℂ) 1) : ℂ) := by simp
    rw [h0, chartAt_center_symm_apply, PunctureFilling.disc_zero]
    exact iff_of_false hs' hs
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
  have hy : (Puncture.zero.coord zeroBasePt : ℂ) = 1 / 2 :=
    (Puncture.coe_coord_zero zeroBasePt).trans (by rw [coe_zeroBasePt]; norm_num)
  simp only [incl_mem_edge_iff]
  exact exists_mk_eq_σ_iff hp ν (q := .zero) (isOpenEmbedding_chart hp hfin _).continuous
    (degree_ne_zero hp hfin _)
    (exists_coe_coord_chart_eq_pow_of_eq hp hfin (q := .zero)
      (congrArg Sigma.fst (sigmaEquiv_overZero (p := p) b)))
    mem_unitSegment_iff_coord_zero (y := zeroBasePt) hy (α := αZero)
    (fun m _ ↦ hp.finEquivConnectedComponentsUnitSegment_eq_mk_monodromy_αZero ν m) (δ := δZero)
    (fun t ↦ (Puncture.coe_coord_zero (δZero t)).trans <| by
      have h : ((δZero t : ThricePuncturedSphere) : ℂ) = 1 / 4 * exp (2 * π * I * t) := by
        rw [coe_δZero, circleMap]
        push_cast
        ring_nf
      linear_combination 2 * h - exp (2 * π * I * t) * hy)
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
  have hy : (Puncture.one.coord oneBasePt : ℂ) = 1 / 2 :=
    (Puncture.coe_coord_one oneBasePt).trans (by rw [coe_oneBasePt]; norm_num)
  simp only [incl_mem_edge_iff]
  exact exists_mk_eq_σ_iff hp ν (q := .one) (isOpenEmbedding_chart hp hfin _).continuous
    (degree_ne_zero hp hfin _)
    (exists_coe_coord_chart_eq_pow_of_eq hp hfin (q := .one)
      (congrArg Sigma.fst (sigmaEquiv_overOne (p := p) b)))
    mem_unitSegment_iff_coord_one (y := oneBasePt) hy (α := αOne)
    (fun m _ ↦ hp.finEquivConnectedComponentsUnitSegment_eq_mk_monodromy_αOne ν m) (δ := δOne)
    (fun t ↦ (Puncture.coe_coord_one (δOne t)).trans <| by
      have h : ((δOne t : ThricePuncturedSphere) : ℂ) = 1 - 1 / 4 * exp (2 * π * I * t) := by
        rw [coe_δOne, circleMap]
        push_cast
        ring_nf
      linear_combination -2 * h - exp (2 * π * I * t) * hy)
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
  chartAt_center_symm_mul_mem_iff_of hp hfin _ (center_notMem_edge hp ν _ k)
    (center_notMem_edge hp ν _ _)
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
  chartAt_center_symm_mul_mem_iff_of hp hfin _ (center_notMem_edge hp ν _ k)
    (center_notMem_edge hp ν _ _)
    ((isPrimitiveRoot_exp _ (degree_ne_zero hp hfin _)).norm'_eq_one (degree_ne_zero hp hfin _))
    (incl_chart_overOne_mem_edge_iff hp ν b k) hz

/-! ### Rotations at the points over `∞` -/

/-- **A sector over the lower half-plane joins `w` to an `e`-th root.** If `w ∈ 𝔻*` has its `e`-th
power in the lower half-plane, and `c` is a point of the lower half-plane in the unit disc, then `w`
is joined to an `e`-th root of `c` by a path of `𝔻*` along which the `e`-th power stays in the lower
half-plane. -/
private theorem exists_path_pow_im_neg {e : ℕ} (he : e ≠ 0) (w : 𝔻*) (hw : ((w : ℂ) ^ e).im < 0)
    {c : ℂ} (hc : c.im < 0) (hc1 : ‖c‖ < 1) :
    ∃ (v : 𝔻*) (_ : (v : ℂ) ^ e = c) (γ : Path w v), ∀ t, (((γ t : 𝔻*) : ℂ) ^ e).im < 0 := by
  set a := (w : ℂ) ^ e with ha
  have ha0 : a ≠ 0 := fun h ↦ by simp [h] at hw
  have ha1 : ‖a‖ < 1 := by
    rw [ha, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) (mem_ball_zero_iff.1 w.2.1) he
  -- The segment `s` from `a` to `c` stays in the lower half-plane and in the unit disc.
  let s : unitInterval → ℂ := fun t ↦ (1 - (t : ℝ)) • a + (t : ℝ) • c
  have hs_im (t : unitInterval) : (s t).im < 0 :=
    convex_halfSpace_im_lt 0 hw hc (sub_nonneg.2 t.2.2) t.2.1 (by ring)
  have hs_norm (t : unitInterval) : ‖s t‖ < 1 :=
    mem_ball_zero_iff.1 (convex_ball (0 : ℂ) 1 (mem_ball_zero_iff.2 ha1) (mem_ball_zero_iff.2 hc1)
      (sub_nonneg.2 t.2.2) t.2.1 (by ring))
  -- Its quotients by `a` avoid the closed negative real axis, so they have continuous `e`-th roots.
  have hslit (t : unitInterval) : s t / a ∈ slitPlane := div_mem_slitPlane_of_im_neg hw (hs_im t)
  let u : unitInterval → ℂ := fun t ↦ w * (s t / a) ^ ((e : ℂ)⁻¹)
  have hu_pow (t : unitInterval) : u t ^ e = s t := by
    simp only [u]
    rw [mul_pow, cpow_nat_inv_pow _ he, ← ha, mul_div_cancel₀ _ ha0]
  have hu_mem (t : unitInterval) : u t ∈ ball (0 : ℂ) 1 \ {0} := by
    refine ⟨mem_ball_zero_iff.2 ?_, fun h ↦ ?_⟩
    · have h := hs_norm t
      rw [← hu_pow t, norm_pow] at h
      exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) he).1 h
    · have h' := hu_pow t
      rw [show u t = 0 from h, zero_pow he] at h'
      simpa [← h'] using hs_im t
  have hu_cont : Continuous u :=
    continuous_const.mul (((by fun_prop : Continuous s).div_const a).cpow continuous_const hslit)
  have hu0 : u 0 = w := by simp [u, s, ha0]
  refine ⟨⟨u 1, hu_mem 1⟩, by rw [hu_pow]; simp [s],
    ⟨⟨fun t ↦ ⟨u t, hu_mem t⟩, hu_cont.subtype_mk _⟩, Subtype.ext hu0, rfl⟩, fun t ↦ ?_⟩
  simpa [hu_pow] using hs_im t

/-- Along a continuous map `φ : 𝔻* → E` sending the points whose `e`-th power lies in the lower
half-plane over the upper half-plane, a path along which the `e`-th power stays in the lower
half-plane joins points of one component of the preimage of the upper half-plane. -/
private theorem mk_eq_mk_of_path {φ : 𝔻* → E} (hφ : Continuous φ) {e : ℕ}
    (hφH : ∀ u : 𝔻*, ((u : ℂ) ^ e).im < 0 → p (φ u) ∈ upperHalfPlane) {u₀ u₁ : 𝔻*}
    (γ : Path u₀ u₁) (hγ : ∀ t, (((γ t : 𝔻*) : ℂ) ^ e).im < 0)
    (h₀ : p (φ u₀) ∈ upperHalfPlane) (h₁ : p (φ u₁) ∈ upperHalfPlane) :
    ConnectedComponents.mk (⟨φ u₀, h₀⟩ : p ⁻¹' upperHalfPlane) =
      ConnectedComponents.mk ⟨φ u₁, h₁⟩ := by
  rw [ConnectedComponents.coe_eq_coe']
  exact pathComponent_subset_component _
    ((joinedIn_iff_joined (F := p ⁻¹' upperHalfPlane) h₁ h₀).1
      ⟨(γ.map hφ).symm, fun t ↦ hφH _ (hγ _)⟩)

/-- The filling chart of an added point over `∞` goes over the upper half-plane exactly where its
power is in the lower half-plane. -/
private theorem chart_overInf_mem_upperHalfPlane_iff (hp : IsCoveringMap p)
    {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀}))
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf)) (u : 𝔻*) :
    p (chart p (overInf p b) u) ∈ upperHalfPlane ↔
      ((u : ℂ) ^ degree p (overInf p b)).im < 0 := by
  obtain ⟨hu, h⟩ := exists_coe_coord_chart_eq_pow_of_eq hp hfin (q := .inf)
    (congrArg Sigma.fst (sigmaEquiv_overInf (p := p) b)) u
  rw [mem_upperHalfPlane_iff_coord_inf _ hu, h]

/-- **Rotation carries the positive triangle of `k` to that of `σinf k`.** In the filling chart of
a component over `∞` of local degree `e`, multiplication by `exp (2πi/e)` carries a point of the
positive triangle of the sheet `k` to a point of the positive triangle of the sheet `σinf k`. -/
private theorem exists_mk_eq_σinf (hp : IsCoveringMap p) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf)) {w w' : 𝔻*}
    (hw' : (w' : ℂ) = exp (2 * π * I / degree p (overInf p b)) * w)
    (hw : p (chart p (overInf p b) w) ∈ upperHalfPlane) {k : Fin n}
    (hk : ConnectedComponents.mk ⟨chart p (overInf p b) w, hw⟩ =
      hp.finEquivConnectedComponentsUpperHalfPlane ν k) :
    ∃ hw'' : p (chart p (overInf p b) w') ∈ upperHalfPlane,
      ConnectedComponents.mk ⟨chart p (overInf p b) w', hw''⟩ =
        hp.finEquivConnectedComponentsUpperHalfPlane ν ((hp.monodromyTriple ν).σinf k) := by
  have hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  have he : degree p (overInf p b) ≠ 0 := degree_ne_zero hp hfin _
  have hφ : Continuous (chart p (overInf p b)) := (isOpenEmbedding_chart hp hfin _).continuous
  have hφq := exists_coe_coord_chart_eq_pow_of_eq hp hfin (q := .inf)
    (congrArg Sigma.fst (sigmaEquiv_overInf (p := p) b))
  have hφH := chart_overInf_mem_upperHalfPlane_iff hp hfin b
  -- The label of a point of the lift of `αPlus` from the sheet `m` is `m`.
  have hlabel {m : Fin n} {x : E} (hx : x = hp.monodromy (.mk αPlus) (ν.symm m))
      (hxH : p x ∈ upperHalfPlane) :
      ConnectedComponents.mk (⟨x, hxH⟩ : p ⁻¹' upperHalfPlane) =
        hp.finEquivConnectedComponentsUpperHalfPlane ν m := by
    subst hx
    rw [hp.finEquivConnectedComponentsUpperHalfPlane_apply]
  -- Join `w`, inside its sector, to a point `v` of the chart over `p₊`; `v` lies on the lift of
  -- `αPlus` from the sheet `k`.
  have hc : (Puncture.inf.coord infBasePt : ℂ).im < 0 :=
    (mem_upperHalfPlane_iff_coord_inf _ _).1 pPlus_mem_upperHalfPlane
  obtain ⟨v, hv, γ, hγ⟩ := exists_path_pow_im_neg he w ((hφH w).1 hw) hc
    (mem_ball_zero_iff.1 (Puncture.inf.coord infBasePt).2.1)
  have hvH : p (chart p (overInf p b) v) ∈ upperHalfPlane := (hφH v).2 (by rw [hv]; exact hc)
  obtain ⟨m, hm⟩ := exists_eq_monodromy_α hp ν hφq (q := .inf) (y := infBasePt) (α := αPlus)
    (v := v) hv
  obtain rfl : m = k := (hp.finEquivConnectedComponentsUpperHalfPlane ν).injective <| by
    rw [← hlabel hm hvH, ← hk, mk_eq_mk_of_path hφ (fun u ↦ (hφH u).2) γ hγ hw hvH]
  -- Rotation by `exp (2πi/e)` preserves `e`-th powers, so it maps the sector of `w` to the sector
  -- of `w'`, and it carries `v` to the end of the lift of `αPlus` from the sheet `σinf m`.
  have hζ := (isPrimitiveRoot_exp _ he).norm'_eq_one he
  let rot : C(𝔻*, 𝔻*) :=
    ⟨fun u ↦ ⟨_, mul_mem_puncturedDisc_of_norm_eq_one hζ u⟩, by fun_prop⟩
  have hrot (u : 𝔻*) : ((rot u : 𝔻*) : ℂ) ^ degree p (overInf p b) = (u : ℂ) ^ _ :=
    exp_mul_pow he u
  obtain rfl : w' = rot w := Subtype.ext hw'
  have hvrot : chart p (overInf p b) (rot v) =
      hp.monodromy (.mk αPlus) (ν.symm ((hp.monodromyTriple ν).σinf m)) := by
    rw [← monodromy_δ_monodromy_α hp ν (q := .inf) (y := infBasePt) (α := αPlus) (δ := δInf)
      (hp.monodromyTriple_σinf ν) transport_δInf_eq_periphInf m]
    exact (monodromy_δ_eq hp hφ he hφq (q := .inf) (y := infBasePt) (δ := δInf) coe_coord_δInf hv
      rfl hm).symm
  have hw'H : p (chart p (overInf p b) (rot w)) ∈ upperHalfPlane :=
    (hφH _).2 (by rw [hrot]; exact (hφH w).1 hw)
  refine ⟨hw'H, ?_⟩
  rw [← hlabel hvrot ((hφH _).2 (by rw [hrot, hv]; exact hc))]
  exact mk_eq_mk_of_path hφ (fun u ↦ (hφH u).2) (γ.map rot.continuous)
    (fun t ↦ by simpa [hrot] using hγ t) hw'H _

/-- **The positive triangles at a point over `∞` rotate by `σinf`.** Let `P` be the added point over
`∞` of a component `b` of `p ⁻¹' D∞*`, of local degree `e`. In the filling chart of `b`, in which
`p` is `w ↦ w ^ e` in the coordinate `z ↦ 2 / z`, multiplication by `exp (2πi/e)` carries the points
of the positive triangle of the sheet `k` exactly to the points of the positive triangle of the
sheet `σinf k`: turning counterclockwise by `2π/e` around `P`, read in the coordinate at `∞`,
advances each positive triangle at `P` by `σinf`. -/
theorem incl_chart_overInf_mem_upperTriangle_iff (hp : IsCoveringMap p)
    (ν : p ⁻¹' {basePt} ≃ Fin n) (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf))
    (k : Fin n) {w w' : 𝔻*} (hw' : (w' : ℂ) = exp (2 * π * I / degree p (overInf p b)) * w) :
    PunctureFilling.incl (chart p) (chart p (overInf p b) w') ∈
        upperTriangle hp ν ((hp.monodromyTriple ν).σinf k) ↔
      PunctureFilling.incl (chart p) (chart p (overInf p b) w) ∈ upperTriangle hp ν k := by
  have hfin : Finite (p ⁻¹' {basePt}) := .of_equiv _ ν.symm
  have he : degree p (overInf p b) ≠ 0 := degree_ne_zero hp hfin _
  simp only [incl_mem_upperTriangle_iff]
  refine ⟨fun ⟨hw'', hk⟩ ↦ ?_, fun ⟨hw, hk⟩ ↦ exists_mk_eq_σinf hp ν b hw' hw hk⟩
  -- `w` and `w'` have the same `e`-th power, so `w` goes over the upper half-plane as well.
  have hw : p (chart p (overInf p b) w) ∈ upperHalfPlane := by
    rw [chart_overInf_mem_upperHalfPlane_iff hp hfin, ← exp_mul_pow he, ← hw',
      ← chart_overInf_mem_upperHalfPlane_iff hp hfin]
    exact hw''
  -- The triangle of `w` is that of some sheet `m`, and rotation carries it to that of `σinf m`.
  set m := (hp.finEquivConnectedComponentsUpperHalfPlane ν).symm
    (ConnectedComponents.mk ⟨_, hw⟩)
  obtain ⟨_, hσm⟩ := exists_mk_eq_σinf hp ν b hw' hw (k := m) (Equiv.apply_symm_apply _ _).symm
  have hmk : m = k := (hp.monodromyTriple ν).σinf.injective
    ((hp.finEquivConnectedComponentsUpperHalfPlane ν).injective (hσm.symm.trans hk))
  exact ⟨hw, hmk ▸ (Equiv.apply_symm_apply _ _).symm⟩

/-- **The positive triangles at a point over `∞` rotate by `σinf`, in the complex structure.** Let
`P` be the added point over `∞` of a component `b` of `p ⁻¹' D∞*`, of local degree `e`. In the
holomorphic chart of the filled cover at `P`, multiplication by `exp (2πi/e)` carries the points of
the positive triangle of the sheet `k` exactly to the points of the positive triangle of the sheet
`σinf k`. -/
theorem chartAt_center_overInf_symm_mul_mem_upperTriangle_iff (hp : IsCoveringMap p)
    {z₀ : ThricePuncturedSphere} (hfin : Finite (p ⁻¹' {z₀})) (ν : p ⁻¹' {basePt} ≃ Fin n)
    (b : ConnectedComponents (p ⁻¹' puncturedNeighborhoodInf)) (k : Fin n) {z : FilledCover p}
    (hz : z ∈ (@chartAt ℂ _ _ _ (chartedSpace hp hfin)
      (PunctureFilling.center (chart p) (overInf p b))).source) :
    letI := chartedSpace hp hfin
    (chartAt ℂ (PunctureFilling.center (chart p) (overInf p b))).symm
        (exp (2 * π * I / degree p (overInf p b)) *
          chartAt ℂ (PunctureFilling.center (chart p) (overInf p b)) z) ∈
        upperTriangle hp ν ((hp.monodromyTriple ν).σinf k) ↔
      z ∈ upperTriangle hp ν k :=
  chartAt_center_symm_mul_mem_iff_of hp hfin _ (center_notMem_upperTriangle hp ν _ k)
    (center_notMem_upperTriangle hp ν _ _)
    ((isPrimitiveRoot_exp _ (degree_ne_zero hp hfin _)).norm'_eq_one (degree_ne_zero hp hfin _))
    (incl_chart_overInf_mem_upperTriangle_iff hp ν b k) hz

end FilledCover

end TauCeti
