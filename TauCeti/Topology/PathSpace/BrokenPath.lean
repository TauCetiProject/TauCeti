/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.UnitInterval
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.CompactOpen

/-!
# Broken paths and the straightening of arcs

Subdivide the unit interval into `r` equal arcs `[i/r, (i+1)/r]` (`unitInterval.arcPoint`). A
path `f : C(I, X)` can be compared with the *broken path* through its vertices `f (i/r)`, which
runs on the `i`-th arc along a chosen interpolating path from `f (i/r)` to `f ((i+1)/r)`. In a
Riemannian manifold the interpolating path is the minimizing geodesic between two close points; in
a real topological vector space it is the segment. This file constructs, for an abstract choice of
interpolating paths, the canonical homotopy from `f` to its broken path.

The interpolation is a map `ρ : X × X → C(I, X)` which, on a set `U` of pairs of points, is
continuous and runs from the first point to the second, and which is constant on the diagonal
(`TauCeti.IsPathInterpolation`). A path has *arcs within `U`* (`TauCeti.ArcsWithin`) if every
point of every arc forms with the initial vertex of its arc a pair in `U`.

On one arc, with initial vertex `x = f (i/r)`, consider the map of the square
`(a, b) ↦ ρ (x, f ((i + a)/r)) b`. Its left edge `a = 0` and its bottom edge `b = 0` are constant
at `x`, its top edge `b = 1` is the arc of `f`, and its right edge `a = 1` is the interpolating
path from `x` to `f ((i+1)/r)`. Sweeping a path through the square, from the left edge followed
by the top edge to the bottom edge followed by the right edge, deforms the arc into the
interpolating path while fixing both of its end points. Doing this on every arc at once gives
`TauCeti.straightenArcs ρ r f t s`: at `t = 0` it is `f`, at `t = 1` the broken path
`TauCeti.brokenPath ρ r f`, and every vertex `f (i/r)` stays fixed throughout. It is continuous
in the path, the time and the parameter for every continuous family of paths whose arcs lie in
`U` (`TauCeti.continuous_straightenArcs`), so the broken path is continuous
(`TauCeti.continuous_brokenPath`). On each arc the broken path is the interpolating path between
its vertices (`TauCeti.brokenPath_arcPoint`), so it only depends on the vertices of `f`
(`TauCeti.brokenPath_congr`).

The Moore path version of the construction is in
`TauCeti.Topology.PathSpace.Moore.ArcStraightening`.

## Main definitions

* `TauCeti.IsPathInterpolation ρ U`: `ρ` is a continuous choice of paths between the pairs of
  points in `U`, constant on the diagonal.
* `TauCeti.ArcsWithin U r f`: every arc of the subdivision of `f` into `r` arcs lies in `U` as
  seen from its initial vertex.
* `TauCeti.straightenArcs ρ r f`: the homotopy from `f` to its broken path.
* `TauCeti.brokenPath ρ r f`: the broken path through the vertices of `f`.

## Main results

* `TauCeti.continuous_straightenArcs`: the homotopy is continuous in families.
* `TauCeti.straightenArcs_zero`, `TauCeti.straightenArcs_one`: its two ends.
* `TauCeti.straightenArcs_arcPoint_zero`: it fixes the vertices.
* `TauCeti.continuous_brokenPath`: the broken path is continuous.
* `TauCeti.brokenPath_arcPoint`, `TauCeti.brokenPath_arcPoint_of_arcsWithin`: the broken path on
  an arc.
* `TauCeti.isPathInterpolation_segment`: segments interpolate in a real topological vector
  space.

## References

* M. Abouzaid, *Symplectic cohomology and Viterbo's theorem*, in *Free loop spaces in geometry
  and topology*, IRMA Lect. Math. Theor. Phys. 24 (2015), §11.2.
* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton, 1963, §16.
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §4.3.
-/

public noncomputable section

open scoped unitInterval
open Set unitInterval

namespace TauCeti

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-! ### Sweeping the square -/

section Sweep

/-- A path, depending on `t ∈ I`, through the unit square `(a, b)`. At `t = 0` it is the top
edge `θ ↦ (θ, 1)`, at `t = 1` the right edge `θ ↦ (1, θ)`. It always ends at the corner `(1, 1)`,
and it starts on the left edge `a = 0` or on the bottom edge `b = 0`. -/
private def sweep (t θ : I) : I × I :=
  (projIcc 0 1 zero_le_one ((θ : ℝ) + (1 - θ) * max 0 (2 * (t : ℝ) - 1)),
    projIcc 0 1 zero_le_one ((θ : ℝ) + (1 - θ) * max 0 (1 - 2 * (t : ℝ))))

@[fun_prop]
private theorem continuous_sweep : Continuous fun p : I × I ↦ sweep p.1 p.2 := by
  unfold sweep
  fun_prop

private theorem sweep_zero (θ : I) : sweep 0 θ = (θ, 1) := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
    simp [sweep]

private theorem sweep_one (θ : I) : sweep 1 θ = (1, θ) := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;>
    norm_num [sweep, coe_projIcc, θ.property.1, θ.property.2]

private theorem sweep_right (t : I) : sweep t 1 = (1, 1) := by
  refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_) <;> simp [sweep]

private theorem sweep_left (t : I) : (sweep t 0).1 = 0 ∨ (sweep t 0).2 = 0 := by
  rcases le_total (t : ℝ) (1 / 2) with h | h
  · left
    refine Subtype.ext ?_
    simp [sweep, show 2 * (t : ℝ) - 1 ≤ 0 by linarith]
  · right
    refine Subtype.ext ?_
    simp [sweep, show 1 - 2 * (t : ℝ) ≤ 0 by linarith]

end Sweep

/-! ### Interpolating paths -/

/-- `ρ` is a **path interpolation** on a set `U` of pairs of points: on `U` the path `ρ (x, y)`
runs from `x` to `y` and depends continuously on `(x, y)`, and it is the constant path at `x`
when `(x, x) ∈ U`. Minimizing geodesics between close points of a Riemannian manifold, and
segments in a real topological vector space (`TauCeti.isPathInterpolation_segment`), are
examples. -/
structure IsPathInterpolation (ρ : X × X → C(I, X)) (U : Set (X × X)) : Prop where
  continuousOn : ContinuousOn ρ U
  apply_zero : ∀ p ∈ U, ρ p 0 = p.1
  apply_one : ∀ p ∈ U, ρ p 1 = p.2
  apply_diag : ∀ x, (x, x) ∈ U → ρ (x, x) = ContinuousMap.const I x

/-- **Segments interpolate** between all pairs of points of a real topological vector space. -/
theorem isPathInterpolation_segment {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [ContinuousAdd E] [ContinuousSMul ℝ E] :
    IsPathInterpolation (fun p : E × E ↦ (Path.segment p.1 p.2 : C(I, E))) univ where
  continuousOn := (ContinuousMap.continuous_of_continuous_uncurry _ (by
    simp only [Function.uncurry_def, ContinuousMap.coe_mk, Path.segment_apply,
      AffineMap.lineMap_apply_module]
    fun_prop)).continuousOn
  apply_zero p _ := (Path.segment p.1 p.2).source
  apply_one p _ := (Path.segment p.1 p.2).target
  apply_diag x _ := by ext; simp [Path.segment_same]

/-! ### The straightening homotopy -/

section Straighten

variable (ρ : X × X → C(I, X)) (r : ℕ) (f : C(I, X))

/-- The map of the square attached to the `i`-th arc of `f`: `(a, b) ↦ ρ (x, f ((i + a)/r)) b`,
with `x = f (i/r)` the initial vertex of the arc. -/
private def arcSquare (i : ℕ) (p : I × I) : X :=
  ρ (f (arcPoint r i 0), f (arcPoint r i p.1)) p.2

/-- Every arc of the subdivision of `f` into `r` equal arcs lies in `U` as seen from its initial
vertex: every point of the `i`-th arc forms with `f (i/r)` a pair in `U`. -/
@[expose] def ArcsWithin (U : Set (X × X)) (r : ℕ) (f : C(I, X)) : Prop :=
  ∀ i < r, ∀ a : I, (f (arcPoint r i 0), f (arcPoint r i a)) ∈ U

/-- The straightening of the arcs of a path `f`, `t` being the time and `s` the parameter of the
path. On the `i`-th arc, with initial vertex `x = f (i/r)`, it follows the map
`(a, b) ↦ ρ (x, f ((i + a)/r)) b` of the unit square along a path through the square that runs
along the top edge `b = 1` at `t = 0` and along the right edge `a = 1` at `t = 1`. At `t = 1` it is
the broken path `TauCeti.brokenPath ρ r f` (`TauCeti.straightenArcs_one`). If
`IsPathInterpolation ρ U`, `ArcsWithin U r f` and `0 < r`, it is `f` at `t = 0`
(`TauCeti.straightenArcs_zero`) and it is continuous (`TauCeti.continuous_straightenArcs`), so it
is a homotopy from `f` to its broken path. -/
def straightenArcs (t s : I) : X :=
  arcSquare ρ r f (arcIndex r s) (sweep t (arcParam r s))

/-- The broken path through the vertices `f (i/r)`: on the `i`-th arc it runs along the
interpolating path `ρ (f (i/r), f ((i+1)/r))`. -/
def brokenPath (s : I) : X :=
  ρ (f (arcPoint r (arcIndex r s) 0), f (arcPoint r (arcIndex r s) 1)) (arcParam r s)

/-- At time one the homotopy is the broken path. -/
@[simp]
theorem straightenArcs_one (s : I) : straightenArcs ρ r f 1 s = brokenPath ρ r f s := by
  rw [straightenArcs, arcSquare, sweep_one, brokenPath]

/-- The broken path only depends on the vertices `f (i/r)`, `0 ≤ i ≤ r`. -/
theorem brokenPath_congr {g : C(I, X)} (h : ∀ i ≤ r, f (arcPoint r i 0) = g (arcPoint r i 0)) :
    brokenPath ρ r f = brokenPath ρ r g := by
  funext s
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have h0 := h 0 le_rfl
    simp only [arcPoint_zero_left] at h0
    simp [brokenPath, h0]
  · have hi := arcIndex_lt hr s
    rw [brokenPath, brokenPath, arcPoint_one, h _ hi.le, h _ hi]

/-- On the `i`-th arc, away from its end point, the broken path runs along the interpolating
path `ρ (f (i/r), f ((i+1)/r))`. -/
theorem brokenPath_arcPoint {i : ℕ} (hi : i < r) {a : I} (ha : a < 1) :
    brokenPath ρ r f (arcPoint r i a) = ρ (f (arcPoint r i 0), f (arcPoint r (i + 1) 0)) a := by
  rw [brokenPath, arcIndex_arcPoint hi ha, arcParam_arcPoint hi ha, arcPoint_one]

variable {ρ r f} {U : Set (X × X)}

/-- The square of an arc within `U` is constant at the initial vertex on the left edge. -/
private theorem arcSquare_of_fst_eq_zero (hρ : IsPathInterpolation ρ U) (hf : ArcsWithin U r f)
    {i : ℕ} (hi : i < r) {p : I × I} (hp : p.1 = 0) : arcSquare ρ r f i p = f (arcPoint r i 0) := by
  rw [arcSquare, hp, hρ.apply_diag _ (hp ▸ hf i hi 0), ContinuousMap.const_apply]

/-- The square of an arc within `U` is constant at the initial vertex on the bottom edge. -/
private theorem arcSquare_of_snd_eq_zero (hρ : IsPathInterpolation ρ U) (hf : ArcsWithin U r f)
    {i : ℕ} (hi : i < r) {p : I × I} (hp : p.2 = 0) : arcSquare ρ r f i p = f (arcPoint r i 0) := by
  rw [arcSquare, hp, hρ.apply_zero _ (hf i hi p.1)]

/-- The top edge of the square of an arc within `U` is the arc of `f`. -/
private theorem arcSquare_top (hρ : IsPathInterpolation ρ U) (hf : ArcsWithin U r f) {i : ℕ}
    (hi : i < r) (a : I) : arcSquare ρ r f i (a, 1) = f (arcPoint r i a) := by
  rw [arcSquare, hρ.apply_one _ (hf i hi a)]

/-- At the start of the sweeping path the square of an arc within `U` is the initial vertex. -/
private theorem arcSquare_sweep_zero (hρ : IsPathInterpolation ρ U) (hf : ArcsWithin U r f) {i : ℕ}
    (hi : i < r) (t : I) : arcSquare ρ r f i (sweep t 0) = f (arcPoint r i 0) :=
  (sweep_left t).elim (arcSquare_of_fst_eq_zero hρ hf hi) (arcSquare_of_snd_eq_zero hρ hf hi)

/-- On the `i`-th arc, the homotopy is the map of the `i`-th square along the sweeping path, also
at the common end point with the next arc. -/
private theorem straightenArcs_eq_arcSquare (hρ : IsPathInterpolation ρ U) (hf : ArcsWithin U r f)
    {i : ℕ} (hi : i < r) (t : I) {s : I} (h₀ : (i : ℝ) ≤ r * s) (h₁ : (r : ℝ) * s ≤ i + 1) :
    straightenArcs ρ r f t s =
      arcSquare ρ r f i (sweep t (projIcc 0 1 zero_le_one ((r : ℝ) * s - i))) := by
  rcases arcIndex_eq_or hi h₀ h₁ with h | ⟨h, hs⟩
  · have hθ : arcParam r s = projIcc 0 1 zero_le_one ((r : ℝ) * s - i) := by
      rw [← h, projIcc_of_mem _ ⟨sub_nonneg.2 (arcIndex_le_mul r s),
        by linarith [mul_le_arcIndex_add_one ((Nat.zero_le i).trans_lt hi) s]⟩]
      exact Subtype.ext (coe_arcParam ((Nat.zero_le i).trans_lt hi) s)
    rw [straightenArcs, h, hθ]
  · have hi' : i + 1 < r := h ▸ arcIndex_lt ((Nat.zero_le i).trans_lt hi) s
    have hθ : arcParam r s = 0 := by
      ext
      simp [coe_arcParam ((Nat.zero_le i).trans_lt hi), h, hs]
    have hθ' : projIcc 0 1 zero_le_one ((r : ℝ) * s - i) = 1 := by
      simp [hs]
    rw [straightenArcs, h, hθ, hθ', arcSquare_sweep_zero hρ hf hi', sweep_right,
      arcSquare_top hρ hf hi, arcPoint_one]

/-- On the whole `i`-th arc of a path whose arcs lie in `U`, end point included, the broken path
runs along the interpolating path `ρ (f (i/r), f ((i+1)/r))`. -/
theorem brokenPath_arcPoint_of_arcsWithin (hρ : IsPathInterpolation ρ U) (hf : ArcsWithin U r f)
    {i : ℕ} (hi : i < r) (a : I) :
    brokenPath ρ r f (arcPoint r i a) = ρ (f (arcPoint r i 0), f (arcPoint r (i + 1) 0)) a := by
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast ((Nat.zero_le i).trans_lt hi).ne'
  have hs : (r : ℝ) * arcPoint r i a = i + a := by
    rw [coe_arcPoint hi, mul_div_cancel₀ _ hr]
  rw [← straightenArcs_one, straightenArcs_eq_arcSquare hρ hf hi 1 (by rw [hs]; simp [a.property.1])
    (by rw [hs]; simp [a.property.2]), hs, add_sub_cancel_left, projIcc_val, sweep_one, arcSquare,
    arcPoint_one]

/-- **The straightening homotopy is continuous** in the time, the parameter and the path, for
every continuous family of paths whose arcs lie in `U`. -/
theorem continuous_straightenArcs (hρ : IsPathInterpolation ρ U) (hr : 0 < r)
    {F : Y → C(I, X)} (hF : Continuous F) (hU : ∀ y, ArcsWithin U r (F y)) :
    Continuous fun p : Y × I × I ↦ straightenArcs ρ r (F p.1) p.2.1 p.2.2 := by
  -- The closed pieces of `Y × I × I` over the `r` arcs cover it, and on each of them the
  -- homotopy is given by one continuous formula.
  let B : Fin r → Set (Y × I × I) := fun i ↦ {p | (i : ℝ) ≤ r * p.2.2 ∧ (r : ℝ) * p.2.2 ≤ i + 1}
  refine (locallyFinite_of_finite B).continuous ?_ (fun i ↦ ?_) (fun i ↦ ?_)
  · refine eq_univ_of_forall fun p ↦ mem_iUnion.2 ⟨⟨arcIndex r p.2.2, arcIndex_lt hr _⟩,
      arcIndex_le_mul r _, mul_le_arcIndex_add_one hr _⟩
  · have hc : Continuous fun p : Y × I × I ↦ (r : ℝ) * p.2.2 := by fun_prop
    exact (isClosed_le continuous_const hc).inter (isClosed_le hc continuous_const)
  · have hpair : Continuous fun p : Y × I × I ↦ ((F p.1) (arcPoint r i 0),
        (F p.1) (arcPoint r i
          (sweep p.2.1 (projIcc 0 1 zero_le_one ((r : ℝ) * p.2.2 - i))).1)) := by
      fun_prop
    have hρp := hρ.continuousOn.comp_continuous hpair fun p ↦ hU p.1 i i.isLt _
    refine (ContinuousEval.continuous_eval.comp (hρp.prodMk ?_)).continuousOn.congr
      fun p hp ↦ straightenArcs_eq_arcSquare hρ (hU p.1) i.isLt p.2.1 hp.1 hp.2
    have hθ : Continuous fun p : Y × I × I ↦
        (p.2.1, projIcc 0 1 zero_le_one ((r : ℝ) * p.2.2 - i)) := by fun_prop
    exact continuous_snd.comp (continuous_sweep.comp hθ)

/-- The broken path through the vertices of a path whose arcs lie in `U` is continuous. -/
theorem continuous_brokenPath (hρ : IsPathInterpolation ρ U) (hr : 0 < r) (hf : ArcsWithin U r f) :
    Continuous (brokenPath ρ r f) := by
  simpa [Function.comp_def] using
    (continuous_straightenArcs (Y := Unit) hρ hr continuous_const fun _ ↦ hf).comp
      (by fun_prop : Continuous fun s : I ↦ ((), (1 : I), s))

/-- At time zero the homotopy is the path itself. -/
theorem straightenArcs_zero (hρ : IsPathInterpolation ρ U) (hr : 0 < r) (hf : ArcsWithin U r f)
    (s : I) : straightenArcs ρ r f 0 s = f s := by
  rw [straightenArcs, sweep_zero, arcSquare_top hρ hf (arcIndex_lt hr s),
    arcPoint_arcIndex_arcParam hr]

/-- The homotopy fixes the vertices `f (j/r)`, `j < r`. -/
theorem straightenArcs_arcPoint_zero (hρ : IsPathInterpolation ρ U) (hf : ArcsWithin U r f)
    {j : ℕ} (hj : j < r) (t : I) :
    straightenArcs ρ r f t (arcPoint r j 0) = f (arcPoint r j 0) := by
  rw [straightenArcs, arcIndex_arcPoint hj zero_lt_one, arcParam_arcPoint hj zero_lt_one,
    arcSquare_sweep_zero hρ hf hj]

/-- The homotopy fixes the start point. -/
theorem straightenArcs_source (hρ : IsPathInterpolation ρ U) (hr : 0 < r)
    (hf : ArcsWithin U r f) (t : I) : straightenArcs ρ r f t 0 = f 0 := by
  simpa using straightenArcs_arcPoint_zero hρ hf hr t

/-- The homotopy fixes the end point. -/
theorem straightenArcs_target (hρ : IsPathInterpolation ρ U) (hr : 0 < r)
    (hf : ArcsWithin U r f) (t : I) : straightenArcs ρ r f t 1 = f 1 := by
  rw [straightenArcs, arcIndex_one, arcParam_one hr, sweep_right,
    arcSquare_top hρ hf (Nat.sub_lt hr one_pos), arcPoint_one, Nat.sub_one_add_one hr.ne',
    arcPoint_self_zero hr]

/-- The homotopy of a constant path is constant. -/
theorem straightenArcs_const (hρ : IsPathInterpolation ρ U) {x : X} (hx : (x, x) ∈ U)
    (t s : I) : straightenArcs ρ r (ContinuousMap.const I x) t s = x := by
  simp [straightenArcs, arcSquare, hρ.apply_diag x hx]

end Straighten

end TauCeti
