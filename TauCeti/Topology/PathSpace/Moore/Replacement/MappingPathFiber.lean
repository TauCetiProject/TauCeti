/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv.Basic
public import TauCeti.Topology.Homotopy.MappingPath.Loop
public import TauCeti.Topology.PathSpace.Moore.Comparison.Trans
public import TauCeti.Topology.PathSpace.Moore.Replacement.Basic

/-!
# The Moore fibre and the mapping-path fibre, with their loop actions

Let `p : E → B` be continuous and `b ∈ B`. Two models of the homotopy fibre of `p` over `b` are
in use: the fibre `F' = TauCeti.MooreReplacement.Fiber p b` of the Moore-path replacement, the
pairs `(e, γ)` of a point `e ∈ E` and a Moore path `γ` from `p e` to `b`, and the mapping-path fibre
`TauCeti.MappingPathFiber p b`, the same pairs with `γ` a path on the unit interval. The comparison
of Moore paths with paths on the unit interval (`TauCeti.MoorePath.toUnitPath`,
`TauCeti.MoorePath.ofUnitPath`) identifies them up to fibre homotopy equivalence over `E`
(`TauCeti.MooreReplacement.Fiber.fiberHomotopyEquivMappingPathFiber`).

The Moore loops at `b` act strictly on `F'`, by `(e, γ) · ω = (e, γ · ω)`
(`TauCeti.MooreReplacement.Fiber.act`), and the loops on the unit interval at `b` act on the
mapping-path fibre by concatenation (`TauCeti.MappingPathFiber.transLoop`), which is an action only
up to homotopy. Under the comparison maps, together with the comparison of the two loop spaces
(`TauCeti.MooreLoopSpace.toPath`, `Path.toMooreLoop`), the two actions correspond up to specified
homotopies, continuous in the point of the fibre and the loop and fixing the point of `E`
throughout:

* `TauCeti.MooreReplacement.Fiber.actToMappingPathFiberHomotopy`: from `(x, ω)` to the
  mapping-path fibre, concatenating the comparison of `x` with the loop of `ω` is homotopic to
  comparing `x · ω`. The homotopy reads the Moore path `γ · ω` along a reparametrization of the
  unit interval that runs at constant speed at one end and through `γ` on `[0, 1/2]` and `ω` on
  `[1/2, 1]` at the other.
* `TauCeti.MooreReplacement.Fiber.actOfMappingPathFiberHomotopy`: from `(y, ℓ)` to the Moore fibre,
  the comparison of `y.trans ℓ`, a Moore path of length one, is homotopic to the comparison of `y`
  acted on by the Moore loop of `ℓ`, of length two, by stretching the duration from one to two
  (`Path.transMoorePath_eq_rescale`).

These are the fibre forms of the multiplicativity of the comparison of loop spaces up to homotopy
(`TauCeti.MooreLoopSpace.mulToPathHomotopy`, `Path.transMooreLoopHomotopy`): constructions made
with the strict Moore action on `F'` agree, up to these homotopies, with their fixed-interval
counterparts on the mapping-path fibre.

## Main definitions

* `TauCeti.MooreReplacement.Fiber.toMappingPathFiber`,
  `TauCeti.MooreReplacement.Fiber.ofMappingPathFiber`: the comparison maps.
* `TauCeti.MooreReplacement.Fiber.fiberHomotopyEquivMappingPathFiber`: the fibre homotopy
  equivalence over `E` between `F'` and `MappingPathFiber p b`.
* `TauCeti.MooreReplacement.Fiber.actToMappingPathFiberHomotopy`,
  `TauCeti.MooreReplacement.Fiber.actOfMappingPathFiberHomotopy`: the two actions correspond up to
  homotopy under the comparison maps.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapters I.7 and III.
-/

public noncomputable section

open scoped NNReal
open ContinuousMap unitInterval

universe u v

namespace TauCeti.MooreReplacement.Fiber

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B)) (b : B)

/-! ### The comparison maps -/

/-- The comparison of the Moore fibre with the mapping-path fibre: `(e, γ) ↦ (e, γ.toUnitPath)`,
the Moore path `γ` of length `L` read on the unit interval as `s ↦ γ (L s)`. -/
def toMappingPathFiber : C(Fiber p b, MappingPathFiber p b) where
  toFun x := ⟨(x.val.point, x.val.path.toUnitPath),
    by rw [MoorePath.toUnitPath_zero, source_path],
    by rw [MoorePath.toUnitPath_one, target_path_val]⟩
  continuous_toFun := ((continuous_point.comp continuous_val).prodMk
    (MoorePath.continuous_toUnitPath.comp (continuous_path.comp continuous_val))).subtype_mk _

@[simp]
theorem toMappingPathFiber_val (x : Fiber p b) :
    (toMappingPathFiber p b x).val = (x.val.point, x.val.path.toUnitPath) :=
  (rfl)

/-- The comparison of the mapping-path fibre with the Moore fibre: `(e, γ) ↦ (e, ofUnitPath γ)`,
the path `γ` on the unit interval read as a Moore path of length one. -/
def ofMappingPathFiber : C(MappingPathFiber p b, Fiber p b) where
  toFun y := ⟨MooreReplacement.mk y.val.1 (MoorePath.ofUnitPath y.val.2)
      (by rw [MoorePath.source_ofUnitPath, y.property.1]),
    (congrArg MoorePath.target (path_mk _ _ _)).trans
      ((MoorePath.target_ofUnitPath _).trans y.property.2)⟩
  continuous_toFun := (continuous_mk continuous_subtypeVal.fst
    (MoorePath.continuous_ofUnitPath.comp continuous_subtypeVal.snd)
    fun y ↦ by rw [Function.comp_apply, MoorePath.source_ofUnitPath, y.property.1]).subtype_mk _

@[simp]
theorem point_ofMappingPathFiber (y : MappingPathFiber p b) :
    (ofMappingPathFiber p b y).val.point = y.val.1 := by
  rw [val_eq_subtypeVal]
  exact point_mk _ _ _

@[simp]
theorem path_ofMappingPathFiber (y : MappingPathFiber p b) :
    (ofMappingPathFiber p b y).val.path = MoorePath.ofUnitPath y.val.2 := by
  rw [val_eq_subtypeVal]
  exact path_mk _ _ _

/-- Reading a path on the unit interval as a Moore path and back gives the path back. -/
@[simp]
theorem toMappingPathFiber_ofMappingPathFiber (y : MappingPathFiber p b) :
    toMappingPathFiber p b (ofMappingPathFiber p b y) = y :=
  Subtype.ext <| by
    rw [toMappingPathFiber_val, point_ofMappingPathFiber, path_ofMappingPathFiber,
      MoorePath.toUnitPath_ofUnitPath]

/-- The projection of the Moore fibre to `E`, `(e, γ) ↦ e`. -/
def proj : C(Fiber p b, E) :=
  ⟨fun x ↦ x.val.point, continuous_point.comp continuous_val⟩

@[simp]
theorem proj_apply (x : Fiber p b) : proj p b x = x.val.point :=
  (rfl)

/-- The homotopy from `ofMappingPathFiber ∘ toMappingPathFiber` to the identity of the Moore
fibre, through maps over `E`: `MoorePath.unitHomotopy` on the path, which keeps its end points,
with the point of `E` fixed. -/
def ofToMappingPathFiberHomotopy :
    ContinuousMap.HomotopyWith ((ofMappingPathFiber p b).comp (toMappingPathFiber p b))
      (ContinuousMap.id (Fiber p b)) fun f ↦ (proj p b).comp f = proj p b where
  toFun q := ⟨MooreReplacement.mk q.2.val.point (MoorePath.unitHomotopy (q.1, q.2.val.path))
      (by rw [MoorePath.unitHomotopy_source, source_path]),
    (congrArg MoorePath.target (path_mk _ _ _)).trans
      ((MoorePath.unitHomotopy_target _ _).trans (target_path_val q.2))⟩
  continuous_toFun := (continuous_mk (continuous_point.comp (continuous_val.comp continuous_snd))
    (MoorePath.unitHomotopy.continuous.comp
      (continuous_fst.prodMk (continuous_path.comp (continuous_val.comp continuous_snd))))
    fun q ↦ (MoorePath.unitHomotopy_source _ _).trans (source_path _)).subtype_mk _
  map_zero_left x := Subtype.ext <| by
    rw [← val_eq_subtypeVal (((ofMappingPathFiber p b).comp (toMappingPathFiber p b)) x)]
    refine MooreReplacement.ext ?_ ?_
    · rw [ContinuousMap.comp_apply, point_ofMappingPathFiber, toMappingPathFiber_val]
      exact point_mk _ _ _
    · rw [ContinuousMap.comp_apply, path_ofMappingPathFiber, toMappingPathFiber_val,
        ← MoorePath.unitHomotopy_apply_zero]
      exact path_mk _ _ _
  map_one_left x := Subtype.ext <| by
    rw [← val_eq_subtypeVal (ContinuousMap.id _ x)]
    exact MooreReplacement.ext (point_mk _ _ _)
      ((path_mk _ _ _).trans (MoorePath.unitHomotopy_apply_one _))
  prop' _ := ContinuousMap.ext fun _ ↦ by
    rw [ContinuousMap.comp_apply, proj_apply, proj_apply, val_eq_subtypeVal]
    exact point_mk _ _ _

/-- Every stage of `ofToMappingPathFiberHomotopy` keeps the point of `E`. -/
@[simp]
theorem point_ofToMappingPathFiberHomotopy (s : I) (x : Fiber p b) :
    (ofToMappingPathFiberHomotopy p b (s, x)).val.point = x.val.point := by
  rw [val_eq_subtypeVal]
  exact point_mk _ _ _

/-- **The Moore fibre and the mapping-path fibre are fibre homotopy equivalent over `E`**, by
`toMappingPathFiber` and `ofMappingPathFiber`: both maps keep the point of `E`, the composite on
the mapping-path fibre is the identity, and the composite on the Moore fibre is homotopic to the
identity through maps over `E` (`ofToMappingPathFiberHomotopy`). Forgetting `E`, it is a homotopy
equivalence `F' ≃ₕ MappingPathFiber p b` (`TauCeti.FiberHomotopyEquiv.toHomotopyEquiv`). -/
def fiberHomotopyEquivMappingPathFiber :
    FiberHomotopyEquiv (proj p b) (MappingPathFiber.proj p b) where
  toFun := toMappingPathFiber p b
  invFun := ofMappingPathFiber p b
  comp_toFun := ContinuousMap.ext fun x ↦ by
    rw [ContinuousMap.comp_apply, MappingPathFiber.proj_apply, toMappingPathFiber_val, proj_apply]
  comp_invFun := ContinuousMap.ext fun y ↦ by
    rw [ContinuousMap.comp_apply, MappingPathFiber.proj_apply, proj_apply,
      point_ofMappingPathFiber]
  left_inv := ⟨ofToMappingPathFiberHomotopy p b⟩
  right_inv := ⟨(ContinuousMap.HomotopyWith.refl
    (P := fun f ↦ (MappingPathFiber.proj p b).comp f = MappingPathFiber.proj p b) (.id _)
    (ContinuousMap.comp_id _)).cast
      (ContinuousMap.ext (toMappingPathFiber_ofMappingPathFiber p b)).symm rfl⟩

@[simp]
theorem fiberHomotopyEquivMappingPathFiber_toFun :
    (fiberHomotopyEquivMappingPathFiber p b).toFun = toMappingPathFiber p b :=
  (rfl)

@[simp]
theorem fiberHomotopyEquivMappingPathFiber_invFun :
    (fiberHomotopyEquivMappingPathFiber p b).invFun = ofMappingPathFiber p b :=
  (rfl)

/-! ### From the Moore action to concatenation -/

/-- The time at which the homotopy `actToMappingPathFiberHomotopy` at stage `τ` reads the Moore
path `γ · ω` at `s ∈ [0, 1]`, for `γ` of length `L` and `ω` of length `M`. At `τ = 0` it runs
through `γ` on `[0, 1/2]` and through `ω` on `[1/2, 1]`, as the concatenation of paths on the unit
interval does; at `τ = 1` it runs through `γ · ω` at constant speed. -/
private def concatTime (τ s : I) (L M : ℝ≥0) : ℝ≥0 :=
  toNNReal (σ τ) * (L * min (2 * toNNReal s) 1 + M * (2 * toNNReal s - 1)) +
    toNNReal τ * ((L + M) * toNNReal s)

private theorem continuous_concatTime :
    Continuous fun q : (I × I) × ℝ≥0 × ℝ≥0 ↦ concatTime q.1.1 q.1.2 q.2.1 q.2.2 := by
  unfold concatTime
  fun_prop

private theorem continuous_concatTime_right (τ : I) (L M : ℝ≥0) :
    Continuous fun s ↦ concatTime τ s L M := by
  unfold concatTime
  fun_prop

@[simp]
private theorem concatTime_zero_right (τ : I) (L M : ℝ≥0) : concatTime τ 0 L M = 0 := by
  simp [concatTime]

@[simp]
private theorem concatTime_one_right (τ : I) (L M : ℝ≥0) : concatTime τ 1 L M = L + M := by
  have h : (2 : ℝ≥0) - 1 = 1 := by
    rw [← one_add_one_eq_two, add_tsub_cancel_right]
  rw [concatTime, toNNReal_one, mul_one, h, min_eq_right one_le_two]
  simp only [mul_one]
  rw [← add_mul, toNNReal_symm_add_toNNReal, one_mul]

private theorem concatTime_zero_left (s : I) (L M : ℝ≥0) :
    concatTime 0 s L M = L * min (2 * toNNReal s) 1 + M * (2 * toNNReal s - 1) := by
  simp [concatTime]

private theorem concatTime_one_left (s : I) (L M : ℝ≥0) :
    concatTime 1 s L M = (L + M) * toNNReal s := by
  simp [concatTime]

/-- The Moore action followed by the comparison: `(x, ω) ↦ toMappingPathFiber (x · ω)`. -/
def actToMappingPathFiber : C(Fiber p b × MooreLoopSpace B b, MappingPathFiber p b) :=
  (toMappingPathFiber p b).comp ⟨fun q ↦ q.1.act q.2, continuous_act⟩

@[simp]
theorem actToMappingPathFiber_apply (x : Fiber p b) (ω : MooreLoopSpace B b) :
    actToMappingPathFiber p b (x, ω) = toMappingPathFiber p b (x.act ω) :=
  (rfl)

/-- The comparison followed by concatenation: `(x, ω)` goes to the comparison of `x`, followed by
the loop `ω.toPath` on the unit interval. -/
def transLoopToMappingPathFiber : C(Fiber p b × MooreLoopSpace B b, MappingPathFiber p b) :=
  (MappingPathFiber.transLoop p b).comp
    ((toMappingPathFiber p b).prodMap ⟨MooreLoopSpace.toPath, MooreLoopSpace.continuous_toPath⟩)

@[simp]
theorem transLoopToMappingPathFiber_apply (x : Fiber p b) (ω : MooreLoopSpace B b) :
    transLoopToMappingPathFiber p b (x, ω) =
      MappingPathFiber.transLoop p b (toMappingPathFiber p b x, ω.toPath) :=
  (rfl)

private theorem continuous_act_path :
    Continuous fun q : Fiber p b × MooreLoopSpace B b ↦ (q.1.act q.2).val.path :=
  continuous_path.comp (continuous_val.comp continuous_act)

private theorem act_path_apply_concatTime_zero (x : Fiber p b) (ω : MooreLoopSpace B b) (s : I) :
    (x.act ω).val.path (concatTime 0 s x.val.path.length ω.length) =
      ((MappingPathFiber.toPath p b (toMappingPathFiber p b x)).trans ω.toPath) s := by
  rw [concatTime_zero_left, Path.trans_apply, path_act]
  split_ifs with h
  · -- On `[0, 1/2]` the reparametrization stays in `γ`, at double speed.
    have h₂ : 2 * toNNReal s ≤ 1 := by
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_toNNReal, NNReal.coe_ofNat, NNReal.coe_one]
      linarith
    have hL : x.val.path.length * (2 * toNNReal s) ≤ x.val.path.length :=
      mul_le_of_le_one_right zero_le h₂
    rw [min_eq_left h₂, tsub_eq_zero_of_le h₂, mul_zero, add_zero,
      MoorePath.trans_apply_of_le _ _ _ hL, MappingPathFiber.coe_toPath, toMappingPathFiber_val,
      MoorePath.toUnitPath_apply]
    congr 2
  · -- On `[1/2, 1]` it runs through `ω`, after the whole of `γ`.
    have h₂ : 1 ≤ 2 * toNNReal s := by
      rw [← NNReal.coe_le_coe, NNReal.coe_mul, coe_toNNReal, NNReal.coe_ofNat, NNReal.coe_one]
      linarith
    rw [min_eq_right h₂, mul_one, MoorePath.trans_apply_length_add, MooreLoopSpace.toPath_apply,
      MooreLoopSpace.length_toMoorePath]
    congr 2
    ext
    simp [NNReal.coe_sub h₂]

/-- **The comparison intertwines the Moore action with concatenation, up to homotopy**: the
homotopy from `(x, ω) ↦ toMappingPathFiber x` followed by the loop `ω.toPath` to
`(x, ω) ↦ toMappingPathFiber (x · ω)`, continuous in `(x, ω)` and keeping the point of `E`
(`TauCeti.MooreReplacement.Fiber.actToMappingPathFiberHomotopy_val_fst`). At each stage it reads
the Moore path `γ · ω` along a reparametrization of the unit interval fixing both ends. -/
def actToMappingPathFiberHomotopy :
    ContinuousMap.Homotopy (transLoopToMappingPathFiber p b) (actToMappingPathFiber p b) where
  toFun q := ⟨(q.2.1.val.point,
    ⟨fun s ↦ (q.2.1.act q.2.2).val.path
        (concatTime q.1 s q.2.1.val.path.length q.2.2.length),
      (q.2.1.act q.2.2).val.path.continuous.comp (continuous_concatTime_right _ _ _)⟩),
    by
      -- The path at `s` is the Moore path `γ · ω` read at `concatTime q.1 s L M`; `change` exposes
      -- this from the bundled `ContinuousMap` so that the end point lemmas apply.
      change (q.2.1.act q.2.2).val.path (concatTime _ 0 _ _) = _
      rw [concatTime_zero_right, ← MoorePath.source_def, source_path, point_act],
    by
      -- As above, read the bundled path at `s = 1`.
      change (q.2.1.act q.2.2).val.path (concatTime _ 1 _ _) = _
      rw [concatTime_one_right, ← MooreLoopSpace.length_toMoorePath, ← MoorePath.length_trans
        _ _ (by simp), ← path_act, ← MoorePath.target_def, target_path_val]⟩
  continuous_toFun := by
    refine ((continuous_point.comp (continuous_val.comp (continuous_fst.comp
      continuous_snd))).prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    -- Uncurried, the map is `((τ, (x, ω)), s) ↦ (x · ω).path (concatTime τ s L M)`.
    exact MoorePath.continuous_eval.comp
      (((continuous_act_path p b).comp (continuous_snd.comp continuous_fst)).prodMk
        (continuous_concatTime.comp
          (((continuous_fst.comp continuous_fst).prodMk continuous_snd).prodMk
          ((MoorePath.continuous_length.comp (continuous_path.comp (continuous_val.comp
            (continuous_fst.comp (continuous_snd.comp continuous_fst))))).prodMk
            (MooreLoopSpace.continuous_length.comp
              (continuous_snd.comp (continuous_snd.comp continuous_fst)))))))
  map_zero_left q := by
    apply Subtype.ext
    rw [transLoopToMappingPathFiber_apply]
    refine Prod.ext ?_ (ContinuousMap.ext fun s ↦ ?_)
    · rw [MappingPathFiber.transLoop_val_fst, toMappingPathFiber_val]
    · rw [MappingPathFiber.transLoop_val_snd, Path.coe_toContinuousMap]
      exact act_path_apply_concatTime_zero p b q.1 q.2 s
  map_one_left q := by
    apply Subtype.ext
    rw [actToMappingPathFiber_apply, toMappingPathFiber_val]
    refine Prod.ext ?_ (ContinuousMap.ext fun s ↦ ?_)
    · exact (point_act q.1 q.2).symm
    · -- Unbundle the path of the homotopy at stage `1`, read at `s`.
      change (q.1.act q.2).val.path (concatTime 1 s _ _) =
        (q.1.act q.2).val.path.toUnitPath s
      rw [concatTime_one_left, MoorePath.toUnitPath_apply, path_act, MoorePath.length_trans,
        MooreLoopSpace.length_toMoorePath]

/-- Every stage of `actToMappingPathFiberHomotopy` keeps the point of `E`. -/
@[simp]
theorem actToMappingPathFiberHomotopy_val_fst (τ : I) (x : Fiber p b) (ω : MooreLoopSpace B b) :
    (actToMappingPathFiberHomotopy p b (τ, (x, ω))).val.1 = x.val.point := by
  simp only [actToMappingPathFiberHomotopy]
  rfl

/-! ### From concatenation to the Moore action -/

/-- Concatenation followed by the comparison: `(y, ℓ) ↦ ofMappingPathFiber (y.trans ℓ)`, whose
Moore path has length one. -/
def ofMappingPathFiberTransLoop : C(MappingPathFiber p b × Path b b, Fiber p b) :=
  (ofMappingPathFiber p b).comp (MappingPathFiber.transLoop p b)

@[simp]
theorem ofMappingPathFiberTransLoop_apply (y : MappingPathFiber p b) (ℓ : Path b b) :
    ofMappingPathFiberTransLoop p b (y, ℓ) =
      ofMappingPathFiber p b (MappingPathFiber.transLoop p b (y, ℓ)) :=
  (rfl)

/-- The comparison followed by the Moore action:
`(y, ℓ) ↦ ofMappingPathFiber y · ℓ.toMooreLoop`, whose Moore path has length two. -/
def actOfMappingPathFiber : C(MappingPathFiber p b × Path b b, Fiber p b) :=
  ⟨fun q ↦ (ofMappingPathFiber p b q.1).act q.2.toMooreLoop,
    continuous_act.comp (((ofMappingPathFiber p b).continuous.comp continuous_fst).prodMk
      (Path.continuous_toMooreLoop.comp continuous_snd))⟩

@[simp]
theorem actOfMappingPathFiber_apply (y : MappingPathFiber p b) (ℓ : Path b b) :
    actOfMappingPathFiber p b (y, ℓ) = (ofMappingPathFiber p b y).act ℓ.toMooreLoop :=
  (rfl)

private theorem one_add_toNNReal_ne_zero (τ : I) : 1 + toNNReal τ ≠ 0 :=
  (add_pos_of_pos_of_nonneg one_pos zero_le).ne'

/-- **The comparison intertwines concatenation with the Moore action, up to homotopy**: the
homotopy from `(y, ℓ) ↦ ofMappingPathFiber (y.trans ℓ)` to
`(y, ℓ) ↦ ofMappingPathFiber y · ℓ.toMooreLoop`, continuous in `(y, ℓ)` and keeping the point of
`E` (`TauCeti.MooreReplacement.Fiber.point_actOfMappingPathFiberHomotopy`). It stretches the Moore
path of `y.trans ℓ` from length one to length two (`Path.transMoorePath_eq_rescale`). -/
def actOfMappingPathFiberHomotopy :
    ContinuousMap.Homotopy (ofMappingPathFiberTransLoop p b) (actOfMappingPathFiber p b) where
  toFun q := ⟨MooreReplacement.mk q.2.1.val.1
      ((MoorePath.ofUnitPath (MappingPathFiber.transLoop p b q.2).val.2).rescale
        (1 + toNNReal q.1))
      (by rw [MoorePath.source_rescale, MoorePath.source_ofUnitPath,
        (MappingPathFiber.transLoop p b q.2).property.1, MappingPathFiber.transLoop_val_fst]),
    (congrArg MoorePath.target (path_mk _ _ _)).trans (by
      rw [MoorePath.target_rescale _ (one_add_toNNReal_ne_zero q.1), MoorePath.target_ofUnitPath,
        (MappingPathFiber.transLoop p b q.2).property.2])⟩
  continuous_toFun := (continuous_mk (continuous_subtypeVal.fst.comp (continuous_fst.comp
    continuous_snd))
    ((MoorePath.continuous_ofUnitPath.comp (continuous_subtypeVal.snd.comp
      ((MappingPathFiber.transLoop p b).continuous.comp continuous_snd))).moorePath_rescale
      (continuous_const.add (toNNReal_continuous.comp continuous_fst))
      fun q ↦ one_add_toNNReal_ne_zero q.1)
    fun q ↦ (MoorePath.source_rescale _ _).trans ((MoorePath.source_ofUnitPath _).trans
      ((MappingPathFiber.transLoop p b q.2).property.1.trans
        (congrArg p (MappingPathFiber.transLoop_val_fst p b _ _))))).subtype_mk _
  map_zero_left := by
    rintro ⟨y, ℓ⟩
    apply Subtype.ext
    rw [← val_eq_subtypeVal (ofMappingPathFiberTransLoop p b (y, ℓ)),
      ofMappingPathFiberTransLoop_apply]
    refine MooreReplacement.ext ((point_mk _ _ _).trans ?_) ((path_mk _ _ _).trans ?_)
    · rw [point_ofMappingPathFiber, MappingPathFiber.transLoop_val_fst]
    · rw [path_ofMappingPathFiber, toNNReal_zero, add_zero]
      conv_lhs =>
        rw [← MoorePath.length_ofUnitPath (MappingPathFiber.transLoop p b (y, ℓ)).val.2]
      exact MoorePath.rescale_length _
  map_one_left := by
    rintro ⟨y, ℓ⟩
    -- `Path.toMoorePath` is `MoorePath.ofUnitPath` of the underlying map.
    have hγ {x y : B} (γ : Path x y) : γ.toMoorePath = MoorePath.ofUnitPath γ.toContinuousMap :=
      MoorePath.ext (by simp) fun t ↦ by
        rw [Path.toMoorePath_apply, MoorePath.ofUnitPath_apply]
        rfl
    apply Subtype.ext
    rw [← val_eq_subtypeVal (actOfMappingPathFiber p b (y, ℓ)), actOfMappingPathFiber_apply]
    refine MooreReplacement.ext ((point_mk _ _ _).trans ?_) ((path_mk _ _ _).trans ?_)
    · rw [point_act, point_ofMappingPathFiber]
    · rw [toNNReal_one, one_add_one_eq_two, MappingPathFiber.transLoop_val_snd,
        ← hγ, ← Path.transMoorePath_eq_rescale, path_act]
      congr 1
      · rw [path_ofMappingPathFiber, hγ]
        exact congrArg MoorePath.ofUnitPath (ContinuousMap.ext fun s ↦ by simp)
      · exact (Path.toMoorePath_toMooreLoop ℓ).symm

/-- Every stage of `actOfMappingPathFiberHomotopy` keeps the point of `E`. -/
@[simp]
theorem point_actOfMappingPathFiberHomotopy (τ : I) (y : MappingPathFiber p b) (ℓ : Path b b) :
    (actOfMappingPathFiberHomotopy p b (τ, (y, ℓ))).val.point = y.val.1 := by
  rw [val_eq_subtypeVal]
  exact point_mk _ _ _

end TauCeti.MooreReplacement.Fiber
