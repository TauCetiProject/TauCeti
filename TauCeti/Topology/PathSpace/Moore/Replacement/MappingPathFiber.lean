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

* `TauCeti.MooreReplacement.Fiber.toMappingPathFiberActHomotopy`: from `(x, ω)` to the
  mapping-path fibre, concatenating the comparison of `x` with the loop of `ω` is homotopic to
  comparing `x · ω`. On the path it is the homotopy `TauCeti.MoorePath.toUnitPathTransHomotopy`
  for composable Moore paths, which reads `γ · ω` along a reparametrization of the unit interval
  that runs at constant speed at one end and through `γ` on `[0, 1/2]` and `ω` on `[1/2, 1]` at
  the other.
* `TauCeti.MooreReplacement.Fiber.actOfMappingPathFiberHomotopy`: from `(y, ℓ)` to the Moore fibre,
  the comparison of `y.trans ℓ`, a Moore path of length one, is homotopic to the comparison of `y`
  acted on by the Moore loop of `ℓ`, of length two. On the path it is
  `Path.transMoorePathHomotopy`, which stretches the duration from one to two.

These are the fibre forms of the multiplicativity of the comparison of loop spaces up to homotopy
(`TauCeti.MooreLoopSpace.mulToPathHomotopy`, `Path.transMooreLoopHomotopy`): constructions made
with the strict Moore action on `F'` agree, up to these homotopies, with their fixed-interval
counterparts on the mapping-path fibre.

## Main definitions

* `TauCeti.MooreReplacement.Fiber.toMappingPathFiber`,
  `TauCeti.MooreReplacement.Fiber.ofMappingPathFiber`: the comparison maps.
* `TauCeti.MooreReplacement.Fiber.fiberHomotopyEquivMappingPathFiber`: the fibre homotopy
  equivalence over `E` between `F'` and `MappingPathFiber p b`.
* `TauCeti.MooreReplacement.Fiber.toMappingPathFiberActHomotopy`,
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

/-- The path of `ofToMappingPathFiberHomotopy` at stage `s` is `MoorePath.unitHomotopy` at `s`. -/
@[simp]
theorem path_ofToMappingPathFiberHomotopy (s : I) (x : Fiber p b) :
    (ofToMappingPathFiberHomotopy p b (s, x)).val.path =
      MoorePath.unitHomotopy (s, x.val.path) := by
  rw [val_eq_subtypeVal]
  exact path_mk _ _ _

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

/-- The Moore action followed by the comparison: `(x, ω) ↦ toMappingPathFiber (x · ω)`. -/
def toMappingPathFiberAct : C(Fiber p b × MooreLoopSpace B b, MappingPathFiber p b) :=
  (toMappingPathFiber p b).comp ⟨fun q ↦ q.1.act q.2, continuous_act⟩

@[simp]
theorem toMappingPathFiberAct_apply (x : Fiber p b) (ω : MooreLoopSpace B b) :
    toMappingPathFiberAct p b (x, ω) = toMappingPathFiber p b (x.act ω) :=
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

/-- **The comparison intertwines the Moore action with concatenation, up to homotopy**: the
homotopy from `(x, ω) ↦ toMappingPathFiber x` followed by the loop `ω.toPath` to
`(x, ω) ↦ toMappingPathFiber (x · ω)`, continuous in `(x, ω)` and keeping the point of `E`
(`TauCeti.MooreReplacement.Fiber.toMappingPathFiberActHomotopy_val_fst`). On the path it is
`TauCeti.MoorePath.toUnitPathTransHomotopy` applied to the path of `x` and the Moore path of `ω`
(`TauCeti.MooreReplacement.Fiber.toMappingPathFiberActHomotopy_val_snd`). -/
def toMappingPathFiberActHomotopy :
    ContinuousMap.Homotopy (transLoopToMappingPathFiber p b) (toMappingPathFiberAct p b) where
  toFun q := ⟨(q.2.1.val.point,
      MoorePath.toUnitPathTransHomotopy (q.1, ⟨(q.2.1.val.path, q.2.2.toMoorePath), by simp⟩)),
    (MoorePath.toUnitPathTransHomotopy_apply_zero_right _ _).trans (source_path _),
    (MoorePath.toUnitPathTransHomotopy_apply_one_right _ _).trans (by simp)⟩
  continuous_toFun := by
    refine (Continuous.prodMk ?_ ?_).subtype_mk _
    · exact continuous_point.comp (continuous_val.comp (continuous_fst.comp continuous_snd))
    refine (MoorePath.toUnitPathTransHomotopy (X := B)).continuous.comp
      (continuous_fst.prodMk ((Continuous.prodMk ?_ ?_).subtype_mk _))
    · exact continuous_path.comp (continuous_val.comp (continuous_fst.comp continuous_snd))
    · exact MooreLoopSpace.continuous_toMoorePath.comp (continuous_snd.comp continuous_snd)
  map_zero_left q := by
    apply Subtype.ext
    rw [transLoopToMappingPathFiber_apply]
    refine Prod.ext ?_ ?_
    · rw [MappingPathFiber.transLoop_val_fst, toMappingPathFiber_val]
    · dsimp only
      rw [ContinuousMap.Homotopy.apply_zero, MoorePath.transToUnitPath_apply,
        MappingPathFiber.transLoop_val_snd]
      -- Both sides concatenate paths with the same underlying maps.
      ext s
      simp only [Path.coe_toContinuousMap, Path.trans_apply, MappingPathFiber.coe_toPath,
        toMappingPathFiber_val, MoorePath.toUnitPath_apply, MoorePath.toPath_apply, Path.cast_coe,
        MooreLoopSpace.toPath_apply]
  map_one_left q := by
    apply Subtype.ext
    rw [toMappingPathFiberAct_apply, toMappingPathFiber_val]
    refine Prod.ext (point_act q.1 q.2).symm ?_
    dsimp only
    rw [ContinuousMap.Homotopy.apply_one, MoorePath.toUnitPathTrans_apply, path_act]

/-- Every stage of `toMappingPathFiberActHomotopy` keeps the point of `E`. -/
@[simp]
theorem toMappingPathFiberActHomotopy_val_fst (τ : I) (x : Fiber p b) (ω : MooreLoopSpace B b) :
    (toMappingPathFiberActHomotopy p b (τ, (x, ω))).val.1 = x.val.point :=
  (rfl)

/-- The path of `toMappingPathFiberActHomotopy` at stage `τ` is
`TauCeti.MoorePath.toUnitPathTransHomotopy` at `τ` on the path of `x` and the Moore path of `ω`. -/
@[simp]
theorem toMappingPathFiberActHomotopy_val_snd (τ : I) (x : Fiber p b) (ω : MooreLoopSpace B b) :
    (toMappingPathFiberActHomotopy p b (τ, (x, ω))).val.2 =
      MoorePath.toUnitPathTransHomotopy (τ, ⟨(x.val.path, ω.toMoorePath), by simp⟩) :=
  (rfl)

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

/-- **The comparison intertwines concatenation with the Moore action, up to homotopy**: the
homotopy from `(y, ℓ) ↦ ofMappingPathFiber (y.trans ℓ)` to
`(y, ℓ) ↦ ofMappingPathFiber y · ℓ.toMooreLoop`, continuous in `(y, ℓ)` and keeping the point of
`E` (`TauCeti.MooreReplacement.Fiber.point_actOfMappingPathFiberHomotopy`). On the path it is
`Path.transMoorePathHomotopy` applied to the path of `y` and the loop `ℓ`
(`TauCeti.MooreReplacement.Fiber.path_actOfMappingPathFiberHomotopy`), which stretches the Moore
path of `y.trans ℓ` from length one to length two. -/
def actOfMappingPathFiberHomotopy :
    ContinuousMap.Homotopy (ofMappingPathFiberTransLoop p b) (actOfMappingPathFiber p b) where
  toFun q := ⟨MooreReplacement.mk q.2.1.val.1
      (Path.transMoorePathHomotopy _ b b (q.1, (MappingPathFiber.toPath p b q.2.1, q.2.2)))
      (Path.transMoorePathHomotopy_source _ _),
    (congrArg MoorePath.target (path_mk _ _ _)).trans (Path.transMoorePathHomotopy_target _ _)⟩
  continuous_toFun := by
    refine (continuous_mk (continuous_subtypeVal.fst.comp (continuous_fst.comp continuous_snd)) ?_
      fun q ↦ Path.transMoorePathHomotopy_source _ _).subtype_mk _
    -- The start `p y` of the path varies with `y`, so continuity is read off the formula of
    -- `Path.transMoorePathHomotopy`, the Moore path of `y.trans ℓ` rescaled to length `1 + τ`.
    simp only [Path.transMoorePathHomotopy_apply, Path.toMoorePath_eq_ofUnitPath,
      ← MappingPathFiber.transLoop_val_snd]
    exact (MoorePath.continuous_ofUnitPath.comp (continuous_subtypeVal.snd.comp
      ((MappingPathFiber.transLoop p b).continuous.comp continuous_snd))).moorePath_rescale
      (continuous_const.add (toNNReal_continuous.comp continuous_fst))
      fun _ ↦ (add_pos_of_pos_of_nonneg one_pos zero_le).ne'
  map_zero_left := by
    rintro ⟨y, ℓ⟩
    apply Subtype.ext
    rw [← val_eq_subtypeVal (ofMappingPathFiberTransLoop p b (y, ℓ)),
      ofMappingPathFiberTransLoop_apply]
    refine MooreReplacement.ext ((point_mk _ _ _).trans ?_) ((path_mk _ _ _).trans ?_)
    · rw [point_ofMappingPathFiber, MappingPathFiber.transLoop_val_fst]
    · rw [ContinuousMap.Homotopy.apply_zero, Path.moorePathTrans_apply, path_ofMappingPathFiber,
        MappingPathFiber.transLoop_val_snd, Path.toMoorePath_eq_ofUnitPath]
  map_one_left := by
    rintro ⟨y, ℓ⟩
    apply Subtype.ext
    rw [← val_eq_subtypeVal (actOfMappingPathFiber p b (y, ℓ)), actOfMappingPathFiber_apply]
    refine MooreReplacement.ext ((point_mk _ _ _).trans ?_) ((path_mk _ _ _).trans ?_)
    · rw [point_act, point_ofMappingPathFiber]
    · rw [ContinuousMap.Homotopy.apply_one, Path.transMoorePath_apply, path_act]
      congr 1
      · rw [path_ofMappingPathFiber, Path.toMoorePath_eq_ofUnitPath,
          MappingPathFiber.toContinuousMap_toPath]
      · exact (Path.toMoorePath_toMooreLoop ℓ).symm

/-- Every stage of `actOfMappingPathFiberHomotopy` keeps the point of `E`. -/
@[simp]
theorem point_actOfMappingPathFiberHomotopy (τ : I) (y : MappingPathFiber p b) (ℓ : Path b b) :
    (actOfMappingPathFiberHomotopy p b (τ, (y, ℓ))).val.point = y.val.1 := by
  rw [val_eq_subtypeVal]
  exact point_mk _ _ _

/-- The path of `actOfMappingPathFiberHomotopy` at stage `τ` is `Path.transMoorePathHomotopy` at
`τ` on the path of `y` and the loop `ℓ`. -/
@[simp]
theorem path_actOfMappingPathFiberHomotopy (τ : I) (y : MappingPathFiber p b) (ℓ : Path b b) :
    (actOfMappingPathFiberHomotopy p b (τ, (y, ℓ))).val.path =
      Path.transMoorePathHomotopy (p y.val.1) b b (τ, (MappingPathFiber.toPath p b y, ℓ)) := by
  rw [val_eq_subtypeVal]
  exact path_mk _ _ _

/-! ### The compatibilities up to homotopy -/

/-- The comparison followed by concatenation is homotopic to the Moore action followed by the
comparison (`toMappingPathFiberActHomotopy`). -/
theorem homotopic_transLoopToMappingPathFiber_toMappingPathFiberAct :
    (transLoopToMappingPathFiber p b).Homotopic (toMappingPathFiberAct p b) :=
  ⟨toMappingPathFiberActHomotopy p b⟩

/-- Concatenation followed by the comparison is homotopic to the comparison followed by the Moore
action (`actOfMappingPathFiberHomotopy`). -/
theorem homotopic_ofMappingPathFiberTransLoop_actOfMappingPathFiber :
    (ofMappingPathFiberTransLoop p b).Homotopic (actOfMappingPathFiber p b) :=
  ⟨actOfMappingPathFiberHomotopy p b⟩

/-- The Moore path of the path of a point `(e, γ)` of the mapping-path fibre is
`MoorePath.ofUnitPath γ`. -/
@[simp]
theorem _root_.TauCeti.MappingPathFiber.toMoorePath_toPath (y : MappingPathFiber p b) :
    (MappingPathFiber.toPath p b y).toMoorePath = MoorePath.ofUnitPath y.val.2 := by
  rw [Path.toMoorePath_eq_ofUnitPath, MappingPathFiber.toContinuousMap_toPath]

end TauCeti.MooreReplacement.Fiber
