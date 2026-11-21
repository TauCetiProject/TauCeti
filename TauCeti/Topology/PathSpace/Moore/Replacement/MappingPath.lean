/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.MappingPath.Fiber
public import TauCeti.Topology.PathSpace.Moore.Comparison.Trans
public import TauCeti.Topology.PathSpace.Moore.Replacement.Basic

/-!
# The Moore-path replacement and the mapping-path fibre

For a continuous map `p : E → B` and a point `b ∈ B`, two models of the homotopy fibre of `p`
over `b` are in use. The fibre `F' = MooreReplacement.Fiber p b` of the Moore-path replacement
consists of the pairs `(e, γ)` of a point `e ∈ E` and a Moore path `γ` from `p e` to `b`; the
mapping-path fibre `MappingPathFiber p b` consists of the pairs `(e, γ)` with `γ` a path on the
unit interval from `p e` to `b`. The Moore loops at `b` act on `F'` strictly, by concatenation
`(e, γ) · ω = (e, γ · ω)`. The loops on the unit interval at `b` act on the mapping-path fibre
only up to homotopy, by concatenation `(e, γ) · ℓ = (e, γ.trans ℓ)`
(`TauCeti.MappingPathFiber.transLoop`), which is associative only up to reparametrization.

This file compares the two models and their actions. Reparametrizing Moore paths to the unit
interval and back (`TauCeti.MoorePath.toUnitPath`, `TauCeti.MoorePath.ofUnitPath`) gives maps
`F' ⇄ MappingPathFiber p b` over `E`, which form a homotopy equivalence
(`TauCeti.MooreReplacement.Fiber.homotopyEquivMappingPathFiber`): one composite is the identity
and the other is homotopic to the identity through maps over `E`. Under these maps and the
comparison `MooreLoopSpace B b ⇄ Path b b` of the loop spaces
(`TauCeti.MooreLoopSpace.toPath`, `Path.toMooreLoop`), the two actions correspond up to specified
homotopies, continuous in the point of the fibre and in the loop:

* `TauCeti.MooreReplacement.Fiber.actHomotopy`: normalizing `x · ω` to the unit interval is
  homotopic to concatenating the normalizations of `x` and of `ω`;
* `TauCeti.MooreReplacement.Fiber.transLoopHomotopy`: the Moore form of `y.trans ℓ` is homotopic
  to the Moore form of `y` acted on by the Moore loop of `ℓ`.

All the homotopies fix the point of `E`. The fixed-interval form is the one in which mapping-space
homeomorphisms such as `Map_*(S¹, X) ≅ Ω X` are stated, and the Moore form the one whose strict
action makes the chains on `F'` a DG module over the chains on the Moore loops; the comparison
lets results move between the two.

## Main definitions

* `TauCeti.MooreReplacement.Fiber.toMappingPathFiber`: the map `F' → MappingPathFiber p b`,
  `(e, γ) ↦ (e, γ.toUnitPath)`.
* `TauCeti.MooreReplacement.Fiber.ofMappingPathFiber`: the map `MappingPathFiber p b → F'`,
  `(e, γ) ↦ (e, ofUnitPath γ)`.
* `TauCeti.MooreReplacement.Fiber.homotopyEquivMappingPathFiber`: the homotopy equivalence
  `F' ≃ₕ MappingPathFiber p b` formed by them.
* `TauCeti.MooreReplacement.Fiber.actHomotopy`,
  `TauCeti.MooreReplacement.Fiber.transLoopHomotopy`: the compatibility of the comparison with the
  actions of the loop spaces.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
-/

public noncomputable section

open scoped NNReal ContinuousMap
open unitInterval

universe u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- The Moore path of the path of a point `(e, γ)` of the mapping-path fibre is
`MoorePath.ofUnitPath γ`. -/
@[simp]
theorem MappingPathFiber.toMoorePath_toPath (p : C(E, B)) (b : B) (y : MappingPathFiber p b) :
    (MappingPathFiber.toPath p b y).toMoorePath = MoorePath.ofUnitPath y.val.2 := by
  rw [Path.toMoorePath_def, MappingPathFiber.toContinuousMap_toPath]

namespace MooreReplacement

namespace Fiber

variable {p : C(E, B)} {b : B}

/-! ### The comparison maps -/

/-- The fibre of the Moore-path replacement to the mapping-path fibre: the Moore path of a point
`(e, γ)` is reparametrized to the unit interval, `(e, γ) ↦ (e, s ↦ γ (L s))` for `γ` of length
`L`. -/
def toMappingPathFiber : C(Fiber p b, MappingPathFiber p b) where
  toFun x := ⟨(x.val.point, x.val.path.toUnitPath),
    by rw [MoorePath.toUnitPath_zero, source_path], by rw [MoorePath.toUnitPath_one,
      target_path_val]⟩
  continuous_toFun := ((continuous_point.comp continuous_val).prodMk
    (MoorePath.continuous_toUnitPath.comp (continuous_path.comp continuous_val))).subtype_mk _

@[simp]
theorem toMappingPathFiber_val (x : Fiber p b) :
    (toMappingPathFiber x).val = (x.val.point, x.val.path.toUnitPath) :=
  (rfl)

/-- The mapping-path fibre to the fibre of the Moore-path replacement: the path of a point
`(e, γ)` becomes a Moore path of length one, `(e, γ) ↦ (e, ofUnitPath γ)`. -/
def ofMappingPathFiber : C(MappingPathFiber p b, Fiber p b) where
  toFun y := mk' (MooreReplacement.mk y.val.1 (MoorePath.ofUnitPath y.val.2)
    (by rw [MoorePath.source_ofUnitPath, y.property.1]))
    (by rw [path_mk, MoorePath.target_ofUnitPath, y.property.2])
  continuous_toFun := by
    refine continuous_mk' (continuous_mk ?_ ?_ _) _ <;> fun_prop

@[simp]
theorem point_ofMappingPathFiber (y : MappingPathFiber p b) :
    (ofMappingPathFiber y).val.point = y.val.1 := by
  simp [ofMappingPathFiber]

@[simp]
theorem path_ofMappingPathFiber (y : MappingPathFiber p b) :
    (ofMappingPathFiber y).val.path = MoorePath.ofUnitPath y.val.2 := by
  simp [ofMappingPathFiber]

/-- A point of the mapping-path fibre, sent to the Moore model and back, is unchanged. -/
@[simp]
theorem toMappingPathFiber_ofMappingPathFiber (y : MappingPathFiber p b) :
    toMappingPathFiber (ofMappingPathFiber y) = y :=
  Subtype.ext (Prod.ext (point_ofMappingPathFiber y) (by
    rw [toMappingPathFiber_val, path_ofMappingPathFiber, MoorePath.toUnitPath_ofUnitPath]))

/-- The homotopy from `ofMappingPathFiber ∘ toMappingPathFiber` to the identity of the fibre of
the Moore-path replacement: `MoorePath.unitHomotopy` on the Moore path of each point. It keeps
the point of `E` (`point_unitHomotopy`). -/
def unitHomotopy :
    ContinuousMap.Homotopy ((ofMappingPathFiber (p := p) (b := b)).comp toMappingPathFiber)
      (ContinuousMap.id (Fiber p b)) where
  toFun q := mk' (MooreReplacement.mk q.2.val.point (MoorePath.unitHomotopy (q.1, q.2.val.path))
    (by rw [MoorePath.unitHomotopy_source, source_path]))
    (by rw [path_mk, MoorePath.unitHomotopy_target, target_path_val])
  continuous_toFun := by
    refine continuous_mk' (continuous_mk ?_ ?_ _) _ <;> fun_prop
  map_zero_left x := ext (MooreReplacement.ext (by simp) (by simp [path_ofMappingPathFiber]))
  map_one_left x := ext (MooreReplacement.ext (by simp) (by simp))

/-- Every stage of `unitHomotopy` is the point of `E` of `x` with the Moore path of `x` deformed
by `MoorePath.unitHomotopy`. -/
theorem val_unitHomotopy (s : I) (x : Fiber p b) :
    (unitHomotopy (s, x)).val = MooreReplacement.mk x.val.point
      (MoorePath.unitHomotopy (s, x.val.path))
      (by rw [MoorePath.unitHomotopy_source, source_path]) :=
  val_mk' _ _

@[simp]
theorem point_unitHomotopy (s : I) (x : Fiber p b) :
    (unitHomotopy (s, x)).val.point = x.val.point := by
  rw [val_unitHomotopy, point_mk]

/-- **The fibre of the Moore-path replacement is homotopy equivalent to the mapping-path
fibre**, by reparametrization to the unit interval and back. -/
def homotopyEquivMappingPathFiber (p : C(E, B)) (b : B) : Fiber p b ≃ₕ MappingPathFiber p b where
  toFun := toMappingPathFiber
  invFun := ofMappingPathFiber
  left_inv := ⟨unitHomotopy⟩
  right_inv := ⟨(ContinuousMap.Homotopy.refl _).cast rfl
    (ContinuousMap.ext toMappingPathFiber_ofMappingPathFiber)⟩

@[simp]
theorem homotopyEquivMappingPathFiber_apply (x : Fiber p b) :
    homotopyEquivMappingPathFiber p b x = toMappingPathFiber x :=
  (rfl)

@[simp]
theorem homotopyEquivMappingPathFiber_symm_apply (y : MappingPathFiber p b) :
    (homotopyEquivMappingPathFiber p b).symm y = ofMappingPathFiber y :=
  (rfl)

/-! ### Compatibility with the actions -/

/-- The fibre of the Moore-path replacement with the action of the Moore loops, normalized to the
mapping-path fibre: `(x, ω) ↦ toMappingPathFiber (x · ω)`. -/
def toMappingPathFiberAct (p : C(E, B)) (b : B) :
    C(Fiber p b × MooreLoopSpace B b, MappingPathFiber p b) :=
  toMappingPathFiber.comp ⟨fun q ↦ q.1.act q.2, continuous_act⟩

@[simp]
theorem toMappingPathFiberAct_apply (q : Fiber p b × MooreLoopSpace B b) :
    toMappingPathFiberAct p b q = toMappingPathFiber (q.1.act q.2) :=
  (rfl)

/-- The fibre of the Moore-path replacement and the Moore loops, normalized to the unit interval
and then concatenated: `(x, ω) ↦ (toMappingPathFiber x).transLoop ω.toPath`. -/
def transLoopToMappingPathFiber (p : C(E, B)) (b : B) :
    C(Fiber p b × MooreLoopSpace B b, MappingPathFiber p b) :=
  ⟨fun q ↦ MappingPathFiber.transLoop p b (toMappingPathFiber q.1) q.2.toPath,
    (MappingPathFiber.continuous_transLoop p b).comp
      ((toMappingPathFiber.continuous.comp continuous_fst).prodMk
        (MooreLoopSpace.continuous_toPath.comp continuous_snd))⟩

@[simp]
theorem transLoopToMappingPathFiber_apply (q : Fiber p b × MooreLoopSpace B b) :
    transLoopToMappingPathFiber p b q =
      MappingPathFiber.transLoop p b (toMappingPathFiber q.1) q.2.toPath :=
  (rfl)

/-- The stage `s` of `actHomotopy` before normalization: the Moore paths of `x` and of `ω`, each
deformed by `MoorePath.unitHomotopy` at time `s`, then concatenated. -/
private def unitHomotopyAct (q : I × (Fiber p b × MooreLoopSpace B b)) : Fiber p b :=
  mk' (MooreReplacement.mk q.2.1.val.point
    ((MoorePath.unitHomotopy (q.1, q.2.1.val.path)).trans
      (MoorePath.unitHomotopy (q.1, q.2.2.toMoorePath))
      (by rw [MoorePath.unitHomotopy_target, MoorePath.unitHomotopy_source, target_path_val,
        MooreLoopSpace.source_eq]))
    (by rw [MoorePath.source_trans, MoorePath.unitHomotopy_source, source_path]))
    (by rw [path_mk, MoorePath.target_trans, MoorePath.unitHomotopy_target,
      MooreLoopSpace.target_eq])

private theorem continuous_unitHomotopyAct :
    Continuous (unitHomotopyAct : I × (Fiber p b × MooreLoopSpace B b) → Fiber p b) := by
  refine continuous_mk' (continuous_mk ?_ (Continuous.moorePath_trans ?_ ?_ _) _) _ <;> fun_prop

private theorem point_unitHomotopyAct (q : I × (Fiber p b × MooreLoopSpace B b)) :
    (unitHomotopyAct q).val.point = q.2.1.val.point := by
  simp [unitHomotopyAct]

/-- At time `0`, `unitHomotopyAct` normalizes to the concatenation of the normalizations. -/
private theorem toMappingPathFiber_unitHomotopyAct_zero (q : Fiber p b × MooreLoopSpace B b) :
    toMappingPathFiber (unitHomotopyAct (0, q)) =
      MappingPathFiber.transLoop p b (toMappingPathFiber q.1) q.2.toPath := by
  have hx : MoorePath.unitHomotopy (0, q.1.val.path) =
      (MappingPathFiber.toPath p b (toMappingPathFiber q.1)).toMoorePath := by
    simp
  have hω : MoorePath.unitHomotopy (0, q.2.toMoorePath) = q.2.toPath.toMoorePath := by
    rw [← MooreLoopSpace.toMoorePath_unitHomotopy, MooreLoopSpace.unitHomotopy_apply_zero,
      Path.toMoorePath_toMooreLoop]
  refine Subtype.ext (Prod.ext (by simp [point_unitHomotopyAct]) ?_)
  rw [toMappingPathFiber_val, MappingPathFiber.transLoop_val_snd,
    ← Path.toUnitPath_trans_toMoorePath]
  simp only [unitHomotopyAct, val_mk', path_mk, hx, hω]

/-- At time `1`, `unitHomotopyAct` is the action. -/
private theorem unitHomotopyAct_one (q : Fiber p b × MooreLoopSpace B b) :
    unitHomotopyAct (1, q) = q.1.act q.2 :=
  ext (MooreReplacement.ext (by rw [point_unitHomotopyAct, point_act])
    (by simp only [unitHomotopyAct, val_mk', path_mk, path_act, MoorePath.unitHomotopy_apply_one]))

/-- **The comparison with the mapping-path fibre is compatible with the actions, from the Moore
side**: normalizing `x · ω` to the unit interval is homotopic, continuously in `(x, ω)`, to
concatenating the normalizations of `x` and of the Moore loop `ω`. The homotopy normalizes the
concatenation of the Moore paths of `x` and `ω`, each deformed by `MoorePath.unitHomotopy`; it
keeps the point of `E` (`actHomotopy_val_fst`). -/
def actHomotopy (p : C(E, B)) (b : B) :
    ContinuousMap.Homotopy (transLoopToMappingPathFiber p b) (toMappingPathFiberAct p b) where
  toFun q := toMappingPathFiber (unitHomotopyAct q)
  continuous_toFun := toMappingPathFiber.continuous.comp continuous_unitHomotopyAct
  map_zero_left q := toMappingPathFiber_unitHomotopyAct_zero q
  map_one_left q := by
    rw [unitHomotopyAct_one, toMappingPathFiberAct_apply]

@[simp]
theorem actHomotopy_val_fst (s : I) (q : Fiber p b × MooreLoopSpace B b) :
    (actHomotopy p b (s, q)).val.1 = q.1.val.point :=
  point_unitHomotopyAct (s, q)

/-- Normalizing `x · ω` to the unit interval is homotopic to concatenating the normalizations of
`x` and of `ω`. -/
theorem homotopic_transLoopToMappingPathFiber_toMappingPathFiberAct (p : C(E, B)) (b : B) :
    (transLoopToMappingPathFiber p b).Homotopic (toMappingPathFiberAct p b) :=
  ⟨actHomotopy p b⟩

/-- The mapping-path fibre with the concatenation of loops on the unit interval, sent to the
Moore model: `(y, ℓ) ↦ ofMappingPathFiber (y.transLoop ℓ)`. -/
def ofMappingPathFiberTransLoop (p : C(E, B)) (b : B) :
    C(MappingPathFiber p b × Path b b, Fiber p b) :=
  ofMappingPathFiber.comp ⟨fun q ↦ MappingPathFiber.transLoop p b q.1 q.2,
    MappingPathFiber.continuous_transLoop p b⟩

@[simp]
theorem ofMappingPathFiberTransLoop_apply (q : MappingPathFiber p b × Path b b) :
    ofMappingPathFiberTransLoop p b q =
      ofMappingPathFiber (MappingPathFiber.transLoop p b q.1 q.2) :=
  (rfl)

/-- The mapping-path fibre and the loops on the unit interval, sent to the Moore model and then
acted on: `(y, ℓ) ↦ ofMappingPathFiber y · ℓ.toMooreLoop`. -/
def actOfMappingPathFiber (p : C(E, B)) (b : B) :
    C(MappingPathFiber p b × Path b b, Fiber p b) :=
  ⟨fun q ↦ (ofMappingPathFiber q.1).act q.2.toMooreLoop,
    continuous_act.comp ((ofMappingPathFiber.continuous.comp continuous_fst).prodMk
      (Path.continuous_toMooreLoop.comp continuous_snd))⟩

@[simp]
theorem actOfMappingPathFiber_apply (q : MappingPathFiber p b × Path b b) :
    actOfMappingPathFiber p b q = (ofMappingPathFiber q.1).act q.2.toMooreLoop :=
  (rfl)

/-- The stage `s` of `Path.transMoorePathHomotopy` at the path of `y` and the loop `ℓ` is the
Moore path of `y.trans ℓ`, as a point of the mapping-path fibre, reparametrized to length `1 + s`:
this form is continuous in `(y, ℓ)`, although the starting point of the path of `y` varies. -/
private theorem transMoorePathHomotopy_toPath (s : I) (y : MappingPathFiber p b) (ℓ : Path b b) :
    Path.transMoorePathHomotopy _ b b (s, (MappingPathFiber.toPath p b y, ℓ)) =
      (MoorePath.ofUnitPath (MappingPathFiber.transLoop p b y ℓ).val.2).rescale
        (1 + toNNReal s) := by
  rw [Path.transMoorePathHomotopy_apply, ← MappingPathFiber.toMoorePath_toPath,
    MappingPathFiber.toPath_transLoop, Path.toMoorePath_cast]

/-- **The comparison with the mapping-path fibre is compatible with the actions, from the
fixed-interval side**: the Moore form of `y.trans ℓ` is homotopic, continuously in `(y, ℓ)`, to
the Moore form of `y` acted on by the Moore loop of `ℓ`. The homotopy is
`Path.transMoorePathHomotopy` on the path of `y` and the loop `ℓ`, which reparametrizes the Moore
path of `y.trans ℓ` from length `1` to length `2`; it keeps the point of `E`
(`point_transLoopHomotopy`). -/
def transLoopHomotopy (p : C(E, B)) (b : B) :
    ContinuousMap.Homotopy (ofMappingPathFiberTransLoop p b) (actOfMappingPathFiber p b) where
  toFun q := mk' (MooreReplacement.mk q.2.1.val.1
      (Path.transMoorePathHomotopy _ b b (q.1, (MappingPathFiber.toPath p b q.2.1, q.2.2)))
      (Path.transMoorePathHomotopy_source _ _))
    (by rw [path_mk, Path.transMoorePathHomotopy_target])
  continuous_toFun := by
    refine continuous_mk' (continuous_mk ?_ ?_ _) _
    · fun_prop
    · simp only [transMoorePathHomotopy_toPath]
      exact (MoorePath.continuous_ofUnitPath.comp (continuous_subtypeVal.snd.comp
        ((MappingPathFiber.continuous_transLoop p b).comp continuous_snd))).moorePath_rescale
          (by fun_prop) fun _ ↦ (add_pos_of_pos_of_nonneg one_pos zero_le).ne'
  map_zero_left q := ext (MooreReplacement.ext (by simp) (by simp [Path.toMoorePath_def]))
  map_one_left q := ext (MooreReplacement.ext (by simp) (by simp))

@[simp]
theorem point_transLoopHomotopy (s : I) (q : MappingPathFiber p b × Path b b) :
    (transLoopHomotopy p b (s, q)).val.point = q.1.val.1 := by
  simp [transLoopHomotopy, ← ContinuousMap.Homotopy.coe_toContinuousMap]

/-- The Moore form of `y.trans ℓ` is homotopic to the Moore form of `y` acted on by the Moore
loop of `ℓ`. -/
theorem homotopic_ofMappingPathFiberTransLoop_actOfMappingPathFiber (p : C(E, B)) (b : B) :
    (ofMappingPathFiberTransLoop p b).Homotopic (actOfMappingPathFiber p b) :=
  ⟨transLoopHomotopy p b⟩

end Fiber

end MooreReplacement

end TauCeti
