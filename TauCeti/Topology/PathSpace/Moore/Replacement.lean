/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Constructions
public import Mathlib.Topology.Homotopy.Equiv
public import TauCeti.Topology.PathSpace.Moore.Lifting

/-!
# The Moore-path replacement of a map

For a continuous map `p : E → B`, the **Moore-path replacement** is the space
`E' = MooreReplacement p` of pairs `(e, γ)` of a point `e ∈ E` and a Moore path `γ` in `B` starting
at `p e`, with the endpoint map `p' (e, γ) = γ.target`.

* `p'` has a transitive lifting function, given by concatenation: a path `δ` starting at
  `γ.target` lifts to `s ↦ (e, γ · δ|[0, s])`.  So `p'` is a Hurewicz fibration, whatever `p` is
  (`TauCeti.MooreReplacement.isHurewiczFibration_endpoint`).
* The inclusion `E → E'`, `e ↦ (e, const)`, is a map over `B` and a homotopy equivalence, with
  homotopy inverse the projection `(e, γ) ↦ e`: a path shrinks to its start
  (`TauCeti.MooreReplacement.homotopyEquiv`).
* The fibre `F'` of `p'` over `b` carries the **strict** right action `(e, γ) · ω = (e, γ · ω)` of
  the Moore loops at `b`, continuous in both variables.  No choice of lifting function for `p` is
  involved.

When `p` itself has a lifting function `Φ`, **transport** `F' → F`, `(e, γ) ↦ Φ (e, γ)(end)`, to
the fibre `F` of `p` over `b` is a homotopy equivalence, with homotopy inverse `f ↦ (f, const)`
(`TauCeti.MooreLiftingFunction.transportHomotopyEquiv`).  When `Φ` is transitive, the Moore loops
act strictly on `F` by `f · ω = Φ (f, ω)(end)`, and transport is strictly equivariant
(`TauCeti.MooreLiftingFunction.IsTransitive.transport_act`).

## Main definitions

* `TauCeti.MooreReplacement.endpoint p`: the endpoint map `p' : E' → B`.
* `TauCeti.MooreReplacement.endpointLiftingFunction p`: the transitive lifting function of `p'`.
* `TauCeti.MooreReplacement.Fiber p b`: the fibre `F'` of `p'` over `b`, with its right action of
  `MooreLoopSpace B b`.
* `TauCeti.MooreLiftingFunction.transport`: transport `F' → F` along a lifting function.

## Main results

* `TauCeti.MooreReplacement.isHurewiczFibration_endpoint`: `p'` is a Hurewicz fibration.
* `TauCeti.MooreReplacement.homotopyEquiv`: `E ≃ₕ E'`, by the inclusion over `B`.
* `TauCeti.MooreLiftingFunction.transportHomotopyEquiv`: transport is a homotopy equivalence.
* `TauCeti.MooreLiftingFunction.IsTransitive.transport_act`: transport is strictly equivariant.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1 (after Dold and Kamps).
-/

public noncomputable section

open scoped NNReal
open unitInterval MulOpposite

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace MooreReplacement

/-! ### The endpoint map and its lifting function -/

/-- The **endpoint map** `p' : E' → B` of the Moore-path replacement, `(e, γ) ↦ γ.target`. -/
@[expose] def endpoint (p : C(E, B)) : C(MooreReplacement p, B) :=
  ⟨fun x ↦ x.path.target, by fun_prop⟩

@[simp]
theorem endpoint_apply {p : C(E, B)} (x : MooreReplacement p) : endpoint p x = x.path.target :=
  (rfl)

theorem source_trans_path {p : C(E, B)} (x : MooreReplacement p) (δ : MoorePath B)
    (h : x.path.target = δ.source) : (x.path.trans δ h).source = p x.point := by
  rw [MoorePath.source_trans, source_path]

theorem source_truncate_path {p : C(E, B)} (x : MooreReplacement p) (t : ℝ≥0) :
    (x.path.truncate t).source = p x.point := by
  rw [MoorePath.source_truncate, source_path]

theorem target_eq_source_truncate {p : C(E, B)} (x : MooreReplacement p) {δ : MoorePath B}
    (h : δ.source = endpoint p x) (s : ℝ≥0) : x.path.target = (δ.truncate s).source := by
  rw [MoorePath.source_truncate, h, endpoint_apply]

/-- The lift of a path `δ` starting at the end point of `(e, γ)`: the Moore path
`s ↦ (e, γ · δ|[0, s])` in the replacement, of the length of `δ`. -/
def liftPath {p : C(E, B)} (x : MooreReplacement p) (δ : MoorePath B)
    (h : δ.source = endpoint p x) : MoorePath (MooreReplacement p) where
  toFun s := mk x.point (x.path.trans (δ.truncate s) (x.target_eq_source_truncate h s))
    (x.source_trans_path _ _)
  continuous_toFun := continuous_mk continuous_const
    (continuous_const.moorePath_trans (continuous_const.moorePath_truncate continuous_id) _) _
  length := δ.length
  apply_of_length_le' s hs := by
    have h' : δ.truncate s = δ.truncate δ.length := by
      rw [δ.truncate_of_length_le hs, MoorePath.truncate_length]
    refine ext rfl ?_
    simp only [path_mk]
    congr 1

theorem liftPath_apply {p : C(E, B)} (x : MooreReplacement p) (δ : MoorePath B)
    (h : δ.source = endpoint p x) (s : ℝ≥0) :
    liftPath x δ h s = mk x.point (x.path.trans (δ.truncate s)
      (x.target_eq_source_truncate h s)) (x.source_trans_path _ _) :=
  (rfl)

@[simp]
theorem length_liftPath {p : C(E, B)} (x : MooreReplacement p) (δ : MoorePath B)
    (h : δ.source = endpoint p x) : (liftPath x δ h).length = δ.length :=
  (rfl)

@[simp]
theorem source_liftPath {p : C(E, B)} (x : MooreReplacement p) (δ : MoorePath B)
    (h : δ.source = endpoint p x) : (liftPath x δ h).source = x := by
  rw [MoorePath.source_def, liftPath_apply]
  exact ext rfl (by simp)

@[simp]
theorem map_liftPath {p : C(E, B)} (x : MooreReplacement p) (δ : MoorePath B)
    (h : δ.source = endpoint p x) : (liftPath x δ h).map (endpoint p) = δ :=
  MoorePath.ext (by simp) fun s ↦ by
    rw [MoorePath.map_apply, liftPath_apply]
    simp

/-- The **transitive lifting function** of the endpoint map of the Moore-path replacement:
concatenation, `((e, γ), δ) ↦ (s ↦ (e, γ · δ|[0, s]))`. -/
@[expose] def endpointLiftingFunction (p : C(E, B)) : MooreLiftingFunction (endpoint p) where
  toContinuousMap := ⟨fun y ↦ liftPath y.point y.path y.source_path, by
    refine MoorePath.continuous_iff.2 ⟨?_, ?_⟩
    · simp only [length_liftPath]
      exact MoorePath.continuous_length.comp continuous_path
    simp only [liftPath_apply]
    exact continuous_mk (continuous_point.comp (continuous_point.comp continuous_fst))
      ((continuous_path.comp (continuous_point.comp continuous_fst)).moorePath_trans
        ((continuous_path.comp continuous_fst).moorePath_truncate continuous_snd) _) _⟩
  source_apply' y := source_liftPath _ _ y.source_path
  map_apply' y := map_liftPath _ _ y.source_path

theorem endpointLiftingFunction_lift {p : C(E, B)} (x : MooreReplacement p) (δ : MoorePath B)
    (h : δ.source = endpoint p x) : (endpointLiftingFunction p).lift x δ h = liftPath x δ h :=
  (rfl)

/-- The lifting function of the endpoint map is transitive. -/
theorem isTransitive_endpointLiftingFunction (p : C(E, B)) :
    (endpointLiftingFunction p).IsTransitive where
  lift_refl x := by
    rw [MooreLiftingFunction.lift_eq_refl_of_length_eq_zero _ _ _ _ (MoorePath.length_refl _)]
  lift_trans x γ δ hγ h := by
    refine MoorePath.ext (by simp) fun s ↦ ?_
    simp only [endpointLiftingFunction_lift]
    rcases le_total s γ.length with hs | hs
    · rw [MoorePath.trans_apply_of_le _ _ _ (by simpa using hs), liftPath_apply, liftPath_apply]
      refine ext rfl ?_
      simp only [path_mk]
      congr 1
      exact MoorePath.truncate_trans_of_le _ _ _ hs
    · obtain ⟨u, rfl⟩ := exists_add_of_le hs
      have ht : (liftPath x γ hγ).target = mk x.point (x.path.trans γ (by rw [hγ, endpoint_apply]))
          (x.source_trans_path _ _) := by
        rw [MoorePath.target_def, length_liftPath, liftPath_apply]
        refine ext rfl ?_
        simp only [path_mk]
        congr 1
        exact MoorePath.truncate_length γ
      rw [show γ.length + u = (liftPath x γ hγ).length + u from rfl,
        MoorePath.trans_apply_length_add, liftPath_apply, liftPath_apply]
      refine ext ?_ ?_
      · simp only [point_mk, ht]
      · simp only [path_mk, ht, length_liftPath, MoorePath.truncate_trans_length_add]
        exact (MoorePath.trans_assoc x.path γ (δ.truncate u) _ _).symm

/-- The endpoint map of the Moore-path replacement is a Hurewicz fibration, whatever `p` is. -/
theorem isHurewiczFibration_endpoint (p : C(E, B)) : IsHurewiczFibration.{w} (endpoint p) :=
  (endpointLiftingFunction p).isHurewiczFibration

/-! ### The inclusion and the projection -/

/-- The inclusion `E → E'`, `e ↦ (e, const)`, a map over `B`. -/
def incl (p : C(E, B)) : C(E, MooreReplacement p) :=
  ⟨fun e ↦ mk e (.refl (p e)) (MoorePath.source_refl _),
    continuous_mk continuous_id (MoorePath.continuous_refl.comp p.continuous) _⟩

@[simp]
theorem point_incl {p : C(E, B)} (e : E) : (incl p e).point = e :=
  (rfl)

@[simp]
theorem path_incl {p : C(E, B)} (e : E) : (incl p e).path = .refl (p e) :=
  (rfl)

theorem endpoint_incl {p : C(E, B)} (e : E) : endpoint p (incl p e) = p e := by
  simp

/-- The projection `E' → E`, `(e, γ) ↦ e`. -/
def proj (p : C(E, B)) : C(MooreReplacement p, E) :=
  ⟨point, continuous_point⟩

@[simp]
theorem proj_apply {p : C(E, B)} (x : MooreReplacement p) : proj p x = x.point :=
  (rfl)

@[simp]
theorem proj_comp_incl (p : C(E, B)) : (proj p).comp (incl p) = .id E :=
  (rfl)

/-- The homotopy from `incl ∘ proj` to the identity of `E'`, shrinking each path to its start:
`(s, (e, γ)) ↦ (e, γ|[0, s · γ.length])`. -/
def shrinkHomotopy (p : C(E, B)) : ContinuousMap.Homotopy ((incl p).comp (proj p)) (.id _) where
  toFun y := mk y.2.point (y.2.path.truncate (toNNReal y.1 * y.2.path.length))
    (y.2.source_truncate_path _)
  continuous_toFun := continuous_mk (continuous_point.comp continuous_snd)
    ((continuous_path.comp continuous_snd).moorePath_truncate
      ((toNNReal_continuous.comp continuous_fst).mul
        (MoorePath.continuous_length.comp (continuous_path.comp continuous_snd)))) _
  map_zero_left x := ext rfl (by simp)
  map_one_left x := ext rfl (by simp)

/-- The inclusion `E → E'` is a homotopy equivalence, with homotopy inverse the projection. -/
def homotopyEquiv (p : C(E, B)) : ContinuousMap.HomotopyEquiv E (MooreReplacement p) where
  toFun := incl p
  invFun := proj p
  left_inv := by rw [proj_comp_incl]
  right_inv := ⟨shrinkHomotopy p⟩

/-! ### The fibre and the action of the Moore loops -/

/-- The fibre `F'` of the endpoint map over `b`: the pairs `(e, γ)` with `γ` ending at `b`. -/
@[expose] def Fiber (p : C(E, B)) (b : B) : Type (max u v) :=
  {x : MooreReplacement p // x.path.target = b}

namespace Fiber

variable {p : C(E, B)} {b : B}

instance : TopologicalSpace (Fiber p b) :=
  inferInstanceAs (TopologicalSpace {x : MooreReplacement p // x.path.target = b})

/-- The underlying pair of a point of the fibre. -/
@[expose] def val (x : Fiber p b) : MooreReplacement p :=
  Subtype.val x

@[simp]
theorem target_path_val (x : Fiber p b) : x.val.path.target = b :=
  x.2

@[ext]
theorem ext {x y : Fiber p b} (h : x.val = y.val) : x = y :=
  Subtype.ext h

@[fun_prop]
theorem continuous_val : Continuous (val : Fiber p b → MooreReplacement p) :=
  continuous_subtype_val

/-- The point `(e, γ)` of the fibre, for a pair whose path ends at `b`. -/
@[expose] def mk' (x : MooreReplacement p) (h : x.path.target = b) : Fiber p b :=
  ⟨x, h⟩

@[simp]
theorem val_mk' (x : MooreReplacement p) (h : x.path.target = b) : (mk' x h).val = x :=
  (rfl)

/-- The right action of a Moore loop `ω` at `b` on the fibre: `(e, γ) · ω = (e, γ · ω)`. -/
@[expose] def act (x : Fiber p b) (ω : MooreLoopSpace B b) : Fiber p b :=
  mk' (MooreReplacement.mk x.val.point (x.val.path.trans ω.toMoorePath (by simp))
    (by rw [MoorePath.source_trans, source_path])) (by simp)

@[simp]
theorem point_act (x : Fiber p b) (ω : MooreLoopSpace B b) :
    (x.act ω).val.point = x.val.point :=
  (rfl)

@[simp]
theorem path_act (x : Fiber p b) (ω : MooreLoopSpace B b) :
    (x.act ω).val.path = x.val.path.trans ω.toMoorePath (by simp) :=
  (rfl)

@[simp]
theorem act_one (x : Fiber p b) : x.act 1 = x :=
  ext (MooreReplacement.ext rfl (by simp))

theorem act_mul (x : Fiber p b) (ω ω' : MooreLoopSpace B b) :
    x.act (ω * ω') = (x.act ω).act ω' :=
  ext (MooreReplacement.ext rfl (by simp [MoorePath.trans_assoc]))

/-- The action is continuous in both variables. -/
theorem continuous_act :
    Continuous fun q : Fiber p b × MooreLoopSpace B b ↦ q.1.act q.2 :=
  (continuous_mk (continuous_point.comp (continuous_val.comp continuous_fst))
    ((continuous_path.comp (continuous_val.comp continuous_fst)).moorePath_trans
      (MooreLoopSpace.continuous_toMoorePath.comp continuous_snd) _) _).subtype_mk _

/-- The **strict right action** of the Moore loops at `b` on the fibre `F'`, as a left action of
the opposite monoid. -/
instance : MulAction (MooreLoopSpace B b)ᵐᵒᵖ (Fiber p b) where
  smul ω x := x.act ω.unop
  one_smul := act_one
  mul_smul ω ω' x := act_mul x ω'.unop ω.unop

theorem op_smul_eq_act (x : Fiber p b) (ω : MooreLoopSpace B b) : op ω • x = x.act ω :=
  (rfl)

instance : ContinuousSMul (MooreLoopSpace B b)ᵐᵒᵖ (Fiber p b) :=
  ⟨continuous_act.comp (continuous_snd.prodMk (continuous_unop.comp continuous_fst))⟩

end Fiber

end MooreReplacement

/-! ### Transport along a lifting function -/

namespace MooreLiftingFunction

open MooreReplacement

/-- The action of a Moore loop `ω` at `b` on the fibre of `p` over `b` through a lifting function:
`f · ω = Φ (f, ω)(end)`.  It is a strict action when `Φ` is transitive. -/
def fiberAct {p : C(E, B)} (Φ : MooreLiftingFunction p) (b : B) (f : {e // p e = b})
    (ω : MooreLoopSpace B b) : {e // p e = b} :=
  ⟨(Φ.lift f ω.toMoorePath (by rw [ω.source_eq, f.2])).target, by rw [target_lift, ω.target_eq]⟩

@[simp]
theorem coe_fiberAct {p : C(E, B)} (Φ : MooreLiftingFunction p) (b : B) (f : {e // p e = b})
    (ω : MooreLoopSpace B b) :
    (Φ.fiberAct b f ω : E) = (Φ.lift f ω.toMoorePath (by rw [ω.source_eq, f.2])).target :=
  (rfl)

/-- The action through a lifting function is continuous in both variables. -/
theorem continuous_fiberAct {p : C(E, B)} (Φ : MooreLiftingFunction p) (b : B) :
    Continuous fun q : {e // p e = b} × MooreLoopSpace B b ↦ Φ.fiberAct b q.1 q.2 :=
  (MoorePath.continuous_target.comp (Φ.continuous_lift (continuous_subtype_val.comp continuous_fst)
    (MooreLoopSpace.continuous_toMoorePath.comp continuous_snd) _)).subtype_mk _

/-- The unit loop acts trivially, for any lifting function: the lift of a path of length zero is
constant. -/
@[simp]
theorem fiberAct_one {p : C(E, B)} (Φ : MooreLiftingFunction p) (b : B) (f : {e // p e = b}) :
    Φ.fiberAct b f 1 = f :=
  Subtype.ext <| by
    rw [coe_fiberAct, Φ.lift_eq_refl_of_length_eq_zero _ _ _ (by simp), MoorePath.target_refl]

theorem IsTransitive.fiberAct_mul {p : C(E, B)} {Φ : MooreLiftingFunction p} (hΦ : Φ.IsTransitive)
    (b : B) (f : {e // p e = b}) (ω ω' : MooreLoopSpace B b) :
    Φ.fiberAct b f (ω * ω') = Φ.fiberAct b (Φ.fiberAct b f ω) ω' := by
  refine Subtype.ext ?_
  simp only [coe_fiberAct, MooreLoopSpace.toMoorePath_mul]
  rw [hΦ.lift_trans, MoorePath.target_trans]

/-- The strict right action of the Moore loops at `b` on the fibre of `p` over `b`, through a
transitive lifting function. -/
abbrev IsTransitive.mulAction {p : C(E, B)} {Φ : MooreLiftingFunction p} (hΦ : Φ.IsTransitive)
    (b : B) : MulAction (MooreLoopSpace B b)ᵐᵒᵖ {e // p e = b} where
  smul ω f := Φ.fiberAct b f ω.unop
  one_smul := Φ.fiberAct_one b
  mul_smul ω ω' f := hΦ.fiberAct_mul b f ω'.unop ω.unop

/-- The action through a transitive lifting function is continuous. -/
theorem IsTransitive.continuousSMul {p : C(E, B)} {Φ : MooreLiftingFunction p}
    (hΦ : Φ.IsTransitive) (b : B) :
    letI := hΦ.mulAction b
    ContinuousSMul (MooreLoopSpace B b)ᵐᵒᵖ {e // p e = b} :=
  letI := hΦ.mulAction b
  ⟨(Φ.continuous_fiberAct b).comp (continuous_snd.prodMk (continuous_unop.comp continuous_fst))⟩

theorem target_lift_val {p : C(E, B)} (Φ : MooreLiftingFunction p) {b : B} (x : Fiber p b) :
    p (Φ.lift x.val.point x.val.path x.val.source_path).target = b := by
  rw [target_lift, Fiber.target_path_val]

/-- **Transport** along a lifting function, from the fibre `F'` of the Moore-path replacement to
the fibre `F` of `p` over `b`: `(e, γ) ↦ Φ (e, γ)(end)`. -/
@[expose] def transport {p : C(E, B)} (Φ : MooreLiftingFunction p) (b : B) :
    C(Fiber p b, {e // p e = b}) :=
  ⟨fun x ↦ ⟨(Φ.lift x.val.point x.val.path x.val.source_path).target, Φ.target_lift_val x⟩,
    (MoorePath.continuous_target.comp (Φ.continuous_lift
      (continuous_point.comp Fiber.continuous_val) (continuous_path.comp Fiber.continuous_val)
      _)).subtype_mk _⟩

@[simp]
theorem coe_transport {p : C(E, B)} (Φ : MooreLiftingFunction p) (b : B) (x : Fiber p b) :
    (Φ.transport b x : E) = (Φ.lift x.val.point x.val.path x.val.source_path).target :=
  (rfl)

/-- Transport is strictly equivariant for the actions of the Moore loops, when the lifting function
is transitive. -/
theorem IsTransitive.transport_act {p : C(E, B)} {Φ : MooreLiftingFunction p}
    (hΦ : Φ.IsTransitive) (b : B) (x : Fiber p b) (ω : MooreLoopSpace B b) :
    Φ.transport b (x.act ω) = Φ.fiberAct b (Φ.transport b x) ω := by
  refine Subtype.ext ?_
  simp only [coe_transport, coe_fiberAct]
  simp only [Fiber.path_act, Fiber.point_act]
  rw [hΦ.lift_trans, MoorePath.target_trans]

theorem target_path_incl_val {p : C(E, B)} {b : B} (f : {e // p e = b}) :
    (incl p f).path.target = b := by
  simp [f.2]

/-- The inclusion of the fibre of `p` into the fibre `F'`, `f ↦ (f, const)`. -/
@[expose] def fiberIncl (p : C(E, B)) (b : B) : C({e // p e = b}, Fiber p b) :=
  ⟨fun f ↦ Fiber.mk' (incl p f) (target_path_incl_val f),
    ((incl p).continuous.comp continuous_subtype_val).subtype_mk _⟩

@[simp]
theorem val_fiberIncl {p : C(E, B)} (b : B) (f : {e // p e = b}) :
    (fiberIncl p b f).val = incl p f :=
  (rfl)

theorem transport_comp_fiberIncl {p : C(E, B)} (Φ : MooreLiftingFunction p) (b : B) :
    (Φ.transport b).comp (fiberIncl p b) = .id _ :=
  ContinuousMap.ext fun f ↦ Subtype.ext <| by
    rw [ContinuousMap.comp_apply, coe_transport,
      Φ.lift_eq_refl_of_length_eq_zero _ _ _ (by simp)]
    simp

theorem source_drop_eq {p : C(E, B)} (Φ : MooreLiftingFunction p) (x : MooreReplacement p)
    (u : ℝ≥0) :
    (x.path.drop u).source =
      p (Φ.lift x.point (x.path.truncate u) (x.source_truncate_path u)).target := by
  rw [MoorePath.source_drop, target_lift, MoorePath.target_truncate]

/-- The homotopy from the identity of `F'` to `fiberIncl ∘ transport`: at time `s`, lift the first
part `γ|[0, u]` of the path, `u = s · γ.length`, and keep the rest `γ|[u, γ.length]`. -/
def transportHomotopy {p : C(E, B)} (Φ : MooreLiftingFunction p) (b : B) :
    ContinuousMap.Homotopy (.id (Fiber p b)) ((fiberIncl p b).comp (Φ.transport b)) where
  toFun y := Fiber.mk' (MooreReplacement.mk
      (Φ.lift y.2.val.point (y.2.val.path.truncate (toNNReal y.1 * y.2.val.path.length))
        (y.2.val.source_truncate_path _)).target
      (y.2.val.path.drop (toNNReal y.1 * y.2.val.path.length))
      (Φ.source_drop_eq _ _))
    (by rw [path_mk, MoorePath.target_drop, Fiber.target_path_val])
  continuous_toFun := by
    have hL : Continuous fun y : I × Fiber p b ↦ toNNReal y.1 * y.2.val.path.length :=
      (toNNReal_continuous.comp continuous_fst).mul (MoorePath.continuous_length.comp
        (continuous_path.comp (Fiber.continuous_val.comp continuous_snd)))
    have hγ : Continuous fun y : I × Fiber p b ↦ y.2.val.path :=
      continuous_path.comp (Fiber.continuous_val.comp continuous_snd)
    exact (continuous_mk (MoorePath.continuous_target.comp (Φ.continuous_lift
      (continuous_point.comp (Fiber.continuous_val.comp continuous_snd))
      (hγ.moorePath_truncate hL) _)) (hγ.moorePath_drop hL) _).subtype_mk _
  map_zero_left x := by
    refine Fiber.ext (MooreReplacement.ext ?_ ?_)
    · simp only [Fiber.val_mk', point_mk, toNNReal_zero, zero_mul, ContinuousMap.id_apply]
      rw [Φ.lift_eq_refl_of_length_eq_zero _ _ _ (by simp), MoorePath.target_refl]
    · simp
  map_one_left x := by
    refine Fiber.ext (MooreReplacement.ext ?_ ?_)
    · simp
    · simp only [Fiber.val_mk', path_mk, toNNReal_one, one_mul, MoorePath.drop_length,
        ContinuousMap.comp_apply, val_fiberIncl, path_incl, coe_transport]
      rw [target_lift, Fiber.target_path_val]

/-- **Transport is a homotopy equivalence** from the fibre `F'` of the Moore-path replacement to
the fibre of `p`, with homotopy inverse `f ↦ (f, const)`. -/
def transportHomotopyEquiv {p : C(E, B)} (Φ : MooreLiftingFunction p) (b : B) :
    ContinuousMap.HomotopyEquiv (Fiber p b) {e // p e = b} where
  toFun := Φ.transport b
  invFun := fiberIncl p b
  left_inv := ⟨(Φ.transportHomotopy b).symm⟩
  right_inv := by rw [transport_comp_fiberIncl]

end MooreLiftingFunction

end TauCeti
