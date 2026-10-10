/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HurewiczFibration
public import TauCeti.Topology.PathSpace.Moore.Truncate

/-!
# Lifting functions on Moore paths

For a continuous map `p : E → B`, the space `MooreReplacement p` consists of the pairs `(e, γ)` of
a point `e ∈ E` and a Moore path `γ` in `B` starting at `p e`, a subspace of `E × P B`.  It is the
domain `E ×_B P B` of a lifting function, and also the total space of the Moore-path replacement of
`p` (the later file `TauCeti.Topology.PathSpace.Moore.Replacement`).

A **lifting function** for `p` on Moore paths is a continuous map `Φ : E ×_B P B → P E` such that
`Φ (e, γ)` starts at `e` and lies over `γ`, `p ∘ Φ (e, γ) = γ` as Moore paths, so in particular of
the length of `γ`.  A map with a lifting function is a Hurewicz fibration
(`TauCeti.MooreLiftingFunction.isHurewiczFibration`): a homotopy `H : I × A → B` is a family of
Moore paths of length one, and lifting them from the initial lift gives the lifted homotopy.

A lifting function is **transitive** (`TauCeti.MooreLiftingFunction.IsTransitive`) when it lifts
the constant paths of length zero to constant paths and lifts a concatenation `γ · δ` to the
concatenation of the lift of `γ` with the lift of `δ` from the end point of the first lift.  A
homotopy lifting property alone does not supply a transitive lifting function, and none is
constructed from one here; transitive lifting functions are what make the action of the Moore loops
on a fibre strict.

## Main definitions

* `TauCeti.MooreReplacement p`: the pairs `(e, γ)` with `γ` a Moore path starting at `p e`.
* `TauCeti.MooreLiftingFunction p`: lifting functions for `p` on Moore paths, with
  `TauCeti.MooreLiftingFunction.lift`.
* `TauCeti.MooreLiftingFunction.IsTransitive`: transitivity of a lifting function.

## Main results

* `TauCeti.MooreLiftingFunction.isHurewiczFibration`: a map with a lifting function is a Hurewicz
  fibration.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1 (transitive lifting functions,
  after Dold and Kamps).
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
-/

public noncomputable section

open scoped NNReal
open unitInterval

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- The pairs `(e, γ)` of a point `e ∈ E` and a Moore path `γ` in `B` starting at `p e`, a subspace
of `E × P B`: the domain `E ×_B P B` of a lifting function, and the total space of the Moore-path
replacement of `p`. -/
@[expose] def MooreReplacement (p : C(E, B)) : Type (max u v) :=
  {x : E × MoorePath B // x.2.source = p x.1}

namespace MooreReplacement

variable {p : C(E, B)}

instance : TopologicalSpace (MooreReplacement p) :=
  inferInstanceAs (TopologicalSpace {x : E × MoorePath B // x.2.source = p x.1})

/-- The pair `(e, γ)`, for a Moore path `γ` starting at `p e`. -/
@[expose] def mk (e : E) (γ : MoorePath B) (h : γ.source = p e) : MooreReplacement p :=
  ⟨(e, γ), h⟩

/-- The point of `E` of a pair `(e, γ)`. -/
@[expose] def point (x : MooreReplacement p) : E :=
  x.1.1

/-- The Moore path of a pair `(e, γ)`. -/
@[expose] def path (x : MooreReplacement p) : MoorePath B :=
  x.1.2

@[simp]
theorem source_path (x : MooreReplacement p) : x.path.source = p x.point :=
  x.2

@[simp]
theorem point_mk (e : E) (γ : MoorePath B) (h : γ.source = p e) : (mk e γ h).point = e :=
  (rfl)

@[simp]
theorem path_mk (e : E) (γ : MoorePath B) (h : γ.source = p e) : (mk e γ h).path = γ :=
  (rfl)

@[ext]
theorem ext {x y : MooreReplacement p} (h₁ : x.point = y.point) (h₂ : x.path = y.path) :
    x = y :=
  Subtype.ext (Prod.ext h₁ h₂)

@[simp]
theorem mk_point_path (x : MooreReplacement p) : mk x.point x.path x.source_path = x :=
  (rfl)

@[fun_prop]
theorem continuous_point : Continuous (point : MooreReplacement p → E) :=
  continuous_fst.comp continuous_subtype_val

@[fun_prop]
theorem continuous_path : Continuous (path : MooreReplacement p → MoorePath B) :=
  continuous_snd.comp continuous_subtype_val

/-- A family of pairs is continuous when its points and its paths are. -/
@[fun_prop]
theorem continuous_mk {Y : Type*} [TopologicalSpace Y] {f : Y → E} {g : Y → MoorePath B}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ y, (g y).source = p (f y)) :
    Continuous fun y ↦ mk (f y) (g y) (h y) :=
  (hf.prodMk hg).subtype_mk _

end MooreReplacement

/-- A **lifting function** for `p : E → B` on Moore paths: a continuous map
`Φ : E ×_B P B → P E` such that `Φ (e, γ)` starts at `e` and lies over `γ`. -/
structure MooreLiftingFunction (p : C(E, B)) where
  /-- The lifting function, as a continuous map. -/
  toContinuousMap : C(MooreReplacement p, MoorePath E)
  /-- The lift of `(e, γ)` starts at `e`. -/
  source_apply' : ∀ x, (toContinuousMap x).source = x.point
  /-- The lift of `(e, γ)` lies over `γ`. -/
  map_apply' : ∀ x, (toContinuousMap x).map p = x.path

namespace MooreLiftingFunction

variable {p : C(E, B)} (Φ : MooreLiftingFunction p)

/-- The lift of a Moore path `γ` starting at `p e`, from `e`. -/
@[expose] def lift (e : E) (γ : MoorePath B) (h : γ.source = p e) : MoorePath E :=
  Φ.toContinuousMap (.mk e γ h)

theorem lift_def (e : E) (γ : MoorePath B) (h : γ.source = p e) :
    Φ.lift e γ h = Φ.toContinuousMap (.mk e γ h) :=
  (rfl)

@[simp]
theorem source_lift (e : E) (γ : MoorePath B) (h : γ.source = p e) :
    (Φ.lift e γ h).source = e :=
  Φ.source_apply' _

@[simp]
theorem map_lift (e : E) (γ : MoorePath B) (h : γ.source = p e) : (Φ.lift e γ h).map p = γ :=
  Φ.map_apply' _

@[simp]
theorem length_lift (e : E) (γ : MoorePath B) (h : γ.source = p e) :
    (Φ.lift e γ h).length = γ.length := by
  rw [← MoorePath.length_map p, map_lift]

/-- The lift of a Moore path of length zero is the constant path at its start. -/
theorem lift_eq_refl_of_length_eq_zero (e : E) (γ : MoorePath B) (h : γ.source = p e)
    (hγ : γ.length = 0) : Φ.lift e γ h = .refl e := by
  rw [MoorePath.eq_refl_of_length_eq_zero (γ := Φ.lift e γ h) (by rwa [length_lift]), source_lift]

@[simp]
theorem apply_lift (e : E) (γ : MoorePath B) (h : γ.source = p e) (t : ℝ≥0) :
    p (Φ.lift e γ h t) = γ t := by
  rw [← MoorePath.map_apply, map_lift]

@[simp]
theorem target_lift (e : E) (γ : MoorePath B) (h : γ.source = p e) :
    p (Φ.lift e γ h).target = γ.target := by
  rw [← MoorePath.target_map, map_lift]

/-- The lifts form a continuous family in the point and the path. -/
@[fun_prop]
theorem continuous_lift {Y : Type*} [TopologicalSpace Y] {f : Y → E} {g : Y → MoorePath B}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ y, (g y).source = p (f y)) :
    Continuous fun y ↦ Φ.lift (f y) (g y) (h y) :=
  Φ.toContinuousMap.continuous.comp (MooreReplacement.continuous_mk hf hg h)

/-- A lifting function is **transitive** when it lifts the constant paths of length zero to
constant paths, and lifts a concatenation `γ · δ` from `e` to the lift of `γ` from `e` followed by
the lift of `δ` from the end point of the first lift. -/
structure IsTransitive : Prop where
  /-- The constant path of length zero lifts to the constant path. -/
  lift_refl : ∀ e, Φ.lift e (.refl (p e)) (MoorePath.source_refl _) = .refl e
  /-- A concatenation lifts to the concatenation of the lifts. -/
  lift_trans : ∀ (e : E) (γ δ : MoorePath B) (hγ : γ.source = p e) (h : γ.target = δ.source),
    Φ.lift e (γ.trans δ h) (by rw [MoorePath.source_trans, hγ]) =
      (Φ.lift e γ hγ).trans (Φ.lift (Φ.lift e γ hγ).target δ (by rw [target_lift, h]))
        (source_lift ..).symm

/-! ### A lifting function makes a Hurewicz fibration -/

/-- The parameter `min t 1` of the unit interval, for a time `t ≥ 0`. -/
private def toI (t : ℝ≥0) : I :=
  Set.projIcc 0 1 zero_le_one t

private theorem continuous_toI : Continuous toI :=
  continuous_projIcc.comp NNReal.continuous_coe

private theorem toI_toNNReal (s : I) : toI (toNNReal s) = s :=
  Set.projIcc_val zero_le_one s

/-- The Moore path of length one `t ↦ H (min t 1, a)` traced by a homotopy at the point `a`. -/
private def unitPath {A : Type w} [TopologicalSpace A] (H : C(I × A, B)) (a : A) : MoorePath B where
  toFun t := H (toI t, a)
  continuous_toFun := H.continuous.comp (continuous_toI.prodMk continuous_const)
  length := 1
  apply_of_length_le' t ht := by
    simp only [toI, Set.projIcc_of_right_le zero_le_one (show (1 : ℝ) ≤ t from ht),
      NNReal.coe_one, Set.projIcc_right]

private theorem unitPath_apply {A : Type w} [TopologicalSpace A] (H : C(I × A, B)) (a : A)
    (t : ℝ≥0) : unitPath H a t = H (toI t, a) :=
  (rfl)

private theorem continuous_unitPath {A : Type w} [TopologicalSpace A] (H : C(I × A, B)) :
    Continuous (unitPath H) :=
  MoorePath.continuous_iff.2 ⟨continuous_const,
    H.continuous.comp ((continuous_toI.comp continuous_snd).prodMk continuous_fst)⟩

/-- A map with a lifting function on Moore paths is a Hurewicz fibration: a homotopy is a family of
Moore paths of length one, and their lifts from the initial lift form the lifted homotopy. -/
theorem isHurewiczFibration (Φ : MooreLiftingFunction p) : IsHurewiczFibration.{w} p := by
  refine isHurewiczFibration_iff.2 fun A _ f H hH ↦ ?_
  have h₀ : ∀ a, (unitPath H a).source = p (f a) := fun a ↦ by
    rw [MoorePath.source_def, unitPath_apply, show toI 0 = 0 from
      Set.projIcc_left zero_le_one, hH a]
  refine ⟨⟨fun x ↦ Φ.lift (f x.2) (unitPath H x.2) (h₀ x.2) (toNNReal x.1), ?_⟩, funext fun x ↦ ?_,
    fun a ↦ ?_⟩
  · exact (Φ.continuous_lift (f.continuous.comp continuous_snd)
      ((continuous_unitPath H).comp continuous_snd) fun x ↦ h₀ x.2).moorePath_eval
      (toNNReal_continuous.comp continuous_fst)
  · simp only [Function.comp_apply, ContinuousMap.coe_mk, apply_lift, unitPath_apply, toI_toNNReal]
  · simp only [ContinuousMap.coe_mk]
    rw [toNNReal_zero, ← MoorePath.source_def, source_lift]

end MooreLiftingFunction

end TauCeti
