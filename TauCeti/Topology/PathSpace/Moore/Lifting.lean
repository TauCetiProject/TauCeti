/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HurewiczFibration
public import TauCeti.Topology.PathSpace.Moore.Comparison.Basic

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
* `TauCeti.MooreLiftingFunction.fst`: the lifting function of a product projection.

## Main results

* `TauCeti.MooreLiftingFunction.isHurewiczFibration`: a map with a lifting function is a Hurewicz
  fibration.
* `TauCeti.MooreLiftingFunction.isTransitive_fst`: the lifting function of a product projection is
  transitive.

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
def mk (e : E) (γ : MoorePath B) (h : γ.source = p e) : MooreReplacement p :=
  ⟨(e, γ), h⟩

/-- The point of `E` of a pair `(e, γ)`. -/
def point (x : MooreReplacement p) : E :=
  x.1.1

/-- The Moore path of a pair `(e, γ)`. -/
def path (x : MooreReplacement p) : MoorePath B :=
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

/-- Two lifting functions are equal when their underlying continuous maps are. -/
@[ext]
theorem ext {Φ Ψ : MooreLiftingFunction p} (h : Φ.toContinuousMap = Ψ.toContinuousMap) :
    Φ = Ψ := by
  cases Φ
  cases Ψ
  congr

/-- The lift of a Moore path `γ` starting at `p e`, from `e`. -/
def lift (e : E) (γ : MoorePath B) (h : γ.source = p e) : MoorePath E :=
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

/-- A lifting function is **transitive** when it lifts a concatenation `γ · δ` from `e` to the lift
of `γ` from `e` followed by the lift of `δ` from the end point of the first lift.  (Constant
paths of length zero lift to constant paths for every lifting function,
`MooreLiftingFunction.lift_eq_refl_of_length_eq_zero`.) -/
structure IsTransitive : Prop where
  /-- A concatenation lifts to the concatenation of the lifts. -/
  lift_trans : ∀ (e : E) (γ δ : MoorePath B) (hγ : γ.source = p e) (h : γ.target = δ.source),
    Φ.lift e (γ.trans δ h) (by rw [MoorePath.source_trans, hγ]) =
      (Φ.lift e γ hγ).trans (Φ.lift (Φ.lift e γ hγ).target δ (by rw [target_lift, h]))
        (source_lift ..).symm

/-! ### A lifting function makes a Hurewicz fibration -/

/-- A map with a lifting function on Moore paths is a Hurewicz fibration: a homotopy is a family of
Moore paths of length one, and their lifts from the initial lift form the lifted homotopy. -/
theorem isHurewiczFibration (Φ : MooreLiftingFunction p) : IsHurewiczFibration.{w} p := by
  refine isHurewiczFibration_iff.2 ⟨p.continuous, fun A _ f H hH ↦ ?_⟩
  -- The homotopy at `a`, as a Moore path of length one.
  let γ : C(A, C(I, B)) := (H.comp ContinuousMap.prodSwap).curry
  have h₀ : ∀ a, (MoorePath.ofUnitPath (γ a)).source = p (f a) := fun a ↦ by
    rw [MoorePath.source_ofUnitPath]
    exact hH a
  refine ⟨⟨fun x ↦ Φ.lift (f x.2) (.ofUnitPath (γ x.2)) (h₀ x.2) (toNNReal x.1), ?_⟩,
    funext fun x ↦ ?_, fun a ↦ ?_⟩
  · exact (Φ.continuous_lift (f.continuous.comp continuous_snd)
      (MoorePath.continuous_ofUnitPath.comp (γ.continuous.comp continuous_snd))
      fun x ↦ h₀ x.2).moorePath_eval (toNNReal_continuous.comp continuous_fst)
  · simp [γ]
  · simp only [ContinuousMap.coe_mk]
    rw [toNNReal_zero, ← MoorePath.source_def, source_lift]


/-! ### The product projection -/

section Fst

variable (F : Type*) [TopologicalSpace F]

/-- The lifting function of the projection `B × F → B`: the lift of `γ` from `(b, f)` is `γ`
paired with the constant path at `f`. -/
def fst : MooreLiftingFunction (ContinuousMap.fst : C(B × F, B)) where
  toContinuousMap :=
    { toFun x :=
        { toFun t := (x.path t, x.point.2)
          continuous_toFun := by fun_prop
          length := x.path.length
          apply_of_length_le' t ht :=
            Prod.ext ((x.path.apply_of_length_le ht).trans x.path.target_def) rfl }
      continuous_toFun := MoorePath.continuous_iff.2
        ⟨(MoorePath.continuous_length.comp MooreReplacement.continuous_path :
            Continuous fun x : MooreReplacement (ContinuousMap.fst : C(B × F, B)) ↦ x.path.length),
          (MoorePath.continuous_iff.1 MooreReplacement.continuous_path).2.prodMk
            ((continuous_snd.comp MooreReplacement.continuous_point).comp continuous_fst)⟩ }
  source_apply' x := by
    rw [MoorePath.source_def]
    exact Prod.ext ((MoorePath.source_def _).symm.trans x.source_path) rfl
  map_apply' x := MoorePath.ext (MoorePath.length_map _ _) fun t ↦ by
    rw [MoorePath.map_apply]
    rfl

variable {F}

@[simp]
theorem fst_lift_apply (e : B × F) (γ : MoorePath B)
    (h : γ.source = (ContinuousMap.fst : C(B × F, B)) e) (t : ℝ≥0) :
    (fst F).lift e γ h t = (γ t, e.2) :=
  (rfl)

/-- The lifting function of a product projection is transitive. -/
theorem isTransitive_fst : (fst F).IsTransitive (B := B) where
  lift_trans e γ δ hγ h := by
    refine MoorePath.ext (by simp [MoorePath.length_trans]) fun t ↦ ?_
    rw [fst_lift_apply, MoorePath.trans_apply, MoorePath.trans_apply, length_lift]
    split_ifs
    · rw [fst_lift_apply]
    · refine Prod.ext ?_ ?_
      · rw [fst_lift_apply]
      · rw [fst_lift_apply, MoorePath.target_def, fst_lift_apply]

end Fst

end MooreLiftingFunction

end TauCeti
