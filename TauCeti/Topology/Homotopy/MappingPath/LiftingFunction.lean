/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HurewiczFibration.Basic
public import TauCeti.Topology.Homotopy.MappingPath.Basic

/-!
# Lifting functions

A **lifting function** for a continuous map `p : E → B` is a continuous map
`Λ : E ×_B C(I, B) → C(I, E)` such that `Λ (e, γ)` starts at `e` and lies over `γ`. Its domain is
the mapping-path space `TauCeti.MappingPathSpace p` of pairs `(e, γ)` with `γ 0 = p e`, with the
compact-open topology on paths.

A lifting function lifts homotopies parametrized by arbitrary spaces, in every universe, so a map
with a lifting function is a Hurewicz fibration. Conversely, a Hurewicz fibration lifts the
tautological homotopy parametrized by `MappingPathSpace p` itself, and currying that lift gives a
lifting function. Hence a map is a Hurewicz fibration for test spaces in `Type (max u v)` if and
only if it admits a lifting function, and then it is a Hurewicz fibration for test spaces in every
universe.

As an application, the endpoint map of any mapping-path replacement `MappingPathSpace f → K`
has an explicit lifting function: the lift of a path `δ` from `(b, γ)` at time `s` is `(b, γ')`
where `γ'` runs through `γ` and then through `δ` on `[0, s]`, at speed `1 + s`. So the endpoint
map is a Hurewicz fibration for every continuous `f`, without any hypothesis on its source or
target.

## Main definitions

* `TauCeti.LiftingFunction p`: lifting functions for `p : C(E, B)`, with
  `TauCeti.LiftingFunction.lift`.
* `TauCeti.LiftingFunction.liftFamily`: the lifts of a continuous family of paths, as a continuous
  map, with `liftFamily_apply`, `liftFamily_zero` and `apply_liftFamily`.
* `TauCeti.MappingPathSpace.endpointLiftingFunction f`: the path-concatenation lifting function
  of the endpoint map of `MappingPathSpace f`.

## Main results

* `TauCeti.LiftingFunction.isHurewiczFibration`: a map with a lifting function is a Hurewicz
  fibration for test spaces in every universe.
* `TauCeti.isHurewiczFibration_iff_nonempty_liftingFunction`: a map `p : C(E, B)` is a Hurewicz
  fibration for test spaces in `Type (max u v)` if and only if it has a lifting function.
* `TauCeti.IsHurewiczFibration.up`: a Hurewicz fibration for test spaces in `Type (max u v)` is
  one for test spaces in every universe.
* `TauCeti.MappingPathSpace.isHurewiczFibration_endpoint`: the endpoint map of a mapping-path
  replacement is a Hurewicz fibration.

## References

* W. Hurewicz, *On the concept of fiber space*, Proc. Nat. Acad. Sci. 41 (1955), 956–961.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
-/

public section

open Set unitInterval

universe w u v u' v'

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- A **lifting function** for `p : C(E, B)`: a continuous map `Λ : E ×_B C(I, B) → C(I, E)`
such that `Λ (e, γ)` starts at `e` and lies over `γ`. -/
structure LiftingFunction (p : C(E, B)) where
  /-- The lifting function, as a continuous map on the mapping-path space of `p`. -/
  toContinuousMap : C(MappingPathSpace p, C(I, E))
  /-- The lift of `(e, γ)` starts at `e`. -/
  apply_zero' : ∀ x, toContinuousMap x 0 = x.val.1
  /-- The lift of `(e, γ)` lies over `γ`. -/
  comp_apply' : ∀ x, p.comp (toContinuousMap x) = x.val.2

namespace LiftingFunction

variable {p : C(E, B)} (Λ : LiftingFunction p)

/-- Two lifting functions are equal when their underlying continuous maps are. -/
@[ext]
theorem ext {Λ Λ' : LiftingFunction p} (h : Λ.toContinuousMap = Λ'.toContinuousMap) :
    Λ = Λ' := by
  cases Λ
  cases Λ'
  congr

/-- The lift from `e` of a path `γ` starting at `p e`. -/
def lift (e : E) (γ : C(I, B)) (h : γ 0 = p e) : C(I, E) :=
  Λ.toContinuousMap ⟨(e, γ), h⟩

theorem lift_def (e : E) (γ : C(I, B)) (h : γ 0 = p e) :
    Λ.lift e γ h = Λ.toContinuousMap ⟨(e, γ), h⟩ :=
  (rfl)

theorem lift_congr {e e' : E} (he : e = e') {γ γ' : C(I, B)} (hγ : γ = γ') (h : γ 0 = p e)
    (h' : γ' 0 = p e') : Λ.lift e γ h = Λ.lift e' γ' h' := by
  subst he hγ
  rfl

@[simp]
theorem lift_zero (e : E) (γ : C(I, B)) (h : γ 0 = p e) : Λ.lift e γ h 0 = e :=
  Λ.apply_zero' _

@[simp]
theorem comp_lift (e : E) (γ : C(I, B)) (h : γ 0 = p e) : p.comp (Λ.lift e γ h) = γ :=
  Λ.comp_apply' _

@[simp]
theorem apply_lift (e : E) (γ : C(I, B)) (h : γ 0 = p e) (t : I) :
    p (Λ.lift e γ h t) = γ t :=
  ContinuousMap.congr_fun (Λ.comp_lift e γ h) t

/-- The lifts form a continuous family in the point and the path. -/
@[fun_prop]
theorem continuous_lift {Y : Type*} [TopologicalSpace Y] {f : Y → E} {g : Y → C(I, B)}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ y, g y 0 = p (f y)) :
    Continuous fun y ↦ Λ.lift (f y) (g y) (h y) :=
  Λ.toContinuousMap.continuous.comp ((hf.prodMk hg).subtype_mk h)

/-- The lifts, starting at the points `f y`, of a family `γ` of paths in `B` with
`γ (y, 0) = p (f y)`, as a continuous map on `Y × I`. -/
def liftFamily {Y : Type*} [TopologicalSpace Y] (f : C(Y, E)) (γ : C(Y × I, B))
    (h : ∀ y, γ (y, 0) = p (f y)) : C(Y × I, E) :=
  ⟨fun z ↦ Λ.lift (f z.1) (γ.curry z.1) (h z.1) z.2,
    continuous_eval.comp
      (((Λ.continuous_lift (f.continuous.comp continuous_fst)
        (γ.curry.continuous.comp continuous_fst) fun z ↦ h z.1)).prodMk continuous_snd)⟩

theorem liftFamily_apply {Y : Type*} [TopologicalSpace Y] (f : C(Y, E)) (γ : C(Y × I, B))
    (h : ∀ y, γ (y, 0) = p (f y)) (y : Y) (t : I) :
    Λ.liftFamily f γ h (y, t) = Λ.lift (f y) (γ.curry y) (h y) t :=
  (rfl)

@[simp]
theorem liftFamily_zero {Y : Type*} [TopologicalSpace Y] (f : C(Y, E)) (γ : C(Y × I, B))
    (h : ∀ y, γ (y, 0) = p (f y)) (y : Y) : Λ.liftFamily f γ h (y, 0) = f y :=
  Λ.lift_zero _ _ _

@[simp]
theorem apply_liftFamily {Y : Type*} [TopologicalSpace Y] (f : C(Y, E)) (γ : C(Y × I, B))
    (h : ∀ y, γ (y, 0) = p (f y)) (y : Y) (t : I) : p (Λ.liftFamily f γ h (y, t)) = γ (y, t) :=
  Λ.apply_lift _ _ _ t

/-- A map with a lifting function is a Hurewicz fibration, for test spaces in every universe. -/
theorem isHurewiczFibration (Λ : LiftingFunction p) : IsHurewiczFibration.{w} p := by
  refine isHurewiczFibration_iff.2 ⟨p.continuous, fun A _ f H hH ↦ ?_⟩
  -- The homotopy at `a` is a path starting at `p (f a)`; lift these paths from `f a`.
  let γ : C(A × I, B) := H.comp ContinuousMap.prodSwap
  have h₀ : ∀ a, γ (a, 0) = p (f a) := fun a ↦ by simpa [γ] using hH a
  refine ⟨(Λ.liftFamily f γ h₀).comp ContinuousMap.prodSwap, funext fun x ↦ ?_, fun a ↦ ?_⟩
  · simp [γ]
  · simp

end LiftingFunction

/-- A Hurewicz fibration for test spaces in `Type (max u v)` has a lifting function: lifting the
tautological homotopy parametrized by the mapping-path space and currying gives one. -/
theorem IsHurewiczFibration.nonempty_liftingFunction {p : C(E, B)}
    (h : IsHurewiczFibration.{max u v} p) : Nonempty (LiftingFunction p) := by
  let H : C(I × MappingPathSpace p, B) := ⟨fun x ↦ x.2.val.2 x.1, by fun_prop⟩
  obtain ⟨G, hG, hG₀⟩ := h.hasHomotopyLiftingProperty (MappingPathSpace p)
    ⟨fun x ↦ x.val.1, by fun_prop⟩ H fun x ↦ x.property
  exact ⟨{ toContinuousMap := (G.comp ContinuousMap.prodSwap).curry
           apply_zero' x := by simpa using hG₀ x
           comp_apply' x := ContinuousMap.ext fun t ↦ by simpa [H] using congrFun hG (t, x) }⟩

/-- A map is a Hurewicz fibration for test spaces in `Type (max u v)` if and only if it has a
lifting function. -/
theorem isHurewiczFibration_iff_nonempty_liftingFunction {p : C(E, B)} :
    IsHurewiczFibration.{max u v} p ↔ Nonempty (LiftingFunction p) :=
  ⟨IsHurewiczFibration.nonempty_liftingFunction, fun ⟨Λ⟩ ↦ Λ.isHurewiczFibration⟩

/-- A Hurewicz fibration for test spaces in `Type (max u v)` is a Hurewicz fibration for test
spaces in every universe. -/
theorem IsHurewiczFibration.up {p : E → B} (h : IsHurewiczFibration.{max u v} p) :
    IsHurewiczFibration.{w} p :=
  (IsHurewiczFibration.nonempty_liftingFunction (p := ⟨p, h.continuous⟩) h).some
    |>.isHurewiczFibration

/-! ### The endpoint map of a mapping-path replacement -/

namespace MappingPathSpace

variable {B : Type u'} {K : Type v'} [TopologicalSpace B] [TopologicalSpace K] (f : C(B, K))

/-- The path `γ` followed by `δ` on `[0, s]`, at speed `1 + s`. When `γ 1 = δ 0` this is a
continuous path from `γ 0` to `δ s`, equal to `γ` at `s = 0`. -/
private noncomputable def extendPath (γ δ : C(I, K)) (s u : I) : K :=
  if (1 + (s : ℝ)) * u ≤ 1 then IccExtend zero_le_one γ ((1 + (s : ℝ)) * u)
  else IccExtend zero_le_one δ ((1 + (s : ℝ)) * u - 1)

private theorem continuous_extendPath {Y : Type*} [TopologicalSpace Y] {γ δ : Y → C(I, K)}
    (hγ : Continuous γ) (hδ : Continuous δ) (h : ∀ y, γ y 1 = δ y 0) {s u : Y → I}
    (hs : Continuous s) (hu : Continuous u) :
    Continuous fun y ↦ extendPath (γ y) (δ y) (s y) (u y) := by
  have hγ' : Continuous fun q : Y × I ↦ γ q.1 q.2 := by fun_prop
  have hδ' : Continuous fun q : Y × I ↦ δ q.1 q.2 := by fun_prop
  refine Continuous.if_le (Continuous.IccExtend hγ' (by fun_prop))
    (Continuous.IccExtend hδ' (by fun_prop)) (by fun_prop) continuous_const fun y hy ↦ ?_
  rw [hy, sub_self, IccExtend_right, IccExtend_left]
  exact h y

private theorem extendPath_zero_left (γ δ : C(I, K)) (u : I) : extendPath γ δ 0 u = γ u := by
  simp [extendPath, u.2.2]

private theorem extendPath_zero_right (γ δ : C(I, K)) (s : I) : extendPath γ δ s 0 = γ 0 := by
  simp [extendPath, IccExtend_left]

private theorem extendPath_one_right {γ δ : C(I, K)} (h : γ 1 = δ 0) (s : I) :
    extendPath γ δ s 1 = δ s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [extendPath, h]
  · have hs : (0 : ℝ) < s := lt_of_le_of_ne s.2.1 fun h ↦ hs (Subtype.ext h.symm)
    simp [extendPath, hs.not_ge, IccExtend_val]

private theorem path_one_eq (x : MappingPathSpace (endpoint f)) :
    x.val.1.val.2 1 = x.val.2 0 :=
  (endpoint_apply f _).symm.trans x.property.symm

/-- The lifting function of the endpoint map of `MappingPathSpace f`: the lift of a path `δ`
from `(b, γ)` at time `s` is `b` together with `γ` followed by `δ` on `[0, s]`, at speed
`1 + s`. -/
noncomputable def endpointLiftingFunction : LiftingFunction (endpoint f) where
  toContinuousMap := ContinuousMap.curry
    { toFun q := ⟨(q.1.val.1.val.1,
        ⟨extendPath q.1.val.1.val.2 q.1.val.2 q.2, continuous_extendPath continuous_const
          continuous_const (fun _ ↦ path_one_eq f q.1) continuous_const continuous_id⟩),
        by simpa [extendPath_zero_right] using q.1.val.1.property⟩
      continuous_toFun := by
        refine (by fun_prop : Continuous fun q : MappingPathSpace (endpoint f) × I ↦
          q.1.val.1.val.1).prodMk ?_ |>.subtype_mk _
        refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
        exact continuous_extendPath (by fun_prop) (by fun_prop)
          (fun q : (MappingPathSpace (endpoint f) × I) × I ↦ path_one_eq f q.1.1)
          (by fun_prop) (by fun_prop) }
  apply_zero' x := by
    refine Subtype.ext (Prod.ext ?_ (ContinuousMap.ext fun u ↦ ?_))
    · simp
    · simpa using extendPath_zero_left _ _ u
  comp_apply' x := by
    ext s
    simp only [ContinuousMap.comp_apply, endpoint_apply, ContinuousMap.curry_apply,
      ContinuousMap.coe_mk]
    exact extendPath_one_right (path_one_eq f x) s

/-- The lifts of the endpoint map keep the source point fixed. -/
@[simp]
theorem endpointLiftingFunction_lift_val_fst (x : MappingPathSpace f) (δ : C(I, K))
    (h : δ 0 = endpoint f x) (s : I) :
    ((endpointLiftingFunction f).lift x δ h s).val.1 = x.val.1 := by
  simp [LiftingFunction.lift_def, endpointLiftingFunction]

/-- The path of a lift of the endpoint map: at time `s`, the original path `γ` followed by `δ` on
`[0, s]`, at speed `1 + s`. -/
theorem endpointLiftingFunction_lift_val_snd (x : MappingPathSpace f) (δ : C(I, K))
    (h : δ 0 = endpoint f x) (s u : I) :
    ((endpointLiftingFunction f).lift x δ h s).val.2 u =
      if (1 + (s : ℝ)) * u ≤ 1 then IccExtend zero_le_one x.val.2 ((1 + (s : ℝ)) * u)
      else IccExtend zero_le_one δ ((1 + (s : ℝ)) * u - 1) := by
  simp [LiftingFunction.lift_def, endpointLiftingFunction, extendPath]

/-- The endpoint map of a mapping-path replacement is a Hurewicz fibration, for test spaces in
every universe. -/
theorem isHurewiczFibration_endpoint : IsHurewiczFibration.{w} (endpoint f) :=
  (endpointLiftingFunction f).isHurewiczFibration

end MappingPathSpace

end TauCeti
