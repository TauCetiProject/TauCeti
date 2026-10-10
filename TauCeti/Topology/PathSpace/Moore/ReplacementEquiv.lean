/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv
public import TauCeti.Topology.PathSpace.Moore.Replacement

/-!
# The Moore-path replacement of a Hurewicz fibration

When `p : E → B` is a Hurewicz fibration, the inclusion `E → E'`, `e ↦ (e, const)`, into its
Moore-path replacement is a **fibre homotopy equivalence** over `B`
(`TauCeti.MooreReplacement.fiberHomotopyEquiv`), and so the fibre `F` of `p` over `b` is homotopy
equivalent to the fibre `F'` of the replacement
(`TauCeti.MooreReplacement.fiberHomotopyEquivFiber`).
The inverse is built by lifting, from `e`, the homotopy `s ↦ γ (s · γ.length)` traced by the path of
each pair `(e, γ)`: its end `ρ (e, γ)` lies over `γ.target`, and the two homotopies are vertical,
`(s, e) ↦ G (s, (e, const))` on `E` and `(s, (e, γ)) ↦ (G (s, (e, γ)), γ|[s · γ.length, γ.length])`
on `E'`.  This uses the homotopy lifting property with respect to `E'` itself, so the universe of
test spaces is that of `E'`.

The endpoint evaluation `P_{A→X} X → X` of the Moore paths starting in a subset `A` is the
Moore-path replacement of the inclusion `A → X`, up to a homeomorphism over `X`
(`TauCeti.MooreReplacement.homeomorphPathsFrom`), so it is a Hurewicz fibration
(`TauCeti.MoorePath.isHurewiczFibration_target`).

## Main definitions

* `TauCeti.MooreReplacement.retraction`: the inverse `E' → E` over `B`, for a Hurewicz fibration.
* `TauCeti.MooreReplacement.fiberHomotopyEquiv`: the fibre homotopy equivalence `E → E'`.
* `TauCeti.MooreReplacement.homeomorphPathsFrom`: `P_{A→X} X` as the replacement of `A → X`.

## Main results

* `TauCeti.MooreReplacement.fiberHomotopyEquivFiber`: `F ≃ₕ F'` for a Hurewicz fibration.
* `TauCeti.MoorePath.isHurewiczFibration_target`: the endpoint evaluation is a Hurewicz fibration.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Morse homology with differential graded
  coefficients*, Progress in Mathematics 360, Birkhäuser, 2025, §7.1 (after Dold and Kamps).
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
-/

public noncomputable section

open scoped NNReal
open unitInterval ContinuousMap

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

namespace MooreReplacement

/-- The homotopy of `B` traced by the paths of the pairs: `(s, (e, γ)) ↦ γ (s · γ.length)`. -/
def pathHomotopy (p : C(E, B)) : C(I × MooreReplacement p, B) :=
  ⟨fun y ↦ y.2.path (toNNReal y.1 * y.2.path.length),
    (continuous_path.comp continuous_snd).moorePath_eval ((toNNReal_continuous.comp
      continuous_fst).mul (MoorePath.continuous_length.comp (continuous_path.comp continuous_snd)))⟩

@[simp]
theorem pathHomotopy_apply {p : C(E, B)} (s : I) (x : MooreReplacement p) :
    pathHomotopy p (s, x) = x.path (toNNReal s * x.path.length) :=
  (rfl)

theorem pathHomotopy_zero {p : C(E, B)} (x : MooreReplacement p) :
    pathHomotopy p (0, x) = p (proj p x) := by
  rw [pathHomotopy_apply, toNNReal_zero, zero_mul, ← MoorePath.source_def, source_path,
    proj_apply]

/-- For a Hurewicz fibration `p`, the homotopy traced by each pair `(e, γ)` lifts from `e`. -/
theorem exists_liftedHomotopy {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p) :
    ∃ G : C(I × MooreReplacement p, E), p ∘ G = pathHomotopy p ∧ ∀ x, G (0, x) = proj p x :=
  hp.hasHomotopyLiftingProperty (MooreReplacement p) (proj p) (pathHomotopy p) pathHomotopy_zero

/-- For a Hurewicz fibration `p`, a lift from `e` of the homotopy `s ↦ γ (s · γ.length)` traced by
each pair `(e, γ)`. -/
def liftedHomotopy {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p) :
    C(I × MooreReplacement p, E) :=
  (exists_liftedHomotopy hp).choose

theorem apply_liftedHomotopy {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p)
    (y : I × MooreReplacement p) : p (liftedHomotopy hp y) = pathHomotopy p y :=
  congrFun (exists_liftedHomotopy hp).choose_spec.1 y

theorem liftedHomotopy_zero {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p)
    (x : MooreReplacement p) : liftedHomotopy hp (0, x) = x.point :=
  ((exists_liftedHomotopy hp).choose_spec.2 x).trans
    (proj_apply x)

/-- For a Hurewicz fibration `p`, the inverse `E' → E` over `B` of the inclusion: the end of the
lift of the path of each pair. -/
def retraction {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p) :
    C(MooreReplacement p, E) :=
  (liftedHomotopy hp).comp ⟨fun x ↦ (1, x), by fun_prop⟩

theorem retraction_apply {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p)
    (x : MooreReplacement p) : retraction hp x = liftedHomotopy hp (1, x) :=
  (rfl)

@[simp]
theorem apply_retraction {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p)
    (x : MooreReplacement p) : p (retraction hp x) = x.path.target := by
  rw [retraction_apply, apply_liftedHomotopy, pathHomotopy_apply, toNNReal_one, one_mul,
    MoorePath.target_def]

theorem source_drop_pathHomotopy {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p)
    (y : I × MooreReplacement p) :
    (y.2.path.drop (toNNReal y.1 * y.2.path.length)).source = p (liftedHomotopy hp y) := by
  rw [MoorePath.source_drop, apply_liftedHomotopy, pathHomotopy_apply]

/-- The vertical homotopy on `E` from the identity to `retraction ∘ incl`:
`(s, e) ↦ G (s, (e, const))`. -/
def leftHomotopy {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p) :
    HomotopyWith (.id E) ((retraction hp).comp (incl p)) fun f ↦ p.comp f = p where
  toFun y := liftedHomotopy hp (y.1, incl p y.2)
  continuous_toFun := (liftedHomotopy hp).continuous.comp
    (continuous_fst.prodMk ((incl p).continuous.comp continuous_snd))
  map_zero_left e := (liftedHomotopy_zero hp (incl p e)).trans (point_incl e)
  map_one_left _ := rfl
  prop' s := ContinuousMap.ext fun e ↦ by
    change p (liftedHomotopy hp (s, incl p e)) = p e
    rw [apply_liftedHomotopy, pathHomotopy_apply, path_incl, MoorePath.refl_apply]

/-- The vertical homotopy on `E'` from the identity to `incl ∘ retraction`:
`(s, (e, γ)) ↦ (G (s, (e, γ)), γ|[s · γ.length, γ.length])`. -/
def rightHomotopy {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p) :
    HomotopyWith (.id (MooreReplacement p)) ((incl p).comp (retraction hp))
      fun f ↦ (endpoint p).comp f = endpoint p where
  toFun y := mk (liftedHomotopy hp y) (y.2.path.drop (toNNReal y.1 * y.2.path.length))
    (source_drop_pathHomotopy hp y)
  continuous_toFun := continuous_mk (liftedHomotopy hp).continuous
    ((continuous_path.comp continuous_snd).moorePath_drop ((toNNReal_continuous.comp
      continuous_fst).mul (MoorePath.continuous_length.comp (continuous_path.comp
        continuous_snd)))) _
  map_zero_left x := ext (by simpa using liftedHomotopy_zero hp x) (by simp)
  map_one_left x := ext (by simp [retraction_apply]) (by simp)
  prop' s := ContinuousMap.ext fun x ↦ by simp

/-- **The inclusion of a Hurewicz fibration into its Moore-path replacement is a fibre homotopy
equivalence** over `B`, with inverse `retraction`. -/
def fiberHomotopyEquiv {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p) :
    FiberHomotopyEquiv p (endpoint p) where
  toFun := incl p
  invFun := retraction hp
  comp_toFun := ContinuousMap.ext fun e ↦ by simp
  comp_invFun := ContinuousMap.ext fun x ↦ by simp
  left_inv := ⟨(leftHomotopy hp).symm⟩
  right_inv := ⟨(rightHomotopy hp).symm⟩

/-- For a Hurewicz fibration, the fibre over `b` is homotopy equivalent to the fibre `F'` of the
Moore-path replacement, by `f ↦ (f, const)`. -/
def fiberHomotopyEquivFiber {p : C(E, B)} (hp : IsHurewiczFibration.{max u v} p) (b : B) :
    HomotopyEquiv {e // p e = b} (Fiber p b) :=
  ((fiberHomotopyEquiv hp).fiber b).trans
    ((Homeomorph.refl (MooreReplacement p)).subtype fun x ↦ by
      rw [endpoint_apply, Homeomorph.refl_apply, id_eq]).toHomotopyEquiv

/-! ### The endpoint evaluation -/

variable {X : Type u} [TopologicalSpace X]

theorem source_path_mem {A : Set X} (x : MooreReplacement (ContinuousMap.subtypeVal A)) :
    x.path.source ∈ A := by
  rw [source_path]
  exact x.point.2

/-- The Moore paths starting in `A` are the Moore-path replacement of the inclusion `A → X`. -/
def homeomorphPathsFrom (A : Set X) :
    MooreReplacement (ContinuousMap.subtypeVal A) ≃ₜ {γ : MoorePath X // γ.source ∈ A} where
  toFun x := ⟨x.path, source_path_mem x⟩
  invFun γ := mk ⟨γ.1.source, γ.2⟩ γ.1 rfl
  left_inv x := ext (Subtype.ext (by simp)) (by simp)
  right_inv γ := Subtype.ext (path_mk _ _ _)
  continuous_toFun := continuous_path.subtype_mk _
  continuous_invFun := continuous_mk ((MoorePath.continuous_source.comp
    continuous_subtype_val).subtype_mk _) continuous_subtype_val _

@[simp]
theorem path_homeomorphPathsFrom_symm (A : Set X) (γ : {γ : MoorePath X // γ.source ∈ A}) :
    ((homeomorphPathsFrom A).symm γ).path = γ.1 :=
  path_mk _ _ _

end MooreReplacement

/-- The **endpoint evaluation** `P_{A→X} X → X` of the Moore paths starting in a subset `A` is a
Hurewicz fibration. -/
theorem MoorePath.isHurewiczFibration_target {X : Type u} [TopologicalSpace X] (A : Set X) :
    IsHurewiczFibration.{w} fun γ : {γ : MoorePath X // γ.source ∈ A} ↦ γ.1.target := by
  convert (MooreReplacement.isHurewiczFibration_endpoint.{w} _).comp_homeomorph
    (MooreReplacement.homeomorphPathsFrom A).symm using 1
  funext γ
  rw [Function.comp_apply, MooreReplacement.endpoint_apply,
    MooreReplacement.path_homeomorphPathsFrom_symm]

end TauCeti
