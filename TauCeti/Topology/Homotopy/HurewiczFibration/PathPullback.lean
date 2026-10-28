/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HurewiczFibration.Basic
public import Mathlib.Topology.Homotopy.Equiv

/-!
# Fibres of a Hurewicz fibration along a path

For a continuous path `α : C(I, B)`, `PathPullback p α` is the pullback of `p : C(E, B)`
along `α`. If `p` is a Hurewicz fibration, the inclusion of the fibre over `α a` into this
pullback is a homotopy equivalence for every `a : I`. Its inverse is obtained by lifting
the contraction of the interval to `a`, with the whole pullback as parameter space.

Consequently any two fibres along the supplied path are homotopy equivalent. In particular,
`PathPullback.fiberHomotopyEquiv hp 0 1` compares the endpoint fibres, with forward map
`toFiber hp 1 ∘ inclusion 0` and reverse map `toFiber hp 0 ∘ inclusion 1`.
These are ordinary, unbased homotopy equivalences: lifting need not fix constant paths.
No nonemptiness hypothesis is needed, and the equivalence depends on the supplied path.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2.
-/

public section

open unitInterval

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- The pullback of `p` along a continuous path `α`, with its subspace topology. -/
abbrev PathPullback (p : C(E, B)) (α : C(I, B)) :=
  {x : I × E // α x.1 = p x.2}

namespace PathPullback

variable {p : C(E, B)} {α : C(I, B)}

/-- The pullback projection to the interval. -/
def projection : C(PathPullback p α, I) :=
  ⟨fun x ↦ x.val.1, by fun_prop⟩

@[simp]
theorem projection_apply (x : PathPullback p α) : projection x = x.val.1 :=
  (rfl)

/-- The inclusion into the path pullback of the fibre over `α a`. -/
def inclusion (a : I) : C(p ⁻¹' {α a}, PathPullback p α) :=
  ⟨fun x ↦ ⟨(a, x.val), x.property.symm⟩, by fun_prop⟩

@[simp]
theorem inclusion_val (a : I) (x : p ⁻¹' {α a}) : (inclusion a x).val = (a, x.val) :=
  (rfl)

/-- The projection of a path pullback of a Hurewicz fibration is a Hurewicz fibration. -/
theorem isHurewiczFibration_projection (hp : IsHurewiczFibration.{w} p) :
    IsHurewiczFibration.{w} (projection (p := p) (α := α)) :=
  hp.pullback α

private theorem exists_contractionLift (hp : IsHurewiczFibration.{u} p) (a : I) :
    ∃ G : C(I × PathPullback p α, PathPullback p α),
      (∀ z, projection (G z) = Set.Icc.convexComb (projection z.2) a z.1) ∧
      ∀ x, G (0, x) = x := by
  obtain ⟨G, hG, hG₀⟩ := (isHurewiczFibration_projection (α := α) hp).hasHomotopyLiftingProperty
    (PathPullback p α) (.id _)
    ⟨fun z ↦ Set.Icc.convexComb (projection z.2) a z.1, by fun_prop⟩
    (fun x ↦ by simp)
  exact ⟨G, congrFun hG, hG₀⟩

private noncomputable def contractionLift (hp : IsHurewiczFibration.{u} p) (a : I) :
    C(I × PathPullback p α, PathPullback p α) :=
  (exists_contractionLift (α := α) hp a).choose

private theorem projection_contractionLift (hp : IsHurewiczFibration.{u} p) (a : I)
    (z : I × PathPullback p α) :
    projection (contractionLift hp a z) = Set.Icc.convexComb (projection z.2) a z.1 :=
  (exists_contractionLift (α := α) hp a).choose_spec.1 z

private theorem contractionLift_zero (hp : IsHurewiczFibration.{u} p) (a : I)
    (x : PathPullback p α) : contractionLift hp a (0, x) = x :=
  (exists_contractionLift (α := α) hp a).choose_spec.2 x

private theorem contractionLift_one_projection (hp : IsHurewiczFibration.{u} p) (a : I)
    (x : PathPullback p α) : (contractionLift hp a (1, x)).val.1 = a := by
  simpa only [Set.Icc.convexComb_one, projection_apply] using
    projection_contractionLift hp a (1, x)

/-- A homotopy inverse of the fibre inclusion, obtained by lifting contraction to `a`.
This map need not be a strict retraction, since constant paths need not have constant lifts. -/
noncomputable def toFiber (hp : IsHurewiczFibration.{u} p) (a : I) :
    C(PathPullback p α, p ⁻¹' {α a}) :=
  ⟨fun x ↦ ⟨(contractionLift hp a (1, x)).val.2, by
      exact (contractionLift hp a (1, x)).property.symm.trans
        (congrArg α (contractionLift_one_projection hp a x))⟩,
    by fun_prop⟩

private theorem inclusion_toFiber (hp : IsHurewiczFibration.{u} p) (a : I)
    (x : PathPullback p α) : inclusion a (toFiber hp a x) = contractionLift hp a (1, x) := by
  exact Subtype.ext (Prod.ext (contractionLift_one_projection hp a x).symm rfl)

/-- The inclusion after its homotopy inverse is homotopic to the identity of the pullback. -/
theorem inclusion_comp_toFiber_homotopic (hp : IsHurewiczFibration.{u} p) (a : I) :
    ((inclusion a).comp (toFiber (α := α) hp a)).Homotopic (.id _) := by
  refine ContinuousMap.Homotopic.symm ⟨{
    toContinuousMap := contractionLift hp a
    map_zero_left := contractionLift_zero hp a
    map_one_left := fun x ↦ (inclusion_toFiber hp a x).symm }⟩

/-- The homotopy inverse after inclusion is homotopic to the identity of the fibre.
The lifted contraction stays in this fibre when restricted to its inclusion. -/
theorem toFiber_comp_inclusion_homotopic (hp : IsHurewiczFibration.{u} p) (a : I) :
    ((toFiber (α := α) hp a).comp (inclusion a)).Homotopic (.id _) := by
  have hfibre (z : I × (p ⁻¹' {α a})) :
      p (contractionLift hp a (z.1, inclusion a z.2)).val.2 = α a :=
    (contractionLift hp a (z.1, inclusion a z.2)).property.symm.trans
      (congrArg α (by simpa using projection_contractionLift hp a (z.1, inclusion a z.2)))
  refine ContinuousMap.Homotopic.symm ⟨{
    toFun := fun z ↦ ⟨(contractionLift hp a (z.1, inclusion a z.2)).val.2, hfibre z⟩
    continuous_toFun := (continuous_subtype_val.comp ((contractionLift hp a).continuous.comp
      (continuous_fst.prodMk ((inclusion a).continuous.comp continuous_snd)))).snd.subtype_mk hfibre
    map_zero_left := fun x ↦ Subtype.ext ?_
    map_one_left := fun _ ↦ rfl }⟩
  exact congrArg (fun y : PathPullback p α ↦ y.val.2)
    (contractionLift_zero hp a (inclusion a x))

/-- The fibre over any point of the interval is homotopy equivalent to the path pullback,
with forward map the actual fibre inclusion. -/
noncomputable def inclusionHomotopyEquiv (hp : IsHurewiczFibration.{u} p) (a : I) :
    ContinuousMap.HomotopyEquiv (p ⁻¹' {α a}) (PathPullback p α) where
  toFun := inclusion a
  invFun := toFiber hp a
  left_inv := toFiber_comp_inclusion_homotopic hp a
  right_inv := inclusion_comp_toFiber_homotopic hp a

@[simp]
theorem inclusionHomotopyEquiv_apply (hp : IsHurewiczFibration.{u} p) (a : I)
    (x : p ⁻¹' {α a}) : inclusionHomotopyEquiv hp a x = inclusion a x :=
  (rfl)

@[simp]
theorem inclusionHomotopyEquiv_symm_apply (hp : IsHurewiczFibration.{u} p) (a : I)
    (x : PathPullback p α) : (inclusionHomotopyEquiv hp a).symm x = toFiber hp a x :=
  (rfl)

/-- Fibres at any two times of a supplied path are homotopy equivalent. The forward map is
the inclusion at `a` followed by contraction to `b`; the reverse uses the opposite contractions.
Taking `a = 0` and `b = 1` gives transport between the endpoint fibres, including empty fibres. -/
noncomputable def fiberHomotopyEquiv (hp : IsHurewiczFibration.{u} p) (a b : I) :
    ContinuousMap.HomotopyEquiv (p ⁻¹' {α a}) (p ⁻¹' {α b}) :=
  (inclusionHomotopyEquiv hp a).trans (inclusionHomotopyEquiv hp b).symm

@[simp]
theorem fiberHomotopyEquiv_apply (hp : IsHurewiczFibration.{u} p) (a b : I)
    (x : p ⁻¹' {α a}) : fiberHomotopyEquiv hp a b x = toFiber hp b (inclusion a x) :=
  (rfl)

@[simp]
theorem fiberHomotopyEquiv_symm_apply (hp : IsHurewiczFibration.{u} p) (a b : I)
    (x : p ⁻¹' {α b}) : (fiberHomotopyEquiv hp a b).symm x = toFiber hp a (inclusion b x) :=
  (rfl)

end PathPullback

end TauCeti
