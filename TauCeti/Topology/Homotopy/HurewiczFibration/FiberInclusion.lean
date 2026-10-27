/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.FiberHomotopyEquiv
public import TauCeti.Topology.Homotopy.MappingPath.Fiber
public import TauCeti.Topology.Homotopy.OpenBoxLifting

/-!
# The homotopy fibre of the fibre inclusion of a Hurewicz fibration

Let `p : E → B` be a continuous map, `e₀ : E` a point and `F = p⁻¹(p e₀)` the fibre through it.
The mapping-path fibre over `e₀` of the inclusion `F → E` is the space
`TauCeti.FiberInclusionPathFiber p e₀` of paths in `E` that start in `F` and end at `e₀`. Each
such path lies over a loop at `p e₀`, which gives the continuous map
`TauCeti.FiberInclusionPathFiber.loop p e₀` to the loop space `Ω B (p e₀)`.

When `p` is a Hurewicz fibration this map is again a Hurewicz fibration, and it is a fibre
homotopy equivalence over `Ω B (p e₀)`, so the homotopy fibre of `F → E` is homotopy equivalent
to `Ω B (p e₀)`. This identifies `Ω B` as the homotopy fibre of `F → E`, the step extending the
fibre sequence `F → E → B` of `p` to the left.

* The section `TauCeti.FiberInclusionPathFiber.loopSection` sends a loop `β` to the reverse of
  the lift of the reversed loop starting at `e₀`; it is a section on every loop component.
* The homotopy from the section after `loop` to the identity lifts, over the constant square
  `(s, t) ↦ β t`, the given path on one side, the section on the other and `e₀` on the end
  (`TauCeti.IsHurewiczFibration.exists_homotopy_lifts`).

No connectedness or other hypothesis is put on `E` or `B`, and the equivalence is unbased: the
lifts need not fix the constant path at `e₀`.

## Main definitions

* `TauCeti.FiberInclusionPathFiber p e₀`: the homotopy fibre over `e₀` of the inclusion of the
  fibre of `p` through `e₀`.
* `TauCeti.FiberInclusionPathFiber.loop`: the projection to the loop space `Ω B (p e₀)`.
* `TauCeti.FiberInclusionPathFiber.loopSection`: a section of `loop`.
* `TauCeti.FiberInclusionPathFiber.loopFiberHomotopyEquiv`: `loop` as a fibre homotopy
  equivalence over `Ω B (p e₀)`.
* `TauCeti.FiberInclusionPathFiber.loopHomotopyEquiv`: the homotopy equivalence with the loop
  space.

## Main results

* `TauCeti.FiberInclusionPathFiber.isHurewiczFibration_loop`: `loop` is a Hurewicz fibration.
* `TauCeti.FiberInclusionPathFiber.loopSection_comp_loop_homotopicWith`: the section after
  `loop` is homotopic to the identity through maps over `Ω B (p e₀)`.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter I.7.
* A. Hatcher, *Algebraic Topology*, Section 4.3.
* J. P. May, *A Concise Course in Algebraic Topology*, Chapter 8.
-/

public section

open unitInterval Topology.Homotopy

universe w u v

namespace TauCeti

variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

/-- The homotopy fibre over `e₀` of the inclusion of the fibre `p⁻¹(p e₀)` into `E`: a point `x`
of the fibre together with a path in `E` from `x` to `e₀`. -/
abbrev FiberInclusionPathFiber (p : C(E, B)) (e₀ : E) :=
  MappingPathFiber (ContinuousMap.subtypeVal (p ⁻¹' {p e₀})) e₀

namespace FiberInclusionPathFiber

variable {p : C(E, B)} {e₀ : E}

/-- A point of the homotopy fibre of a fibre inclusion is determined by its path. -/
@[ext]
theorem ext {x y : FiberInclusionPathFiber p e₀}
    (h : ∀ t, x.val.2 t = y.val.2 t) : x = y := by
  refine Subtype.ext (Prod.ext (Subtype.ext ?_) (ContinuousMap.ext h))
  exact x.property.1.symm.trans ((h 0).trans y.property.1)

/-- The path of a point of the homotopy fibre of the fibre inclusion starts in the fibre. -/
theorem apply_path_zero (x : FiberInclusionPathFiber p e₀) : p (x.val.2 0) = p e₀ :=
  x.property.1 ▸ x.val.1.property

variable (p e₀)

/-- The path of a point of the homotopy fibre of the fibre inclusion lies over a loop at
`p e₀`: the projection from the homotopy fibre of the fibre inclusion to the loop space. -/
def loop : C(FiberInclusionPathFiber p e₀, Ω B (p e₀)) where
  toFun x := ⟨p.comp x.val.2, apply_path_zero x, congrArg p x.property.2⟩
  continuous_toFun := continuous_induced_rng.2 <|
    (ContinuousMap.continuous_postcomp p).comp continuous_subtype_val.snd

@[simp]
theorem loop_apply (x : FiberInclusionPathFiber p e₀) (t : I) :
    loop p e₀ x t = p (x.val.2 t) :=
  (rfl)

variable {p}

variable {Y : Type*} [TopologicalSpace Y]

/-- A continuous family of paths in `E` from the fibre through `e₀` to `e₀`, parametrized by `Y`,
as a continuous map into the homotopy fibre of the fibre inclusion. -/
private def ofFamily (G : C(Y × I, E)) (h₀ : ∀ y, p (G (y, 0)) = p e₀)
    (h₁ : ∀ y, G (y, 1) = e₀) : C(Y, FiberInclusionPathFiber p e₀) where
  toFun y := ⟨(⟨G (y, 0), h₀ y⟩, G.curry y), rfl, h₁ y⟩
  continuous_toFun := (((G.continuous.comp (continuous_id.prodMk continuous_const)).subtype_mk
    _).prodMk G.curry.continuous).subtype_mk _

@[simp]
private theorem ofFamily_val_fst (G : C(Y × I, E)) (h₀ : ∀ y, p (G (y, 0)) = p e₀)
    (h₁ : ∀ y, G (y, 1) = e₀) (y : Y) : ((ofFamily e₀ G h₀ h₁ y).val.1 : E) = G (y, 0) :=
  (rfl)

@[simp]
private theorem ofFamily_val_snd (G : C(Y × I, E)) (h₀ : ∀ y, p (G (y, 0)) = p e₀)
    (h₁ : ∀ y, G (y, 1) = e₀) (y : Y) (t : I) : (ofFamily e₀ G h₀ h₁ y).val.2 t = G (y, t) :=
  (rfl)

/-- **The loop projection is a Hurewicz fibration.** For a Hurewicz fibration `p`, the projection
from the homotopy fibre of the inclusion of the fibre through `e₀` to the loop space
`Ω B (p e₀)` is a Hurewicz fibration. -/
theorem isHurewiczFibration_loop (hp : IsHurewiczFibration.{w} p) :
    IsHurewiczFibration.{w} (loop p e₀) := by
  refine isHurewiczFibration_iff.2 ⟨(loop p e₀).continuous, fun A _ f H hH ↦ ?_⟩
  -- The lifting problem as a relative lifting problem for the open box, coordinates `(t, u)`:
  -- the given paths on the bottom, their fixed starting points and `e₀` on the two sides.
  let g : C(A × (I × I), E) := ⟨fun y ↦ (f y.1).val.2 y.2.1, by fun_prop⟩
  let H' : C(A × (I × I), B) := ⟨fun y ↦ H (y.2.2, y.1) y.2.1, by fun_prop⟩
  have hg : ∀ a (x : I × I), x.2 = 0 ∨ x.1 = 0 ∨ x.1 = 1 → p (g (a, x)) = H' (a, x) := by
    rintro a ⟨t, u⟩ (h | h | h)
    · obtain rfl : u = 0 := h
      simp [g, H', hH a]
    · obtain rfl : t = 0 := h
      simp [g, H', apply_path_zero]
    · obtain rfl : t = 1 := h
      simp [g, H', (f a).property.2]
  obtain ⟨G, hG, hGg⟩ := hp.exists_lift_openBox g H' hg
  have hG₀ : ∀ y : I × A, G (y.2, (0, y.1)) = (f y.2).val.1 := fun y ↦ by
    rw [hGg _ _ (Or.inr (Or.inl rfl))]
    exact (f y.2).property.1
  have hG₁ : ∀ y : I × A, G (y.2, (1, y.1)) = e₀ := fun y ↦ by
    rw [hGg _ _ (Or.inr (Or.inr rfl))]
    exact (f y.2).property.2
  let L : C(I × A, FiberInclusionPathFiber p e₀) :=
    ofFamily e₀ (G.comp ⟨fun y : (I × A) × I ↦ (y.1.2, (y.2, y.1.1)), by fun_prop⟩)
    (fun y ↦ (congrArg p (hG₀ y)).trans (f y.2).val.1.property) hG₁
  refine ⟨L, funext fun y ↦ Path.ext (funext fun t ↦ ?_), fun a ↦ ?_⟩
  · simpa [L, H'] using congrFun hG (y.2, (t, y.1))
  · ext t
    simpa [L, g] using hGg a (t, 0) (Or.inl rfl)

/-- The lift of the reversed loop `t ↦ β (1 - t)` from `e₀`, a family of paths parametrized by
the loop space and lying over the reversed loops. -/
private theorem exists_lift_symm (hp : IsHurewiczFibration.{v} p) :
    ∃ L : C(I × Ω B (p e₀), E), (∀ y, p (L y) = y.2 (σ y.1)) ∧ ∀ β, L (0, β) = e₀ := by
  obtain ⟨L, hL, hL₀⟩ := hp.hasHomotopyLiftingProperty (Ω B (p e₀)) (.const _ e₀)
    ⟨fun y ↦ y.2 (σ y.1), by fun_prop⟩ fun β ↦ by simp
  exact ⟨L, congrFun hL, hL₀⟩

/-- A chosen lift of the reversed loops from `e₀`. -/
private noncomputable def liftSymm (hp : IsHurewiczFibration.{v} p) : C(I × Ω B (p e₀), E) :=
  (exists_lift_symm e₀ hp).choose

private theorem apply_liftSymm (hp : IsHurewiczFibration.{v} p) (y : I × Ω B (p e₀)) :
    p (liftSymm e₀ hp y) = y.2 (σ y.1) :=
  (exists_lift_symm e₀ hp).choose_spec.1 y

private theorem liftSymm_zero (hp : IsHurewiczFibration.{v} p) (β : Ω B (p e₀)) :
    liftSymm e₀ hp (0, β) = e₀ :=
  (exists_lift_symm e₀ hp).choose_spec.2 β

/-- A **section of the loop projection**: a loop `β` at `p e₀` is sent to the reverse of the lift
of the reversed loop `t ↦ β (1 - t)` from `e₀`, a path from the fibre to `e₀` over `β`. The
section is defined on every loop component. -/
noncomputable def loopSection (hp : IsHurewiczFibration.{v} p) :
    C(Ω B (p e₀), FiberInclusionPathFiber p e₀) :=
  ofFamily e₀ ((liftSymm e₀ hp).comp ⟨fun y ↦ (σ y.2, y.1), by fun_prop⟩)
    (fun β ↦ by simpa using apply_liftSymm e₀ hp (1, β))
    (fun β ↦ by simpa using liftSymm_zero e₀ hp β)

/-- The section of the loop projection lies over the given loop. -/
@[simp]
theorem loop_loopSection (hp : IsHurewiczFibration.{v} p) (β : Ω B (p e₀)) :
    loop p e₀ (loopSection e₀ hp β) = β := by
  ext t
  simpa [loopSection] using apply_liftSymm e₀ hp (σ t, β)

/-- The section of the loop projection is a right inverse of the loop projection. -/
@[simp]
theorem loop_comp_loopSection (hp : IsHurewiczFibration.{v} p) :
    (loop p e₀).comp (loopSection e₀ hp) = .id _ :=
  ContinuousMap.ext (loop_loopSection e₀ hp)

/-- **The section of the loop projection is a fibrewise homotopy inverse.** The composite of the
loop projection and its section is homotopic to the identity through maps over `Ω B (p e₀)`. -/
theorem loopSection_comp_loop_homotopicWith (hp : IsHurewiczFibration.{v} p)
    (hp' : IsHurewiczFibration.{u} p) :
    ((loopSection e₀ hp).comp (loop p e₀)).HomotopicWith (.id _)
      fun f ↦ (loop p e₀).comp f = loop p e₀ := by
  -- The two families of reversed paths from `e₀`, both over the reversed loop of each point.
  let γ : C(FiberInclusionPathFiber p e₀ × I, B) := ⟨fun y ↦ p (y.1.val.2 (σ y.2)), by fun_prop⟩
  let α : C(FiberInclusionPathFiber p e₀ × I, E) :=
    ⟨fun y ↦ (loopSection e₀ hp (loop p e₀ y.1)).val.2 (σ y.2),
      (continuous_subtype_val.comp ((loopSection e₀ hp).continuous.comp
        ((loop p e₀).continuous.comp continuous_fst))).snd.eval
        (continuous_symm.comp continuous_snd)⟩
  let α' : C(FiberInclusionPathFiber p e₀ × I, E) := ⟨fun y ↦ y.1.val.2 (σ y.2), by fun_prop⟩
  have hα : ∀ y t, p (α (y, t)) = γ (y, t) := fun y t ↦ by
    simpa only [α, γ, ContinuousMap.coe_mk, loop_apply] using
      congrArg (· (σ t)) (loop_loopSection e₀ hp (loop p e₀ y))
  have h₀ : ∀ y, α (y, 0) = α' (y, 0) := fun y ↦ by
    simp [α, α', (loopSection e₀ hp _).property.2, y.property.2]
  obtain ⟨G, hG₀, hG₁, hG, hpG⟩ :=
    hp'.exists_homotopy_lifts γ α α' hα (fun _ _ ↦ (rfl)) h₀
  have hG' : ∀ x s, G (x, (s, 0)) = e₀ := fun x s ↦ by
    simpa [α, (loopSection e₀ hp _).property.2] using hG x s
  -- The homotopy reverses the lifted paths `t ↦ G (x, (s, t))` back.
  let K : C(I × FiberInclusionPathFiber p e₀, FiberInclusionPathFiber p e₀) :=
    ofFamily e₀ (G.comp ⟨fun y : (I × FiberInclusionPathFiber p e₀) × I ↦
      (y.1.2, (y.1.1, σ y.2)), by fun_prop⟩)
    (fun y ↦ by simpa [γ, apply_path_zero] using hpG y.2 y.1 1) (fun y ↦ by simpa using hG' y.2 y.1)
  refine ⟨⟨⟨K, fun x ↦ ?_, fun x ↦ ?_⟩, fun s ↦ ContinuousMap.ext fun x ↦ ?_⟩⟩
  · ext t
    simpa [K, α] using hG₀ x (σ t)
  · ext t
    simpa [K, α'] using hG₁ x (σ t)
  · ext t
    simpa [K, γ] using hpG x s (σ t)

/-- **The loop projection is a fibre homotopy equivalence.** For a Hurewicz fibration `p`, the
projection from the homotopy fibre of the inclusion of the fibre through `e₀` to the loop space
`Ω B (p e₀)` is a fibre homotopy equivalence over `Ω B (p e₀)` with its identity map. -/
noncomputable def loopFiberHomotopyEquiv (hp : IsHurewiczFibration.{max u v} p) :
    FiberHomotopyEquiv (loop p e₀) (.id (Ω B (p e₀))) where
  toFun := loop p e₀
  invFun := loopSection e₀ hp.down
  comp_toFun := ContinuousMap.id_comp _
  comp_invFun := loop_comp_loopSection e₀ hp.down
  left_inv := loopSection_comp_loop_homotopicWith e₀ hp.down hp.down
  right_inv := by
    rw [loop_comp_loopSection]
    exact .refl _ (ContinuousMap.id_comp _)

@[simp]
theorem loopFiberHomotopyEquiv_toFun (hp : IsHurewiczFibration.{max u v} p) :
    (loopFiberHomotopyEquiv e₀ hp).toFun = loop p e₀ :=
  (rfl)

@[simp]
theorem loopFiberHomotopyEquiv_invFun (hp : IsHurewiczFibration.{max u v} p) :
    (loopFiberHomotopyEquiv e₀ hp).invFun = loopSection e₀ hp.down :=
  (rfl)

/-- **The homotopy fibre of the fibre inclusion is the loop space of the base.** For a Hurewicz
fibration `p`, the space of paths in `E` from the fibre through `e₀` to `e₀` is homotopy
equivalent to the loop space `Ω B (p e₀)`, by composing the paths with `p`. -/
noncomputable def loopHomotopyEquiv (hp : IsHurewiczFibration.{max u v} p) :
    ContinuousMap.HomotopyEquiv (FiberInclusionPathFiber p e₀) (Ω B (p e₀)) :=
  (loopFiberHomotopyEquiv e₀ hp).toHomotopyEquiv

@[simp]
theorem loopHomotopyEquiv_apply (hp : IsHurewiczFibration.{max u v} p)
    (x : FiberInclusionPathFiber p e₀) : loopHomotopyEquiv e₀ hp x = loop p e₀ x :=
  FiberHomotopyEquiv.toHomotopyEquiv_apply _ x

@[simp]
theorem loopHomotopyEquiv_symm_apply (hp : IsHurewiczFibration.{max u v} p) (β : Ω B (p e₀)) :
    (loopHomotopyEquiv e₀ hp).symm β = loopSection e₀ hp.down β :=
  FiberHomotopyEquiv.toHomotopyEquiv_symm_apply _ β

end FiberInclusionPathFiber

end TauCeti
