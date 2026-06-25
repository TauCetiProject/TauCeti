/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Topology.Homotopy.Lifting

/-!
# Covering maps, fundamental-group monodromy, and lifting

This file records generic covering-space consequences of Mathlib's path-lifting and
monodromy API. For a covering map `p : E → X`, it packages the fundamental-group
subgroup condition used by Mathlib's lifting criterion. When the total space is simply
connected, choosing a lift `e` over `x` also identifies `π₁(X, x)` with the fibre over
`x` by sending a loop class to its monodromy translate of `e`.

## Main declarations

* `TauCeti.IsCoveringMap.LiftCondition`: the fundamental-group subgroup inclusion in the
  lifting criterion.
* `TauCeti.IsCoveringMap.existsUnique_continuousMap_lifts_of_liftCondition`: Mathlib's
  lifting criterion stated using `LiftCondition`.
* `TauCeti.IsCoveringMap.fundamentalGroupEquivFiber`: the monodromy bijection
  `FundamentalGroup X x ≃ p ⁻¹' {x}`, `γ ↦ monodromy γ e`.

## References

This builds directly on Junyan Xu's covering-space lifting and monodromy API in
`Mathlib.Topology.Homotopy.Lifting`.
-/

public section

namespace TauCeti

namespace IsCoveringMap

variable {A E X : Type*} [TopologicalSpace A] [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X} {x : X}

/-- The subgroup condition in the lifting criterion.

For a continuous map `q : C(E, X)`, a map `f : C(A, X)`, and a chosen lift `e₀` of
`f a₀`, this says that the image of `π₁(A, a₀)` under `f` is contained in the image of
`π₁(E, e₀)` under `q`. When `q = ⟨p, hp.continuous⟩` for a covering map `p`, this is the
hypothesis needed to lift `f` uniquely through `p` with value `e₀` at `a₀`, assuming `A`
is path connected and locally path connected. -/
def LiftCondition (q : C(E, X)) (f : C(A, X)) (a₀ : A) (e₀ : E)
    (he : q e₀ = f a₀) : Prop :=
  (FundamentalGroup.map f a₀).range ≤ (FundamentalGroup.mapOfEq q he).range

/-- The lifting condition is exactly the fundamental-group image inclusion appearing in
Mathlib's covering-space lifting criterion. -/
lemma liftCondition_iff_range_le (q : C(E, X)) (f : C(A, X)) (a₀ : A) (e₀ : E)
    (he : q e₀ = f a₀) :
    LiftCondition q f a₀ e₀ he ↔
      (FundamentalGroup.map f a₀).range ≤ (FundamentalGroup.mapOfEq q he).range :=
  Iff.rfl

/-- The covering-space lifting criterion, stated using `LiftCondition`.

This is Mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts_of_range_le` with its
subgroup-inclusion hypothesis packaged as `LiftCondition`. The simply-connected special
case is Mathlib's `IsCoveringMap.existsUnique_continuousMap_lifts`. -/
theorem existsUnique_continuousMap_lifts_of_liftCondition
    [PathConnectedSpace A] [LocallyPathConnectedSpace A] (hp : IsCoveringMap p)
    {f : C(A, X)} {a₀ : A} {e₀ : E} (he : p e₀ = f a₀)
    (hcond : LiftCondition ⟨p, hp.continuous⟩ f a₀ e₀ he) :
    ∃! F : C(A, E), F a₀ = e₀ ∧ p ∘ F = f :=
  hp.existsUnique_continuousMap_lifts_of_range_le he hcond

/-- Choosing a basepoint lift `e` in the fibre over `x` identifies the fundamental group of
the base with that fibre, via `γ ↦ monodromy γ e`. -/
@[expose] noncomputable def fundamentalGroupEquivFiber [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e : p ⁻¹' {x}) :
    FundamentalGroup X x ≃ p ⁻¹' {x} :=
  { toFun γ := hp.monodromy γ e
    invFun e' :=
      FundamentalGroup.fromPath <|
        ((Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (e : E) (e' : E))).map
          ⟨p, hp.continuous⟩).cast e.2.symm e'.2.symm
    left_inv γ := by
      set Γ : Path.Homotopic.Quotient (e : E) (hp.monodromy γ e : E) :=
        hp.liftPathQuotient γ e
      have hpath :
          Path.Homotopic.Quotient.mk
              (PathConnectedSpace.somePath (e : E) (hp.monodromy γ e : E)) = Γ :=
        Subsingleton.elim _ _
      dsimp only
      rw [hpath, hp.map_liftPathQuotient]
      simp [Path.Homotopic.Quotient.cast_cast]
    right_inv e' := by
      obtain ⟨e₀, he₀⟩ := e
      obtain ⟨e₁, he₁⟩ := e'
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at he₀ he₁
      set Γ : Path.Homotopic.Quotient e₀ e₁ :=
        Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath e₀ e₁)
      dsimp only
      simpa [Γ] using
        hp.monodromy_eq_of_map_eq Γ (by simp [Γ, Path.Homotopic.Quotient.cast_cast]) }

/-- The general fibre equivalence sends a loop class to the monodromy translate of the chosen
lift, as an equality in the total space `E`. -/
@[simp]
lemma fundamentalGroupEquivFiber_apply_coe [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    (fundamentalGroupEquivFiber hp e γ : E) = (hp.monodromy γ e : E) :=
  rfl

/-- The general fibre equivalence sends a loop class to the monodromy translate of the chosen
lift, as an equality in the fibre subtype. -/
@[simp]
lemma fundamentalGroupEquivFiber_apply [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    fundamentalGroupEquivFiber hp e γ = hp.monodromy γ e :=
  rfl

/-- The inverse of the general fibre equivalence is characterized by the loop class whose
monodromy sends the chosen lift to the requested fibre point. -/
@[simp]
lemma fundamentalGroupEquivFiber_apply_symm_apply [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e e' : p ⁻¹' {x}) :
    hp.monodromy ((fundamentalGroupEquivFiber hp e).symm e') e = e' := by
  have h := (fundamentalGroupEquivFiber hp e).apply_symm_apply e'
  rw [fundamentalGroupEquivFiber_apply] at h
  exact h

/-- On underlying points, the inverse of the general fibre equivalence is characterized by
the loop class whose monodromy sends the chosen lift to the requested fibre point. -/
@[simp]
lemma fundamentalGroupEquivFiber_apply_symm_apply_coe [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e e' : p ⁻¹' {x}) :
    (hp.monodromy ((fundamentalGroupEquivFiber hp e).symm e') e : E) = e' := by
  exact congrArg Subtype.val (fundamentalGroupEquivFiber_apply_symm_apply hp e e')

end IsCoveringMap

end TauCeti
