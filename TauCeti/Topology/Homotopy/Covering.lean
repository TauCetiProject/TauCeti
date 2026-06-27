/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Topology.Homotopy.FundamentalGroup
public import Mathlib.Topology.Homotopy.Lifting

/-!
# Covering maps and fundamental-group monodromy

This file records generic covering-space consequences of Mathlib's path-lifting and
monodromy API. For a covering map `p : E → X` whose total space is simply connected,
choosing a lift `e` over `x` identifies `π₁(X, x)` with the fibre over `x` by sending a
loop class to its monodromy translate of `e`.

## Main declarations

* `TauCeti.IsCoveringMap.fundamentalGroupEquivFiber`: the monodromy bijection
  `FundamentalGroup X x ≃ p ⁻¹' {x}`, `γ ↦ monodromy γ e`.
* `TauCeti.IsCoveringMap.fundamentalGroupEquivFiber_apply_symm_apply`: the inverse sends a
  fibre point to the loop class whose monodromy translate of the chosen lift is that point.

## References

This builds directly on Junyan Xu's covering-space lifting and monodromy API in
`Mathlib.Topology.Homotopy.Lifting`.
-/

public section

namespace TauCeti

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X] {p : E → X} {x : X}
variable {A : Type*} [TopologicalSpace A]

open FundamentalGroup

/-- Choosing a basepoint lift `e` in the fibre over `x` identifies the fundamental group of
the base with that fibre, via `γ ↦ monodromy γ e`. -/
@[expose] noncomputable def IsCoveringMap.fundamentalGroupEquivFiber [SimplyConnectedSpace E]
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
lemma IsCoveringMap.fundamentalGroupEquivFiber_apply_coe [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    (IsCoveringMap.fundamentalGroupEquivFiber hp e γ : E) = (hp.monodromy γ e : E) :=
  rfl

/-- The general fibre equivalence sends a loop class to the monodromy translate of the chosen
lift, as an equality in the fibre subtype. -/
@[simp]
lemma IsCoveringMap.fundamentalGroupEquivFiber_apply [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e : p ⁻¹' {x}) (γ : FundamentalGroup X x) :
    IsCoveringMap.fundamentalGroupEquivFiber hp e γ = hp.monodromy γ e :=
  rfl

/-- The inverse of the general fibre equivalence is characterized by the loop class whose
monodromy sends the chosen lift to the requested fibre point. -/
@[simp]
lemma IsCoveringMap.fundamentalGroupEquivFiber_apply_symm_apply [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e e' : p ⁻¹' {x}) :
    hp.monodromy ((IsCoveringMap.fundamentalGroupEquivFiber hp e).symm e') e = e' := by
  have h := (IsCoveringMap.fundamentalGroupEquivFiber hp e).apply_symm_apply e'
  rw [IsCoveringMap.fundamentalGroupEquivFiber_apply] at h
  exact h

/-- On underlying points, the inverse of the general fibre equivalence is characterized by
the loop class whose monodromy sends the chosen lift to the requested fibre point. -/
@[simp]
lemma IsCoveringMap.fundamentalGroupEquivFiber_apply_symm_apply_coe [SimplyConnectedSpace E]
    (hp : IsCoveringMap p) (e e' : p ⁻¹' {x}) :
    (hp.monodromy ((IsCoveringMap.fundamentalGroupEquivFiber hp e).symm e') e : E) = e' := by
  exact congrArg Subtype.val (IsCoveringMap.fundamentalGroupEquivFiber_apply_symm_apply hp e e')

end TauCeti
