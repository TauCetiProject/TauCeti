/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.LinearAlgebra.Dimension.Free
public import TauCeti.Algebra.Category.FiniteHopfModuleCat.Basic

/-!
# Finite-dimensional algebra modules form an essentially small category

For a field `k : Type u` and a `k`-algebra `H : Type v`, the category
`FiniteHopfModuleCat k H` is essentially small in the universe `max u v`. Its morphism types
already lie in `Type u`, so the point is that its isomorphism classes form a small set.

A finite-dimensional module `M` is determined up to isomorphism by its dimension `n` together
with the operators by which `H` acts on `kⁿ`, after transport along any linear isomorphism
`M ≃ kⁿ`. Assigning to each isomorphism class the set of all pairs `(n, ρ)` obtained in this way
is therefore injective, with values in the sets of a type in `Type (max u v)`.

Essential smallness is what split Grothendieck groups `TauCeti.SplitK0` of the category, such as
representation rings of Hopf algebras, require.
-/

public noncomputable section

open CategoryTheory

namespace TauCeti.FiniteHopfModuleCat

universe u v

variable {k : Type u} [Field k] {H : Type v} [Ring H] [Algebra k H]

/-- The action matrices of `M`: all pairs `(n, ρ)` such that some linear isomorphism `M ≃ kⁿ`
transports the action of each `h : H` to `ρ h`. -/
private def actionData (M : FiniteHopfModuleCat k H) :
    Set (Σ n : ℕ, H → Module.End k (Fin n → k)) :=
  {p | ∃ e : M ≃ₗ[k] (Fin p.1 → k), ∀ (h : H) (x : M), e (h • x) = p.2 h (e x)}

/-- Modules with a common transported action are isomorphic. -/
private theorem nonempty_iso_of_actionData_eq {M N : FiniteHopfModuleCat k H}
    (hMN : actionData M = actionData N) : Nonempty (M ≅ N) := by
  let e₀ := (Module.finBasis k M).equivFun
  let p : Σ n : ℕ, H → Module.End k (Fin n → k) :=
    ⟨_, fun h => e₀.conj (Algebra.lsmul k k M h)⟩
  have hp : p ∈ actionData M := ⟨e₀, fun h x => by simp [p, LinearEquiv.conj_apply]⟩
  obtain ⟨e₁, he₁⟩ := hMN ▸ hp
  -- `e₁⁻¹ ∘ e₀` intertwines the two actions, since both transport them to `p`.
  refine ⟨LinearEquiv.toFiniteHopfModuleCatIso
    { e₀.trans e₁.symm with
      map_smul' := fun h x => e₁.injective ?_ }⟩
  simp [p, he₁, LinearEquiv.conj_apply]

/-- **Finite-dimensional modules over a `k`-algebra form an essentially small category**, in
the universe `max u v` of the field `k : Type u` and the algebra `H : Type v`. -/
instance essentiallySmall : EssentiallySmall.{max u v} (FiniteHopfModuleCat k H) := by
  refine (essentiallySmall_iff _).2 ⟨?_, locallySmall_max⟩
  refine small_of_injective (f := fun X : Skeleton (FiniteHopfModuleCat k H) =>
    actionData ((fromSkeleton _).obj X)) fun X Y hXY => ?_
  obtain ⟨e⟩ := nonempty_iso_of_actionData_eq hXY
  rw [← toSkeleton_fromSkeleton_obj X, ← toSkeleton_fromSkeleton_obj Y]
  exact congr_toSkeleton_of_iso e

end TauCeti.FiniteHopfModuleCat
