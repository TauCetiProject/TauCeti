/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Deformation.Restriction

/-!
# Checks for restriction of lifts

Restriction along the identity is the identity. The framed restricted lift is invariant under
simultaneous strict conjugation of the lift and its frame, while the unframed restriction changes
by conjugation. Restriction is not injective: along the inclusion of the trivial group every lift
restricts to the same lift, while the trivial representation of `ℤ` has a distinct lift to `A`
sending `1` to `u` for every element `u ≠ 1` of the strict kernel of `A`.
-/

public section

open CategoryTheory Matrix

namespace TauCeti.Examples

open Deformation ArtinLocalAlg

variable {Λ : Type*} [CommRing Λ] {k : Type*} [Field k] [Algebra Λ k]
  {n : Type*} [Fintype n] [DecidableEq n] {G : Type*} [Monoid G] [TopologicalSpace G]
  {ρbar : G →* GL n k} {A : ArtinLocalAlg Λ k}

/-- Restriction along the identity is the identity. -/
example (ρ : Lift ρbar A) : ⇑(ρ.restrict (ContinuousMonoidHom.id G)) = ⇑ρ := by
  ext1 g
  simp

/-- The framed restricted lift does not see simultaneous strict conjugation of the lift and its
frame. -/
example {H : Type*} [Monoid H] [TopologicalSpace H] (ι : H →ₜ* G) (β α : A.strictKernel n)
    (ρ : Lift ρbar A) (h : H) :
    (β • ρ).framedRestrict ι (β * α) h = ρ.framedRestrict ι α h := by
  simp

/-- The unframed restriction changes by conjugation under strict conjugation of the lift. -/
example {H : Type*} [Monoid H] [TopologicalSpace H] (ι : H →ₜ* G) (β : A.strictKernel n)
    (ρ : Lift ρbar A) (h : H) :
    (β • ρ).restrict ι h = β * ρ.restrict ι h * (β : GL n A.obj.left)⁻¹ := by
  simp

/-- A residual representation of a trivial monoid has at most one lift: restriction to the trivial
group identifies all lifts. -/
example {H : Type*} [Monoid H] [TopologicalSpace H] [Subsingleton H] {σbar : H →* GL n k}
    (ρ ρ' : Lift σbar A) : ρ = ρ' :=
  Lift.ext fun h ↦ by rw [Subsingleton.elim h 1, map_one, map_one]

/-- The lift of the trivial representation of `ℤ` sending `1` to an element `u` of the strict
kernel. -/
def zpowersLift (u : A.strictKernel n) : Lift (1 : Multiplicative ℤ →* GL n k) A where
  toMonoidHom := zpowersHom _ (u : GL n A.obj.left)
  isLocallyConstant' := IsLocallyConstant.of_discrete _
  map_augmentation_comp' := MonoidHom.ext_mint <| by
    simpa using mem_strictKernel_iff.mp u.property

/-- Restriction is not injective: if the strict kernel of `A` is nontrivial, the trivial
representation of `ℤ` has two distinct lifts to `A` whose restrictions along the inclusion of the
trivial group agree. -/
example (u : A.strictKernel n) (hu : u ≠ 1) :
    zpowersLift u ≠ zpowersLift 1 ∧
      (zpowersLift u).restrict (1 : Unit →ₜ* Multiplicative ℤ) = (zpowersLift 1).restrict 1 := by
  refine ⟨fun h ↦ hu (Subtype.ext ?_), Lift.ext fun v ↦ by rw [Subsingleton.elim v 1, map_one,
    map_one]⟩
  simpa [zpowersLift] using congrArg (fun ρ : Lift _ A ↦ ρ (.ofAdd 1)) h

end TauCeti.Examples
