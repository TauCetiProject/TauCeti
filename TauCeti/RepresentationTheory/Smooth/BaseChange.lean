/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Basic
public import TauCeti.RepresentationTheory.BaseChange

/-!
# Change of coefficients for smooth representations

Let `A → B` be a homomorphism of commutative rings and `ρ` a representation of a topological group
`G` on an `A`-module `V`. The base change `B ⊗_A V` (`Representation.baseChange`) of a smooth
representation is smooth: the stabilizer of `b ⊗ v` contains the open stabilizer of `v`.

For a subgroup `U`, typically compact open, the inclusion `V^U → V` induces the natural `B`-linear
comparison map `B ⊗_A V^U → (B ⊗_A V)^U`. It is injective when `B` is flat over `A`, and bijective
when moreover the group is finite (main's `Representation.invariantsBaseChangeEquiv`). It is not
surjective in general: for `U = ℤˣ` acting by sign on `ℤ` and `B = ℤ/2`, the source is `0` while
the target is `ℤ/2`.

## Main definitions

* `Representation.invariantsBaseChangeMap ρ`: the comparison map `B ⊗_A V^G → (B ⊗_A V)^G`.

## Main results

* `Representation.isSmooth_baseChange`: base change preserves smoothness.
* `Representation.injective_invariantsBaseChangeMap`: the comparison map is injective for flat
  `B`.
* `Representation.bijective_invariantsBaseChangeMap`: the comparison map is bijective for flat `B`
  and a finite group.

## References

* J. Bernstein, *Le "centre" de Bernstein*, in *Représentations des groupes réductifs sur un
  corps local*, Hermann, 1984, §2.0, Generalization, p. 9.
-/

public section

open TensorProduct

namespace Representation

/-! ### Smoothness of the base change -/

section Smooth

variable {A B G V : Type*} [CommSemiring A] [Semiring B] [Algebra A B] [Group G]
  [AddCommMonoid V] [Module A V] {ρ : Representation A G V}

/-- The stabilizer of `b ⊗ v` in the base change contains the stabilizer of `v`. -/
theorem stabilizer_le_stabilizer_baseChange_tmul (b : B) (v : V) :
    ρ.stabilizer v ≤ (baseChange B ρ).stabilizer (b ⊗ₜ[A] v) := fun g hg ↦ by
  rw [mem_stabilizer, baseChange_apply, LinearMap.baseChange_tmul, mem_stabilizer.1 hg]

variable [TopologicalSpace G] [SeparatelyContinuousMul G]

/-- **Base change preserves smoothness.** -/
instance isSmooth_baseChange [IsSmooth ρ] : IsSmooth (baseChange B ρ) := by
  rw [isSmooth_iff_forall_mem_smoothVectors]
  intro x
  induction x with
  | add x y hx hy => exact (baseChange B ρ).smoothVectors.toSubmodule.add_mem hx hy
  | tmul b v =>
    exact mem_smoothVectors_iff.2 (Subgroup.isOpen_mono
      (stabilizer_le_stabilizer_baseChange_tmul b v) (IsSmooth.isOpen_stabilizer v))

end Smooth

/-! ### Invariants -/

section Invariants

variable {A B G V : Type*} [CommRing A] [CommRing B] [Algebra A B] [Group G]
  [AddCommGroup V] [Module A V] (ρ : Representation A G V)

/-- The natural comparison map `B ⊗_A V^G → (B ⊗_A V)^G`, the base change of the inclusion of the
invariants. Applied to the restriction of `ρ` to a subgroup `U`, it is `B ⊗_A V^U → (B ⊗_A V)^U`
(`Representation.baseChange_comp`). -/
@[expose] noncomputable def invariantsBaseChangeMap :
    B ⊗[A] ρ.invariants →ₗ[B] (baseChange B ρ).invariants :=
  (AlgebraTensorModule.lTensor B B ρ.invariants.subtype).codRestrict _ fun x ↦ by
    induction x with
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | tmul b v =>
      exact (mem_invariants _ _).2 fun g ↦ by
        simp [mem_invariants _ _ |>.1 v.property g]

@[simp]
theorem coe_invariantsBaseChangeMap_tmul (b : B) (v : ρ.invariants) :
    (ρ.invariantsBaseChangeMap (b ⊗ₜ[A] v) : B ⊗[A] V) = b ⊗ₜ[A] (v : V) :=
  rfl

/-- **The comparison map is injective for flat coefficients.** -/
theorem injective_invariantsBaseChangeMap [Module.Flat A B] :
    Function.Injective (ρ.invariantsBaseChangeMap (B := B)) := by
  intro x y h
  have h' := congrArg Subtype.val h
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := B) ρ.invariants.subtype
    ρ.invariants.injective_subtype h'

/-- **The comparison map is bijective for flat coefficients and a finite group**: it is main's
`Representation.invariantsBaseChangeEquiv`. -/
theorem bijective_invariantsBaseChangeMap [Module.Flat A B] [Finite G] :
    Function.Bijective (ρ.invariantsBaseChangeMap (B := B)) := by
  have h : ρ.invariantsBaseChangeMap (B := B) =
      (ρ.invariantsBaseChangeEquiv (A := B)).toLinearMap := by
    refine LinearMap.ext fun x ↦ Subtype.ext ?_
    induction x with
    | add x y hx hy => simp only [map_add, Submodule.coe_add, hx, hy]
    | tmul b v => simp
  rw [h]
  exact (ρ.invariantsBaseChangeEquiv (A := B)).bijective

end Invariants

end Representation
