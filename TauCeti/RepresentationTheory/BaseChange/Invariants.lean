/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.BaseChange

/-!
# Invariants under free scalar extension

Let `ρ` be a representation of a group `G` over a commutative ring `R`, and let `A` be a commutative
`R`-algebra that is free as an `R`-module (for instance any field extension of a field `R`). Then
the comparison map `A ⊗_R V^G → (A ⊗_R V)^G` (`Representation.invariantsBaseChangeMap`) is
bijective, with no finiteness assumption on `G` or `V`
(`Representation.invariantsBaseChangeEquivOfFree`). Unlike
`Representation.invariantsBaseChangeMap_bijective`, `G` need not be finite.

Proof: a `R`-basis `(bᵢ)` of `A` writes every `w ∈ A ⊗ V` uniquely as `∑ bᵢ ⊗ vᵢ`, and `G` acts on
the coefficients `vᵢ` (`Representation.equivFinsuppOfBasisLeft_apply_fixed_of_baseChange`), so `w`
is invariant exactly when every `vᵢ` is. Injectivity holds because free modules are flat.

## Main results

* `Representation.invariantsBaseChangeMap_surjective_of_free`,
  `Representation.invariantsBaseChangeMap_bijective_of_free`: the comparison map is surjective and
  bijective for free coefficients.
* `Representation.invariantsBaseChangeEquivOfFree`: `A ⊗_R V^G ≃ (A ⊗_R V)^G`.
-/

public section

open TensorProduct

namespace Representation

section CommSemiring

variable {G R A V : Type*} [Monoid G] [CommSemiring R] [Semiring A] [Algebra R A]
  [Module.Free R A] [AddCommMonoid V] [Module R V]

/-- Under scalar extension to an algebra free as a module, a fixed vector comes from the tensor
of any submodule containing every fixed vector of the original representation. -/
theorem mem_range_lTensor_subtype_of_fixed_baseChange_of_free (ρ : Representation R G V)
    (P : Submodule R V) (hP : ∀ v, (∀ g, ρ g v = v) → v ∈ P)
    {w : A ⊗[R] V} (hw : ∀ g, baseChange A ρ g w = w) :
    w ∈ LinearMap.range (P.subtype.lTensor A) := by
  classical
  let b := Module.Free.chooseBasis R A
  exact (b.mem_range_lTensor_subtype_iff P w).2 fun i ↦
    hP _ (equivFinsuppOfBasisLeft_apply_fixed_of_baseChange b ρ hw i)

end CommSemiring

variable {G R A V : Type*} [Group G] [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A]
  [AddCommGroup V] [Module R V]

/-- **Free scalar extension: every invariant comes from an invariant.** For `A` free over `R`, the
comparison map `A ⊗_R V^G → (A ⊗_R V)^G` is surjective for every group `G`. -/
theorem invariantsBaseChangeMap_surjective_of_free (ρ : Representation R G V) :
    Function.Surjective (ρ.invariantsBaseChangeMap (A := A)) := by
  rintro ⟨w, hw⟩
  obtain ⟨y, hy⟩ := ρ.mem_range_lTensor_subtype_of_fixed_baseChange_of_free ρ.invariants
    (fun v ↦ (mem_invariants ρ v).2) ((mem_invariants _ w).1 hw)
  exact ⟨y, Subtype.ext ((coe_invariantsBaseChangeMap ρ y).trans hy)⟩

/-- **Free scalar extension commutes with invariants**: for `A` free over `R`, the comparison map
`A ⊗_R V^G → (A ⊗_R V)^G` is bijective for every group `G`. -/
theorem invariantsBaseChangeMap_bijective_of_free (ρ : Representation R G V) :
    Function.Bijective (ρ.invariantsBaseChangeMap (A := A)) :=
  ⟨ρ.invariantsBaseChangeMap_injective, ρ.invariantsBaseChangeMap_surjective_of_free⟩

/-- **Invariants of a free scalar extension**: `A ⊗_R V^G ≃ (A ⊗_R V)^G` for `A` free over `R` and
any group `G`, by the comparison map `Representation.invariantsBaseChangeMap`. -/
noncomputable def invariantsBaseChangeEquivOfFree (ρ : Representation R G V) :
    A ⊗[R] ρ.invariants ≃ₗ[A] (baseChange A ρ).invariants :=
  LinearEquiv.ofBijective _ ρ.invariantsBaseChangeMap_bijective_of_free

/-- The free base-change equivalence of invariants is the comparison map. -/
@[simp]
theorem toLinearMap_invariantsBaseChangeEquivOfFree (ρ : Representation R G V) :
    (ρ.invariantsBaseChangeEquivOfFree (A := A)).toLinearMap = ρ.invariantsBaseChangeMap :=
  LinearMap.ext fun _ ↦ LinearEquiv.ofBijective_apply _ _

/-- The free base-change equivalence of invariants is the scalar extension of the inclusion of the
invariant submodule. -/
@[simp]
theorem coe_invariantsBaseChangeEquivOfFree (ρ : Representation R G V) (x : A ⊗[R] ρ.invariants) :
    (ρ.invariantsBaseChangeEquivOfFree x : A ⊗[R] V) = ρ.invariants.subtype.lTensor A x := by
  rw [← LinearEquiv.coe_toLinearMap, toLinearMap_invariantsBaseChangeEquivOfFree,
    coe_invariantsBaseChangeMap]

end Representation
