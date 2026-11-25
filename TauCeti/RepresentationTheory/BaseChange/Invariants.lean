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
the coefficients `vᵢ` (`Module.Basis.equivFinsuppOfBasisLeft_lTensor_apply`), so `w` is invariant
exactly when every `vᵢ` is. Injectivity holds because free modules are flat.

## Main results

* `Representation.invariantsBaseChangeMap_surjective_of_free`,
  `Representation.invariantsBaseChangeMap_bijective_of_free`: the comparison map is surjective and
  bijective for free coefficients.
* `Representation.invariantsBaseChangeEquivOfFree`: `A ⊗_R V^G ≃ (A ⊗_R V)^G`.
-/

public section

open TensorProduct

namespace Representation

variable {G R A V : Type*} [Group G] [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A]
  [AddCommGroup V] [Module R V]

/-- **Free scalar extension: every invariant comes from an invariant.** For `A` free over `R`, the
comparison map `A ⊗_R V^G → (A ⊗_R V)^G` is surjective for every group `G`. -/
theorem invariantsBaseChangeMap_surjective_of_free (ρ : Representation R G V) :
    Function.Surjective (ρ.invariantsBaseChangeMap (A := A)) := by
  classical
  rintro ⟨w, hw⟩
  let b := Module.Free.chooseBasis R A
  let e := TensorProduct.equivFinsuppOfBasisLeft b (N := V)
  have hinv (i : Module.Free.ChooseBasisIndex R A) : e w i ∈ ρ.invariants :=
    (mem_invariants _ _).2 fun g => by
      have h := (mem_invariants _ _).1 hw g
      rw [baseChange_apply, LinearMap.baseChange_eq_lTensor] at h
      rw [← Module.Basis.equivFinsuppOfBasisLeft_lTensor_apply]
      exact congrArg (fun x => e x i) h
  refine ⟨∑ i ∈ (e w).support, b i ⊗ₜ[R] (⟨e w i, hinv i⟩ : ρ.invariants), Subtype.ext ?_⟩
  change _ = w
  rw [coe_invariantsBaseChangeMap, map_sum]
  conv_rhs => rw [← e.symm_apply_apply w]
  rw [TensorProduct.equivFinsuppOfBasisLeft_symm_apply, Finsupp.sum]
  rfl

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

@[simp]
theorem coe_invariantsBaseChangeEquivOfFree_tmul (ρ : Representation R G V) (a : A)
    (v : ρ.invariants) :
    (ρ.invariantsBaseChangeEquivOfFree (a ⊗ₜ[R] v) : A ⊗[R] V) = a ⊗ₜ[R] (v : V) :=
  ρ.coe_invariantsBaseChangeMap_tmul a v

end Representation
