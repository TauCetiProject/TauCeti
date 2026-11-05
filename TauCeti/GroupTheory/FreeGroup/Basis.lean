/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
import Mathlib.GroupTheory.FreeGroup.Reduce

/-!
# Basic facts about free bases

Three elementary consequences of the universal property of a free basis `b : FreeGroupBasis ι H`.

## Main results

* `FreeGroupBasis.injective_lift_comp`: if `FreeGroup α` surjects onto `H`, a function on the
  basis `ι` is determined by the values of its extension to `H` on the images of the elements
  of `α`.
* `FreeGroupBasis.nontrivial_of_not_commute`: a free basis of a group containing two
  noncommuting elements has at least two elements.
* `FreeGroupBasis.exists_comp_eq_of_surjective`: a homomorphism out of a group with a free basis
  lifts through every surjective homomorphism.
-/

public section

namespace FreeGroupBasis

variable {ι H : Type*} [Group H]

/-- If `f : FreeGroup α →* H` is surjective, a function on the basis `ι`, extended to a
homomorphism on `H`, is determined by its values on the images of the elements of `α`. -/
theorem injective_lift_comp {α : Type*} {f : FreeGroup α →* H} (b : FreeGroupBasis ι H)
    {M : Type*} [Group M] (hf : Function.Surjective f) :
    Function.Injective fun (v : ι → M) (a : α) => b.lift v (f (FreeGroup.of a)) := by
  intro v w hvw
  have hcomp : (b.lift v).comp f = (b.lift w).comp f := by
    ext a
    exact congr_fun hvw a
  exact b.lift.injective ((MonoidHom.cancel_right hf).mp hcomp)

/-- A free basis of a group containing two noncommuting elements has at least two elements:
a free group on at most one generator is commutative. -/
theorem nontrivial_of_not_commute (b : FreeGroupBasis ι H) {x y : H} (h : ¬Commute x y) :
    Nontrivial ι := by
  by_contra hι
  have : IsMulCommutative (FreeGroup ι) :=
    FreeGroup.isMulCommutative_iff_subsingleton.mpr (not_nontrivial_iff_subsingleton.mp hι)
  have : IsMulCommutative H := b.repr.symm.surjective.isMulCommutative
  exact h (this.is_comm.comm x y)

/-- **Free groups are projective**: a homomorphism `π` out of a group with a free basis lifts
through every surjective homomorphism `p`, by lifting the image of each basis element. -/
theorem exists_comp_eq_of_surjective (b : FreeGroupBasis ι H) {E G : Type*} [Group E] [Group G]
    {p : E →* G} (hp : Function.Surjective p) (π : H →* G) : ∃ ψ : H →* E, p.comp ψ = π :=
  ⟨b.lift fun i ↦ (hp (π (b i))).choose, b.ext_hom _ _ fun i ↦ by
    simpa using (hp (π (b i))).choose_spec⟩

end FreeGroupBasis
