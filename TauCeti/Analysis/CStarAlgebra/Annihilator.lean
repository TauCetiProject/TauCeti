/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Ideal
public import TauCeti.RingTheory.TwoSidedIdeal.Annihilator

/-!
# Annihilators of closed ideals in C⋆-algebras

Let `I` be a closed two-sided ideal of a possibly nonunital C⋆-algebra `A`. Then `I` is
self-adjoint, so the results of `TauCeti.RingTheory.TwoSidedIdeal.Annihilator` apply to its
annihilator `I.annihilator = {a | ∀ x ∈ I, a * x = 0}`: it is the right annihilator as well, it is
a closed self-adjoint two-sided ideal (so a nonunital C⋆-algebra in its own right), it is the
largest two-sided ideal disjoint from `I`, and it vanishes exactly when `I` is essential.

This file adds the two descriptions of `I.annihilator` that need the C⋆-structure.

* **As a module annihilator.** A closed ideal is a complex subspace, so the unitization
  `Unitization ℂ A` acts on `I` on the left by `(z, a) • x = z • x + a * x`. This action is
  `TwoSidedIdeal.unitizationModule I`, a definition rather than an instance since it depends on
  `I`. The annihilator of `I` is the preimage in `A` of the module annihilator of `I` under this
  action. This extends to nonunital `A` the identification
  `TwoSidedIdeal.annihilator_eq_toTwoSided_annihilator` valid for unital rings.
* **As a kernel.** The annihilator of `I` is the kernel of the canonical homomorphism
  `A →⋆ₙₐ[ℂ] 𝓜(ℂ, I)` into the multiplier algebra of `I`. So this homomorphism is injective exactly
  when `I` is an essential ideal.

## References

* B. Blackadar, *Operator Algebras*, II.5.4 and II.7.3.
* G. J. Murphy, *C⋆-Algebras and Operator Theory*, Section 3.1.
-/

public section

open scoped CStarAlgebra

namespace TwoSidedIdeal

variable {A : Type*} [NonUnitalCStarAlgebra A] (I : TwoSidedIdeal A) [IsClosed (I : Set A)]

/-- A closed two-sided ideal of a C⋆-algebra is essential exactly when its annihilator vanishes. -/
theorem annihilator_eq_bot_iff_isEssential_of_isClosed : I.annihilator = ⊥ ↔ I.IsEssential :=
  annihilator_eq_bot_iff_isEssential fun _ ↦ I.star_mem_of_isClosed

/-- Left multiplication by elements of `A` on a closed two-sided ideal `I`, as a nonunital algebra
homomorphism into the complex-linear endomorphisms of `I`. -/
def mulLeftEnd : A →ₙₐ[ℂ] Module.End ℂ I where
  toFun a :=
    { toFun x := ⟨a * x, I.mul_mem_left a x x.property⟩
      map_add' x y := Subtype.ext (mul_add a (x : A) y)
      map_smul' c x := Subtype.ext (mul_smul_comm c a (x : A)) }
  map_smul' c a := LinearMap.ext fun x ↦ Subtype.ext (smul_mul_assoc c a (x : A))
  map_zero' := LinearMap.ext fun x ↦ Subtype.ext (zero_mul (x : A))
  map_add' a b := LinearMap.ext fun x ↦ Subtype.ext (add_mul a b (x : A))
  map_mul' a b := LinearMap.ext fun x ↦ Subtype.ext (mul_assoc a b (x : A))

@[simp]
theorem coe_mulLeftEnd_apply (a : A) (x : I) : ((I.mulLeftEnd a x : I) : A) = a * x :=
  (rfl)

/-- The left action `(z, a) • x = z • x + a * x` of the unitization `Unitization ℂ A` on a closed
two-sided ideal `I`. -/
@[instance_reducible]
noncomputable def unitizationModule : Module (Unitization ℂ A) I :=
  Module.compHom I (Unitization.lift I.mulLeftEnd : Unitization ℂ A →+* Module.End ℂ I)

theorem unitizationModule_smul_def (u : Unitization ℂ A) (x : I) :
    letI := I.unitizationModule
    u • x = Unitization.lift I.mulLeftEnd u x :=
  (rfl)

@[simp]
theorem coe_unitizationModule_smul (u : Unitization ℂ A) (x : I) :
    letI := I.unitizationModule
    ((u • x : I) : A) = u.fst • (x : A) + u.snd * x := by
  let _ : Module (Unitization ℂ A) I := I.unitizationModule
  simp [unitizationModule_smul_def, Module.algebraMap_end_apply]

/-- The annihilator of a closed two-sided ideal `I` is the preimage in `A` of the module
annihilator of `I` under the left action of the unitization. -/
theorem annihilator_eq_comap_toTwoSided_annihilator :
    letI := I.unitizationModule
    I.annihilator = (Module.annihilator (Unitization ℂ A) I).toTwoSided.comap
      (Unitization.inrNonUnitalAlgHom ℂ A) := by
  let _ : Module (Unitization ℂ A) I := I.unitizationModule
  ext a
  simp [mem_comap, Module.mem_annihilator, ← Subtype.coe_inj]

/-- The annihilator of a closed two-sided ideal `I` is the kernel of the canonical homomorphism
from `A` into the multiplier algebra of `I`. -/
theorem ker_multiplierHom :
    ker (I.toNonUnitalStarSubalgebra.multiplierHom I.mul_mem_toNonUnitalStarSubalgebra) =
      I.annihilator :=
  ext fun _ ↦ by
    simp only [mem_ker, NonUnitalStarSubalgebra.multiplierHom_eq_zero_iff,
      mem_toNonUnitalStarSubalgebra, mem_annihilator]

/-- The canonical homomorphism from `A` into the multiplier algebra of a closed two-sided ideal `I`
is injective exactly when `I` is essential. -/
theorem multiplierHom_injective_iff_isEssential :
    Function.Injective (I.toNonUnitalStarSubalgebra.multiplierHom
      I.mul_mem_toNonUnitalStarSubalgebra) ↔ I.IsEssential := by
  rw [← ker_eq_bot, ker_multiplierHom, annihilator_eq_bot_iff_isEssential_of_isClosed]

end TwoSidedIdeal
