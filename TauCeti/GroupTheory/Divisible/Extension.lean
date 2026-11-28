/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Divisible
import Mathlib.Algebra.Category.Grp.Injective
import TauCeti.GroupTheory.Divisible.Basic

/-!
# Extending homomorphisms into divisible groups

A homomorphism into a divisible abelian group extends along a map into an abelian group
if and only if it kills the kernel of that map. This is the multiplicative form of Baer's
criterion (`Module.Baer.of_divisible`), applied after descent to the image.
-/

public section

namespace MonoidHom

/-- A homomorphism `χ` into a divisible commutative group factors through a map `f` into an
abelian group if and only if it is trivial on the kernel of `f`. The domain need not be abelian. -/
theorem exists_comp_eq_iff_ker_le_ker_of_rootableBy {H G A : Type*} [Group H] [CommGroup G]
    [CommGroup A] [RootableBy A ℕ] (f : H →* G) (χ : H →* A) :
    (∃ ψ : G →* A, ψ.comp f = χ) ↔ f.ker ≤ χ.ker := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨ψ, rfl⟩ x hx
    simp [MonoidHom.mem_ker.mp hx]
  have hker : f.rangeRestrict.ker ≤ χ.ker := by simpa using h
  let c := (f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective) ⟨χ, hker⟩
  let : DivisibleBy (Additive A) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨F, hF⟩ := (Module.Baer.of_divisible (Additive A)).extension_property_addMonoidHom
    f.range.subtype.toAdditive Subtype.coe_injective c.toAdditive
  refine ⟨MonoidHom.toAdditive.symm F, MonoidHom.ext fun x ↦ ?_⟩
  have hx := congrArg Additive.toMul (DFunLike.congr_fun hF (Additive.ofMul (f.rangeRestrict x)))
  simpa only [AddMonoidHom.comp_apply, MonoidHom.coe_toAdditive, Function.comp_apply,
    MonoidHom.comp_apply, MonoidHom.toAdditive_symm_apply_apply, toMul_ofMul,
    Subgroup.coe_subtype, MonoidHom.coe_rangeRestrict, c,
    MonoidHom.liftOfRightInverse_comp_apply] using hx

end MonoidHom
