/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import TauCeti.Algebra.Module.Annihilator

/-!
# The Serre class of modules annihilated by an ideal power

For any ideal `I`, modules killed by some positive power of `I` form a Serre class.
The exponent may depend on the module, but is uniform over its elements.
No noetherianity or finite generation is required for the Serre property.

For finite modules and finitely generated `I`, this is precisely support in `V(I)`
(see `Module.support_subset_zeroLocus_iff_exists_pow_le_annihilator`). This supplies
the affine algebra behind categories of coherent modules with formal support.

## References

* The Stacks Project, Tag 00L6.
-/

public section

open CategoryTheory

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- Modules annihilated by some positive power of an ideal form a Serre class. -/
theorem isSerreClass_exists_pow_le_annihilator (I : Ideal R) :
    ObjectProperty.IsSerreClass
      (fun M : ModuleCat.{v} R ↦ ∃ n : ℕ, 0 < n ∧ I ^ n ≤ Module.annihilator R M) where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    1, Nat.one_pos, fun r _ ↦ Module.mem_annihilator.mpr fun _ ↦ Subsingleton.elim _ _⟩
  prop_of_mono {M N} f hf hN := by
    obtain ⟨n, hn, h⟩ := hN
    exact ⟨n, hn, h.trans
      (f.hom.annihilator_le_of_injective ((ModuleCat.mono_iff_injective f).mp hf))⟩
  prop_of_epi {M N} f hf hM := by
    obtain ⟨n, hn, h⟩ := hM
    exact ⟨n, hn, h.trans
      (f.hom.annihilator_le_of_surjective ((ModuleCat.epi_iff_surjective f).mp hf))⟩
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    obtain ⟨a, ha, hM⟩ := h₁
    obtain ⟨b, -, hP⟩ := h₃
    refine ⟨a + b, Nat.add_pos_left ha b, ?_⟩
    rw [pow_add]
    exact S.f.hom.mul_le_annihilator_of_exact S.g.hom
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact) hM hP

end Ideal
