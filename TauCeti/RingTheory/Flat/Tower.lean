/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Detecting flatness in a tower

Let `S` be an `R`-algebra and `M` a faithfully flat `S`-module. Then `S` is flat over
`R` if and only if `M` is flat over `R`. In particular, flatness of a composite
`R → S → T` descends to `R → S` when `S → T` is faithfully flat.

This is useful when the larger ring is a completion whose flatness over the original
base can be proved using an explicit presentation. The descent requires neither
Noetherianity nor finiteness.

The proof uses Mathlib's reflection of injectivity under faithfully flat tensoring
and its `TensorProduct.AlgebraTensorModule.cancelBaseChange` equivalence.

## References

* Stacks Project, Lemma 10.39.10, Tag 039V.
-/

public section

open TensorProduct

namespace Module.Flat

variable (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- If a faithfully flat `S`-module is flat over `R`, then `S` is flat over `R`.
For an algebra `M`, this descends flatness from the composite `R → S → M`. -/
theorem of_faithfullyFlat_of_flat [FaithfullyFlat S M] [Flat R M] : Flat R S := by
  rw [iff_lTensor_injectiveₛ]
  intro P _ _ N
  rw [← AlgebraTensorModule.coe_lTensor (A := S),
    ← FaithfullyFlat.lTensor_injective_iff_injective S M]
  have h₀ : Function.Injective (AlgebraTensorModule.lTensor S M N.subtype) := by
    rw [AlgebraTensorModule.coe_lTensor]
    exact lTensor_preserves_injective_linearMap N.subtype Subtype.val_injective
  have h := h₀.comp (AlgebraTensorModule.cancelBaseChange R S S M N).injective
  rw [← LinearEquiv.coe_coe, ← LinearMap.coe_comp,
    AlgebraTensorModule.lTensor_comp_cancelBaseChange,
    LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective,
    AlgebraTensorModule.coe_lTensor] at h
  exact h

/-- Flatness over `R` can be tested on any faithfully flat `S`-module. -/
theorem iff_of_faithfullyFlat [FaithfullyFlat S M] : Flat R S ↔ Flat R M :=
  ⟨fun _ ↦ .trans R S M, fun _ ↦ .of_faithfullyFlat_of_flat R S M⟩

end Module.Flat
