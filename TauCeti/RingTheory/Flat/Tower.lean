/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-!
# Detecting flatness and exactness in a tower

Let `S` be an `R`-algebra and `M` a faithfully flat `S`-module. Then `S` is flat over
`R` if and only if `M` is flat over `R`. In particular, flatness of a composite
`R → S → T` descends to `R → S` when `S → T` is faithfully flat.

In the same situation, a sequence of `R`-modules becomes exact after tensoring with `M` over `R`
if and only if it becomes exact after tensoring with `S`
(`Module.FaithfullyFlat.lTensor_exact_iff_lTensor_exact`). For instance, exactness after
completing a Dedekind domain at a prime is exactness after localizing there.

This is useful when the larger ring is a completion whose flatness over the original
base can be proved using an explicit presentation. The descent requires neither
Noetherianity nor finiteness.

The proofs use Mathlib's reflection of injectivity and exactness under faithfully flat
tensoring and its `TensorProduct.AlgebraTensorModule.cancelBaseChange` equivalence.

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
  have key := LinearMap.congr_fun
    (AlgebraTensorModule.lTensor_comp_cancelBaseChange R S S (M := M) N.subtype)
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    AlgebraTensorModule.coe_lTensor] at key
  rw [← AlgebraTensorModule.coe_lTensor (A := S),
    ← FaithfullyFlat.lTensor_injective_iff_injective S M]
  intro x y hxy
  apply (AlgebraTensorModule.cancelBaseChange R S S M N).injective
  apply lTensor_preserves_injective_linearMap N.subtype Subtype.val_injective
  rw [key, key, hxy]

/-- Flatness over `R` can be tested on any faithfully flat `S`-module. -/
theorem iff_of_faithfullyFlat [FaithfullyFlat S M] : Flat R S ↔ Flat R M :=
  ⟨fun _ ↦ .trans R S M, fun _ ↦ .of_faithfullyFlat_of_flat R S M⟩

end Module.Flat

namespace Module.FaithfullyFlat

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- Let `M` be a faithfully flat `S`-module over an `R`-algebra `S`. A sequence of `R`-modules is
exact after tensoring with `M` over `R` if and only if it is exact after tensoring with `S`. -/
theorem lTensor_exact_iff_lTensor_exact [FaithfullyFlat S M]
    {N₁ N₂ N₃ : Type*} [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup N₃] [Module R N₃] (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃) :
    Function.Exact (f.lTensor M) (g.lTensor M) ↔ Function.Exact (f.lTensor S) (g.lTensor S) := by
  rw [← AlgebraTensorModule.coe_lTensor (A := S) (M := S) f,
    ← AlgebraTensorModule.coe_lTensor (A := S) (M := S) g, ← lTensor_exact_iff_exact S M]
  -- `M ⊗[S] (S ⊗[R] -)` is identified with `M ⊗[R] -` by `cancelBaseChange`, naturally.
  refine Function.Exact.iff_of_ladder_linearEquiv
    (f₁₂ := ((AlgebraTensorModule.lTensor S S f).lTensor M).restrictScalars R)
    (f₂₃ := ((AlgebraTensorModule.lTensor S S g).lTensor M).restrictScalars R)
    (e₁ := (AlgebraTensorModule.cancelBaseChange R S S M N₁).restrictScalars R)
    (e₂ := (AlgebraTensorModule.cancelBaseChange R S S M N₂).restrictScalars R)
    (e₃ := (AlgebraTensorModule.cancelBaseChange R S S M N₃).restrictScalars R) ?_ ?_
  · exact congr(($(AlgebraTensorModule.lTensor_comp_cancelBaseChange R S S (M := M)
      f)).restrictScalars R)
  · exact congr(($(AlgebraTensorModule.lTensor_comp_cancelBaseChange R S S (M := M)
      g)).restrictScalars R)

end Module.FaithfullyFlat
