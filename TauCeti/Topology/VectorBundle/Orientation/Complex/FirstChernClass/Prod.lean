/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Determinant.Prod
public import TauCeti.Topology.VectorBundle.Orientation.Complex.FirstChernClass

/-!
# The first Chern class of a sum with a trivial bundle

Adding a trivial summand does not change the first Chern class of a complex vector bundle:
`c₁((B × V) ⊕ E) = c₁(E)` (`TauCeti.firstChernClass_trivial_prod`). The determinant lines of the
two bundles are isomorphic, `a ↦ ω ∧ a` for the constant section `ω` of `det (B × V) = B × ℂ`
(`TauCeti.DetBundle.trivialProdHomeomorph`), and `c₁` is the first Chern class of the determinant
line.

So when `E' ≅ (B × V) ⊕ E`, then `c₁(E) = c₁(E')`
(`TauCeti.firstChernClass_eq_of_fiberwise_trivialProd`); for a line bundle `E = L` this computes
`c₁(E')` from the line summand of a splitting `E' ≅ (B × ℂⁿ) ⊕ L`. This is the case of the Whitney
sum formula for `c₁` with one trivial summand.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §14 (the Whitney product formula for Chern classes).
-/

public section

noncomputable section

open Bundle Module

namespace TauCeti

variable {B : Type} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F]
  {E : B → Type} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℂ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℂ F E]
  (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]

/-- **A trivial summand does not change the first Chern class**: `c₁((B × V) ⊕ E) = c₁(E)`, by the
isomorphism of determinant lines `TauCeti.DetBundle.trivialProdHomeomorph`. -/
@[simp]
theorem firstChernClass_trivial_prod :
    firstChernClass (V × F) (Trivial B V ×ᵇ E) = firstChernClass F E := by
  rw [firstChernClass_def, firstChernClass_def, lineFirstChernClass_def, lineFirstChernClass_def]
  exact complexEulerClass_eq_of_fiberwise (finrank_self ℂ) (finrank_self ℂ)
    (φ := fun b ↦ (DetBundle.trivialProdEquiv ℂ B F E V b).symm)
    ((DetBundle.trivialProdHomeomorph ℂ B F E V).symm.continuous.congr fun _ ↦
      DetBundle.trivialProdHomeomorph_symm_apply _)

variable {V}

/-- **The first Chern class of a summand complementary to a trivial bundle.** If a complex vector
bundle `E'` is isomorphic to `(B × V) ⊕ E`, by a fibrewise complex-linear isomorphism continuous
on total spaces, then `c₁(E) = c₁(E')`. -/
theorem firstChernClass_eq_of_fiberwise_trivialProd
    {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℂ F'] [FiniteDimensional ℂ F']
    {E' : B → Type} [TopologicalSpace (TotalSpace F' E')] [∀ b, AddCommGroup (E' b)]
    [∀ b, Module ℂ (E' b)] [∀ b, TopologicalSpace (E' b)] [FiberBundle F' E']
    [VectorBundle ℂ F' E'] {φ : ∀ b, (Trivial B V ×ᵇ E) b ≃L[ℂ] E' b}
    (hφ : Continuous fun v : TotalSpace (V × F) (Trivial B V ×ᵇ E) ↦
      TotalSpace.mk' F' v.proj (φ v.proj v.snd)) :
    firstChernClass F E = firstChernClass F' E' := by
  rw [← firstChernClass_trivial_prod V, firstChernClass_eq_of_fiberwise hφ]

end TauCeti
