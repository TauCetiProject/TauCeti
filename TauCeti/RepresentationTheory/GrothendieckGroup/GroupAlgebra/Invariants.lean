/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Finrank
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Universal
import Mathlib.RepresentationTheory.Maschke
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import TauCeti.RepresentationTheory.Invariants

/-!
# Invariant dimensions on the Grothendieck group of a group algebra

Let `G` be a finite group and `k` a field whose characteristic does not divide `#G`. Maschke's
theorem makes the invariants functor exact, so the dimension of the invariant subspace is additive
in short exact sequences of finite-dimensional representations. This file descends that dimension
to a homomorphism

`finrankInvariantsK0 k G : G₀(k[G]) →+ ℤ`.

The Grothendieck ring product is induced by the tensor product of representations. Hence, for a
fixed finite-dimensional representation `A`, multiplication by `[A]` followed by invariant
dimension gives another additive homomorphism,

`finrankTensorInvariantsK0 A : G₀(k[G]) →+ ℤ`,

whose value at `[M]` is `dimₖ (M ⊗ A)^G`. This packages the semisimple representation-theoretic
functional used in Euler characteristic calculations.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), §§1.4 and 14.1.
-/

public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped MonoidAlgebra

namespace TauCeti

universe u

variable {k G : Type u} [Field k] [Group G] [Finite G] [NeZero (Nat.card G : k)]

/-- Under Maschke's hypothesis, taking invariants preserves short exact sequences of
finite-dimensional representations. -/
theorem FDRep.shortExact_map_invariantsFunctor {S : ShortComplex (FDRep k G)}
    (hS : S.ShortExact) :
    (S.map (forget₂ (FDRep k G) (Rep k G) ⋙ Rep.invariantsFunctor k G)).ShortExact := by
  let F := forget₂ (FDRep k G) (Rep k G) ⋙ Rep.invariantsFunctor k G
  have : F.PreservesEpimorphisms := ⟨fun {X Y} f hf ↦ by
      have hsurj : Function.Surjective f.hom :=
        (Rep.epi_iff_surjective ((forget₂ (FDRep k G) (Rep k G)).map f)).1 inferInstance
      let Y' := (forget₂ (FDRep k G) (Rep k G)).obj Y
      have : Module.Projective k[G] Y'.ρ.asModule :=
        Module.projective_of_isSemisimpleRing k[G] Y'.ρ.asModule
      exact (ModuleCat.epi_iff_surjective _).2
        (Rep.invariantsFunctor_map_surjective_of_surjective_of_projective
          ((forget₂ (FDRep k G) (Rep k G)).map f) hsurj)⟩
  have : F.PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels F
  have : F.PreservesMonomorphisms := by
    dsimp [F]
    infer_instance
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  exact hS.map F

/-- Invariant dimension is additive on short exact sequences of finite-dimensional
representations when the group order is invertible in the coefficient field. -/
theorem FDRep.finrank_invariants_add_of_shortExact {S : ShortComplex (FDRep k G)}
    (hS : S.ShortExact) :
    Module.finrank k (Representation.invariants S.X₂.ρ) =
      Module.finrank k (Representation.invariants S.X₁.ρ) +
        Module.finrank k (Representation.invariants S.X₃.ρ) := by
  let F := forget₂ (FDRep k G) (Rep k G) ⋙ Rep.invariantsFunctor k G
  have hInv : (S.map F).ShortExact := FDRep.shortExact_map_invariantsFunctor hS
  have : Module.Finite k (S.map F).X₁ :=
    Module.Finite.of_injective (Submodule.subtype _) Subtype.coe_injective
  have : Module.Finite k (S.map F).X₃ :=
    Module.Finite.of_injective (Submodule.subtype _) Subtype.coe_injective
  have h := ModuleCat.free_shortExact_finrank_add hInv
    (n := Module.finrank k (F.obj S.X₁))
    (p := Module.finrank k (F.obj S.X₃)) rfl rfl
  exact h

/-- **Invariant dimension on the group-algebra Grothendieck group.** When `#G` is nonzero in
`k`, this homomorphism sends the class of a finite-dimensional representation `V` to
`dimₖ(Vᴳ)`. -/
noncomputable def finrankInvariantsK0 :
    ExactK0 (finiteModulesExactStructure k[G]) →+ ℤ :=
  liftFDRepK0 (fun V ↦ (Module.finrank k (Representation.invariants V.ρ) : ℤ))
    fun {_} hS ↦ by
    exact_mod_cast FDRep.finrank_invariants_add_of_shortExact hS

/-- The invariant-dimension homomorphism evaluates on an actual representation as the dimension
of its invariant subspace. -/
theorem finrankInvariantsK0_fdRepK0RingEquiv_of (V : FDRep k G) :
    finrankInvariantsK0 (k := k) (G := G) (fdRepK0RingEquiv k G (ExactK0.of V)) =
      Module.finrank k (Representation.invariants V.ρ) := by
  rw [fdRepK0RingEquiv_of]
  simp [finrankInvariantsK0]

/-- **Invariant dimension after tensoring with `A`.** This additive homomorphism sends a class
`[M]` to `dimₖ (M ⊗ A)ᴳ`. -/
noncomputable def finrankTensorInvariantsK0 (A : FDRep k G) :
    ExactK0 (finiteModulesExactStructure k[G]) →+ ℤ :=
  (finrankInvariantsK0 (k := k) (G := G)).comp
    (AddMonoidHom.mulRight (fdRepK0RingEquiv k G (ExactK0.of A)))

/-- Evaluating `finrankTensorInvariantsK0 A` on `[M]` gives the dimension of the invariants of
the tensor product `M ⊗ A`. -/
theorem finrankTensorInvariantsK0_fdRepK0RingEquiv_of (A M : FDRep k G) :
    finrankTensorInvariantsK0 A (fdRepK0RingEquiv k G (ExactK0.of M)) =
      Module.finrank k (Representation.invariants (M ⊗ A).ρ) := by
  rw [finrankTensorInvariantsK0, AddMonoidHom.comp_apply, AddMonoidHom.mulRight_apply,
    ← map_mul, ExactK0.of_mul_of, finrankInvariantsK0_fdRepK0RingEquiv_of]

end TauCeti
