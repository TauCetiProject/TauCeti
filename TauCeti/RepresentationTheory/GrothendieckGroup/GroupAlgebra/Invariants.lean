/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Invariants
public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.Ring
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
representations. -/
theorem Rep.shortExact_map_invariantsFunctor {S : ShortComplex (Rep k G)} (hS : S.ShortExact) :
    (S.map (Rep.invariantsFunctor k G)).ShortExact := by
  have : (Rep.invariantsFunctor k G).PreservesEpimorphisms := ⟨fun {X Y} f hf ↦ by
      have : Module.Projective k[G] Y.ρ.asModule :=
        Module.projective_of_isSemisimpleRing k[G] Y.ρ.asModule
      exact (ModuleCat.epi_iff_surjective _).2
        (Rep.invariantsFunctor_map_surjective_of_surjective_of_projective f
          ((Rep.epi_iff_surjective f).1 hf))⟩
  have : (Rep.invariantsFunctor k G).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels _
  have : Mono S.f := hS.mono_f
  have : Epi S.g := hS.epi_g
  exact hS.map _

/-- Invariant dimension is additive on short exact sequences of finite-dimensional
representations when the group order is invertible in the coefficient field. -/
theorem FDRep.finrank_invariants_add_of_shortExact {S : ShortComplex (FDRep k G)}
    (hS : S.ShortExact) :
    Module.finrank k (Representation.invariants S.X₂.ρ) =
      Module.finrank k (Representation.invariants S.X₁.ρ) +
        Module.finrank k (Representation.invariants S.X₃.ρ) := by
  have hInv := Rep.shortExact_map_invariantsFunctor
    (hS.map_of_exact (forget₂ (FDRep k G) (Rep k G)))
  -- `Rep.invariantsFunctor` sends `forget₂ V` to the invariant subspace of `V.ρ`
  -- (`Rep.invariantsFunctor_obj_carrier`, `FDRep.forget₂_ρ`).
  have hfinrank (V : FDRep k G) :
      Module.finrank k ((Rep.invariantsFunctor k G).obj ((forget₂ (FDRep k G) (Rep k G)).obj V)) =
        Module.finrank k (Representation.invariants V.ρ) :=
    rfl
  have hfinite (V : FDRep k G) :
      Module.Finite k ((Rep.invariantsFunctor k G).obj ((forget₂ (FDRep k G) (Rep k G)).obj V)) :=
    Module.Finite.of_injective (Representation.invariants V.ρ).subtype Subtype.coe_injective
  have : Module.Finite k ((S.map (forget₂ (FDRep k G) (Rep k G))).map
      (Rep.invariantsFunctor k G)).X₁ := hfinite S.X₁
  have : Module.Finite k ((S.map (forget₂ (FDRep k G) (Rep k G))).map
      (Rep.invariantsFunctor k G)).X₃ := hfinite S.X₃
  simpa only [ShortComplex.map_X₁, ShortComplex.map_X₂, ShortComplex.map_X₃, hfinrank] using
    ModuleCat.free_shortExact_finrank_add hInv rfl rfl

/-- **Invariant dimension on the group-algebra Grothendieck group.** When `#G` is nonzero in
`k`, this homomorphism sends the class of a finite-dimensional representation `V` to
`dimₖ(Vᴳ)`. -/
noncomputable def finrankInvariantsK0 :
    ExactK0 (finiteModulesExactStructure k[G]) →+ ℤ :=
  liftFDRepK0 (fun V ↦ (Module.finrank k (Representation.invariants V.ρ) : ℤ))
    fun {_} hS ↦ by
    exact_mod_cast FDRep.finrank_invariants_add_of_shortExact hS

/-- The invariant-dimension homomorphism evaluates on the class of the group-algebra module of a
representation `V` as the dimension of the invariant subspace of `V`. -/
@[simp]
theorem finrankInvariantsK0_of (V : FDRep k G) :
    letI : Module.Finite k[G] (Representation.asModule V.ρ) :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    finrankInvariantsK0 (ExactK0.of (FGModuleCat.of k[G] (Representation.asModule V.ρ))) =
      Module.finrank k (Representation.invariants V.ρ) :=
  liftFDRepK0_of _ _ V

/-- **Invariant dimension after tensoring with `A`.** This additive homomorphism sends a class
`[M]` to `dimₖ (M ⊗ A)ᴳ`. -/
noncomputable def finrankTensorInvariantsK0 (A : FDRep k G) :
    ExactK0 (finiteModulesExactStructure k[G]) →+ ℤ :=
  (finrankInvariantsK0 (k := k) (G := G)).comp
    (AddMonoidHom.mulRight (fdRepK0RingEquiv k G (ExactK0.of A)))

/-- `finrankTensorInvariantsK0 A` is invariant dimension after multiplication by the class of
`A`. -/
theorem finrankTensorInvariantsK0_apply (A : FDRep k G)
    (x : ExactK0 (finiteModulesExactStructure k[G])) :
    finrankTensorInvariantsK0 A x =
      finrankInvariantsK0 (x * fdRepK0RingEquiv k G (ExactK0.of A)) := by
  rw [finrankTensorInvariantsK0, AddMonoidHom.comp_apply, AddMonoidHom.mulRight_apply]

/-- Evaluating `finrankTensorInvariantsK0 A` on the class of the group-algebra module of `M`
gives the dimension of the invariants of the tensor product `M ⊗ A`. -/
@[simp]
theorem finrankTensorInvariantsK0_of (A M : FDRep k G) :
    letI : Module.Finite k[G] (Representation.asModule M.ρ) :=
      Module.Finite.of_restrictScalars_finite k k[G] _
    finrankTensorInvariantsK0 A (ExactK0.of (FGModuleCat.of k[G] (Representation.asModule M.ρ))) =
      Module.finrank k (Representation.invariants (M ⊗ A).ρ) := by
  rw [← fdRepK0RingEquiv_of, finrankTensorInvariantsK0_apply, ← map_mul, ExactK0.of_mul_of,
    fdRepK0RingEquiv_of, finrankInvariantsK0_of]

end TauCeti
