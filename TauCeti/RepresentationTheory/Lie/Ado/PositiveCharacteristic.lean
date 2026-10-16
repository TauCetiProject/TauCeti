/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Domain
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Embedding
public import TauCeti.RepresentationTheory.Lie.Ado.CharP

/-!
# Faithful Lie representations in positive characteristic

Every finite-dimensional Lie algebra over a field of prime characteristic admits a faithful
finite-dimensional representation that sends adjoint-nilpotent elements to nilpotent
endomorphisms. This is Hochschild's strengthening of the positive-characteristic Ado theorem.

The representation comes from left multiplication on a finite-dimensional quotient of the
universal enveloping algebra by a power of its central augmentation ideal. The quotient
construction preserves adjoint nilpotence and has the same kernel on the Lie algebra as the
canonical map into its enveloping algebra. The Poincaré--Birkhoff--Witt theorem makes that
canonical map injective and supplies the domain property needed by the quotient construction.
The resulting existence statements involve no chosen basis or central generating family.

## References

* G. Hochschild, *An Addition to Ado's Theorem*, Proceedings of the American Mathematical Society
  **17** (1966), 531--533.
-/

public section

namespace TauCeti

universe u v

attribute [local instance 100] LieRing.ofAssociativeRing

variable (K : Type u) (L : Type v) [Field K] [LieRing L] [LieAlgebra K L]
variable [FiniteDimensional K L]

/-- **Hochschild's strengthening in prime characteristic.** A finite-dimensional Lie algebra
has a faithful finite-dimensional representation that preserves nilpotence of the adjoint
action. There is no restriction on the prime, including in characteristics two and three. -/
theorem exists_faithful_preserving_ad_nilpotence_charP (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (ρ : L →ₗ⁅K⁆ Module.End K V),
      Function.Injective ρ ∧
        ∀ x : L, IsNilpotent (LieAlgebra.ad K L x) → IsNilpotent (ρ x) := by
  obtain ⟨V, _, _, _, ρ, hker, hnil⟩ :=
    UniversalEnvelopingAlgebra.exists_representation_eq_zero_iff_ι_eq_zero K L p
  refine ⟨V, inferInstance, inferInstance, inferInstance, ρ, ?_, hnil⟩
  apply (injective_iff_map_eq_zero ρ).2
  intro x hx
  exact (UniversalEnvelopingAlgebra.ι_injective K L)
    (by simpa only [map_zero] using (hker x).1 hx)

/-- **Ado's theorem in prime characteristic.** Every finite-dimensional Lie algebra over a
field of prime characteristic admits a faithful finite-dimensional representation. -/
theorem adoCharP (p : ℕ) [Fact p.Prime] [CharP K p] :
    ∃ (V : Type (max u v)) (_ : AddCommGroup V) (_ : Module K V)
      (_ : FiniteDimensional K V) (ρ : L →ₗ⁅K⁆ Module.End K V), Function.Injective ρ := by
  obtain ⟨V, _, _, _, ρ, hρ, _⟩ := exists_faithful_preserving_ad_nilpotence_charP K L p
  exact ⟨V, inferInstance, inferInstance, inferInstance, ρ, hρ⟩

end TauCeti
