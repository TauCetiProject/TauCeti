/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Derivation
public import TauCeti.Algebra.Lie.UniversalEnveloping.LieIdeal
public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Cofinite
public import TauCeti.RingTheory.Ideal.Quotient.Nilpotent
public import TauCeti.RingTheory.Ideal.Operations

/-!
# Cofinite refinements stable under lifted derivations

Let `L` be a module-finite Lie algebra, `I` a two-sided ideal of `U(L)` with Noetherian
quotient over the coefficient ring, and `N` a Lie ideal whose canonical images are
nilpotent modulo `I`. A power of `B = I ⊔ N.envelopingIdeal` lies
inside `I`, has module-finite quotient, and is stable under every lifted derivation whose values
on `L` lie in `N`. Moreover, every element nilpotent modulo `I` remains nilpotent modulo the
refinement, and conversely.

For a solvable Lie algebra in characteristic zero, taking `N` to be its nilradical reduces
construction of a derivation-stable cofinite representation kernel to the structural statement
that derivations take values in the nilradical. The refinement below applies independently of
that structural statement, to any Lie ideal with the stated nilpotent action. It also works over
commutative coefficient rings when the original quotient is Noetherian, and
does not require a free Lie algebra.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2,
  the cofinite-ideal refinement in the proof of Proposition E.5.
-/

public section

namespace TauCeti

universe u v

variable {R : Type u} {L : Type v} [CommRing R]
  [LieRing L] [LieAlgebra R L] [Module.Finite R L]

local notation "U" => UniversalEnvelopingAlgebra R L

/-- A two-sided ideal whose quotient is Noetherian over the coefficient ring
admits a cofinite refinement stable under every lifted derivation taking values in a Lie ideal `N`
that acts nilpotently modulo the original ideal. The refinement
is a power of `I ⊔ N.envelopingIdeal`, and it has exactly the same nilpotent elements in its
quotient as the original ideal. No stability of `I` is assumed. -/
theorem _root_.LieIdeal.exists_cofinite_refinement_stableDerivations (N : LieIdeal R L)
    (I : Ideal U) [I.IsTwoSided] [IsNoetherian R (U ⧸ I)]
    (hnil : ∀ x : L, x ∈ N → IsNilpotent (Ideal.Quotient.mk I
      (UniversalEnvelopingAlgebra.ι R x))) :
    ∃ n : ℕ,
      (I ⊔ N.envelopingIdeal) ^ n ≤ I ∧
      Module.Finite R (U ⧸ (I ⊔ N.envelopingIdeal) ^ n) ∧
      (∀ D : LieDerivation R L L, (∀ x : L, D x ∈ N) →
        UniversalEnvelopingAlgebra.envelopingDerivation R L D ∈
          stableDerivations R (((I ⊔ N.envelopingIdeal) ^ n).restrictScalars R)) ∧
      ∀ a : U, IsNilpotent (Ideal.Quotient.mk ((I ⊔ N.envelopingIdeal) ^ n) a) ↔
        IsNilpotent (Ideal.Quotient.mk I a) := by
  let B : Ideal U := I ⊔ N.envelopingIdeal
  have hIB : I ≤ B := le_sup_left
  have : Module.Finite R (U ⧸ B) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ R hIB).toLinearMap
      (Ideal.Quotient.factor_surjective hIB)
  obtain ⟨n, hn⟩ := N.exists_sup_envelopingIdeal_pow_le_of_forall_isNilpotent I hnil
  refine ⟨n, hn, UniversalEnvelopingAlgebra.moduleFinite_quotient_pow R L B n, ?_, ?_⟩
  · intro D hD
    exact UniversalEnvelopingAlgebra.envelopingDerivation_mem_stableDerivations_pow R L D B
      (fun x ↦ Ideal.mem_sup_right (N.ι_mem_envelopingIdeal (hD x))) n
  · intro a
    constructor
    · intro ha
      simpa only [Ideal.Quotient.factorₐ_apply_mk] using
        ha.map (Ideal.Quotient.factorₐ R hn)
    · intro ha
      have hBa : IsNilpotent (Ideal.Quotient.mk B a) := by
        simpa only [Ideal.Quotient.factorₐ_apply_mk]
          using ha.map (Ideal.Quotient.factorₐ R hIB)
      exact B.isNilpotent_quotient_pow_of_isNilpotent_quotient hBa n

end TauCeti
