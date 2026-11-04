/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Isomorphism
public import TauCeti.Algebra.Lie.HighestWeight.CentralCharacter.Isotypic
-- Non-public: these appear only inside proofs, never in the type of an exported declaration.
import TauCeti.Algebra.Lie.HighestWeight.Decomposition
import TauCeti.LinearAlgebra.RootSystem.Weyl.DominantIntegral

/-!
# Central characters separate the dominant integral weights

Let `L` be a finite-dimensional Lie algebra with non-degenerate Killing form over an algebraically
closed field `K` of characteristic zero, `H` a splitting Cartan subalgebra and `b` a base of its
root system. The central character `χ_lam = TauCeti.vermaCentralCharacter b lam` records how the
centre `Z(U(L))` of the universal enveloping algebra acts on a highest weight module of weight
`lam`.

* **Central characters separate the dominant integral weights**
  (`TauCeti.vermaCentralCharacter_injOn_isDominantIntegral`): if `lam` and `mu` are dominant
  integral and `χ_lam = χ_mu`, then `lam = mu`. By Harish-Chandra's theorem
  (`TauCeti.vermaCentralCharacter_eq_iff`) the two weights lie in one dot orbit, and a dominant
  integral weight is the only dominant integral weight in its dot orbit
  (`TauCeti.dotAction_eq_self_of_dominantIntegral`). No order on `K` is used: the comparison takes
  place in the positive root cone, which is pointed in characteristic zero.
* **The centre eigenspaces of a finite-dimensional module are its isotypic components**
  (`TauCeti.centerEigenspace_vermaCentralCharacter_eq_isotypicComponent`): for a dominant integral
  weight `lam`, the vectors of a finite-dimensional module on which the centre acts by `χ_lam` form
  exactly the `L(lam)`-isotypic component. So the decomposition of a finite-dimensional module
  into centre eigenspaces (`TauCeti.isInternal_centerEigenspace`) is its decomposition into
  isotypic components.

A single central element, such as the Casimir element, does not separate distinct dominant
integral weights in general; the whole centre does.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.3.
* J. E. Humphreys, *Representations of Semisimple Lie Algebras in the BGG Category `O`*, §1.10.
-/

public section

namespace TauCeti

-- `TauCeti.LieModule` exists in the imports, so the root namespace is named explicitly.
open LieAlgebra _root_.LieModule Module TauCeti.UniversalEnvelopingAlgebra

universe v w

variable {K : Type} {L : Type v} [Field K] [CharZero K] [IsAlgClosed K] [LieRing L]
  [LieAlgebra K L] [IsKilling K L] [FiniteDimensional K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (IsKilling.rootSystem H).Base)

/-- **Central characters separate the dominant integral weights**: two dominant integral weights
with the same central character are equal. -/
theorem vermaCentralCharacter_injOn_isDominantIntegral :
    Set.InjOn (vermaCentralCharacter b) {lam | IsDominantIntegral b lam} := by
  have hcoroot : ∀ {chi : Dual K H}, IsDominantIntegral b chi →
      ∀ i ∈ b.support, ∃ n : ℕ, (IsKilling.rootSystem H).coroot' i chi = (n : K) :=
    fun hchi i hi ↦ by
      obtain ⟨n, hn⟩ := isDominantIntegral_iff.mp hchi i hi
      exact ⟨n, by rwa [rootSystem_coroot'_apply]⟩
  intro lam hlam mu hmu h
  obtain ⟨w, rfl⟩ := (vermaCentralCharacter_eq_iff b).mp h
  exact (dotAction_eq_self_of_dominantIntegral (hcoroot hlam) (hcoroot hmu)).symm

variable {M : Type w} [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
  [FiniteDimensional K M]

variable {b} in
/-- **The centre eigenspace of `χ_lam` is the `L(lam)`-isotypic component**: in a
finite-dimensional module, for a dominant integral weight `lam`, the vectors on which every central
element `z` of `U(L)` acts by the scalar `χ_lam z` form exactly the `L(lam)`-isotypic
component. -/
theorem centerEigenspace_vermaCentralCharacter_eq_isotypicComponent {lam : Dual K H}
    (hlam : IsDominantIntegral b lam) :
    centerEigenspace K L M (vermaCentralCharacter b lam) =
      isotypicComponent K L M (irreducibleQuotient b lam) := by
  set I := isotypicComponent K L M (irreducibleQuotient b lam)
  have hI : I ≤ centerEigenspace K L M (vermaCentralCharacter b lam) :=
    isotypicComponent_irreducibleQuotient_le_centerEigenspace
  -- the sum of the centre eigenspaces of the other eigenvalue functions
  set X := ⨆ (χ : Subalgebra.center K (_root_.UniversalEnvelopingAlgebra K L) → K)
    (_ : χ ≠ vermaCentralCharacter b lam), centerEigenspace K L M χ
  -- every other isotypic component lies in `X`, since its central character differs from `χ_lam`
  have htop : I ⊔ X = ⊤ := by
    refine top_unique <| (iSup_isotypicComponent_irreducibleQuotient_eq_top M b).ge.trans <|
      iSup_le fun mu ↦ ?_
    rcases eq_or_ne mu.1 lam with h | h
    · exact le_sup_of_le_left (h ▸ le_rfl)
    · refine le_sup_of_le_right <| le_iSup₂_of_le (f := fun χ (_ : χ ≠ _) ↦
        centerEigenspace K L M χ) _ (fun he ↦ h ?_)
        isotypicComponent_irreducibleQuotient_le_centerEigenspace
      exact vermaCentralCharacter_injOn_isDominantIntegral b mu.2 hlam (DFunLike.coe_injective he)
  have hdisj : Disjoint X (centerEigenspace K L M (vermaCentralCharacter b lam)) :=
    (iSupIndep_centerEigenspace (vermaCentralCharacter b lam : _ → K)).symm
  refine le_antisymm (le_of_eq ?_) hI
  calc centerEigenspace K L M (vermaCentralCharacter b lam)
      = (I ⊔ X) ⊓ centerEigenspace K L M (vermaCentralCharacter b lam) := by
        rw [htop, top_inf_eq]
    _ = I ⊔ X ⊓ centerEigenspace K L M (vermaCentralCharacter b lam) := sup_inf_assoc_of_le X hI
    _ = I := by rw [hdisj.eq_bot, sup_bot_eq]

end TauCeti
