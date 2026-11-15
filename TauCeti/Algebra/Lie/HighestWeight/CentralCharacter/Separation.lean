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
  intro lam hlam mu hmu h
  obtain ⟨w, rfl⟩ := (vermaCentralCharacter_eq_iff b).mp h
  exact (dotAction_eq_self_of_dominantIntegral (isDominantIntegral_iff_forall_coroot'.mp hlam)
    (isDominantIntegral_iff_forall_coroot'.mp hmu)).symm

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
  -- the centre eigenspaces of the dominant integral central characters are independent
  have hindep : iSupIndep fun mu : {l : Dual K H // IsDominantIntegral b l} ↦
      centerEigenspace K L M (vermaCentralCharacter b mu.1) :=
    (iSupIndep_centerEigenspace (M := M)).comp fun mu nu h ↦ Subtype.ext <|
      vermaCentralCharacter_injOn_isDominantIntegral b mu.2 nu.2 (DFunLike.coe_injective h)
  exact congr_fun ((hindep.le_iff_eq_of_iSup_eq_top
    (iSup_isotypicComponent_irreducibleQuotient_eq_top M b)).mp
    fun _ ↦ isotypicComponent_irreducibleQuotient_le_centerEigenspace) ⟨lam, hlam⟩ |>.symm

end TauCeti
