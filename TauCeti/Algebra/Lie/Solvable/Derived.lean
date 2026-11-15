/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Character
public import TauCeti.Algebra.Lie.BaseChange.Radical

/-!
# The derived algebra of a solvable Lie algebra

In characteristic zero, the derived algebra of a solvable Lie algebra acts nilpotently on
any finite-dimensional module. In particular the derived algebra of a finite-dimensional
solvable Lie algebra is nilpotent and lies in its nilradical. This is the structural input
for controlling images of derivations by adjoining a derivation as a new Lie algebra element.

Lie's theorem supplies a nonzero common weight space after extending scalars to an algebraic
closure. The derived algebra acts trivially on that space, and induction on the dimension of
the quotient proves nilpotence. Nilpotence then descends along the injective scalar-extension
map on endomorphisms, as in Mathlib's
`LieModule.isNilpotent_derivedSeries_of_traceForm_eq_zero`.

## References

* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter II, Lie's theorem and its corollaries.
-/

public section

open LieAlgebra LieModule TensorProduct

namespace TauCeti

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Over an algebraically closed field of characteristic zero, the derived algebra of a
solvable Lie algebra acts nilpotently on any finite-dimensional module. -/
private theorem isNilpotent_derivedSeries_of_isSolvable_of_isAlgClosed [IsAlgClosed K]
    [IsSolvable L] (M : Type*) [AddCommGroup M] [Module K M]
    [LieRingModule L M] [LieModule K L M] [FiniteDimensional K M] :
    LieModule.IsNilpotent (derivedSeries K L 1) M := by
  classical
  obtain hM | hM := subsingleton_or_nontrivial M
  · exact (LieModule.isNilpotent_iff K _ M).mpr ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨χ, hχ⟩ := exists_nontrivial_weightSpace_of_isSolvable K L M
  let N := weightSpace M χ
  obtain ⟨v, hv⟩ := exists_ne (0 : N)
  have hv0 : (v : M) ≠ 0 := by simpa using hv
  have hweight := (mem_weightSpace (M := M) χ (v : M)).mp v.property
  have hχlie (x y : L) : χ ⁅x, y⁆ = 0 := by
    have h : χ ⁅x, y⁆ • (v : M) = 0 := by
      calc
        _ = ⁅⁅x, y⁆, (v : M)⁆ := (hweight _).symm
        _ = ⁅x, ⁅y, (v : M)⁆⁆ - ⁅y, ⁅x, (v : M)⁆⁆ := lie_lie x y (v : M)
        _ = 0 := by simp [hweight, smul_smul, mul_comm]
    exact (smul_eq_zero.mp h).resolve_right hv0
  let χ' : LieCharacter K L :=
    { χ with map_lie' := fun {x y} ↦ by simp [hχlie, Ring.lie_def, mul_comm] }
  let N' : LieSubmodule K (derivedSeries K L 1) M :=
    { N.toSubmodule with lie_mem := fun {x m} hm ↦ N.lie_mem hm }
  have htriv : N' ≤
      maxTrivSubmodule K (derivedSeries K L 1) M := by
    intro m hm
    rw [LieModule.mem_maxTrivSubmodule]
    intro x
    -- The ideal action is the ambient action through its subtype inclusion.
    change ⁅(x : L), m⁆ = 0
    have hzero : χ (x : L) = 0 := lieCharacter_apply_of_mem_derived χ' x.property
    rw [(mem_weightSpace (M := M) χ m).mp hm x, hzero, zero_smul]
  have hquot : LieModule.IsNilpotent (derivedSeries K L 1) (M ⧸ N) :=
    isNilpotent_derivedSeries_of_isSolvable_of_isAlgClosed (M ⧸ N)
  -- Restricting the acting algebra does not change the underlying quotient or its action.
  exact nilpotentOfNilpotentQuotient K (derivedSeries K L 1) M htriv hquot
termination_by Module.finrank K M
decreasing_by
  have hN : 0 < Module.finrank K N := Module.finrank_pos
  have hdim : Module.finrank K (M ⧸ weightSpace M χ) +
      Module.finrank K (weightSpace M χ) = Module.finrank K M :=
    Submodule.finrank_quotient_add_finrank N.toSubmodule
  dsimp only [N] at hN
  omega

/-- In characteristic zero, the derived algebra of a solvable Lie algebra acts nilpotently
on any finite-dimensional module, over the original field. -/
theorem isNilpotent_derivedSeries_of_isSolvable [IsSolvable L]
    (M : Type*) [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [FiniteDimensional K M] : LieModule.IsNilpotent (derivedSeries K L 1) M := by
  let A := AlgebraicClosure K
  have : IsSolvable (A ⊗[K] L) := by
    have htop := LieIdeal.isSolvable_baseChange A (⊤ : LieIdeal K L)
    rw [LieSubmodule.baseChange_top] at htop
    exact (solvable_iff_equiv_solvable LieIdeal.topEquiv).mp htop
  have hnil := isNilpotent_derivedSeries_of_isSolvable_of_isAlgClosed
    (K := A) (L := A ⊗[K] L) (A ⊗[K] M)
  rw [LieModule.isNilpotent_iff_forall' (R := K)]
  intro ⟨x, hx⟩
  have hxA : (1 : A) ⊗ₜ[K] x ∈ derivedSeries A (A ⊗[K] L) 1 := by
    rw [derivedSeries_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hx
  have hinj : Function.Injective (Module.End.baseChangeHom K A M) :=
    LinearMap.baseChangeHom_injective K M A
  -- On a restricted module the action of the subtype element is the original action.
  have haction : toEnd K (derivedSeries K L 1) M ⟨x, hx⟩ = toEnd K L M x := rfl
  rw [haction, ← IsNilpotent.map_iff hinj]
  -- The endomorphism algebra map is scalar extension of the underlying linear map.
  have hbase : Module.End.baseChangeHom K A M (toEnd K L M x) =
      (toEnd K L M x).baseChange A := rfl
  rw [hbase, ← toEnd_baseChange]
  exact (LieModule.isNilpotent_iff_forall' (R := A)).mp hnil ⟨_, hxA⟩

/-- The derived algebra of a finite-dimensional solvable Lie algebra in characteristic zero
is contained in its nilradical. -/
theorem derivedSeries_le_nilradical_of_isSolvable [IsSolvable L] [FiniteDimensional K L] :
    derivedSeries K L 1 ≤ LieAlgebra.nilradical K L := by
  have := isNilpotent_derivedSeries_of_isSolvable (K := K) (L := L) L
  exact LieIdeal.le_nilradical K L _
    ((LieIdeal.isNilpotent_iff_isNilpotent_ambient _).mpr this)

end TauCeti
