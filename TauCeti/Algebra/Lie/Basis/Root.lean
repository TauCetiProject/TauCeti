/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Basis.Base

/-!
# Root vectors of a Lie algebra basis

This file relates a `LieAlgebra.Basis` to the root-space decomposition of its Cartan subalgebra.
The raising and lowering generators lie in the expected simple-root spaces. Moreover, the
three-part Cartan/lower-Borel/upper-Borel decomposition already constructed by Mathlib lies in
generalized weight spaces. It follows that the Cartan action is triangularizable over the ground
field, without passing to an algebraic closure.

## Main results

* `LieAlgebra.Basis.isTriangularizable`: the Cartan action associated to a Lie-algebra basis is
  triangularizable over the ground field.
* `TauCeti.lieBasis_e_mem_rootSpace` and `TauCeti.lieBasis_f_mem_rootSpace`: the simple raising
  and lowering generators lie in their expected root spaces.

## References

* M. Geck, *On the construction of semisimple Lie algebras and Chevalley groups*,
  Proc. Amer. Math. Soc. **145** (2017), 3233--3247, Lemma 4.4.
-/

public section

open LieAlgebra LieModule

namespace LieAlgebra.Basis

variable {ι K L : Type*} [Finite ι] [CommRing K] [IsDomain K] [CharZero K]
  [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L}

/-- The Cartan action associated to a Lie-algebra basis is triangularizable over the ground
field. The three-part decomposition from the basis is already contained in generalized weight
spaces, so every Cartan element has a full decomposition into generalized eigenspaces. -/
theorem isTriangularizable (b : LieAlgebra.Basis ι H) :
    LieModule.IsTriangularizable K H L := by
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : IsLieAbelian H := b.isLieAbelian_cartan
  have hweights : ⨆ chi : H → K, genWeightSpace L chi = ⊤ := by
    apply top_unique
    rw [← b.iSup_cartan_borelLower_borelUpper_eq_top]
    apply iSup_le
    intro k
    fin_cases k
    · exact (toLieSubmodule_le_rootSpace_zero K L H).trans (le_iSup _ 0)
    · exact b.borelLower_le_biSup.trans <| iSup_le fun n => iSup_le fun hn =>
        le_iSup (fun chi : H → K => genWeightSpace L chi) _
    · exact b.borelUpper_le_biSup.trans <| iSup_le fun n => iSup_le fun hn =>
        le_iSup (fun chi : H → K => genWeightSpace L chi) _
  refine ⟨fun z => top_unique ?_⟩
  calc
    (⊤ : Submodule K L) = (⊤ : LieSubmodule K H L).toSubmodule :=
      LieSubmodule.top_toSubmodule.symm
    _ = (⨆ chi : H → K, genWeightSpace L chi).toSubmodule := congrArg _ hweights.symm
    _ = ⨆ chi : H → K, (genWeightSpace L chi).toSubmodule :=
      by rw [LieSubmodule.iSup_toSubmodule]
    _ ≤ ⨆ a : K, (LieModule.toEnd K H L z).maxGenEigenspace a := iSup_le fun chi =>
      calc
        (genWeightSpace L chi).toSubmodule ≤
            (genWeightSpaceOf L (chi z) z).toSubmodule :=
          (LieSubmodule.toSubmodule_orderEmbedding K H L).le_iff_le.mpr
            (genWeightSpace_le_genWeightSpaceOf L z chi)
        _ = (LieModule.toEnd K H L z).maxGenEigenspace (chi z) := by
          ext m
          rw [LieSubmodule.mem_toSubmodule, LieModule.mem_genWeightSpaceOf,
            Module.End.mem_maxGenEigenspace]
        _ ≤ ⨆ a : K, (LieModule.toEnd K H L z).maxGenEigenspace a := le_iSup _ _

end LieAlgebra.Basis

namespace TauCeti

variable {ι K L : Type*} [Fintype ι] [CommRing K] [LieRing L] [LieAlgebra K L]
  {H : LieSubalgebra K L} [H.IsCartanSubalgebra] (b : LieAlgebra.Basis ι H)

/-- The raising generator `eᵢ` of a Lie algebra basis is a root vector for its simple root. -/
theorem lieBasis_e_mem_rootSpace (i : ι) : b.e i ∈ rootSpace H (⇑(b.baseSupp i)) :=
  (mem_genWeightSpace _ _ _).mpr fun x ↦ ⟨1, by simp⟩

/-- The lowering generator `fᵢ` of a Lie algebra basis is a root vector for minus its simple
root. -/
theorem lieBasis_f_mem_rootSpace (i : ι) : b.f i ∈ rootSpace H (-⇑(b.baseSupp i)) :=
  (mem_genWeightSpace _ _ _).mpr fun x ↦ ⟨1, by simp [← eq_neg_iff_add_eq_zero]⟩

end TauCeti
